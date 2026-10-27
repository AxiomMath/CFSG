module

public import Certificates.Data.Kernel.PCentExt
public import CFSG.Certificates.Kernel.PCentCheck
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.PCent

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask pinvS)
open CFSG.KC.BfsPin (PP)
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem commutator_le_of_conj {S T : Set G}
    (h1 : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ Subgroup.closure T)
    (h2 : ∀ s ∈ S, ∀ t ∈ T, s⁻¹ * t * s ∈ Subgroup.closure T)
    (h3 : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ Subgroup.closure T) :
    ⁅Subgroup.closure S, Subgroup.closure S⁆ ≤ Subgroup.closure T := by
  set D := Subgroup.closure T
  have hc : ∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D ∧ s⁻¹ * d * s ∈ D := by
    intro s hs d hd
    induction hd using Subgroup.closure_induction with
    | mem t ht => exact ⟨h1 s hs t ht, h2 s hs t ht⟩
    | one => simp [D.one_mem]
    | mul a b _ _ ha hb =>
      refine ⟨?_, ?_⟩
      · have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        rw [e]
        exact D.mul_mem ha.1 hb.1
      · have e : s⁻¹ * (a * b) * s = (s⁻¹ * a * s) * (s⁻¹ * b * s) := by group
        rw [e]
        exact D.mul_mem ha.2 hb.2
    | inv a _ ha =>
      refine ⟨?_, ?_⟩
      · have e : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
        rw [e]
        exact D.inv_mem ha.1
      · have e : s⁻¹ * a⁻¹ * s = (s⁻¹ * a * s)⁻¹ := by group
        rw [e]
        exact D.inv_mem ha.2
  set N := Subgroup.normalizer (D : Set G)
  have hN : Subgroup.closure S ≤ N := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨fun hd => (hc s hs d hd).1, fun hd => ?_⟩
    have e : d = s⁻¹ * (s * d * s⁻¹) * s := by group
    rw [e]
    exact (hc s hs _ hd).2
  let H (x : G) : Subgroup G :=
    { carrier := {y | y ∈ N ∧ ⁅x, y⁆ ∈ D}
      one_mem' := ⟨N.one_mem, by rw [commutatorElement_one_right]; exact D.one_mem⟩
      mul_mem' := by
        rintro y z ⟨hy, hxy⟩ ⟨hz, hxz⟩
        refine ⟨N.mul_mem hy hz, ?_⟩
        have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact D.mul_mem hxy ((Subgroup.mem_normalizer_iff.1 hy _).1 hxz)
      inv_mem' := by
        rintro y ⟨hy, hxy⟩
        refine ⟨N.inv_mem hy, ?_⟩
        have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (N.inv_mem hy) _).1 (D.inv_mem hxy) }
  have hmemH : ∀ x y, y ∈ H x ↔ y ∈ N ∧ ⁅x, y⁆ ∈ D := fun _ _ => Iff.rfl
  have hstep : ∀ x ∈ Subgroup.closure S, (∀ s ∈ S, ⁅x, s⁆ ∈ D) →
      ∀ y ∈ Subgroup.closure S, ⁅x, y⁆ ∈ D := by
    intro x _ hx y hy
    have hle : Subgroup.closure S ≤ H x := by
      rw [Subgroup.closure_le]
      intro s hs
      exact (hmemH x s).2 ⟨hN (Subgroup.subset_closure hs), hx s hs⟩
    exact ((hmemH x y).1 (hle hy)).2
  have hS : ∀ s ∈ S, ∀ y ∈ Subgroup.closure S, ⁅s, y⁆ ∈ D := fun s hs =>
    hstep s (Subgroup.subset_closure hs) fun s' hs' => h3 s hs s' hs'
  refine Subgroup.commutator_le.2 fun x hx y hy => hstep x hx (fun s hs => ?_) y hy
  have e : ⁅x, s⁆ = ⁅s, x⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact D.inv_mem (hS s hs x hx)

theorem fix_of_odd_orbit [Finite G] {α : Type*} [MulAction G α] {D Q : Subgroup G} {k : ℕ}
    (hQD : Q ≤ D) (hQn : ∀ d ∈ D, ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) (hQ : Nat.card Q = 2 ^ k)
    (Ω : Finset α) (x₀ : α) (htr : ∀ y ∈ Ω, ∃ d ∈ D, d • x₀ = y)
    (hinv : ∀ d ∈ D, ∀ y ∈ Ω, d • y ∈ Ω) (hodd : Odd Ω.card) :
    ∀ q ∈ Q, ∀ y ∈ Ω, q • y = y := by
  classical
  have hp : IsPGroup 2 Q := IsPGroup.of_card hQ
  let P : SubMulAction Q α :=
    { carrier := (Ω : Set α)
      smul_mem' := fun q y hy => by
        rw [Subgroup.smul_def]
        exact hinv q (hQD q.2) y hy }
  have hfin : Finite P := by
    change Finite (Ω : Set α)
    exact Ω.finite_toSet.to_subtype
  have hcard : Nat.card P = Ω.card := by
    change Nat.card ((Ω : Set α)) = Ω.card
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hmod := hp.card_modEq_card_fixedPoints P
  obtain ⟨⟨f, hfΩ⟩, hf⟩ : (MulAction.fixedPoints Q P).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hcard, hne, Nat.card_of_isEmpty] at hmod
    have h1 := Nat.odd_iff.1 hodd
    unfold Nat.ModEq at hmod
    omega
  have hfix : ∀ q ∈ Q, (q : G) • f = f := fun q hq => by
    have e := hf ⟨q, hq⟩
    have e' := congrArg Subtype.val e
    rw [SubMulAction.val_smul, Subgroup.smul_def] at e'
    exact e'
  intro q hq y hy
  obtain ⟨d, hd, rfl⟩ := htr y hy
  obtain ⟨d', hd', hfd⟩ := htr f hfΩ
  have he : d * d'⁻¹ ∈ D := D.mul_mem hd (D.inv_mem hd')
  have hy' : d • x₀ = (d * d'⁻¹) • f := by rw [← hfd, ← mul_smul, inv_mul_cancel_right]
  have hq' : (d * d'⁻¹)⁻¹ * q * (d * d'⁻¹) ∈ Q := by
    have := hQn _ (D.inv_mem he) q hq
    rwa [inv_inv] at this
  rw [hy', ← mul_smul]
  calc (q * (d * d'⁻¹)) • f = (d * d'⁻¹) • (((d * d'⁻¹)⁻¹ * q * (d * d'⁻¹)) • f) := by
        rw [← mul_smul]
        group
    _ = (d * d'⁻¹) • f := by rw [hfix _ hq']

end Group

variable {n w : Nat}

theorem toPerm_conjP {x y : Nat} (hx : PP n w x) (hy : PP n w y) :
    toPerm n w (conjP n w x y) = toPerm n w x * toPerm n w y * (toPerm n w x)⁻¹ := by
  unfold conjP
  rw [toPerm_mul hx (hy.mul hx.inv), toPerm_mul hy hx.inv, toPerm_inv hx, mul_assoc]

theorem PP_commP {x y : Nat} (hx : PP n w x) (hy : PP n w y) : PP n w (commP n w x y) :=
  (hx.mul hy).mul (hx.inv.mul hy.inv)

theorem toPerm_commP {x y : Nat} (hx : PP n w x) (hy : PP n w y) :
    toPerm n w (commP n w x y) = ⁅toPerm n w x, toPerm n w y⁆ := by
  unfold commP
  rw [toPerm_mul (hx.mul hy) (hx.inv.mul hy.inv), toPerm_mul hx hy, toPerm_mul hx.inv hy.inv,
    toPerm_inv hx, toPerm_inv hy, commutatorElement_def]
  group

theorem wordEqK_sound {D : Nat → Nat} {nd x : Nat} {ws : List Nat}
    (hsz : CFSG.KS.Raw.szOK n w = true) (hD : ∀ k < nd, PP n w (D k))
    (h : wordEqK n w D nd x ws = true) :
    toPerm n w x ∈ Subgroup.closure (gens n w D nd) := by
  unfold wordEqK at h
  rw [Bool.and_eq_true, allL_iff, Nat.beq_eq] at h
  rw [h.2]
  exact (wordK_sound hsz hD ws fun c hc => by
    have e := h.1 c hc
    rwa [Nat.blt_eq] at e).2

theorem normK_sound {M D : Nat → Nat} {nm nd : Nat} {W : List (List Nat)}
    (hsz : CFSG.KS.Raw.szOK n w = true) (hM : ∀ k < nm, PP n w (M k))
    (hD : ∀ k < nd, PP n w (D k)) (h : normK n w M nm D nd W = true) :
    ⁅Subgroup.closure (gens n w M nm), Subgroup.closure (gens n w M nm)⁆ ≤
      Subgroup.closure (gens n w D nd) := by
  unfold normK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h12, h3⟩ := h
  have e12 := fun a ha b hb => CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h12 a ha) b hb
  have e3 := fun a ha c hc => CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h3 a ha) c hc
  refine commutator_le_of_conj ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have e := e12 a ha b hb
    rw [Bool.and_eq_true] at e
    rw [← toPerm_conjP (hM a ha) (hD b hb)]
    exact wordEqK_sound hsz hD e.1
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have e := e12 a ha b hb
    rw [Bool.and_eq_true] at e
    have h := wordEqK_sound hsz hD e.2
    rw [toPerm_conjP (hM a ha).inv (hD b hb), toPerm_inv (hM a ha), inv_inv] at h
    exact h
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [← toPerm_commP (hM a ha) (hM c hc)]
    exact wordEqK_sound hsz hD (e3 a ha c hc)

theorem fix_of_oddOrbK {D : Nat → Nat} {ngen x OM : Nat} {R : List Rec}
    (hD : ∀ k < ngen, PP n w (D k)) (h : oddOrbK n w D ngen x OM R = true)
    {Q : Subgroup (Equiv.Perm (Fin n))} {k : Nat} (hQD : Q ≤ Subgroup.closure (gens n w D ngen))
    (hQn : ∀ d ∈ Subgroup.closure (gens n w D ngen), ∀ q ∈ Q, d * q * d⁻¹ ∈ Q)
    (hQ : Nat.card Q = 2 ^ k) : ∀ q ∈ Q, ∀ y ∈ ptsOf n R, q • y = y := by
  obtain ⟨hx, hodd, htr, hinv⟩ := oddOrbK_sound hD h
  exact fix_of_odd_orbit hQD hQn hQ _ ⟨x, hx⟩ htr hinv hodd

theorem eq_bot_of_checks {G GI Mg Dg : Nat → Nat} {ngen nm v x r m : Nat} {R RO : List Rec}
    {L : List (Nat × List Nat × List (List Nat) × List Rec)} {WS : List (List Nat)}
    (hsz : CFSG.KS.Raw.szOK n w = true) (hG : ∀ k < ngen, PP n w (G k)) (hv : PP n w v)
    (hcl : classK n w G GI ngen v R = true) (hr : R.length = r)
    (hm : (L.map fun lv => lv.2.2.2.length).prod = m)
    (hcard : Nat.card (Subgroup.closure (gens n w G ngen)) = r * m)
    (hMg : ∀ k < nm, PP n w (Mg k) ∧ toPerm n w (Mg k) ∈ Subgroup.closure (gens n w G ngen) ∧
      toPerm n w (Mg k) * toPerm n w v = toPerm n w v * toPerm n w (Mg k))
    (hL : stabLowK n w Mg nm L = true) (hbase : baseInK L (maskK RO) = true)
    (hW : ∀ k < 2, ∃ a b, PP n w a ∧ PP n w b ∧
      toPerm n w a ∈ Subgroup.closure (gens n w G ngen) ⊓
        Subgroup.centralizer {toPerm n w v} ∧
      toPerm n w b ∈ Subgroup.closure (gens n w G ngen) ⊓
        Subgroup.centralizer {toPerm n w v} ∧ Dg k = commP n w a b)
    (hN : normK n w Mg nm Dg 2 WS = true) (hO : oddOrbK n w Dg 2 x (maskK RO) RO = true) :
    ∀ Q : Subgroup (Equiv.Perm (Fin n)), IsPGroup 2 Q →
      Q ≤ ⁅Subgroup.closure (gens n w G ngen) ⊓ Subgroup.centralizer {toPerm n w v},
        Subgroup.closure (gens n w G ngen) ⊓ Subgroup.centralizer {toPerm n w v}⁆ →
      ⁅Subgroup.closure (gens n w G ngen) ⊓ Subgroup.centralizer {toPerm n w v},
        Subgroup.closure (gens n w G ngen) ⊓ Subgroup.centralizer {toPerm n w v}⁆ ≤
          Subgroup.normalizer (Q : Set (Equiv.Perm (Fin n))) → Q = ⊥ := by
  set P := Subgroup.closure (gens n w G ngen)
  set M := P ⊓ Subgroup.centralizer {toPerm n w v}
  set M0 := Subgroup.closure (gens n w Mg nm)
  set D := Subgroup.closure (gens n w Dg 2)
  have hMgP : ∀ k < nm, PP n w (Mg k) := fun k hk => (hMg k hk).1
  have hDgP : ∀ k < 2, PP n w (Dg k) := fun k hk => by
    obtain ⟨a, b, ha, hb, -, -, e⟩ := hW k hk
    rw [e]
    exact PP_commP ha hb
  have hM0M : M0 ≤ M := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨-, h1, h2⟩ := hMg k hk
    exact Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_centralizer_singleton_iff.2 h2⟩
  have hpos : 0 < r * m := by
    rw [← hcard]
    exact Nat.card_pos
  have hr0 : 0 < r := Nat.pos_of_mul_pos_right hpos
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hpos
  have hcM : Nat.card M ≤ m := by
    have h := card_centralizer_le_of_classK hG hv hcl
    rw [hr, hcard] at h
    exact Nat.le_of_mul_le_mul_left h hr0
  have hprod : m ≤ Nat.card M0 := hm ▸ prod_le_card_of_stabLowK hsz hMgP hL
  have hM0 : M0 = M := Subgroup.eq_of_le_of_card_ge hM0M (hcM.trans hprod)
  have hMM : ⁅M, M⁆ ≤ M := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  have hDle : D ≤ ⁅M, M⁆ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨a, b, ha, hb, haM, hbM, e⟩ := hW k hk
    rw [SetLike.mem_coe, e, toPerm_commP ha hb]
    exact Subgroup.commutator_mem_commutator haM hbM
  have hMD : ⁅M, M⁆ ≤ D := by
    rw [← hM0]
    exact normK_sound hsz hMgP hDgP hN
  have hDeq : ⁅M, M⁆ = D := le_antisymm hMD hDle
  intro Q hQ hQle hnorm
  rw [hDeq] at hQle hnorm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).1 hQ
  have hQn : ∀ d ∈ D, ∀ q ∈ Q, d * q * d⁻¹ ∈ Q := fun d hd q hq =>
    (Subgroup.mem_normalizer_iff.1 (hnorm hd) q).1 hq
  have hfix := fix_of_oddOrbK hDgP hO hQle hQn hk
  have hQM0 : Q ≤ M0 := by
    rw [hM0]
    exact hQle.trans (hDeq ▸ hMM)
  have hb := stabLowK_bound hsz hMgP hL Q hQM0 fun g hg lv hlv hb => by
    have e := allL_iff.1 hbase lv.1 (List.mem_map_of_mem hlv)
    rw [testBit_maskK] at e
    have := hfix g hg ⟨lv.1, hb⟩ (mem_ptsOf.2 e)
    rwa [Equiv.Perm.smul_def] at this
  rw [hm] at hb
  change m * Nat.card Q ≤ Nat.card M0 at hb
  rw [hM0] at hb
  have h1 : Nat.card Q ≤ 1 := by
    have h2 : m * Nat.card Q ≤ m * 1 := by
      rw [Nat.mul_one]
      exact hb.trans hcM
    exact Nat.le_of_mul_le_mul_left h2 hm0
  exact Subgroup.eq_bot_of_card_le Q h1

end CFSG.KC.PCent

end
