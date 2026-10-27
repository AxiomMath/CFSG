module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_RedDefs
import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

set_option linter.unusedSectionVars false

section CaseJK

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {x : Q}

theorem Triple113.cjk_conj_B (Tr : Triple113 B L x) {g : Q} (hg : g ∈ B) :
    ∃ n : ℕ, n < 3 ∧ GLBConj g L = GLBConj (x ^ n) L := by
  set N := Subgroup.normalizer (L : Set Q) with hN
  have hnorm : (N.subgroupOf B).Normal := ⟨fun n hn g => by
    have : ((g * n * g⁻¹ : B) : Q) = (n : Q) := by
      have h := Tr.comm_B g.2 n.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h]; group
    rw [Subgroup.mem_subgroupOf, this]
    exact hn⟩
  have hidx : (N.subgroupOf B).index = 3 := Tr.index
  have hcard : Nat.card (B ⧸ N.subgroupOf B) = 3 := by
    rw [← hidx, Subgroup.index_eq_card]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact Tr.not_mem h
  have htop := zpowers_eq_top_of_prime_card hcard hx1
  have hg' : (QuotientGroup.mk (⟨g, hg⟩ : B) : B ⧸ N.subgroupOf B) ∈
      Subgroup.zpowers (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B) := by
    rw [htop]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg'
  have hx3 : (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B) ^ 3 = 1 := by
    rw [← hcard]; exact pow_card_eq_one'
  have e := zpow_eq_zpow_emod' (x := (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B))
    k hx3
  have hr : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
  have key : ∀ n : ℕ, n < 3 →
      (QuotientGroup.mk (⟨x, Tr.mem⟩ : B) : B ⧸ N.subgroupOf B) ^ n =
        (QuotientGroup.mk (⟨g, hg⟩ : B) : B ⧸ N.subgroupOf B) → GLBConj g L = GLBConj (x ^ n) L := by
    intro n hn hnk
    have hq : (QuotientGroup.mk (⟨x ^ n, B.pow_mem Tr.mem n⟩ : B) : B ⧸ N.subgroupOf B) =
        QuotientGroup.mk (⟨g, hg⟩ : B) := by
      rw [← hnk]; rfl
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
    have hq' : (x ^ n)⁻¹ * g ∈ N := hq
    have hc : (x ^ n) * g = g * (x ^ n) := Tr.comm_B (B.pow_mem Tr.mem n) hg
    have hgeq : g = ((x ^ n)⁻¹ * g) * x ^ n := by
      calc g = (x ^ n)⁻¹ * (x ^ n * g) := by group
        _ = (x ^ n)⁻¹ * (g * x ^ n) := by rw [hc]
        _ = _ := by group
    have h1 : GLBConj ((x ^ n)⁻¹ * g) L = L := mem_normalizer_iff_gLBConj_eq.1 hq'
    calc GLBConj g L = GLBConj (((x ^ n)⁻¹ * g) * x ^ n) L := by rw [← hgeq]
      _ = GLBConj (x ^ n) (GLBConj ((x ^ n)⁻¹ * g) L) := (gLBConj_gLBConj _ _ _).symm
      _ = GLBConj (x ^ n) L := by rw [h1]
  rcases hr with h | h | h
  · refine ⟨0, by norm_num, key 0 (by norm_num) ?_⟩
    rw [← hk, e, h]; simp
  · refine ⟨1, by norm_num, key 1 (by norm_num) ?_⟩
    rw [← hk, e, h]; simp
  · refine ⟨2, by norm_num, key 2 (by norm_num) ?_⟩
    rw [← hk, e, h]; simp

@[expose] def cjkC (L : Subgroup Q) (x : Q) (i : Fin 3) : Subgroup Q := GLBConj (x ^ (i : ℕ)) L

theorem Triple113.cjkC_succ (Tr : Triple113 B L x) (i : Fin 3) :
    GLBConj x (cjkC L x i) = cjkC L x (i + 1) := by
  unfold cjkC
  rw [gLBConj_gLBConj]
  fin_cases i
  · simp
  · simp [pow_two]
  · have h3 : x ^ 2 * x = x ^ 3 := by group
    have := mem_normalizer_iff_gLBConj_eq.1 Tr.pow_three_mem
    show GLBConj (x ^ 2 * x) L = GLBConj (x ^ 0) L
    rw [h3, this, pow_zero, gLBConj_one]

theorem Triple113.cjkC_pred (Tr : Triple113 B L x) (i : Fin 3) :
    GLBConj x⁻¹ (cjkC L x i) = cjkC L x (i - 1) := by
  have h := Tr.cjkC_succ (i - 1)
  rw [sub_add_cancel] at h
  rw [← h, gLBConj_inv_gLBConj]

theorem cjkC_zero (L : Subgroup Q) (x : Q) : cjkC L x 0 = L := by
  simp [cjkC, gLBConj_one]

theorem cjkC_one (L : Subgroup Q) (x : Q) : cjkC L x 1 = GLBConj x L := by
  simp [cjkC]

theorem cjkC_two (L : Subgroup Q) (x : Q) : cjkC L x 2 = GLBConj (x ^ 2) L := by
  simp [cjkC]

theorem Triple113.cjkC_inj (Tr : Triple113 B L x) {i j : Fin 3} (h : cjkC L x i = cjkC L x j) :
    i = j := by
  have h1 := Tr.conj1_ne
  have h2 := Tr.conj2_ne
  have h21 := Tr.conj21_ne
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | (exfalso
       simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, cjkC_zero, cjkC_one,
         cjkC_two] at h
       first | exact h1 h | exact h1 h.symm | exact h2 h | exact h2 h.symm | exact h21 h | exact h21 h.symm)

theorem cjk_conj_mem_conj {g : Q} {L : Subgroup Q} {l : Q} (hl : l ∈ L) :
    g⁻¹ * l * g ∈ GLBConj g L := by
  rw [mem_gLBConj]
  simpa [mul_assoc] using hl

theorem Triple113.cjk_mem_of_normalizes (Tr : Triple113 B L x) {t : Q}
    (ht : t ∈ Subgroup.normalizer (t113K B L : Set Q)) (i : Fin 3) :
    ∃ j : Fin 3, GLBConj t (cjkC L x i) = cjkC L x j := by
  have hMeq : GLBConj t (cjkC L x i) = GLBConj (x ^ (i : ℕ) * t) L := by
    unfold cjkC; rw [gLBConj_gLBConj]
  have hMcomp : IsComponentOf (GLBConj (x ^ (i : ℕ) * t) L) ⊤ := Tr.comp_conj _
  have hMK : GLBConj (x ^ (i : ℕ) * t) L ≤ t113K B L := by
    intro z hz
    rw [mem_gLBConj] at hz
    have h1 := Tr.conj_le_K (B.pow_mem Tr.mem (i : ℕ))
      (cjk_conj_mem_conj (g := x ^ (i : ℕ)) hz)
    have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ht) _).1 h1
    have hk : z = t⁻¹ * ((x ^ (i : ℕ))⁻¹ * (x ^ (i : ℕ) * t * z * (x ^ (i : ℕ) * t)⁻¹) *
        x ^ (i : ℕ)) * t := by group
    rw [hk]
    simpa using h2
  have hex : ∃ g ∈ B, GLBConj (x ^ (i : ℕ) * t) L = GLBConj g L := by
    by_contra hno
    push Not at hno
    have hcomm : ∀ g ∈ B, ∀ u ∈ GLBConj (x ^ (i : ℕ) * t) L, ∀ w ∈ GLBConj g L,
        u * w = w * u := by
      intro g hg
      rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hMcomp (Tr.comp_conj g) with h | h
      · exact absurd h (hno g hg)
      · exact h
    have hcK : ∀ u ∈ GLBConj (x ^ (i : ℕ) * t) L, ∀ w ∈ t113K B L, u * w = w * u := by
      intro u hu
      have hle : t113K B L ≤ Subgroup.centralizer ({u} : Set Q) := by
        refine iSup₂_le fun g hg w hw => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm g hg u hu w hw).symm
      intro w hw
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hw)).symm
    have hbot : ∀ u ∈ GLBConj (x ^ (i : ℕ) * t) L, u = 1 := fun u hu =>
      Tr.eq_one_of_central hu fun w hw => hcK u hu w (hMK hw)
    have hL : ∀ l ∈ L, l = 1 := by
      intro l hl
      have h := hbot _ (cjk_conj_mem_conj (g := x ^ (i : ℕ) * t) hl)
      calc l = (x ^ (i : ℕ) * t) * ((x ^ (i : ℕ) * t)⁻¹ * l * (x ^ (i : ℕ) * t)) *
          (x ^ (i : ℕ) * t)⁻¹ := by group
        _ = 1 := by rw [h]; group
    apply Tr.not_mem
    refine t113_mem_normalizer_of_commute fun j hj => ?_
    rw [hL j hj]; simp
  obtain ⟨g, hg, hMg⟩ := hex
  obtain ⟨n, hn, hgn⟩ := Tr.cjk_conj_B hg
  exact ⟨⟨n, hn⟩, by rw [hMeq, hMg, hgn]; rfl⟩

theorem cjk_perm_aux (f : Fin 3 → Fin 3) (h1 : ∀ i, f (f i) = i)
    (h2 : ∀ i, (fun j => f (j + 1) - 1) (f i) = f ((fun j => f (j + 1) - 1) i)) :
    ∀ i, f i = i := by
  revert f
  decide

theorem Triple113.cjk_le_normalizer (Tr : Triple113 B L x) {T : Subgroup Q}
    (hTK : T ≤ Subgroup.normalizer (t113K B L : Set Q))
    (hTB : B ≤ Subgroup.normalizer (T : Set Q)) (hTe : IsElemAbelian 2 T) :
    T ≤ Subgroup.normalizer (L : Set Q) := by
  intro t ht
  have hex : ∀ s ∈ T, ∃ f : Fin 3 → Fin 3, ∀ i, GLBConj s (cjkC L x i) = cjkC L x (f i) := by
    intro s hs
    choose f hf using fun i => Tr.cjk_mem_of_normalizes (hTK hs) i
    exact ⟨f, hf⟩
  obtain ⟨f, hf⟩ := hex t ht
  have ht' : x * t * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hTB Tr.mem) t).1 ht
  obtain ⟨f', hf'⟩ := hex _ ht'
  have hff : ∀ i, f (f i) = i := by
    intro i
    have h : GLBConj t (GLBConj t (cjkC L x i)) = cjkC L x i := by
      rw [gLBConj_gLBConj, ← pow_two, hTe.2 t ht, gLBConj_one]
    rw [hf, hf] at h
    exact Tr.cjkC_inj h
  have hf'eq : ∀ i, f' i = f (i + 1) - 1 := by
    intro i
    have h : GLBConj (x * t * x⁻¹) (cjkC L x i) =
        GLBConj x⁻¹ (GLBConj t (GLBConj x (cjkC L x i))) := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_assoc]
    rw [hf', Tr.cjkC_succ, hf, Tr.cjkC_pred] at h
    exact Tr.cjkC_inj h
  have hcomm : ∀ i, f' (f i) = f (f' i) := by
    intro i
    have hc : t * (x * t * x⁻¹) = (x * t * x⁻¹) * t := by
      have := hTe.1.is_comm.comm (⟨t, ht⟩ : T) ⟨x * t * x⁻¹, ht'⟩
      exact congrArg Subtype.val this
    have h : GLBConj (x * t * x⁻¹) (GLBConj t (cjkC L x i)) =
        GLBConj t (GLBConj (x * t * x⁻¹) (cjkC L x i)) := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj, hc]
    rw [hf, hf', hf', hf] at h
    exact Tr.cjkC_inj h
  have h0 := cjk_perm_aux f hff (fun i => by
    have := hcomm i
    simp only [hf'eq] at this
    exact this) 0
  have h1 := hf 0
  rw [h0, cjkC_zero] at h1
  exact mem_normalizer_iff_gLBConj_eq.2 h1

theorem cjk_le_centralizer {T : Subgroup Q}
    (hTB : B ≤ Subgroup.normalizer (T : Set Q))
    (htriv : ∀ t ∈ T, ∀ l ∈ L, t * l = l * t) :
    T ≤ Subgroup.centralizer (t113K B L : Set Q) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hle : t113K B L ≤ Subgroup.centralizer ({t} : Set Q) := by
    refine iSup₂_le fun g hg w hw => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ht' : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hTB hg) t).1 ht
    have h := htriv _ ht' _ (mem_gLBConj.1 hw)
    calc w * t = g⁻¹ * ((g * w * g⁻¹) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (g * w * g⁻¹)) * g := by rw [← h]
      _ = t * w := by group
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)

theorem Triple113.cjk_Y12_comm_L (Tr : Triple113 B L x) {y : Q} (hy : y ∈ L) :
    ∀ z ∈ t113Y12 x y, ∀ l ∈ L, z * l = l * z := by
  intro z hz l hl
  have hle : t113Y12 x y ≤ Subgroup.centralizer ({l} : Set Q) := by
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Tr.comm01 l hl _ (Tr.conj1_mem hy)).symm
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Tr.comm02 l hl _ (Tr.conj2_mem hy)).symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz)

theorem cjk_mem_normalizer_zpowers {u e : Q} (h : e * u = u * e) :
    e ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup Q) : Set Q) :=
  t113_mem_normalizer_of_commute fun j hj => by
    obtain ⟨n, rfl⟩ := hj
    exact (Commute.zpow_right (show Commute e u from h) n).eq

theorem Triple113.cjk_normalizes (Tr : Triple113 B L x) {a : Q} (ha : a ∈ t113A B L)
    (S1 : Subgroup ↥L) (hS : S1.map (t113Rho B L ⟨a, ha⟩).toMonoidHom = S1) :
    a ∈ Subgroup.normalizer ((S1.map L.subtype : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨s, hs, rfl⟩
    have h1 : t113Rho B L ⟨a, ha⟩ s ∈ S1 := by
      rw [← hS]; exact Subgroup.mem_map_of_mem _ hs
    exact ⟨_, h1, (Tr.rho_apply ⟨a, ha⟩ s)⟩
  · rintro ⟨u, hu, hue⟩
    rw [← hS] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hu
    have hue' : a * (v : Q) * a⁻¹ = a * h * a⁻¹ := by
      rw [← hue]; exact (Tr.rho_apply ⟨a, ha⟩ v).symm
    have : (v : Q) = h := mul_left_cancel (mul_right_cancel hue')
    exact ⟨v, hv, this⟩

theorem caseJK113_of_tables (Tb : Tables113) : CaseJK113 := by
  intro Q _ _ B L x T R hTK
  have Tr : Triple113 B L x := R.tri
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h2L, h3L, -⟩ := Tb.T0 ↥L R.isL2
  have hB0pos : 0 < Nat.card (t113B0 B L) := Nat.card_pos
  have hcardB := Tr.card_B
  have hKB : t113K B L ≤ (⨆ g ∈ B, GLBConj g L) ⊔ B := le_sup_left
  have hBle : B ≤ (⨆ g ∈ B, GLBConj g L) ⊔ B := le_sup_right
  have hTN : T ≤ Subgroup.normalizer (L : Set Q) := Tr.cjk_le_normalizer hTK R.T_norm R.T_elem
  obtain ⟨ρT, hρT⟩ : ∃ ρT : ↥T →* MulAut ↥L, ∀ (t : ↥T) (l : ↥L),
      ((ρT t l : ↥L) : Q) = (t : Q) * l * (t : Q)⁻¹ :=
    ⟨L.normalizerMonoidHom.comp (Subgroup.inclusion hTN), fun _ _ => rfl⟩
  have hS2 : IsPGroup 2 ρT.range :=
    IsPGroup.of_surjective R.T_two ρT.rangeRestrict ρT.rangeRestrict_surjective
  have hSne : ρT.range ≠ ⊥ := by
    intro h
    apply R.T_ne
    refine R.hR1 T R.T_two R.T_norm (cjk_le_centralizer R.T_norm ?_)
    intro t ht l hl
    have h1 : ρT ⟨t, ht⟩ ∈ ρT.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : Q)) h1
    simp only [MulAut.one_apply] at h2
    rw [hρT] at h2
    calc t * l = (t * l * t⁻¹) * t := by group
      _ = l * t := by rw [h2]
  have hHN : t113H B L ≤ Subgroup.normalizer ((ρT.range : Subgroup (MulAut ↥L)) : Set (MulAut ↥L)) := by
    have key : ∀ β ∈ t113H B L, ∀ s ∈ ρT.range, β * s * β⁻¹ ∈ ρT.range := by
      rintro β ⟨a, rfl⟩ s ⟨t, rfl⟩
      have hmem : (a : Q) * t * (a : Q)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.1 (R.T_norm a.2.2) t).1 t.2
      refine ⟨⟨(a : Q) * t * (a : Q)⁻¹, hmem⟩, ?_⟩
      apply MulEquiv.ext
      intro l
      apply Subtype.ext
      have hm : (a : Q) * (((t113Rho B L a)⁻¹ l : ↥L) : Q) * (a : Q)⁻¹ = (l : Q) := by
        have h0 : (t113Rho B L a) ((t113Rho B L a)⁻¹ l) = l :=
          (t113Rho B L a).apply_symm_apply l
        have := congrArg Subtype.val h0
        rwa [Tr.rho_apply] at this
      rw [hρT]
      show _ = ((t113Rho B L a (ρT t ((t113Rho B L a)⁻¹ l)) : ↥L) : Q)
      rw [Tr.rho_apply, hρT]
      rw [← hm]
      group
    intro β hβ
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · exact key β hβ s
    · intro h
      have := key β⁻¹ (Subgroup.inv_mem _ hβ) _ h
      simpa [mul_assoc] using this
  obtain ⟨hH3, hHin⟩ := Tb.T3 ↥L R.isL2 (t113H B L) ρT.range Tr.H_elem hS2 hSne hHN
  obtain ⟨y0', hy0'⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  have hy0L : (y0' : Q) ∈ L := y0'.2
  have hy0o : orderOf (y0' : Q) = 3 := by rw [Subgroup.orderOf_coe, hy0']
  obtain ⟨u', hu'⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2L
  have huL : (u' : Q) ∈ L := u'.2
  have huo : orderOf (u' : Q) = 2 := by rw [Subgroup.orderOf_coe, hu']
  obtain ⟨eY, cY, hYK, hYB0⟩ := Tr.Y12_spec hy0L hy0o
  have hE1 : IsElemAbelian 3 (t113B0 B L ⊔ t113Y12 x (y0' : Q)) ∧
      Nat.card ↥(t113B0 B L ⊔ t113Y12 x (y0' : Q)) = Nat.card (t113B0 B L) * 9 := by
    have hi : t113B0 B L ⊓ t113Y12 x (y0' : Q) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      exact hYB0 z hz.2 hz.1
    obtain ⟨h1, h2⟩ := t113_sup_elemAbelian Tr.B0_elem eY
      (fun p hp r hr => (Tr.B0_comm_K hp r (hYK hr)).symm) hi
    exact ⟨h1, by rw [h2, cY]⟩
  have hS0two : IsPGroup 2 (Subgroup.zpowers (u' : Q)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huo]; simp)
  have hS0ne : Subgroup.zpowers (u' : Q) ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at huo
    omega
  have hE1N : t113B0 B L ⊔ t113Y12 x (y0' : Q) ≤
      Subgroup.normalizer ((Subgroup.zpowers (u' : Q) : Subgroup Q) : Set Q) := by
    refine sup_le (fun b hb => ?_) (fun z hz => ?_)
    · exact cjk_mem_normalizer_zpowers (Tr.B0_comm_K hb _ (Tr.L_le_K huL)).symm
    · exact cjk_mem_normalizer_zpowers (Tr.cjk_Y12_comm_L hy0L z hz _ huL)
  have hE1le : t113B0 B L ⊔ t113Y12 x (y0' : Q) ≤ (⨆ g ∈ B, GLBConj g L) ⊔ B :=
    sup_le ((inf_le_left : t113B0 B L ≤ B).trans hBle) (hYK.trans hKB)
  have h3 : 3 ≤ Nat.card (t113H B L) := by
    have := R.hmax _ hE1.1 ⟨_, hS0ne, hS0two, hE1N⟩
    rw [hE1.2, hcardB] at this
    by_contra hlt
    push Not at hlt
    nlinarith
  have hH : Nat.card (t113H B L) = 3 := le_antisymm hH3 h3
  obtain ⟨α, hαH, hα1⟩ : ∃ α ∈ t113H B L, α ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : t113H B L = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at hH
    omega
  have hαout : α ∉ innerAut113 ↥L := by
    intro hin
    have : α ∈ t113H B L ⊓ innerAut113 ↥L := ⟨hαH, hin⟩
    rw [hHin, Subgroup.mem_bot] at this
    exact hα1 this
  obtain ⟨⟨a, ha⟩, rfl⟩ := hαH
  have hα3 : t113Rho B L ⟨a, ha⟩ ^ 3 = 1 := Tr.H_elem.2 _ ⟨⟨a, ha⟩, rfl⟩
  have hαo : orderOf (t113Rho B L ⟨a, ha⟩) = 3 := orderOf_eq_prime hα3 hα1
  obtain ⟨⟨y', hy'o, hy'fix⟩, S1, hS1ne, hS1two, hS1⟩ := Tb.T4 ↥L R.isL2 _ hαo hαout
  have hyL : (y' : Q) ∈ L := y'.2
  have hyo : orderOf (y' : Q) = 3 := by rw [Subgroup.orderOf_coe, hy'o]
  have hay : a * (y' : Q) = (y' : Q) * a := by
    have h := congrArg Subtype.val hy'fix
    have e : ((t113Rho B L ⟨a, ha⟩ y' : ↥L) : Q) = a * (y' : Q) * a⁻¹ := rfl
    rw [e] at h
    calc a * (y' : Q) = (a * (y' : Q) * a⁻¹) * a := by group
      _ = (y' : Q) * a := by rw [h]
  obtain ⟨eY2, cY2, hYK2, hYB02⟩ := Tr.Y12_spec hyL hyo
  obtain ⟨eF, cF, hFB, hFY⟩ := Tr.F_spec ha hαout
  have hE2 : IsElemAbelian 3 ((Subgroup.zpowers a ⊔ t113B0 B L) ⊔ t113Y12 x (y' : Q)) ∧
      Nat.card ↥((Subgroup.zpowers a ⊔ t113B0 B L) ⊔ t113Y12 x (y' : Q)) =
        3 * Nat.card (t113B0 B L) * 9 := by
    have hi : (Subgroup.zpowers a ⊔ t113B0 B L) ⊓ t113Y12 x (y' : Q) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      exact hFY _ hYK2 hYB02 z hz.1 hz.2
    have hFy : ∀ f ∈ Subgroup.zpowers a ⊔ t113B0 B L, f * (y' : Q) = (y' : Q) * f := by
      have hle : Subgroup.zpowers a ⊔ t113B0 B L ≤ Subgroup.centralizer ({(y' : Q)} : Set Q) := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (fun b hb => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]; exact hay
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Tr.B0_comm_K hb _ (Tr.L_le_K hyL)).symm
      intro f hf
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hf))
    obtain ⟨h1, h2⟩ := t113_sup_elemAbelian eF eY2
      (fun f hf z hz => Tr.Y12_comm (hFB hf) (hFy f hf) z hz) hi
    exact ⟨h1, by rw [h2, cF, cY2]⟩
  have hS1'two : IsPGroup 2 (S1.map L.subtype) :=
    IsPGroup.of_surjective hS1two
      (Subgroup.equivMapOfInjective S1 L.subtype L.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective S1 L.subtype L.subtype_injective).surjective
  have hS1'ne : S1.map L.subtype ≠ ⊥ := fun h =>
    hS1ne ((Subgroup.map_eq_bot_iff_of_injective S1 L.subtype_injective).1 h)
  have hS1'L : ∀ j ∈ S1.map L.subtype, j ∈ L := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hE2N : (Subgroup.zpowers a ⊔ t113B0 B L) ⊔ t113Y12 x (y' : Q) ≤
      Subgroup.normalizer ((S1.map L.subtype : Subgroup Q) : Set Q) := by
    refine sup_le (sup_le (Subgroup.zpowers_le.2 (Tr.cjk_normalizes ha S1 hS1)) (fun b hb => ?_))
      (fun z hz => ?_)
    · exact t113_mem_normalizer_of_commute fun j hj =>
        (Tr.B0_comm_K hb j (Tr.L_le_K (hS1'L j hj))).symm
    · exact t113_mem_normalizer_of_commute fun j hj =>
        (Tr.cjk_Y12_comm_L hyL z hz j (hS1'L j hj))
  have hE2le : (Subgroup.zpowers a ⊔ t113B0 B L) ⊔ t113Y12 x (y' : Q) ≤
      (⨆ g ∈ B, GLBConj g L) ⊔ B :=
    sup_le (hFB.trans hBle) (hYK2.trans hKB)
  have := R.hmax _ hE2.1 ⟨_, hS1'ne, hS1'two, hE2N⟩
  rw [hE2.2, hcardB, hH] at this
  nlinarith

end CaseJK

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
