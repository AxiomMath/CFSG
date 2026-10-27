module

public import CFSG.CGT.Foote82.T66.CaseIS6b
public import CFSG.CGT.Foote82.T66.CaseIF6
public import CFSG.CGT.Foote82.T66.CaseIF8
public import CFSG.CGT.Foote82.T66.CaseIS6

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart CaseIS6D8 CaseIClimbAux

section Groups

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem map_center_subgroupOf {A B : Subgroup Γ} (hAB : A ≤ B) :
    ((Subgroup.center ↥(A.subgroupOf B)).map (A.subgroupOf B).subtype).map B.subtype =
      (Subgroup.center ↥A).map A.subtype := by
  ext x
  rw [mem_map_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyA, hy'⟩ := mem_map_center_iff.1 hy
    refine ⟨Subgroup.mem_subgroupOf.1 hyA, fun a ha => ?_⟩
    exact congrArg Subtype.val (hy' ⟨a, hAB ha⟩ (Subgroup.mem_subgroupOf.2 ha))
  · rintro ⟨hxA, hx⟩
    refine ⟨⟨x, hAB hxA⟩, ?_, rfl⟩
    exact mem_map_center_iff.2 ⟨Subgroup.mem_subgroupOf.2 hxA,
      fun a ha => Subtype.ext (hx a (Subgroup.mem_subgroupOf.1 ha))⟩

theorem map_center_conj (A : Subgroup Γ) (g : Γ) :
    (Subgroup.center ↥(A.map (MulAut.conj g).toMonoidHom)).map
        (A.map (MulAut.conj g).toMonoidHom).subtype =
      ((Subgroup.center ↥A).map A.subtype).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_center_iff]
  constructor
  · rintro ⟨⟨y, hyA, rfl⟩, hx⟩
    refine ⟨y, mem_map_center_iff.2 ⟨hyA, fun a ha => ?_⟩, rfl⟩
    have h1 := hx _ ⟨a, ha, rfl⟩
    have h2 : (MulAut.conj g) (a * y) = (MulAut.conj g) (y * a) := by
      rw [map_mul, map_mul]; exact h1
    exact (MulAut.conj g).injective h2
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyA, hy'⟩ := mem_map_center_iff.1 hy
    refine ⟨⟨y, hyA, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    show (MulAut.conj g) a * (MulAut.conj g) y = (MulAut.conj g) y * (MulAut.conj g) a
    rw [← map_mul, ← map_mul, hy' a ha]

end Groups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}
variable {S : Subgroup (GLV V)}

theorem card_sylow_eq (hm : m ≤ 1) (T₀ : Sylow 2 (Perm (Fin (m + 6 + 2)))) :
    Nat.card T₀ = 128 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 T₀.isPGroup'
  have h1 := Subgroup.card_mul_index (T₀ : Subgroup (Perm (Fin (m + 6 + 2))))
  rw [Nat.card_eq_fintype_card (α := Perm (Fin (m + 6 + 2))), Fintype.card_perm,
    Fintype.card_fin] at h1
  have hodd := T₀.not_dvd_index
  have hk' : Nat.card ↥(T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) = 2 ^ k := hk
  rw [hk'] at h1
  rw [hk]
  have hpos : 0 < (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).index := Nat.pos_of_ne_zero
    (Subgroup.index_ne_zero_of_finite)
  interval_cases m
  · have e8 : Nat.factorial (0 + 6 + 2) = 40320 := by decide
    rw [e8] at h1
    have hk15 : k ≤ 15 := by
      by_contra hc
      push Not at hc
      have : 2 ^ 16 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
      have : 2 ^ k ≤ 40320 := by rw [← h1]; exact Nat.le_mul_of_pos_right _ hpos
      omega
    interval_cases k <;> omega
  · have e9 : Nat.factorial (1 + 6 + 2) = 362880 := by decide
    rw [e9] at h1
    have hk18 : k ≤ 18 := by
      by_contra hc
      push Not at hc
      have : 2 ^ 19 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
      have : 2 ^ k ≤ 362880 := by rw [← h1]; exact Nat.le_mul_of_pos_right _ hpos
      omega
    interval_cases k <;> omega

theorem SBad.false_of_le7 (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) (hm : m ≤ 1)
    (hG10 : CaseIG10) (h511 : CaseILemma511) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hext := h.std.extremal
  have hz2 := h.std.orderOf_s
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have h4 : Nat.card S = 4 := by
    have h1 := hS.card_le h
    have h2 := hS.four
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS.isP
    rw [hk] at h1 h2 ⊢
    have hk2 : k ≤ 2 := by
      by_contra hc
      push Not at hc
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
      omega
    interval_cases k <;> simp_all
  obtain ⟨s, hsS, hs4, hss, hgen⟩ := hS.exists_gen h h4
  obtain ⟨P, hPG, ⟨eP⟩, hP64, hZ4, hzZ, -⟩ := hS.exists_P h h4 hm
  set ZP := (Subgroup.center ↥P).map P.subtype with hZP
  have hZP4 : Nat.card ZP = 4 := by
    rw [hZP, Subgroup.card_map_of_injective P.subtype_injective, hZ4]
  have hbound : ∀ {Q : Subgroup (GLV V)}, Q ≤ G → (∀ q ∈ Q, q * z = z * q) → IsPGroup 2 Q →
      Nat.card Q ≤ 64 := fun hQG hQz hQ2 => hS.card_le_64 h h4 hm hQG hQz hQ2
  have h128 : 2 ^ (6 + 1) ∣ Nat.card ↥G := by
    have h1 : Nat.card H₁ = (m + 6 + 2).factorial := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
    have h2 : Nat.card H₁ ∣ Nat.card G := Subgroup.card_dvd_of_le h.H₁_le_G
    rw [h1] at h2
    refine dvd_trans ?_ h2
    interval_cases m <;> decide
  have hPGc : Nat.card (P.subgroupOf G) = 2 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, hP64]; norm_num
  obtain ⟨P', hP'card, hPP'⟩ := Sylow.exists_subgroup_card_pow_succ h128 hPGc
  set Pst := P'.map G.subtype with hPst
  have hPstG : Pst ≤ G := Subgroup.map_subtype_le _
  have hPPst : P ≤ Pst := fun x hx => ⟨⟨x, hPG hx⟩, hPP' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hPst128 : Nat.card Pst = 128 := by
    rw [hPst, Subgroup.card_map_of_injective G.subtype_injective, hP'card]; norm_num
  have hPst2 : IsPGroup 2 Pst := IsPGroup.of_card (n := 7) (by rw [hPst128]; norm_num)
  have hnc : ∃ g ∈ Pst, g * z ≠ z * g := by
    by_contra hc
    push Not at hc
    have := hbound hPstG hc hPst2
    omega
  have hG10' : ∀ g : GLV V, (∀ p ∈ Pst, g * p * g⁻¹ ∈ Pst) → ∀ c ∈ ZP, g * c * g⁻¹ ∈ ZP := by
    intro g hg c hc
    have hPgPst : P.map (MulAut.conj g).toMonoidHom ≤ Pst := by
      rintro _ ⟨p, hp, rfl⟩
      exact hg p (hPPst hp)
    have hcardP₀ : Nat.card ↥(P.subgroupOf Pst) = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPPst).toEquiv, hP64]
    have hidxP₀ : (P.subgroupOf Pst).index = 2 := by
      have := Subgroup.card_mul_index (P.subgroupOf Pst)
      rw [hcardP₀, hPst128] at this
      omega
    have hcardQ₀ : Nat.card ↥((P.map (MulAut.conj g).toMonoidHom).subgroupOf Pst) = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPgPst).toEquiv,
        Subgroup.card_map_of_injective (MulAut.conj g).injective, hP64]
    have hidxQ₀ : ((P.map (MulAut.conj g).toMonoidHom).subgroupOf Pst).index = 2 := by
      have := Subgroup.card_mul_index ((P.map (MulAut.conj g).toMonoidHom).subgroupOf Pst)
      rw [hcardQ₀, hPst128] at this
      omega
    have hisoP₀ : Nonempty (↥(P.subgroupOf Pst) ≃* DihedralGroup 4 × DihedralGroup 4) :=
      ⟨(Subgroup.subgroupOfEquivOfLe hPPst).trans eP⟩
    have hisoQ₀ : Nonempty (↥((P.map (MulAut.conj g).toMonoidHom).subgroupOf Pst) ≃*
        DihedralGroup 4 × DihedralGroup 4) :=
      ⟨((Subgroup.subgroupOfEquivOfLe hPgPst).trans
        (P.equivMapOfInjective _ (MulAut.conj g).injective).symm).trans eP⟩
    have hact : ∃ x : ↥Pst, ∃ c ∈ Subgroup.center ↥(P.subgroupOf Pst),
        x * (c : ↥Pst) ≠ (c : ↥Pst) * x := by
      obtain ⟨g', hg'P, hg'z⟩ := hnc
      have hzP : z ∈ P := (mem_map_center_iff.1 hzZ).1
      refine ⟨⟨g', hg'P⟩, ⟨⟨z, hPPst hzP⟩, Subgroup.mem_subgroupOf.2 hzP⟩, ?_, ?_⟩
      · rw [Subgroup.mem_center_iff]
        intro w
        apply Subtype.ext
        apply Subtype.ext
        exact (mem_map_center_iff.1 hzZ).2 _ (Subgroup.mem_subgroupOf.1 w.2)
      · intro he
        exact hg'z (congrArg Subtype.val he)
    have hcent := hG10 ↥Pst (P.subgroupOf Pst) ((P.map (MulAut.conj g).toMonoidHom).subgroupOf Pst)
      hPst128 hidxP₀ hisoP₀ hact hidxQ₀ hisoQ₀
    have h1 := congrArg (fun K : Subgroup ↥Pst => K.map Pst.subtype) hcent
    rw [map_center_subgroupOf hPgPst, map_center_subgroupOf hPPst, map_center_conj] at h1
    rw [hZP, ← h1]
    exact ⟨c, hc, rfl⟩
  have hnormZ : ∀ g : GLV V, (∀ p ∈ Pst, g * p * g⁻¹ ∈ Pst) →
      (∀ p ∈ Pst, g⁻¹ * p * g ∈ Pst) → g ∈ Subgroup.normalizer (ZP : Set (GLV V)) := by
    intro g hg hg'
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hG10' g hg c
    · intro hc
      have := hG10' g⁻¹ (by simpa using hg') _ hc
      simpa [mul_assoc] using this
  have hmax : ∀ Q₂ : Subgroup (GLV V), Q₂ ≤ G → IsPGroup 2 Q₂ → Pst ≤ Q₂ → Q₂ = Pst := by
    intro Q₂ hQ₂G hQ₂ hle
    by_contra hne
    haveI : Group.IsNilpotent ↥Q₂ := hQ₂.isNilpotent
    set Pst' : Subgroup ↥Q₂ := Pst.subgroupOf Q₂ with hPst'
    have hlt : Pst' < ⊤ := by
      refine lt_of_le_of_ne le_top fun he => hne ?_
      apply le_antisymm _ hle
      intro q hq
      have : (⟨q, hq⟩ : ↥Q₂) ∈ Pst' := by rw [he]; trivial
      exact Subgroup.mem_subgroupOf.1 this
    obtain ⟨g, hgN, hgP⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent Pst' hlt)
    have hg1 : ∀ p ∈ Pst, (g : GLV V) * p * (g : GLV V)⁻¹ ∈ Pst := by
      intro p hp
      have := (Subgroup.mem_normalizer_iff.1 hgN ⟨p, hle hp⟩).1 (Subgroup.mem_subgroupOf.2 hp)
      exact Subgroup.mem_subgroupOf.1 this
    have hg2 : ∀ p ∈ Pst, (g : GLV V)⁻¹ * p * (g : GLV V) ∈ Pst := by
      intro p hp
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgN) ⟨p, hle hp⟩).1
        (Subgroup.mem_subgroupOf.2 hp)
      simpa using Subgroup.mem_subgroupOf.1 this
    set Y := Pst ⊔ Subgroup.zpowers (g : GLV V) with hY
    have hYQ : Y ≤ Q₂ := sup_le hle (Subgroup.zpowers_le.2 g.2)
    have hY2 : IsPGroup 2 Y := hQ₂.to_le hYQ
    have hYN : Y ≤ Subgroup.normalizer (ZP : Set (GLV V)) :=
      sup_le (fun p hp => hnormZ p (fun q hq => Pst.mul_mem (Pst.mul_mem hp hq) (Pst.inv_mem hp))
        (fun q hq => Pst.mul_mem (Pst.mul_mem (Pst.inv_mem hp) hq) hp))
        (Subgroup.zpowers_le.2 (hnormZ _ hg1 hg2))
    have hYZ : ∀ y ∈ Y, y * z * y⁻¹ ∈ ZP := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 (hYN hy) z).1 hzZ
    have hc := card_le_two_mul_of_conj_mem hY2 hZP4 hzZ hz1 hYZ
    have hC := hbound (le_trans inf_le_left (hYQ.trans hQ₂G))
      (fun q hq => Subgroup.mem_centralizer_singleton_iff.1 hq.2) (hY2.to_le inf_le_left)
    have hYcard : Nat.card Y ≤ 128 := by omega
    have hYeq : Pst = Y := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hPst128]; exact hYcard)
    apply hgP
    rw [Subgroup.mem_subgroupOf, hYeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hPst_odd : ¬ 2 ∣ Pst.relIndex G := by
    have hP' : IsPGroup 2 (Pst.subgroupOf G) := hPst2.comap_subtype
    obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
    have hS'map : (S' : Subgroup ↥G).map G.subtype = Pst := by
      refine hmax _ (Subgroup.map_subtype_le _) (S'.isPGroup'.map _) ?_
      intro x hx
      exact ⟨⟨x, hPstG hx⟩, hS' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hS'eq : (S' : Subgroup ↥G) = Pst.subgroupOf G := by
      rw [← hS'map]
      exact (Subgroup.comap_map_eq_self_of_injective G.subtype_injective _).symm
    rw [Subgroup.relIndex, ← hS'eq]
    exact S'.not_dvd_index
  obtain ⟨T₀, hzT, hyT⟩ := exists_sylow_T₀ (m := m)
  set T := (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ) with hT
  have hT128 : Nat.card T = 128 := by
    rw [hT, Subgroup.card_map_of_injective pe_injective]
    exact card_sylow_eq hm T₀
  have hT_odd : ¬ 2 ∣ T.relIndex G := by
    have e1 := Subgroup.relIndex_mul_card T G
    rw [inf_eq_left.2 (h.T_le_G _), hT128] at e1
    have e2 := Subgroup.relIndex_mul_card Pst G
    rw [inf_eq_left.2 hPstG, hPst128] at e2
    have : T.relIndex G = Pst.relIndex G := by omega
    rw [this]
    exact hPst_odd
  have h4K : 4 ∣ Nat.card (KK G L) := by rw [← h4]; exact Subgroup.card_dvd_of_le hS.le
  obtain ⟨-, hGq⟩ := h.std.quasisimple h4K
  have hLcomp : IsComponentOf L (G ⊓ Subgroup.centralizer {z}) := by
    have := h.setup6.component
    rwa [centralizer_zpowers_eq] at this
  have hk : m + 6 = 6 ∨ m + 6 = 7 := by omega
  have hGn : (G.subgroupOf G).Normal := by rw [Subgroup.subgroupOf_self]; infer_instance
  have hrel : G.relIndex G ≤ 2 := by rw [Subgroup.relIndex_self]; norm_num
  have hcen : G ⊓ Subgroup.centralizer (G : Set (GLV V)) ≤
      (Subgroup.center ↥G).map G.subtype := by
    intro x hx
    exact mem_map_center_iff.2 ⟨hx.1, fun a ha => Subgroup.mem_centralizer_iff.1 hx.2 a ha⟩
  have hoddZ : Odd (Nat.card ↥(Subgroup.center ↥G)) := by
    have h1 := hext.setup.odd_card_center
    have h2 : (Subgroup.center ↥G).map G.subtype ≤ G ⊓ Subgroup.centralizer (G : Set (GLV V)) := by
      intro x hx
      obtain ⟨hxG, hx'⟩ := mem_map_center_iff.1 hx
      exact ⟨hxG, Subgroup.mem_centralizer_iff.2 hx'⟩
    have h3 := Odd.of_dvd_nat h1 (Subgroup.card_dvd_of_le h2)
    rwa [Subgroup.card_map_of_injective G.subtype_injective] at h3
  obtain ⟨ha511, -⟩ := h511 V G G L z (m + 6) (eL h) le_rfl hGn hrel hGq hoddZ hcen
    hext.setup.irr h.z_mem_G hz2 hLcomp hk h.isAltNaturalModule_L
    (fun c hc => h.finrank_eq_two c hc)
  have hsyl : ∃ (m' : ℕ) (P'' : Subgroup ↥G) (Q : Subgroup (Equiv.Perm (Fin m'))),
      (m' = 8 ∨ m' = 9) ∧ IsPGroup 2 P'' ∧ ¬ 2 ∣ P''.index ∧ IsPGroup 2 Q ∧ ¬ 2 ∣ Q.index ∧
        Nonempty (↥P'' ≃* ↥Q) :=
    ⟨m + 6 + 2, T.subgroupOf G, T₀, by omega, (T₀.isPGroup'.map _).comap_subtype, hT_odd,
      T₀.isPGroup', T₀.not_dvd_index,
      ⟨(Subgroup.subgroupOfEquivOfLe (h.T_le_G _)).trans
        ((T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).equivMapOfInjective _ pe_injective).symm⟩⟩
  have hLG : L ≤ G := h.L_le_H.trans h.H_le_G
  have key : ∀ M : ℕ, (M = 10 ∨ M = 11) → (↥G ≃* alternatingGroup (Fin M)) → False := by
    intro M hM φ
    obtain ⟨τ, hττ, h5, hτL⟩ := exists_altOn_fix (Γ := GLV V) (Hb := G) (E := G) (Lb := L)
      (r := z) (by omega) φ le_rfl Subgroup.le_normalizer h.zz h.z_mem_G h.setup6.component hLG
    set F : Set (Fin M) := {i | τ i = i} with hF
    have hcardL : Nat.card L = (m + 6).factorial / 2 := by
      obtain ⟨eL'⟩ := h.L_equiv
      exact (Nat.card_congr eL'.toEquiv).trans (card_altGroup (by omega))
    have hcardA : Nat.card ↥(altOn F) = (m + 6).factorial / 2 := by
      rw [← hτL, Subgroup.card_map_of_injective (Subtype.val_injective.comp φ.injective),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLG).toEquiv, hcardL]
    have h2 := two_mul_card_altOn F (by omega)
    rw [hcardA, Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) (by omega))] at h2
    have hFc : Nat.card F = m + 6 := (Nat.factorial_inj (by omega)).1 h2.symm
    have hsum := Set.ncard_add_ncard_compl F
    rw [← Nat.card_coe_set_eq, hFc, Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
    have hsupp : Fᶜ = (τ.support : Set (Fin M)) := by
      ext i
      simp [hF, Equiv.Perm.mem_support]
    rw [hsupp, Set.ncard_coe_finset] at hsum
    obtain ⟨hs, -⟩ := card_support_of_mul_self hττ
    have hsupp4 : τ.support.card = 4 := by omega
    set φ' : ↥G →* Perm (Fin M) := (alternatingGroup (Fin M)).subtype.comp φ.toMonoidHom
      with hφ'
    have hsG : s ∈ G := (hS.le hsS).1
    set σ := φ' ⟨s, hsG⟩ with hσ
    have hσfix : ∀ i ∈ F, σ i = i := by
      intro i hi
      refine fixes_of_commute_altOn (F := F) h5 (fun k hk => ?_) hi
      rw [← hτL] at hk
      obtain ⟨l, hl, rfl⟩ := hk
      rw [hσ, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 (hS.le hsS).2 _ (Subgroup.mem_subgroupOf.1 hl)).symm
    have hσsupp : σ.support ⊆ τ.support := by
      intro i hi
      rw [Perm.mem_support] at hi ⊢
      intro hτi
      exact hi (hσfix i hτi)
    have hσ4 : orderOf σ = 4 := by
      rw [hσ, orderOf_injective φ' (Subtype.val_injective.comp φ.injective),
        Subgroup.orderOf_mk, hs4]
    have hsign := sign_eq_neg_one_of_orderOf_eq_four hσ4
      ((Finset.card_le_card hσsupp).trans hsupp4.le)
    have hA : σ ∈ alternatingGroup (Fin M) := (φ ⟨s, hsG⟩).2
    rw [Equiv.Perm.mem_alternatingGroup, hsign] at hA
    exact absurd hA (by decide)
  rcases ha511 hsyl with he10 | he11
  · obtain ⟨e10⟩ := he10
    exact key 10 (Or.inl rfl) e10
  · obtain ⟨e11⟩ := he11
    exact key 11 (Or.inr rfl) e11

theorem Hyp.smallK_of_le (h : Hyp G L z v H₁ m ψ) (hm : m ≤ 1) (hG10 : CaseIG10)
    (h511 : CaseILemma511) :
    ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2 := by
  intro Q hQK hQ
  by_contra hc
  push Not at hc
  obtain ⟨S, hS⟩ := h.exists_sBad ⟨Q, hQK, hQ, hc⟩
  exact hS.false_of_le7 h hm hG10 h511

end CaseIAux

end CFSG.CGT.Foote82
