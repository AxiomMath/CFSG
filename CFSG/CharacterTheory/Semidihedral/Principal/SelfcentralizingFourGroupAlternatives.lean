module

public import CFSG.CharacterTheory.Semidihedral.Principal.SelfcentralizingFourGroupProjectiveFive
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.CharacterTheory.Semidihedral.CoreFreeDihedral
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Semidihedral.Principal

theorem eq_top_of_normal_simple_klein_sylow {X : Type*} [Group X] [Finite X] (L : Subgroup X)
    [L.Normal] [IsSimpleGroup L] (hLnonab : ∃ a b : L, a * b ≠ b * a) (S : Sylow 2 X)
    (hS : IsKleinFour (S : Subgroup X)) (hSL : (S : Subgroup X) ≤ L)
    (hCS : Subgroup.centralizer ((S : Subgroup X) : Set X) ≤ S) : L = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : Nat.card (S : Subgroup X) = 4 := hS.card_four
  have hScomm : ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm_of_exponent_two hS.exponent_two ⟨x, hx⟩ ⟨y, hy⟩)
  have hSC : (S : Subgroup X) ≤ Subgroup.centralizer ((S : Subgroup X) : Set X) := fun x hx y hy =>
    hScomm y hy x hx
  have hCeq : Subgroup.centralizer ((S : Subgroup X) : Set X) = S := le_antisymm hCS hSC
  set N := Subgroup.normalizer ((S : Subgroup X) : Set X) with hNdef
  have hSN : (S : Subgroup X) ≤ N := Subgroup.le_normalizer
  have hN24 : Nat.card N ∣ 24 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (S : Subgroup X).normalizerMonoidHom.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      Subgroup.normalizerMonoidHom_ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer _)).toEquiv, hCeq, h4] at h1
    have hr : Nat.card (S : Subgroup X).normalizerMonoidHom.range ∣ 6 := by
      rw [← (CFSG.Semidihedral.Local.kleinFour_automorphism_action
        (V := (S : Subgroup X))).2.1]
      exact Subgroup.card_subgroup_dvd_card _
    rw [h1]
    exact Nat.mul_dvd_mul_right hr 4
  have hNcard : Nat.card N = 4 * (S : Subgroup X).relIndex N := by
    have h := Subgroup.card_mul_index ((S : Subgroup X).subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, h4] at h
    exact h.symm
  have hodd : ¬ 2 ∣ (S : Subgroup X).relIndex N := fun h =>
    S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hSN))
  let S' : Sylow 2 L := S.subtype hSL
  have hS'map : (S' : Subgroup L).map L.subtype = S := by
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSL]
  have hS'card : Nat.card (S' : Subgroup L) = 4 := by
    rw [← h4, ← hS'map, Subgroup.card_map_of_injective L.subtype_injective]
  have hnotle : ¬ Subgroup.normalizer ((S' : Subgroup L) : Set L) ≤
      Subgroup.centralizer ((S' : Subgroup L) : Set L) := by
    intro hle
    obtain ⟨K, hKn, -, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement S' hle
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
    · rw [hK, Subgroup.index_bot] at hKidx
      have htop : (S' : Subgroup L) = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [hS'card, hKidx, hS'card])
      obtain ⟨a, b, hab⟩ := hLnonab
      apply hab
      have ha : (a : X) ∈ (S : Subgroup X) := by
        rw [← hS'map]
        exact ⟨a, htop ▸ Subgroup.mem_top a, rfl⟩
      have hb : (b : X) ∈ (S : Subgroup X) := by
        rw [← hS'map]
        exact ⟨b, htop ▸ Subgroup.mem_top b, rfl⟩
      exact Subtype.ext (hScomm _ ha _ hb)
    · rw [hK, Subgroup.index_top, hS'card] at hKidx
      norm_num at hKidx
  obtain ⟨y, hyN, hyC⟩ := Set.not_subset.mp hnotle
  have hyN' : (y : X) ∈ N := by
    have h := Subgroup.le_normalizer_map L.subtype ⟨y, hyN, rfl⟩
    rw [hS'map] at h
    exact h
  have hyS : (y : X) ∉ (S : Subgroup X) := by
    intro hy
    apply hyC
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    have hz' : (z : X) ∈ (S : Subgroup X) := by
      rw [← hS'map]
      exact ⟨z, hz, rfl⟩
    exact hScomm _ hz' _ hy
  have hNL : N ≤ L := by
    have hle : (S : Subgroup X) ≤ N ⊓ L := le_inf hSN hSL
    obtain ⟨k, hk⟩ : 4 ∣ Nat.card (N ⊓ L : Subgroup X) := h4 ▸ Subgroup.card_dvd_of_le hle
    have hdvd : Nat.card (N ⊓ L : Subgroup X) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    have hk1 : k ≠ 1 := by
      rintro rfl
      have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hk, h4])
      exact hyS (heq ▸ Subgroup.mem_inf.mpr ⟨hyN', y.2⟩)
    set m := (S : Subgroup X).relIndex N with hm
    rw [hNcard] at hN24 hdvd
    rw [hk] at hdvd
    have hm6 : m ∣ 6 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) (by simpa using hN24)
    have hkm : k ∣ m := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) hdvd
    have hm3 : m = 3 ∧ k = 3 := by
      have hmle : m ≤ 6 := Nat.le_of_dvd (by norm_num) hm6
      have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hm6)
      have hkle : k ≤ m := Nat.le_of_dvd hmpos hkm
      interval_cases m <;> interval_cases k <;> omega
    have heq : N ⊓ L = N :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hNcard, hk, hm3.1, hm3.2])
    exact heq ▸ inf_le_right
  have hF : N ⊔ L = ⊤ :=
    Sylow.normalizer_sup_eq_top' S hSL
  rwa [sup_eq_right.mpr hNL] at hF

theorem odd_core_free_selfcentralizing_four_group_involution_centralizer_three_alternatives
    {X : Type} [Group X] [Finite X] (hcore : CFSG.pPrimeCore 2 X = ⊥) (S : Sylow 2 X)
    (hS : IsKleinFour (S : Subgroup X)) (t : X) (htS : t ∈ (S : Subgroup X)) (ht1 : t ≠ 1)
    (hC : Subgroup.centralizer {t} = (S : Subgroup X)) :
    let P₁ : Prop := (S : Subgroup X) = ⊤
    let P₂ : Prop := Nonempty (X ≃* alternatingGroup (Fin 4))
    let P₃ : Prop :=
      Nat.card X = 60 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 5 1
    (P₁ ∨ P₂ ∨ P₃) ∧ ¬ (P₁ ∧ P₂) ∧ ¬ (P₁ ∧ P₃) ∧ ¬ (P₂ ∧ P₃) := by
  intro P₁ P₂ P₃
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : Nat.card (S : Subgroup X) = 4 := hS.card_four
  have hcard₁ : P₁ → Nat.card X = 4 := fun h => by
    have h' : (S : Subgroup X) = ⊤ := h
    rw [← h4, h', Subgroup.card_top]
  have hcard₂ : P₂ → Nat.card X = 12 := fun ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv, alternatingGroup.card_of_card_eq_four (by simp)]
  refine ⟨?_, fun h => by have := hcard₁ h.1; have := hcard₂ h.2; omega,
    fun h => by have := hcard₁ h.1; have := h.2.1; omega,
    fun h => by have := hcard₂ h.1; have := h.2.1; omega⟩
  have hD : Nonempty ((S : Subgroup X) ≃* DihedralGroup 2) := IsKleinFour.nonempty_mulEquiv
  obtain ⟨e⟩ := hD
  rcases CoreFreeDihedral.corefree_dihedral_generalized_fitting_alternatives hcore S 2 le_rfl e
    with h2 | hA4 | hS4 | ⟨hLs, hLnonab, -, hLsyl⟩
  ·
    exact Or.inl (S.is_maximal' (h2.to_subgroup ⊤) le_top).symm
  · exact Or.inr (Or.inl hA4)
  ·
    exfalso
    obtain ⟨e4⟩ := hS4
    have h24 : Nat.card X = 24 := by
      rw [Nat.card_congr e4.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    have hidx := Subgroup.card_mul_index (S : Subgroup X)
    rw [h4, h24] at hidx
    exact S.not_dvd_index ⟨3, by omega⟩
  right
  right
  set L := CFSG.generalizedFitting X with hLdef
  have : IsSimpleGroup L := hLs
  have : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨T⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨m, hm2, ⟨eT⟩⟩ := hLsyl T
  have hTcard : 4 ≤ Nat.card (T : Subgroup L) := by
    rw [Nat.card_congr eT.toEquiv, DihedralGroup.nat_card]
    have : 2 ≤ 2 ^ (m - 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hTp : IsPGroup 2 ((T : Subgroup L).map L.subtype) := T.isPGroup'.map _
  obtain ⟨S'', hS''⟩ := hTp.exists_le_sylow
  have hS''card : Nat.card (S'' : Subgroup X) = 4 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S, h4]
  have hTeq : (T : Subgroup L).map L.subtype = S'' :=
    Subgroup.eq_of_le_of_card_ge hS''
      (by rw [hS''card, Subgroup.card_map_of_injective L.subtype_injective]; exact hTcard)
  have hS''L : (S'' : Subgroup X) ≤ L := hTeq ▸ Subgroup.map_subtype_le _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S'' S
  have hSL : (S : Subgroup X) ≤ L := by
    intro x hx
    have hx' : x ∈ ((g • S'' : Sylow 2 X) : Subgroup X) := hg ▸ hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    have h' : g⁻¹ * x * g ∈ L :=
      hS''L (by simpa [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply] using hx')
    have h'' := (inferInstance : L.Normal).conj_mem _ h' g
    simpa [mul_assoc] using h''
  have hCS : Subgroup.centralizer ((S : Subgroup X) : Set X) ≤ S := fun x hx => by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx t htS).symm
  have hLtop : L = ⊤ := eq_top_of_normal_simple_klein_sylow L hLnonab S hS hSL hCS
  have htL : t ∈ L := hSL htS
  let SL : Sylow 2 L := S.subtype hSL
  have hSLcoe : (SL : Subgroup L) = (S : Subgroup X).subgroupOf L := Sylow.coe_subtype S hSL
  have hSLk : IsKleinFour (SL : Subgroup L) := by
    rw [hSLcoe]
    let e' := Subgroup.subgroupOfEquivOfLe hSL
    exact ⟨(Nat.card_congr e'.toEquiv).trans h4,
      (Monoid.exponent_eq_of_mulEquiv e').trans hS.exponent_two⟩
  have hCL : Subgroup.centralizer {(⟨t, htL⟩ : L)} = (SL : Subgroup L) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, hSLcoe, Subgroup.mem_subgroupOf, ← hC,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have htSL : (⟨t, htL⟩ : L) ∈ (SL : Subgroup L) := by
    rw [hSLcoe, Subgroup.mem_subgroupOf]
    exact htS
  obtain ⟨hL60, hLmodel⟩ :=
    simple_selfcentralizing_four_group_involution_centralizer_forces_projective_five hLnonab SL
      hSLk ⟨t, htL⟩ htSL (fun h => ht1 (congrArg Subtype.val h)) hCL
  let eX : X ≃* L := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)
  refine ⟨by rw [Nat.card_congr eX.toEquiv, hL60], ?_⟩
  obtain ⟨hadm, K, hK, hKfin, hKcard, ⟨eK⟩⟩ := hLmodel
  exact ⟨hadm, K, hK, hKfin, hKcard, ⟨eX.trans eK⟩⟩

end CFSG.Semidihedral.Principal
