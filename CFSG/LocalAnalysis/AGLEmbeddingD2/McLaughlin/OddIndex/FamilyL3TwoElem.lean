module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyTwoSub

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open scoped commutatorElement
open Matrix CFSG.SL2MinimalFaithful CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section TwoGroups

variable {F : Type} [Field F] [Finite F]

theorem sl2_two_group_comm (hF : 2 ∣ Nat.card F) {R : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hR : IsPGroup 2 R) : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨p, f, hp, hf, hcard⟩ := (isPrimePow_nat_iff _).1 (FiniteField.isPrimePow_card F)
  have hFc : Nat.card F = p ^ f := by
    rw [Nat.card_eq_fintype_card]
    exact hcard.symm
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow (hFc ▸ hF))).symm
  subst hp2
  have hU₀ : Nat.card (unipotentHom (F := F)).range = Nat.card F :=
    (Nat.card_congr (MonoidHom.ofInjective unipotentHom_injective).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  have hU₀p : IsPGroup 2 (unipotentHom (F := F)).range := IsPGroup.of_card (hU₀.trans hFc)
  have hind : ¬ 2 ∣ (unipotentHom (F := F)).range.index := by
    intro hdvd
    have hmul := (unipotentHom (F := F)).range.card_mul_index
    rw [hU₀, card_specialLinearGroup_fin_two] at hmul
    have hind : (unipotentHom (F := F)).range.index = Nat.card F ^ 2 - 1 := by
      have hq : 1 < Nat.card F := Finite.one_lt_card
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by have := Finite.one_lt_card (α := F); omega)
    have h2' : 2 ∣ Nat.card F ^ 2 - 1 + 1 := by
      rw [Nat.sub_add_cancel h1]
      exact dvd_pow hF two_ne_zero
    rw [hind] at hdvd
    have := (Nat.dvd_add_right hdvd).mp h2'
    omega
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) F)
    (hU₀p.toSylow hind) S
  have key : ∀ a ∈ R, ∃ t : F, g⁻¹ * a * g = unipotent t := by
    intro a ha
    have haS : a ∈ ((S : Sylow 2 _) : Subgroup (SpecialLinearGroup (Fin 2) F)) := hRS ha
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      IsPGroup.toSylow_coe] at haS
    obtain ⟨m, hm⟩ := haS
    refine ⟨Multiplicative.toAdd m, ?_⟩
    have hconj : (MulAut.conj g)⁻¹ • a = g⁻¹ * a * g := by
      simp [MulAut.smul_def]
    rw [← hconj, ← hm]
    rfl
  intro a ha b hb
  obtain ⟨s, hs⟩ := key a ha
  obtain ⟨t, ht⟩ := key b hb
  have hcomm : (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by
    rw [hs, ht, ← unipotent_add, ← unipotent_add, add_comm]
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
    _ = b * a := by group

theorem gl2_two_group_comm (hF : 2 ∣ Nat.card F) {R : Subgroup (GL (Fin 2) F)}
    (hR : IsPGroup 2 R) : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdet : ∀ g ∈ R, GeneralLinearGroup.det g = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := hR ⟨g, hg⟩
    have h1 : (GeneralLinearGroup.det g) ^ 2 ^ k = 1 := by
      have : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [← map_pow, this, map_one]
    have hd1 : orderOf (GeneralLinearGroup.det g) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have hd2 : orderOf (GeneralLinearGroup.det g) ∣ Nat.card Fˣ := orderOf_dvd_natCard _
    have hodd : Odd (Nat.card Fˣ) := by
      rw [Nat.card_units]
      obtain ⟨c, hc⟩ := hF
      have hpos : 0 < Nat.card F := Nat.card_pos
      exact ⟨c - 1, by omega⟩
    have hcop : Nat.Coprime (2 ^ k) (Nat.card Fˣ) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hmemSL : ∀ g ∈ R, ∃ A : SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.toGL A = g := by
    intro g hg
    refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) F), ?_⟩, ?_⟩
    · have := congrArg Units.val (hdet g hg)
      simpa using this
    · ext
      rfl
  have hS : IsPGroup 2 (R.comap (Matrix.SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)) :=
    hR.comap_of_ker_isPGroup _ (IsPGroup.ker_isPGroup_of_injective
      Matrix.SpecialLinearGroup.toGL_injective)
  intro a ha b hb
  obtain ⟨A, rfl⟩ := hmemSL a ha
  obtain ⟨B, rfl⟩ := hmemSL b hb
  rw [← map_mul, ← map_mul, sl2_two_group_comm hF hS A ha B hb]

end TwoGroups

theorem exists_two_subgroup_comm_not_mem_pCore {K : Type} [Group K] [Finite K]
    {Y : Subgroup K} (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    ∃ R : Subgroup ↥Y, IsPGroup 2 R ∧ ∃ a ∈ R, ∃ b ∈ R, ⁅a, b⁆ ∉ CFSG.pCore 2 ↥Y := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  let S₀ : Sylow 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) := default
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_sylow_of_isLThreeTwo hY S₀
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) b
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  refine ⟨(S₀ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)),
    IsPGroup.comap_of_ker_isPGroup S₀.isPGroup' _ hker, a', ha, b', hb, fun hc => hab ?_⟩
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ⁅a', b'⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hc
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem two_subgroup_comm_of_odd_index {G H : Type} [Group G] [Finite G] [Group H]
    {T : Subgroup G} (hT : ¬ 2 ∣ T.index) (ρ : ↥T →* H) (hρ : Function.Injective ρ)
    (hH : ∀ Q : Subgroup H, IsPGroup 2 Q → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    {R : Subgroup G} (hR : IsPGroup 2 R) : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ST : Sylow 2 ↥T := default
  let S' : Subgroup G := (ST : Subgroup ↥T).map T.subtype
  have hcardS' : Nat.card S' = Nat.card ST :=
    Nat.card_congr ((ST : Subgroup ↥T).equivMapOfInjective T.subtype T.subtype_injective).symm.toEquiv
  have hmul : Nat.card G = Nat.card T * T.index := (T.card_mul_index).symm
  have hfac : (Nat.card G).factorization 2 = (Nat.card T).factorization 2 := by
    rw [hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
    simp [Nat.factorization_eq_zero_of_not_dvd hT]
  have hS'card : Nat.card S' = 2 ^ (Nat.card G).factorization 2 := by
    rw [hcardS', Sylow.card_eq_multiplicity, hfac]
  let SG : Sylow 2 G := Sylow.ofCard S' hS'card
  have hS'c : ∀ x ∈ S', ∀ y ∈ S', x * y = y * x := by
    rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
    have hc := hH ((ST : Subgroup ↥T).map ρ) (ST.isPGroup'.map ρ) (ρ x') ⟨x', hx', rfl⟩ (ρ y')
      ⟨y', hy', rfl⟩
    have : x' * y' = y' * x' := hρ (by rw [map_mul, map_mul]; exact hc)
    exact congrArg Subtype.val this
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SG S
  have key : ∀ c ∈ R, g⁻¹ * c * g ∈ S' := by
    intro c hc
    have hcS : c ∈ ((S : Sylow 2 G) : Subgroup G) := hRS hc
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Sylow.coe_ofCard] at hcS
    have hconj : (MulAut.conj g)⁻¹ • c = g⁻¹ * c * g := by
      simp [MulAut.smul_def]
    rwa [hconj] at hcS
  intro a ha b hb
  have hcomm := hS'c _ (key a ha) _ (key b hb)
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
    _ = b * a := by group

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
