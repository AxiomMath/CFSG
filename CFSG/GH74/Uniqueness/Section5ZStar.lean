module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.Lemma33b
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section ZStar5

variable {X : Type} [Group X] [Finite X] {Z : Set X}

theorem two_le_pRank_zHull_of_commuting (hZ : IsInvariantInvolutionSet Z) {A : Subgroup X}
    {y z : X} (hy : y ∈ Z) (hyA : y ∈ A) (hz : z ∈ Z) (hzA : z ∈ A) (hne : y ≠ z)
    (hyz : y * z = z * y) : 2 ≤ Open.pRank 2 (zHull Z A) := by
  have hzz : z ∈ zHull Z A := Subgroup.subset_closure ⟨hz, hzA⟩
  have hyy : y ∈ zHull Z A := Subgroup.subset_closure ⟨hy, hyA⟩
  have h2 : 2 ≤ Open.twoRank ↥(zHull Z A) :=
    CFSG.TwoRankLowerBound.Helpers.two_le_twoRank_of_commuting_involutions _ ⟨z, hzz⟩ ⟨y, hyy⟩
      (by rw [Subgroup.orderOf_mk]; exact hZ.1 z hz) (by rw [Subgroup.orderOf_mk]; exact hZ.1 y hy)
      (fun hh => hne (congrArg Subtype.val hh).symm) (Subtype.ext hyz.symm)
  have h3 := CFSG.SectionRank.pRank_le_map Nat.one_lt_two (zHull Z A).subtype
    Subtype.val_injective (⊤ : Subgroup ↥(zHull Z A))
  have h4 : (⊤ : Subgroup ↥(zHull Z A)).map (zHull Z A).subtype = zHull Z A := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h4] at h3
  exact h2.trans h3

theorem eq_of_commute_of_pRank_zHull_le_one (hZ : IsInvariantInvolutionSet Z) {A : Subgroup X}
    (hA : Open.pRank 2 (zHull Z A) ≤ 1) {y z : X} (hy : y ∈ Z) (hyA : y ∈ A) (hz : z ∈ Z)
    (hzA : z ∈ A) (hyz : y * z = z * y) : y = z := by
  by_contra hne
  have := two_le_pRank_zHull_of_commuting hZ hy hyA hz hzA hne hyz
  omega

theorem exists_mem_conj_of_isolated (hZ : IsInvariantInvolutionSet Z) {A : Subgroup X} {z : X}
    (hz : z ∈ Z) (hzA : z ∈ A) (hiso : ∀ y ∈ Z, y ∈ A → y * z = z * y → y = z) {y : X}
    (hy : y ∈ Z) (hyA : y ∈ A) : ∃ a ∈ A, a⁻¹ * z * a = y := by
  have hz2 := hZ.mul_self_eq_one hz
  have hy2 := hZ.mul_self_eq_one hy
  have hodd : Odd (orderOf (z * y)) := by
    by_contra hnot
    have heven : Even (orderOf (z * y)) := Nat.not_odd_iff_even.mp hnot
    obtain ⟨m, hm⟩ := heven
    have hmpos : 0 < m := by
      have := orderOf_pos (z * y)
      omega
    obtain ⟨hv2, hv1, hzv, -, x, hxcl, hx⟩ := dihedral_even hz2 hy2 hmpos (by rw [hm]; ring)
    set v := (z * y) ^ m with hv
    have hvA : v ∈ A := A.pow_mem (A.mul_mem hzA hyA) m
    have hzvZ : z * v ∈ Z := by
      rcases hx with h1 | h1
      · rw [← h1]
        exact hZ.2 z hz x
      · rw [← h1]
        exact hZ.2 y hy x
    have hcomm : (z * v) * z = z * (z * v) := by
      calc (z * v) * z = z * (v * z) := by rw [mul_assoc]
        _ = z * (z * v) := by rw [← hzv]
    have heq := hiso (z * v) hzvZ (A.mul_mem hzA hvA) hcomm
    exact hv1 (by simpa using heq)
  obtain ⟨x, hxcl, hx⟩ := exists_mem_closure_conj_of_odd hz2 hy2 hodd
  have hclA : Subgroup.closure ({z, y} : Set X) ≤ A :=
    (Subgroup.closure_le _).mpr (by
      intro w hw
      rcases hw with rfl | rfl
      · exact hzA
      · exact hyA)
  refine ⟨x⁻¹, A.inv_mem (hclA hxcl), ?_⟩
  rw [inv_inv]
  calc x * z * x⁻¹ = x * (x⁻¹ * y * x) * x⁻¹ := by rw [hx]
    _ = y := by group

theorem isZStarIn_of_isolated (hZ : IsInvariantInvolutionSet Z) {A : Subgroup X} {z : X}
    (hz : z ∈ Z) (hzA : z ∈ A) (hiso : ∀ y ∈ Z, y ∈ A → y * z = z * y → y = z) :
    IsZStarIn A z := by
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  have hz1 : z ≠ 1 := by
    intro h1
    have := hZ.1 z hz
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have : Fintype ↥A := Fintype.ofFinite _
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar ↥A ⟨z, hzA⟩
    (fun h => hz1 (congrArg Subtype.val h)) (Subtype.ext hz2) (by
      intro g hg
      have hyZ : (g : X) * z * (g : X)⁻¹ ∈ Z := by
        have := hZ.2 z hz (g : X)⁻¹
        simpa using this
      have hyA : (g : X) * z * (g : X)⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem g.2 hzA) (A.inv_mem g.2)
      exact Subtype.ext (hiso _ hyZ hyA (congrArg Subtype.val hg)))
  have hsub : (N.map A.subtype).subgroupOf A = N :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective N
  refine ⟨hzA, N.map A.subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
  · rw [hsub]
    exact hNn
  · rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hNodd
  · intro m hm
    refine ⟨⟨m * z * m⁻¹ * z⁻¹, A.mul_mem (A.mul_mem (A.mul_mem hm hzA) (A.inv_mem hm))
      (A.inv_mem hzA)⟩, ?_, rfl⟩
    exact hN ⟨m, hm⟩

theorem isZStarIn_of_pRank_zHull_le_one (hZ : IsInvariantInvolutionSet Z) {A : Subgroup X}
    (hA : Open.pRank 2 (zHull Z A) ≤ 1) {z : X} (hz : z ∈ Z) (hzA : z ∈ A) : IsZStarIn A z :=
  isZStarIn_of_isolated hZ hz hzA (fun _ hy hyA hyz =>
    eq_of_commute_of_pRank_zHull_le_one hZ hA hy hyA hz hzA hyz)

omit [Finite X] in
theorem mul_inv_mem_of_isZStarIn {A K : Subgroup X} {z : X}
    (hK : ∀ m ∈ A, m * z * m⁻¹ * z⁻¹ ∈ K) {y : X} (hy : ∃ a ∈ A, a⁻¹ * z * a = y) :
    y * z⁻¹ ∈ K := by
  obtain ⟨a, ha, rfl⟩ := hy
  have := hK a⁻¹ (A.inv_mem ha)
  simpa using this

theorem exists_odd_normal_of_isolated (hZ : IsInvariantInvolutionSet Z) {A : Subgroup X} {z : X}
    (hz : z ∈ Z) (hzA : z ∈ A) (hiso : ∀ y ∈ Z, y ∈ A → y * z = z * y → y = z) :
    ∃ K : Subgroup X, K ≤ A ∧ (K.subgroupOf A).Normal ∧ Odd (Nat.card K) ∧
      (∀ m ∈ A, m * z * m⁻¹ * z⁻¹ ∈ K) ∧
      ∀ y ∈ Z, y ∈ A → (∃ a ∈ A, a⁻¹ * z * a = y) ∧ y * z⁻¹ ∈ K := by
  obtain ⟨-, K, hKA, hKn, hKodd, hK⟩ := isZStarIn_of_isolated hZ hz hzA hiso
  refine ⟨K, hKA, hKn, hKodd, hK, fun y hy hyA => ?_⟩
  have hc := exists_mem_conj_of_isolated hZ hz hzA hiso hy hyA
  exact ⟨hc, mul_inv_mem_of_isZStarIn hK hc⟩

end ZStar5

end CFSG.GH74.Uniqueness
