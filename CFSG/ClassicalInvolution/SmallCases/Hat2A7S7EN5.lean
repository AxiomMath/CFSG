module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7Coset
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic
  CFSG.StronglyEmbedded.UniqueCoset


theorem false_of_uniqueCoset_a7_F {G : Type} [Group G] [Finite G] {F : Subgroup G} [F.Normal]
    (hFs : IsSimpleGroup ↥F) (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x)
    (hFc : Subgroup.centralizer (F : Set G) = ⊥) {H : Subgroup G} {z : G} (hH : H ≠ ⊤)
    (hz : orderOf z = 2) (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    {K : Subgroup G} (hK : Hat2A7.IsClassical2A7 ⊤ K z) : False :=
  false_of_uniqueCoset_of_not_isSolvable hH hz h1 h2 hFs hFnab hFc hK.le_centralizer
    (not_isSolvable_of_isClassical2A7 hK)

theorem false_of_uniqueCoset_a7_of_sylow {G : Type} [Group G] [Finite G] {F : Subgroup G}
    [F.Normal] (hFs : IsSimpleGroup ↥F) (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x)
    (hFc : Subgroup.centralizer (F : Set G) = ⊥) {H S : Subgroup G} {z : G} (hH : H ≠ ⊤)
    (hz : orderOf z = 2)
    (hSyl : IsSylow2In (S ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2S : ∀ h : G, h⁻¹ * z * h ∈ S → h⁻¹ * z * h ≠ z → z * (h⁻¹ * z * h) = h⁻¹ * z * h * z →
      ∃! c : G ⧸ H, (z * (h⁻¹ * z * h)) • c = c)
    {K : Subgroup G} (hK : Hat2A7.IsClassical2A7 ⊤ K z) : False :=
  false_of_uniqueCoset_a7_F hFs hFnab hFc hH hz h1
    (existsUnique_fixed_mul_of_isSylow2In hz hSyl h2S) hK

end CFSG.ClassicalInvolution.Hat2A7S

namespace CFSG.ClassicalInvolution.Hat2A7E.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77


theorem e18_endS {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCex Ω K S R W H)
    (hF : ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
      Subgroup.centralizer (F : Set G) = ⊥)
    {z : G} (hz : IsUniqueInvolution K z)
    (hSyl : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (h1 : FixesUniqueCoset z H)
    (h2S : ∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) → h⁻¹ * z * h ≠ z →
      z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z → FixesUniqueCoset (z * (h⁻¹ * z * h)) H) :
    False := by
  obtain ⟨F, hFn, hFs, hFnab, hFc⟩ := hF
  have := hFn
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hK : Hat2A7.IsClassical2A7 ⊤ K z := by
    obtain ⟨u, hu⟩ := c.stand.hyp.classical K c.stand.mem
    have hu' := hu.to2A7
    rcases hz.unique u hu'.mem hu'.mul_self with h | h
    · exfalso
      have := hu'.orderOf_eq_two
      rw [h, orderOf_one] at this
      omega
    · rw [← h]
      exact hu'
  exact Hat2A7S.false_of_uniqueCoset_a7_of_sylow hFs hFnab hFc c.proper hz2 hSyl h1 h2S hK

end CFSG.ClassicalInvolution.Hat2A7E.Asc77
