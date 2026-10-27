module

public import CFSG.GroupActions.PrimitiveNormalTransitive
public import CFSG.GroupActions.StabilizerFactorization
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.GroupActions

theorem isSimpleGroup_of_preprimitive_of_coprime_generator_orders
    {G Ω : Type*} [Group G] [Finite G] [Finite Ω]
    [MulAction G Ω] [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    (hΩ : 2 ≤ Nat.card Ω) (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (ω : Ω)
    (hab : (orderOf a).Coprime (orderOf b))
    (hst : (orderOf (a * b)).Coprime (Nat.card (MulAction.stabilizer G ω))) :
    IsSimpleGroup G := by
  classical
  let _ : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (Nat.lt_of_succ_le hΩ)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  have hg_ne : g ≠ 1 := by
    intro h
    apply hxy
    simpa [h] using hg
  let _ : Nontrivial G := ⟨⟨g, 1, hg_ne⟩⟩
  rw [isSimpleGroup_iff]
  refine ⟨inferInstance, ?_⟩
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  let _ : N.Normal := hN
  let _ : MulAction.IsPretransitive N Ω := isPretransitive_of_normal_ne_bot N hNbot
  let φ : G →* G ⧸ N := QuotientGroup.mk' N
  have hcard : Nat.card (G ⧸ N) ∣ Nat.card (MulAction.stabilizer G ω) :=
    quotient_card_dvd_stabilizer_card N ω
  have hprod : φ (a * b) = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes hst (orderOf_map_dvd φ (a * b))
      ((orderOf_dvd_natCard (φ (a * b))).trans hcard)
  have hinv : φ a = (φ b)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa using hprod
  have ha : φ a = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hab (orderOf_map_dvd φ a)
    rw [hinv, orderOf_inv]
    exact orderOf_map_dvd φ b
  have hb : φ b = 1 := by
    simpa [map_mul, ha] using hprod
  have haN : a ∈ N := (QuotientGroup.eq_one_iff a).mp ha
  have hbN : b ∈ N := (QuotientGroup.eq_one_iff b).mp hb
  apply top_le_iff.mp
  rw [← hgen]
  apply (Subgroup.closure_le N).mpr
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact haN
  · exact hbN

end CFSG.GroupActions
