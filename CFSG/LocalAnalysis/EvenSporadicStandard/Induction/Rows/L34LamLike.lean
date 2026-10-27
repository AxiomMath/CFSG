module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.LamLike2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34CoverProfile

public section

namespace CFSG.EvenSporadicStandard.L34Q8

open CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78 Subgroup

variable {K : Type} [Group K] {α : MulAut K}

theorem mul_comm_of_forall_sq {X : Type*} [Group X] {P : Subgroup X} (h : ∀ x ∈ P, x * x = 1)
    {x y : X} (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  have hxy : x * y * (x * y) = 1 := h _ (P.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

theorem not_lamLike_of_nonsolvable (h : ¬ Group.IsSolvable ↥(fixSubgroup α)) (b : ℕ) :
    ¬ LamLike b ↥(fixSubgroup α) ∧ ¬ LamLike b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
      ¬ LamLike2 b ↥(fixSubgroup α) ∧
      ¬ LamLike2 b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) := by
  have h1 : ¬ LamLike b ↥(fixSubgroup α) := fun hl => h hl.1
  have h2 : ¬ LamLike2 b ↥(fixSubgroup α) := fun hl => h hl.1
  exact ⟨h1, fun hl => h1 (hl.of_injective (inl_injective' _ _)), h2,
    fun hl => h2 (hl.of_injective (inl_injective' _ _))⟩

theorem not_lamLike_of_nonabelian (h : NonabelianTwoIn α) (b : ℕ) :
    ¬ LamLike b ↥(fixSubgroup α) ∧ ¬ LamLike b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
      ¬ LamLike2 b ↥(fixSubgroup α) ∧
      ¬ LamLike2 b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) := by
  obtain ⟨P, hPf, hP2, p, hp, q, hq, hpq⟩ := h
  let P' : Subgroup ↥(fixSubgroup α) := P.subgroupOf (fixSubgroup α)
  have hP' : IsPGroup 2 P' := hP2.comap_subtype
  have hp' : (⟨p, hPf p hp⟩ : ↥(fixSubgroup α)) ∈ P' := hp
  have hq' : (⟨q, hPf q hq⟩ : ↥(fixSubgroup α)) ∈ P' := hq
  have hne : (⟨p, hPf p hp⟩ : ↥(fixSubgroup α)) * ⟨q, hPf q hq⟩ ≠
      ⟨q, hPf q hq⟩ * ⟨p, hPf p hp⟩ := fun e => hpq (congrArg Subtype.val e)
  have h1 : ¬ LamLike b ↥(fixSubgroup α) := fun hl => hne (hl.2.1 P' hP' _ hp' _ hq')
  have h2 : ¬ LamLike2 b ↥(fixSubgroup α) := fun hl =>
    hne (mul_comm_of_forall_sq (hl.2 P' hP').1 hp' hq')
  exact ⟨h1, fun hl => h1 (hl.of_injective (inl_injective' _ _)), h2,
    fun hl => h2 (hl.of_injective (inl_injective' _ _))⟩

theorem not_lamLike2_eight_of_orderEight [Finite K] (h : OrderEightIn α) :
    ¬ LamLike2 8 (↥(fixSubgroup α) × Multiplicative (ZMod 2)) := by
  obtain ⟨P, hPf, hP2, hPc⟩ := h
  let P' : Subgroup ↥(fixSubgroup α) := P.subgroupOf (fixSubgroup α)
  have hle : P ≤ fixSubgroup α := hPf
  have hcard' : Nat.card P' = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hPc]
  let Q : Subgroup (↥(fixSubgroup α) × Multiplicative (ZMod 2)) :=
    P'.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))
  have hQcard : Nat.card Q = 16 := by
    rw [Nat.card_congr (Subgroup.prodEquiv P' (⊤ : Subgroup (Multiplicative (ZMod 2)))).toEquiv,
      Nat.card_prod, hcard', Subgroup.card_top]
    have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card 2
    rw [this]
  intro hl
  have := (hl.2 Q (IsPGroup.of_card (n := 4) (by rw [hQcard]; norm_num))).2
  omega

theorem not_lamLike_four_of_elemFour [Finite K] (h : ElemFourIn α) :
    ¬ LamLike 4 (↥(fixSubgroup α) × Multiplicative (ZMod 2)) := by
  obtain ⟨E, hEf, hEsq, hEc, hE4⟩ := h
  let E' : Subgroup ↥(fixSubgroup α) := E.subgroupOf (fixSubgroup α)
  have hle : E ≤ fixSubgroup α := hEf
  have hcard' : 4 ≤ Nat.card E' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hE4
  let Q : Subgroup (↥(fixSubgroup α) × Multiplicative (ZMod 2)) :=
    E'.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))
  have hQcard : Nat.card Q = Nat.card E' * 2 := by
    rw [Nat.card_congr (Subgroup.prodEquiv E' (⊤ : Subgroup (Multiplicative (ZMod 2)))).toEquiv,
      Nat.card_prod, Subgroup.card_top]
    have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card 2
    rw [this]
  intro hl
  have hZ2 : ∀ t : Multiplicative (ZMod 2), t * t = 1 := by decide
  have hsq : ∀ x ∈ Q, x * x = 1 := by
    rintro ⟨e, t⟩ ⟨he, -⟩
    have h1 : e * e = 1 := Subtype.ext (hEsq e he)
    exact Prod.ext h1 (hZ2 t)
  have hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    rintro ⟨e, t⟩ ⟨he, -⟩ ⟨f, s⟩ ⟨hf, -⟩
    have h1 : e * f = f * e := Subtype.ext (hEc e he f hf)
    have h2 : t * s = s * t := mul_comm t s
    exact Prod.ext h1 h2
  have := hl.2.2 Q hsq hcomm
  omega

end CFSG.EvenSporadicStandard.L34Q8
