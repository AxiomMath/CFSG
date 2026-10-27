module

public import CFSG.CGT.L5R.L2InputsL
public import CFSG.CGT.M24R.L2Sub

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.CGT.M24R

theorem card_le_of_forall_mem {K : Type*} [Group K] [Finite K] {S : Subgroup K} {L : List K}
    (h : ∀ y ∈ S, y ∈ L) : Nat.card S ≤ L.length := by
  classical
  have hsub : (S : Set K) ⊆ (L.toFinset : Set K) := fun y hy => by simpa using h y hy
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  calc (S : Set K).ncard ≤ (L.toFinset : Set K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ ≤ L.length := List.toFinset_card_le L

theorem comm_of_sq {K : Type*} [Group K] {S : Subgroup K} (hexp : ∀ x ∈ S, x * x = 1) {a b : K}
    (ha : a ∈ S) (hb : b ∈ S) : a * b = b * a := by
  have h1 := hexp _ (S.mul_mem ha hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by
      rw [inv_eq_of_mul_eq_one_right (hexp a ha), inv_eq_of_mul_eq_one_right (hexp b hb)]

section FB

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem candL_of_mem {B' : Subgroup N8} {P : Table} {p : N8} (hP : IsTab P p)
    (hPs : P.size = 16) (hp : p ∈ B') (hp1 : p ≠ 1) (hexp : ∀ x ∈ B', x * x = 1)
    (hbot : B' ⊓ T8 = ⊥)
    (hcomm : ∀ a ∈ T8 ⊓ Subgroup.normalizer (B' : Set N8), ∀ x ∈ B', a * x = x * a)
    (hcent : ∀ b ∈ B', b ≠ 1 → ∀ y : N8, y * b = b * y →
      y ∈ Subgroup.normalizer (B' : Set N8))
    {X : Table} {x : N8} (hX : IsTab X x) (hXs : X.size = 16) (hx : x ∈ B') (hx1 : x ≠ 1)
    (hxp : x ≠ p) : candL (mkCtx ()) P X = true := by
  have hnT : ∀ y ∈ B', y ≠ 1 → y ∉ T8 := by
    intro y hy hy1 hyT
    have : y ∈ B' ⊓ T8 := ⟨hy, hyT⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hy1 this
  have hpat : ∀ y ∈ B', y ≠ 1 → ∀ t ∈ T8,
      (y * t = t * y ↔ t ∈ T8 ⊓ Subgroup.normalizer (B' : Set N8)) := by
    intro y hy hy1 t ht
    constructor
    · intro h
      exact ⟨ht, hcent y hy hy1 t h.symm⟩
    · intro h
      exact (hcomm t h y hy).symm
  have hpx1 : p * x ≠ 1 := by
    intro h
    apply hxp
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (hexp p hp)]
  simp only [candL, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ((hX.mul hX).beq_iff hcard IsTab.one (compT_size _ _) idT_size).2 (hexp x hx)
  · exact (hX.commT_iff hcard hP).2 (comm_of_sq hexp hx hp)
  · rw [Bool.eq_false_iff]
    intro h
    exact hnT x hx hx1 ((isTt_iff hcard hX hXs).1 h)
  · rw [Bool.eq_false_iff]
    intro h
    exact hxp ((hX.beq_iff hcard hP hXs hPs).1 h)
  · rw [Bool.eq_false_iff]
    intro h
    exact hnT _ (B'.mul_mem hp hx) hpx1 ((isTt_iff hcard (hP.mul hX) (compT_size _ _)).1 h)
  · intro k hk
    have ht := isTab_tt hk
    rw [beq_iff_eq, Bool.eq_iff_iff, ht.commT_iff hcard hX, ht.commT_iff hcard hP]
    rw [eq_comm, hpat x hx hx1 _ (n8_tw_mem k), eq_comm (a := n8 (tw k) * p),
      hpat p hp hp1 _ (n8_tw_mem k)]

end FB

end CFSG.CGT.L5R
