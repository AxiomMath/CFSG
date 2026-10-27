module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCard

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

theorem natCard_of_isQ8D8Type {X : Type} [Group X] (h : IsQ8D8Type X) :
    Nat.card X = 32 := by
  classical
  obtain ⟨Q, E, ⟨eQ⟩, ⟨eE⟩, hcomm, hsup, hcardQE⟩ := h
  have hQcard : Nat.card ↥Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hEcard : Nat.card ↥E = 8 := by
    rw [Nat.card_congr eE.toEquiv, DihedralGroup.nat_card]
  let φ : ↥Q × ↥E →* X :=
    { toFun := fun p => (p.1 : X) * (p.2 : X)
      map_one' := by simp
      map_mul' := by
        rintro ⟨q₁, e₁⟩ ⟨q₂, e₂⟩
        change ((q₁ : X) * (q₂ : X)) * ((e₁ : X) * (e₂ : X)) =
          ((q₁ : X) * (e₁ : X)) * ((q₂ : X) * (e₂ : X))
        calc
          ((q₁ : X) * (q₂ : X)) * ((e₁ : X) * (e₂ : X))
              = (q₁ : X) * ((q₂ : X) * (e₁ : X)) * (e₂ : X) := by group
          _ = (q₁ : X) * ((e₁ : X) * (q₂ : X)) * (e₂ : X) := by
              rw [hcomm q₂ q₂.2 e₁ e₁.2]
          _ = ((q₁ : X) * (e₁ : X)) * ((q₂ : X) * (e₂ : X)) := by group }
  have hQle : Q ≤ φ.range := by
    intro q hq
    exact ⟨(⟨q, hq⟩, 1), by simp [φ]⟩
  have hEle : E ≤ φ.range := by
    intro e he
    exact ⟨(1, ⟨e, he⟩), by simp [φ]⟩
  have hrange : φ.range = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le hQle hEle
  have hker : Nat.card ↥φ.ker = 2 := by
    rw [← hcardQE]
    let f : ↥φ.ker → ↥(Q ⊓ E) := fun x =>
      ⟨(x.1.1 : X), by
        refine Subgroup.mem_inf.mpr ⟨x.1.1.2, ?_⟩
        have hx : φ x.1 = 1 := x.2
        have h : (x.1.1 : X) = (x.1.2 : X)⁻¹ := eq_inv_of_mul_eq_one_left hx
        rw [h]
        exact E.inv_mem x.1.2.2⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      have hqval : (x.1.1 : X) = (y.1.1 : X) :=
        congrArg (fun z : ↥(Q ⊓ E) => (z : X)) hxy
      have hq : x.1.1 = y.1.1 := Subtype.ext hqval
      have hx : (x.1.1 : X) = (x.1.2 : X)⁻¹ :=
        eq_inv_of_mul_eq_one_left (x.2 : φ x.1 = 1)
      have hy : (y.1.1 : X) = (y.1.2 : X)⁻¹ :=
        eq_inv_of_mul_eq_one_left (y.2 : φ y.1 = 1)
      have he : (x.1.2 : X) = (y.1.2 : X) := by
        calc
          (x.1.2 : X) = ((x.1.1 : X))⁻¹ := by rw [hx, inv_inv]
          _ = ((y.1.1 : X))⁻¹ := by rw [hqval]
          _ = (y.1.2 : X) := by rw [hy, inv_inv]
      exact Subtype.ext (Prod.ext hq (Subtype.ext he))
    have hsurj : Function.Surjective f := by
      intro z
      obtain ⟨hzQ, hzE⟩ := Subgroup.mem_inf.mp z.2
      refine ⟨⟨(⟨(z : X), hzQ⟩, ⟨(z : X)⁻¹, E.inv_mem hzE⟩), ?_⟩, ?_⟩
      · show (z : X) * (z : X)⁻¹ = 1
        exact mul_inv_cancel (z : X)
      · apply Subtype.ext
        rfl
    exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  have hprod : Nat.card (↥Q × ↥E) = 64 := by
    rw [Nat.card_prod, hQcard, hEcard]
  have hmain := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Subgroup.card_top, hprod] at hmain
  omega

theorem natCard_of_isExtNotation_alternating_five_q8d8 {Y : Type} [Group Y]
    (h : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) Y) : Nat.card Y = 1920 := by
  obtain ⟨N, hN, hBN, hAN, -⟩ := h
  haveI := hN
  obtain ⟨e⟩ := hAN
  have hA5 : Nat.card (Y ⧸ N) = 60 := by
    rw [Nat.card_congr e.toEquiv, natCard_alternatingGroup_fin 5 (by norm_num)]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hA5,
    natCard_of_isQ8D8Type hBN]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
