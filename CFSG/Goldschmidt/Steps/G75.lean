module

public import CFSG.Goldschmidt.StatementsG4
import CFSG.Goldschmidt.Steps.G75Basic
import CFSG.Goldschmidt.Steps.G75Sz
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG3

public section

namespace CFSG.Goldschmidt

open CFSG.Open G75

theorem G75_of
    (h74 : S_G74) (h36 : S_G36) (h210 : S_G210) (h211 : S_G211)
    (hmult : S_GSz8Mult) : S_G75 := by
  intro G _ _ S A hset h8 hE
  obtain ⟨a, haA, ha1, H, hH, K, hK, h1, h2, h3, -, h5⟩ := h74 G S A hset h8 hE
  have hS := isSStarIn_of_mem_benderM hset haA hH
  obtain ⟨y, ⟨hyK, hyN⟩, hyodd, hytrans, hyC, hcase⟩ := h36 G H A hS hset.elem K hK
  have hAK := le_normalizer_of_isComponentOf hS hK
  have hsup := eq_sup_inf_centralizer hset.elem hAK hyK hyN hyodd hyC
  set W := A ⊓ Subgroup.centralizer (K : Set G) with hW
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h2
    omega
  have hTI : ∀ x ∈ Subgroup.normalizer (A : Set G), conjSub x W ≠ W →
      W ⊓ conjSub x W = ⊥ := by
    intro x hx hne
    by_cases hxH : x ∈ H
    · exact inf_conjSub_eq_bot hK hsup h3 hset.elem.1 hx hxH hne
    · exact h5 x hx hxH
  have hnormK : ∀ x ∈ Subgroup.normalizer (A : Set G), conjSub x W = W →
      x ∈ Subgroup.normalizer (K : Set G) := by
    intro x hx hWx
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hWne
    have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hwx : x⁻¹ * w * x ∈ W := by rw [← hWx]; exact conj_mem_conjSub hw
    have hwx1 : x⁻¹ * w * x ≠ 1 := by
      intro h
      apply hw1'
      calc w = x * (x⁻¹ * w * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hxH : x⁻¹ ∈ H := mem_of_benderM_eq hset hw1' (h1 w hw hw1')
      (by rw [inv_inv]; exact h1 _ hwx hwx1)
    have hxH' : x ∈ H := by simpa using H.inv_mem hxH
    by_contra hxK
    have h := inf_conjSub_eq_bot_of_ne hK hsup h3 hset.elem.1 hx hxH'
      (fun h => hxK (mem_normalizer_of_conjSub_eq h))
    rw [hWx, inf_idem] at h
    exact hWne h
  have hAy : y ∉ Subgroup.centralizer (A : Set G) := by
    intro hyA
    have hle : A ≤ Subgroup.centralizer ({y} : Set G) := fun b hb => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hyA b hb
    have hWA : W = A := by rw [← hyC, inf_of_le_left hle]
    rw [hWA] at h3
    have hpos : 0 < Nat.card A := Nat.card_pos
    have : Nat.card A ≤ 1 := by
      have h3' : Nat.card A * Nat.card A ≤ Nat.card A * 1 := by rw [mul_one, ← sq]; exact h3
      exact Nat.le_of_mul_le_mul_left h3' hpos
    omega
  have hON : ONanHyp A (Subgroup.normalizer (A : Set G)) y :=
    { elem := hset.elem
      le := le_rfl
      irreducible := hset.irreducible
      mem := hyN
      odd := hyodd
      not_mem := hAy
      ne_bot := by rw [hyC]; exact hWne
      trans := hytrans
      ti := by
        intro x hx hne
        rw [hyC] at hne ⊢
        exact hTI x hx hne }
  rcases hcase with ha | hb
  ·
    have hnorm : ∀ x ∈ Subgroup.normalizer (A : Set G),
        conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) =
          A ⊓ Subgroup.centralizer ({y} : Set G) →
        x⁻¹ * y * x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A : Set G) := by
      intro x hx hWx
      rw [hyC] at hWx
      have hxK := hnormK x hx hWx
      exact (sup_le_sup_left (inf_le_right : K ⊓ Subgroup.centralizer (A : Set G) ≤ _)
        (Subgroup.zpowers y)) (ha x ⟨hx, hxK⟩)
    obtain ⟨hA8, -, hidx, hnab⟩ := h211 G A (Subgroup.normalizer (A : Set G)) y hON
      (fun X₀ hX₀ _ => hset.noIndexTwo X₀ hX₀) hnorm
    refine ⟨hA8, ?_, hnab⟩
    rwa [Subgroup.inf_subgroupOf_left] at hidx
  ·
    obtain ⟨hcov, h56, -, hy7, -⟩ := hb
    exact (false_of_sz8Cover h210 hmult hset.elem hK h2 hTI hnormK hsup hyK hyN hyodd hytrans
      hyC hON hcov h56 hAy hy7).elim

end CFSG.Goldschmidt
