module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Twist
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Tower
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ComponentClassification.HSFLit.Sec5H

open Sec8

@[expose] def mR : TwData 3 where
  qmulT := 1673236465891068964647157294543140572111398587903436834440
  qinvT := 12306056
  actT :=
    93147698238093040243760848110073386055825254729997505896946901080747116081680 + 2 ^ 256 *
    (99932287442226494482229386224930055817241604771358242631796538698913667097360)
  cocT := 44046506503220586675653207336702889942699699921689156213796984541643341299712

theorem mR_valid : mR.Valid where
  qmul_assoc := by decide +kernel
  qone_mul := by decide +kernel
  qmul_one := by decide +kernel
  qinv_mul := by decide +kernel
  act_ex := by decide +kernel
  act_one := by decide +kernel
  act_mul := by decide +kernel
  coc_one_left := by decide +kernel
  coc_one_right := by decide +kernel
  coc_cocycle := by decide +kernel

abbrev RH : Type := mR.Carrier

instance : Group RH := TwData.group mR_valid

namespace RH

@[expose] def w₂ : RH := ⟨0, 1⟩
@[expose] def w : RH := ⟨0, 2⟩
@[expose] def x : RH := ⟨0, 4⟩
@[expose] def z : RH := ⟨1, 0⟩
@[expose] def y : RH := ⟨2, 0⟩
@[expose] def t : RH := ⟨4, 0⟩
@[expose] def k : RH := ⟨8, 0⟩

@[expose] def gens : List RH := [w₂, w, x, z, y, t, k]

@[expose] def nfTab : ℕ :=
  47665071433714642246693880070116095772181536964584699102693715878639465138176 + 2 ^ 256 *
  (44968821672195664249773344394838085517732248881512860580586278488090839484930 + 2 ^ 256 *
  (49481362932424487981014817906141574338530342324998476714562926013790574873604 + 2 ^ 256 *
  (46785223167487911958704650435211799434279293523692821737151484565104738831878)))

@[expose] def nfBits (c : RH) : List Bool :=
  (List.range 7).map fun i => (tget nfTab 8 (16 * c.g.val + c.a.val)).testBit i

theorem nf_spec : ∀ c : RH, c = nfProd gens (nfBits c) := by decide +kernel

structure PcX {X : Type*} [Group X] (w₂' w' x' z' y' t' k' : X) : Prop where
  w₂_sq : w₂' * w₂' = y'
  w₂_w : w₂' * w' * w₂'⁻¹ = w' * y'
  w₂_x : w₂' * x' * w₂'⁻¹ = w' * (x' * (z' * (y' * t')))
  w₂_z : w₂' * z' * w₂'⁻¹ = z'
  w₂_y : w₂' * y' * w₂'⁻¹ = y'
  w₂_t : w₂' * t' * w₂'⁻¹ = y' * t'
  w₂_k : w₂' * k' * w₂'⁻¹ = k'
  w_sq : w' * w' = 1
  w_x : w' * x' * w'⁻¹ = x'
  w_z : w' * z' * w'⁻¹ = z'
  w_y : w' * y' * w'⁻¹ = y'
  w_t : w' * t' * w'⁻¹ = z' * t'
  w_k : w' * k' * w'⁻¹ = k'
  x_sq : x' * x' = z'
  x_z : x' * z' * x'⁻¹ = z'
  x_y : x' * y' * x'⁻¹ = z' * y'
  x_t : x' * t' * x'⁻¹ = t'
  x_k : x' * k' * x'⁻¹ = k'
  z_sq : z' * z' = 1
  z_y : z' * y' * z'⁻¹ = y'
  z_t : z' * t' * z'⁻¹ = t'
  z_k : z' * k' * z'⁻¹ = k'
  y_sq : y' * y' = 1
  y_t : y' * t' * y'⁻¹ = t'
  y_k : y' * k' * y'⁻¹ = k'
  t_sq : t' * t' = 1
  t_k : t' * k' * t'⁻¹ = k'
  k_sq : k' * k' = 1

theorem pcRel_of {X : Type*} [Group X] {w₂' w' x' z' y' t' k' : X}
    (h : PcX w₂' w' x' z' y' t' k') :
    PcRel [(w₂, w₂'), (w, w'), (x, x'), (z, z'), (y, y'), (t, t'), (k, k')] := by
  refine ⟨⟨[false, false, false, true, false, false], ?_,
    by simpa [nfProd] using h.w₂_sq⟩, ?_, ?_, ?_⟩
  · show w₂ * w₂ = nfProd [w, x, z, y, t, k] [false, false, false, true, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨[true, false, false, true, false, false], ?_, by simpa [nfProd] using h.w₂_w⟩
      show w₂ * w * w₂⁻¹ =
        nfProd [w, x, z, y, t, k] [true, false, false, true, false, false]
      decide +kernel
    · refine ⟨[true, true, true, true, true, false], ?_, by simpa [nfProd] using h.w₂_x⟩
      show w₂ * x * w₂⁻¹ =
        nfProd [w, x, z, y, t, k] [true, true, true, true, true, false]
      decide +kernel
    · refine ⟨[false, false, true, false, false, false], ?_, by simpa [nfProd] using h.w₂_z⟩
      show w₂ * z * w₂⁻¹ =
        nfProd [w, x, z, y, t, k] [false, false, true, false, false, false]
      decide +kernel
    · refine ⟨[false, false, false, true, false, false], ?_, by simpa [nfProd] using h.w₂_y⟩
      show w₂ * y * w₂⁻¹ =
        nfProd [w, x, z, y, t, k] [false, false, false, true, false, false]
      decide +kernel
    · refine ⟨[false, false, false, true, true, false], ?_, by simpa [nfProd] using h.w₂_t⟩
      show w₂ * t * w₂⁻¹ =
        nfProd [w, x, z, y, t, k] [false, false, false, true, true, false]
      decide +kernel
    · refine ⟨[false, false, false, false, false, true], ?_, by simpa [nfProd] using h.w₂_k⟩
      show w₂ * k * w₂⁻¹ =
        nfProd [w, x, z, y, t, k] [false, false, false, false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 6, w₂ ≠ nfProd [w, x, z, y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false, false, false, false], ?_, by simpa [nfProd] using h.w_sq⟩, ?_, ?_, ?_⟩
  · show w * w = nfProd [x, z, y, t, k] [false, false, false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · refine ⟨[true, false, false, false, false], ?_, by simpa [nfProd] using h.w_x⟩
      show w * x * w⁻¹ =
        nfProd [x, z, y, t, k] [true, false, false, false, false]
      decide +kernel
    · refine ⟨[false, true, false, false, false], ?_, by simpa [nfProd] using h.w_z⟩
      show w * z * w⁻¹ =
        nfProd [x, z, y, t, k] [false, true, false, false, false]
      decide +kernel
    · refine ⟨[false, false, true, false, false], ?_, by simpa [nfProd] using h.w_y⟩
      show w * y * w⁻¹ =
        nfProd [x, z, y, t, k] [false, false, true, false, false]
      decide +kernel
    · refine ⟨[false, true, false, true, false], ?_, by simpa [nfProd] using h.w_t⟩
      show w * t * w⁻¹ =
        nfProd [x, z, y, t, k] [false, true, false, true, false]
      decide +kernel
    · refine ⟨[false, false, false, false, true], ?_, by simpa [nfProd] using h.w_k⟩
      show w * k * w⁻¹ =
        nfProd [x, z, y, t, k] [false, false, false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 5, w ≠ nfProd [x, z, y, t, k] bs
    decide +kernel
  refine ⟨⟨[true, false, false, false], ?_, by simpa [nfProd] using h.x_sq⟩, ?_, ?_, ?_⟩
  · show x * x = nfProd [z, y, t, k] [true, false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨[true, false, false, false], ?_, by simpa [nfProd] using h.x_z⟩
      show x * z * x⁻¹ =
        nfProd [z, y, t, k] [true, false, false, false]
      decide +kernel
    · refine ⟨[true, true, false, false], ?_, by simpa [nfProd] using h.x_y⟩
      show x * y * x⁻¹ =
        nfProd [z, y, t, k] [true, true, false, false]
      decide +kernel
    · refine ⟨[false, false, true, false], ?_, by simpa [nfProd] using h.x_t⟩
      show x * t * x⁻¹ =
        nfProd [z, y, t, k] [false, false, true, false]
      decide +kernel
    · refine ⟨[false, false, false, true], ?_, by simpa [nfProd] using h.x_k⟩
      show x * k * x⁻¹ =
        nfProd [z, y, t, k] [false, false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 4, x ≠ nfProd [z, y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false, false], ?_, by simpa [nfProd] using h.z_sq⟩, ?_, ?_, ?_⟩
  · show z * z = nfProd [y, t, k] [false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨[true, false, false], ?_, by simpa [nfProd] using h.z_y⟩
      show z * y * z⁻¹ =
        nfProd [y, t, k] [true, false, false]
      decide +kernel
    · refine ⟨[false, true, false], ?_, by simpa [nfProd] using h.z_t⟩
      show z * t * z⁻¹ =
        nfProd [y, t, k] [false, true, false]
      decide +kernel
    · refine ⟨[false, false, true], ?_, by simpa [nfProd] using h.z_k⟩
      show z * k * z⁻¹ =
        nfProd [y, t, k] [false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 3, z ≠ nfProd [y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false], ?_, by simpa [nfProd] using h.y_sq⟩, ?_, ?_, ?_⟩
  · show y * y = nfProd [t, k] [false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨[true, false], ?_, by simpa [nfProd] using h.y_t⟩
      show y * t * y⁻¹ =
        nfProd [t, k] [true, false]
      decide +kernel
    · refine ⟨[false, true], ?_, by simpa [nfProd] using h.y_k⟩
      show y * k * y⁻¹ =
        nfProd [t, k] [false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 2, y ≠ nfProd [t, k] bs
    decide +kernel
  refine ⟨⟨[false], ?_, by simpa [nfProd] using h.t_sq⟩, ?_, ?_, ?_⟩
  · show t * t = nfProd [k] [false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · refine ⟨[true], ?_, by simpa [nfProd] using h.t_k⟩
      show t * k * t⁻¹ =
        nfProd [k] [true]
      decide +kernel
  · show ∀ bs ∈ allBits 1, t ≠ nfProd [k] bs
    decide +kernel
  refine ⟨⟨[], ?_, by simpa [nfProd] using h.k_sq⟩, ?_, ?_, ?_⟩
  · show k * k = nfProd [] []
    decide +kernel
  · intro r hr
    simp at hr
  · show ∀ bs ∈ allBits 0, k ≠ nfProd [] bs
    decide +kernel
  trivial

theorem exists_hom {X : Type*} [Group X] {w₂' w' x' z' y' t' k' : X}
    (h : PcX w₂' w' x' z' y' t' k') :
    ∃ ι : RH →* X, ι w₂ = w₂' ∧ ι w = w' ∧ ι x = x' ∧ ι z = z' ∧ ι y = y' ∧ ι t = t' ∧
      ι k = k' := by
  obtain ⟨F, hF, -⟩ := exists_hom_of_pcRel _ (pcRel_of h) (fun c =>
    ⟨nfBits c, by simpa [nfBits] using mem_allBits (nfBits c), nf_spec c⟩)
  exact ⟨F, hF (w₂, w₂') (by simp), hF (w, w') (by simp), hF (x, x') (by simp),
    hF (z, z') (by simp), hF (y, y') (by simp), hF (t, t') (by simp), hF (k, k') (by simp)⟩

theorem center_cases : ∀ c : RH, (∀ g ∈ gens, g * c = c * g) →
    c = 1 ∨ c = z ∨ c = k ∨ c = z * k := by
  decide +kernel

theorem card_eq : Nat.card RH = 2 ^ 7 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (TwData.Carrier.equiv mR), Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  norm_num

theorem isPGroup : IsPGroup 2 RH := IsPGroup.of_card card_eq

theorem injective_of {X : Type*} [Group X] (ι : RH →* X) (hz : ι z ≠ 1) (hk : ι k ≠ 1)
    (hzk : ι (z * k) ≠ 1) : Function.Injective ι := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent RH := isPGroup.isNilpotent
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨c, hck, hcc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hc1' : c ≠ 1 := fun h' => hc1 (Subtype.ext h')
  rcases center_cases c (fun g _ => Subgroup.mem_center_iff.mp hcc g) with h1 | h1 | h1 | h1
  · exact hc1' h1
  · rw [h1] at hck
    exact hz hck
  · rw [h1] at hck
    exact hk hck
  · rw [h1] at hck
    exact hzk hck

theorem range_le {X : Type*} [Group X] (ι : RH →* X) {H : Subgroup X}
    (h : ∀ g ∈ gens, ι g ∈ H) : ι.range ≤ H := by
  rintro _ ⟨c, rfl⟩
  rw [nf_spec c]
  exact map_mem_of_inSpan ι ⟨nfBits c, by simpa [nfBits, gens] using mem_allBits (nfBits c), rfl⟩ h

end RH

end CFSG.ComponentClassification.HSFLit.Sec5H
