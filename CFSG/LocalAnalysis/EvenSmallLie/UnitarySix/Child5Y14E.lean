module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSetting
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Hyp

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix YamadaPar YamadaD YamadaN2

section Coords


structure Y14Coords {G : Type} [Group G] (d : YamadaD.Data G) (θ₂ : SL3 →* G)
    (ιG : (Fin 9 → ZMod 2) → G) : Prop where
  K₂_eq : θ₂.range = d.K₂
  ι_mem : ∀ u, ιG u ∈ d.A₂
  ι_add : ∀ u v, ιG (u + v) = ιG u * ιG v
  ι_inj : ∀ u, ιG u = 1 → u = 0
  K₂_ι : ∀ g u, θ₂ g * ιG u * (θ₂ g)⁻¹ = ιG (rhoA g *ᵥ u)
  E_mem : ∀ m < 4, θ₂ (gen3 (Fin.ofNat 12 m)) ∈ d.A₁
  ν_mem : ∀ j < 4, θ₂ (gen3 (nuS j)) ∈ d.K₁

end Coords

@[expose] def prodBits9 (μ : ℕ) : Array ℕ :=
  (List.range 4).foldl (fun acc m =>
    if μ.testBit m then bmul 9 9 acc (genABits (Fin.ofNat 12 m)) else acc) id9

@[expose] def decMask9 (A : Array ℕ) : ℕ :=
  (if (A.getD 0 0).testBit 2 then 1 else 0) + (if (A.getD 0 0).testBit 1 then 2 else 0) +
    (if (A.getD 0 0).testBit 4 then 4 else 0) + (if (A.getD 0 0).testBit 3 then 8 else 0)

theorem decMask9_prodBits9 : ∀ μ < 16, decMask9 (prodBits9 μ) = μ := by decide

theorem toMat_prodBits9 (μ : ℕ) :
    toMat 9 9 (prodBits9 μ) = ((bitList μ).map fun m => genA (Fin.ofNat 12 m)).prod := by
  have key : ∀ (l : List ℕ) (acc : Array ℕ), toMat 9 9 (l.foldl (fun acc m =>
      if μ.testBit m then bmul 9 9 acc (genABits (Fin.ofNat 12 m)) else acc) acc) =
      toMat 9 9 acc * ((l.filter fun m => μ.testBit m).map fun m => genA (Fin.ofNat 12 m)).prod := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons m l ih =>
      intro acc
      by_cases hm : μ.testBit m
      · simp only [List.foldl_cons, hm, ↓reduceIte]
        rw [ih, toMat_bmul, List.filter_cons_of_pos (by simpa using hm), List.map_cons,
          List.prod_cons, mul_assoc]
        rfl
      · simp only [List.foldl_cons, hm, Bool.false_eq_true, ↓reduceIte]
        rw [ih, List.filter_cons_of_neg (by simpa using hm)]
  rw [prodBits9, key, toMat_id9, one_mul, bitList]

theorem testBit_eq_of_toMat9_eq {A B : Array ℕ} (h : toMat 9 9 A = toMat 9 9 B) {i j : ℕ}
    (hi : i < 9) (hj : j < 9) : (A.getD i 0).testBit j = (B.getD i 0).testBit j := by
  have h1 := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
  rw [toMat_apply, toMat_apply] at h1
  cases h2 : (A.getD i 0).testBit j <;> cases h3 : (B.getD i 0).testBit j <;>
    simp_all [bz]

theorem decMask9_congr {A B : Array ℕ} (h : toMat 9 9 A = toMat 9 9 B) :
    decMask9 A = decMask9 B := by
  simp only [decMask9, testBit_eq_of_toMat9_eq h (i := 0) (j := 2) (by norm_num) (by norm_num),
    testBit_eq_of_toMat9_eq h (i := 0) (j := 1) (by norm_num) (by norm_num),
    testBit_eq_of_toMat9_eq h (i := 0) (j := 4) (by norm_num) (by norm_num),
    testBit_eq_of_toMat9_eq h (i := 0) (j := 3) (by norm_num) (by norm_num)]

@[expose] noncomputable def prodSL (μ : ℕ) : SL3 :=
  ((bitList μ).map fun m => gen3 (Fin.ofNat 12 m)).prod

theorem eProdG_eq {Γ : Type*} [Group Γ] (θ : SL3 →* Γ) (μ : ℕ) :
    eProdG θ μ = θ (prodSL μ) := by
  rw [eProdG, prodSL, map_list_prod, List.map_map]
  rfl

theorem rhoA_prodSL (μ : ℕ) :
    rhoA (prodSL μ) = toMat 9 9 (prodBits9 μ) := by
  rw [toMat_prodBits9, prodSL, map_list_prod, List.map_map]
  have e : (⇑rhoA ∘ fun m => gen3 (Fin.ofNat 12 m)) = fun m => genA (Fin.ofNat 12 m) := by
    funext m
    exact rhoA_gen3 _
  rw [e]

section Inj

variable {G : Type} [Group G] {d : YamadaD.Data G}
  {θ₂ : SL3 →* G} {ιG : (Fin 9 → ZMod 2) → G}

theorem ι₂_zero (hc : Y14Coords d θ₂ ιG) : ιG 0 = 1 := by
  have h1 := hc.ι_add 0 0
  rw [add_zero] at h1
  exact (mul_eq_left.mp h1.symm)

theorem ι₂_inj (hc : Y14Coords d θ₂ ιG) {a b : Fin 9 → ZMod 2} (hab : ιG a = ιG b) : a = b := by
  have h1 : ιG (a + b) = 1 := by
    rw [hc.ι_add, ← hab, ← hc.ι_add]
    have : a + a = 0 := by
      funext i
      simp only [Pi.add_apply, Pi.zero_apply]
      generalize a i = x
      revert x
      decide
    rw [this, ι₂_zero hc]
  have h2 := hc.ι_inj _ h1
  funext i
  have h3 := congrFun h2 i
  simp only [Pi.add_apply, Pi.zero_apply] at h3
  generalize a i = x at h3 ⊢
  generalize b i = y at h3 ⊢
  revert x y
  decide

theorem eProdG_inj (hc : Y14Coords d θ₂ ιG) {μ μ' : ℕ} (hμ : μ < 16) (hμ' : μ' < 16)
    (h : eProdG θ₂ μ = eProdG θ₂ μ') : μ = μ' := by
  rw [eProdG_eq, eProdG_eq] at h
  have hM : rhoA (prodSL μ) = rhoA (prodSL μ') := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    apply ι₂_inj hc
    rw [← hc.K₂_ι, ← hc.K₂_ι, h]
  rw [rhoA_prodSL, rhoA_prodSL] at hM
  have h1 := decMask9_congr hM
  rwa [decMask9_prodBits9 μ hμ, decMask9_prodBits9 μ' hμ'] at h1

end Inj

end CFSG.EvenSmallLie.UnitarySix.Child5
