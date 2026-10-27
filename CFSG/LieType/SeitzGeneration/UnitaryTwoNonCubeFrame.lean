module

public import CFSG.LieType.SeitzGeneration.UnitaryTwoBase

public section

namespace CFSG.LieType.SeitzGeneration.TwoNonCube

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers CFSG.LieType.SeitzGeneration.ONExt
  CFSG.LieType.SeitzGeneration.UnitaryTwo

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ} {ω : K}

section Elements

theorem isON_two (hσ : ∀ c, σ (σ c) = c) {u v : Fin n → K} (hu : herm σ u u = 1)
    (hv : herm σ v v = 1) (huv : herm σ u v = 0) : IsON σ ![u, v] := by
  have hvu : herm σ v u = 0 := herm_eq_zero_comm σ hσ huv
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hu, hv, huv, hvu]

theorem isON_three (hσ : ∀ c, σ (σ c) = c) {u v w : Fin n → K} (hu : herm σ u u = 1)
    (hv : herm σ v v = 1) (hw : herm σ w w = 1) (huv : herm σ u v = 0) (huw : herm σ u w = 0)
    (hvw : herm σ v w = 0) : IsON σ ![u, v, w] := by
  have hvu : herm σ v u = 0 := herm_eq_zero_comm σ hσ huv
  have hwu : herm σ w u = 0 := herm_eq_zero_comm σ hσ huw
  have hwv : herm σ w v = 0 := herm_eq_zero_comm σ hσ hvw
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hu, hv, hw, huv, huw, hvw, hvu, hwu, hwv]

@[expose] noncomputable def dft3 (hK : Field4 σ ω) {u v w : Fin n → K} (h : IsON σ ![u, v, w]) :
    SUid σ n :=
  ext hK.invol.invol h (dftSU σ hK.norm_one hK.cube hK.ne_one hK.two)

theorem dft3_smul_fst (hK : Field4 σ ω) {u v w : Fin n → K} (h : IsON σ ![u, v, w]) :
    dft3 hK h • u = u + v + w := by
  have h0 : u = orthoEmb ![u, v, w] (Pi.single 0 1) := by
    rw [orthoEmb_single]
    rfl
  have h1 : dft3 hK h • orthoEmb ![u, v, w] (Pi.single 0 1) =
      orthoEmb ![u, v, w] (fun _ => 1) := by
    rw [dft3, ext_smul_orthoEmb, dftSU_smul_single_zero]
  have h2 : orthoEmb ![u, v, w] (fun _ => 1) = u + v + w := by
    rw [orthoEmb_apply, Fin.sum_univ_three]
    simp
  calc dft3 hK h • u = dft3 hK h • orthoEmb ![u, v, w] (Pi.single 0 1) := congrArg _ h0
    _ = orthoEmb ![u, v, w] (fun _ => 1) := h1
    _ = u + v + w := h2

theorem dft3_smul_of_orth (hK : Field4 σ ω) {u v w : Fin n → K} (h : IsON σ ![u, v, w])
    {z : Fin n → K} (hu : herm σ u z = 0) (hv : herm σ v z = 0) (hw : herm σ w z = 0) :
    dft3 hK h • z = z := by
  rw [dft3]
  refine ext_smul_of_orth _ _ _ fun i => ?_
  fin_cases i
  · exact hu
  · exact hv
  · exact hw

@[expose] noncomputable def scale2 (hK : Field4 σ ω) {u v : Fin n → K} (h : IsON σ ![u, v])
    {t : K} (ht : t ≠ 0) : SUid σ n :=
  ext hK.invol.invol h (diagPair hK.norm_one ht)

theorem scale2_smul_fst (hK : Field4 σ ω) {u v : Fin n → K} (h : IsON σ ![u, v]) {t : K}
    (ht : t ≠ 0) : scale2 hK h ht • u = t • u := by
  have h0 : u = orthoEmb ![u, v] (Pi.single 0 1) := by
    rw [orthoEmb_single]
    rfl
  have h1 : (diagPair (σ := σ) hK.norm_one ht • (Pi.single 0 1 : Fin 2 → K)) =
      t • Pi.single 0 1 := by
    funext s
    rw [diagPair_smul]
    fin_cases s <;> simp
  calc scale2 hK h ht • u = scale2 hK h ht • orthoEmb ![u, v] (Pi.single 0 1) :=
        congrArg _ h0
    _ = orthoEmb ![u, v] (diagPair (σ := σ) hK.norm_one ht • Pi.single 0 1) := by
        rw [scale2, ext_smul_orthoEmb]
    _ = t • u := by rw [h1, map_smul, ← h0]

theorem scale2_smul_of_orth (hK : Field4 σ ω) {u v : Fin n → K} (h : IsON σ ![u, v]) {t : K}
    (ht : t ≠ 0) {z : Fin n → K} (hu : herm σ u z = 0) (hv : herm σ v z = 0) :
    scale2 hK h ht • z = z := by
  rw [scale2]
  refine ext_smul_of_orth _ _ _ fun i => ?_
  fin_cases i
  · exact hu
  · exact hv

@[expose] noncomputable def swapSU (σ : K ≃+* K) (h2 : (1 : K) + 1 = 0) : SUid σ 2 :=
  mkSU σ !![0, 1; 1, 0] (by rw [Matrix.det_fin_two_of]; linear_combination (-1 : K) * h2)
    (fun x y => by
      simp only [herm_def, Fin.sum_univ_two]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm])

@[expose] noncomputable def swap2 (hK : Field4 σ ω) {u v : Fin n → K} (h : IsON σ ![u, v]) :
    SUid σ n :=
  ext hK.invol.invol h (swapSU σ hK.two)

theorem swapSU_smul_zero (h2 : (1 : K) + 1 = 0) :
    swapSU σ h2 • (Pi.single 0 1 : Fin 2 → K) = Pi.single 1 1 := by
  funext i
  simp only [swapSU, mkSU_smul]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem swap2_smul_fst (hK : Field4 σ ω) {u v : Fin n → K} (h : IsON σ ![u, v]) :
    swap2 hK h • u = v := by
  have h0 : u = orthoEmb ![u, v] (Pi.single 0 1) := by
    rw [orthoEmb_single]
    rfl
  have h1 : v = orthoEmb ![u, v] (Pi.single 1 1) := by
    rw [orthoEmb_single]
    rfl
  calc swap2 hK h • u = swap2 hK h • orthoEmb ![u, v] (Pi.single 0 1) := congrArg _ h0
    _ = orthoEmb ![u, v] (swapSU σ hK.two • (Pi.single 0 1 : Fin 2 → K)) := by
        rw [swap2, ext_smul_orthoEmb]
    _ = v := by rw [swapSU_smul_zero, ← h1]

theorem swap2_smul_of_orth (hK : Field4 σ ω) {u v : Fin n → K} (h : IsON σ ![u, v])
    {z : Fin n → K} (hu : herm σ u z = 0) (hv : herm σ v z = 0) : swap2 hK h • z = z := by
  rw [swap2]
  refine ext_smul_of_orth _ _ _ fun i => ?_
  fin_cases i
  · exact hu
  · exact hv

end Elements

section Commute

theorem mulVec_orthoEmb_of_eig {m : ℕ} {x : Fin m → Fin n → K} {Y : Matrix (Fin n) (Fin n) K}
    {D : Fin m → K} (hD : ∀ i, Y *ᵥ x i = D i • x i) (c : Fin m → K) :
    Y *ᵥ orthoEmb x c = orthoEmb x (fun i => D i * c i) := by
  simp only [orthoEmb_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hD, smul_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem commute_ext_mat (hσ : ∀ c, σ (σ c) = c) {m : ℕ} {x : Fin m → Fin n → K} (hx : IsON σ x)
    {Y : Matrix (Fin n) (Fin n) K} (hY : ∀ u w, herm σ (Y *ᵥ u) (Y *ᵥ w) = herm σ u w)
    {D : Fin m → K} (hD : ∀ i, Y *ᵥ x i = D i • x i) (G : SUid σ m)
    (hG : ∀ c : Fin m → K, G • (fun i => D i * c i) = fun i => D i * (G • c) i) :
    (((ext hσ hx G : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y =
      Y * (((ext hσ hx G : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hxs : ∀ i, herm σ (x i) (x i) = 1 := fun i => by simpa using hx i i
  have hDn : ∀ i, σ (D i) * D i = 1 := by
    intro i
    have h1 := hY (x i) (x i)
    rw [hD i, herm_smul_left, herm_smul_right, hxs i] at h1
    linear_combination h1
  have hD0 : ∀ i, σ (D i) ≠ 0 := fun i h0 => by
    have := hDn i
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hperp : ∀ w, (∀ i, herm σ (x i) w = 0) → ∀ i, herm σ (x i) (Y *ᵥ w) = 0 := by
    intro w hw i
    have h1 := hY (x i) w
    rw [hD i, herm_smul_left, hw i] at h1
    exact (mul_eq_zero.mp h1).resolve_left (hD0 i)
  have key : ∀ v, (((ext hσ hx G : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (Y *ᵥ v) = Y *ᵥ ((((ext hσ hx G : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        v) := by
    intro v
    obtain ⟨c, w, hw, rfl⟩ := exists_decomp hx v
    have hE : ∀ z, (((ext hσ hx G : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z =
        extMat σ x ((G : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ z := fun z => rfl
    have hGc : ∀ c' : Fin m → K, ((G : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
        (fun i => D i * c' i) = fun i => D i * (((G : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
          c') i := fun c' => hG c'
    rw [mulVec_add, mulVec_orthoEmb_of_eig hD, hE, hE, extMat_mulVec hx _ _ hw,
      extMat_mulVec hx _ _ (hperp w hw), mulVec_add, mulVec_orthoEmb_of_eig hD, hGc]
  exact Matrix.ext_of_mulVec_single fun i => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact key _

end Commute

section Base

theorem herm_eq_zero_of_isON {ι : Type*} [DecidableEq ι] {c : ι → Fin n → K}
    (hc : ∀ i j, herm σ (c i) (c j) = if i = j then 1 else 0) {a b : ι} (hab : a ≠ b) :
    herm σ (c a) (c b) = 0 := by
  simpa [hab] using hc a b

theorem herm_self_of_isON {ι : Type*} [DecidableEq ι] {c : ι → Fin n → K}
    (hc : ∀ i j, herm σ (c i) (c j) = if i = j then 1 else 0) (a : ι) :
    herm σ (c a) (c a) = 1 := by
  simpa using hc a a

@[expose] def blk4 (x : Fin 5 → Fin n → K) : Fin 4 → Fin n → K := fun s => x s.castSucc

theorem blk4_isON {x : Fin 5 → Fin n → K} (hx : IsON σ x) : IsON σ (blk4 x) :=
  isON_comp hx (τ := fun s : Fin 4 => s.castSucc) (Fin.castSucc_injective 4)

variable {x : Fin 5 → Fin n → K}

theorem isON_012 (hσ : ∀ c, σ (σ c) = c) (hx : IsON σ x) : IsON σ ![x 0, x 1, x 2] :=
  isON_three hσ (herm_self_of_isON hx 0) (herm_self_of_isON hx 1) (herm_self_of_isON hx 2)
    (herm_eq_zero_of_isON hx (by decide)) (herm_eq_zero_of_isON hx (by decide))
    (herm_eq_zero_of_isON hx (by decide))

theorem isON_pair4 (hσ : ∀ c, σ (σ c) = c) (hx : IsON σ x) (a : Fin 4) :
    IsON σ ![x a.castSucc, x 4] :=
  isON_two hσ (herm_self_of_isON hx _) (herm_self_of_isON hx _)
    (herm_eq_zero_of_isON hx (Fin.castSucc_lt_last a).ne)

variable {H : Subgroup (SUid σ n)}

theorem isCenter_sum_four (hK : Field4 σ ω) (hx : IsON σ x) (hP : IsCenter H (x 0 + x 3))
    (hD : ∀ h : IsON σ ![x 0, x 1, x 2], dft3 hK h ∈ H) :
    IsCenter H (x 0 + x 1 + x 2 + x 3) := by
  have h012 := isON_012 hK.invol.invol hx
  have h03 : herm σ (x 0) (x 3) = 0 := herm_eq_zero_of_isON hx (by decide)
  have h13 : herm σ (x 1) (x 3) = 0 := herm_eq_zero_of_isON hx (by decide)
  have h23 : herm σ (x 2) (x 3) = 0 := herm_eq_zero_of_isON hx (by decide)
  have := hP.map (hD h012)
  rw [smul_add, dft3_smul_fst hK h012, dft3_smul_of_orth hK h012 h03 h13 h23] at this
  exact this

theorem scale2_smul_blk (hK : Field4 σ ω) (hx : IsON σ x) (i : Fin 4) {t : K} (ht : t ≠ 0)
    (h : IsON σ ![x i.castSucc, x 4]) (c c' : Fin 4 → K)
    (hc' : ∀ s, c' s = if s = i then t * c s else c s) :
    scale2 hK h ht • orthoEmb (blk4 x) c = orthoEmb (blk4 x) c' := by
  simp only [orthoEmb_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_comm _ (c s), hc' s]
  by_cases hs : s = i
  · subst hs
    rw [if_pos rfl, blk4, scale2_smul_fst, smul_smul, mul_comm]
  · rw [if_neg hs, blk4, scale2_smul_of_orth hK h ht]
    · exact herm_eq_zero_of_isON hx (fun h' => hs (Fin.castSucc_injective 4 h').symm)
    · exact herm_eq_zero_of_isON hx (Fin.castSucc_lt_last s).ne.symm

theorem isCenter_pair_coeff (hK : Field4 σ ω) (hx : IsON σ x)
    (hS : ∀ (i : Fin 4) (h : IsON σ ![x i.castSucc, x 4]) (t : K) (ht : t ≠ 0),
      scale2 hK h ht ∈ H)
    {a b : Fin 4} (hab : a ≠ b) (hP : IsCenter H (x a.castSucc + x b.castSucc)) {α β : K}
    (hα : α ≠ 0) (hβ : β ≠ 0) : IsCenter H (α • x a.castSucc + β • x b.castSucc) := by
  have hσ := hK.invol.invol
  have hab' : a.castSucc ≠ b.castSucc := fun h => hab (Fin.castSucc_injective 4 h)
  have ha4 : a.castSucc ≠ 4 := (Fin.castSucc_lt_last a).ne
  have hb4 : b.castSucc ≠ 4 := (Fin.castSucc_lt_last b).ne
  have hab0 : herm σ (x a.castSucc) (x b.castSucc) = 0 := herm_eq_zero_of_isON hx hab'
  have hba0 : herm σ (x b.castSucc) (x a.castSucc) = 0 := herm_eq_zero_of_isON hx hab'.symm
  have h4b : herm σ (x 4) (x b.castSucc) = 0 := herm_eq_zero_of_isON hx hb4.symm
  have h4a : herm σ (x 4) (x a.castSucc) = 0 := herm_eq_zero_of_isON hx ha4.symm
  have e1 := hP.map (hS a (isON_pair4 hσ hx a) α hα)
  rw [smul_add, scale2_smul_fst, scale2_smul_of_orth hK _ hα hab0 h4b] at e1
  have e2 := e1.map (hS b (isON_pair4 hσ hx b) β hβ)
  rw [smul_add, smul_comm _ α, scale2_smul_of_orth hK _ hβ hba0 h4a, scale2_smul_fst] at e2
  exact e2

theorem isCenter_full (hK : Field4 σ ω) (hx : IsON σ x) (hP : IsCenter H (x 0 + x 3))
    (hD : ∀ h : IsON σ ![x 0, x 1, x 2], dft3 hK h ∈ H)
    (hS : ∀ (i : Fin 4) (h : IsON σ ![x i.castSucc, x 4]) (t : K) (ht : t ≠ 0),
      scale2 hK h ht ∈ H) (c : Fin 4 → K) (hc : ∀ s, c s ≠ 0) :
    IsCenter H (orthoEmb (blk4 x) c) := by
  have hc₀ := isCenter_sum_four hK hx hP hD
  have step : ∀ (i : Fin 4) (t : K) (ht : t ≠ 0) (c c' : Fin 4 → K),
      (∀ s, c' s = if s = i then t * c s else c s) → IsCenter H (orthoEmb (blk4 x) c) →
      IsCenter H (orthoEmb (blk4 x) c') := fun i t ht c c' hc' hw => by
    rw [← scale2_smul_blk hK hx i ht (isON_pair4 hK.invol.invol hx i) c c' hc']
    exact hw.map (hS i _ t ht)
  have e0 : IsCenter H (orthoEmb (blk4 x) ![1, 1, 1, 1]) := by
    convert hc₀ using 1
    simp [orthoEmb_apply, Fin.sum_univ_four, blk4]
  have e1 := step 0 (c 0) (hc 0) _ ![c 0, 1, 1, 1] (fun s => by fin_cases s <;> simp) e0
  have e2 := step 1 (c 1) (hc 1) _ ![c 0, c 1, 1, 1] (fun s => by fin_cases s <;> simp) e1
  have e3 := step 2 (c 2) (hc 2) _ ![c 0, c 1, c 2, 1] (fun s => by fin_cases s <;> simp) e2
  have e4 := step 3 (c 3) (hc 3) _ ![c 0, c 1, c 2, c 3] (fun s => by fin_cases s <;> simp) e3
  convert e4 using 2
  funext s
  fin_cases s <;> simp

theorem allCenters_blk4 (hK : Field4 σ ω) (hx : IsON σ x)
    (hP : ∀ i j : Fin 4, i ≠ j → IsCenter H (x i.castSucc + x j.castSucc))
    (hD : ∀ h : IsON σ ![x 0, x 1, x 2], dft3 hK h ∈ H)
    (hS : ∀ (i : Fin 4) (h : IsON σ ![x i.castSucc, x 4]) (t : K) (ht : t ≠ 0),
      scale2 hK h ht ∈ H) :
    AllCenters H (Submodule.span K (Set.range (blk4 x))) := by
  classical
  intro v hv hiso
  obtain ⟨c, rfl⟩ := (mem_span_range_iff _ v).1 hv
  have hiso' : herm σ c c = 0 := by rwa [herm_orthoEmb (blk4_isON hx)] at hiso
  have hn : ∀ t : K, σ t * t = if t = 0 then 0 else 1 := fun t => by
    by_cases ht : t = 0 <;> simp [ht, hK.norm_one]
  have hpr : ∀ (a b : Fin 4), a ≠ b → ∀ (α β : K), α ≠ 0 → β ≠ 0 →
      IsCenter H (α • x a.castSucc + β • x b.castSucc) := fun a b hab α β hα hβ =>
    isCenter_pair_coeff hK hx hS hab (hP a b hab) hα hβ
  have hvec : orthoEmb (blk4 x) c = c 0 • x 0 + c 1 • x 1 + c 2 • x 2 + c 3 • x 3 := by
    simp [orthoEmb_apply, Fin.sum_univ_four, blk4]
  rw [herm_def, Fin.sum_univ_four] at hiso'
  simp only [hn] at hiso'
  by_cases h0 : c 0 = 0 <;> by_cases h1 : c 1 = 0 <;> by_cases h2 : c 2 = 0 <;>
    by_cases h3 : c 3 = 0 <;>
    first
    | (exfalso; simp [h0, h1, h2, h3, hK.two] at hiso'; done)
    | skip
  · rw [hvec]
    simp only [h0, h1, h2, h3, zero_smul, add_zero]
    exact isCenter_zero
  · rw [hvec]
    simp only [h0, h1, zero_smul, zero_add]
    exact hpr 2 3 (by decide) _ _ h2 h3
  · rw [hvec]
    simp only [h0, h2, zero_smul, zero_add, add_zero]
    exact hpr 1 3 (by decide) _ _ h1 h3
  · rw [hvec]
    simp only [h0, h3, zero_smul, zero_add, add_zero]
    exact hpr 1 2 (by decide) _ _ h1 h2
  · rw [hvec]
    simp only [h1, h2, zero_smul, zero_add, add_zero]
    exact hpr 0 3 (by decide) _ _ h0 h3
  · rw [hvec]
    simp only [h1, h3, zero_smul, zero_add, add_zero]
    exact hpr 0 2 (by decide) _ _ h0 h2
  · rw [hvec]
    simp only [h2, h3, zero_smul, add_zero]
    exact hpr 0 1 (by decide) _ _ h0 h1
  · exact isCenter_full hK hx (hP 0 3 (by decide)) hD hS c
      (fun s => by fin_cases s <;> assumption)

end Base

section Grow

variable {ι : Type*} [DecidableEq ι] {c : ι → Fin n → K}

@[expose] def spanS (c : ι → Fin n → K) (S : Finset ι) : Submodule K (Fin n → K) :=
  Submodule.span K (c '' (S : Set ι))

theorem spanS_mono {S T : Finset ι} (h : S ⊆ T) : spanS c S ≤ spanS c T :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

theorem spanS_hasON (hσ : ∀ c, σ (σ c) = c)
    (hc : ∀ i j, herm σ (c i) (c j) = if i = j then 1 else 0) {S : Finset ι}
    (hS : 4 ≤ S.card) : HasONBasis σ (spanS c S) := by
  refine ⟨S.card, fun i => c (S.equivFin.symm i : ι), fun i j => ?_, ?_, Or.inl hS⟩
  · rw [hc]
    simp [Subtype.ext_iff]
  · rw [spanS]
    congr 1
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (S.equivFin.symm i).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨S.equivFin ⟨a, ha⟩, by simp⟩

theorem herm_spanS_of_notMem (hc : ∀ i j, herm σ (c i) (c j) = if i = j then 1 else 0)
    {S : Finset ι} {j : ι} (hj : j ∉ S) {w : Fin n → K} (hw : w ∈ spanS c S) :
    herm σ w (c j) = 0 := by
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    exact herm_eq_zero_of_isON hc (fun h => hj (h ▸ hi))
  | zero => simp
  | add a b _ _ ha hb => rw [herm_add_left, ha, hb, add_zero]
  | smul a b _ hb => rw [herm_smul_left, hb, mul_zero]

theorem allCenters_grow (hK : Field4 σ ω)
    (hc : ∀ i j, herm σ (c i) (c j) = if i = j then 1 else 0) {H : Subgroup (SUid σ n)}
    {S₀ : Finset ι} (h4 : 4 ≤ S₀.card) (hA : AllCenters H (spanS c S₀))
    (hpt : ∀ j, j ∉ S₀ → ∃ u ∈ spanS c S₀, herm σ u u = 1 ∧ IsCenter H (u + c j))
    (T : Finset ι) : AllCenters H (spanS c (S₀ ∪ T)) := by
  induction T using Finset.induction_on with
  | empty => simpa using hA
  | insert j T hj ih =>
    rw [Finset.union_insert]
    by_cases hjS : j ∈ S₀ ∪ T
    · rwa [Finset.insert_eq_of_mem hjS]
    · set S := S₀ ∪ T with hSdef
      have hS4 : 4 ≤ S.card := h4.trans (Finset.card_le_card Finset.subset_union_left)
      have hj0 : j ∉ S₀ := fun h => hjS (Finset.mem_union_left _ h)
      obtain ⟨u, hu, hu1, hC⟩ := hpt j hj0
      have huS : u ∈ spanS c S := spanS_mono Finset.subset_union_left hu
      have hstep := allCenters_step hK.invol hK.norm_one hK.two
        (spanS_hasON hK.invol.invol hc hS4) ih huS hu1 (herm_self_of_isON hc j)
        (fun w hw => herm_spanS_of_notMem hc hjS hw) hC
      have hspan : spanS c (insert j S) = spanS c S ⊔ Submodule.span K {c j} := by
        rw [spanS, Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert, sup_comm]
        rfl
      rw [hspan]
      exact hstep

theorem hasONBasis_of_family [Fintype ι] (hσ : ∀ c, σ (σ c) = c)
    (hc : ∀ i j, herm σ (c i) (c j) = if i = j then 1 else 0) (h4 : 4 ≤ Fintype.card ι) :
    HasONBasis σ (Submodule.span K (Set.range c)) := by
  have := spanS_hasON hσ hc (S := Finset.univ) (by simpa using h4)
  simpa [spanS, Set.image_univ] using this

end Grow

section Mixed

variable {m₁ m₂ : ℕ} {x : Fin m₁ → Fin n → K} {y : Fin m₂ → Fin n → K}

structure Blocks3 (σ : K ≃+* K) (H : Subgroup (SUid σ n)) (x : Fin m₁ → Fin n → K)
    (y : Fin m₂ → Fin n → K) : Prop where
  ortho_x : ∀ i j, herm σ (x i) (x j) = if i = j then 1 else 0
  ortho_y : ∀ i j, herm σ (y i) (y j) = if i = j then 1 else 0
  orth : ∀ i j, herm σ (x i) (y j) = 0
  dim_x : 3 ≤ m₁
  dim_y : 3 ≤ m₂
  center_x : ∀ c, herm σ c c = 0 → IsCenter H (orthoEmb x c)
  center_y : ∀ d, herm σ d d = 0 → IsCenter H (orthoEmb y d)

variable {H : Subgroup (SUid σ n)}

theorem herm_blockVec3 (hσ : IsUnitaryInvolution σ) (B : Blocks3 σ H x y) (c c' : Fin m₁ → K)
    (d d' : Fin m₂ → K) :
    herm σ (orthoEmb x c + orthoEmb y d) (orthoEmb x c' + orthoEmb y d') =
      herm σ c c' + herm σ d d' := by
  have h1 := herm_orthoEmb B.ortho_x c c'
  have h2 := herm_orthoEmb B.ortho_y d d'
  have h3 := herm_orthoEmb_orth B.orth c d'
  have h4 : herm σ (orthoEmb y d) (orthoEmb x c') = 0 :=
    herm_eq_zero_comm σ hσ.invol (herm_orthoEmb_orth B.orth c' d)
  simp only [herm_add_left, herm_add_right, h1, h2, h3, h4]
  ring

theorem exists_mem_move_x3 (hσ : IsUnitaryInvolution σ) (B : Blocks3 σ H x y)
    {c c' : Fin m₁ → K} (hc0 : c ≠ 0) (hc : herm σ c c = 0) (hc0' : c' ≠ 0)
    (hc' : herm σ c' c' = 0) (d : Fin m₂ → K) :
    ∃ g ∈ H, g • (orthoEmb x c + orthoEmb y d) = orthoEmb x c' + orthoEmb y d := by
  obtain ⟨g, hg, hgc, hgv⟩ := exists_mem_fix_of_iso hσ B.dim_x (herm_orthoEmb B.ortho_x)
    B.center_x hc0 hc hc0' hc'
  refine ⟨g, hg, ?_⟩
  rw [smul_add, hgc, hgv (orthoEmb y d) fun u => herm_orthoEmb_orth B.orth u d]

theorem exists_mem_move_y3 (hσ : IsUnitaryInvolution σ) (B : Blocks3 σ H x y)
    {d d' : Fin m₂ → K} (hd0 : d ≠ 0) (hd : herm σ d d = 0) (hd0' : d' ≠ 0)
    (hd' : herm σ d' d' = 0) (c : Fin m₁ → K) :
    ∃ g ∈ H, g • (orthoEmb x c + orthoEmb y d) = orthoEmb x c + orthoEmb y d' := by
  obtain ⟨g, hg, hgd, hgv⟩ := exists_mem_fix_of_iso hσ B.dim_y (herm_orthoEmb B.ortho_y)
    B.center_y hd0 hd hd0' hd'
  refine ⟨g, hg, ?_⟩
  rw [smul_add, hgd, hgv (orthoEmb x c) fun u =>
    herm_eq_zero_comm σ hσ.invol (herm_orthoEmb_orth B.orth c u)]

theorem isCenter_blockVec_type0_3 (hσ : IsUnitaryInvolution σ) (B : Blocks3 σ H x y)
    {c₀ : Fin m₁ → K} {d₀ : Fin m₂ → K} (hc₀ : c₀ ≠ 0) (hc₀i : herm σ c₀ c₀ = 0) (hd₀ : d₀ ≠ 0)
    (hd₀i : herm σ d₀ d₀ = 0) (hC : IsCenter H (orthoEmb x c₀ + orthoEmb y d₀))
    {c : Fin m₁ → K} {d : Fin m₂ → K} (hc : c ≠ 0) (hci : herm σ c c = 0) (hd : d ≠ 0)
    (hdi : herm σ d d = 0) : IsCenter H (orthoEmb x c + orthoEmb y d) := by
  obtain ⟨g₁, hg₁, h₁⟩ := exists_mem_move_x3 hσ B hc₀ hc₀i hc hci d₀
  obtain ⟨g₂, hg₂, h₂⟩ := exists_mem_move_y3 hσ B hd₀ hd₀i hd hdi c
  have h := (hC.map hg₁).map hg₂
  rwa [h₁, h₂] at h

theorem exists_typeN_of_type0_3 (hσ : IsUnitaryInvolution σ) (B : Blocks3 σ H x y)
    {c₀ : Fin m₁ → K} {d₀ : Fin m₂ → K} (hc₀ : c₀ ≠ 0) (hc₀i : herm σ c₀ c₀ = 0) (hd₀ : d₀ ≠ 0)
    (hd₀i : herm σ d₀ d₀ = 0) (hC : IsCenter H (orthoEmb x c₀ + orthoEmb y d₀)) :
    ∃ (c : Fin m₁ → K) (d : Fin m₂ → K), herm σ c c ≠ 0 ∧
      IsCenter H (orthoEmb x c + orthoEmb y d) := by
  obtain ⟨f₁, hf₁i, hf₁⟩ := exists_partner hσ hc₀ hc₀i
  obtain ⟨f₂, hf₂i, hf₂⟩ := exists_partner hσ hd₀ hd₀i
  obtain ⟨ρ, hρ⟩ := hσ.exists_ne
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hρ0 : ρ ≠ 0 := fun h => hρ (by rw [h, map_zero])
  have hf₁0 : f₁ ≠ 0 := by
    intro h0
    rw [h0, herm_zero_right] at hf₁
    exact zero_ne_one hf₁
  have hf₂0 : f₂ ≠ 0 := by
    intro h0
    rw [h0, herm_zero_right] at hf₂
    exact zero_ne_one hf₂
  have hρf₂i : herm σ (ρ • f₂) (ρ • f₂) = 0 := by
    rw [herm_smul_left, herm_smul_right, hf₂i]
    ring
  have hρf₂0 : ρ • f₂ ≠ 0 := smul_ne_zero hρ0 hf₂0
  have hb : IsCenter H (orthoEmb x f₁ + orthoEmb y (ρ • f₂)) :=
    isCenter_blockVec_type0_3 hσ B hc₀ hc₀i hd₀ hd₀i hC hf₁0 hf₁i hρf₂0 hρf₂i
  have hmv := hb.move hC hτ
  have hf₁c : herm σ f₁ c₀ = 1 := by rw [herm_conj σ hσ.invol, hf₁, map_one]
  have hf₂d : herm σ f₂ d₀ = 1 := by rw [herm_conj σ hσ.invol, hf₂, map_one]
  have hw : herm σ (orthoEmb x f₁ + orthoEmb y (ρ • f₂)) (orthoEmb x c₀ + orthoEmb y d₀) =
      1 + σ ρ := by
    rw [herm_blockVec3 hσ B, hf₁c, herm_smul_left, hf₂d]
    ring
  rw [hw] at hmv
  set z : K := τ * (1 + σ ρ) with hz
  have hV : orthoEmb x c₀ + orthoEmb y d₀ + z • (orthoEmb x f₁ + orthoEmb y (ρ • f₂)) =
      orthoEmb x (c₀ + z • f₁) + orthoEmb y (d₀ + z • (ρ • f₂)) := by
    simp only [map_add, map_smul, smul_add]
    abel
  rw [hV] at hmv
  refine ⟨c₀ + z • f₁, d₀ + z • (ρ • f₂), ?_, hmv⟩
  have hn : herm σ (c₀ + z • f₁) (c₀ + z • f₁) = z + σ z := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hc₀i, hf₁i,
      hf₁, hf₁c]
    ring
  have hστ : σ τ = -τ := by linear_combination hτ
  have hz2 : z + σ z = τ * (σ ρ - ρ) := by
    rw [hz, map_mul, map_add, map_one, hσ.invol, hστ]
    ring
  rw [hn, hz2]
  exact mul_ne_zero hτ0 (sub_ne_zero.mpr hρ)

theorem exists_unit_center (hK : Field4 σ ω) (B : Blocks3 σ H x y)
    (hmix : ∃ (c : Fin m₁ → K) (d : Fin m₂ → K), c ≠ 0 ∧ d ≠ 0 ∧
      IsCenter H (orthoEmb x c + orthoEmb y d)) :
    ∃ (c : Fin m₁ → K) (d : Fin m₂ → K), herm σ c c = 1 ∧ herm σ d d = 1 ∧
      IsCenter H (orthoEmb x c + orthoEmb y d) := by
  have hσ := hK.invol
  obtain ⟨c₀, d₀, hc₀, hd₀, hC⟩ := hmix
  have key : ∃ (c : Fin m₁ → K) (d : Fin m₂ → K), herm σ c c ≠ 0 ∧
      IsCenter H (orthoEmb x c + orthoEmb y d) := by
    by_cases h0 : herm σ c₀ c₀ = 0
    · have hd0 : herm σ d₀ d₀ = 0 := by
        have := hC.1
        rw [herm_blockVec3 hσ B, h0, zero_add] at this
        exact this
      exact exists_typeN_of_type0_3 hσ B hc₀ h0 hd₀ hd0 hC
    · exact ⟨c₀, d₀, h0, hC⟩
  obtain ⟨c, d, hc, hC'⟩ := key
  have hfix : σ (herm σ c c) = herm σ c c := herm_self_fixed σ hσ.invol c
  have hc1 : herm σ c c = 1 := by
    have h1 := hK.norm_one _ hc
    rw [hfix] at h1
    have h2 : (herm σ c c - 1) * (herm σ c c - 1) = 0 := by
      linear_combination h1 + (1 - herm σ c c) * hK.two
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)
  refine ⟨c, d, hc1, ?_, hC'⟩
  have := hC'.1
  rw [herm_blockVec3 hσ B, hc1] at this
  linear_combination this - hK.two

end Mixed

section Mem

variable {H : Subgroup (SUid σ n)} {Y : Matrix (Fin n) (Fin n) K}

theorem ext_mem_of_scalar (hσ : ∀ c, σ (σ c) = c) {m : ℕ} {x : Fin m → Fin n → K}
    (hx : IsON σ x) (hY : ∀ u w, herm σ (Y *ᵥ u) (Y *ᵥ w) = herm σ u w)
    (hH : ∀ g : SUid σ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y =
      Y * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    {l : K} (hx_eig : ∀ i, Y *ᵥ x i = l • x i) (G : SUid σ m) : ext hσ hx G ∈ H :=
  hH _ (commute_ext_mat hσ hx hY (D := fun _ => l) hx_eig G fun c => smul_comm G l c)

theorem scale2_mem (hK : Field4 σ ω) (hY : ∀ u w, herm σ (Y *ᵥ u) (Y *ᵥ w) = herm σ u w)
    (hH : ∀ g : SUid σ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y =
      Y * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    {u v : Fin n → K} (h : IsON σ ![u, v]) {lu lv : K} (hu : Y *ᵥ u = lu • u)
    (hv : Y *ᵥ v = lv • v) {t : K} (ht : t ≠ 0) : scale2 hK h ht ∈ H := by
  refine hH _ (commute_ext_mat hK.invol.invol h hY (D := ![lu, lv]) ?_ _ ?_)
  · intro i
    fin_cases i
    · exact hu
    · exact hv
  · intro c
    funext s
    simp only [diagPair_smul]
    ring

theorem dft3_mem (hK : Field4 σ ω) (hY : ∀ u w, herm σ (Y *ᵥ u) (Y *ᵥ w) = herm σ u w)
    (hH : ∀ g : SUid σ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y =
      Y * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    {u v w : Fin n → K} (h : IsON σ ![u, v, w]) {l : K} (hu : Y *ᵥ u = l • u)
    (hv : Y *ᵥ v = l • v) (hw : Y *ᵥ w = l • w) : dft3 hK h ∈ H := by
  refine ext_mem_of_scalar hK.invol.invol h hY hH (l := l) ?_ _
  intro i
  fin_cases i
  · exact hu
  · exact hv
  · exact hw

theorem swap2_mem (hK : Field4 σ ω) (hY : ∀ u w, herm σ (Y *ᵥ u) (Y *ᵥ w) = herm σ u w)
    (hH : ∀ g : SUid σ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y =
      Y * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    {u v : Fin n → K} (h : IsON σ ![u, v]) {l : K} (hu : Y *ᵥ u = l • u)
    (hv : Y *ᵥ v = l • v) : swap2 hK h ∈ H := by
  refine ext_mem_of_scalar hK.invol.invol h hY hH (l := l) ?_ _
  intro i
  fin_cases i
  · exact hu
  · exact hv

theorem isON_comp_inj {ι : Type*} [DecidableEq ι] {c : ι → Fin n → K}
    (hc : ∀ i j, herm σ (c i) (c j) = if i = j then 1 else 0) {m : ℕ} {τ : Fin m → ι}
    (hτ : Function.Injective τ) : IsON σ (fun s => c (τ s)) := by
  intro i j
  rw [hc]
  simp [hτ.eq_iff]

end Mem

end CFSG.LieType.SeitzGeneration.TwoNonCube
