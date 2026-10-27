module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversBasic

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Covers

open scoped IsMulCommutative

section Cycle

variable {G E X : Type*} [Group G] [Group E] [MulAction G X]

@[expose] def pathEnd (g : Fin 2 → G) : List Letter → X → X
  | [], y => y
  | l :: w, y => letterVal g l • pathEnd g w y

theorem pathEnd_eq (g : Fin 2 → G) (w : List Letter) (y : X) :
    pathEnd g w y = wordVal g w • y := by
  induction w with
  | nil => simp [pathEnd]
  | cons l w ih => rw [pathEnd, ih, wordVal_cons, mul_smul]

@[expose] def letterKey (g : Fin 2 → G) (y : X) (l : Letter) : X × Fin 2 :=
  if l.2 then (y, l.1) else ((g l.1)⁻¹ • y, l.1)

@[expose] def wordKeys (g : Fin 2 → G) : List Letter → X → List (X × Fin 2)
  | [], _ => []
  | l :: w, y => letterKey g (pathEnd g w y) l :: wordKeys g w y

theorem letterKey_true (g : Fin 2 → G) (y : X) (i : Fin 2) :
    letterKey g y (i, true) = (y, i) := rfl

theorem letterKey_false (g : Fin 2 → G) (y : X) (i : Fin 2) :
    letterKey g y (i, false) = ((g i)⁻¹ • y, i) := rfl

theorem prod_eq_one_of_even {K : Type*} [DecidableEq K] (μ : K → E)
    (hc : ∀ k, μ k ∈ Subgroup.center E) (hsq : ∀ k, μ k * μ k = 1) (L : List K)
    (hL : ∀ k ∈ L, Even (L.count k)) : (L.map μ).prod = 1 := by
  let μc : K → Subgroup.center E := fun k => ⟨μ k, hc k⟩
  have h1 : (L.map μ).prod = (((L.map μc).prod : Subgroup.center E) : E) := by
    rw [show (L.map μ) = (L.map μc).map (Subgroup.center E).subtype by
      simp [List.map_map, Function.comp_def, μc]]
    exact (map_list_prod (Subgroup.center E).subtype _).symm
  have h3 : (L.map μc).prod = ∏ m ∈ L.toFinset, μc m ^ L.count m :=
    Finset.prod_list_map_count L μc
  rw [h1, h3]
  have h2 : ∀ k ∈ L.toFinset, μc k ^ L.count k = 1 := by
    intro k hk
    obtain ⟨j, hj⟩ := hL k (List.mem_toFinset.mp hk)
    have hμ : μc k ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_two]
      exact hsq k
    rw [hj, ← two_mul, pow_mul, hμ, one_pow]
  rw [Finset.prod_eq_one h2]
  rfl

structure SplitData (π : E →* G) (D : X) where
  central : ∀ z, π z = 1 → z ∈ Subgroup.center E
  sq : ∀ z, π z = 1 → z * z = 1
  σ : G → E
  σπ : ∀ g, g • D = D → π (σ g) = g
  σmul : ∀ g h, g • D = D → h • D = D → σ (g * h) = σ g * σ h

namespace SplitData

variable {π : E →* G} {D : X} (S : SplitData π D)

theorem σ_one : S.σ 1 = 1 := by
  have h := S.σmul 1 1 (one_smul G D) (one_smul G D)
  rw [mul_one] at h
  exact mul_left_cancel (a := S.σ 1) (by rw [mul_one]; exact h.symm)

@[expose] def tau (e : E) : E := e * (S.σ (π e))⁻¹

theorem tau_ker (e : E) (he : π e • D = D) : π (S.tau e) = 1 := by
  simp [tau, S.σπ _ he]

theorem tau_of_ker (z : E) (hz : π z = 1) : S.tau z = z := by
  simp [tau, hz, S.σ_one]

theorem tau_one : S.tau 1 = 1 := S.tau_of_ker 1 (map_one π)

theorem tau_mul (e₁ e₂ : E) (h₁ : π e₁ • D = D) (h₂ : π e₂ • D = D) :
    S.tau (e₁ * e₂) = S.tau e₁ * S.tau e₂ := by
  unfold tau
  rw [map_mul, S.σmul _ _ h₁ h₂, mul_inv_rev]
  have hc : (e₂ * (S.σ (π e₂))⁻¹) ∈ Subgroup.center E := S.central _ (S.tau_ker e₂ h₂)
  have h := Subgroup.mem_center_iff.mp hc (S.σ (π e₁))⁻¹
  calc e₁ * e₂ * ((S.σ (π e₂))⁻¹ * (S.σ (π e₁))⁻¹)
      = e₁ * ((e₂ * (S.σ (π e₂))⁻¹) * (S.σ (π e₁))⁻¹) := by simp only [mul_assoc]
    _ = e₁ * ((S.σ (π e₁))⁻¹ * (e₂ * (S.σ (π e₂))⁻¹)) := by rw [← h]
    _ = e₁ * (S.σ (π e₁))⁻¹ * (e₂ * (S.σ (π e₂))⁻¹) := by simp only [mul_assoc]

theorem tau_inv (e : E) (he : π e • D = D) : S.tau e⁻¹ = (S.tau e)⁻¹ := by
  have he' : π e⁻¹ • D = D := by
    rw [map_inv, inv_smul_eq_iff]; exact he.symm
  have h := S.tau_mul e e⁻¹ he he'
  rw [mul_inv_cancel, S.tau_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem tau_central (e : E) (he : π e • D = D) : S.tau e ∈ Subgroup.center E :=
  S.central _ (S.tau_ker e he)

theorem tau_sq (e : E) (he : π e • D = D) : S.tau e * S.tau e = 1 :=
  S.sq _ (S.tau_ker e he)

end SplitData

@[expose] def InOrbit (G : Type*) [Group G] {X : Type*} [MulAction G X] (D y : X) : Prop :=
  ∃ a : G, a • D = y

theorem InOrbit.smul {D y : X} (h : InOrbit G D y) (a : G) : InOrbit G D (a • y) := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨a * b, mul_smul a b D⟩

@[expose] def edgeElt (x : Fin 2 → E) (g : Fin 2 → G) (lift : X → E) (y : X) (l : Letter) : E :=
  (lift (letterVal g l • y))⁻¹ * letterVal x l * lift y

open Classical in
@[expose] noncomputable def muPlus {π : E →* G} {D : X} (S : SplitData π D) (x : Fin 2 → E)
    (g : Fin 2 → G) (lift : X → E) (k : X × Fin 2) : E :=
  if InOrbit G D k.1 then S.tau (edgeElt x g lift k.1 (k.2, true)) else 1

section Telescoping

variable {π : E →* G} {D : X} (S : SplitData π D) {x : Fin 2 → E} {g : Fin 2 → G}
  (hg : ∀ i, π (x i) = g i) {lift : X → E} (hlift : ∀ y, InOrbit G D y → π (lift y) • D = y)

include hg hlift in
theorem edgeElt_good {y : X} (hy : InOrbit G D y) (l : Letter) :
    π (edgeElt x g lift y l) • D = D := by
  have hl : π (letterVal x l) = letterVal g l := by
    rw [map_letterVal]
    simp only [hg]
  have h1 : π (lift y) • D = y := hlift y hy
  have h2 : π (lift (letterVal g l • y)) • D = letterVal g l • y := hlift _ (hy.smul _)
  have h3 : π (edgeElt x g lift y l) =
      (π (lift (letterVal g l • y)))⁻¹ * letterVal g l * π (lift y) := by
    simp only [edgeElt, map_mul, map_inv, hl]
  rw [h3, mul_smul, mul_smul, h1, inv_smul_eq_iff]
  exact h2.symm

include hg hlift in
theorem tau_edgeElt {y : X} (hy : InOrbit G D y) (l : Letter) :
    S.tau (edgeElt x g lift y l) = muPlus S x g lift (letterKey g y l) := by
  obtain ⟨i, b⟩ := l
  cases b
  ·
    have hy₂ : InOrbit G D ((g i)⁻¹ • y) := hy.smul _
    have hgood : π (edgeElt x g lift ((g i)⁻¹ • y) (i, true)) • D = D :=
      edgeElt_good hg hlift hy₂ (i, true)
    have hinv : edgeElt x g lift y (i, false) = (edgeElt x g lift ((g i)⁻¹ • y) (i, true))⁻¹ := by
      simp only [edgeElt, letterVal, ↓reduceIte, Bool.false_eq_true, smul_inv_smul, mul_inv_rev,
        inv_inv, mul_assoc]
    rw [hinv, S.tau_inv _ hgood, letterKey_false]
    unfold muPlus
    simp only [hy₂, ↓reduceIte]
    exact inv_eq_of_mul_eq_one_right (S.tau_sq _ hgood)
  · rw [letterKey_true]
    unfold muPlus
    simp only [hy, ↓reduceIte]

include hg hlift in
theorem telescoping {y : X} (hy : InOrbit G D y) (w : List Letter) :
    InOrbit G D (pathEnd g w y) ∧
    π ((lift (pathEnd g w y))⁻¹ * wordVal x w * lift y) • D = D ∧
    S.tau ((lift (pathEnd g w y))⁻¹ * wordVal x w * lift y) =
      ((wordKeys g w y).map (muPlus S x g lift)).prod := by
  induction w with
  | nil =>
    refine ⟨hy, ?_, ?_⟩
    · simp [pathEnd]
    · simp [pathEnd, wordKeys, S.tau_one]
  | cons l w ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hy₁ : InOrbit G D (letterVal g l • pathEnd g w y) := h0.smul _
    have hpath : pathEnd g (l :: w) y = letterVal g l • pathEnd g w y := rfl
    have hsplit : (lift (pathEnd g (l :: w) y))⁻¹ * wordVal x (l :: w) * lift y =
        edgeElt x g lift (pathEnd g w y) l *
          ((lift (pathEnd g w y))⁻¹ * wordVal x w * lift y) := by
      rw [hpath, wordVal_cons]
      unfold edgeElt
      group
    have hgood : π (edgeElt x g lift (pathEnd g w y) l) • D = D :=
      edgeElt_good hg hlift h0 l
    refine ⟨hy₁, ?_, ?_⟩
    · rw [hsplit, map_mul, mul_smul, h1, hgood]
    · rw [hsplit, S.tau_mul _ _ hgood h1, h2, tau_edgeElt S hg hlift h0 l]
      simp [wordKeys]

include hg hlift in
theorem cell_value {y : X} (hy : InOrbit G D y) (w : List Letter) (hw : wordVal g w = 1) :
    wordVal x w = ((wordKeys g w y).map (muPlus S x g lift)).prod := by
  obtain ⟨-, -, h3⟩ := telescoping S hg hlift hy w
  have hpath : pathEnd g w y = y := by rw [pathEnd_eq, hw, one_smul]
  have hker : π (wordVal x w) = 1 := by
    rw [map_wordVal]
    have : (fun i => π (x i)) = g := funext hg
    rw [this]
    exact hw
  have hcen := S.central _ hker
  have hconj : (lift y)⁻¹ * wordVal x w * lift y = wordVal x w := by
    have := Subgroup.mem_center_iff.mp hcen (lift y)⁻¹
    rw [this, mul_assoc, inv_mul_cancel, mul_one]
  rw [hpath, hconj, S.tau_of_ker _ hker] at h3
  exact h3

end Telescoping

theorem prod_flatMap_map {α β : Type*} (K : α → List β) (μ : β → E) :
    ∀ cells : List α,
      ((cells.flatMap K).map μ).prod = (cells.map fun c => ((K c).map μ).prod).prod
  | [] => rfl
  | c :: cells => by
    simp [List.flatMap_cons, List.map_append, List.prod_append, prod_flatMap_map K μ cells]

theorem cycle_relation [DecidableEq X] {π : E →* G} {D : X} (S : SplitData π D)
    (hπ : Function.Surjective π) {x : Fin 2 → E} {g : Fin 2 → G} (hg : ∀ i, π (x i) = g i)
    (cells : List (X × List Letter)) (hrel : ∀ c ∈ cells, wordVal g c.2 = 1)
    (horb : ∀ c ∈ cells, InOrbit G D c.1)
    (heven : ∀ k ∈ cells.flatMap (fun c => wordKeys g c.2 c.1),
      Even ((cells.flatMap (fun c => wordKeys g c.2 c.1)).count k)) :
    (cells.map fun c => wordVal x c.2).prod = 1 := by
  classical
  let lift : X → E := fun y =>
    if h : InOrbit G D y then Classical.choose (hπ (Classical.choose h)) else 1
  have hlift : ∀ y, InOrbit G D y → π (lift y) • D = y := by
    intro y hy
    have h1 := Classical.choose_spec hy
    have h2 := Classical.choose_spec (hπ (Classical.choose hy))
    simp only [lift, hy, ↓reduceDIte]
    rw [h2]
    exact h1
  have hμc : ∀ k, muPlus S x g lift k ∈ Subgroup.center E := by
    intro k
    by_cases hk : InOrbit G D k.1
    · simp only [muPlus, hk, ↓reduceIte]
      exact S.tau_central _ (edgeElt_good hg hlift hk _)
    · simp only [muPlus, hk, ↓reduceIte]
      exact Subgroup.one_mem _
  have hμsq : ∀ k, muPlus S x g lift k * muPlus S x g lift k = 1 := by
    intro k
    by_cases hk : InOrbit G D k.1
    · simp only [muPlus, hk, ↓reduceIte]
      exact S.tau_sq _ (edgeElt_good hg hlift hk _)
    · simp only [muPlus, hk, ↓reduceIte, mul_one]
  have hcells : ∀ c ∈ cells,
      wordVal x c.2 = ((wordKeys g c.2 c.1).map (muPlus S x g lift)).prod :=
    fun c hc => cell_value S hg hlift (horb c hc) c.2 (hrel c hc)
  rw [List.map_congr_left hcells,
    ← prod_flatMap_map (fun c => wordKeys g c.2 c.1) (muPlus S x g lift) cells]
  exact prod_eq_one_of_even _ hμc hμsq _ heven

end Cycle

end CFSG.QuasithinUnique.Vol2Native.L239.Covers
