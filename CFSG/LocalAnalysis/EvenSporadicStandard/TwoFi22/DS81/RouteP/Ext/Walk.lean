module

public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Sporadic.Bridge

structure ExtData {M W : Type*} [Group M] [CommGroup W] (ρ : M →* MulAut W) (N : Type*)
    [Group N] where
  π : N →* M
  eT : N → W
  π_surjective : Function.Surjective π
  eT_mul : ∀ x y, π x = 1 → π y = 1 → eT (x * y) = eT x * eT y
  eT_conj : ∀ n x, π x = 1 → eT (n * x * n⁻¹) = ρ (π n) (eT x)
  eT_inj : ∀ x y, π x = 1 → π y = 1 → eT x = eT y → x = y
  eT_surj : ∀ w, ∃ x, π x = 1 ∧ eT x = w

namespace ExtData

variable {M W N : Type*} [Group M] [CommGroup W] [Group N] {ρ : M →* MulAut W}
  (X : ExtData ρ N)

theorem eT_one : X.eT 1 = 1 := by
  have h := X.eT_mul 1 1 (map_one _) (map_one _)
  rw [one_mul] at h
  exact left_eq_mul.1 h

theorem eT_inv {x : N} (hx : X.π x = 1) : X.eT x⁻¹ = (X.eT x)⁻¹ := by
  have hx' : X.π x⁻¹ = 1 := by rw [map_inv, hx, inv_one]
  have h := X.eT_mul x x⁻¹ hx hx'
  rw [mul_inv_cancel, X.eT_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem eT_inv_of_sq (hW : ∀ w : W, w * w = 1) {x : N} (hx : X.π x = 1) :
    X.eT x⁻¹ = X.eT x := by
  rw [X.eT_inv hx]
  exact inv_eq_of_mul_eq_one_right (hW _)

theorem π_eq_one_mul {x y : N} (hx : X.π x = 1) (hy : X.π y = 1) : X.π (x * y) = 1 := by
  rw [map_mul, hx, hy, one_mul]

end ExtData

@[expose] def letterVal {G : Type*} [Group G] (x : ℕ → G) (l : ℕ × Bool) : G :=
  if l.2 then x l.1 else (x l.1)⁻¹

theorem wordProd_nil {G : Type*} [Group G] (x : ℕ → G) : wordProd x [] = 1 := rfl

theorem wordProd_cons {G : Type*} [Group G] (x : ℕ → G) (l : ℕ × Bool) (w : List (ℕ × Bool)) :
    wordProd x (l :: w) = letterVal x l * wordProd x w := by
  simp only [wordProd, letterVal, List.map_cons, List.prod_cons]

theorem map_letterVal {G H : Type*} [Group G] [Group H] (φ : G →* H) (x : ℕ → G)
    (l : ℕ × Bool) : φ (letterVal x l) = letterVal (fun i => φ (x i)) l := by
  unfold letterVal
  split_ifs <;> simp

variable {M : Type*} [Group M]

@[expose] def walkEdges (g : ℕ → M) : List (ℕ × Bool) → M → List (M × ℕ)
  | [], _ => []
  | l :: w, h =>
    ((if l.2 then h else h * (g l.1)⁻¹), l.1) :: walkEdges g w (h * letterVal g l)

@[simp] theorem walkEdges_nil (g : ℕ → M) (h : M) : walkEdges g [] h = [] := rfl

theorem walkEdges_cons (g : ℕ → M) (l : ℕ × Bool) (w : List (ℕ × Bool)) (h : M) :
    walkEdges g (l :: w) h =
      ((if l.2 then h else h * (g l.1)⁻¹), l.1) :: walkEdges g w (h * letterVal g l) := rfl

@[expose] def edgeElt {G : Type*} [Group G] (s : M → G) (x : ℕ → G) (g : ℕ → M) (h : M)
    (i : ℕ) : G :=
  s h * x i * (s (h * g i))⁻¹

theorem ExtData.π_wordProd {W N : Type*} [CommGroup W] [Group N] {ρ : M →* MulAut W}
    (X : ExtData ρ N) {g : ℕ → M} {xt : ℕ → N} (hxt : ∀ i, X.π (xt i) = g i)
    (w : List (ℕ × Bool)) : X.π (wordProd xt w) = wordProd g w := by
  rw [map_wordProd]
  simp only [hxt]

theorem ExtData.π_letterVal {W N : Type*} [CommGroup W] [Group N] {ρ : M →* MulAut W}
    (X : ExtData ρ N) {g : ℕ → M} {xt : ℕ → N} (hxt : ∀ i, X.π (xt i) = g i)
    (l : ℕ × Bool) : X.π (letterVal xt l) = letterVal g l := by
  rw [map_letterVal]
  simp only [hxt]

section Telescoping

variable {W N : Type*} [CommGroup W] [Group N] {ρ : M →* MulAut W}

theorem eT_walk (X : ExtData ρ N) (hW : ∀ w : W, w * w = 1) {g : ℕ → M} {xt : ℕ → N}
    (hxt : ∀ i, X.π (xt i) = g i) {s : M → N} (hs : ∀ h, X.π (s h) = h) :
    ∀ (w : List (ℕ × Bool)) (h : M),
      X.π (s h * wordProd xt w * (s (h * wordProd g w))⁻¹) = 1 ∧
      X.eT (s h * wordProd xt w * (s (h * wordProd g w))⁻¹) =
        ((walkEdges g w h).map fun e => X.eT (edgeElt s xt g e.1 e.2)).prod
  | [], h => by
    simp only [wordProd_nil, mul_one, walkEdges_nil, List.map_nil, List.prod_nil, mul_inv_cancel]
    exact ⟨map_one _, X.eT_one⟩
  | l :: w, h => by
    obtain ⟨ih1, ih2⟩ := eT_walk X hW hxt hs w (h * letterVal g l)
    set h' := h * letterVal g l with hh'
    have hsplit : s h * wordProd xt (l :: w) * (s (h * wordProd g (l :: w)))⁻¹ =
        (s h * letterVal xt l * (s h')⁻¹) *
          (s h' * wordProd xt w * (s (h' * wordProd g w))⁻¹) := by
      rw [wordProd_cons, wordProd_cons, ← mul_assoc h, ← hh']
      group
    have hA : X.π (s h * letterVal xt l * (s h')⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hs, hs, X.π_letterVal hxt, hh']
      group
    rw [hsplit]
    refine ⟨X.π_eq_one_mul hA ih1, ?_⟩
    rw [X.eT_mul _ _ hA ih1, ih2, walkEdges_cons, List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · simp only [letterVal, Bool.false_eq_true, ↓reduceIte] at hh' ⊢
      have hφ : s h * (xt i)⁻¹ * (s h')⁻¹ = (edgeElt s xt g (h * (g i)⁻¹) i)⁻¹ := by
        have : h * (g i)⁻¹ * g i = h := by group
        simp only [edgeElt, this, hh']
        group
      rw [hφ, X.eT_inv_of_sq hW]
      rw [edgeElt, map_mul, map_mul, map_inv, hs, hs, hxt]
      group
    · simp only [letterVal, ↓reduceIte] at hh' ⊢
      rfl

end Telescoping

section ChangeLift

variable {W N : Type*} [CommGroup W] [Group N] {ρ : M →* MulAut W}

theorem exists_letter_changeLift (X : ExtData ρ N) (hW : ∀ w : W, w * w = 1) {g : ℕ → M}
    {xt z : ℕ → N} (hxt : ∀ i, X.π (xt i) = g i) (hz : ∀ i, X.π (z i) = 1) (u : N)
    (l : ℕ × Bool) :
    ∃ c : N, X.π c = 1 ∧
      X.eT c = ρ (if l.2 then X.π u else X.π u * (g l.1)⁻¹) (X.eT (z l.1)) ∧
      u * letterVal (fun i => z i * xt i) l = c * (u * letterVal xt l) := by
  obtain ⟨i, b⟩ := l
  cases b
  · refine ⟨(u * (xt i)⁻¹) * (z i)⁻¹ * (u * (xt i)⁻¹)⁻¹, ?_, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, map_inv, hz, inv_one, mul_one, mul_inv_cancel]
    · have h := X.eT_conj (u * (xt i)⁻¹) (z i)⁻¹ (by rw [map_inv, hz, inv_one])
      rw [X.eT_inv_of_sq hW (hz i), map_mul, map_inv, hxt] at h
      simpa using h
    · simp only [letterVal, Bool.false_eq_true, ↓reduceIte]
      group
  · refine ⟨u * z i * u⁻¹, ?_, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, hz, mul_one, mul_inv_cancel]
    · simpa using X.eT_conj u (z i) (hz i)
    · simp only [letterVal, ↓reduceIte]
      group

theorem exists_changeLift (X : ExtData ρ N) (hW : ∀ w : W, w * w = 1) {g : ℕ → M}
    {xt z : ℕ → N} (hxt : ∀ i, X.π (xt i) = g i) (hz : ∀ i, X.π (z i) = 1) :
    ∀ (w : List (ℕ × Bool)) (u : N),
      ∃ c : N, X.π c = 1 ∧
        X.eT c = ((walkEdges g w (X.π u)).map fun e => ρ e.1 (X.eT (z e.2))).prod ∧
        u * wordProd (fun i => z i * xt i) w = c * (u * wordProd xt w)
  | [], u => ⟨1, map_one _, by simp [X.eT_one], by simp [wordProd_nil]⟩
  | l :: w, u => by
    obtain ⟨c₁, hc₁π, hc₁e, hc₁⟩ := exists_letter_changeLift X hW hxt hz u l
    obtain ⟨c', hc'π, hc'e, hc'⟩ := exists_changeLift X hW hxt hz w (u * letterVal xt l)
    refine ⟨c₁ * c', X.π_eq_one_mul hc₁π hc'π, ?_, ?_⟩
    · rw [X.eT_mul _ _ hc₁π hc'π, hc₁e, hc'e, walkEdges_cons, List.map_cons, List.prod_cons,
        map_mul, X.π_letterVal hxt]
    · rw [wordProd_cons, wordProd_cons, ← mul_assoc u, hc₁, mul_assoc c₁, hc', ← mul_assoc c₁,
        mul_assoc u]

theorem eT_wordProd_changeLift (X : ExtData ρ N) (hW : ∀ w : W, w * w = 1) {g : ℕ → M}
    {xt z : ℕ → N} (hxt : ∀ i, X.π (xt i) = g i) (hz : ∀ i, X.π (z i) = 1)
    (w : List (ℕ × Bool)) (hw : wordProd g w = 1) :
    X.π (wordProd (fun i => z i * xt i) w) = 1 ∧
    X.eT (wordProd (fun i => z i * xt i) w) = X.eT (wordProd xt w) *
      ((walkEdges g w 1).map fun e => ρ e.1 (X.eT (z e.2))).prod := by
  obtain ⟨c, hcπ, hce, hc⟩ := exists_changeLift X hW hxt hz w 1
  rw [map_one] at hce
  rw [one_mul, one_mul] at hc
  have hw1 : X.π (wordProd xt w) = 1 := by rw [X.π_wordProd hxt, hw]
  rw [hc]
  exact ⟨X.π_eq_one_mul hcπ hw1, by rw [X.eT_mul _ _ hcπ hw1, hce, mul_comm]⟩

end ChangeLift

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
