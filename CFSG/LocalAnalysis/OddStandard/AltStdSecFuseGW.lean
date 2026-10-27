module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseWr

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

variable {D : Type*} [Group D] {R : Type*} [CommSemiring R]

open scoped Classical in
@[expose] noncomputable def wrW (w : D → R) (c : R) (y : D ≀ᵣ Z2) : R :=
  if y.right = 1 then w (y.left 1) * w (y.left z2)
  else if y.left z2 = (y.left 1)⁻¹ then c else 0

open scoped Classical in
@[expose] noncomputable def trSum {D : Type*} [Group D] {R : Type*} [CommSemiring R]
    (w : Fin 3 → D → R) (g : D) : R :=
  ∑ᶠ t : Fin 3 → D, if t 0 * t 1 * t 2 = g then ∏ j, w j (t j) else 0

section Tri

variable {G : Type*} [Group G] [Fintype G]

open scoped Classical in
private noncomputable def tri3 (A B C : G → R) (u : G) : R :=
  ∑ x : G, ∑ y : G, ∑ z : G, if x * y * z = u then A x * B y * C z else 0

open scoped Classical in
private theorem trSum_eq_tri3 (w : Fin 3 → G → R) (u : G) :
    trSum w u = tri3 (w 0) (w 1) (w 2) u := by
  unfold trSum
  rw [finsum_eq_sum_of_fintype]
  simp only [Fin.prod_univ_three]
  let e : (Fin 3 → G) ≃ G × G × G :=
    { toFun := fun t => (t 0, t 1, t 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun t => by ext i; fin_cases i <;> rfl
      right_inv := fun p => rfl }
  refine (Fintype.sum_equiv e _
    (fun p : G × G × G => if p.1 * p.2.1 * p.2.2 = u then w 0 p.1 * w 1 p.2.1 * w 2 p.2.2 else 0)
    (fun t => rfl)).trans ?_
  simp only [Fintype.sum_prod_type, tri3]

private theorem tri3_add_left (A A' B C : G → R) (u : G) :
    tri3 (A + A') B C u = tri3 A B C u + tri3 A' B C u := by
  unfold tri3
  simp only [Pi.add_apply, add_mul, ite_add_zero, Finset.sum_add_distrib]

private theorem tri3_add_mid (A B B' C : G → R) (u : G) :
    tri3 A (B + B') C u = tri3 A B C u + tri3 A B' C u := by
  unfold tri3
  simp only [Pi.add_apply, add_mul, mul_add, ite_add_zero, Finset.sum_add_distrib]

private theorem tri3_add_right (A B C C' : G → R) (u : G) :
    tri3 A B (C + C') u = tri3 A B C u + tri3 A B C' u := by
  unfold tri3
  simp only [Pi.add_apply, mul_add, ite_add_zero, Finset.sum_add_distrib]

private theorem tri3_add (A A' B B' C C' : G → R) (u : G) :
    tri3 (A + A') (B + B') (C + C') u =
      tri3 A B C u + tri3 A B C' u + tri3 A B' C u + tri3 A B' C' u +
      tri3 A' B C u + tri3 A' B C' u + tri3 A' B' C u + tri3 A' B' C' u := by
  simp only [tri3_add_left, tri3_add_mid, tri3_add_right]
  ring

private theorem tri3_eq_zero (A B C : G → R) (u : G)
    (h : ∀ x y z, x * y * z = u → A x * B y * C z = 0) : tri3 A B C u = 0 := by
  unfold tri3
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ =>
    Finset.sum_eq_zero fun z _ => ?_
  split_ifs with hxyz
  · exact h x y z hxyz
  · rfl

omit [Group G] in
private theorem sum_ite_of_iff {α : Type*} [Fintype α] (f : α → R) (P : α → Prop)
    [DecidablePred P] (a : α) (h : ∀ x, P x ↔ x = a) : ∑ x, (if P x then f x else 0) = f a := by
  rw [Finset.sum_eq_single a]
  · simp [(h a).2 rfl]
  · intro x _ hx
    have hp : ¬ P x := fun hp => hx ((h x).1 hp)
    simp [hp]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

open scoped Classical in
private theorem tri3_elim_first (A B C : G → R) (u : G) :
    tri3 A B C u = ∑ y : G, ∑ z : G, A (u * z⁻¹ * y⁻¹) * B y * C z := by
  unfold tri3
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact sum_ite_of_iff (fun x => A x * B y * C z) (fun x => x * y * z = u) (u * z⁻¹ * y⁻¹)
    fun x => by rw [eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq]

open scoped Classical in
private theorem tri3_elim_mid (A B C : G → R) (u : G) :
    tri3 A B C u = ∑ x : G, ∑ z : G, A x * B (x⁻¹ * u * z⁻¹) * C z := by
  unfold tri3
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact sum_ite_of_iff (fun y => A x * B y * C z) (fun y => x * y * z = u) (x⁻¹ * u * z⁻¹)
    fun y => by rw [eq_mul_inv_iff_mul_eq, eq_inv_mul_iff_mul_eq, mul_assoc]

open scoped Classical in
private theorem tri3_elim_last (A B C : G → R) (u : G) :
    tri3 A B C u = ∑ x : G, ∑ y : G, A x * B y * C ((x * y)⁻¹ * u) := by
  unfold tri3
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  exact sum_ite_of_iff (fun z => A x * B y * C z) (fun z => x * y * z = u) ((x * y)⁻¹ * u)
    fun z => by rw [eq_inv_mul_iff_mul_eq]

end Tri

section Wreath

open scoped Classical in
private noncomputable def wrP1 (w : D → R) (y : D ≀ᵣ Z2) : R :=
  if y.right = 1 then w (y.left 1) * w (y.left z2) else 0

open scoped Classical in
private noncomputable def wrPz (c : R) (y : D ≀ᵣ Z2) : R :=
  if y.right = z2 then (if y.left z2 = (y.left 1)⁻¹ then c else 0) else 0

private theorem wrW_eq (w : D → R) (c : R) : wrW w c = wrP1 w + wrPz c := by
  funext y
  rcases z2_cases y.right with h | h <;> simp [wrW, wrP1, wrPz, h, z2_ne_one, z2_ne_one.symm]

omit [Group D] in
private theorem wrP1_wr_one (w : D → R) (a b : D) : wrP1 w (wr a b 1) = w a * w b := by
  simp [wrP1]

omit [Group D] in
private theorem wrP1_of_ne (w : D → R) {y : D ≀ᵣ Z2} (h : y.right ≠ 1) : wrP1 w y = 0 := by
  simp [wrP1, h]

private theorem wrPz_of_ne (c : R) {y : D ≀ᵣ Z2} (h : y.right ≠ z2) : wrPz c y = 0 := by
  simp [wrPz, h]

private theorem wr_inv_one (a b : D) : (wr a b 1)⁻¹ = wr a⁻¹ b⁻¹ 1 := by
  rw [inv_eq_iff_mul_eq_one, wr_mul_one, mul_inv_cancel, mul_inv_cancel, wr_one]

private theorem wr_inv_z2 (a b : D) : (wr a b z2)⁻¹ = wr b⁻¹ a⁻¹ z2 := by
  rw [inv_eq_iff_mul_eq_one, wr_mul_z2, mul_inv_cancel, mul_inv_cancel, z2_mul_self, wr_one]

omit [Group D] in
private theorem sum_wrP1 [Fintype D] [Fintype (D ≀ᵣ Z2)] (w : D → R) (F : D ≀ᵣ Z2 → R) :
    ∑ y : D ≀ᵣ Z2, wrP1 w y * F y = ∑ a : D, ∑ b : D, w a * w b * F (wr a b 1) := by
  rw [← Equiv.sum_comp wrEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_eq_single 1]
  · simp [wrEquiv, wrP1_wr_one]
  · intro q hq
    simp [wrEquiv, wrP1, hq]

private theorem sum_wrPz [Fintype D] [Fintype (D ≀ᵣ Z2)] (c : R) (F : D ≀ᵣ Z2 → R) :
    ∑ y : D ≀ᵣ Z2, wrPz c y * F y = ∑ h : D, c * F (wr h h⁻¹ z2) := by
  rw [← Equiv.sum_comp wrEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single a⁻¹]
  · rw [Fintype.sum_eq_single z2]
    · simp [wrEquiv, wrPz]
    · intro q hq
      simp [wrEquiv, wrPz, hq]
  · intro b hb
    rw [Fintype.sum_eq_single z2]
    · simp [wrEquiv, wrPz, hb]
    · intro q hq
      simp [wrEquiv, wrPz, hq]

private theorem tops_of_eq {x y z : D ≀ᵣ Z2} {g : D} (h : x * y * z = diag g) :
    x.right * y.right * z.right = 1 := by
  have := congrArg RegularWreathProduct.right h
  simpa [RegularWreathProduct.mul_right, diag] using this

variable [Fintype (D ≀ᵣ Z2)]

private theorem tri3_top_zero (A B C : D ≀ᵣ Z2 → R) (q₀ q₁ q₂ : Z2) (hq : q₀ * q₁ * q₂ ≠ 1)
    (hA : ∀ x : D ≀ᵣ Z2, x.right ≠ q₀ → A x = 0) (hB : ∀ y : D ≀ᵣ Z2, y.right ≠ q₁ → B y = 0)
    (hC : ∀ z : D ≀ᵣ Z2, z.right ≠ q₂ → C z = 0) (g : D) : tri3 A B C (diag g) = 0 := by
  refine tri3_eq_zero _ _ _ _ fun x y z h => ?_
  have ht := tops_of_eq h
  by_cases hx : x.right = q₀
  · by_cases hy : y.right = q₁
    · by_cases hz : z.right = q₂
      · rw [hx, hy, hz] at ht
        exact absurd ht hq
      · rw [hC z hz, mul_zero]
    · rw [hB y hy, mul_zero, zero_mul]
  · rw [hA x hx, zero_mul, zero_mul]

private theorem tri3_PPZ (a b : D → R) (c : R) (g : D) :
    tri3 (wrP1 a) (wrP1 b) (wrPz c) (diag g) = 0 :=
  tri3_top_zero _ _ _ 1 1 z2 (by decide) (fun _ h => wrP1_of_ne a h) (fun _ h => wrP1_of_ne b h)
    (fun _ h => wrPz_of_ne c h) g

private theorem tri3_PZP (a b : D → R) (c : R) (g : D) :
    tri3 (wrP1 a) (wrPz c) (wrP1 b) (diag g) = 0 :=
  tri3_top_zero _ _ _ 1 z2 1 (by decide) (fun _ h => wrP1_of_ne a h) (fun _ h => wrPz_of_ne c h)
    (fun _ h => wrP1_of_ne b h) g

private theorem tri3_ZPP (a b : D → R) (c : R) (g : D) :
    tri3 (wrPz c) (wrP1 a) (wrP1 b) (diag g) = 0 :=
  tri3_top_zero _ _ _ z2 1 1 (by decide) (fun _ h => wrPz_of_ne c h) (fun _ h => wrP1_of_ne a h)
    (fun _ h => wrP1_of_ne b h) g

private theorem tri3_ZZZ (a b c : R) (g : D) :
    tri3 (wrPz a) (wrPz b) (wrPz c) (diag g) = 0 :=
  tri3_top_zero _ _ _ z2 z2 z2 (by decide) (fun _ h => wrPz_of_ne a h) (fun _ h => wrPz_of_ne b h)
    (fun _ h => wrPz_of_ne c h) g

private theorem tri3_PZZ [Fintype D] (a : D → R) (c₁ c₂ : R) (g : D) :
    tri3 (wrP1 a) (wrPz c₁) (wrPz c₂) (diag g) =
      c₁ * c₂ * ∑ h : D, ∑ k : D, a (g * k * h⁻¹) * a (g * k⁻¹ * h) := by
  rw [tri3_elim_first]
  have e1 : ∀ y : D ≀ᵣ Z2, ∑ z : D ≀ᵣ Z2, wrP1 a (diag g * z⁻¹ * y⁻¹) * wrPz c₁ y * wrPz c₂ z =
      wrPz c₁ y * ∑ z : D ≀ᵣ Z2, wrPz c₂ z * wrP1 a (diag g * z⁻¹ * y⁻¹) := fun y => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  have e2 : ∀ h k : D, diag g * (wr k k⁻¹ z2)⁻¹ * (wr h h⁻¹ z2)⁻¹ =
      wr (g * k * h⁻¹) (g * k⁻¹ * h) 1 := fun h k => by
    simp only [wr_inv_z2, inv_inv, diag_eq_wr, wr_mul_one, wr_mul_z2, z2_mul_self]
  simp only [e1, sum_wrPz, e2, wrP1_wr_one]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => by ring

private theorem tri3_ZPZ [Fintype D] (a : D → R) (c₀ c₂ : R) (g : D) :
    tri3 (wrPz c₀) (wrP1 a) (wrPz c₂) (diag g) =
      c₀ * c₂ * ∑ h : D, ∑ k : D, a (h * g * k⁻¹) * a (h⁻¹ * g * k) := by
  rw [tri3_elim_mid]
  have e1 : ∀ x : D ≀ᵣ Z2,
      ∑ z : D ≀ᵣ Z2, wrPz c₀ x * wrP1 a (x⁻¹ * diag g * z⁻¹) * wrPz c₂ z =
      wrPz c₀ x * ∑ z : D ≀ᵣ Z2, wrPz c₂ z * wrP1 a (x⁻¹ * diag g * z⁻¹) := fun x => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  have e2 : ∀ h k : D, (wr h h⁻¹ z2)⁻¹ * diag g * (wr k k⁻¹ z2)⁻¹ =
      wr (h * g * k⁻¹) (h⁻¹ * g * k) 1 := fun h k => by
    simp only [wr_inv_z2, inv_inv, diag_eq_wr, wr_mul_z2, z2_mul_self, mul_one]
  simp only [e1, sum_wrPz, e2, wrP1_wr_one]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => by ring

private theorem tri3_ZZP [Fintype D] (a : D → R) (c₀ c₁ : R) (g : D) :
    tri3 (wrPz c₀) (wrPz c₁) (wrP1 a) (diag g) =
      c₀ * c₁ * ∑ h : D, ∑ k : D, a (k * h⁻¹ * g) * a (k⁻¹ * h * g) := by
  rw [tri3_elim_last]
  have e1 : ∀ x : D ≀ᵣ Z2,
      ∑ y : D ≀ᵣ Z2, wrPz c₀ x * wrPz c₁ y * wrP1 a ((x * y)⁻¹ * diag g) =
      wrPz c₀ x * ∑ y : D ≀ᵣ Z2, wrPz c₁ y * wrP1 a ((x * y)⁻¹ * diag g) := fun x => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have e2 : ∀ h k : D, (wr h h⁻¹ z2 * wr k k⁻¹ z2)⁻¹ * diag g =
      wr (k * h⁻¹ * g) (k⁻¹ * h * g) 1 := fun h k => by
    simp only [wr_mul_z2, z2_mul_self, wr_inv_one, mul_inv_rev, inv_inv, diag_eq_wr, wr_mul_one]
  simp only [e1, sum_wrPz, e2, wrP1_wr_one]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => by ring

private theorem tri3_PPP [Fintype D] (a : Fin 3 → D → R) (g : D) :
    tri3 (wrP1 (a 0)) (wrP1 (a 1)) (wrP1 (a 2)) (diag g) = trSum a g ^ 2 := by
  rw [trSum_eq_tri3, tri3_elim_first, tri3_elim_first, sq]
  have e1 : ∀ y : D ≀ᵣ Z2,
      ∑ z : D ≀ᵣ Z2, wrP1 (a 0) (diag g * z⁻¹ * y⁻¹) * wrP1 (a 1) y * wrP1 (a 2) z =
      wrP1 (a 1) y * ∑ z : D ≀ᵣ Z2, wrP1 (a 2) z * wrP1 (a 0) (diag g * z⁻¹ * y⁻¹) := fun y => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  have e2 : ∀ p₁ q₁ p₂ q₂ : D, diag g * (wr p₂ q₂ 1)⁻¹ * (wr p₁ q₁ 1)⁻¹ =
      wr (g * p₂⁻¹ * p₁⁻¹) (g * q₂⁻¹ * q₁⁻¹) 1 := fun p₁ q₁ p₂ q₂ => by
    simp only [wr_inv_one, diag_eq_wr, wr_mul_one]
  simp only [e1, sum_wrP1, e2, wrP1_wr_one, Fintype.sum_mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun q₁ _ =>
    Finset.sum_congr rfl fun p₂ _ => Finset.sum_congr rfl fun q₂ _ => by ring

end Wreath

theorem trSum_wrW [Finite D] (w : Fin 3 → D → R) (c : Fin 3 → R) (g : D) :
    trSum (fun j => wrW (w j) (c j)) (diag g) = trSum w g ^ 2 +
      c 1 * c 2 * ∑ᶠ hk : D × D, w 0 (g * hk.2 * hk.1⁻¹) * w 0 (g * hk.2⁻¹ * hk.1) +
      c 0 * c 2 * ∑ᶠ hk : D × D, w 1 (hk.1 * g * hk.2⁻¹) * w 1 (hk.1⁻¹ * g * hk.2) +
      c 0 * c 1 * ∑ᶠ hk : D × D, w 2 (hk.2 * hk.1⁻¹ * g) * w 2 (hk.2⁻¹ * hk.1 * g) := by
  have := Fintype.ofFinite D
  have : Fintype (D ≀ᵣ Z2) := Fintype.ofFinite _
  rw [trSum_eq_tri3]
  simp only [wrW_eq]
  rw [tri3_add, tri3_PPP, tri3_PZZ, tri3_ZPZ, tri3_ZZP, tri3_PPZ, tri3_PZP, tri3_ZPP, tri3_ZZZ]
  simp only [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
  ring

private theorem mul_conj_inv_sq (f : D → R) (hf2 : ∀ x, x * x ≠ 1 → f x = 0)
    (hfc : ∀ x d, f (d * x * d⁻¹) = f x) (m d : D) :
    f m * f (d * m⁻¹ * d⁻¹) = f m ^ 2 := by
  rw [hfc]
  by_cases hm : m * m = 1
  · rw [inv_eq_of_mul_eq_one_right hm, sq]
  · simp [hf2 m hm]

omit [Group D] in
private theorem sum_const_pair [Fintype D] (f : D → R) :
    ∑ _h : D, ∑ x : D, f x = (Nat.card D : R) * ∑ x : D, f x := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem trSum_wrW_inv [Finite D] (w : Fin 3 → D → R) (c : Fin 3 → R) (g : D) (hg2 : g * g = 1)
    (hgc : ∀ d : D, d * g = g * d) (hw2 : ∀ j x, x * x ≠ 1 → w j x = 0)
    (hwc : ∀ j x d, w j (d * x * d⁻¹) = w j x) :
    trSum (fun j => wrW (w j) (c j)) (diag g) = trSum w g ^ 2 +
      (Nat.card D : R) * (c 1 * c 2 * ∑ᶠ x : D, w 0 x ^ 2 + c 0 * c 2 * ∑ᶠ x : D, w 1 x ^ 2 +
        c 0 * c 1 * ∑ᶠ x : D, w 2 x ^ 2) := by
  have := Fintype.ofFinite D
  rw [trSum_wrW]
  simp only [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have s0 : ∑ h : D, ∑ k : D, w 0 (g * k * h⁻¹) * w 0 (g * k⁻¹ * h) =
      (Nat.card D : R) * ∑ x : D, w 0 x ^ 2 := by
    have e : ∀ h k : D, w 0 (g * k * h⁻¹) * w 0 (g * k⁻¹ * h) = w 0 (g * k * h⁻¹) ^ 2 :=
      fun h k => by
        have e : g * k⁻¹ * h = h⁻¹ * (g * k * h⁻¹)⁻¹ * h⁻¹⁻¹ := by
          calc g * k⁻¹ * h = k⁻¹ * g⁻¹ * h := by rw [hginv, hgc k⁻¹]
            _ = _ := by group
        rw [e]
        exact mul_conj_inv_sq (w 0) (hw2 0) (hwc 0) _ _
    simp only [e]
    rw [← sum_const_pair]
    exact Finset.sum_congr rfl fun h _ =>
      Fintype.sum_equiv ((Equiv.mulLeft g).trans (Equiv.mulRight h⁻¹)) _ _ (fun k => rfl)
  have s1 : ∑ h : D, ∑ k : D, w 1 (h * g * k⁻¹) * w 1 (h⁻¹ * g * k) =
      (Nat.card D : R) * ∑ x : D, w 1 x ^ 2 := by
    have e : ∀ h k : D, w 1 (h * g * k⁻¹) * w 1 (h⁻¹ * g * k) = w 1 (h * g * k⁻¹) ^ 2 :=
      fun h k => by
        have e : h⁻¹ * g * k = h⁻¹ * (h * g * k⁻¹)⁻¹ * h⁻¹⁻¹ := by
          calc h⁻¹ * g * k = h⁻¹ * k * g⁻¹ := by
                rw [hginv, mul_assoc h⁻¹ k g, hgc k, ← mul_assoc]
            _ = _ := by group
        rw [e]
        exact mul_conj_inv_sq (w 1) (hw2 1) (hwc 1) _ _
    simp only [e]
    rw [← sum_const_pair]
    exact Finset.sum_congr rfl fun h _ =>
      Fintype.sum_equiv ((Equiv.inv D).trans (Equiv.mulLeft (h * g))) _ _ (fun k => rfl)
  have s2 : ∑ h : D, ∑ k : D, w 2 (k * h⁻¹ * g) * w 2 (k⁻¹ * h * g) =
      (Nat.card D : R) * ∑ x : D, w 2 x ^ 2 := by
    have e : ∀ h k : D, w 2 (k * h⁻¹ * g) * w 2 (k⁻¹ * h * g) = w 2 (k * h⁻¹ * g) ^ 2 :=
      fun h k => by
        have e : k⁻¹ * h * g = k⁻¹ * (k * h⁻¹ * g)⁻¹ * k⁻¹⁻¹ := by
          calc k⁻¹ * h * g = k⁻¹ * g⁻¹ * h := by
                rw [hginv, mul_assoc k⁻¹ g h, ← hgc h, ← mul_assoc]
            _ = _ := by group
        rw [e]
        exact mul_conj_inv_sq (w 2) (hw2 2) (hwc 2) _ _
    simp only [e]
    rw [← sum_const_pair]
    exact Finset.sum_congr rfl fun h _ =>
      Fintype.sum_equiv ((Equiv.mulRight h⁻¹).trans (Equiv.mulRight g)) _ _ (fun k => rfl)
  rw [s0, s1, s2]
  ring

theorem trSum_prod {E : Type*} [Group E] [Finite D] [Finite E] (w : Fin 3 → D → R)
    (v : Fin 3 → E → R) (g : D) (g' : E) :
    trSum (fun j (p : D × E) => w j p.1 * v j p.2) (g, g') = trSum w g * trSum v g' := by
  classical
  have := Fintype.ofFinite D
  have := Fintype.ofFinite E
  unfold trSum
  simp only [finsum_eq_sum_of_fintype]
  rw [Fintype.sum_mul_sum]
  rw [← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin 3) (fun _ => D) (fun _ => E)).symm,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  simp only [Equiv.arrowProdEquivProdArrow_symm_apply, Fin.prod_univ_three, Prod.mk_mul_mk,
    Prod.mk.injEq, ite_and, Finset.prod_mul_distrib]
  split_ifs <;> first | rfl | ring

end CFSG.OddStandard.AltStdSec.SylowSn
