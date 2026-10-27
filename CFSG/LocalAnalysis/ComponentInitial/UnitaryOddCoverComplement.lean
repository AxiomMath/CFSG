module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverSplit

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem mul_central_three {a b d c : G} (hc : c ∈ Subgroup.center G) :
    a * c * (b * c) * (d * c) = a * b * d * c ^ 3 := by
  have h1 : ∀ g, c * g = g * c := fun g => (Subgroup.mem_center_iff.mp hc g).symm
  rw [pow_three]
  calc a * c * (b * c) * (d * c) = a * (c * b) * c * d * c := by group
    _ = a * (b * c) * c * d * c := by rw [h1 b]
    _ = a * b * (c * (c * d)) * c := by group
    _ = a * b * (c * (d * c)) * c := by rw [h1 d]
    _ = a * b * ((c * d) * c) * c := by group
    _ = a * b * ((d * c) * c) * c := by rw [h1 d]
    _ = a * b * d * (c * (c * c)) := by group

end Group

variable {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 1 K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 1} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E) (hr : 2 ≤ r) {Vt : Subgroup E}
  (hVt : IsHermComplement θ Vt)

omit [CharP K 2] in
theorem conj_mem_preN_of_lift {A : GL (Fin r) K} {g : E}
    (hg : θ g = hypProj h r 1 (lHom h r A)) {y : E} (hy : y ∈ preN θ) : g * y * g⁻¹ ∈ preN θ := by
  obtain ⟨x, hx⟩ := mem_preN.mp hy
  exact (hx.conj A hg).mem

include hθ hC hr hVt in
theorem mul_comm_of_mem_Vt {v y : E} (hv : v ∈ Vt) (hy : y ∈ preN θ) : y * v = v * y :=
  (mul_comm_of_mem_preV_of_mem_preN hθ hC hr (hVt.le hv) hy).symm

include hθ hC hr hVt in
theorem complement_mul_mem {A : GL (Fin r) K} {g : E} (hg : θ g = hypProj h r 1 (lHom h r A))
    {y z : E} (hy : y ∈ preN θ) (hz : z ∈ preN θ)
    (hy' : y * (g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹) ∈ Vt)
    (hz' : z * (g * z * g⁻¹) * (g * (g * z * g⁻¹) * g⁻¹) ∈ Vt) :
    y * z * (g * (y * z) * g⁻¹) * (g * (g * (y * z) * g⁻¹) * g⁻¹) ∈ Vt := by
  set a₁ := g * y * g⁻¹ with ha₁
  set b₁ := g * z * g⁻¹ with hb₁
  set a₂ := g * a₁ * g⁻¹ with ha₂
  set b₂ := g * b₁ * g⁻¹ with hb₂
  have hma₁ : a₁ ∈ preN θ := conj_mem_preN_of_lift hg hy
  have hmb₁ : b₁ ∈ preN θ := conj_mem_preN_of_lift hg hz
  have hma₂ : a₂ ∈ preN θ := conj_mem_preN_of_lift hg hma₁
  have e1 : g * (y * z) * g⁻¹ = a₁ * b₁ := by rw [ha₁, hb₁]; group
  have e2 : g * (a₁ * b₁) * g⁻¹ = a₂ * b₂ := by rw [ha₂, hb₂]; group
  rw [e1, e2]
  have hc₁ := commutatorElement_mem_herm_complement hθ hC hVt hr hz hma₁
  have hc₂ := commutatorElement_mem_herm_complement hθ hC hVt hr (mul_mem hz hmb₁) hma₂
  have f1 : z * a₁ = ⁅z, a₁⁆ * (a₁ * z) := by rw [commutatorElement_def]; group
  have f2 : z * b₁ * a₂ = ⁅z * b₁, a₂⁆ * (a₂ * (z * b₁)) := by rw [commutatorElement_def]; group
  have k1 : y * ⁅z, a₁⁆ = ⁅z, a₁⁆ * y := mul_comm_of_mem_Vt hθ hC hr hVt hc₁ hy
  have k2 : y * a₁ * ⁅z * b₁, a₂⁆ = ⁅z * b₁, a₂⁆ * (y * a₁) :=
    mul_comm_of_mem_Vt hθ hC hr hVt hc₂ (mul_mem hy hma₁)
  have e : y * z * (a₁ * b₁) * (a₂ * b₂) =
      ⁅z, a₁⁆ * ⁅z * b₁, a₂⁆ * (y * a₁ * a₂) * (z * b₁ * b₂) :=
    calc y * z * (a₁ * b₁) * (a₂ * b₂) = y * (z * a₁) * b₁ * a₂ * b₂ := by group
      _ = y * (⁅z, a₁⁆ * (a₁ * z)) * b₁ * a₂ * b₂ := by rw [f1]
      _ = (y * ⁅z, a₁⁆) * a₁ * z * b₁ * a₂ * b₂ := by group
      _ = (⁅z, a₁⁆ * y) * a₁ * z * b₁ * a₂ * b₂ := by rw [k1]
      _ = ⁅z, a₁⁆ * (y * a₁) * (z * b₁ * a₂) * b₂ := by group
      _ = ⁅z, a₁⁆ * (y * a₁) * (⁅z * b₁, a₂⁆ * (a₂ * (z * b₁))) * b₂ := by rw [f2]
      _ = ⁅z, a₁⁆ * (y * a₁ * ⁅z * b₁, a₂⁆) * a₂ * z * b₁ * b₂ := by group
      _ = ⁅z, a₁⁆ * (⁅z * b₁, a₂⁆ * (y * a₁)) * a₂ * z * b₁ * b₂ := by rw [k2]
      _ = ⁅z, a₁⁆ * ⁅z * b₁, a₂⁆ * (y * a₁ * a₂) * (z * b₁ * b₂) := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hc₁ hc₂) hy') hz'

include hθ hC hr hVt in
theorem complement_inv_mem {A : GL (Fin r) K} {g : E} (hg : θ g = hypProj h r 1 (lHom h r A))
    {y : E} (hy : y ∈ preN θ) (hy' : y * (g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹) ∈ Vt) :
    y⁻¹ * (g * y⁻¹ * g⁻¹) * (g * (g * y⁻¹ * g⁻¹) * g⁻¹) ∈ Vt := by
  set a₁ := g * y * g⁻¹ with ha₁
  set a₂ := g * a₁ * g⁻¹ with ha₂
  have hma₁ : a₁ ∈ preN θ := conj_mem_preN_of_lift hg hy
  have hma₂ : a₂ ∈ preN θ := conj_mem_preN_of_lift hg hma₁
  have e1 : y⁻¹ * (g * y⁻¹ * g⁻¹) * (g * (g * y⁻¹ * g⁻¹) * g⁻¹) = (a₂ * a₁ * y)⁻¹ := by
    rw [ha₂, ha₁]
    group
  rw [e1]
  refine inv_mem ?_
  have hd₁ := commutatorElement_mem_herm_complement hθ hC hVt hr hma₂ hma₁
  have hd₂ := commutatorElement_mem_herm_complement hθ hC hVt hr hma₂ hy
  have hd₃ := commutatorElement_mem_herm_complement hθ hC hVt hr hma₁ hy
  have f1 : a₂ * a₁ = ⁅a₂, a₁⁆ * (a₁ * a₂) := by rw [commutatorElement_def]; group
  have f2 : a₂ * y = ⁅a₂, y⁆ * (y * a₂) := by rw [commutatorElement_def]; group
  have f3 : a₁ * y = ⁅a₁, y⁆ * (y * a₁) := by rw [commutatorElement_def]; group
  have k : a₁ * ⁅a₂, y⁆ = ⁅a₂, y⁆ * a₁ := mul_comm_of_mem_Vt hθ hC hr hVt hd₂ hma₁
  have e : a₂ * a₁ * y = ⁅a₂, a₁⁆ * ⁅a₂, y⁆ * ⁅a₁, y⁆ * (y * a₁ * a₂) :=
    calc a₂ * a₁ * y = ⁅a₂, a₁⁆ * (a₁ * a₂) * y := by rw [f1]
      _ = ⁅a₂, a₁⁆ * a₁ * (a₂ * y) := by group
      _ = ⁅a₂, a₁⁆ * a₁ * (⁅a₂, y⁆ * (y * a₂)) := by rw [f2]
      _ = ⁅a₂, a₁⁆ * (a₁ * ⁅a₂, y⁆) * y * a₂ := by group
      _ = ⁅a₂, a₁⁆ * (⁅a₂, y⁆ * a₁) * y * a₂ := by rw [k]
      _ = ⁅a₂, a₁⁆ * ⁅a₂, y⁆ * (a₁ * y) * a₂ := by group
      _ = ⁅a₂, a₁⁆ * ⁅a₂, y⁆ * (⁅a₁, y⁆ * (y * a₁)) * a₂ := by rw [f3]
      _ = ⁅a₂, a₁⁆ * ⁅a₂, y⁆ * ⁅a₁, y⁆ * (y * a₁ * a₂) := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hd₁ hd₂) hd₃) hy'

include hθ hC hr hVt in
variable (θ Vt) in
@[expose] def complement {A : GL (Fin r) K} {g : E} (hg : θ g = hypProj h r 1 (lHom h r A)) :
    Subgroup E where
  carrier := {y | y ∈ preN θ ∧ y * (g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹) ∈ Vt}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
    exact ⟨mul_mem hy hz, complement_mul_mem hθ hC hr hVt hg hy hz hy' hz'⟩
  inv_mem' := by
    rintro y ⟨hy, hy'⟩
    exact ⟨inv_mem hy, complement_inv_mem hθ hC hr hVt hg hy hy'⟩

section Properties

variable {A : GL (Fin r) K} {g : E} (hg : θ g = hypProj h r 1 (lHom h r A))

theorem mem_complement {y : E} :
    y ∈ complement θ hθ hC hr Vt hVt hg ↔
      y ∈ preN θ ∧ y * (g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹) ∈ Vt :=
  Iff.rfl

theorem le_complement : Vt ≤ complement θ hθ hC hr Vt hVt hg := fun v hv =>
  ⟨preV_le_preN (hVt.le hv), mul_mem (mul_mem hv (hVt.conj A g hg v hv))
    (hVt.conj A g hg _ (hVt.conj A g hg v hv))⟩

theorem eq_one_of_mem_complement (h2 : ∀ c, θ c = 1 → c ^ 2 = 1) {y : E}
    (hy : y ∈ complement θ hθ hC hr Vt hVt hg) (hy1 : θ y = 1) : y = 1 := by
  have hyc := hC hy1
  have e : y * (g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹) = y := by
    rw [conj_central hyc, conj_central hyc, ← pow_two, h2 y hy1, one_mul]
  exact hVt.inj y (e ▸ hy.2) hy1

omit [CharP K 2] in
theorem isV_of_map_eq_one {c : E} (hc : θ c = 1) : c ∈ preV θ :=
  (isV_zero_iff.mpr hc).mem

theorem exists_mem_complement (h2 : ∀ c, θ c = 1 → c ^ 2 = 1)
    (hfpf : ∀ y ∈ preN θ, y * (g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹) ∈ preV θ) {m : E}
    (hm : m ∈ preN θ) : ∃ y ∈ complement θ hθ hC hr Vt hVt hg, θ y = θ m := by
  obtain ⟨c, v, hc, hv, he⟩ := hVt.dec _ (hfpf m hm)
  have hcc := hC hc
  refine ⟨m * c, ⟨mul_mem hm (preV_le_preN (isV_of_map_eq_one hc)), ?_⟩,
    by rw [map_mul, hc, mul_one]⟩
  have e1 : g * (m * c) * g⁻¹ = g * m * g⁻¹ * c := by
    rw [show g * (m * c) * g⁻¹ = g * m * g⁻¹ * (g * c * g⁻¹) by group, conj_central hcc]
  have e2 : g * (g * m * g⁻¹ * c) * g⁻¹ = g * (g * m * g⁻¹) * g⁻¹ * c := by
    rw [show g * (g * m * g⁻¹ * c) * g⁻¹ = g * (g * m * g⁻¹) * g⁻¹ * (g * c * g⁻¹) by group,
      conj_central hcc]
  rw [e1, e2, mul_central_three hcc, he]
  have hc2 := h2 c hc
  have e3 : c * v * c ^ 3 = v := by
    rw [show c ^ 3 = c * c ^ 2 by group, hc2, mul_one, mul_assoc,
      Subgroup.mem_center_iff.mp hcc v, ← mul_assoc, ← pow_two, hc2, one_mul]
  rw [e3]
  exact hv

omit [CharP K 2] in
include hC hg in
theorem conj_conj_eq_of_commute {B : GL (Fin r) K} {e : E}
    (he : θ e = hypProj h r 1 (lHom h r B)) (hAB : A * B = B * A) (x : E) :
    g * (e * x * e⁻¹) * g⁻¹ = e * (g * x * g⁻¹) * e⁻¹ := by
  have hge : θ (g * e) = θ (e * g) := by
    rw [map_mul, map_mul, hg, he, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hAB]
  have hc : (e * g)⁻¹ * (g * e) ∈ Subgroup.center E := hC (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hge, inv_mul_cancel])
  calc g * (e * x * e⁻¹) * g⁻¹ = (e * g) * (((e * g)⁻¹ * (g * e)) * x *
        ((e * g)⁻¹ * (g * e))⁻¹) * (e * g)⁻¹ := by group
    _ = e * (g * x * g⁻¹) * e⁻¹ := by rw [conj_eq_of_mem_center hc]; group

theorem conj_mem_complement {B : GL (Fin r) K} {e : E}
    (he : θ e = hypProj h r 1 (lHom h r B)) (hAB : A * B = B * A) {y : E}
    (hy : y ∈ complement θ hθ hC hr Vt hVt hg) : e * y * e⁻¹ ∈ complement θ hθ hC hr Vt hVt hg := by
  refine ⟨conj_mem_preN_of_lift he hy.1, ?_⟩
  rw [conj_conj_eq_of_commute hC hg he hAB, conj_conj_eq_of_commute hC hg he hAB,
    show e * y * e⁻¹ * (e * (g * y * g⁻¹) * e⁻¹) * (e * (g * (g * y * g⁻¹) * g⁻¹) * e⁻¹) =
      e * (y * (g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹)) * e⁻¹ by group]
  exact hVt.conj B e he _ hy.2

theorem complement_le (h2 : ∀ c, θ c = 1 → c ^ 2 = 1) {B : GL (Fin r) K} {e : E}
    (he : θ e = hypProj h r 1 (lHom h r B)) (hAB : A * B = B * A)
    (hfpf : ∀ y ∈ preN θ, y * (e * y * e⁻¹) * (e * (e * y * e⁻¹) * e⁻¹) ∈ preV θ) :
    complement θ hθ hC hr Vt hVt hg ≤ complement θ hθ hC hr Vt hVt he := by
  intro y hy
  have h1 := conj_mem_complement hθ hC hr hVt hg he hAB hy
  have h2' := conj_mem_complement hθ hC hr hVt hg he hAB h1
  have hz := mul_mem (mul_mem hy h1) h2'
  obtain ⟨c, v, hc, hv, hzcv⟩ := hVt.dec _ (hfpf y hy.1)
  have hcM : c ∈ complement θ hθ hC hr Vt hVt hg := by
    have := mul_mem hz (inv_mem (le_complement hθ hC hr hVt hg hv))
    rwa [hzcv, mul_inv_cancel_right] at this
  have hc1 := eq_one_of_mem_complement hθ hC hr hVt hg h2 hcM hc
  refine ⟨hy.1, ?_⟩
  rw [hzcv, hc1, one_mul]
  exact hv

end Properties

omit [CharP K 2] in
theorem IsN.conj_torus_vec {x : Fin r → K} {m g : E} (hm : IsN θ x m) (d : Fin r → Kˣ)
    (hg : θ g = hypProj h r 1 (lHom h r (hTorusGL d))) :
    IsN θ (fun k => (∏ i, (d i : K))⁻¹ * d k * x k) (g * m * g⁻¹) := by
  refine (hm.conj _ hg).congr ?_
  funext k
  rw [dval_eq_det, hTorusGL_det, hTorusGL_coe, Pi.smul_apply, mulVec_diagonal, smul_eq_mul,
    mul_assoc]

theorem mem_preV_of_torus {d : Fin r → Kˣ} (hd : ∀ k, (∏ i, (d i : K))⁻¹ * d k ≠ 1) {g : E}
    (hg : θ g = hypProj h r 1 (lHom h r (hTorusGL d))) {y : E} (hy : y ∈ preN θ) :
    y * (g * y * g⁻¹) * (g * (g * y * g⁻¹) * g⁻¹) ∈ preV θ := by
  have hK := card_eq_four h
  obtain ⟨x, hx⟩ := mem_preN.mp hy
  have h1 := hx.conj_torus_vec d hg
  have h2 := h1.conj_torus_vec d hg
  refine isN_zero_iff.mp (((hx.mul h1).mul h2).congr ?_)
  funext k
  have hprod : (∏ i, (d i : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (d i).ne_zero
  have hζ0 : (∏ i, (d i : K))⁻¹ * d k ≠ 0 := mul_ne_zero (inv_ne_zero hprod) (d k).ne_zero
  have hζ2 := four_omega_sq hK hζ0 (hd k)
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [Pi.add_apply, Pi.zero_apply]
  linear_combination (x k) * hζ2 + (x k * (1 + (∏ i, (d i : K))⁻¹ * d k)) * h2'

include hθ hC hr in
theorem exists_radical_complement [Finite E] (h2 : ∀ c, θ c = 1 → c ^ 2 = 1) :
    ∃ M₀ : Subgroup E, M₀ ≤ preN θ ∧ (∀ y ∈ M₀, θ y = 1 → y = 1) ∧
      (∀ {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hx : IsRad h x C),
        ∃ y ∈ M₀, θ y = hypProj h r 1 (nElt hx)) ∧
      ∀ (A : SpecialLinearGroup (Fin r) K) (u : E),
        θ u = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) →
          ∀ y, y ∈ M₀ ↔ u * y * u⁻¹ ∈ M₀ := by
  have hK := card_eq_four h
  obtain ⟨Vt, hVt⟩ := exists_herm_complement hθ hC h2 hr
  obtain ⟨w, hw1, hw2, -⟩ := exists_unit_ne_one hK
  set dd : Fin r → Fin r → Fin r → Kˣ := fun a b => Pi.mulSingle a w * Pi.mulSingle b w with hdd
  have hweight : ∀ a b : Fin r, a ≠ b → ∀ k, (∏ i, ((dd a b i : Kˣ) : K))⁻¹ * (dd a b k) ≠ 1 := by
    intro a b hab k
    rw [hdd, prod_mulSingle_mul, mulSingle_mul_apply]
    have hw0 : (w : K) ≠ 0 := w.ne_zero
    by_cases hka : k = a
    · rw [ite_eq_left hka, ite_eq_right (hka ▸ hab), mul_one, _root_.mul_inv_rev, mul_assoc,
        inv_mul_cancel₀ hw0, mul_one]
      exact inv_ne_one.mpr hw1
    · rw [ite_eq_right hka]
      by_cases hkb : k = b
      · rw [ite_eq_left hkb, one_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hw0, mul_one]
        exact inv_ne_one.mpr hw1
      · rw [ite_eq_right hkb, mul_one, mul_one, ← pow_two]
        exact inv_ne_one.mpr hw2
  have hval : ∀ a b : Fin r, a ≠ b → (dd a b a : K) = w ∧ (dd a b b : K) = w := fun a b hab => by
    rw [hdd, mulSingle_mul_apply, mulSingle_mul_apply, ite_eq_left rfl, ite_eq_right hab,
      ite_eq_right (Ne.symm hab), ite_eq_left rfl, mul_one, one_mul]
    exact ⟨rfl, rfl⟩
  choose gg hgg using fun a b => hθ (hypProj h r 1 (lHom h r (hTorusGL (dd a b))))
  have hfpf : ∀ a b : Fin r, a ≠ b → ∀ y ∈ preN θ,
      y * (gg a b * y * (gg a b)⁻¹) * (gg a b * (gg a b * y * (gg a b)⁻¹) * (gg a b)⁻¹) ∈
        preV θ := fun a b hab y hy => mem_preV_of_torus (hweight a b hab) (hgg a b) hy
  set i₀ : Fin r := ⟨0, by omega⟩
  set i₁ : Fin r := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by simp [i₀, i₁, Fin.ext_iff] at h
  set M₀ := complement θ hθ hC hr Vt hVt (hgg i₀ i₁) with hM₀
  have hM₀eq : ∀ a b : Fin r, a ≠ b → M₀ = complement θ hθ hC hr Vt hVt (hgg a b) :=
    fun a b hab => le_antisymm
      (complement_le hθ hC hr hVt (hgg i₀ i₁) h2 (hgg a b) (hTorusGL_comm _ _) (hfpf a b hab))
      (complement_le hθ hC hr hVt (hgg a b) h2 (hgg i₀ i₁) (hTorusGL_comm _ _) (hfpf i₀ i₁ h01))
  refine ⟨M₀, fun y hy => hy.1, fun y hy hy1 => eq_one_of_mem_complement hθ hC hr hVt _ h2 hy hy1,
    fun {x C} hx => ?_, fun A => ?_⟩
  · obtain ⟨m, hm⟩ := hθ (hypProj h r 1 (nElt hx))
    obtain ⟨y, hy, hym⟩ := exists_mem_complement hθ hC hr hVt (hgg i₀ i₁) h2 (hfpf i₀ i₁ h01)
      (show m ∈ preN θ from ⟨_, nElt_mem_radN hx, hm.symm⟩)
    exact ⟨y, hy, hym.trans hm⟩
  have hA : A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet r K) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top A
  induction hA using Subgroup.closure_induction with
  | mem A hA =>
    obtain ⟨a, b, hab, c, rfl⟩ := hA
    have htoGL : SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hab c) =
        hElemGL hab c := Units.ext rfl
    have hcomm : hTorusGL (dd a b) * hElemGL hab c = hElemGL hab c * hTorusGL (dd a b) := by
      rw [hTorusGL_mul_hElemGL, (hval a b hab).1, (hval a b hab).2, mul_comm (w : K) c,
        mul_assoc, mul_inv_cancel₀ w.ne_zero, mul_one]
    intro u hu y
    rw [htoGL] at hu
    have hu' : θ u⁻¹ = hypProj h r 1 (lHom h r (hElemGL hab c)) := by
      rw [map_inv, hu, ← map_inv, ← map_inv, hElemGL_inv]
    rw [hM₀eq a b hab]
    constructor
    · exact fun hy => conj_mem_complement hθ hC hr hVt (hgg a b) hu hcomm hy
    · intro hy
      have := conj_mem_complement hθ hC hr hVt (hgg a b) hu' hcomm hy
      rwa [show u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y by group] at this
  | one =>
    intro u hu y
    rw [map_one, map_one, map_one] at hu
    rw [conj_eq_of_mem_center (hC hu)]
  | mul A B _ _ ihA ihB =>
    intro u hu y
    obtain ⟨uA, huA⟩ := hθ (hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)))
    have huB : θ (uA⁻¹ * u) = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL B)) := by
      rw [map_mul, map_inv, huA, hu, map_mul, map_mul, map_mul, inv_mul_cancel_left]
    rw [ihB (uA⁻¹ * u) huB y, ihA uA huA,
      show uA * (uA⁻¹ * u * y * (uA⁻¹ * u)⁻¹) * uA⁻¹ = u * y * u⁻¹ by group]
  | inv A _ ihA =>
    intro u hu y
    have hu' : θ u⁻¹ = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) := by
      rw [map_inv, hu, map_inv, map_inv, map_inv, inv_inv]
    rw [ihA u⁻¹ hu' (u * y * u⁻¹), show u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y by group]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover
