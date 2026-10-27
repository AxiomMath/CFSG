module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoMatrices

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

variable {F : Type} [Field F] {h : UnitaryFieldData 2 1 F} {E : Type*} [Group E]
  {θ : E →* hypPSU h 3 0}

section Lifts

variable (θ) in
@[expose] def IsLift (Y : Matrix (HypIndex 3 0) (HypIndex 3 0) F) (x : E) : Prop :=
  ∃ g : hypSU h 3 0, ((g : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) = Y ∧
    θ x = hypProj h 3 0 g

theorem IsLift.map_eq {Y : Matrix (HypIndex 3 0) (HypIndex 3 0) F} {x : E} (hx : IsLift θ Y x)
    {g : hypSU h 3 0}
    (hg : ((g : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) = Y) :
    θ x = hypProj h 3 0 g := by
  obtain ⟨g', hg', hx'⟩ := hx
  rw [hx']
  congr 1
  exact Subtype.ext (Units.ext (hg'.trans hg.symm))

theorem IsLift.map_eq_map {Y : Matrix (HypIndex 3 0) (HypIndex 3 0) F} {x x' : E}
    (hx : IsLift θ Y x) (hx' : IsLift θ Y x') : θ x = θ x' := by
  obtain ⟨g, hg, hgx⟩ := hx
  rw [hgx, hx'.map_eq hg]

theorem IsLift.mul {Y Y' : Matrix (HypIndex 3 0) (HypIndex 3 0) F} {x x' : E}
    (hx : IsLift θ Y x) (hx' : IsLift θ Y' x') : IsLift θ (Y * Y') (x * x') := by
  obtain ⟨g, rfl, hg⟩ := hx
  obtain ⟨g', rfl, hg'⟩ := hx'
  exact ⟨g * g', rfl, by rw [map_mul, map_mul, hg, hg']⟩

theorem IsLift.inv {Y Y' : Matrix (HypIndex 3 0) (HypIndex 3 0) F} {x : E} (hx : IsLift θ Y x)
    (hY : Y * Y' = 1) : IsLift θ Y' x⁻¹ := by
  obtain ⟨g, rfl, hg⟩ := hx
  refine ⟨g⁻¹, ?_, by rw [map_inv, map_inv, hg]⟩
  rw [Subgroup.coe_inv]
  exact Units.inv_eq_of_mul_eq_one_right hY

theorem isLift_one_iff {x : E} : IsLift θ 1 x ↔ θ x = 1 := by
  constructor
  · intro hx
    rw [hx.map_eq (g := 1) rfl, map_one]
  · intro hx
    exact ⟨1, rfl, by rw [hx, map_one]⟩

theorem IsLift.mul_ker {Y : Matrix (HypIndex 3 0) (HypIndex 3 0) F} {x c : E}
    (hx : IsLift θ Y x) (hc : θ c = 1) : IsLift θ Y (x * c) := by
  simpa using hx.mul (isLift_one_iff.mpr hc)

theorem IsLift.exists_ker {Y : Matrix (HypIndex 3 0) (HypIndex 3 0) F} {x x' : E}
    (hx : IsLift θ Y x) (hx' : IsLift θ Y x') : ∃ c, θ c = 1 ∧ x' = x * c :=
  ⟨x⁻¹ * x', by rw [map_mul, map_inv, hx.map_eq_map hx', inv_mul_cancel],
    (mul_inv_cancel_left x x').symm⟩

theorem IsLift.conj {G Y Y' : Matrix (HypIndex 3 0) (HypIndex 3 0) F} {g x : E}
    (hg : IsLift θ G g) (hx : IsLift θ Y x) (hGY : G * Y = Y' * G) :
    IsLift θ Y' (g * x * g⁻¹) := by
  obtain ⟨s, rfl, hs⟩ := hg
  obtain ⟨t, rfl, ht⟩ := hx
  refine ⟨s * t * s⁻¹, ?_, by rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hs, ht]⟩
  change ((s : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) *
    ((t : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) *
    (((s : GL (HypIndex 3 0) F)⁻¹ : GL (HypIndex 3 0) F) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) F) = Y'
  rw [hGY, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem exists_isLift (hθ : Function.Surjective θ) (g : hypSU h 3 0) :
    ∃ x, IsLift θ ((g : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) x := by
  obtain ⟨x, hx⟩ := hθ (hypProj h 3 0 g)
  exact ⟨x, g, rfl, hx⟩

theorem exists_isLift_lMat (hθ : Function.Surjective θ) (A : SpecialLinearGroup (Fin 3) F) :
    ∃ x, IsLift θ (lMat h A) x :=
  exists_isLift hθ (lHom h A)

theorem isLift_lMat_iff {A : SpecialLinearGroup (Fin 3) F} {x : E} :
    IsLift θ (lMat h A) x ↔ θ x = hypProj h 3 0 (lHom h A) :=
  ⟨fun hx => hx.map_eq (coe_lHom h A), fun hx => ⟨lHom h A, coe_lHom h A, hx⟩⟩

variable [CharP F 2]

theorem exists_isLift_nMat (hθ : Function.Surjective θ) {B : Matrix (Fin 3) (Fin 3) F}
    (hB : hconj B = B) : ∃ x, IsLift θ (nMat B) x :=
  exists_isLift hθ (nElt h hB)

theorem IsLift.hconj_eq {B : Matrix (Fin 3) (Fin 3) F} {x : E} (hx : IsLift θ (nMat B) x) :
    hconj B = B := by
  obtain ⟨g, hg, -⟩ := hx
  have hgram := (mem_hypSU.mp g.2).1
  rw [hg, nMat] at hgram
  obtain ⟨-, -, -, h4⟩ := (blk3_gram_iff h _ _ _ _ _ _).mp hgram
  rw [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.map_one _ (map_zero _) (map_one _),
    transpose_one, Matrix.one_mul, bar_transpose h] at h4
  rw [eq_neg_of_add_eq_zero_left h4]
  ext i j
  exact CharTwo.neg_eq _

omit [CharP F 2] in
theorem IsLift.conj_nMat {A : SpecialLinearGroup (Fin 3) F} {g x : E}
    (hg : IsLift θ (lMat h A) g) {B : Matrix (Fin 3) (Fin 3) F} (hx : IsLift θ (nMat B) x) :
    IsLift θ (nMat ((A : Matrix (Fin 3) (Fin 3) F) * B * hconj A)) (g * x * g⁻¹) :=
  hg.conj hx (lMat_mul_nMat h (by rw [A.2]; exact isUnit_one) B)

theorem IsLift.conj_hermQ {A : SpecialLinearGroup (Fin 3) F} {g x : E}
    (hg : IsLift θ (lMat h A) g) {u : Fin 3 → F} (hx : IsLift θ (nMat (hermQ u)) x) :
    IsLift θ (nMat (hermQ ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ u))) (g * x * g⁻¹) := by
  have := hg.conj_nMat hx
  rwa [mul_hermQ_hconj] at this

omit [CharP F 2] in
theorem map_commutator_nMat {B B' : Matrix (Fin 3) (Fin 3) F} {x y : E}
    (hx : IsLift θ (nMat B) x) (hy : IsLift θ (nMat B') y) : θ ⁅x, y⁆ = 1 := by
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨g', hg', hgy⟩ := hy
  have hcomm : g * g' = g' * g := Subtype.ext (Units.ext (by
    change ((g : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) *
      ((g' : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) =
      ((g' : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) *
      ((g : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F)
    rw [hg, hg', nMat_mul, nMat_mul, add_comm]))
  rw [map_commutatorElement, hgx, hgy, ← map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.mpr hcomm, map_one]

theorem map_sq_nMat {B : Matrix (Fin 3) (Fin 3) F} {x : E} (hx : IsLift θ (nMat B) x) :
    θ (x ^ 2) = 1 := by
  have := hx.mul hx
  rw [nMat_mul, show B + B = 0 from by ext i j; exact CharTwo.add_self_eq_zero _, nMat_zero]
    at this
  rw [sq]
  exact isLift_one_iff.mp this

end Lifts

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_of_mem_center {a b c : G}
    (hbc : ⁅b, c⁆ ∈ Subgroup.center G) : ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq, Subgroup.mem_center_iff.mp hbc a, mul_inv_cancel_right,
    ← Subgroup.mem_center_iff.mp hbc]

theorem commutatorElement_sq_left {a b : G} (hab : a * ⁅a, b⁆ = ⁅a, b⁆ * a) :
    ⁅a ^ 2, b⁆ = ⁅a, b⁆ ^ 2 := by
  simp only [commutatorElement_def, sq] at hab ⊢
  calc a * a * b * (a * a)⁻¹ * b⁻¹ = a * (a * b * a⁻¹ * b⁻¹) * (b * a⁻¹ * b⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * a * (b * a⁻¹ * b⁻¹) := by rw [hab]
    _ = (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) := by group

theorem commutatorElement_conj (g x y : G) : ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * ⁅x, y⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

end Commutators

theorem cross_ne_zero_of_two {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    crossProduct ![0, a, b] (Pi.single 0 1 : Fin 3 → F) ≠ 0 := by
  intro h0
  have h1 := congrFun h0 1
  have h2 := congrFun h0 2
  simp [cross_apply] at h1 h2
  rcases hab with ha | hb
  · exact ha h2
  · exact hb h1

section Pairing

variable [CharP F 2] (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
include hC

omit [CharP F 2] in
theorem commute_of_isLift_same {Y : Matrix (HypIndex 3 0) (HypIndex 3 0) F} {x x' : E}
    (hx : IsLift θ Y x) (hx' : IsLift θ Y x') : Commute x x' := by
  obtain ⟨c, hc, rfl⟩ := hx.exists_ker hx'
  exact (Commute.refl x).mul_right (Subgroup.mem_center_iff.mp (hC hc) x)

omit [CharP F 2] in
theorem commute_of_isLift_of_commute {Y Y' : Matrix (HypIndex 3 0) (HypIndex 3 0) F}
    {x x' y y' : E} (hx : IsLift θ Y x) (hx' : IsLift θ Y x') (hy : IsLift θ Y' y)
    (hy' : IsLift θ Y' y') (hxy : Commute x y) : Commute x' y' := by
  obtain ⟨c, hc, rfl⟩ := hx.exists_ker hx'
  obtain ⟨d, hd, rfl⟩ := hy.exists_ker hy'
  have hc' : ∀ g, g * c = c * g := Subgroup.mem_center_iff.mp (hC hc)
  have hd' : ∀ g, g * d = d * g := Subgroup.mem_center_iff.mp (hC hd)
  exact (hxy.mul_right (hd' x)).mul_left (show Commute c (y * d) from (hc' (y * d)).symm)

omit [CharP F 2] in
theorem commutator_eq_of_isLift {Y Y' : Matrix (HypIndex 3 0) (HypIndex 3 0) F}
    {x x' y y' : E} (hx : IsLift θ Y x) (hx' : IsLift θ Y x') (hy : IsLift θ Y' y)
    (hy' : IsLift θ Y' y') : ⁅x, y⁆ = ⁅x', y'⁆ :=
  commutatorElement_eq_of_map_eq θ hC (hx.map_eq_map hx') (hy.map_eq_map hy')

theorem commutator_sq_nMat {B B' : Matrix (Fin 3) (Fin 3) F} {x y : E}
    (hx : IsLift θ (nMat B) x) (hy : IsLift θ (nMat B') y) : ⁅x, y⁆ ^ 2 = 1 := by
  have hc : ⁅x, y⁆ ∈ Subgroup.center E := hC (map_commutator_nMat hx hy)
  rw [← commutatorElement_sq_left (Subgroup.mem_center_iff.mp hc x),
    commutatorElement_eq_one_of_mem_center_left (hC (map_sq_nMat hx))]

include hθ in
theorem commutator_eq_of_cross_ne_zero {x₀ y₀ : E}
    (hx₀ : IsLift θ (nMat (hermQ (Pi.single 0 1 : Fin 3 → F))) x₀)
    (hy₀ : IsLift θ (nMat (hermQ (Pi.single 1 1 : Fin 3 → F))) y₀) {u v : Fin 3 → F}
    (huv : crossProduct u v ≠ 0) {x y : E} (hx : IsLift θ (nMat (hermQ u)) x)
    (hy : IsLift θ (nMat (hermQ v)) y) : ⁅x, y⁆ = ⁅x₀, y₀⁆ := by
  obtain ⟨A, hAu, hAv⟩ := exists_SL_mulVec_pair huv
  obtain ⟨g, hg⟩ := exists_isLift_lMat hθ A
  have h1 := hg.conj_hermQ hx₀
  have h2 := hg.conj_hermQ hy₀
  rw [hAu] at h1
  rw [hAv] at h2
  rw [commutator_eq_of_isLift hC hx h1 hy h2, commutatorElement_conj,
    conj_eq_self_of_mem_center g (hC (map_commutator_nMat hx₀ hy₀))]

include hθ in
theorem commutator_eq_one_basic {x₀ y₀ : E}
    (hx₀ : IsLift θ (nMat (hermQ (Pi.single 0 1 : Fin 3 → F))) x₀)
    (hy₀ : IsLift θ (nMat (hermQ (Pi.single 1 1 : Fin 3 → F))) y₀) : ⁅x₀, y₀⁆ = 1 := by
  obtain ⟨ω, hω⟩ := UnitaryFourCover.exists_omega h
  have hlift : ∀ a b : F, a ≠ 0 ∨ b ≠ 0 → ∃ x, IsLift θ (nMat (hermQ ![0, a, b])) x ∧
      ⁅x, x₀⁆ = ⁅x₀, y₀⁆ := by
    intro a b hab
    obtain ⟨x, hx⟩ := exists_isLift_nMat hθ (hconj_hermQ h ![0, a, b])
    exact ⟨x, hx, commutator_eq_of_cross_ne_zero hθ hC hx₀ hy₀ (cross_ne_zero_of_two hab) hx hx₀⟩
  obtain ⟨x₁, hx₁, e₁⟩ := hlift 1 0 (Or.inl one_ne_zero)
  obtain ⟨x₂, hx₂, e₂⟩ := hlift 0 1 (Or.inr one_ne_zero)
  obtain ⟨x₃, hx₃, e₃⟩ := hlift 1 1 (Or.inl one_ne_zero)
  obtain ⟨x₄, hx₄, e₄⟩ := hlift 1 ω (Or.inl one_ne_zero)
  obtain ⟨x₅, hx₅, e₅⟩ := hlift 1 (ω ^ 2) (Or.inl one_ne_zero)
  have hX : IsLift θ 1 (x₁ * x₂ * x₃ * x₄ * x₅) := by
    have := (((hx₁.mul hx₂).mul hx₃).mul hx₄).mul hx₅
    rwa [nMat_mul, nMat_mul, nMat_mul, nMat_mul, five_point hω, nMat_zero] at this
  have hcen : ∀ {B : Matrix (Fin 3) (Fin 3) F} {x : E}, IsLift θ (nMat B) x →
      ⁅x, x₀⁆ ∈ Subgroup.center E := fun hx => hC (map_commutator_nMat hx hx₀)
  have h5 : ⁅x₀, y₀⁆ ^ 5 = 1 := by
    have h1 := commutatorElement_eq_one_of_mem_center_left (hC (isLift_one_iff.mp hX)) x₀
    rw [commutatorElement_mul_left_of_mem_center (hcen hx₅),
      commutatorElement_mul_left_of_mem_center (hcen hx₄),
      commutatorElement_mul_left_of_mem_center (hcen hx₃),
      commutatorElement_mul_left_of_mem_center (hcen hx₂), e₁, e₂, e₃, e₄, e₅] at h1
    rw [show ∀ z : E, z ^ 5 = z * z * z * z * z from fun z => by
      simp only [pow_succ, pow_zero, one_mul]]
    exact h1
  have h2 := commutator_sq_nMat hC hx₀ hy₀
  generalize ⁅x₀, y₀⁆ = κ at h5 h2 ⊢
  calc κ = κ ^ 5 * (κ ^ 2)⁻¹ ^ 2 := by group
    _ = 1 := by rw [h5, h2, inv_one, one_pow, one_mul]

include hθ in
theorem commute_of_isLift_hermQ {u v : Fin 3 → F} {x y : E} (hx : IsLift θ (nMat (hermQ u)) x)
    (hy : IsLift θ (nMat (hermQ v)) y) : Commute x y := by
  have hzero : hermQ (0 : Fin 3 → F) = 0 := by
    ext i j
    simp [hermQ]
  by_cases huv : crossProduct u v = 0
  · rcases eq_zero_or_eq_smul_of_cross_eq_zero huv with rfl | ⟨c, rfl⟩
    · rw [hzero, nMat_zero] at hx
      exact (Subgroup.mem_center_iff.mp (hC (isLift_one_iff.mp hx)) y).symm
    · by_cases hc : c = 0
      · rw [hc, zero_smul, hzero, nMat_zero] at hy
        exact Subgroup.mem_center_iff.mp (hC (isLift_one_iff.mp hy)) x
      · rw [hermQ_smul_of_ne_zero h hc] at hy
        exact commute_of_isLift_same hC hx hy
  · obtain ⟨x₀, hx₀⟩ := exists_isLift_nMat hθ (hconj_hermQ h (Pi.single 0 1 : Fin 3 → F))
    obtain ⟨y₀, hy₀⟩ := exists_isLift_nMat hθ (hconj_hermQ h (Pi.single 1 1 : Fin 3 → F))
    have := commutator_eq_of_cross_ne_zero hθ hC hx₀ hy₀ huv hx hy
    rw [commutator_eq_one_basic hθ hC hx₀ hy₀] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this

omit hC in
theorem exists_isLift_of_hermQ (P : E → Prop) (h1 : P 1)
    (hmul : ∀ {B₁ B₂ : Matrix (Fin 3) (Fin 3) F} {x₁ x₂ : E}, IsLift θ (nMat B₁) x₁ →
      IsLift θ (nMat B₂) x₂ → P x₁ → P x₂ → P (x₁ * x₂))
    (hinv : ∀ {B : Matrix (Fin 3) (Fin 3) F} {x : E}, IsLift θ (nMat B) x → P x → P x⁻¹)
    (hq : ∀ u : Fin 3 → F, ∃ x, IsLift θ (nMat (hermQ u)) x ∧ P x)
    {B : Matrix (Fin 3) (Fin 3) F} (hB : hconj B = B) : ∃ x, IsLift θ (nMat B) x ∧ P x := by
  let S : AddSubgroup (Matrix (Fin 3) (Fin 3) F) :=
    { carrier := {B | ∃ x, IsLift θ (nMat B) x ∧ P x}
      add_mem' := by
        rintro B₁ B₂ ⟨x₁, hx₁, p₁⟩ ⟨x₂, hx₂, p₂⟩
        exact ⟨x₁ * x₂, by rw [← nMat_mul]; exact hx₁.mul hx₂, hmul hx₁ hx₂ p₁ p₂⟩
      zero_mem' := ⟨1, by rw [nMat_zero]; exact isLift_one_iff.mpr (map_one θ), h1⟩
      neg_mem' := by
        rintro B ⟨x, hx, px⟩
        exact ⟨x⁻¹, hx.inv (by rw [nMat_mul, add_neg_cancel, nMat_zero]), hinv hx px⟩ }
  have hle : AddSubgroup.closure (Set.range fun u : Fin 3 → F => hermQ u) ≤ S :=
    (AddSubgroup.closure_le S).mpr (by
      rintro _ ⟨u, rfl⟩
      exact hq u)
  exact hle (herm_mem_closure_hermQ hB)

include hθ in
theorem commute_of_isLift_nMat {B B' : Matrix (Fin 3) (Fin 3) F} {x y : E}
    (hx : IsLift θ (nMat B) x) (hy : IsLift θ (nMat B') y) : Commute x y := by
  have step : ∀ (v : Fin 3 → F) (y' : E), IsLift θ (nMat (hermQ v)) y' →
      ∀ {B₀ : Matrix (Fin 3) (Fin 3) F} {x' : E}, IsLift θ (nMat B₀) x' → Commute x' y' := by
    intro v y' hy' B₀ x' hx'
    obtain ⟨x'', hx'', hc⟩ := exists_isLift_of_hermQ (θ := θ) (fun z => Commute z y')
      (Commute.one_left y') (fun _ _ c₁ c₂ => c₁.mul_left c₂) (fun _ c => c.inv_left)
      (fun u => by
        obtain ⟨z, hz⟩ := exists_isLift_nMat hθ (hconj_hermQ h u)
        exact ⟨z, hz, commute_of_isLift_hermQ hθ hC hz hy'⟩) hx'.hconj_eq
    exact commute_of_isLift_of_commute hC hx'' hx' hy' hy' hc
  obtain ⟨y'', hy'', hc⟩ := exists_isLift_of_hermQ (θ := θ) (fun z => Commute x z)
    (Commute.one_right x) (fun _ _ c₁ c₂ => c₁.mul_right c₂) (fun _ c => c.inv_right)
    (fun v => by
      obtain ⟨z, hz⟩ := exists_isLift_nMat hθ (hconj_hermQ h v)
      exact ⟨z, hz, step v z hz hx⟩) hy.hconj_eq
  exact commute_of_isLift_of_commute hC hx hx hy'' hy hc

include hθ in
theorem exists_sq_eq_basic {x₀ : E} (hx₀ : IsLift θ (nMat (hermQ (Pi.single 0 1 : Fin 3 → F))) x₀) :
    ∃ c, θ c = 1 ∧ x₀ ^ 2 = c ^ 2 := by
  obtain ⟨ω, hω⟩ := UnitaryFourCover.exists_omega h
  have hcen : x₀ ^ 2 ∈ Subgroup.center E := hC (map_sq_nMat hx₀)
  have hlift : ∀ p : Fin 3 → F, p ≠ 0 → ∃ y, IsLift θ (nMat (hermQ p)) y ∧ y ^ 2 = x₀ ^ 2 := by
    intro p hp
    obtain ⟨A, hA⟩ := exists_SL_mulVec hp
    obtain ⟨g, hg⟩ := exists_isLift_lMat hθ A
    have := hg.conj_hermQ hx₀
    rw [hA] at this
    exact ⟨g * x₀ * g⁻¹, this, by rw [conj_pow, conj_eq_self_of_mem_center g hcen]⟩
  have hne : ∀ a b : F, a ≠ 0 ∨ b ≠ 0 → (![0, a, b] : Fin 3 → F) ≠ 0 := by
    intro a b hab h0
    have h1 := congrFun h0 1
    have h2 := congrFun h0 2
    simp at h1 h2
    rcases hab with ha | hb
    · exact ha h1
    · exact hb h2
  obtain ⟨y₁, hy₁, e₁⟩ := hlift _ (hne 1 0 (Or.inl one_ne_zero))
  obtain ⟨y₂, hy₂, e₂⟩ := hlift _ (hne 0 1 (Or.inr one_ne_zero))
  obtain ⟨y₃, hy₃, e₃⟩ := hlift _ (hne 1 1 (Or.inl one_ne_zero))
  obtain ⟨y₄, hy₄, e₄⟩ := hlift _ (hne 1 ω (Or.inl one_ne_zero))
  obtain ⟨y₅, hy₅, e₅⟩ := hlift _ (hne 1 (ω ^ 2) (Or.inl one_ne_zero))
  have hY : IsLift θ 1 (y₁ * y₂ * y₃ * y₄ * y₅) := by
    have := (((hy₁.mul hy₂).mul hy₃).mul hy₄).mul hy₅
    rwa [nMat_mul, nMat_mul, nMat_mul, nMat_mul, five_point hω, nMat_zero] at this
  have cm : ∀ {B B' : Matrix (Fin 3) (Fin 3) F} {x y : E}, IsLift θ (nMat B) x →
      IsLift θ (nMat B') y → Commute x y := fun hx hy => commute_of_isLift_nMat hθ hC hx hy
  have hY2 : (y₁ * y₂ * y₃ * y₄ * y₅) ^ 2 = x₀ ^ 10 := by
    rw [(((((cm hy₁ hy₅).mul_left (cm hy₂ hy₅)).mul_left (cm hy₃ hy₅)).mul_left
        (cm hy₄ hy₅))).mul_pow, ((((cm hy₁ hy₄).mul_left (cm hy₂ hy₄)).mul_left
        (cm hy₃ hy₄))).mul_pow, (((cm hy₁ hy₃).mul_left (cm hy₂ hy₃))).mul_pow,
      (cm hy₁ hy₂).mul_pow, e₁, e₂, e₃, e₄, e₅]
    group
  have hw : (x₀ ^ 2)⁻¹ ^ 2 ∈ Subgroup.center E :=
    Subgroup.pow_mem _ (Subgroup.inv_mem _ hcen) 2
  refine ⟨y₁ * y₂ * y₃ * y₄ * y₅ * (x₀ ^ 2)⁻¹ ^ 2, ?_, ?_⟩
  · rw [map_mul, isLift_one_iff.mp hY, one_mul, map_pow, map_inv, map_sq_nMat hx₀, inv_one,
      one_pow]
  · rw [(show Commute (y₁ * y₂ * y₃ * y₄ * y₅) ((x₀ ^ 2)⁻¹ ^ 2) from
      Subgroup.mem_center_iff.mp hw _).mul_pow, hY2]
    group

include hθ in
theorem exists_sq_eq_of_isLift_nMat {B : Matrix (Fin 3) (Fin 3) F} {x : E}
    (hx : IsLift θ (nMat B) x) : ∃ c, θ c = 1 ∧ x ^ 2 = c ^ 2 := by
  have hzero : hermQ (0 : Fin 3 → F) = 0 := by
    ext i j
    simp [hermQ]
  obtain ⟨x₀, hx₀⟩ := exists_isLift_nMat hθ (hconj_hermQ h (Pi.single 0 1 : Fin 3 → F))
  obtain ⟨c₀, hc₀, hx₀c⟩ := exists_sq_eq_basic hθ hC hx₀
  have hc₀' : Commute x₀ c₀ := Subgroup.mem_center_iff.mp (hC hc₀) x₀
  have hinvol : (x₀ * c₀⁻¹) ^ 2 = 1 := by
    rw [hc₀'.inv_right.mul_pow, hx₀c, inv_pow, mul_inv_cancel]
  have hx₀' : IsLift θ (nMat (hermQ (Pi.single 0 1 : Fin 3 → F))) (x₀ * c₀⁻¹) :=
    hx₀.mul_ker (by rw [map_inv, hc₀, inv_one])
  obtain ⟨x₁, hx₁, hx₁2⟩ := exists_isLift_of_hermQ (θ := θ) (fun z => z ^ 2 = 1) (one_pow 2)
    (fun hy₁ hy₂ p₁ p₂ => by
      rw [(commute_of_isLift_nMat hθ hC hy₁ hy₂).mul_pow, p₁, p₂, mul_one])
    (fun _ p => by rw [inv_pow, p, inv_one])
    (fun u => by
      by_cases hu : u = 0
      · refine ⟨1, ?_, one_pow 2⟩
        rw [hu, hzero, nMat_zero]
        exact isLift_one_iff.mpr (map_one θ)
      · obtain ⟨A, hA⟩ := exists_SL_mulVec hu
        obtain ⟨g, hg⟩ := exists_isLift_lMat hθ A
        have := hg.conj_hermQ hx₀'
        rw [hA] at this
        exact ⟨_, this, by rw [conj_pow, hinvol, mul_one, mul_inv_cancel]⟩)
    hx.hconj_eq
  obtain ⟨k, hk, rfl⟩ := hx₁.exists_ker hx
  refine ⟨k, hk, ?_⟩
  rw [(show Commute x₁ k from Subgroup.mem_center_iff.mp (hC hk) x₁).mul_pow, hx₁2, one_mul]

end Pairing

end CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo
