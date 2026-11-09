module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.KacMask

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice

@[expose] def kacTest {r : ℕ} (θ : Fin r → ℤ) (C : Finset (Option (Fin r))) (γ : Fin r → ℤ) :
    Prop :=
  (∀ j, some j ∉ C → γ j = 0) ∨
    (none ∈ C ∧ ((∀ j, some j ∉ C → γ j = -θ j) ∨ (∀ j, some j ∉ C → γ j = θ j)))

instance {r : ℕ} (θ : Fin r → ℤ) (C : Finset (Option (Fin r))) (γ : Fin r → ℤ) :
    Decidable (kacTest θ C γ) := by
  unfold kacTest
  infer_instance

@[expose] def kacCount (τ : Tag) (θ : Fin τ.rank → ℤ) (C : Finset (Option (Fin τ.rank))) : ℕ :=
  (τ.artifactRoots.filter fun l => decide (kacTest θ C (toVec τ.rank l))).length

open KacMask in
theorem kacTest_setOf {r : ℕ} (θ γ : Fin r → ℤ) (m : ℕ) :
    decide (kacTest θ (setOf r m) γ) = kacTestB r m (zm γ) (zm (γ + θ)) (zm (γ - θ)) := by
  have e1 : (∀ j, some j ∉ setOf r m → γ j = 0) ↔ (zm γ &&& m == zm γ) = true := by
    rw [← forall_zero_iff]; simp only [not_mem_setOf_some]
  have e2 : (∀ j, some j ∉ setOf r m → γ j = -θ j) ↔
      (zm (γ + θ) &&& m == zm (γ + θ)) = true := by
    rw [← forall_zero_iff]; simp only [not_mem_setOf_some, Pi.add_apply]
    exact forall_congr' fun j => imp_congr_right fun _ => by constructor <;> intro h <;> omega
  have e3 : (∀ j, some j ∉ setOf r m → γ j = θ j) ↔
      (zm (γ - θ) &&& m == zm (γ - θ)) = true := by
    rw [← forall_zero_iff]; simp only [not_mem_setOf_some, Pi.sub_apply]
    exact forall_congr' fun j => imp_congr_right fun _ => by constructor <;> intro h <;> omega
  rw [Bool.eq_iff_iff, decide_eq_true_iff, kacTest, e1, e2, e3, mem_setOf_none, kacTestB]
  simp only [Bool.or_eq_true, Bool.and_eq_true]

open KacMask in
theorem kacCount_setOf (τ : Tag) (θ : Fin τ.rank → ℤ) (m : ℕ) :
    kacCount τ θ (setOf τ.rank m) = ((τ.artifactRoots.map fun l =>
      (zm (toVec τ.rank l), zm (toVec τ.rank l + θ), zm (toVec τ.rank l - θ))).filter
        fun t => kacTestB τ.rank m t.1 t.2.1 t.2.2).length := by
  rw [kacCount, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro l _
  simp only [Function.comp_apply, kacTest_setOf]

@[expose] def kacMaskE8 : List (ℕ × ℕ × ℕ) :=
  [(255, 0, 255), (255, 128, 255), (255, 192, 255), (255, 224, 255), (255, 240, 255), (255, 248, 255), (255, 252, 255), (255, 250, 255),
    (255, 254, 255), (255, 254, 255), (255, 254, 255), (255, 254, 255), (255, 254, 255), (127, 254, 255), (255, 253, 255), (255, 255, 255),
    (255, 255, 255), (255, 255, 255), (255, 255, 255), (255, 255, 255), (127, 255, 255), (255, 255, 255), (255, 255, 255), (255, 255, 255),
    (255, 255, 255), (127, 255, 255), (255, 255, 255), (255, 255, 255), (255, 255, 255), (127, 255, 255), (255, 255, 255), (255, 255, 255),
    (127, 255, 255), (255, 255, 255), (127, 255, 255), (63, 255, 255), (255, 255, 255), (255, 255, 255), (255, 255, 255), (127, 255, 255),
    (255, 255, 255), (255, 255, 255), (127, 255, 255), (255, 255, 255), (127, 255, 255), (63, 255, 255), (255, 255, 255), (255, 255, 255),
    (127, 255, 255), (255, 255, 255), (127, 255, 255), (63, 255, 255), (255, 255, 255), (127, 255, 255), (63, 255, 255), (31, 255, 255),
    (255, 255, 255), (255, 255, 255), (127, 255, 255), (255, 255, 255), (127, 255, 255), (63, 255, 255), (255, 255, 255), (127, 255, 255),
    (63, 255, 255), (31, 255, 255), (255, 255, 255), (127, 255, 255), (63, 255, 255), (31, 255, 255), (15, 255, 255), (253, 255, 255),
    (125, 255, 255), (61, 255, 255), (29, 255, 255), (13, 255, 255), (5, 255, 255), (1, 255, 255), (254, 255, 255), (254, 255, 255),
    (126, 255, 255), (254, 255, 255), (126, 255, 255), (62, 255, 255), (254, 255, 255), (126, 255, 255), (62, 255, 255), (30, 255, 255),
    (254, 255, 255), (126, 255, 255), (62, 255, 255), (30, 255, 255), (14, 255, 255), (250, 255, 255), (122, 255, 255), (58, 255, 255),
    (26, 255, 255), (10, 255, 255), (2, 255, 255), (252, 255, 255), (124, 255, 255), (60, 255, 255), (28, 255, 255), (12, 255, 255),
    (4, 255, 255), (248, 255, 255), (120, 255, 255), (56, 255, 255), (24, 255, 255), (8, 255, 255), (240, 255, 255), (112, 255, 255),
    (48, 255, 255), (16, 255, 255), (224, 255, 255), (96, 255, 255), (32, 255, 255), (192, 255, 255), (64, 255, 255), (128, 255, 255),
    (128, 255, 255), (64, 255, 255), (192, 255, 255), (32, 255, 255), (96, 255, 255), (224, 255, 255), (16, 255, 255), (48, 255, 255),
    (112, 255, 255), (240, 255, 255), (8, 255, 255), (24, 255, 255), (56, 255, 255), (120, 255, 255), (248, 255, 255), (4, 255, 255),
    (12, 255, 255), (28, 255, 255), (60, 255, 255), (124, 255, 255), (252, 255, 255), (2, 255, 255), (10, 255, 255), (26, 255, 255),
    (58, 255, 255), (122, 255, 255), (250, 255, 255), (14, 255, 255), (30, 255, 255), (62, 255, 255), (126, 255, 255), (254, 255, 255),
    (30, 255, 255), (62, 255, 255), (126, 255, 255), (254, 255, 255), (62, 255, 255), (126, 255, 255), (254, 255, 255), (126, 255, 255),
    (254, 255, 255), (254, 255, 255), (1, 255, 255), (5, 255, 255), (13, 255, 255), (29, 255, 255), (61, 255, 255), (125, 255, 255),
    (253, 255, 255), (15, 255, 255), (31, 255, 255), (63, 255, 255), (127, 255, 255), (255, 255, 255), (31, 255, 255), (63, 255, 255),
    (127, 255, 255), (255, 255, 255), (63, 255, 255), (127, 255, 255), (255, 255, 255), (127, 255, 255), (255, 255, 255), (255, 255, 255),
    (31, 255, 255), (63, 255, 255), (127, 255, 255), (255, 255, 255), (63, 255, 255), (127, 255, 255), (255, 255, 255), (127, 255, 255),
    (255, 255, 255), (255, 255, 255), (63, 255, 255), (127, 255, 255), (255, 255, 255), (127, 255, 255), (255, 255, 255), (255, 255, 255),
    (127, 255, 255), (255, 255, 255), (255, 255, 255), (255, 255, 255), (63, 255, 255), (127, 255, 255), (255, 255, 255), (127, 255, 255),
    (255, 255, 255), (255, 255, 255), (127, 255, 255), (255, 255, 255), (255, 255, 255), (255, 255, 255), (127, 255, 255), (255, 255, 255),
    (255, 255, 255), (255, 255, 255), (255, 255, 255), (127, 255, 255), (255, 255, 255), (255, 255, 255), (255, 255, 255), (255, 255, 255),
    (255, 255, 255), (255, 255, 253), (127, 255, 254), (255, 255, 254), (255, 255, 254), (255, 255, 254), (255, 255, 254), (255, 255, 254),
    (255, 255, 250), (255, 255, 252), (255, 255, 248), (255, 255, 240), (255, 255, 224), (255, 255, 192), (255, 255, 128), (255, 255, 0)]

@[expose] def kacThetaE8 : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

open KacMask in
theorem kacMaskE8_eq : (Tag.E8.artifactRoots.map fun l =>
    (zm (toVec Tag.E8.rank l), zm (toVec Tag.E8.rank l + kacThetaE8),
      zm (toVec Tag.E8.rank l - kacThetaE8))) = kacMaskE8 := by
  decide +kernel

open KacMask in
theorem kacCount_setOf_E8 (m : ℕ) : kacCount .E8 kacThetaE8 (setOf Tag.E8.rank m) =
    (kacMaskE8.filter fun t => kacTestB Tag.E8.rank m t.1 t.2.1 t.2.2).length := by
  rw [kacCount_setOf, kacMaskE8_eq]

set_option maxRecDepth 100000

open KacMask in
theorem kacCount_E8_six_m : ∀ m < 2 ^ (Tag.E8.rank + 1), (setOf Tag.E8.rank m).card = 6 →
    (kacMaskE8.filter fun t => kacTestB Tag.E8.rank m t.1 t.2.1 t.2.2).length = 72 →
    setOf Tag.E8.rank m = {some 0, some 1, some 2, some 3, some 4, some 5} := by
  decide +kernel

open KacMask in
theorem kacCount_E8_four_m : ∀ m < 2 ^ (Tag.E8.rank + 1), (setOf Tag.E8.rank m).card = 4 →
    (kacMaskE8.filter fun t => kacTestB Tag.E8.rank m t.1 t.2.1 t.2.2).length = 24 →
    setOf Tag.E8.rank m = {some 1, some 2, some 3, some 4} := by
  decide +kernel

theorem kacCount_E8_six : ∀ C : Finset (Option (Fin Tag.E8.rank)), C.card = 6 →
    kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] C = 72 →
    C = {some 0, some 1, some 2, some 3, some 4, some 5} := by
  refine KacMask.forall_finset (P := fun C => C.card = 6 →
    kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] C = 72 →
    C = {some 0, some 1, some 2, some 3, some 4, some 5}) fun m hm => ?_
  rw [show kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] (KacMask.setOf Tag.E8.rank m) =
    kacCount .E8 kacThetaE8 (KacMask.setOf Tag.E8.rank m) from rfl, kacCount_setOf_E8]
  exact kacCount_E8_six_m m hm

theorem kacCount_E8_four : ∀ C : Finset (Option (Fin Tag.E8.rank)), C.card = 4 →
    kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] C = 24 → C = {some 1, some 2, some 3, some 4} := by
  refine KacMask.forall_finset (P := fun C => C.card = 4 →
    kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] C = 24 → C = {some 1, some 2, some 3, some 4})
    fun m hm => ?_
  rw [show kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] (KacMask.setOf Tag.E8.rank m) =
    kacCount .E8 kacThetaE8 (KacMask.setOf Tag.E8.rank m) from rfl, kacCount_setOf_E8]
  exact kacCount_E8_four_m m hm

theorem kacCount_E7_six : ∀ C : Finset (Option (Fin Tag.E7.rank)), C.card = 6 →
    kacCount .E7 ![2, 2, 3, 4, 3, 2, 1] C = 72 →
    C = {some 0, some 1, some 2, some 3, some 4, some 5} := by
  decide +kernel

theorem kacCount_E7_four : ∀ C : Finset (Option (Fin Tag.E7.rank)), C.card = 4 →
    kacCount .E7 ![2, 2, 3, 4, 3, 2, 1] C = 24 → C = {some 1, some 2, some 3, some 4} := by
  decide +kernel

theorem kacCount_E6_four : ∀ C : Finset (Option (Fin Tag.E6.rank)), C.card = 4 →
    kacCount .E6 ![1, 2, 2, 3, 2, 1] C = 24 → C = {some 1, some 2, some 3, some 4} := by
  decide +kernel

theorem kacCount_F4_four : ∀ C : Finset (Option (Fin Tag.F4.rank)), C.card = 4 →
    kacCount .F4 ![2, 3, 4, 2] C ≠ 24 := by
  decide +kernel

end CFSG.HardMathSupport.Timmesfeld.LangTorus
