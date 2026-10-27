module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit

open Subgroup

variable {G : Type*} [Group G] (D Y : Subgroup G)

@[expose] def normDY : Subgroup G := normalizer (D : Set G) ⊓ normalizer (Y : Set G)

theorem mem_normDY {g : G} :
    g ∈ normDY D Y ↔ g ∈ normalizer (D : Set G) ∧ g ∈ normalizer (Y : Set G) :=
  Subgroup.mem_inf

theorem conj_mem_D {g : G} (hg : g ∈ normDY D Y) {x : G} (hx : x ∈ D) :
    g * x * g⁻¹ ∈ D :=
  (Subgroup.mem_normalizer_iff.mp ((mem_normDY D Y).mp hg).1 x).mp hx

theorem conj_inv_mem_D {g : G} (hg : g ∈ normDY D Y) {x : G} (hx : x ∈ D) :
    g⁻¹ * x * g ∈ D :=
  (Subgroup.mem_normalizer_iff''.mp ((mem_normDY D Y).mp hg).1 x).mp hx

@[expose] def conjD (g : normDY D Y) : D ≃* D where
  toFun x := ⟨(g : G) * (x : G) * (g : G)⁻¹, conj_mem_D D Y g.2 x.2⟩
  invFun x := ⟨(g : G)⁻¹ * (x : G) * (g : G), conj_inv_mem_D D Y g.2 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjD_apply_coe (g : normDY D Y) (x : D) :
    ((conjD D Y g x : D) : G) = (g : G) * (x : G) * (g : G)⁻¹ :=
  rfl

theorem conjD_symm_apply_coe (g : normDY D Y) (x : D) :
    (((conjD D Y g).symm x : D) : G) = (g : G)⁻¹ * (x : G) * (g : G) :=
  rfl

theorem conjD_one (x : D) : conjD D Y 1 x = x :=
  Subtype.ext (by simp [conjD_apply_coe])

theorem conjD_mul (g h : normDY D Y) (x : D) :
    conjD D Y (g * h) x = conjD D Y g (conjD D Y h x) :=
  Subtype.ext (by simp [conjD_apply_coe, mul_assoc])

theorem map_conjD_eq (g : normDY D Y) :
    (Y.subgroupOf D).map (conjD D Y g).toMonoidHom = Y.subgroupOf D := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    conjD_symm_apply_coe]
  exact (Subgroup.mem_normalizer_iff''.mp ((mem_normDY D Y).mp g.2).2 (x : G)).symm

variable [(Y.subgroupOf D).Normal]

@[expose] def actQuot : normDY D Y →* MulAut (D ⧸ Y.subgroupOf D) where
  toFun g := QuotientGroup.congr (Y.subgroupOf D) (Y.subgroupOf D) (conjD D Y g)
    (map_conjD_eq D Y g)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (conjD_one D Y x)
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (conjD_mul D Y g h x)

theorem actQuot_mk (g : normDY D Y) (x : D) :
    ∃ h : (g : G) * (x : G) * (g : G)⁻¹ ∈ D,
      actQuot D Y g (QuotientGroup.mk x) = QuotientGroup.mk ⟨(g : G) * (x : G) * (g : G)⁻¹, h⟩ :=
  ⟨conj_mem_D D Y g.2 x.2, rfl⟩

theorem conj_mem_Y (x : D) {m : G} (hm : m ∈ D) (h : m ∈ Y) :
    (x : G) * m * (x : G)⁻¹ ∈ Y :=
  Subgroup.mem_subgroupOf.mp
    (Subgroup.Normal.conj_mem inferInstance ⟨m, hm⟩ (Subgroup.mem_subgroupOf.mpr h) x)

theorem conj_mem_iff (x : D) {m : G} (hm : m ∈ D) :
    (x : G) * m * (x : G)⁻¹ ∈ Y ↔ m ∈ Y := by
  refine ⟨fun h => ?_, conj_mem_Y D Y x hm⟩
  have hm' : (x : G) * m * (x : G)⁻¹ ∈ D := D.mul_mem (D.mul_mem x.2 hm) (D.inv_mem x.2)
  have h' := conj_mem_Y D Y x⁻¹ hm' h
  simpa [mul_assoc] using h'

theorem inv_mul_mem_iff (x : D) {c : G} (hc : c ∈ D) :
    (x : G)⁻¹ * c ∈ Y ↔ c * (x : G)⁻¹ ∈ Y := by
  have hm : (x : G)⁻¹ * c ∈ D := D.mul_mem (D.inv_mem x.2) hc
  have h := conj_mem_iff D Y x hm
  simp only [mul_inv_cancel_left] at h
  exact h.symm

theorem actQuot_mk_eq_iff (g : normDY D Y) (x : D) :
    actQuot D Y g (QuotientGroup.mk x) = QuotientGroup.mk x ↔
      (g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹ ∈ Y := by
  obtain ⟨h, hh⟩ := actQuot_mk D Y g x
  rw [hh, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact inv_mul_mem_iff D Y x (conj_mem_D D Y g.2 x.2)

theorem card_D_eq (hYD : Y ≤ D) :
    Nat.card D = Nat.card (D ⧸ Y.subgroupOf D) * Nat.card Y := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf D)]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYD).toEquiv

theorem quot_mul_self (h : ∀ x ∈ D, x * x ∈ Y) (a : D ⧸ Y.subgroupOf D) : a * a = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact h (x : G) x.2

theorem quot_comm (h : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Y) (a b : D ⧸ Y.subgroupOf D) :
    a * b = b * a := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hy : (y : G)⁻¹ ∈ D := D.inv_mem y.2
  have hx : (x : G)⁻¹ ∈ D := D.inv_mem x.2
  simpa [mul_assoc] using h (y : G)⁻¹ hy (x : G)⁻¹ hx

theorem mk_eq_one_iff (x : D) :
    (QuotientGroup.mk x : D ⧸ Y.subgroupOf D) = 1 ↔ (x : G) ∈ Y := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit
