module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3A
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Aut

public section

namespace CFSG.ComponentClassification.HarrisLit.Q81

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.CatFactsL4U4.DiagU
  CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {Q : Subgroup G}

section Phi

variable {P : Type*} [Group P] (e : ↥Q ⧸ center ↥Q ≃* P)

theorem xAut_mul {x y : G} (hx : x ∈ normalizer (Q : Set G)) (hy : y ∈ normalizer (Q : Set G)) :
    C3.xAut (mul_mem hx hy) = C3.xAut hx * C3.xAut hy :=
  map_mul (normalizerConj Q) ⟨x, hx⟩ ⟨y, hy⟩

theorem phi_mul {x y : G} (hx : x ∈ normalizer (Q : Set G)) (hy : y ∈ normalizer (Q : Set G)) :
    C3.phi (mul_mem hx hy) e = C3.phi hx e * C3.phi hy e := by
  rw [C3.phi, C3.phi, C3.phi, xAut_mul, GSThmB.Cent516.barAut_mul, map_mul]

theorem phi_one : C3.phi (one_mem (normalizer (Q : Set G))) e = 1 := by
  rw [C3.phi, show C3.xAut (one_mem (normalizer (Q : Set G))) = 1 from
    map_one (normalizerConj Q), GSThmB.Cent516.barAut_one, map_one]

theorem phi_congr {x y : G} (hxy : x = y) (hx : x ∈ normalizer (Q : Set G))
    (hy : y ∈ normalizer (Q : Set G)) : C3.phi hx e = C3.phi hy e := by
  subst hxy
  rfl

theorem phi_inv {x : G} (hx : x ∈ normalizer (Q : Set G)) :
    C3.phi (inv_mem hx) e = (C3.phi hx e)⁻¹ := by
  have h1 := phi_mul e (inv_mem hx) hx
  rw [phi_congr e (inv_mul_cancel x) (mul_mem (inv_mem hx) hx) (one_mem _), phi_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem phi_of_mem {q : G} (hq : q ∈ Q) :
    C3.phi (Q.le_normalizer hq) e = MulAut.conj (C3.piQ e ⟨q, hq⟩) := by
  ext y
  obtain ⟨r, rfl⟩ := C3.piQ_surjective e y
  rw [C3.phi_piQ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem phi_of_mem_centralizer {c : G} (hc : c ∈ centralizer (Q : Set G)) :
    C3.phi (Subgroup.centralizer_le_normalizer (Q : Set G) hc) e = 1 := by
  ext y
  obtain ⟨r, rfl⟩ := C3.piQ_surjective e y
  rw [C3.phi_piQ, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [C3.coe_xAut]
  have h1 : (r : G) * c = c * r := mem_centralizer_iff.mp hc r r.2
  calc c * (r : G) * c⁻¹ = (r : G) * c * c⁻¹ := by rw [h1]
    _ = r := by group

end Phi

section Linear

variable {F : Type} [Field F] [Finite F] (e : ↥Q ⧸ center ↥Q ≃* projectiveSL 4 F)

@[expose] def innDiagL : Subgroup G where
  carrier := {x | ∃ hx : x ∈ normalizer (Q : Set G), C3.phi hx e ∈ (conjAut 4 F).range}
  one_mem' := ⟨one_mem _, by rw [phi_one]; exact one_mem _⟩
  mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ =>
    ⟨mul_mem hx hy, by rw [phi_mul e hx hy]; exact mul_mem hx' hy'⟩
  inv_mem' := fun ⟨hx, hx'⟩ => ⟨inv_mem hx, by rw [phi_inv e hx]; exact inv_mem hx'⟩

omit [Finite F] in
theorem mem_innDiagL_iff {x : G} (hx : x ∈ normalizer (Q : Set G)) :
    x ∈ innDiagL e ↔ C3.phi hx e ∈ (conjAut 4 F).range :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩

omit [Finite F] in
theorem innDiagL_le_normalizer : innDiagL e ≤ normalizer (Q : Set G) := fun _ ⟨hx, _⟩ => hx

omit [Finite F] in
theorem conj_mem_range_conjAut (y : projectiveSL 4 F) :
    MulAut.conj y ∈ (conjAut 4 F).range := by
  obtain ⟨s, rfl⟩ := proj_surjective 4 F y
  exact ⟨_, conjAut_toGL s⟩

omit [Finite F] in
theorem le_innDiagL : Q ≤ innDiagL e := fun q hq =>
  ⟨Q.le_normalizer hq, by rw [phi_of_mem e hq]; exact conj_mem_range_conjAut _⟩

omit [Finite F] in
theorem centralizer_le_innDiagL : centralizer (Q : Set G) ≤ innDiagL e := fun c hc =>
  ⟨Subgroup.centralizer_le_normalizer (Q : Set G) hc, by
    rw [phi_of_mem_centralizer e hc]; exact one_mem _⟩

theorem mul_mem_innDiagL (hF : Nat.card F = 3) {x y : G} (hx : x ∈ normalizer (Q : Set G))
    (hy : y ∈ normalizer (Q : Set G)) (hx' : x ∉ innDiagL e) (hy' : y ∉ innDiagL e) :
    x * y ∈ innDiagL e := by
  rw [mem_innDiagL_iff e hx] at hx'
  rw [mem_innDiagL_iff e hy] at hy'
  refine ⟨mul_mem hx hy, ?_⟩
  rw [phi_mul e hx hy]
  exact mul_mem_range_conjAut hF hx' hy'

end Linear

section Unitary

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K)
  (e : ↥Q ⧸ center ↥Q ≃* StatedProj (StatedSU 4 (3 ^ 1) K))

@[expose] def innDiagU : Subgroup G where
  carrier := {x | ∃ hx : x ∈ normalizer (Q : Set G), C3.phi hx e ∈ InnU 3 1 K h}
  one_mem' := ⟨one_mem _, by rw [phi_one]; exact one_mem _⟩
  mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ =>
    ⟨mul_mem hx hy, by rw [phi_mul e hx hy]; exact mul_mem hx' hy'⟩
  inv_mem' := fun ⟨hx, hx'⟩ => ⟨inv_mem hx, by rw [phi_inv e hx]; exact inv_mem hx'⟩

theorem mem_innDiagU_iff {x : G} (hx : x ∈ normalizer (Q : Set G)) :
    x ∈ innDiagU h e ↔ C3.phi hx e ∈ InnU 3 1 K h :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩

theorem innDiagU_le_normalizer : innDiagU h e ≤ normalizer (Q : Set G) := fun _ ⟨hx, _⟩ => hx

theorem conj_mem_InnU (y : StatedProj (StatedSU 4 (3 ^ 1) K)) :
    MulAut.conj y ∈ InnU 3 1 K h := by
  obtain ⟨s, rfl⟩ := thU_surjective y
  exact ⟨_, isCU_conj h s⟩

theorem le_innDiagU : Q ≤ innDiagU h e := fun q hq =>
  ⟨Q.le_normalizer hq, by rw [phi_of_mem e hq]; exact conj_mem_InnU h _⟩

theorem centralizer_le_innDiagU : centralizer (Q : Set G) ≤ innDiagU h e := fun c hc =>
  ⟨Subgroup.centralizer_le_normalizer (Q : Set G) hc, by
    rw [phi_of_mem_centralizer e hc]; exact one_mem _⟩

theorem mul_mem_innDiagU {x y : G} (hx : x ∈ normalizer (Q : Set G))
    (hy : y ∈ normalizer (Q : Set G)) (hx' : x ∉ innDiagU h e) (hy' : y ∉ innDiagU h e) :
    x * y ∈ innDiagU h e := by
  rw [mem_innDiagU_iff h e hx] at hx'
  rw [mem_innDiagU_iff h e hy] at hy'
  refine ⟨mul_mem hx hy, ?_⟩
  rw [phi_mul e hx hy]
  exact mul_mem_InnU h hx' hy'

end Unitary

end CFSG.ComponentClassification.HarrisLit.Q81
