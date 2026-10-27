module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def IsGL3Ext (E N : Subgroup G) : Prop :=
  N ≤ E ∧ SecProp E N
    (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))

structure Gl3Pair (M L1 L2 : Subgroup G) : Prop where
  elem : IsElemAbelian 2 M
  card : Nat.card M = 2 ^ 6
  inf : L1 ⊓ L2 = M
  comm : ⁅L1, L2⁆ ≤ M
  ext1 : IsGL3Ext L1 M
  ext2 : IsGL3Ext L2 M

variable {M L1 L2 : Subgroup G}

theorem Gl3Pair.symm (h : Gl3Pair M L1 L2) : Gl3Pair M L2 L1 :=
  ⟨h.elem, h.card, by rw [inf_comm]; exact h.inf,
    by rw [Subgroup.commutator_comm]; exact h.comm, h.ext2, h.ext1⟩

theorem Gl3Pair.le_normalizer_M (h : Gl3Pair M L1 L2) : L1 ≤ normalizer (M : Set G) := by
  obtain ⟨hle, hnorm, -⟩ := h.ext1
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hnorm

theorem Gl3Pair.L1_le_normalizer_L2 (h : Gl3Pair M L1 L2) : L1 ≤ normalizer (L2 : Set G) := by
  have key : ∀ x ∈ L1, ∀ y ∈ L2, x * y * x⁻¹ ∈ L2 := by
    intro x hx y hy
    have hc : ⁅x, y⁆ ∈ M := h.comm (Subgroup.commutator_mem_commutator hx hy)
    have hM2 : M ≤ L2 := h.ext2.1
    have : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      rw [commutatorElement_def]; group
    rw [this]
    exact L2.mul_mem (hM2 hc) hy
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact key x hx y hy
  · intro hy
    have := key x⁻¹ (L1.inv_mem hx) _ hy
    simpa [mul_assoc] using this

theorem Gl3Pair.mem_centIn_conj (h : Gl3Pair M L1 L2) {D : Subgroup G} (hD : D ≤ L1) {y c : G}
    (hy : y ∈ L2) (hc : c ∈ centIn M D) : y * c * y⁻¹ ∈ centIn M D := by
  obtain ⟨hcM, hcD⟩ := Subgroup.mem_inf.mp hc
  have hcomm := Subgroup.mem_centralizer_iff.mp hcD
  have hyM : y * c * y⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp (h.symm.le_normalizer_M hy) c).mp hcM
  refine Subgroup.mem_inf.mpr ⟨hyM, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro d hd
  have hdL1 : d ∈ L1 := hD hd
  have hm : ⁅d, y⁆ ∈ M := h.comm (Subgroup.commutator_mem_commutator hdL1 hy)
  have hdc : d * c = c * d := hcomm d hd
  have hMcomm : ⁅d, y⁆ * (y * c * y⁻¹) = (y * c * y⁻¹) * ⁅d, y⁆ := by
    have := h.elem.1.is_comm.comm (⟨_, hm⟩ : ↥M) ⟨_, hyM⟩
    exact congrArg Subtype.val this
  have h1 : d * y * d⁻¹ = ⁅d, y⁆ * y := by
    rw [commutatorElement_def]; group
  have h2 : d * (y * c * y⁻¹) * d⁻¹ = y * c * y⁻¹ := by
    calc d * (y * c * y⁻¹) * d⁻¹
        = (d * y * d⁻¹) * (d * c * d⁻¹) * (d * y * d⁻¹)⁻¹ := by group
      _ = (⁅d, y⁆ * y) * c * (⁅d, y⁆ * y)⁻¹ := by
          rw [h1, show d * c * d⁻¹ = c by rw [hdc]; group]
      _ = ⁅d, y⁆ * (y * c * y⁻¹) * ⁅d, y⁆⁻¹ := by group
      _ = y * c * y⁻¹ := by rw [hMcomm]; group
  calc d * (y * c * y⁻¹) = (d * (y * c * y⁻¹) * d⁻¹) * d := by group
    _ = (y * c * y⁻¹) * d := by rw [h2]

theorem Gl3Pair.L2_le_normalizer_centIn (h : Gl3Pair M L1 L2) {D : Subgroup G} (hD : D ≤ L1) :
    L2 ≤ normalizer (centIn M D : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact h.mem_centIn_conj hD hy hc
  · intro hc
    have := h.mem_centIn_conj hD (L2.inv_mem hy) hc
    simpa [mul_assoc] using this

theorem Gl3Pair.isElemAbelian_centIn (h : Gl3Pair M L1 L2) (D : Subgroup G) :
    IsElemAbelian 2 (centIn M D) := by
  haveI := h.elem.1
  exact ⟨isMulCommutative_anti (inf_le_left : centIn M D ≤ M),
    fun x hx => h.elem.2 x (Subgroup.mem_inf.mp hx).1⟩

end CFSG.OddStandard.HigherRank.YamadaG23
