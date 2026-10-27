module

public import CFSG.GH74.QTGen4.Recog.Ku.Defs
public import CFSG.Quasithin.Recognition.HSType154

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

variable {G : Type} [Group G]

theorem lamS_le_alternating : lamS ≤ alternatingGroup (Fin 6) := by
  rw [← closure_αS_βS, Subgroup.closure_le]
  intro σ hσ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl
  · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]
    decide +kernel

namespace KuA6Model

variable {E W V2 N : Subgroup G} {z : G}

theorem mem_pre_iff_of_mem (Ψ : KuA6Model E W V2 N z) {X : Subgroup (Equiv.Perm (Fin 6))} {n : G}
    (hn : n ∈ N) : n ∈ Ψ.pre X ↔ Ψ.π ⟨n, hn⟩ ∈ X := by
  unfold KuA6Model.pre
  constructor
  · intro h
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp h
    have hm' : m = ⟨n, hn⟩ := Subtype.ext hmn
    subst hm'
    exact Subgroup.mem_comap.mp hm
  · intro h
    exact Subgroup.mem_map.mpr ⟨⟨n, hn⟩, Subgroup.mem_comap.mpr h, rfl⟩

theorem selfNormalizing_L2 (Ψ : KuA6Model E W V2 N z) :
    ∀ n ∈ N, (∀ x ∈ Ψ.L2, n * x * n⁻¹ ∈ Ψ.L2) → n ∈ Ψ.L2 := by
  intro n hn hcj
  show n ∈ Ψ.pre lamS
  rw [Ψ.mem_pre_iff_of_mem hn]
  have hconj : ∀ y ∈ lamS, Ψ.π ⟨n, hn⟩ * y * (Ψ.π ⟨n, hn⟩)⁻¹ ∈ lamS := by
    intro y hy
    obtain ⟨m, hm⟩ := Ψ.π_surj y (lamS_le_alternating hy)
    have hmL2 : (m : G) ∈ Ψ.L2 := by
      show (m : G) ∈ Ψ.pre lamS
      rw [Ψ.mem_pre_iff_of_mem m.2]
      rw [show Ψ.π ⟨(m : G), m.2⟩ = y from hm]
      exact hy
    have hnm : n * (m : G) * n⁻¹ ∈ N := N.mul_mem (N.mul_mem hn m.2) (N.inv_mem hn)
    have hc := (Ψ.mem_pre_iff_of_mem hnm).mp (hcj (m : G) hmL2)
    have heq : (⟨n * (m : G) * n⁻¹, hnm⟩ : ↥N) = ⟨n, hn⟩ * m * (⟨n, hn⟩ : ↥N)⁻¹ := rfl
    rw [heq, map_mul, map_mul, map_inv, hm] at hc
    exact hc
  have hNorm : NormLamS (Ψ.π ⟨n, hn⟩) := ⟨hconj _ αS_mem, hconj _ βS_mem⟩
  have hsign : Equiv.Perm.sign (Ψ.π ⟨n, hn⟩) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (Ψ.π_alt ⟨n, hn⟩)
  exact mem_lamS_of_normLamS _ hsign hNorm

end KuA6Model

end CFSG.GH74.QTGen4.Ku

end
