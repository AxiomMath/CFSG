module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem blockQ_eq_map (L : Subgroup G) : blockQ L = (CFSG.pCore 2 L).map L.subtype := by
  unfold blockQ CFSG.Open.pCoreOf
  try with_reducible rfl

theorem blockQ_conj_mem {L : Subgroup G} {g : G} (hg : g ∈ L) {q : G} (hq : q ∈ blockQ L) :
    g * q * g⁻¹ ∈ blockQ L := by
  rw [blockQ_eq_map] at hq ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
  have hc : (⟨g, hg⟩ : L) * y * (⟨g, hg⟩ : L)⁻¹ ∈ CFSG.pCore 2 L :=
    (inferInstance : (CFSG.pCore 2 L).Normal).conj_mem y hy ⟨g, hg⟩
  exact Subgroup.mem_map.mpr ⟨_, hc, by simp⟩

theorem blockU_conj_mem {L : Subgroup G} {g : G} (hg : g ∈ L) {u : G} (hu : u ∈ blockU L) :
    g⁻¹ * u * g ∈ blockU L := by
  have key : ⁅blockQ L, L⁆ ≤ (blockU L).comap (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro q hq x hx
    rw [Subgroup.mem_comap]
    have hgi : g⁻¹ ∈ L := L.inv_mem hg
    have h1 : g⁻¹ * q * g⁻¹⁻¹ ∈ blockQ L := blockQ_conj_mem hgi hq
    have h2 : g⁻¹ * x * g⁻¹⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hgi hx) (L.inv_mem hgi)
    have e : (MulAut.conj g⁻¹).toMonoidHom ⁅q, x⁆ =
        ⁅g⁻¹ * q * g⁻¹⁻¹, g⁻¹ * x * g⁻¹⁻¹⁆ := by
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator h1 h2
  have := key hu
  rw [Subgroup.mem_comap] at this
  simpa [MulAut.conj_apply] using this

