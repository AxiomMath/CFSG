module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP4
public import CFSG.Quasithin.EmptyFaithful.S151S4D
public import CFSG.Quasithin.EmptyFaithful.S152Y22
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem nonempty_twoResidual_quot_pCore_mulEquiv (H : Subgroup G) :
    Nonempty (↥(twoResidual H) ⧸ CFSG.pCore 2 ↥(twoResidual H) ≃*
      ↥(twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) := by
  let π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let f : ↥(twoResidual H) →* ↥H ⧸ CFSG.pCore 2 ↥H :=
    π.comp (Subgroup.inclusion (twoResidual_le H))
  have hinc : (Subgroup.inclusion (twoResidual_le H)).range =
      (twoResidual H).subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hrange : f.range = twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [MonoidHom.range_comp, hinc]
    have hmap := B6.twoResidual_map_top (φ := π) (QuotientGroup.mk'_surjective _)
    rwa [B6.twoResidual_top_eq_subgroupOf H] at hmap
  have hker : f.ker = CFSG.pCore 2 ↥(twoResidual H) := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 (twoResidual H),
      S152Y.pCoreOf_eq_inf_of_normalizer (twoResidual_le H) (le_normalizer_twoResidual H)]
    ext x
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk ⟨(x : G), twoResidual_le H x.2⟩ : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 ↔
      (x : G) ∈ twoResidual H ⊓ CFSG.Open.pCoreOf 2 H
    rw [QuotientGroup.eq_one_iff, ← CFSG.mem_openPCoreOf_iff]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)⟩

theorem nonempty_twoResidual_top_mulEquiv_alt5 {Q : Type} [Group Q] [Finite Q]
    (h : Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨ Nonempty (Q ≃* Equiv.Perm (Fin 5))) :
    Nonempty (↥(twoResidual (⊤ : Subgroup Q)) ≃* alternatingGroup (Fin 5)) := by
  rcases h with hA | hS
  · obtain ⟨e⟩ := hA
    have hperf : ⁅(⊤ : Subgroup ↥(alternatingGroup (Fin 5))),
        (⊤ : Subgroup ↥(alternatingGroup (Fin 5)))⁆ = ⊤ := by
      rw [← commutator_def]
      exact commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)
    have hmap := B6.twoResidual_map_top (φ := e.toMonoidHom) e.surjective
    rw [S151S4.twoResidual_eq_self_of_perfect hperf] at hmap
    have htop : twoResidual (⊤ : Subgroup Q) = ⊤ :=
      Subgroup.map_injective (f := e.toMonoidHom) e.injective (by simpa using hmap)
    rw [htop]
    exact ⟨Subgroup.topEquiv.trans e⟩
  · obtain ⟨e⟩ := hS
    have hmap := B6.twoResidual_map_top (φ := e.toMonoidHom) e.surjective
    rw [H13.twoResidual_perm5_cv] at hmap
    have e' := Subgroup.equivMapOfInjective (twoResidual (⊤ : Subgroup Q)) e.toMonoidHom
      e.injective
    rw [hmap] at e'
    exact ⟨e'⟩

end CFSG.GroupTheory
