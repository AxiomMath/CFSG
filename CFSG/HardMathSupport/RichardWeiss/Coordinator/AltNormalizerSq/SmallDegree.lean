module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Action
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.SmallDegreeP5

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open CFSG.AGLEmbedding

variable {G : Type} [Group G]

theorem relIndex_inf_blockCentralizer_eq_index_ker {M L U : Subgroup G} (hUM : U ≤ M)
    {Ω : Type} {π : ↥U →* Equiv.Perm Ω}
    (hπ : ∀ h : ↥U, π h = 1 ↔
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(h : G), hUM h.2⟩ : ↥M)) ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    (U ⊓ blockCentralizer M L).relIndex U = π.ker.index := by
  have hker : (U ⊓ blockCentralizer M L).subgroupOf U = π.ker := by
    ext h
    have key := mem_blockCentralizer_iff (M := M) (L := L) ⟨(h : G), hUM h.2⟩
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hπ, Subgroup.mem_inf]
    exact ⟨fun hh => key.mp hh.2, fun hh => ⟨h.2, key.mpr hh⟩⟩
  exact congrArg Subgroup.index hker

theorem relIndex_le_of_alt_fin {M L U : Subgroup G} {p k : ℕ} (hp : p.Prime)
    (hk : k < 2 * p) (h5 : 5 ≤ k) (h6 : k ≠ 6) (hUM : U ≤ M)
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hUp : IsPGroup p U)
    (φ : ↥(barM M L) ≃* ↥(alternatingGroup (Fin k))) :
    (U ⊓ blockCentralizer M L).relIndex U ≤ p := by
  set ψ : ↥U →* (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hUM) with hψdef
  have hψ : ∀ h : ↥U, ψ h ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro h
    have hmem : ψ h ∈ barM M U :=
      ⟨⟨(h : G), hUM h.2⟩, Subgroup.mem_subgroupOf.mpr h.2, rfl⟩
    exact barM_le_normalizer_barM hUL hmem
  obtain ⟨π, -, hπ⟩ := exists_action (Ω := Fin k) (by rwa [Fintype.card_fin])
    (by rwa [Fintype.card_fin]) φ ψ hψ
  have hπ' : ∀ h : ↥U, π h = 1 ↔
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(h : G), hUM h.2⟩ : ↥M)) ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun h => hπ h
  rw [relIndex_inf_blockCentralizer_eq_index_ker hUM hπ', Subgroup.index_ker]
  have hpg : IsPGroup p π.range :=
    hUp.of_surjective π.rangeRestrict (MonoidHom.rangeRestrict_surjective π)
  exact card_le_of_isPGroup_perm_lt hp hk hpg

end CFSG.HardMathSupport.RichardWeiss.Coordinator

end
