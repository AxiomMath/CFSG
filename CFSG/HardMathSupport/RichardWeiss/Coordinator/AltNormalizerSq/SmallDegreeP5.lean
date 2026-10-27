module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbAltFive
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open CFSG.AGLEmbedding

variable {G : Type} [Group G]

theorem conj_mem_barM {M L : Subgroup G} (m : ↥M)
    (hm : (m : G) ∈ Subgroup.normalizer (L : Set G))
    {n : ↥M ⧸ CFSG.pCore 2 ↥M} (hn : n ∈ barM M L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) m * n *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m)⁻¹ ∈ barM M L := by
  unfold barM at hn ⊢
  obtain ⟨l, hl, rfl⟩ := hn
  refine ⟨m * l * m⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
  · have h := (Subgroup.mem_normalizer_iff.mp hm (l : G)).mp (Subgroup.mem_subgroupOf.mp hl)
    simpa [mul_assoc] using h
  · simp [map_mul, map_inv]

theorem barM_le_normalizer_barM {M L U : Subgroup G}
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) :
    barM M U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro x hx
  unfold barM at hx
  obtain ⟨m, hm, rfl⟩ := hx
  have hmL : ((m : ↥M) : G) ∈ Subgroup.normalizer (L : Set G) :=
    hUL (Subgroup.mem_subgroupOf.mp hm)
  have hmL' : (((m⁻¹ : ↥M)) : G) ∈ Subgroup.normalizer (L : Set G) := by
    simpa using inv_mem hmL
  refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => conj_mem_barM m hmL hn, fun hn => ?_⟩
  have := conj_mem_barM m⁻¹ hmL' hn
  simpa [map_inv, mul_assoc] using this

theorem isPGroup_barM_of {M U : Subgroup G} {p : ℕ} (hUp : IsPGroup p U) :
    IsPGroup p ↥(barM M U) := by
  have h : IsPGroup p ↥(U.subgroupOf M) := IsPGroup.comap_subtype hUp
  exact h.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))

theorem relIndex_inf_blockCentralizer_eq {M L U : Subgroup G} (hUM : U ≤ M) :
    (U ⊓ blockCentralizer M L).relIndex U =
      (barM M U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex
        (barM M U) := by
  set ρ' : ↥U →* (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hUM) with hρ'
  have hmap : (⊤ : Subgroup ↥U).map ρ' = barM M U := by
    ext x
    unfold barM
    constructor
    · rintro ⟨u, -, rfl⟩
      exact ⟨⟨(u : G), hUM u.2⟩, Subgroup.mem_subgroupOf.mpr u.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩, Subgroup.mem_top _, rfl⟩
  have hsub : (U ⊓ blockCentralizer M L).subgroupOf U =
      (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap ρ' := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    have key := mem_blockCentralizer_iff (M := M) (L := L) ⟨(u : G), hUM u.2⟩
    constructor
    · rintro ⟨-, hB⟩
      exact key.mp hB
    · intro h
      exact ⟨u.2, key.mpr h⟩
  calc (U ⊓ blockCentralizer M L).relIndex U
      = ((U ⊓ blockCentralizer M L).subgroupOf U).index := rfl
    _ = ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap ρ').index := by
        rw [hsub]
    _ = ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap ρ').relIndex ⊤ :=
        (Subgroup.relIndex_top_right _).symm
    _ = (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex (barM M U) := by
        rw [Subgroup.relIndex_comap, hmap]
    _ = (barM M U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex
          (barM M U) := (Subgroup.inf_relIndex_left _ _).symm

theorem altNormalizerSq_deg6_of_five_le [Finite G]
    {M S L : Subgroup G} {p : ℕ} {U : Subgroup G}
    (hp : p.Prime) (hp5 : 5 ≤ p) (_hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hdeg6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hUK : U ≤ M ⊓ Subgroup.normalizer (S : Set G)) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hUp : IsPGroup p U) :
    (U ⊓ blockCentralizer M L).relIndex U ≤ p := by
  have hUM : U ≤ M := fun u hu => (hUK hu).1
  have hK : KFactAltSixSevenAutFive := kFactAltSixSevenAutFive
  have hrel := hK (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) (barM M U) p hL.component (Or.inl hdeg6)
    hp hp5 (barM_le_normalizer_barM hUL) (isPGroup_barM_of hUp)
  rw [relIndex_inf_blockCentralizer_eq hUM]
  exact hrel

end CFSG.HardMathSupport.RichardWeiss.Coordinator

end
