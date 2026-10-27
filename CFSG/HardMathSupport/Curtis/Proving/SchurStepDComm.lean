module

public import CFSG.HardMathSupport.Curtis.Proving.ActsTrivially
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_mem_blockQ {M L Q : Subgroup G} (hML : IsTwoPrimeComponent M L)
    (hQM : Q ≤ M) (hQN : Q ≤ Subgroup.normalizer (L : Set G))
    (hcent : barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {a l : G} (ha : a ∈ Q) (hl : l ∈ L) : a * l * a⁻¹ * l⁻¹ ∈ blockQ L := by
  have haM : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨a, hQM ha⟩ : ↥M) ∈ barM M Q :=
    Subgroup.mem_map.mpr ⟨⟨a, hQM ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
  have hlM : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨l, hML.le hl⟩ : ↥M) ∈ barM M L :=
    Subgroup.mem_map.mpr ⟨⟨l, hML.le hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.1 (hcent haM) _ hlM
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⁅(⟨a, hQM ha⟩ : ↥M), ⟨l, hML.le hl⟩⁆) = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  have h2 : ((⁅(⟨a, hQM ha⟩ : ↥M), ⟨l, hML.le hl⟩⁆ : ↥M) : G) ∈ pCoreOf 2 M :=
    (mk_eq_one_iff_coe_mem_pCoreOf _).1 h1
  have e : ((⁅(⟨a, hQM ha⟩ : ↥M), ⟨l, hML.le hl⟩⁆ : ↥M) : G) = a * l * a⁻¹ * l⁻¹ := by
    simp [commutatorElement_def]
  rw [e] at h2
  have hL : a * l * a⁻¹ * l⁻¹ ∈ L :=
    L.mul_mem (conj_mem_of_mem_normalizer (hQN ha) hl) (L.inv_mem hl)
  have hmem : a * l * a⁻¹ * l⁻¹ ∈ L ⊓ pCoreOf 2 M := Subgroup.mem_inf.2 ⟨hL, h2⟩
  rw [hML.inf_twoCore] at hmem
  exact hmem

end CFSG.HardMathSupport.Curtis.Proving

end
