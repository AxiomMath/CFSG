module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Construct
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.PushUpElt

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (mem_barM)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem commutator_pCore_le_blockV_a7 (hclass : A7PerfectSylow)
    (h85 : Asc81bEightFive) (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L)
    (hact : ∀ s ∈ S, ∃ l ∈ L, ∀ v ∈ blockV S L, s * v * s⁻¹ = l * v * l⁻¹)
    (he : Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin 7))) :
    ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L := by
  classical
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  obtain ⟨K, hKL, hKperf, hKQ, hKcore, hKshort, hKnc⟩ :=
    exists_block_of_perfectSylow hclass h85 hX hA hL hact he
  set M : Subgroup G := L ⊔ S with hM
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set V : Subgroup G := blockV S L with hV
  have hLs : IsTwoPrimeComponent M L :=
    Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1
      hA.twoRadical.isPGroup hSL
  have hLM : L ≤ M := le_sup_left
  have hKM : K ≤ M := hKL.trans hLM
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := sup_le_normalizer_blockV S L
  have hVQ : V ≤ Q := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) :=
    AscTenThree.le_centralizer_omegaOneCenterOf_self (pCoreOf 2 M)
  have hne : ⁅V, K⁆ ≠ ⊥ := by
    intro h
    apply hKnc
    have hKC : K ≤ Subgroup.centralizer (V : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact h)
    have hcen : barM M (L ⊓ Subgroup.centralizer (V : Set G)) ≤
        (Subgroup.center ↥(barM M L)).map (barM M L).subtype :=
      barM_inf_le_center_of_core_le hLs (le_sup_left.trans (le_normalizer_centralizer_blockV S L))
        (inf_le_right.trans hQC) (not_le_centralizer_blockV hA hL hSL)
    exact (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.barM_mono (le_inf hKL hKC)).trans hcen
  have hcomm : ⁅Q, K⁆ = ⁅V, K⁆ :=
    commutator_eq_of_short hKshort hKperf hKQ (fun k hk => hMQ (hKM hk)) hKcore hVQ
      (fun k hk => hMV (hKM hk)) hne
  have hVK : ⁅V, K⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    have h1 : k * v⁻¹ * k⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hMV (hKM hk)) v⁻¹).mp (V.inv_mem hv)
    have : ⁅v, k⁆ = v * (k * v⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [this]; exact V.mul_mem hv h1
  have hnc : ∃ k : ↥M, (k : G) ∈ K ∧ (QuotientGroup.mk k : ↥M ⧸ CFSG.pCore 2 ↥M) ∉
      (Subgroup.center ↥(barM M L)).map (barM M L).subtype := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hKnc
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (mem_barM y).1 hy
    exact hcon k hk
  obtain ⟨k, hkK, hkn⟩ := hnc
  have hyL : (k : G) ∈ L := hKL hkK
  refine commutator_pCore_le_blockV_of_noncentral hX hA hL hyL (k := 0) ?_ ?_
  · intro hz
    apply hkn
    refine ⟨_, hz, ?_⟩
    simp [Proving.coe_barMHomSub]
    rfl
  · intro q hq
    simp only [pow_zero, pow_one]
    exact hVK (hcomm ▸ Subgroup.commutator_mem_commutator hq hkK)

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
