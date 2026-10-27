module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocGen
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiOddCore
public import CFSG.CharacterTheory.Semidihedral.CoreFreeDihedral
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {T : Type} [Group T] [Finite T]

theorem locBal1Two_of_fitting (hs : IsSimpleGroup T) (hna : ∃ a b : T, a * b ≠ b * a)
    (hT : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup (CFSG.generalizedFitting X)],
      (∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) →
      Nonempty (CFSG.generalizedFitting X ≃* T) → ∀ t : X, orderOf t = 2 →
        CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥) :
    S3T2A7.LocBal1Two T := by
  refine locBal1Two_of_normal (center_eq_bot_of_simple hs hna) fun X _ _ S _ hST hC t ht => ?_
  obtain ⟨ψ⟩ := hST
  have hSs : IsSimpleGroup S := by
    have := hs
    exact MulEquiv.isSimpleGroup ψ
  have hSna : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨ψ.symm a, ψ.symm b, fun h => hab (by simpa using congrArg ψ h)⟩
  have hF : CFSG.generalizedFitting X = S :=
    Semidihedral.CoreFreeDihedral.generalizedFitting_eq_of_normal_simple_centralizer_eq_bot S
      hSna hC
  have : IsSimpleGroup (CFSG.generalizedFitting X) := by rw [hF]; exact hSs
  refine hT X ?_ ⟨(MulEquiv.subgroupCongr hF).trans ψ⟩ t ht
  obtain ⟨a, b, hab⟩ := hSna
  refine ⟨(MulEquiv.subgroupCongr hF).symm a, (MulEquiv.subgroupCongr hF).symm b,
    fun h => hab ?_⟩
  simpa using congrArg (MulEquiv.subgroupCongr hF) h

theorem locBal1Two_linear_two {f : ℕ} (hf : 3 ≤ f)
    (h : LieModel T .PSL 2 2 f) (hp : ¬ (Nat.card T).Prime) : S3T2A7.LocBal1Two T := by
  have hst : StatedClassicalModel T .PSL 2 2 f :=
    GH74.statedClassicalModel_of_lieModel two_ne_zero h
  have hs := (LieType.Simplicity.fam_PSL_simplicity T 2 2 f hst).2
  refine locBal1Two_of_fitting hs (exists_noncomm_of_not_prime hs hp)
    fun X _ _ _ hnonab hFY t ht => ?_
  obtain ⟨e⟩ := hFY
  obtain ⟨-, hiff, -⟩ :=
    ComponentClassification.UnbalancedCatalog.even_linear_two_almost_simple_unbalanced_outcome
      hnonab (LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm hst)
  by_contra hne
  have := ((hiff t ht).mp hne).1
  omega

theorem locBal1Two_U34 (h : LieModel T .PSU 3 2 2) : S3T2A7.LocBal1Two T := by
  have hst : StatedClassicalModel T .PSU 3 2 2 :=
    GH74.statedClassicalModel_of_lieModel (by norm_num) h
  have hs := (ClassicalGroups.Unitary.fam_PSU_simplicity T 3 2 2 hst).2
  have hc : Nat.card T = 62400 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hst).2.1 rfl]
    decide
  refine locBal1Two_of_fitting hs (exists_noncomm_of_not_prime hs (by rw [hc]; norm_num))
    fun X _ _ _ hnonab hFY t ht => ?_
  obtain ⟨e⟩ := hFY
  exact (ComponentClassification.UnbalancedCatalog.even_unitary_almost_simple_odd_core_vanishing
    hnonab (LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm hst)).2 t ht

theorem locBal1Two_Sz8 (h : LieModel T .twistedB2 0 2 3) :
    S3T2A7.LocBal1Two T := by
  have hSz : SuzukiModel T 2 3 := by
    rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  have hs : IsSimpleGroup T := by
    obtain ⟨-, a, ha, K, _, _, hf, hcard, ⟨e⟩⟩ := hSz
    have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hf]; exact hcard
    have := (LieType.Ree.suzuki_simple ha hK).2.2
    exact e.isSimpleGroup
  have hc : Nat.card T = 29120 := by
    rw [GH74.card_of_lieModel_twistedB2 h]
    decide
  refine locBal1Two_of_fitting hs (exists_noncomm_of_not_prime hs (by rw [hc]; norm_num))
    fun X _ _ hsF hnonab hFY t ht => ?_
  obtain ⟨e⟩ := hFY
  have hSzF : SuzukiModel (CFSG.generalizedFitting X) 2 3 := by
    obtain ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩ := hSz
    exact ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.trans e'⟩⟩
  exact (ComponentClassification.UnbalancedGS.catalog_suzuki_almost_simple_odd_core_vanishing
    hsF hnonab hSzF t ht).2.2

theorem locBal1For_even2GH :
    S3T2A7.LocBal1For S3T2A7.Even2GH := by
  intro T _ _ hT
  rcases hT with h | h | h | h
  · refine locBal1Two_linear_two (f := 3) le_rfl h ?_
    rw [GH74.card_of_lieModel_PSL two_ne_zero h,
      show CFSG.Open.ordA (2 - 1) (2 ^ 3) = 504 by decide]
    norm_num
  · refine locBal1Two_linear_two (f := 4) (by norm_num) h ?_
    rw [GH74.card_of_lieModel_PSL two_ne_zero h,
      show CFSG.Open.ordA (2 - 1) (2 ^ 4) = 4080 by decide]
    norm_num
  · exact locBal1Two_U34 h
  · exact locBal1Two_Sz8 h

end CFSG.GH74.Generic.BProg.B3.S3T2A7Loc
