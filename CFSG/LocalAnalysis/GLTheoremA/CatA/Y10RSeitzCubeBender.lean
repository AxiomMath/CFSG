module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeCore
public import CFSG.LieType.ChevTwo.OppositeFixedExcBender
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.ClassicalRankOne
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import Certificates.Certificate43
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.Models.BenderSuzuki
import CFSG.StronglyEmbedded.MatrixGroups.SzModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega (eq_one_of_mem_of_mem
  exists_smul_eq mem_smul_iff mem_conj_smul_iff)

theorem seitzTwoGen_of_stronglyEmbedded {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hX : ∀ T : Sylow 2 X, fusionStronglyEmbedded (Subgroup.normalizer ((T : Subgroup X) : Set X)) ∧
      Nat.card (Sylow 2 X) = Nat.card (T : Subgroup X) + 1) :
    SeitzTwoGen X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro q hq hq2 E hE ⟨U, hU0, hU2, hUinv⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨T, hUT⟩ := hU2.exists_le_sylow
  have huniq : ∀ P : Sylow 2 X, U ≤ P → P = T := by
    intro P hUP
    by_contra hPT
    obtain ⟨u, hu, hu1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hU0
    exact hu1 (eq_one_of_mem_of_mem (hX T).1 hPT (hUT hu) (hUP hu))
  have hTmap : ∀ α ∈ E, (T : Subgroup X).map α.toMonoidHom = (T : Subgroup X) := by
    intro α hα
    have hαT : α • T = T := huniq _ fun u hu => by
      rw [mem_smul_iff]
      exact hUT (hUinv α⁻¹ (E.inv_mem hα) u hu)
    have h := congrArg (fun P : Sylow 2 X => (P : Subgroup X)) hαT
    simpa only [CFSG.LocalAnalysis.ComponentInitial.coe_mulAut_smul_sylow'] using h
  have hTfix : ∀ α ∈ E, α • T = T := fun α hα => Sylow.ext (by
    rw [CFSG.LocalAnalysis.ComponentInitial.coe_mulAut_smul_sylow']
    exact hTmap α hα)
  obtain ⟨T', hT'fix, hT'T⟩ : ∃ T' : Sylow 2 X, (∀ α ∈ E, α • T' = T') ∧ T' ≠ T := by
    by_contra hno
    push Not at hno
    have hfix : MulAction.fixedPoints E (Sylow 2 X) = {T} := by
      ext P
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro hP
        exact hno P fun α hα => hP ⟨α, hα⟩
      · rintro rfl α
        exact hTfix α α.2
    have hmod := hE.card_modEq_card_fixedPoints (Sylow 2 X)
    rw [hfix, Nat.card_unique (α := ↥({T} : Set (Sylow 2 X))), (hX T).2] at hmod
    have hdvd : q ∣ Nat.card (T : Subgroup X) := by
      have := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
      rwa [Nat.add_sub_cancel] at this
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
    rw [hk] at hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))
  have hT'map : ∀ α ∈ E, (T' : Subgroup X).map α.toMonoidHom = (T' : Subgroup X) := by
    intro α hα
    have h := congrArg (fun P : Sylow 2 X => (P : Subgroup X)) (hT'fix α hα)
    simpa only [CFSG.LocalAnalysis.ComponentInitial.coe_mulAut_smul_sylow'] using h
  have hPle : ∀ P : Sylow 2 X, (P : Subgroup X) ≤ (T : Subgroup X) ⊔ (T' : Subgroup X) := by
    intro P
    by_cases hPT : P = T
    · rw [hPT]; exact le_sup_left
    obtain ⟨r, hr, hrP⟩ := exists_smul_eq (hX T).1 (hX T).2 hT'T hPT
    rw [← hrP]
    intro x hx
    rw [mem_conj_smul_iff] at hx
    have hx' : x = r * (r⁻¹ * x * r) * r⁻¹ := by group
    rw [hx']
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hx))
      (Subgroup.mem_sup_left ((T : Subgroup X).inv_mem hr))
  have hHnorm : ((T : Subgroup X) ⊔ (T' : Subgroup X)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hmap : ((T : Subgroup X) ⊔ (T' : Subgroup X)).map (MulAut.conj g).toMonoidHom ≤
        (T : Subgroup X) ⊔ (T' : Subgroup X) := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · have h := hPle (MulAut.conj g • T)
        rwa [CFSG.LocalAnalysis.ComponentInitial.coe_mulAut_smul_sylow'] at h
      · have h := hPle (MulAut.conj g • T')
        rwa [CFSG.LocalAnalysis.ComponentInitial.coe_mulAut_smul_sylow'] at h
    have := hmap (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hn)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
  have htop : (T : Subgroup X) ⊔ (T' : Subgroup X) = ⊤ := by
    haveI := hHnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((T : Subgroup X) ⊔ (T' : Subgroup X)) with
      h | h
    · exfalso
      have hTbot : (T : Subgroup X) = ⊥ := le_bot_iff.mp (h ▸ le_sup_left)
      have h2 : 2 ∣ Nat.card X :=
        (hX T).1.2.1.two_dvd.trans (Subgroup.card_subgroup_dvd_card _)
      exact Sylow.ne_bot_of_dvd_card T h2 hTbot
    · exact h
  exact ⟨(T : Subgroup X), (T' : Subgroup X), T.isPGroup', T'.isPGroup',
    fun φ hφ u hu => by
      have hmem := Subgroup.mem_map_of_mem φ.toMonoidHom hu
      rwa [hTmap φ hφ] at hmem,
    fun φ hφ u hu => by
      have hmem := Subgroup.mem_map_of_mem φ.toMonoidHom hu
      rwa [hT'map φ hφ] at hmem,
    htop⟩

theorem seitzTwoGen_of_fusionIsBenderGroup {X : Type} [Group X]
    [Finite X] (hX : fusionIsBenderGroup X) : SeitzTwoGen X :=
  seitzTwoGen_of_stronglyEmbedded
    (CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hX) fun T => by
    obtain ⟨D, h⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hX T
    exact ⟨h.se, h.card⟩

theorem seitzTwoGen_of_statedPSL_two {S : Type} [Group S]
    [Finite S] {f : ℕ} (h : StatedClassicalModel S .PSL 2 2 f) : SeitzTwoGen S :=
  seitzTwoGen_of_fusionIsBenderGroup
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.fusionIsBenderGroup_of_statedPSL_two h)

theorem seitzTwoGen_of_statedPSU_three {S : Type} [Group S]
    [Finite S] {f : ℕ} (h : StatedClassicalModel S .PSU 3 2 f) : SeitzTwoGen S :=
  seitzTwoGen_of_fusionIsBenderGroup
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.fusionIsBenderGroup_of_statedPSU_three h)

theorem seitzTwoGen_of_valid_suzuki {S : Type} [Group S]
    [Finite S] (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩) : SeitzTwoGen S := by
  have hm : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine seitzTwoGen_of_fusionIsBenderGroup (Or.inr (Or.inr ⟨m, hm, ⟨?_⟩⟩))
  exact (e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).trans
    (MulEquiv.subgroupCongr ((CFSG.Models.benderSzModel_eq_sz m).symm.trans
      (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup m))).symm

end CFSG.LocalAnalysis.GLTheoremA.Y10F
