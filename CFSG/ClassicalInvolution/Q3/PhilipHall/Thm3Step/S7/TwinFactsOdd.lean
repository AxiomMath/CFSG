module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoInputs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3.Rows
public import CFSG.LieType.SeitzGeneration.OuterSpData

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_symplectic_inner_involution_full_centralizer_odd_core)

theorem conj_injective_of_center_eq_bot {P : Type} [Group P] (hZ : Subgroup.center P = ⊥) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro x
  have h := congrArg (fun α : MulAut P => α x) ((MonoidHom.mem_ker).mp hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc x * g = g * x * g⁻¹ * g := by rw [h]
    _ = g * x := by group

theorem oddCore_centralizer_eq_bot_of_inner {P : Type} [Group P] (hZ : Subgroup.center P = ⊥)
    (s : P)
    (h : classicalInvolutionOddCore ↥((MulAut.conj : P →* MulAut P).range ⊓
      Subgroup.centralizer ({MulAut.conj s} : Set (MulAut P))) = ⊥) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({s} : Set P)) = ⊥ := by
  have hinj := conj_injective_of_center_eq_bot hZ
  have hmap : (Subgroup.centralizer ({s} : Set P)).map (MulAut.conj : P →* MulAut P) =
      (MulAut.conj : P →* MulAut P).range ⊓
        Subgroup.centralizer ({MulAut.conj s} : Set (MulAut P)) := by
    ext α
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
      exact ⟨⟨g, rfl⟩, by rw [← map_mul, ← map_mul, hg]⟩
    · rintro ⟨⟨g, rfl⟩, hα⟩
      refine ⟨g, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hinj (by rw [map_mul, map_mul, hα])
  exact S3.oddCore_eq_bot_of_mulEquiv
    ((Subgroup.equivMapOfInjective _ _ hinj).trans (MulEquiv.subgroupCongr hmap)) h

theorem twinOddCore_sp {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1)
    (z : X) (hz : orderOf z = 2) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have hZ : Subgroup.center (StatedProj (StatedSp 3 K)) = ⊥ :=
    CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (by norm_num)
  refine S3.oddCore_centralizer_eq_bot_of_mulEquiv e (oddCore_centralizer_eq_bot_of_inner hZ _ ?_)
  have ht : orderOf (MulAut.conj (e z)) = 2 := by
    rw [orderOf_injective _ (conj_injective_of_center_eq_bot hZ), MulEquiv.orderOf_eq, hz]
  exact even_symplectic_inner_involution_full_centralizer_odd_core (r := 3) (f := 1) (by norm_num)
    le_rfl hK _ le_rfl ⟨e z, rfl⟩ ht

theorem twinOddCore_omega {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X .POmegaPlus 4 2 1) (z : X) (hz : orderOf z = 2) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  obtain ⟨e⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT hX
  have hZ := CFSG.EvenSmallLie.OmegaEight.center_omegaT
  refine S3.oddCore_centralizer_eq_bot_of_mulEquiv e (oddCore_centralizer_eq_bot_of_inner hZ _ ?_)
  have ht : orderOf (MulAut.conj (e z)) = 2 := by
    rw [orderOf_injective _ (conj_injective_of_center_eq_bot hZ), MulEquiv.orderOf_eq, hz]
  exact CFSG.EvenSmallLie.OmegaEight.fullOddCore_omegaT _ le_rfl _ ⟨e z, rfl⟩ ht

theorem twinOddCore_proved : TwinOddCore := by
  intro X _ _ hX z hz
  rcases hX with hX | hX
  · exact twinOddCore_sp hX z hz
  · exact twinOddCore_omega hX z hz

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
