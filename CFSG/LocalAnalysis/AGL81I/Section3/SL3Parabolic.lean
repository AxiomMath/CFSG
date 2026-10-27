module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Par
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient
open CFSG.ABGLocalTools
open Matrix

section Transport

variable {A A' : Type} [Group A] [Group A'] {p : ℕ}

theorem isMaxParabolicP_map_iff (f : A ≃* A') {K P : Subgroup A} :
    IsMaxParabolicP p K P ↔
      IsMaxParabolicP p (K.map f.toMonoidHom) (P.map f.toMonoidHom) := by
  refine ⟨CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.isMaxParabolicP_map f p, fun h => ?_⟩
  have h' := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.isMaxParabolicP_map f.symm p h
  rwa [CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.map_map_symm,
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.map_map_symm] at h'

theorem isMaxParabolicP_of_mulEquiv (e : A ≃* A') (P : Subgroup A) :
    IsMaxParabolicP p (⊤ : Subgroup A) P ↔
      IsMaxParabolicP p (⊤ : Subgroup A') (P.map e.toMonoidHom) := by
  have h := isMaxParabolicP_map_iff (p := p) e (K := ⊤) (P := P)
  rwa [Subgroup.map_top_of_surjective _ e.surjective] at h

end Transport

section Kernel

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

omit [Finite F] in
theorem proj_ker_le_center (n : ℕ) :
    (proj n F).ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
  rw [ker_proj]
  exact scalars_le_center n F

theorem coprime_card_proj_ker (n : ℕ) (hn : 1 ≤ n) (hF : Nat.card F = p) :
    Nat.Coprime p (Nat.card (proj n F).ker) := by
  rw [ker_proj]
  have hZ : Nat.card (scalars n F) ∣ Nat.card F - 1 := card_scalars_dvd hn
  have hp1 : Nat.Coprime p (Nat.card F - 1) := by
    rw [hF]
    exact (Nat.coprime_self_sub_right (Fact.out : p.Prime).one_le).mpr
      (Nat.coprime_one_right p)
  exact Nat.Coprime.coprime_dvd_right hZ hp1

end Kernel

section Bridge

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isParabolicP_top_iff_isParabolicGrp (Q : Subgroup G) :
    IsParabolicP p (⊤ : Subgroup G) Q ↔ IsParabolicGrp p Q := by
  constructor
  · rintro ⟨-, U, hU, hUQ⟩
    have hUidx : ¬ p ∣ U.index := by
      have h := (isSylowOf_iff (P := U) (K := (⊤ : Subgroup G))).mp hU
      rw [Subgroup.relIndex_top_right] at h
      exact h.2.2
    refine ⟨hU.isPGroup.toSylow hUidx, ?_⟩
    rw [IsPGroup.toSylow_coe]
    simpa using hUQ
  · rintro ⟨T, hT⟩
    refine ⟨le_top, (T : Subgroup G), ?_, ?_⟩
    · rw [isSylowOf_iff]
      exact ⟨le_top, T.isPGroup', by
        rw [Subgroup.relIndex_top_right]
        exact T.not_dvd_index⟩
    · simpa using hT

theorem isMaxParabolicP_top_iff_isMaxParabolicGrp (P : Subgroup G) :
    IsMaxParabolicP p (⊤ : Subgroup G) P ↔ IsMaxParabolicGrp p P := by
  simp only [IsMaxParabolicP, IsMaxParabolicGrp, isParabolicP_top_iff_isParabolicGrp]

omit [Finite G] [Fact p.Prime] in
theorem isMaxParabolicGrp_iff_mem_maximalParabolics (Q : Subgroup G) :
    IsMaxParabolicGrp p Q ↔ Q ∈ maximalParabolics G p := by
  constructor
  · rintro ⟨⟨S, hS⟩, hne, hmax⟩
    refine ⟨⟨hne, fun R hQR => ?_⟩, _, ⟨S, rfl⟩, hS⟩
    by_contra hRne
    exact absurd (hmax R ⟨S, hS.trans hQR.le⟩ hRne hQR.le) hQR.ne'
  · rintro ⟨⟨hne, hco⟩, B₀, ⟨S, hSB⟩, hBQ⟩
    refine ⟨⟨S, hSB.trans_le hBQ⟩, hne, fun R _ hRne hQR => ?_⟩
    by_contra hRQ
    exact hRne (hco _ (lt_of_le_of_ne hQR fun h => hRQ h.symm))

end Bridge

section SL3

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem isMaxParabolicP_sl3_iff (hF : Nat.card F = p)
    (P : Subgroup (SpecialLinearGroup (Fin 3) F)) :
    IsMaxParabolicP p (⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)) P ↔
      ∃ W : Submodule F (Fin 3 → F), ⊥ < W ∧ W < ⊤ ∧
        P = (projStabilizer W).comap (proj 3 F) := by
  classical
  have hchar : CharP F p :=
    @charP_of_card_eq_prime F _ (Fintype.ofFinite F) p _ (by
      rw [← @Nat.card_eq_fintype_card F (Fintype.ofFinite F)]
      exact hF)
  have hmaxpar := @maximal_parabolics F _ 3 _ p _ hchar (by norm_num)
  have hker_center : (proj 3 F).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin 3) F) := proj_ker_le_center 3
  have hker_coprime : Nat.Coprime p (Nat.card (proj 3 F).ker) :=
    coprime_card_proj_ker 3 (by norm_num) hF
  constructor
  · intro hP
    have hmaxP : IsMaxParabolicGrp p P :=
      (isMaxParabolicP_top_iff_isMaxParabolicGrp P).mp hP
    obtain ⟨S, hS⟩ := hmaxP.1
    have hkerS : (proj 3 F).ker ≤
        Subgroup.normalizer (((S : Subgroup (SpecialLinearGroup (Fin 3) F))) :
          Set (SpecialLinearGroup (Fin 3) F)) := by
      rw [ker_proj]
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hzx : z * x * z⁻¹ = x := by
        rw [← Subgroup.mem_center_iff.mp (scalars_le_center 3 F hz) x, mul_assoc,
          mul_inv_cancel, mul_one]
      rw [hzx]
    have hkerP : (proj 3 F).ker ≤ P := hkerS.trans hS
    have hmaxQ : IsMaxParabolicGrp p (P.map (proj 3 F)) :=
      (isMaxParabolicGrp_map_iff (proj 3 F) (proj_surjective 3 F) hker_center hker_coprime
        hkerP).mpr hmaxP
    have hmem : P.map (proj 3 F) ∈ maximalParabolics (projectiveSL 3 F) p :=
      (isMaxParabolicGrp_iff_mem_maximalParabolics _).mp hmaxQ
    rw [hmaxpar.1] at hmem
    obtain ⟨W, ⟨h0, htop⟩, hW⟩ := hmem
    refine ⟨W, h0, htop, ?_⟩
    rw [hW, Subgroup.comap_map_eq, sup_eq_left.mpr hkerP]
  · rintro ⟨W, h0, htop, rfl⟩
    have hmem : projStabilizer W ∈ maximalParabolics (projectiveSL 3 F) p := by
      rw [hmaxpar.1]
      exact ⟨W, ⟨h0, htop⟩, rfl⟩
    have hmaxQ : IsMaxParabolicGrp p (projStabilizer W) :=
      (isMaxParabolicGrp_iff_mem_maximalParabolics _).mpr hmem
    have hker_le : (proj 3 F).ker ≤ (projStabilizer W).comap (proj 3 F) := by
      intro x hx
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact one_mem _
    have hmaxP : IsMaxParabolicGrp p ((projStabilizer W).comap (proj 3 F)) := by
      refine (isMaxParabolicGrp_map_iff (proj 3 F) (proj_surjective 3 F) hker_center
        hker_coprime hker_le).mp ?_
      rwa [Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 F)]
    exact (isMaxParabolicP_top_iff_isMaxParabolicGrp _).mpr hmaxP

end SL3

end CFSG.LocalAnalysis.AGL81I.Section3
