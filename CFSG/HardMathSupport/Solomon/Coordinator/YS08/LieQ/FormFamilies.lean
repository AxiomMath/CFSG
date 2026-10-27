module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.FormRigid
public import CFSG.LieType.ChevTwo.OppCl.FormsEA
public import CFSG.LieType.ChevTwo.OppCl.AutLifts
public import CFSG.LieType.ChevTwo.OppCl.Toolkit
import CFSG.LieType.ChevTwo.OppCl.FormsSplitBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo.OppCl

section Families

variable (F : Type) [Field F] [Finite F] [CharP F 2]

theorem radRigid_PSp (r : ℕ) (hr : 2 ≤ r) (hF : 4 ≤ Nat.card F ∨ 3 ≤ r) :
    RadRigid 2 (StatedProj (StatedSp r F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hE1, hE2⟩ := ea_Sp r F
  have hdim : 4 ≤ Module.finrank F (Fin r ⊕ Fin r → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine radRigid_of_rigid (H := StatedSp r F)
    ((StatedScalars (Fin r ⊕ Fin r) F).subgroupOf (StatedSp r F)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime 2 _) (SemiIso (spForm r F)) (natRep (StatedSp r F))
    (natRep_injective _) (fun Q => isoFlag (spForm r F) (natRep (StatedSp r F)) Q)
    (fun Q _ => isoFlag_zero _ _ Q) (fun Q _ => ⟨_, isoFlag_top _ _ Q⟩)
    (fun Q _ => normalizer_le_flagStab_isoFlag _ _ (isIsometric_natRep_statedSp r F) Q)
    (fun Q hQ => le_flagKernel_isoFlag _ _ 2 (isIsometric_natRep_statedSp r F) Q hQ) ?_
    (fun p hp hp2 => rigidProp_form (spForm r F) (fun _ => True)
      (spForm r F).IsTotallyIsotropic (natRep (StatedSp r F)) (SemiIso (spForm r F)) _ p hp hp2
      (fun c => rfl) hdim (fun U hU => hU) (fun U _ v _ => trivial) (natRep_injective _) hE1
      (Or.inl hE2) (hflag_iso (spForm r F) (natRep (StatedSp r F))) (fun g h => h))
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  refine autLift_of_induced _ (semiIso_one _) (fun _ _ => semiIso_mul _)
    (fun _ => semiIso_inv _) p R hR ?_
  rcases le_or_gt 3 r with h3 | h3
  · exact induced_PSp F p hp2 r h3 R hR
  · obtain rfl : r = 2 := by omega
    exact induced_PSp_two F p hp2 (hF.resolve_right (by omega)) R hR

theorem radRigid_PSU (f : ℕ) (hK : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 4 ≤ n) :
    RadRigid 2 (StatedProj (StatedSU n (2 ^ f) F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hE1, hE2⟩ := ea_SU F f hK n
  have hdim : 4 ≤ Module.finrank F (Fin n → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hn
  refine radRigid_of_rigid (H := StatedSU n (2 ^ f) F)
    ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (2 ^ f) F)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime 2 _) (SemiIso (unitaryForm 2 f hK n))
    (natRep (StatedSU n (2 ^ f) F)) (natRep_injective _)
    (fun Q => isoFlag (unitaryForm 2 f hK n) (natRep (StatedSU n (2 ^ f) F)) Q)
    (fun Q _ => isoFlag_zero _ _ Q) (fun Q _ => ⟨_, isoFlag_top _ _ Q⟩)
    (fun Q _ => normalizer_le_flagStab_isoFlag _ _ (isIsometric_natRep_statedSU hK n) Q)
    (fun Q hQ => le_flagKernel_isoFlag _ _ 2 (isIsometric_natRep_statedSU hK n) Q hQ) ?_
    (fun p hp hp2 => rigidProp_form (unitaryForm 2 f hK n)
      (fun v => (unitaryForm 2 f hK n).β v v = 0) (unitaryForm 2 f hK n).IsTotallyIsotropic
      (natRep (StatedSU n (2 ^ f) F)) (SemiIso (unitaryForm 2 f hK n)) _ p hp hp2
      (fun c => unitaryInvolution_involutive hK c) hdim (fun U hU => hU)
      (fun U hU v hv => hU hv v hv) (natRep_injective _) hE1 (Or.inl hE2)
      (hflag_iso _ _) (fun g h => h))
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  exact autLift_of_induced _ (semiIso_one _) (fun _ _ => semiIso_mul _) (fun _ => semiIso_inv _)
    p R hR (induced_PSU F p hp2 f hK n (by omega) (Or.inr hn) R hR)

theorem radRigid_POmegaPlus (n : ℕ) (hn : 5 ≤ n) :
    RadRigid 2 (StatedProj (StatedOmega (StatedQuadPlus n F))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : ∀ (h : StatedOmega (StatedQuadPlus n F)) (v : Fin n ⊕ Fin n → F),
      (quadPlusForm n F).Q (natRep (StatedOmega (StatedQuadPlus n F)) h v) =
        (quadPlusForm n F).Q v := fun h v => by
    rw [natRep_apply]
    exact orthGroup_preserves (quadPlusForm n F).Q (statedOmega_le_orthGroup _ h.2) v
  have hstar : NoQuotientReflection (quadPlusForm n F)
      (natRep (StatedOmega (StatedQuadPlus n F))) := fun h Z hZ a ha hQa => by
    simp only [natRep_apply]
    exact not_reflection_on_quotient_of_mem_statedOmega (quadPlusForm n F) h.2 hZ ha hQa
  have hι : 5 ≤ Fintype.card (Fin n ⊕ Fin n) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨-, hE1, -⟩ := ea_Omega F (quadPlusForm n F) hι
  have hdim : 6 ≤ Module.finrank F (Fin n ⊕ Fin n → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine radRigid_of_rigid (H := StatedOmega (StatedQuadPlus n F))
    ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedOmega (StatedQuadPlus n F)))
    (statedProj_kernel_central _) (statedProj_kernel_coprime 2 _)
    (fun g => g ∈ semilinGroup F (Fin n ⊕ Fin n → F) ∧ SemiIsoQ (quadPlusForm n F) g)
    (natRep (StatedOmega (StatedQuadPlus n F))) (natRep_injective _)
    (fun Q => singFlag (quadPlusForm n F) (natRep (StatedOmega (StatedQuadPlus n F))) Q)
    (fun Q _ => singFlag_zero _ _ Q) (fun Q _ => ⟨_, singFlag_top _ _ Q⟩)
    (fun Q _ => normalizer_le_flagStab_singFlag hQ Q)
    (fun Q hQ2 => le_flagKernel_singFlag 2 hQ hstar Q hQ2) ?_
    (fun p hp hp2 => rigidProp_form (quadPlusForm n F).polar
      (fun v => (quadPlusForm n F).Q v = 0) (quadPlusForm n F).IsTotallySingular
      (natRep (StatedOmega (StatedQuadPlus n F))) _ _ p hp hp2
      (fun c => by rw [(quadPlusForm n F).polar_σ]; rfl) (by omega)
      (fun U hU => hU.isTotallyIsotropic) (fun U hU v hv => hU v hv) (natRep_injective _) hE1
      (Or.inr hdim) (hflag_sing (quadPlusForm n F) _)
      (fun g hg => FS.semiIso_polar (quadPlusForm n F) hg.1 hg.2))
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  refine autLift_of_induced _ ⟨one_mem _, semiIsoQ_one _⟩
    (fun a b ha hb => ⟨mul_mem ha.1 hb.1, semiIsoQ_mul _ ha.2 hb.2⟩)
    (fun a ha => ⟨inv_mem ha.1, semiIsoQ_inv _ ha.2⟩) p R hR ?_
  intro α hα
  obtain ⟨s, hs, hsQ, hind⟩ := induced_POmegaPlus F p hp2 n hn R hR α hα
  exact ⟨s, hs, ⟨hs, hsQ⟩, hind⟩

theorem radRigid_POmegaMinus (n : ℕ) (hn : 4 ≤ n) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    RadRigid 2 (StatedProj (StatedOmega (StatedQuadMinus n F b c))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : ∀ (h : StatedOmega (StatedQuadMinus n F b c))
      (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
      (quadMinusForm n F b c hirr).Q (natRep (StatedOmega (StatedQuadMinus n F b c)) h v) =
        (quadMinusForm n F b c hirr).Q v := fun h v => by
    rw [natRep_apply]
    exact orthGroup_preserves (quadMinusForm n F b c hirr).Q (statedOmega_le_orthGroup _ h.2) v
  have hstar : NoQuotientReflection (quadMinusForm n F b c hirr)
      (natRep (StatedOmega (StatedQuadMinus n F b c))) := fun h Z hZ a ha hQa => by
    simp only [natRep_apply]
    exact not_reflection_on_quotient_of_mem_statedOmega (quadMinusForm n F b c hirr) h.2 hZ ha hQa
  have hι : 5 ≤ Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨-, hE1, -⟩ := ea_Omega F (quadMinusForm n F b c hirr) hι
  have hdim : 6 ≤ Module.finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  refine radRigid_of_rigid (H := StatedOmega (StatedQuadMinus n F b c))
    ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus n F b c)))
    (statedProj_kernel_central _) (statedProj_kernel_coprime 2 _)
    (fun g => g ∈ semilinGroup F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ∧
      SemiIsoQ (quadMinusForm n F b c hirr) g)
    (natRep (StatedOmega (StatedQuadMinus n F b c))) (natRep_injective _)
    (fun Q => singFlag (quadMinusForm n F b c hirr)
      (natRep (StatedOmega (StatedQuadMinus n F b c))) Q)
    (fun Q _ => singFlag_zero _ _ Q) (fun Q _ => ⟨_, singFlag_top _ _ Q⟩)
    (fun Q _ => normalizer_le_flagStab_singFlag hQ Q)
    (fun Q hQ2 => le_flagKernel_singFlag 2 hQ hstar Q hQ2) ?_
    (fun p hp hp2 => rigidProp_form (quadMinusForm n F b c hirr).polar
      (fun v => (quadMinusForm n F b c hirr).Q v = 0) (quadMinusForm n F b c hirr).IsTotallySingular
      (natRep (StatedOmega (StatedQuadMinus n F b c))) _ _ p hp hp2
      (fun c' => by rw [(quadMinusForm n F b c hirr).polar_σ]; rfl) (by omega)
      (fun U hU => hU.isTotallyIsotropic) (fun U hU v hv => hU v hv) (natRep_injective _) hE1
      (Or.inr hdim) (hflag_sing (quadMinusForm n F b c hirr) _)
      (fun g hg => FS.semiIso_polar (quadMinusForm n F b c hirr) hg.1 hg.2))
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  refine autLift_of_induced _ ⟨one_mem _, semiIsoQ_one _⟩
    (fun a b ha hb => ⟨mul_mem ha.1 hb.1, semiIsoQ_mul _ ha.2 hb.2⟩)
    (fun a ha => ⟨inv_mem ha.1, semiIsoQ_inv _ ha.2⟩) p R hR ?_
  intro α hα
  obtain ⟨s, hs, hsQ, hind⟩ := induced_POmegaMinus F p hp2 n hn b c hirr R hR α hα
  exact ⟨s, hs, ⟨hs, hsQ⟩, hind⟩

end Families

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
