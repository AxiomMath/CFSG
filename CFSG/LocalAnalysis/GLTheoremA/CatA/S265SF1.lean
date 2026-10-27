module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace SF

variable {Ω : Type} [Group Ω]

theorem nonempty_centerQuot_equiv_pSimple {p : ℕ} {K : Subgroup Ω}
    (hK : CFSG.Open.IsQuasisimple ↥K) [Nontrivial (PSimple p K)] :
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* PSimple p K) := by
  haveI : Group.IsPerfect ↥K := ⟨hK.1⟩
  have hne : GLAPPrimeCore p ↥K ≠ ⊤ := by
    intro htop
    have h1 : ∀ y : PQuot p K, y = 1 := fun y => by
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
      exact (QuotientGroup.eq_one_iff k).2 (by rw [htop]; exact Subgroup.mem_top k)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PSimple p K)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [h1 a, h1 b])
  exact ⟨S172A.pSimpleEquivCenterQuot p
    (le_center_of_normal_of_isQuasisimple hK inferInstance hne)⟩

theorem exists_psl_model {p : ℕ} {K : Subgroup Ω} (hK : CFSG.Open.IsQuasisimple ↥K)
    (h : catalogIs (PSimple p K) (tyFLin p)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), p ∣ Nat.card F - 1 ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* LinearFlag.projectiveSL p F) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases i with _ | _ | ⟨⟨l, hv⟩⟩ | _
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases l
    case A r q =>
      obtain ⟨hr, hq2, hpq⟩ := (hi : r + 1 = p ∧ q.p = 2 ∧ p ∣ q.card - 1)
      subst hr
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      have hr1 : 1 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
      let e₀ := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)
      haveI : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1))
          (GaloisField q.p q.exponent)) := CFSG.LinearGroups.linear_projective_nontrivial (by omega)
      haveI : Nontrivial (PSimple (r + 1) K) := e₀.toEquiv.nontrivial
      obtain ⟨θ⟩ := nonempty_centerQuot_equiv_pSimple (p := r + 1) hK
      refine ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, CharP.congr q.p hq2, ?_,
        ⟨θ.trans (e₀.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))⟩⟩
      rwa [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
    all_goals exact (hi : False).elim
  · exact (hi : False).elim

theorem exists_psu_model {p : ℕ} {K : Subgroup Ω} (hK : CFSG.Open.IsQuasisimple ↥K)
    (h : catalogIs (PSimple p K) (tyFUni p)) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (hF : UnitaryFieldData 2 m F), p ∣ 2 ^ m + 1 ∧
      3 ≤ p ∧ (p, 2 ^ m) ≠ (3, 2) ∧ Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
        primeFormP hF ((1 : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases i with _ | _ | ⟨⟨l, hv⟩⟩ | _
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases l
    case twistedA r q =>
      obtain ⟨hr, hq2, hpq⟩ := (hi : r + 1 = p ∧ q.p = 2 ∧ p ∣ q.card + 1)
      subst hr
      have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      haveI : Nontrivial (PSimple (r + 1) K) :=
        (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _ hM).1
      obtain ⟨⟨-, hm, hn3, hq⟩, F, _, _, hFc, ⟨eT⟩⟩ := hM
      rw [hq2] at hFc hq eT
      rw [TauCeti.PrimePower.card_def, hq2] at hpq
      have hFd : UnitaryFieldData 2 q.exponent F :=
        ⟨Nat.prime_two, hm, by rw [hFc, ← pow_mul, mul_comm]⟩
      obtain ⟨θ⟩ := nonempty_centerQuot_equiv_pSimple (p := r + 1) hK
      exact ⟨q.exponent, F, inferInstance, hFd, hpq, hn3, hq,
        ⟨θ.trans (eT.trans (CFSG.StandardType.InndiagSU.projEquiv hFd (by omega)))⟩⟩
    all_goals exact (hi : False).elim
  · exact (hi : False).elim

variable [Finite Ω]

theorem pow_self_le_card_of_tyFLin {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL p S B T x D K) (hp5 : 5 ≤ p) (hF : catalogIs (PSimple p K) (tyFLin p)) :
    p ^ p ≤ Nat.card B := by
  obtain ⟨-, -, -, -, -, hKcomp, -⟩ := h.cfg.std
  obtain ⟨F, _, _, _, hpF, ⟨θ⟩⟩ := exists_psl_model hKcomp.2.2 hF
  have hT := CFSG.StandardType.TypeA.ggTorusLift_sub_two h.cfg.prime hpF (by omega)
    (CFSG.StandardType.TypeA.slHasSections_of_five_le hp5)
  have h1 := pow_add_two_le_card_of_torusLift h θ hT
  rwa [Nat.sub_add_cancel (by omega : 2 ≤ p)] at h1

theorem pow_sub_one_le_card_of_tyFUni
    {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL p S B T x D K) (hF : catalogIs (PSimple p K) (tyFUni p)) :
    p ^ (p - 1) ≤ Nat.card B := by
  obtain ⟨-, -, -, -, -, hKcomp, -⟩ := h.cfg.std
  obtain ⟨m, F, _, hFd, hpm, hp3, hq, ⟨θ⟩⟩ := exists_psu_model hKcomp.2.2 hF
  haveI := hFd.finite
  have hT := CFSG.StandardType.ggTorusLift_unitary (K := F)
    (by rw [hFd.card, ← pow_mul, mul_comm]) hFd.one_le hp3 hq h.cfg.prime hpm
  have h1 := pow_add_two_le_card_of_torusLift h
    (θ.trans (CFSG.StandardType.InndiagSU.projEquiv hFd (by omega)).symm) hT
  have hr : CFSG.StandardType.ggUnitaryTorusRank p p + 2 = p - 1 := by
    simp only [CFSG.StandardType.ggUnitaryTorusRank, dvd_refl, if_true]
    omega
  rwa [hr] at h1

end SF

end CFSG.LocalAnalysis.GLTheoremA.S265

end
