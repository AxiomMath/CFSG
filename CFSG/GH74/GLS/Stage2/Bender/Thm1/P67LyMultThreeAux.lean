module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultLocal
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestMcL
public import CFSG.Sporadic.Recognition.LyonsSimsRecognition

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.LySchreier CFSG.GH74.GLS.Stage12
  CFSG.Sporadic.Recognition.LyonsSims

theorem coverBound_of_simple_quot {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hnp : ¬ (Nat.card Q).Prime) {p m : ℕ}
    (hmult : ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup p (center X) →
      (X ⧸ center X ≃* Q) → Nat.card (center X) ∣ m) : CoverBound Q p m := by
  intro E _ _ hE q hq hker hpg
  obtain ⟨hQ, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (exists_noncomm_of_simple hnp)
  have hQE : IsQuasisimple E :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hE q hq hker).mpr hQ
  have hcen : center E = q.ker := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hE q hq hker, hZ, MonoidHom.comap_bot]
  have e : E ⧸ center E ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have h := hmult E hQE (hcen ▸ hpg) e
  rwa [hcen] at h

theorem coverBound_of_equiv_mcl
    {Q : Type} [Group Q] (e : Q ≃* NativeSporadic.McL) : CoverBound Q 3 3 := by
  have hfinM : Finite NativeSporadic.McL := (CFSG.Sporadic.McL.fam_mcl_simplicity).1
  have hfin : Finite Q := Finite.of_equiv _ e.symm.toEquiv
  have hs : IsSimpleGroup Q :=
    @MulEquiv.isSimpleGroup Q _ NativeSporadic.McL _ CFSG.Sporadic.McL.isSimpleGroup_McL e
  have hcard : Nat.card Q = 898128000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  refine coverBound_of_simple_quot (Q := Q) (by rw [hcard]; norm_num) ?_
  intro X _ _ hX hp eX
  exact CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.card_center_dvd_three_of_McL
    hX hp (eX.trans e)

theorem oneClassDoubleCover_of_ly
    {T : Type} [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.Ly)) : OneClassDoubleCover T 11 := by
  obtain ⟨eT⟩ := hT
  have hcard : Nat.card T = 51765179004000000 := by
    rw [Nat.card_congr eT.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  have hfin : Finite T := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hs : IsSimpleGroup T :=
    @MulEquiv.isSimpleGroup T _ NativeSporadic.Ly _ CFSG.Sporadic.Ly.isSimpleGroup_Ly eT
  have hnab : ∃ a b : T, a * b ≠ b * a :=
    exists_noncomm_of_simple (by rw [hcard]; norm_num)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 (by rw [hcard]; norm_num)
  obtain ⟨hq, hc, ⟨e⟩⟩ := involution_centralizers_quasisimple ⟨eT⟩ t ht
  have hzc : (⟨t, mem_centralizer_singleton_self t⟩ : ↥(centralizer ({t} : Set T))) ∈
      center ↥(centralizer ({t} : Set T)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp y.2)
  have hcfin : Finite (center ↥(centralizer ({t} : Set T))) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hZ : center ↥(centralizer ({t} : Set T)) =
      zpowers (⟨t, mem_centralizer_singleton_self t⟩ : ↥(centralizer ({t} : Set T))) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hzc) ?_
    rw [hc, Nat.card_zpowers, Subgroup.orderOf_mk, ht]
  exact oneClassDoubleCover_of_blueprint hs hnab ht hq.1 hZ ⟨e⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult
