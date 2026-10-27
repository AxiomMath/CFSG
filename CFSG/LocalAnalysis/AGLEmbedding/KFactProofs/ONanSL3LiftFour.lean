module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourLift
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourCover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourInner
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftMain
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem exists_mulEquiv_map_four
    {X X' : Type} [Group X] [Finite X] [Group X'] [Finite X'] {K : Subgroup X} [K.Normal]
    (hK : commutator K = ⊤) {π : X →* X'} (hker : π.ker = twoPart K) {k : Type} [Field k]
    [Finite k] (hk4 : Nat.card k = 4)
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 2 2)
    (e' : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL 3 k))
    (hcenne : Subgroup.center (K.map π) ≠ ⊥) :
    Nonempty (SpecialLinearGroup (Fin 3) k ≃* K.map π) := by
  set K' : Subgroup X' := K.map π with hK'
  let θ : K →* K' := π.subgroupMap K
  have hθ : Function.Surjective θ := π.subgroupMap_surjective K
  have hkerφ : ((QuotientGroup.mk' (Subgroup.center K')).comp θ).ker = Subgroup.center K := by
    ext κ
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_center_subtype_iff κ]
    exact mem_center_map_iff hK hker κ.2
  have hφ : Function.Surjective ((QuotientGroup.mk' (Subgroup.center K')).comp θ) :=
    (QuotientGroup.mk'_surjective _).comp hθ
  let eL : K ⧸ Subgroup.center K ≃* ↥K' ⧸ Subgroup.center ↥K' :=
    (QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hφ)
  have hL : commutator ↥K' = ⊤ := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup K) ⊤ θ
    rw [Subgroup.map_top_of_surjective θ hθ] at h1
    have h2 : (⁅(⊤ : Subgroup K), ⊤⁆ : Subgroup K) = ⊤ := hK
    rw [h2, Subgroup.map_top_of_surjective θ hθ] at h1
    exact (commutator_def ↥K').symm ▸ h1.symm
  have hmodL : StatedClassicalModel (↥K' ⧸ Subgroup.center ↥K') .PSL 3 2 2 :=
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv eL hmod
  have eKfull : (↥K' ⧸ Subgroup.center ↥K') ≃* LinearFlag.projectiveSL 3 k :=
    ((eL.symm.trans e').trans (projectiveSpecialLinearGroupEquivStatedProj 3 k).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k)
  exact exists_mulEquiv_specialLinear_four hk4 hL hmodL eKfull
    (odd_card_center_map hK hker) hcenne

theorem kFactSL3LiftGenFour :
    KFactSL3LiftGenFour := by
  intro X _ _ R K _ z d _ hd4 hK ⟨e⟩ hzc hzK hz3 hΩ hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hqd, h3, h4⟩ := hd4
  simp only at hqd
  subst hqd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpe : q.p ^ q.exponent = 2 ^ 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact h4
  have hp2 : q.p = 2 := by
    have hd : q.p ∣ 2 ^ 2 := hpe ▸ dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hd)
  have hexp : q.exponent = 2 := by
    rw [hp2] at hpe
    exact Nat.pow_right_injective (le_refl 2) hpe
  have hm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, by norm_num, ?_, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField q.p q.exponent))⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  rw [hp2, hexp] at hm
  have hm' := hm
  obtain ⟨hadm, k, _, _, hkcard, ⟨e'⟩⟩ := hm
  have hk4 : Nat.card k = 4 := by rw [hkcard]; norm_num
  let π : X →* X ⧸ twoPart K := QuotientGroup.mk' (twoPart K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = twoPart K := QuotientGroup.ker_mk' _
  refine exists_generating_of_quotient hπ R hK.1 hker hzc hzK hz3 hΩ hrank ?_
  intro R' z' _ hz'c hz'K hz'3 hΩ' hrank'
  have hcenne : Subgroup.center (K.map π) ≠ ⊥ := by
    intro hbot
    have hmem : (⟨z', hz'K⟩ : K.map π) ∈ Subgroup.center (K.map π) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.1 hz'c g.1)
    rw [hbot, Subgroup.mem_bot] at hmem
    have : z' = 1 := congrArg Subtype.val hmem
    rw [this, orderOf_one] at hz'3
    omega
  obtain ⟨ψ⟩ := exists_mulEquiv_map_four hK.1 hker hk4 hm' e' hcenne
  have h3k : 3 ∣ Nat.card k - 1 := by rw [hk4]
  have hσ := SL3Lift.no_ringAut_order_three (p := 2) hkcard (by norm_num : ¬ 3 ∣ 2)
  exact exists_generating_elemAbelian_of_equiv R' (K.map π) z' h3k hσ ψ hz'c hz'3 hΩ' hrank'

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour
