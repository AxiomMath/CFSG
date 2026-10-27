module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY1b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section U20

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem oddCore_Ct_le_gamma2 (hc : P23Cfg n Y R S t K' W u e g) :
    oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤
      gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (Subgroup.centralizer ({t} : Set Y)) := by
  have hB := B_isElemAbelian hc
  have hB8 := B_natCard hc
  have hBC : Subgroup.closure ({u * e, u, t} : Set Y) ≤ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_gen hc x hx t (by simp))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two (Subgroup.closure ({u * e, u, t} : Set Y))
    (oddCoreOf (Subgroup.centralizer ({t} : Set Y))) hB (by rw [hB8]; norm_num)
    (fun b hb => CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ (hBC hb))
    (Nat.coprime_two_left.mpr
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({t} : Set Y))))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun x hx => by rw [← pow_two]; exact hB.2 x (hE.1 hx)⟩
  exact (inf_le_inf_right _ (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _)).trans
    (T7K.le_gamma2 hE.1 hE2)

theorem inf_cent_t_le_gamma2 (hc : P23Cfg n Y R S t K' W u e g) {s : Y}
    (hsB : s ∈ Subgroup.closure ({u * e, u, t} : Set Y)) (hs1 : s ≠ 1) (hst : s ≠ t) :
    Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({s} : Set Y) ≤
      gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (Subgroup.centralizer ({t} : Set Y)) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hB := B_isElemAbelian hc
  have hcomm := T7A.commutes_closure (comm_gen hc)
  have htB : t ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({u * e, u, t} : Set Y) := T7K.u_mem_B t u e
  have hs2 : s * s = 1 := by
    have := hB.2 s hsB
    rwa [pow_two] at this
  have hts : t * s = s * t := hcomm t htB s hsB
  have hA := T7A.isElemAbelian2_closure_pair hz.sq hs2 hz.ne_one hs1 (Ne.symm hst) hts
  have hAB : Subgroup.closure ({t, s} : Set Y) ≤ Subgroup.closure ({u * e, u, t} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · rw [h]; exact htB
    · rw [h]; exact hsB
  rintro y ⟨hyY, hys⟩
  have hyt : t * y = y * t := (Subgroup.mem_centralizer_singleton_iff.mp hyY).symm
  have hys' : s * y = y * s := (Subgroup.mem_centralizer_singleton_iff.mp hys).symm
  exact T7K.le_gamma2 hAB hA ⟨hyY, T7B.mem_centralizer_closure_pair hyt hys'⟩

theorem twin_le_gamma2_t (hc : P23Cfg n Y R S t K' W u e g) {L : Subgroup Y} (hLΩ : L ∈ Om R)
    (hzL : IsUniqueInvolution L t) {R₁ : Subgroup Y} (hR₁ : IsSylow2In R₁ L)
    (hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y)) :
    L ≤ gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (Subgroup.centralizer ({t} : Set Y)) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have he2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  have hLtq : e ∈ trivialOnQuot L := TwinADescent3.mem_tq_of_sylCent hΩ h2 hLΩ ⟨R₁, hR₁, hR₁e⟩
  have heB : e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
    have hueB : u * e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ (T7K.u_mem_B t u e)) hueB
    rwa [show u⁻¹ * (u * e) = e by group] at h
  have het : e ≠ t := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left
    (Inner.isUniqueInvolution_core hC.datum).mem)
  intro ℓ hℓ
  obtain ⟨i, hi, n', hn, rfl⟩ := TwinLayer.exactCore_cover he2 hLtq (h2 L hLΩ) ℓ hℓ
  refine Subgroup.mul_mem _ ?_ ?_
  · have hiL : i ∈ L := TwinLayer.exactCore_le_left e L hi
    have hiC : i ∈ Subgroup.centralizer ({e} : Set Y) := TwinLayer.exactCore_le_centralizer e L hi
    have hzi : t * i = i * t := hzL.commute_of_mem hiL
    have hit : i ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzi.symm
    exact inf_cent_t_le_gamma2 hc heB hd.he1 het ⟨hit, hiC⟩
  · exact oddCore_Ct_le_gamma2 hc
      (CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal
        (isSubnormal_of_hypOmegaGen hΩ hLΩ hzL) hn)

end U20

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
