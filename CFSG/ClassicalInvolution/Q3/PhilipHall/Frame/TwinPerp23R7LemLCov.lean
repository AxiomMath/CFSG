module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAbs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL2
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Cov

variable {H : Type} [Group H] [Finite H]

theorem exists_conj_cent {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) {R : Subgroup H}
    (hR2 : IsPGroup 2 ↥R) {f : H} (hf2 : f * f = 1)
    (hcomm : ∀ r ∈ R, QuotientGroup.mk' N r * QuotientGroup.mk' N f =
      QuotientGroup.mk' N f * QuotientGroup.mk' N r) :
    ∃ n ∈ N, conjSub n R ≤ Subgroup.centralizer ({f} : Set H) := by
  have hA2 : IsPGroup 2 ↥(Subgroup.zpowers f) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf2
  set J := R ⊔ N with hJ
  have hRJ : IsSylow2In R J := isSylow2In_sup_of_odd hN hR2
  have hJN : J ≤ Subgroup.normalizer (N : Set H) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hNJ : N ≤ oddCoreOf J := le_oddCoreOf_of_normal le_sup_right hJN hN
  have hcommJ : ⁅Subgroup.zpowers f, J⁆ ≤ oddCoreOf J := by
    refine le_trans (Subgroup.commutator_le.mpr fun a ha j hj => ?_) hNJ
    obtain ⟨r, hr, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hj
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc : Commute (QuotientGroup.mk' N f) (QuotientGroup.mk' N r) := (hcomm r hr).symm
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    have h1 : QuotientGroup.mk' N ⁅f ^ k, r * n⁆ = 1 := by
      rw [map_commutatorElement, map_zpow, map_mul, hn1, mul_one]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hc.zpow_left k).eq
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨T, hTJ, hTc⟩ := AscE184Sect.exists_isSylow2In_centralizer hA2 hcommJ
  obtain ⟨x, hxJ, hxT⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hRJ hTJ
  have hxJ' : x ∈ N ⊔ R := by rwa [hJ, sup_comm] at hxJ
  obtain ⟨n, hn, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxJ'
  refine ⟨n, hn, ?_⟩
  have e : conjSub (n * r) R = conjSub n R := by
    rw [conjSub_mul, conjSub_eq_self_of_mem hr]
  rw [← e, hxT]
  exact hTc.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers f)))

end Cov

section CovSec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem exists_conj_cent_sec {R' : Subgroup G} (hR2 : IsPGroup 2 ↥R') (hR'X : R' ≤ rLayerSub Ω A)
    {f : G} (hfX : f ∈ rLayerSub Ω A) (hf2 : f * f = 1)
    (hcent : secImage (rLayerSub Ω A) R' ≤
      Subgroup.centralizer ({(QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub Ω A))
        ⟨f, hfX⟩ : SecQuot (rLayerSub Ω A))} : Set (SecQuot (rLayerSub Ω A)))) :
    ∃ n : ↥(rLayerSub Ω A), n ∈ classicalInvolutionOddCore ↥(rLayerSub Ω A) ∧
      conjSub (n : G) R' ≤ Subgroup.centralizer ({f} : Set G) := by
  set X := rLayerSub Ω A with hXdef
  have hR2' : IsPGroup 2 ↥(R'.subgroupOf X) := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hR'X).symm
  have hf2' : (⟨f, hfX⟩ : ↥X) * ⟨f, hfX⟩ = 1 := Subtype.ext hf2
  obtain ⟨n, hn, hnc⟩ := exists_conj_cent (N := classicalInvolutionOddCore ↥X)
    (CFSG.ComponentClassification.OddCore.odd_card ↥X) hR2' hf2' (fun r hr => by
      have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) r ∈ secImage X R' :=
        Subgroup.mem_map_of_mem _ hr
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hcent hmem)))
  refine ⟨n, hn, fun y hy => ?_⟩
  have hcn : conjSub (n : G) R' ≤ X := by
    have := conjSub_mono (n := (n : G)) hR'X
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer n.2)] at this
  have hyX : y ∈ X := hcn hy
  have hy' : (⟨y, hyX⟩ : ↥X) ∈ conjSub n (R'.subgroupOf X) := by
    rw [conjSub_subgroupOf X n R']
    exact Subgroup.mem_subgroupOf.mpr hy
  have h4 := Subgroup.mem_centralizer_singleton_iff.mp (hnc hy')
  exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h4)

end CovSec

section S3

variable {G : Type} [Group G] [Finite G]

theorem hasS3Quot_secImage_of_cover {X E E₀ : Subgroup G} (hE₀X : E₀ ≤ X) (hE₀E : E₀ ≤ E)
    (hcov : E ≤ oddCoreOf E ⊔ E₀) (h : ModS3O ↥E) : HasS3Quot ↥(secImage X E₀) := by
  obtain ⟨π, hπs, hπO, -⟩ := h
  set N := classicalInvolutionOddCore ↥X with hN
  let ι : ↥(E₀.subgroupOf X) →* ↥(secImage X E₀) :=
    (QuotientGroup.mk' N).subgroupMap (E₀.subgroupOf X)
  have hι : Function.Surjective ι := MonoidHom.subgroupMap_surjective _ _
  let e1 : ↥(E₀.subgroupOf X) ≃* ↥E₀ := Subgroup.subgroupOfEquivOfLe hE₀X
  let π₀ : ↥(E₀.subgroupOf X) →* Equiv.Perm (Fin 3) :=
    π.comp ((Subgroup.inclusion hE₀E).comp e1.toMonoidHom)
  have hπ₀ : ∀ (x : ↥(E₀.subgroupOf X)) (hx : ((x : ↥X) : G) ∈ E),
      π₀ x = π ⟨((x : ↥X) : G), hx⟩ := fun x hx => rfl
  have hker : ι.ker ≤ π₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxE₀ : ((x : ↥X) : G) ∈ E₀ := Subgroup.mem_subgroupOf.mp x.2
    have hxN : (x : ↥X) ∈ N := by
      have h1 : QuotientGroup.mk' N (x : ↥X) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hxO : ((x : ↥X) : G) ∈ oddCoreOf X := mem_oddCoreOf_iff.mpr ⟨(x : ↥X).2, hxN⟩
    have hN'le : oddCoreOf X ⊓ E₀ ≤ oddCoreOf E := by
      refine F7L.le_oddCoreOf_of_cover hE₀E hcov inf_le_right ?_ ?_
      · intro g hg
        exact mem_normalizer_inf' (Sec7.le_normalizer_oddCoreOf X (hE₀X hg))
          (Subgroup.le_normalizer hg)
      · exact (odd_natCard_oddCoreOf X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    obtain ⟨hxE, hxEO⟩ := mem_oddCoreOf_iff.mp (hN'le ⟨hxO, hxE₀⟩)
    rw [hπ₀ x hxE]
    exact hπO hxEO
  have hπ₀s : Function.Surjective π₀ := by
    intro s
    obtain ⟨y, rfl⟩ := hπs s
    have hyE : (y : G) ∈ ((oddCoreOf E ⊔ E₀ : Subgroup G) : Set G) := hcov y.2
    have hBN : E₀ ≤ Subgroup.normalizer (oddCoreOf E : Set G) :=
      hE₀E.trans (Sec7.le_normalizer_oddCoreOf E)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN] at hyE
    obtain ⟨o, ho, w, hw, hyow⟩ := hyE
    refine ⟨⟨⟨w, hE₀X hw⟩, Subgroup.mem_subgroupOf.mpr hw⟩, ?_⟩
    obtain ⟨hoE, hoEO⟩ := mem_oddCoreOf_iff.mp ho
    have hyeq : y = ⟨o, hoE⟩ * ⟨w, hE₀E hw⟩ := Subtype.ext hyow.symm
    rw [hπ₀ _ (hE₀E hw), hyeq, map_mul, hπO hoEO, one_mul]
  refine ⟨MonoidHom.liftOfSurjective ι hι ⟨π₀, hker⟩, fun s => ?_⟩
  obtain ⟨x, rfl⟩ := hπ₀s s
  exact ⟨ι x, MonoidHom.liftOfRightInverse_comp_apply ι _ _ ⟨π₀, hker⟩ x⟩

end S3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
