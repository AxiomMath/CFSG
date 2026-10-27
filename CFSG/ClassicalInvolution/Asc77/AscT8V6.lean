module

public import CFSG.ClassicalInvolution.Asc77.AscT8V5
public import CFSG.ClassicalInvolution.Asc77.AscT8V3

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8V

section LayerMk

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem layerMk_mul {x g h : G} (hg : g ∈ T8.layerJoin Ω x) (hh : h ∈ T8.layerJoin Ω x) :
    layerMk x g hg * layerMk x h hh = layerMk x (g * h) ((T8.layerJoin Ω x).mul_mem hg hh) := by
  unfold layerMk
  rw [← map_mul]
  rfl

theorem layerMk_eq_one {x g : G} (hg : g ∈ T8.layerJoin Ω x) (h1 : g = 1) :
    layerMk x g hg = 1 := by
  subst h1
  exact map_one (QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω x)))

theorem conj_eq_of_central_mul {Q : Type*} [Group Q] {x x' : Q} (hx : x * x = 1)
    (hc : x * x' ∈ Subgroup.center Q) : MulAut.conj x' = MulAut.conj x := by
  ext u
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hcu : (x * x') * u = u * (x * x') := (Subgroup.mem_center_iff.mp hc u).symm
  simp only [MulAut.conj_apply]
  have h1 : x' * u * x'⁻¹ = x⁻¹ * ((x * x') * u * (x * x')⁻¹) * x := by group
  rw [h1, hcu, mul_inv_cancel_right, hxi]

end LayerMk

section E4

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem layerMk_central (hs : Std8 p f Ω K J S R T W z t) :
    layerMk (z * t) z (z_mem_layerJoin hs) * layerMk (z * t) t (t_mem_layerJoin hs) ∈
      Subgroup.center (T8.LayerQuot Ω (z * t)) := by
  have hzY := z_mem_layerJoin hs
  have htY := t_mem_layerJoin hs
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  have hg : (g' : G) ∈ T8.cenZ (z * t) := T8.layerJoin_le_cenZ (z * t) g'.2
  have hcz : (g' : G) * (z * t) = (z * t) * g' := T8.mem_cenZ_iff.mp hg
  have hm : layerMk (z * t) z hzY * layerMk (z * t) t htY =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω (z * t)))
        (⟨z, hzY⟩ * ⟨t, htY⟩) := by
    unfold layerMk
    rw [map_mul]
  have hc2 : g' * (⟨z, hzY⟩ * ⟨t, htY⟩ : ↥(T8.layerJoin Ω (z * t))) =
      (⟨z, hzY⟩ * ⟨t, htY⟩ : ↥(T8.layerJoin Ω (z * t))) * g' :=
    Subtype.ext (by simpa using hcz)
  rw [hm]
  change QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω (z * t))) g' * _ =
    _ * QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω (z * t))) g'
  rw [← map_mul, ← map_mul, hc2]

theorem layerMk_z_sq (hs : Std8 p f Ω K J S R T W z t) :
    layerMk (z * t) z (z_mem_layerJoin hs) * layerMk (z * t) z (z_mem_layerJoin hs) = 1 := by
  rw [layerMk_mul]
  exact layerMk_eq_one _ hs.hz.sq

theorem e4_layer [IsSimpleGroup G] (hE : E4SecNoRoot p f) (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (T8.layerFamQ Ω (z * t))) :
    (∀ σ : MulAut (T8.LayerQuot Ω (z * t)),
      (∀ k ∈ T8.layerImg Ω (z * t) K,
        σ k * k⁻¹ ∈ oddCoreOf (T8.layerImg Ω (z * t) K)) →
      (∀ k ∈ T8.layerImg Ω (z * t) J,
        σ k * k⁻¹ ∈ oddCoreOf (T8.layerImg Ω (z * t) J)) →
        σ * σ ≠ MulAut.conj (layerMk (z * t) z (z_mem_layerJoin hs))) ∧
    (∀ e : T8.LayerQuot Ω (z * t),
      (∀ k ∈ T8.layerImg Ω (z * t) K, ⁅e, k⁆ ∈ oddCoreOf (T8.layerImg Ω (z * t) K)) →
      (∀ k ∈ T8.layerImg Ω (z * t) J, ⁅e, k⁆ ∈ oddCoreOf (T8.layerImg Ω (z * t) J)) →
        e * e ≠ layerMk (z * t) z (z_mem_layerJoin hs) *
          layerMk (z * t) t (t_mem_layerJoin hs)) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hXK := T8.xMem_zt hs
  have hXJ := xMem_J hs
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hlt := T8.card_layerQuot_lt (Ω := Ω) (T8.zt_not_central hs)
  have hzY := z_mem_layerJoin hs
  have htY := t_mem_layerJoin hs
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(T8.layerJoin Ω (z * t)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hcomm : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  have hne : T8.layerImg Ω (z * t) K ≠ T8.layerImg Ω (z * t) J :=
    T8.layerImg_ne_of_involutions hp hq hΩ hx hXK hXJ hs.hz hs.ht
      (T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht)
      (T8.ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  have hTJ : IsSylow2In T J :=
    T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
  have hc : Thompson.Ctx p f Ω W := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := by
    intro y hy
    have hn21 : K ∈ omegaNbr Ω J :=
      T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hs.stand.mem hs.hJ.1 hs.hJ
    have h1 : y ∈ Subgroup.centralizer ({z} : Set G) :=
      T8.rep_le_centralizer hc (T8.stdRepJ hs) (T8.stdRepK hs) (Or.inr hn21) hs.hz hy
    exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz h1
  have hAB : T8.layerImg Ω (z * t) J ∈ omegaNbr (T8.layerFamQ Ω (z * t))
      (T8.layerImg Ω (z * t) K) :=
    T8.layerImg_omegaNbr hp hq hΩ hx hXK hXJ hTJ (T_le_cenZ hs) hTN hne
  have hLYK : T8.layerRes (z * t) K ≤ T8.layerJoin Ω (z * t) := T8.le_layerJoin ⟨K, hXK, rfl⟩
  have hLYJ : T8.layerRes (z * t) J ≤ T8.layerJoin Ω (z * t) := T8.le_layerJoin ⟨J, hXJ, rfl⟩
  have hzL : IsUniqueInvolution (T8.layerRes (z * t) K) z :=
    hXK.isUniqueInvolution_layerRes hp hq hΩ hx hs.hz
  have htL : IsUniqueInvolution (T8.layerRes (z * t) J) t :=
    hXJ.isUniqueInvolution_layerRes hp hq hΩ hx hs.ht
  have hxA : IsUniqueInvolution (T8.layerImg Ω (z * t) K) (layerMk (z * t) z hzY) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf hzL hLYK)
  have hxB : IsUniqueInvolution (T8.layerImg Ω (z * t) J) (layerMk (z * t) t htY) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf htL hLYJ)
  have hcen : layerMk (z * t) z hzY * layerMk (z * t) t htY ∈
      Subgroup.center (T8.LayerQuot Ω (z * t)) := layerMk_central hs
  exact hE hp hq (Nat.card G) hn (T8.LayerQuot Ω (z * t)) hlt (T8.layerFamQ Ω (z * t))
    (T8.hypOmegaMod_layerQuot hp hq hΩ hx)
    (CFSG.ComponentClassification.OddCore.quotient_corefree _) (T8.omegaGen_layerFamQ Ω _)
    (T8.noTwins_layerQuot hp hq hΩ hnt hx) hdisc _ (T8.layerImg_mem hXK) _ hAB _ _ hxA hxB hcen

end E4

end T8V

end CFSG.ClassicalInvolution.Asc77
