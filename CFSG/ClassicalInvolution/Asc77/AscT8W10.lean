module

public import CFSG.ClassicalInvolution.Asc77.AscT8W9
public import CFSG.ClassicalInvolution.Asc77.AscT8V7
public import CFSG.ClassicalInvolution.Asc77.AscT8W7
public import CFSG.ClassicalInvolution.Asc77.AscT8W8
public import CFSG.ClassicalInvolution.Asc77.AscT8Y4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8W

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def E4SecGen : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ n : ℕ, CITBelowU p f n →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), HypOmegaMod p f Φ → classicalInvolutionOddCore X = ⊥ →
        omegaGen Φ = ⊤ → (∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) → ¬ T3.DStarConnected Φ →
          ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ x x' : X, IsUniqueInvolution A x →
            IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
              ∀ σ : MulAut X, σ * σ = 1 → σ x' = x' →
                (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) → (∀ k ∈ B, σ k ∈ B) →
                (¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) →
                  Subgroup.closure ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪
                    {g | σ (x' * g * x'⁻¹) = g}) = ⊤

end Statement

section Assembly

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem layerJoin_le_sigmaNorm_E4 [IsSimpleGroup G] (hgen : E4SecGen p f)
    (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) :
    T8.layerJoin Ω (z * t) ≤ sigmaNorm Ω K := by
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hXK : T8.XMem Ω (z * t) K := T8.xMem_zt hs
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hO := oddCoreOf_layerJoin_le_E4 hs hdisc hE
  by_cases hconn : T3.DStarConnected (T8.layerFamQ Ω (z * t))
  · exact T8.layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hXK (s26_dComp_eq_of_e4 hs hE) hO hconn
  obtain ⟨t₁, ht1sq, ht1ne, hne, htt1, hzt1, -, hcommR, hnJ, hC1, hC2, J₁, hJ₁, hJ₁X, hJ₁t⟩ :=
    exists_good_involution_E4 hs hdisc hE
  have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  have htcen : t ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    have h1 : t * (z * t) = z := by rw [hzt, ← mul_assoc, hs.ht.sq, one_mul]
    have h2 : z * t * t = z := by rw [mul_assoc, hs.ht.sq, mul_one]
    rw [h1, h2])
  have ht1cen : t₁ ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    calc t₁ * (z * t) = (t₁ * z) * t := by rw [mul_assoc]
      _ = (z * t₁) * t := by rw [hzt1]
      _ = z * (t₁ * t) := by rw [mul_assoc]
      _ = z * (t * t₁) := by rw [htt1]
      _ = z * t * t₁ := by rw [mul_assoc])
  have hJmem : J ∈ dComp Ω K := T8.mem_dComp_of_mem_omegaNbr hs.hJ
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ (hnt _ hJΩ) hs.ht).trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJmem)
  have htY := T8V.t_mem_layerJoin hs
  have hzY := T8V.z_mem_layerJoin hs
  have hyY1 : t₁ ∈ Subgroup.normalizer ((T8.layerJoin Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (T8.layerJoin_conjSub_eq hΩ ht1cen)
  have hyYt : t ∈ Subgroup.normalizer ((T8.layerJoin Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (T8.layerJoin_conjSub_eq hΩ htcen)
  set σ : MulAut (T8.LayerQuot Ω (z * t)) := s26Act (T8.layerJoin Ω (z * t)) ⟨t₁, hyY1⟩ with hσ
  set x' : T8.LayerQuot Ω (z * t) := T8V.layerMk (z * t) t htY with hx'
  set x : T8.LayerQuot Ω (z * t) := T8V.layerMk (z * t) z hzY with hxdef
  have hσt : s26Act (T8.layerJoin Ω (z * t)) ⟨t, hyYt⟩ = MulAut.conj x' :=
    s26Act_eq_conj (T8.layerJoin Ω (z * t)) ⟨t, htY⟩
  have hS : ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪ {g | σ (x' * g * x'⁻¹) = g} :
      Set (T8.LayerQuot Ω (z * t))) ⊆ (T8W.layerImage Ω (z * t) (sigmaNorm Ω K) :
        Set (T8.LayerQuot Ω (z * t))) := by
    intro u hu
    rcases hu with (hu | hu) | hu
    · exact mem_layerImage_of_fixed hΩ ht1cen ht1sq hC1 u hu
    · refine mem_layerImage_of_fixed hΩ htcen hs.ht.sq hCt u ?_
      rw [hσt, MulAut.conj_apply]
      have hu' : x' * u = u * x' := hu
      calc x' * u * x'⁻¹ = u * x' * x'⁻¹ := by rw [hu']
        _ = u := by group
    · have hcen : t₁ * t ∈ T8.cenZ (z * t) := (T8.cenZ (z * t)).mul_mem ht1cen htcen
      have hsq : (t₁ * t) * (t₁ * t) = 1 := by
        calc (t₁ * t) * (t₁ * t) = t₁ * (t * t₁) * t := by group
          _ = t₁ * (t₁ * t) * t := by rw [htt1]
          _ = (t₁ * t₁) * (t * t) := by group
          _ = 1 := by rw [ht1sq, hs.ht.sq, mul_one]
      have hC : Subgroup.centralizer ({t₁ * t} : Set G) ≤ sigmaNorm Ω K := by
        rw [← htt1]
        exact hC2
      refine mem_layerImage_of_fixed hΩ hcen hsq hC u ?_
      have hmul : (⟨t₁ * t, mem_normalizer_iff_conjSub_eq.mpr
          (T8.layerJoin_conjSub_eq hΩ hcen)⟩ : ↥(Subgroup.normalizer
            ((T8.layerJoin Ω (z * t) : Subgroup G) : Set G))) = ⟨t₁, hyY1⟩ * ⟨t, hyYt⟩ := rfl
      rw [hmul, map_mul, ← hσ, hσt, MulAut.mul_apply, MulAut.conj_apply]
      exact hu
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hlt := T8.card_layerQuot_lt (Ω := Ω) (T8.zt_not_central hs)
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(T8.layerJoin Ω (z * t)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hne' : T8.layerImg Ω (z * t) K ≠ T8.layerImg Ω (z * t) J :=
    T8.layerImg_ne_of_involutions hp hq hΩ hx hXK hXJ hs.hz hs.ht hzt
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
    T8.layerImg_omegaNbr hp hq hΩ hx hXK hXJ hTJ (T8V.T_le_cenZ hs) hTN hne'
  have hLYK : T8.layerRes (z * t) K ≤ T8.layerJoin Ω (z * t) := T8.le_layerJoin ⟨K, hXK, rfl⟩
  have hLYJ : T8.layerRes (z * t) J ≤ T8.layerJoin Ω (z * t) := T8.le_layerJoin ⟨J, hXJ, rfl⟩
  have hzL : IsUniqueInvolution (T8.layerRes (z * t) K) z :=
    hXK.isUniqueInvolution_layerRes hp hq hΩ hx hs.hz
  have htL : IsUniqueInvolution (T8.layerRes (z * t) J) t :=
    hXJ.isUniqueInvolution_layerRes hp hq hΩ hx hs.ht
  have hxA : IsUniqueInvolution (T8.layerImg Ω (z * t) K) x :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf hzL hLYK)
  have hxB : IsUniqueInvolution (T8.layerImg Ω (z * t) J) x' :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf htL hLYJ)
  have hcen : x * x' ∈ Subgroup.center (T8.LayerQuot Ω (z * t)) := T8V.layerMk_central hs
  have hσsq : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨t₁, hyY1⟩ * ⟨t₁, hyY1⟩ : ↥(Subgroup.normalizer
        ((T8.layerJoin Ω (z * t) : Subgroup G) : Set G))) = 1 := Subtype.ext ht1sq
    rw [this, map_one]
  have hσx' : σ x' = x' := by
    refine s26Act_mk (T8.layerJoin Ω (z * t)) ⟨t₁, hyY1⟩ ⟨t, htY⟩ ⟨t, htY⟩ ?_
    show t = t₁ * t * t₁⁻¹
    calc t = t * t₁ * t₁⁻¹ := by group
      _ = t₁ * t * t₁⁻¹ := by rw [htt1]
  have hRsyl : IsSylow2In R K :=
    T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hs.hR.1 hs.hR.2.1
  have hyNK : t₁ ∈ Subgroup.normalizer (K : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hzt1.symm)
  have hcommK : ∀ k ∈ K, ⁅t₁, k⁆ ∈ oddCoreOf K :=
    T8V.comm_mem_oddCoreOf_of_pow hp hq hΩ hK hRsyl hyNK (m := 1)
      (by rw [pow_one, pow_two]; exact ht1sq) (fun r hr => (hcommR r hr).symm)
  have hσA : ∀ k ∈ T8.layerImg Ω (z * t) K,
      σ k * k⁻¹ ∈ oddCoreOf (T8.layerImg Ω (z * t) K) :=
    T8V.s26Act_mul_inv_mem hΩ hXK ht1cen hyNK hcommK
  have hJN : t₁ ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_conjSub_eq.mpr hnJ
  have hLaN : t₁ ∈ Subgroup.normalizer (T8.layerRes (z * t) J : Set G) :=
    T8.mem_normalizer_layerRes hJN ht1cen
  have hσB : ∀ k ∈ T8.layerImg Ω (z * t) J, σ k ∈ T8.layerImg Ω (z * t) J := by
    intro kb hkb
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkb
    have hkL : (k' : G) ∈ T8.layerRes (z * t) J := Subgroup.mem_subgroupOf.mp hk'
    have hyk : t₁ * (k' : G) * t₁⁻¹ ∈ T8.layerJoin Ω (z * t) :=
      (Subgroup.mem_normalizer_iff.mp hyY1 (k' : G)).mp k'.2
    have e := s26Act_mk (T8.layerJoin Ω (z * t)) ⟨t₁, hyY1⟩ k' ⟨t₁ * (k' : G) * t₁⁻¹, hyk⟩ rfl
    change σ (↑k') ∈ _
    rw [hσ, e]
    exact ⟨⟨t₁ * (k' : G) * t₁⁻¹, hyk⟩,
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hLaN (k' : G)).mp hkL), rfl⟩
  have hσnt : ¬ ∀ k ∈ T8.layerImg Ω (z * t) J, σ k * k⁻¹ ∈ oddCoreOf (T8.layerImg Ω (z * t) J) :=
    not_trivial_on_layerImg_J hs hdisc hE ht1cen ht1sq hne hnJ hJ₁ hJ₁X hJ₁t
  have hclosure := hgen hp hq (Nat.card G) hn (T8.LayerQuot Ω (z * t)) hlt (T8.layerFamQ Ω (z * t))
    (T8.hypOmegaMod_layerQuot hp hq hΩ hx)
    (CFSG.ComponentClassification.OddCore.quotient_corefree _) (T8.omegaGen_layerFamQ Ω _)
    (T8.noTwins_layerQuot hp hq hΩ hnt hx) hconn _ (T8.layerImg_mem hXK) _ hAB x x' hxA hxB hcen σ
    hσsq hσx' hσA hσB hσnt
  exact layerJoin_le_of_closure hO _ hS hclosure

theorem c27_8E4_of_e4SecGen (hgen : E4SecGen p f) : C27_8E4 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  exact T8.centralizer_le_sigmaNorm_of_layerJoin_le hs
    (layerJoin_le_sigmaNorm_E4 hgen hs hdisc hE4)

end Assembly

end T8W

end CFSG.ClassicalInvolution.Asc77
