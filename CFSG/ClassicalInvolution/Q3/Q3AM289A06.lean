module

public import CFSG.ClassicalInvolution.Q3.Q3AM289A03
public import CFSG.ClassicalInvolution.Q3.Q3AM289A04

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77.Thompson
open scoped MatrixGroups commutatorElement

namespace S3A

section Root

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sq_root_of_omegaStarNbr (hΩ : HypOmegaMod Ω) {J J₁ : Subgroup G} {w : G}
    (hJ₁ : J₁ ∈ omegaStarNbr Ω J) (hw : IsUniqueInvolution J₁ w) :
    ∃ w' ∈ Subgroup.normalizer (J : Set G), w' * w' = w := by
  obtain ⟨-, -, U, hU, hUJ₁, hUN⟩ := hJ₁
  obtain ⟨R₁, -, J', -, hR₁J', hUR₁, hUcyc, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
  have hUp : IsPGroup 2 ↥U := hR₁J'.2.1.to_le hUR₁
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨g, hg⟩ := hUcyc.exists_generator
  obtain ⟨k, hk⟩ := hUp.exists_card_eq
  have hord : orderOf (g : G) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hu4 : orderOf ((g : G) ^ 2 ^ (k - 2)) = 4 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hord]; exact pow_dvd_pow 2 (by omega)), hord,
      show 2 ^ k = 2 ^ (k - 2) * 4 by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega]
    exact Nat.mul_div_cancel_left 4 (by positivity)
  have hwU : (g : G) ^ 2 ^ (k - 2) ∈ U := U.pow_mem g.2 _
  refine ⟨(g : G) ^ 2 ^ (k - 2), hUN hwU, ?_⟩
  have h44 : ((g : G) ^ 2 ^ (k - 2)) ^ 4 = 1 := by
    rw [← hu4]
    exact pow_orderOf_eq_one _
  have h2ne : ((g : G) ^ 2 ^ (k - 2)) ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hu4] at this
    omega
  have hsq1 : ((g : G) ^ 2 ^ (k - 2)) ^ 2 * ((g : G) ^ 2 ^ (k - 2)) ^ 2 = 1 := by
    rw [← pow_add]
    exact h44
  rcases hw.unique (((g : G) ^ 2 ^ (k - 2)) ^ 2) (hUJ₁ (U.pow_mem hwU 2)) hsq1 with h | h
  · exact absurd h h2ne
  · rw [← pow_two]
    exact h

end Root

section LayerTwin


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layer_twin_s3 [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t) {w : G}
    (hw2 : w * w = 1) (hwz : z * w = w * z) (hwt : t * w = w * t) (hne : w ≠ t)
    {R₀ : Subgroup G} (hR₀ : IsSylow2In R₀ K) (hwR : ∀ r ∈ R₀, r * w = w * r)
    {J₁ : Subgroup G} (hJ₁ : J₁ ∈ Ω) (hJ₁w : IsUniqueInvolution J₁ w)
    (hJ₁star : J₁ ∈ omegaStarNbr Ω J) (hJ₁nbr : J₁ ∉ omegaNbr Ω J)
    (hdisc : ¬ DConnected (Q3T7.layerFam3 Ω (z * t)))
    (hwN : w ∈ Subgroup.normalizer ((exactLayer3 Ω (z * t) : Subgroup G) : Set G)) :
    ∃ (t' : Assembly.LowTwoRank.StatedLieTag) (k' : ℕ)
      (M : Ih8Model 3 1 (Q3T7.layerFam3 Ω (z * t)) t' k' 1)
      (R₁ R₂ : Subgroup (modelUniv t' k' 3 1 Fact.out).K)
      (y y' k : (modelUniv t' k' 3 1 Fact.out).K),
      R₁ ∈ fundamentalSubgroups t' (modelUniv t' k' 3 1 Fact.out).D ∧
      R₂ ∈ fundamentalSubgroups t' (modelUniv t' k' 3 1 Fact.out).D ∧ R₁ ≠ R₂ ∧
      Commutes R₁ R₂ ∧ y ∈ R₁ ∧ y * y = 1 ∧ y ≠ 1 ∧ y' ∈ R₂ ∧ y' * y' = 1 ∧ y' ≠ 1 ∧
      M.ψ y = T8V.layerMk (z * t) z (T8V.z_mem_layerJoin hs) ∧
      M.ψ y' = T8V.layerMk (z * t) t (T8V.t_mem_layerJoin hs) ∧
      k ∈ R₂ ∧ M.ψ k * M.ψ k = M.ψ y' ∧
      (∀ r ∈ R₁, s26Act (exactLayer3 Ω (z * t)) ⟨w, hwN⟩ (M.ψ r) = M.ψ r) ∧
      (∀ r ∈ R₂, s26Act (exactLayer3 Ω (z * t)) ⟨w, hwN⟩ (M.ψ r) =
        M.ψ k * M.ψ r * (M.ψ k)⁻¹) := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hXK : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hKt : K ∈ tqMembers3 Ω (z * t) := hXK.mem_tqMembers3 hΩ hx
  have hJt : J ∈ tqMembers3 Ω (z * t) := hXJ.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hne0 : (tqMembers3 Ω (z * t)).Nonempty := ⟨K, hKt⟩
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hwcomm : w * (z * t) = z * t * w := by
    calc w * (z * t) = (w * z) * t := by rw [mul_assoc]
      _ = (z * w) * t := by rw [hwz]
      _ = z * (w * t) := by rw [mul_assoc]
      _ = z * (t * w) := by rw [hwt]
      _ = z * t * w := by rw [mul_assoc]
  have hwcen : w ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr hwcomm
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hnJ : conjSub w J = J :=
    conjSub_eq_of_mem_normalizer (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ
      (hnt J hJΩ) hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm))
  have htY := T8V.t_mem_layerJoin hs
  have hzY := T8V.z_mem_layerJoin hs
  set σ : MulAut (Q3T7.layerQuot3 Ω (z * t)) :=
    s26Act (exactLayer3 Ω (z * t)) ⟨w, hwN⟩ with hσ
  set x' : Q3T7.layerQuot3 Ω (z * t) := T8V.layerMk (z * t) t htY with hx'
  set x : Q3T7.layerQuot3 Ω (z * t) := T8V.layerMk (z * t) z hzY with hxdef
  have hlt := Q3T7.card_layerQuot3_lt (Ω := Ω) (Layer.zt_not_central3 hs)
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(exactLayer3 Ω (z * t)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hne' : Layer.layerImg3 Ω (z * t) K ≠ Layer.layerImg3 Ω (z * t) J :=
    Layer.layerImg3_ne_of_involutions hL hXK hXJ hs.hz hs.ht hzt
      (T8.ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  have hTJ : IsSylow2In T J :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
  have hc : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := by
    intro y hy
    have hn21 : K ∈ omegaNbr Ω J :=
      Q3CL.T3.omegaNbr_symm Disconnected.AschTight.Sec6Gen.l6_2Gen hΩ hs.stand.mem hs.hJ.1 hs.hJ
    have h1 : y ∈ Subgroup.centralizer ({z} : Set G) :=
      T8.rep_le_centralizer hc (T8.stdRepJ hs) (T8.stdRepK hs) (Or.inr hn21) hs.hz hy
    exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz h1
  have hAB : Layer.layerImg3 Ω (z * t) J ∈ omegaNbr (Q3T7.layerFam3 Ω (z * t))
      (Layer.layerImg3 Ω (z * t) K) :=
    Layer.layerImg3_omegaNbr hKt hJt hTJ (T8V.T_le_cenZ hs) hTN hne'
  have hLYK : exactCore3 (z * t) K ≤ exactLayer3 Ω (z * t) := exactCore3_le_exactLayer3 hKt
  have hLYJ : exactCore3 (z * t) J ≤ exactLayer3 Ω (z * t) := exactCore3_le_exactLayer3 hJt
  have hzL : IsUniqueInvolution (exactCore3 (z * t) K) z :=
    Layer.isUniqueInvolution_exactCore3 hXK.2.1 hs.hz
  have htL : IsUniqueInvolution (exactCore3 (z * t) J) t :=
    Layer.isUniqueInvolution_exactCore3 hXJ.2.1 hs.ht
  have hxA : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) K) x :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf hzL hLYK)
  have hxB : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) J) x' :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf htL hLYJ)
  have hcen : x * x' ∈ Subgroup.center (Q3T7.layerQuot3 Ω (z * t)) := T8V.layerMk_central hs
  have hσsq : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨w, hwN⟩ * ⟨w, hwN⟩ : ↥(Subgroup.normalizer
        ((exactLayer3 Ω (z * t) : Subgroup G) : Set G))) = 1 := Subtype.ext hw2
    rw [this, map_one]
  have hσσ : ∀ q, σ (σ q) = q := fun q => by
    have := congrArg (fun τ : MulAut (Q3T7.layerQuot3 Ω (z * t)) => τ q) hσsq
    simpa using this
  have hyNK : w ∈ Subgroup.normalizer (K : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hwz.symm)
  have hcommK : ∀ k ∈ K, ⁅w, k⁆ ∈ oddCoreOf K :=
    commutator_mem_oddCoreOf_of_pow3 hs.hz hR₀ hyNK (m := 1)
      (by rw [pow_one, pow_two]; exact hw2) (fun r hr => (hwR r hr).symm)
  have hσA : ∀ k ∈ Layer.layerImg3 Ω (z * t) K,
      σ k * k⁻¹ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t) K) :=
    T8V.s26Act_mul_inv_mem hΩ hKt hwcen hyNK hcommK
  have hσnt : ¬ ∀ k ∈ Layer.layerImg3 Ω (z * t) J,
      σ k * k⁻¹ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t) J) := by
    intro H₀
    have h1 := omegaNbr_of_trivialOn_layerImg hs hwcen hw2 hne hnJ hJ₁ hJ₁w H₀
    exact hJ₁nbr (Q3CL.T3.omegaNbr_symm Disconnected.AschTight.Sec6Gen.l6_2Gen hΩ hJ₁ hJΩ h1)
  have hΦ : HypOmegaModU (.sl2 3 1) (Q3T7.layerFam3 Ω (z * t)) :=
    Q3T7.hypOmegaModU_layerFam3 hs3 hL.hc2 hne0
  have hKΦ : Layer.layerImg3 Ω (z * t) K ∈ Q3T7.layerFam3 Ω (z * t) := Layer.layerImg3_mem hKt
  obtain ⟨t', k', htag, ⟨M⟩⟩ := tag3_of_not_dConnected hs.stand.below hs.stand.ih hlt hΦ
    Q3T7.layerQuot3_oddCore_eq_bot (Q3T7.omegaGen_layerFam3 hs3 hL.hc2 hne0)
    (Q3T7.aEmpty_layerFam3 hs3 hL.hc2 hne0) hdisc hKΦ hAB
  have hG2 : t' ≠ .G2 := by
    rcases htag with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hD4 : t' ≠ .trialityD4 := by
    rcases htag with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hnpsl : ¬ (t' = .PSL ∧ k' = 2) := by
    rintro ⟨h3, h4⟩
    rcases htag with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at h3
      exact absurd h3 (by decide)
    · omega
    · rw [h1] at h3
      exact absurd h3 (by decide)
    · rw [h1] at h3
      exact absurd h3 (by decide)
    · rw [h1] at h3
      exact absurd h3 (by decide)
    · rw [h1] at h3
      exact absurd h3 (by decide)
  have hSperf : Group.IsPerfect (modelUniv t' k' 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (ModelFacts.modelClauseZero t' k' 3 1 Fact.out (ih8_isFundTag_mf M.isFundTag)
        M.admissible).1.1
  obtain ⟨RM, RM', y, y', hRM, hRM', hAR, hBR, hy, hy', hP⟩ :=
    E4G3.e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hKΦ hAB hxA hxB hcen
  have hex := exactMembers_of_ih8Model M hΦ hG2 hD4
  have hA0 : oddCoreOf (Layer.layerImg3 Ω (z * t) K) = ⊥ := oddCoreOf_eq_bot_of_exact hex hKΦ
  have hB0 : oddCoreOf (Layer.layerImg3 Ω (z * t) J) = ⊥ := oddCoreOf_eq_bot_of_exact hex hAB.1
  have hσR : ∀ r ∈ RM, σ (M.ψ r) = M.ψ r := by
    intro r hr
    have h := hσA (M.ψ r) (by rw [hAR]; exact Subgroup.mem_map_of_mem _ hr)
    rw [hA0, Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  have hinj : ∀ a ∈ RM', ∀ b ∈ RM', M.ψ a = M.ψ b → a = b := by
    intro a ha b hb hab
    have h1 : a * b⁻¹ = 1 := M.injOn_fund hnpsl (M.cls_sub hRM') (a * b⁻¹)
      (RM'.mul_mem ha (RM'.inv_mem hb)) (by rw [map_mul, map_inv, hab, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  obtain ⟨eR'⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hRM'
  have hodd3 := M.natCard_galoisField_odd hp2
  have hy'ord : orderOf y' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hP.hy'2) hP.hy'1
  have hy'sl : y' = sl2Inv eR' := eq_sl2Inv_of_orderOf_eq_two hodd3 eR' hP.hy' hy'ord
  obtain ⟨w', hw'N, hw'⟩ := exists_sq_root_of_omegaStarNbr hΩ hJ₁star hJ₁w
  have hJcl : IsClassicalMember3 J t :=
    Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hs.stand.modU hJΩ hs.ht
  have hc2 : IsPGroup 2 (Subgroup.zpowers (z * t)) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one hx
  obtain ⟨i, hi, hinner⟩ := exists_exactCore_inner_of_sq hJcl hc2 hJt.2 hw'N hw'
  have hiY : i ∈ exactLayer3 Ω (z * t) := hLYJ hi
  have hiC : i ∈ Subgroup.centralizer ({z * t} : Set G) := exactCore3_le_centralizer _ _ hi
  have hiJ : i ∈ J := exactCore3_le_left _ _ hi
  have hwC : w ∈ Subgroup.centralizer ({z * t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hwcomm
  have hw₂C : i⁻¹ * w ∈ Subgroup.centralizer ({z * t} : Set G) :=
    (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem hiC) hwC
  have hw₂cen : i⁻¹ * w ∈ T8.cenZ (z * t) :=
    T8.mem_cenZ_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hw₂C)
  have hw₂N : i⁻¹ * w ∈ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hiJ))
      (mem_normalizer_iff_conjSub_eq.mpr hnJ)
  have hs2 := T8V.s26Act_mul_inv_mem hΩ hJt hw₂cen hw₂N hinner
  set κ : Q3T7.layerQuot3 Ω (z * t) :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω (z * t))) ⟨i, hiY⟩ with hκ
  have hκJ : κ ∈ Layer.layerImg3 Ω (z * t) J := ⟨⟨i, hiY⟩, Subgroup.mem_subgroupOf.mpr hi, rfl⟩
  have hi'Y : i⁻¹ ∈ exactLayer3 Ω (z * t) := (exactLayer3 Ω (z * t)).inv_mem hiY
  have hconj : ∀ q : Q3T7.layerQuot3 Ω (z * t),
      s26Act (exactLayer3 Ω (z * t)) ⟨i⁻¹ * w, mem_normalizer_iff_conjSub_eq.mpr
        (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hw₂cen)⟩ q = κ⁻¹ * σ q * κ := by
    intro q
    have e1 : (⟨i⁻¹ * w, mem_normalizer_iff_conjSub_eq.mpr
        (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hw₂cen)⟩ :
          ↥(Subgroup.normalizer ((exactLayer3 Ω (z * t) : Subgroup G) : Set G))) =
        ⟨i⁻¹, Subgroup.le_normalizer hi'Y⟩ * ⟨w, hwN⟩ := rfl
    rw [e1, map_mul, MulAut.mul_apply]
    have e2 := s26Act_eq_conj (exactLayer3 Ω (z * t)) ⟨i⁻¹, hi'Y⟩
    rw [e2, MulAut.conj_apply]
    have e3 : (QuotientGroup.mk (⟨i⁻¹, hi'Y⟩ : ↥(exactLayer3 Ω (z * t))) :
        ↥(exactLayer3 Ω (z * t)) ⧸ classicalInvolutionOddCore ↥(exactLayer3 Ω (z * t))) = κ⁻¹ := by
      rw [hκ]
      have : (⟨i⁻¹, hi'Y⟩ : ↥(exactLayer3 Ω (z * t))) = (⟨i, hiY⟩ : ↥(exactLayer3 Ω (z * t)))⁻¹ :=
        rfl
      rw [this, QuotientGroup.mk_inv]
      rfl
    rw [e3, inv_inv]
  have hσJ : ∀ q ∈ Layer.layerImg3 Ω (z * t) J, σ q = κ * q * κ⁻¹ := by
    intro q hq
    have h1 := hs2 q hq
    rw [hconj q, hB0, Subgroup.mem_bot, mul_inv_eq_one] at h1
    calc σ q = κ * (κ⁻¹ * σ q * κ) * κ⁻¹ := by group
      _ = κ * q * κ⁻¹ := by rw [h1]
  have hconjJ : ∀ q ∈ Layer.layerImg3 Ω (z * t) J,
      κ * q * κ⁻¹ ∈ Layer.layerImg3 Ω (z * t) J := fun q hq =>
    (Layer.layerImg3 Ω (z * t) J).mul_mem
      ((Layer.layerImg3 Ω (z * t) J).mul_mem hκJ hq) ((Layer.layerImg3 Ω (z * t) J).inv_mem hκJ)
  have hsq : ∀ q ∈ Layer.layerImg3 Ω (z * t) J, κ * κ * q * (κ * κ)⁻¹ = q := by
    intro q hq
    have h1 := hσσ q
    rw [hσJ q hq, hσJ _ (hconjJ q hq)] at h1
    calc κ * κ * q * (κ * κ)⁻¹ = κ * (κ * q * κ⁻¹) * κ⁻¹ := by group
      _ = q := h1
  obtain ⟨k₀, hk₀R, hk₀⟩ : ∃ k₀ ∈ RM', M.ψ k₀ = κ := by
    have : κ ∈ RM'.map M.ψ := by
      rw [← hBR]
      exact hκJ
    exact Subgroup.mem_map.mp this
  have hψR' : ∀ r ∈ RM', M.ψ r ∈ Layer.layerImg3 Ω (z * t) J := fun r hr => by
    rw [hBR]
    exact Subgroup.mem_map_of_mem _ hr
  have hcent : ∀ r ∈ RM', (k₀ * k₀) * r = r * (k₀ * k₀) := by
    intro r hr
    apply hinj _ (RM'.mul_mem (RM'.mul_mem hk₀R hk₀R) hr) _
      (RM'.mul_mem hr (RM'.mul_mem hk₀R hk₀R))
    have h := hsq (M.ψ r) (hψR' r hr)
    rw [← hk₀] at h
    have h' := mul_inv_eq_iff_eq_mul.mp h
    simp only [map_mul]
    exact h'
  have hk₀sq : k₀ * k₀ = y' := by
    rcases eq_one_or_eq_sl2Inv_of_central eR' (RM'.mul_mem hk₀R hk₀R) hcent with h | h
    · exfalso
      have hk₀c : ∀ r ∈ RM', k₀ * r = r * k₀ := by
        by_cases hk1 : k₀ = 1
        · intro r _
          rw [hk1, one_mul, mul_one]
        · have hord : orderOf k₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h) hk1
          have hk₀y : k₀ = sl2Inv eR' := eq_sl2Inv_of_orderOf_eq_two hodd3 eR' hk₀R hord
          intro r hr
          rw [hk₀y, ← hy'sl]
          exact hP.cy' r hr
      apply hσnt
      intro q hq
      have hq' : q ∈ RM'.map M.ψ := by
        rw [← hBR]
        exact hq
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hq'
      have hcomm : κ * M.ψ r = M.ψ r * κ := by
        rw [← hk₀, ← map_mul, ← map_mul, hk₀c r hr]
      have hfix : σ (M.ψ r) = M.ψ r := by
        rw [hσJ _ hq, hcomm]
        group
      rw [hfix, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h, ← hy'sl]
  exact ⟨t', k', M, RM, RM', y, y', k₀, M.cls_sub hRM, M.cls_sub hRM', hP.ne, hP.comm, hP.hy,
    hP.hy2, hP.hy1, hP.hy', hP.hy'2, hP.hy'1, hy, hy', hk₀R, by rw [← map_mul, hk₀sq], hσR,
    fun r hr => by rw [hσJ _ (hψR' r hr), hk₀]⟩

end LayerTwin

end S3A

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
