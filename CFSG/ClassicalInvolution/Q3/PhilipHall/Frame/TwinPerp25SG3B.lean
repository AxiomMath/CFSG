module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SG3A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Pf2C

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement


section Lift

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem nc4_lift_sec (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    {c : G} (hbC : c * z * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    {M : Subgroup (↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a))}
    (hM : M ∈ TwinDisc.secFam Ω a)
    {y : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)}
    (hyM : y ∈ M) (hy4 : y * y * y * y = 1) (hy2 : y * y ≠ 1)
    (hfix : secAct hΩ hc2 ⟨c * z * c⁻¹, hbC⟩ y = y) :
    ∃ J ∈ tqMembers3 Ω a, IsUniqueInvolution J (c * z * c⁻¹) := by
  classical
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hzK : IsUniqueInvolution K z := hs.hz
  have hN₀odd : Odd (Nat.card (classicalInvolutionOddCore ↥(coreHull Ω a))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω a)
  have hb2 : (c * z * c⁻¹) * (c * z * c⁻¹) = 1 := by
    have hz2 : z * z = 1 := hzK.sq
    calc (c * z * c⁻¹) * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hbH2 : (⟨c * z * c⁻¹, hbC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) *
      ⟨c * z * c⁻¹, hbC⟩ = 1 := Subtype.ext hb2
  have hbY : conjSub (⟨c * z * c⁻¹, hbC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) (coreHull Ω a) =
      coreHull Ω a := conjSub_coreHull hΩ hc2 _
  obtain ⟨J₁, hJ₁tq, hMJ⟩ := exists_of_mem_secFam hM
  rw [hMJ] at hyM
  obtain ⟨g₁, hg₁⟩ := hst.trans J₁ hJ₁tq.1
  have hzJ₁ : IsUniqueInvolution J₁ (g₁ * z * g₁⁻¹) := by
    rw [← hg₁]
    exact hzK.conj g₁
  have hy_ord : orderOf y = 4 := by
    have h4 : y ^ 2 ^ (1 + 1) = 1 := by
      have : y ^ 2 ^ (1 + 1) = y * y * y * y := by simp [pow_succ, mul_assoc]
      rw [this]
      exact hy4
    have h2 : ¬ y ^ 2 ^ 1 = 1 := by simpa [pow_two] using hy2
    have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
    simpa using this
  have hyM' : y ∈ (((TwinADescent.coreAt a J₁).subgroupOf (Subgroup.centralizer ({a} : Set G))).subgroupOf
      (coreHull Ω a)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω a))) := hyM
  obtain ⟨c0, hcmem, hcy⟩ := Subgroup.mem_map.mp hyM'
  have hcM : ((c0 : ↥(Subgroup.centralizer ({a} : Set G))) : G) ∈ TwinADescent.coreAt a J₁ :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hcmem)
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c0).ne'
  have hc'k : (c0 ^ m) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hkm]
    exact pow_orderOf_eq_one c0
  have hπc' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω a)) (c0 ^ m) = y ^ m := by
    rw [map_pow, hcy]
  have hcop : Nat.Coprime (orderOf y) m := by
    rw [hy_ord]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
  have hym_ord : orderOf (y ^ m) = 4 := by
    rw [Nat.Coprime.orderOf_pow hcop, hy_ord]
  have hy44 : y ^ 4 = 1 := by
    rw [← hy_ord]
    exact pow_orderOf_eq_one y
  have hc'4 : (c0 ^ m) ^ 4 = 1 := by
    have h1 : (c0 ^ m) ^ 4 ∈ classicalInvolutionOddCore ↥(coreHull Ω a) := by
      have h0 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω a)) ((c0 ^ m) ^ 4) = 1 := by
        rw [map_pow, hπc', ← pow_mul, mul_comm, pow_mul, hy44, one_pow]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have h2 : orderOf (⟨(c0 ^ m) ^ 4, h1⟩ : classicalInvolutionOddCore ↥(coreHull Ω a)) ∣
        Nat.card (classicalInvolutionOddCore ↥(coreHull Ω a)) := orderOf_dvd_natCard _
    have h3 : orderOf (⟨(c0 ^ m) ^ 4, h1⟩ : classicalInvolutionOddCore ↥(coreHull Ω a)) ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      refine orderOf_dvd_of_pow_eq_one ?_
      show ((c0 ^ m) ^ 4) ^ (2 ^ k) = 1
      rw [← pow_mul, mul_comm, pow_mul, hc'k, one_pow]
    have h4 : Nat.Coprime (2 ^ k) (Nat.card (classicalInvolutionOddCore ↥(coreHull Ω a))) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN₀odd)
    have h5 : orderOf (⟨(c0 ^ m) ^ 4, h1⟩ : classicalInvolutionOddCore ↥(coreHull Ω a)) = 1 :=
      Nat.eq_one_of_dvd_coprimes h4 h3 h2
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h5)
  have hc'2 : ¬ (c0 ^ m) ^ 2 ^ 1 = 1 := by
    intro h'
    have h'' : (c0 ^ m) ^ 2 = 1 := by simpa using h'
    have h3 : (y ^ m) ^ 2 = 1 := by
      rw [← hπc', ← map_pow, h'', map_one]
    have h4 : orderOf (y ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one h3
    rw [hym_ord] at h4
    omega
  have hc'_ord : orderOf (c0 ^ m) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hc'2 (by simpa using hc'4)
    simpa using this
  have hy₁coe : (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) =
      ((c0 : ↥(Subgroup.centralizer ({a} : Set G))) : G) ^ m := by
    simp
  have hy₁J : (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) ∈ J₁ := by
    rw [hy₁coe]
    exact TwinADescent.coreAt_le_left a J₁ ((TwinADescent.coreAt a J₁).pow_mem hcM m)
  have hy₁Y : ((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) ∈ coreHull Ω a :=
    (c0 ^ m).2
  have hy₁4H : orderOf ((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) = 4 := by
    rw [Subgroup.orderOf_coe]; exact hc'_ord
  have hy₁4 : orderOf (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) = 4 := by
    rw [Subgroup.orderOf_coe]; exact hy₁4H
  have hfixc : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω a))
        (C25Y.conjOnSub (coreHull Ω a) hbY (c0 ^ m)) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω a)) (c0 ^ m) := by
    have h1 : secAct hΩ hc2 ⟨c * z * c⁻¹, hbC⟩
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω a)) (c0 ^ m)) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω a))
          (C25Y.conjOnSub (coreHull Ω a) hbY (c0 ^ m)) := secAct_mk hΩ hc2 _ (c0 ^ m)
    have h2 : secAct hΩ hc2 ⟨c * z * c⁻¹, hbC⟩ (y ^ m) = y ^ m := by rw [map_pow, hfix]
    rw [← h1, hπc', h2]
  have hcom : ⁅(⟨c * z * c⁻¹, hbC⟩ : ↥(Subgroup.centralizer ({a} : Set G))),
      ((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G)))⁆ ∈ oddCoreOf (coreHull Ω a) := by
    have h1 : C25Y.conjOnSub (coreHull Ω a) hbY (c0 ^ m) * (c0 ^ m)⁻¹ ∈
        classicalInvolutionOddCore ↥(coreHull Ω a) := by
      have h0 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω a))
          (C25Y.conjOnSub (coreHull Ω a) hbY (c0 ^ m) * (c0 ^ m)⁻¹) = 1 := by
        rw [map_mul, map_inv, hfixc, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    refine Subgroup.mem_map.mpr ⟨_, h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, C25Y.coe_conjOnSub,
      commutatorElement_def]
  have hR2 : IsPGroup 2 (Subgroup.zpowers
      ((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G)))) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hy₁4H]; norm_num)
  have hcN : (⟨c * z * c⁻¹, hbC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈
      Subgroup.normalizer (oddCoreOf (coreHull Ω a) : Set ↥(Subgroup.centralizer ({a} : Set G))) :=
    T7L.mem_normalizer_oddCoreOf (mem_normalizer_iff_conjSub_eq.mpr hbY)
  have huN : ((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) ∈
      Subgroup.normalizer (oddCoreOf (coreHull Ω a) : Set ↥(Subgroup.centralizer ({a} : Set G))) :=
    T7L.mem_normalizer_oddCoreOf (Subgroup.le_normalizer hy₁Y)
  obtain ⟨n, hn, hncent⟩ := T7L.exists_conj_centralizes hbH2 (oddCoreOf_odd_natCard (coreHull Ω a)) hR2
    (Subgroup.zpowers_le.mpr huN) hcN
    (fun r hr => C25X.comm_mem_of_mem_zpowers huN hcom hr)
  have hyc := Subgroup.mem_centralizer_singleton_iff.mp
      (hncent (conj_mem_conjSub (Subgroup.mem_zpowers
        ((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))))))
  have hnC : ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) ∈ Subgroup.centralizer ({a} : Set G) := n.2
  have hJ₀Ω : conjSub ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) J₁ ∈ Ω :=
    hst.hyp.conjInvariant _ J₁ hJ₁tq.1
  have hJ₀z : IsUniqueInvolution (conjSub ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) J₁)
      (((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) * (g₁ * z * g₁⁻¹) *
        ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹) := hzJ₁.conj _
  have hyJ' : ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
      (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
      ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹ ∈
        conjSub ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) J₁ :=
    conj_mem_conjSub hy₁J
  have hy4' : orderOf (((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
      (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
      ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G))
      (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G)
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hy₁4
  have hycG : (((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
      (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
      ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹) * (c * z * c⁻¹) =
      (c * z * c⁻¹) * (((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
      (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
      ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹) := by
    have := congrArg Subtype.val hyc
    simpa using this
  by_cases hbeq : c * z * c⁻¹ = ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) * (g₁ * z * g₁⁻¹) *
      ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹
  · refine ⟨conjSub ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) J₁,
      conjSub_mem_tqMembers3 hst.hyp.conjInvariant hnC hJ₁tq, ?_⟩
    rw [hbeq]
    exact hJ₀z
  · exact absurd hycG.symm
      (T7ER.not_commute_of_conj hs hyp.hW hyp.hE4 hJ₀Ω hJ₀z hbeq hyJ' hy4')

theorem conj_of_member_sec (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hT : TwinThmE.T4Supply) (hbad : BadElt z a)
    {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω a) {b : G} (hb : IsUniqueInvolution J b) :
    ∃ h : ↥(Subgroup.centralizer ({a} : Set G)), h ∈ coreHull Ω a ∧ (h : G) * z * (h : G)⁻¹ = b := by
  classical
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  obtain ⟨hKtq, -, hz, -, -, -⟩ := layer_twins_tq hyp hacA
  have htr := layer_transitive_of_bad hyp ha2 ha1 hacA hT hbad
  obtain ⟨hzC, hzY, hzb⟩ := isUniqueInvolution_secImg hΩ hc2 hKtq hz
  obtain ⟨hbC, hbY, hbb⟩ := isUniqueInvolution_secImg hΩ hc2 hJ hb
  obtain ⟨xb, hxb⟩ := htr _ (secImg_mem_secFam hKtq) _ (secImg_mem_secFam hJ)
  have h1 := hzb.conj xb
  rw [hxb] at h1
  have heq := h1.eq hbb
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xb
  set u : ↥(coreHull Ω a) := x₀ * ⟨⟨z, hzC⟩, hzY⟩ * x₀⁻¹ with hu
  set v : ↥(coreHull Ω a) := ⟨⟨b, hbC⟩, hbY⟩ with hv
  have hu2 : u * u = 1 := by
    have hz2 : z * z = 1 := hz.sq
    apply Subtype.ext; apply Subtype.ext
    simp only [hu, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    calc ((x₀ : ↥(Subgroup.centralizer ({a} : Set G))) : G) * z *
          ((x₀ : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹ *
          (((x₀ : ↥(Subgroup.centralizer ({a} : Set G))) : G) * z *
          ((x₀ : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹) =
          ((x₀ : ↥(Subgroup.centralizer ({a} : Set G))) : G) * (z * z) *
          ((x₀ : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hv2 : v * v = 1 := by
    apply Subtype.ext; apply Subtype.ext
    exact hb.sq
  have hmk : (QuotientGroup.mk u : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)) =
      QuotientGroup.mk v := by
    rw [hu, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact heq
  have huv : u * v ∈ classicalInvolutionOddCore ↥(coreHull Ω a) := by
    have h1 : u⁻¹ * v ∈ classicalInvolutionOddCore ↥(coreHull Ω a) := QuotientGroup.eq.mp hmk
    rwa [inv_eq_of_mul_eq_one_right hu2] at h1
  obtain ⟨n, hn, hnv⟩ := C25Y.exists_conj_of_involutions_odd
    (CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω a)) hu2 hv2 huv
  refine ⟨((n * x₀ : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))), (n * x₀).2, ?_⟩
  have h2 : b = ((((n : ↥(coreHull Ω a)) * u * (n : ↥(coreHull Ω a))⁻¹ : ↥(coreHull Ω a)) :
      ↥(Subgroup.centralizer ({a} : Set G))) : G) := by
    have := congrArg (fun w : ↥(coreHull Ω a) => ((w : ↥(Subgroup.centralizer ({a} : Set G))) : G)) hnv
    simpa [hv] using this
  rw [h2]
  simp only [hu, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  group

end Lift

section SqZ

@[expose] def P25_SqLayer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ cA S R R', a * a = 1 → a ≠ 1 → BadElt z a →
      LayerSq Ω a

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem sqZL_of_layerSq (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hT : TwinThmE.T4Supply) (hbad : BadElt z a)
    (hsq : LayerSq Ω a) {g x : G} (hgC : g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    (hxC : x ∈ Subgroup.centralizer ({a} : Set G)) (hxx : x * x = g * z * g⁻¹) :
    ∃ h : ↥(Subgroup.centralizer ({a} : Set G)), h ∈ coreHull Ω a ∧
      (h : G) * z * (h : G)⁻¹ = g * z * g⁻¹ := by
  classical
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  set xH : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨x, hxC⟩ with hxH
  set tH : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨g * z * g⁻¹, hgC⟩ with htH
  have hxxH : xH * xH = tH := Subtype.ext hxx
  have htt : tH * tH = 1 := by
    apply Subtype.ext
    show (g * z * g⁻¹) * (g * z * g⁻¹) = 1
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  set β := secAct hΩ hc2 xH with hβ
  have hββ : β * β = secAct hΩ hc2 tH := by rw [hβ, ← map_mul, hxxH]
  have hβ4 : ∀ y, β (β (β (β y))) = y := by
    intro y
    have h1 : (β * β) * (β * β) = 1 := by rw [hββ, ← map_mul, htt, map_one]
    have h2 := congrArg (fun φ => φ y) h1
    simpa [MulAut.mul_apply] using h2
  obtain ⟨M, hM, yb, hybM, hyb4, hβyb⟩ := hsq β hβ4
  have hfix : secAct hΩ hc2 tH yb = yb := by
    rw [← hββ, MulAut.mul_apply]
    exact hβyb
  have hyb4' : yb * yb * yb * yb = 1 := by
    have : yb ^ 4 = 1 := by rw [← hyb4]; exact pow_orderOf_eq_one yb
    simpa [pow_succ, mul_assoc] using this
  have hyb2 : yb * yb ≠ 1 := by
    intro h
    have : orderOf yb ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hyb4] at this
    omega
  obtain ⟨J, hJ, hJt⟩ := nc4_lift_sec hyp hΩ hc2 hgC hM hybM hyb4' hyb2 hfix
  exact conj_of_member_sec hyp ha2 ha1 hacA hT hbad hJ hJt

end SqZ

section Global

theorem p25_sqZ_of_layerSq (hT : TwinThmE.T4Supply) (h : P25_SqLayer) : P25S.P25_SqZ := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 _ _ hbad g x hgC hxC hxx _
  obtain ⟨h₀, -, hh₀⟩ := sqZL_of_layerSq hyp ha2 ha1 haA hT hbad
    (h G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad) hgC hxC hxx
  exact ⟨(h₀ : G), h₀.2, hh₀⟩

end Global

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
