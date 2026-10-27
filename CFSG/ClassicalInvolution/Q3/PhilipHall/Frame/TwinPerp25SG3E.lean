module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SG3D
public import CFSG.ClassicalInvolution.Q3.Q3T7P25NC4
public import CFSG.ClassicalInvolution.ModelFacts.L6CFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25L5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25L6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SG3B
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YM01

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


section NC4

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

open scoped commutatorElement

theorem nc4_lift_sec2 (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    {c : G} (hbC : c * z * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    {M : Subgroup (↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a))}
    (hM : M ∈ TwinDisc.secFam Ω a)
    {y : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)}
    (hyM : y ∈ M) (hy4 : y * y * y * y = 1) (hy2 : y * y ≠ 1)
    (hfix : secAct hΩ hc2 ⟨c * z * c⁻¹, hbC⟩ y = y) :
    ∃ w : ↥(coreHull Ω a), ((w : ↥(Subgroup.centralizer ({a} : Set G))) : G) = c * z * c⁻¹ ∧
      (QuotientGroup.mk w : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)) = y * y := by
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
  · have hsq : (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
        (((c0 ^ m : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) = g₁ * z * g₁⁻¹ :=
      layer_sq_of_order_four hzJ₁ hy₁J hy₁4
    obtain ⟨n', hn', hn'eq⟩ := Subgroup.mem_map.mp hn
    refine ⟨n' * (c0 ^ m) * (c0 ^ m) * n'⁻¹, ?_, ?_⟩
    · have hn'G : (((n' : ↥(coreHull Ω a)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) =
          ((n : ↥(Subgroup.centralizer ({a} : Set G))) : G) := congrArg Subtype.val hn'eq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hn'G, hbeq, ← hsq]
      group
    · have h1 : (QuotientGroup.mk n' : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hn'
      have h2 : (QuotientGroup.mk (c0 ^ m) : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)) =
          y ^ m := hπc'
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, h2]
      obtain ⟨j, rfl⟩ := hm
      rw [one_mul, inv_one, mul_one, ← pow_add, show 2 * j + 1 + (2 * j + 1) = 4 * j + 2 by ring,
        pow_add, pow_mul, hy44, one_pow, one_mul, pow_two]
  · exact absurd hycG.symm
      (T7ER.not_commute_of_conj hs hyp.hW hyp.hE4 hJ₀Ω hJ₀z hbeq hyJ' hy4')


theorem nc4_sec_false (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (h2 : ∀ J ∈ TwinDisc.secFam Ω a, IsPGroup 2 J) (hex : ExactSylow (TwinDisc.secFam Ω a))
    {J₁ J₂ : Subgroup (↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a))}
    (hJ₁ : J₁ ∈ liftFam (TwinDisc.secFam Ω a)) (hJ₂ : J₂ ∈ liftFam (TwinDisc.secFam Ω a))
    {y z₂ : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)}
    (hyJ : y ∈ J₁) (hy4 : y * y * y * y = 1) (hy2 : y * y ≠ 1) (hz₂J : z₂ ∈ J₂)
    (hz₂2 : z₂ * z₂ = 1) (hz₂1 : z₂ ≠ 1) (hne : z₂ ≠ y * y) (hcomm : z₂ * y = y * z₂) : False := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  have hS := layer_q8Section hyp ha2
  obtain ⟨M₁, hM₁, hyM₁⟩ := mem_member_of_mem_liftFam hS.hyp h2 hex hJ₁ hyJ hy4
  have hz₂4 : z₂ * z₂ * z₂ * z₂ = 1 := by rw [hz₂2, one_mul, hz₂2]
  obtain ⟨M₂, hM₂, hz₂M₂⟩ := mem_member_of_mem_liftFam hS.hyp h2 hex hJ₂ hz₂J hz₂4
  obtain ⟨N₂, hN₂, rfl⟩ := exists_of_mem_secFam hM₂
  obtain ⟨g₂, hg₂⟩ := hyp.std.1.stand.trans N₂ hN₂.1
  have hzN₂ : IsUniqueInvolution N₂ (g₂ * z * g₂⁻¹) := by
    rw [← hg₂]
    exact hyp.std.setting.hz.conj g₂
  obtain ⟨hbC, hbY, hbb⟩ := isUniqueInvolution_secImg hΩ hc2 hN₂ hzN₂
  have hz₂b : z₂ = QuotientGroup.mk (⟨⟨g₂ * z * g₂⁻¹, hbC⟩, hbY⟩ : ↥(coreHull Ω a)) := by
    rcases hbb.unique z₂ hz₂M₂ hz₂2 with h | h
    · exact absurd h hz₂1
    · exact h
  have hfix : secAct hΩ hc2 ⟨g₂ * z * g₂⁻¹, hbC⟩ y = y := by
    rw [secAct_of_mem hΩ hc2 hbY, MulAut.conj_apply, ← hz₂b, hcomm, mul_assoc, mul_inv_cancel,
      mul_one]
  obtain ⟨w, hw, hwy⟩ := nc4_lift_sec2 hyp hΩ hc2 hbC hM₁ hyM₁ hy4 hy2 hfix
  have hweq : w = ⟨⟨g₂ * z * g₂⁻¹, hbC⟩, hbY⟩ := Subtype.ext (Subtype.ext hw)
  apply hne
  rw [hz₂b, ← hweq, hwy]

theorem genSection_liftFam (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hT : TwinThmE.T4Supply) (hno : SecNoExitAt Ω a) :
    Q3.Q3T8.Asc77.GenSection (liftFam (TwinDisc.secFam Ω a)) := by
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  obtain ⟨h2, hl, hex⟩ := lifts_of_noExit hih.2 hlt hS hno
  obtain ⟨-, hgen, -, -⟩ := layer_lifts hyp ha2 ha1 hacA hT hno
  exact ⟨hypOmegaModU_liftFam hS.hyp.conjInvariant, hS.oddFree, hgen,
    ExactSylow.aEmpty_liftFam hS.hyp h2 hl hex hS.aEmpty⟩

end NC4

section Typing

variable {G : Type} [Group G] [Finite G]

@[expose] def LayerLie (Ω : Set (Subgroup G)) (c : G) (d : ℕ) : Prop :=
  ∃ D : LieSystemData 3 1 (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
      (liftFam (TwinDisc.secFam Ω c)),
    D.card = 1 ∧ ∃ i : Fin D.card, IsOrthTag d true (D.tag i) (D.rank i)

@[expose] def LayerTypedL (Ω : Set (Subgroup G)) (c : G) : Prop :=
  (SecNoExitAt Ω c ∧ (LayerLie Ω c 5 ∨ LayerLie Ω c 6)) ∨ LayerAE5 Ω c

end Typing

section Lift

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem layer_lie_of_noExit (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hT : TwinThmE.T4Supply) (hbad : BadElt z a)
    (hno : SecNoExitAt Ω a) : LayerLie Ω a 5 ∨ LayerLie Ω a 6 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  obtain ⟨h2, hl, hex⟩ := lifts_of_noExit hih.2 hlt hS hno
  obtain ⟨-, hgen, -, -⟩ := layer_lifts hyp ha2 ha1 hacA hT hno
  have hGS := genSection_liftFam hyp ha2 ha1 hacA hT hno
  obtain ⟨htC, htY, A, A', a₀, b₀, htw⟩ := layer_twinSect0 hyp ha2 ha1 hacA hno
  have hBelow : Q3.Q3T8.Generic.CITBelowU (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mpr hih.1
  rcases Q3.Q3T8.Asc77.C25X.twinSection_cases0 hBelow hlt hGS htw with hpair | ⟨D, hcard, i, hsix⟩
  ·
    exfalso
    obtain ⟨hKtq, -, -, -, -, -⟩ := layer_twins_tq hyp hacA
    apply hbad
    refine TwinPerpV3.mem_zStarOf_of_allMembers hΩ hc2 hKtq htC htY ?_
    intro M hM
    obtain ⟨L, u, hL⟩ := hl M hM
    have hsat := satU_mem_liftFam hM hL
    have hu : u = QuotientGroup.mk (⟨⟨z, htC⟩, htY⟩ : ↥(coreHull Ω a)) := by
      have huM : u ∈ satU (.sl2 3 1) L u := hL.le_sat hL.inv.mem
      rcases hpair _ hsat with h | h
      · rw [h] at huM
        rcases htw.hzA.unique u huM hL.inv.sq with h1 | h1
        · exact absurd h1 hL.inv.ne_one
        · exact h1
      · rw [h] at huM
        rcases htw.hzA'.unique u huM hL.inv.sq with h1 | h1
        · exact absurd h1 hL.inv.ne_one
        · exact h1
    have := hL.inv
    rw [hu] at this
    exact this
  · have hπ : (!piSign 3 1) = true := by decide
    let M := Q3.Q3T8.Asc77.T7L.toModelOfGen hGS.hyp D hcard hGS.gen i
    have hS4 : ((D.tag i = .PSU ∧ D.rank i = 4) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
        (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4)) → False := by
      intro hS4
      obtain ⟨J₁, hJ₁, J₂, hJ₂, y, hy, z₂, hz₂, hy4, hy2, hz₂2, hz₂1, hne, hcomm⟩ :=
        Q3.Q3T8.Asc77.C25X.s4_excl Q3.Q3T7P25.nc4Fact3_proved M ⟨_, htw.hA⟩ hS4
      have h2' : ∀ J ∈ TwinDisc.secFam Ω a, IsPGroup 2 J := h2
      exact nc4_sec_false hyp ha2 h2' hex hJ₁ hJ₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
    rcases hsix with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      obtain ⟨D', hD'1, i', ht, hn⟩ := LieSystemData.exists_of_hasLieType hgen
        (⟨D, hcard, i, h1, h2⟩ : HasLieType 3 1 (liftFam (TwinDisc.secFam Ω a)) _ _)
      exact ⟨D', hD'1, i', Or.inl ⟨rfl, ht, hn⟩⟩
    · right
      obtain ⟨D', hD'1, i', ht, hn⟩ := LieSystemData.exists_of_hasLieType hgen
        (⟨D, hcard, i, h1, h2⟩ : HasLieType 3 1 (liftFam (TwinDisc.secFam Ω a)) _ _)
      exact ⟨D', hD'1, i', Or.inr (Or.inl ⟨rfl, rfl, ht, hn⟩)⟩
    · exact (hS4 (Or.inl ⟨h1, h2⟩)).elim
    · exact (hS4 (Or.inr (Or.inl ⟨h1, h2⟩))).elim
    · exact (hS4 (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))).elim
    · exact (hS4 (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))).elim

theorem layerSq_of_layerLie (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hno : SecNoExitAt Ω a)
    (hL : LayerLie Ω a 5 ∨ LayerLie Ω a 6) : LayerSq Ω a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  obtain ⟨h2, -, hex⟩ := lifts_of_noExit hih.2 hlt hS hno
  obtain ⟨htC, htY, A, A', a₀, b₀, htw⟩ := layer_twinSect0 hyp ha2 ha1 hacA hno
  intro β hβ4
  rcases hL with ⟨D, hD1, i, hi⟩ | ⟨D, hD1, i, hi⟩
  · obtain ⟨J, hJ, y, hyJ, hy4, hy2, hβy⟩ :=
      Q3.Q3T8.Asc77.C25W.layer5Sq_proved _ _ D _ _ _ _ _ hD1 ⟨i, hi⟩ htw (liftFam_conj hyp ha2) β hβ4
    obtain ⟨M, hM, hyM⟩ := mem_member_of_mem_liftFam hS.hyp h2 hex hJ hyJ hy4
    exact ⟨M, hM, y, hyM, orderOf_eq_four_of hy4 hy2, hβy⟩
  · have hπ : (!piSign 3 1) = true := by decide
    obtain ⟨J, hJ, y, hyJ, hy4, hy2, hβy⟩ :=
      ModelFacts.L6C.layer6Cen4_proved 3 1 _ _ D _ _ _ _ _ hD1 ⟨i, by rw [hπ]; exact hi⟩ htw
        (liftFam_conj hyp ha2) (β * β) (fun x => by simpa [MulAut.mul_apply] using hβ4 x)
    obtain ⟨M, hM, hyM⟩ := mem_member_of_mem_liftFam hS.hyp h2 hex hJ hyJ hy4
    exact ⟨M, hM, y, hyM, orderOf_eq_four_of hy4 hy2, by simpa [MulAut.mul_apply] using hβy⟩

end Lift

section Global

@[expose] def P25_TypedL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ cA S R R', a * a = 1 → a ≠ 1 → BadElt z a →
      LayerTypedL Ω a

theorem p25_typedL_of_exits (hT : TwinThmE.T4Supply) (hOE : ∀ n, TwinDisc.OddCentEdge n)
    (h2 : P25_TypedO2) (h3 : P25_TypedE4) : P25_TypedL := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad
  rcases layer_trichotomy_of_bad hyp ha2 ha1 haA hT (hOE _) hbad with hno | hO2 | hE4
  · exact Or.inl ⟨hno, layer_lie_of_noExit hyp ha2 ha1 haA hT hbad hno⟩
  · exact Or.inr (h2 G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad hO2)
  · by_cases hO2 : ∃ M ∈ TwinDisc.secFam Ω a,
        ∃ zb : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a),
          IsUniqueInvolution M zb ∧ TightInO2 zb
    · exact Or.inr (h2 G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad hO2)
    · exact (h3 G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad hO2 hE4).elim

theorem p25_sqLayer_of_typedL (hAE : AE5SqModel) (hty : P25_TypedL) : P25_SqLayer := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad
  rcases hty G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad with ⟨hno, hL⟩ | hae
  · exact layerSq_of_layerLie hyp ha2 ha1 haA hno hL
  · exact layerSq_of_ae5 hyp ha2 hAE hae

theorem p25_sqZ_of_exits (hT : TwinThmE.T4Supply) (hOE : ∀ n, TwinDisc.OddCentEdge n)
    (hAE : AE5SqModel) (h2 : P25_TypedO2) (h3 : P25_TypedE4) : P25S.P25_SqZ :=
  p25_sqZ_of_layerSq hT (p25_sqLayer_of_typedL hAE (p25_typedL_of_exits hT hOE h2 h3))

end Global

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
