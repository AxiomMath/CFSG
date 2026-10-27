module

public import CFSG.Sporadic.HNOddCore.FiveF
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Generic

theorem rkBM_exists_sq {C : Type} [Group C] {p : ℕ} (hp : p.Prime) {E : Subgroup C}
    (hE : IsElemAbelian p E) {k : ℕ} (hk : 2 ≤ k) (hc : Nat.card E = p ^ k) :
    ∃ E₀ : Subgroup C, IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) p (n := 2)
    (by rw [hc]; exact pow_dvd_pow p hk)
  have hcard : Nat.card ↥(K.map E.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  refine ⟨K.map E.subtype, ⟨?_, ?_⟩, hcard⟩
  · exact ⟨⟨(IsPGroup.commGroupOfCardEqPrimeSq hcard).mul_comm⟩⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hE.2 _ x.2

theorem rkBM_coprime {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : n ≤ 2) (hpos : 0 < n) :
    Nat.Coprime p n := by
  interval_cases n
  · exact Nat.coprime_one_right p
  · exact (Nat.coprime_primes hp Nat.prime_two).2 hp2

theorem rkBM_rkAut_of_simple {C : Type} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hOut : SporadicOuterLeTwo) {X : TauCeti.SporadicName}
    (b : C ≃* (TauCeti.CFSGIndex.sporadic X).Group) (hsimple : IsSimpleGroup C)
    {E : Subgroup C} (hE : IsElemAbelian p E) {k : ℕ} (hk : 2 ≤ k) (hc : Nat.card E = p ^ k) :
    RkAut p C := by
  obtain ⟨E₀, hE₀, hc₀⟩ := rkBM_exists_sq hp hE hk hc
  have hdvd : p ^ 2 ∣ Nat.card C := by
    rw [← hc₀]
    exact Subgroup.card_subgroup_dvd_card E₀
  have hnab : ∃ a c : C, a * c ≠ c * a := by
    by_contra hcon
    push Not at hcon
    letI : CommGroup C := { (inferInstance : Group C) with mul_comm := hcon }
    have hpr := IsSimpleGroup.prime_card (α := C)
    rcases (Nat.dvd_prime hpr).1 hdvd with h | h
    · have := Nat.one_lt_pow two_ne_zero hp.one_lt
      omega
    · exact Nat.Prime.not_prime_pow (le_refl 2) (h ▸ hpr)
  have hZ := center_eq_bot_of_isSimpleGroup hnab
  have ho := hOut C hsimple hnab X ⟨b⟩
  exact rkAut_of_simple hp hZ (rkBM_coprime hp hp2 ho Nat.card_pos) ⟨E₀, hE₀, hc₀⟩

noncomputable def rkBMQuotBot {T : Type} [Group T] (hZ : Subgroup.center T = ⊥) :
    T ≃* T ⧸ Subgroup.center T :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

theorem rkBM_center_eq_bot (hSpM : SporadicMultipliers) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {s : TauCeti.SporadicName}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hm : sporadicMultiplierOrder s = 1) : Subgroup.center K = ⊥ := by
  have hd := card_center_dvd_multiplier hSpM hq s e
  rw [hm, Nat.dvd_one] at hd
  exact Subgroup.eq_bot_of_card_eq _ hd

end Generic

section Th

theorem rkAut_Th_native (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) :
    RkAut 3 NativeSporadic.Th := by
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Th_elementary_three_rank_four
  exact rkBM_rkAut_of_simple (C := NativeSporadic.Th) Nat.prime_three (by norm_num) hOut
    (hBr .Th).some (CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th
      CFSG.Sporadic.Th.th_kernel_facts) hE (by norm_num : 2 ≤ 4) hc

theorem rkAut_Th_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) {T : Type}
    [Group T] (e : T ≃* (TauCeti.CFSGIndex.sporadic .Th).Group) : RkAut 3 T :=
  rkAut_of_equiv ((hBr .Th).some.trans e.symm) (rkAut_Th_native hOut hBr)

theorem rkAut_Th_three_of_quasisimple (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) {T : Type} [Group T] [Finite T] (hq : CFSG.Open.IsQuasisimple T)
    (e : T ⧸ Subgroup.center T ≃* (TauCeti.CFSGIndex.sporadic .Th).Group) : RkAut 3 T :=
  rkAut_Th_three hOut hBr ((rkBMQuotBot (rkBM_center_eq_bot hSpM hq e rfl)).trans e)

end Th

section HN

theorem rkAut_HN_native (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) :
    RkAut 5 NativeSporadic.HN := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card CFSG.Sporadic.HNSchreier.IJ := by
    rw [CFSG.Sporadic.HNOddCore.card_IJ]
    norm_num
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.Sporadic.HNSchreier.IJ) 5 h5
  have hu5 : (u : ↥CFSG.Sporadic.HNSchreier.JH) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one (u : ↥CFSG.Sporadic.HNSchreier.JH)
    rwa [Subgroup.orderOf_coe, hu] at h
  have hu1 : (u : ↥CFSG.Sporadic.HNSchreier.JH) ≠ 1 := by
    intro h
    have : orderOf (u : ↥CFSG.Sporadic.HNSchreier.JH) = 5 := by rw [Subgroup.orderOf_coe]; exact hu
    rw [h, orderOf_one] at this
    omega
  have hf5 : CFSG.Sporadic.HNSchreier.fJ ^ 5 = 1 := by
    have h := pow_orderOf_eq_one CFSG.Sporadic.HNSchreier.fJ
    rwa [CFSG.Sporadic.HNOddCore.orderOf_fJ] at h
  have hf1 : CFSG.Sporadic.HNSchreier.fJ ≠ 1 := by
    intro h
    have := CFSG.Sporadic.HNOddCore.orderOf_fJ
    rw [h, orderOf_one] at this
    omega
  have huf : (u : ↥CFSG.Sporadic.HNSchreier.JH) ∉ Subgroup.zpowers CFSG.Sporadic.HNSchreier.fJ := by
    intro h
    apply hu1
    have hm : (u : ↥CFSG.Sporadic.HNSchreier.JH) ∈
        Subgroup.zpowers CFSG.Sporadic.HNSchreier.fJ ⊓ CFSG.Sporadic.HNSchreier.IJ :=
      Subgroup.mem_inf.2 ⟨h, u.2⟩
    rw [CFSG.Sporadic.HNOddCore.zpowers_inf_IJ] at hm
    exact Subgroup.mem_bot.1 hm
  have hcomm : (u : ↥CFSG.Sporadic.HNSchreier.JH) * CFSG.Sporadic.HNSchreier.fJ =
      CFSG.Sporadic.HNSchreier.fJ * u :=
    (CFSG.Sporadic.HNOddCore.zpowers_comm_IJ _ (Subgroup.mem_zpowers _) _ u.2).symm
  obtain ⟨hel, hcard⟩ :=
    CFSG.Goldschmidt.G63.sup_zpowers_isElemAbelian Nat.prime_five hu5 hf5 hf1 huf hcomm
  have hsimple : IsSimpleGroup ↥CFSG.Sporadic.HNSchreier.JH :=
    @MulEquiv.isSimpleGroup _ _ NativeSporadic.HN _ CFSG.Sporadic.HN.isSimpleGroup_HN
      CFSG.Sporadic.HNSchreier.hnEquivJ.symm
  haveI : Finite NativeSporadic.HN :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.HN.card_HN]; norm_num)
  haveI : Finite ↥CFSG.Sporadic.HNSchreier.JH :=
    Finite.of_equiv NativeSporadic.HN CFSG.Sporadic.HNSchreier.hnEquivJ.toEquiv
  have hJ : RkAut 5 ↥CFSG.Sporadic.HNSchreier.JH :=
    @rkBM_rkAut_of_simple ↥CFSG.Sporadic.HNSchreier.JH
      (Subgroup.toGroup CFSG.Sporadic.HNSchreier.JH) _ 5 Nat.prime_five (by norm_num) hOut .HN
      (CFSG.Sporadic.HNSchreier.hnEquivJ.symm.trans (hBr .HN).some) hsimple _ hel 2 le_rfl hcard
  exact @rkAut_of_equiv 5 ↥CFSG.Sporadic.HNSchreier.JH NativeSporadic.HN
    (Subgroup.toGroup CFSG.Sporadic.HNSchreier.JH) Units.instGroup
    CFSG.Sporadic.HNSchreier.hnEquivJ.symm hJ

theorem rkAut_HN_five (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) {T : Type}
    [Group T] (e : T ≃* (TauCeti.CFSGIndex.sporadic .HN).Group) : RkAut 5 T :=
  rkAut_of_equiv ((hBr .HN).some.trans e.symm) (rkAut_HN_native hOut hBr)

theorem rkSpor_HN_five_of_quasisimple (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) {T : Type} [Group T] [Finite T] (hq : CFSG.Open.IsQuasisimple T) :
    RkSpor 5 [.HN] T := by
  rintro (⟨h3, -⟩ | ⟨S, hS, ⟨f⟩⟩)
  · norm_num at h3
  · obtain rfl := List.mem_singleton.1 hS
    exact rkAut_HN_five hOut hBr ((rkBMQuotBot (rkBM_center_eq_bot hSpM hq f rfl)).trans f)

end HN

end CFSG.HardMathSupport.Dickson.I271
