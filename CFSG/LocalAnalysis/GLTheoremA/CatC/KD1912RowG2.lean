module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PCore.QuasisimpleNormalCore
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalG2Eight
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Certificates


theorem odd_card_gLAPPrimeCoreOf_inner_G2_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {s : adjointGroup .G2 K} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (innerAut (adjointGroup .G2 K) ⊓
      Subgroup.centralizer ({MulAut.conj s} : Set (MulAut (adjointGroup .G2 K)))))) := by
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAutConj_injective_of_center_eq_bot hZ
  have hNo : CFSG.HardMathSupport.Timmesfeld.CrossChar.NoNormalPPrime 3
      (Subgroup.centralizer ({s} : Set (adjointGroup .G2 K))) :=
    CFSG.HardMathSupport.Dickson.Bal207.noNormalPPrime_centralizer_adjointG2_eight hK hs3 hs1
  rw [innerAut_inf_centralizer_conj hZ s,
    card_gLAPPrimeCoreOf_map_of_injective 3 (MulAut.conj : adjointGroup .G2 K →*
      MulAut (adjointGroup .G2 K)) hinj]
  have hbot : GLAPPrimeCoreOf 3
      (Subgroup.centralizer ({s} : Set (adjointGroup .G2 K))) = ⊥ := by
    refine hNo (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set (adjointGroup .G2 K))))
      (Subgroup.map_subtype_le _) ?_ ?_
    · intro y hy x hx
      exact gLAPPrimeCoreOf_conj_mem' y hy x hx
    · exact coprime_card_gLAPPrimeCoreOf' (p := 3) Nat.prime_three _
  rw [hbot, Subgroup.card_bot]
  exact odd_one

private theorem gLAPPrimeCoreOf_eq_bot_of_fieldCore_data {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hZ : Subgroup.center K = ⊥) {α : MulAut K} {T : Subgroup K}
    (hTF : T ≤ fixSub α) (hTn : ∀ f ∈ fixSub α, ∀ t ∈ T, f * t * f⁻¹ ∈ T)
    (hTq : CFSG.IsQuasisimple ↥T) (hTp : ¬ Nat.Coprime p (Nat.card T))
    (hfaith : ∀ g : MulAut K, Nat.Coprime p (orderOf g) → g * α = α * g →
      (∀ t ∈ T, g t = t) → g = 1) :
    GLAPPrimeCoreOf p (innerAut K ⊓ Subgroup.centralizer ({α} : Set (MulAut K))) = ⊥ := by
  classical
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    mulAutConj_injective_of_center_eq_bot hZ
  set H : Subgroup (MulAut K) :=
    innerAut K ⊓ Subgroup.centralizer ({α} : Set (MulAut K)) with hHdef
  set Tc : Subgroup (MulAut K) := T.map (MulAut.conj : K →* MulAut K) with hTcdef
  have hHfix : H = (fixSub α).map (MulAut.conj : K →* MulAut K) := by
    rw [hHdef, innerAut_inf_centralizer_eq_map_eqLocus hZ α]
    congr 1
  have hTcH : Tc ≤ H := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hHfix]
    exact Subgroup.mem_map_of_mem _ (hTF ht)
  have hTcq : CFSG.IsQuasisimple ↥Tc :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (T.equivMapOfInjective _ hinj) hTq
  have hTcn : ∀ y ∈ H, ∀ x ∈ Tc, y * x * y⁻¹ ∈ Tc := by
    intro y hy x hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [hHfix] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    refine ⟨f * t * f⁻¹, hTn f hf t ht, ?_⟩
    rw [map_mul, map_mul, map_inv]
  set N : Subgroup (MulAut K) := GLAPPrimeCoreOf p H with hNdef
  have hNH : N ≤ H := Subgroup.map_subtype_le _
  have hNconj : ∀ y ∈ H, ∀ x ∈ N, y * x * y⁻¹ ∈ N :=
    fun y hy x hx => gLAPPrimeCoreOf_conj_mem' y hy x hx
  have hNcop : Nat.Coprime p (Nat.card N) := coprime_card_gLAPPrimeCoreOf' hp H
  have hTpTc : ¬ Nat.Coprime p (Nat.card Tc) := by
    rwa [hTcdef, Subgroup.card_map_of_injective (K := T)
      (f := (MulAut.conj : K →* MulAut K)) hinj]
  have hNsub : (N.subgroupOf H).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNconj c.1 c.2 n.1 hn
  have hTcsub : (Tc.subgroupOf H).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hTcn c.1 c.2 n.1 hn
  have hTcq' : CFSG.IsQuasisimple ↥(Tc.subgroupOf H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTcH).symm hTcq
  have hNcop' : Nat.Coprime p (Nat.card ↥(N.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hTpTc' : ¬ Nat.Coprime p (Nat.card ↥(Tc.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTcH).toEquiv]
  have hNcent : N ≤ Subgroup.centralizer (Tc : Set (MulAut K)) := by
    have hcent := le_centralizer_of_isQuasisimple_of_coprime hp hTcq' hNcop' hTpTc'
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hn' : (⟨n, hNH hn⟩ : ↥H) ∈ N.subgroupOf H := hn
    have hl' : (⟨l, hTcH hl⟩ : ↥H) ∈ Tc.subgroupOf H := hl
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.1 (hcent hn') ⟨l, hTcH hl⟩ hl')
  refine eq_bot_iff.2 fun n hn => ?_
  rw [Subgroup.mem_bot]
  have hfixT : ∀ t ∈ T, n t = t := by
    intro t ht
    have hmem : MulAut.conj t ∈ Tc := ⟨t, ht, rfl⟩
    have hc : MulAut.conj t * n = n * MulAut.conj t :=
      Subgroup.mem_centralizer_iff.1 (hNcent hn) (MulAut.conj t) hmem
    have hconj : n * MulAut.conj t * n⁻¹ = MulAut.conj t := by
      rw [← hc]; group
    have heq : n * MulAut.conj t * n⁻¹ = MulAut.conj (n t) := by
      ext x
      simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    exact hinj (by rw [heq] at hconj; exact hconj)
  exact hfaith n (hNcop.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hn))
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hNH hn)).2) hfixT

theorem gLAPPrimeCoreOf_eq_bot_of_outer_G2_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {α : MulAut (adjointGroup .G2 K)} (hα : orderOf α = 3)
    (hout : α ∉ innerAut (adjointGroup .G2 K)) :
    GLAPPrimeCoreOf 3 (innerAut (adjointGroup .G2 K) ⊓
      Subgroup.centralizer ({α} : Set (MulAut (adjointGroup .G2 K)))) = ⊥ := by
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨T, hTF, hTn, hTq, hTp, hfaith⟩ := g2EightFieldCore K hK α hα hout
  exact gLAPPrimeCoreOf_eq_bot_of_fieldCore_data Nat.prime_three hZ hTF hTn hTq hTp hfaith

theorem outTwoNilpConcl_adjointG2_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) :
    CFSG.LieType.ChevTwo.OutTwoNilpConcl (adjointGroup .G2 K) := by
  have hK8 : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      (f := 3) (by norm_num) K hK8
  have hcardAut : Nat.card (K ≃+* K) = 3 := by
    obtain ⟨-, -, -, -, hc, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        (p := 2) (n := 3) Nat.prime_two (by norm_num) hK8
    exact hc
  have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .G2 K) =
      Θ.ker := hker.symm
  let eOut : CFSG.ComponentClassification.OuterAutomorphisms.Outer (adjointGroup .G2 K) ≃*
      (K ≃+* K) :=
    (QuotientGroup.quotientMulEquivOfEq hinner).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  have hodd : Odd (Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (adjointGroup .G2 K))) := by
    rw [Nat.card_congr eOut.toEquiv, hcardAut]
    norm_num
  exact CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer
    (CFSG.Quasithin.H13.OutTwoNilp.twoNilpotent_of_odd hodd)

theorem oddCoreFact_three_adjointG2_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) : OddCoreFact 3 (adjointGroup .G2 K) := by
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAutConj_injective_of_center_eq_bot hZ
  constructor
  · exact outTwoNilpConcl_adjointG2_eight hK
  · intro α hα
    by_cases hinn : α ∈ innerAut (adjointGroup .G2 K)
    · obtain ⟨s, rfl⟩ := hinn
      have hord : orderOf s = 3 := by
        have h1 : orderOf (MulAut.conj s) = orderOf s :=
          orderOf_injective (MulAut.conj : adjointGroup .G2 K →*
            MulAut (adjointGroup .G2 K)) hinj s
        rw [← h1]
        exact hα
      have hs3 : s ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one s
      have hs1 : s ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hord
        norm_num at hord
      exact odd_card_gLAPPrimeCoreOf_inner_G2_eight hK hs3 hs1
    · rw [gLAPPrimeCoreOf_eq_bot_of_outer_G2_eight hK hα hinn, Subgroup.card_bot]
      exact odd_one

theorem oddCoreFact_three_of_G2_eight {q : TauCeti.PrimePower} (hq : q.card = 8)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : OddCoreFact 3 S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGal : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hK : Nat.card (GaloisField 2 3) = q.card := by rw [hGal, hq]
  have hp2 : q.p = 2 := by
    have h1 : q.p ∣ 8 := by
      rw [← hq, TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    have h2 : q.p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 from by norm_num]
      exact h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h2)
  obtain ⟨eQ⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp2
    (GaloisField 2 3) hK
  have hZ : Subgroup.center (adjointGroup .G2 (GaloisField 2 3)) = ⊥ :=
    center_adjointGroup_eq_bot
  let eModel : adjointGroup .G2 (GaloisField 2 3) ≃*
      (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eQ
  exact (oddCoreFact_congr (p := 3) (e.trans eModel.symm)).mpr
    (oddCoreFact_three_adjointG2_eight hGal)

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.KD1912
