module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusNPlus
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusOdd
public import CFSG.ClassicalInvolution.LBalance.Glauberman

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

variable {X : Type} [Group X]

theorem NPlus_le_of_odd [Finite X] (R : Subgroup X) (hR : ∀ x : X, Odd (orderOf x) → x ∈ R) :
    NPlus X ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 X with hO
  set π := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h3 : pCore 3 (X ⧸ O) = ⊥ := pCore_three_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨-, hN1, -⟩ := lemma_2_4_one h3
  obtain ⟨-, hN2, -⟩ := lemma_2_4_two h3
  have hRπ : ∀ x : X ⧸ O, Odd (orderOf x) → x ∈ R.map π := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_odd_lift π hπs hx
    exact ⟨y, hR y hy, hyx⟩
  have hgen : ∀ (Q : Type) [Group Q], GoodQ Q → ∀ N : Subgroup (X ⧸ O), IsCommProd Q N →
      N ≤ R.map π := by
    intro Q _ hQ N hN
    obtain ⟨S, hS, hc, rfl⟩ := hN
    refine le_of_three_of_commProd (fun A hA => hQ.qFacts (hS A hA).some) hc
      fun x hx hx3 => hRπ x ?_
    have : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    exact (by decide : Odd 3).of_dvd_nat this
  have hle : NOne (X ⧸ O) ⊔ NTwo (X ⧸ O) ≤ R.map π :=
    sup_le (hgen SL23 goodQ_SL23 _ hN1) (hgen A4 goodQ_A4 _ hN2)
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  intro x hx
  obtain ⟨r, hr, hrx⟩ := hle hx
  have hxO : r⁻¹ * x ∈ O := (QuotientGroup.eq (s := O)).mp hrx
  have hoR : r⁻¹ * x ∈ R :=
    hR _ (((hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hxO))))
  have : x = r * (r⁻¹ * x) := by group
  rw [this]
  exact R.mul_mem hr hoR

variable {G : Type} [Group G]

theorem caseA [Finite G] (hG : pPrimeCore 2 G = ⊥) (B : Subgroup G) (hB : IsPGroup 2 B)
    (hodd : Odd ((B ⊓ (LPlus G ⊔ pCore 2 G)).relIndex (LPlus G ⊔ pCore 2 G))) :
    ∀ u ∈ NPlusIn (centralizer (B : Set G)), TwoElt u → u ∈ LPlus G ⊔ pCore 2 G := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := LPlus G with hH
  set O2 : Subgroup G := pCore 2 G with hO2
  set M : Subgroup G := H ⊔ O2 with hM
  have hHn : H.Normal := inferInstance
  have hO2n : O2.Normal := pCore_normal
  have hoddH : Odd ((B ⊓ H).relIndex H) :=
    odd_relIndex_of_le (B := B) (H := H) (M := M) le_sup_left hodd
  have hBH2 : IsPGroup 2 ((B ⊓ H).subgroupOf H) := (hB.to_inf_left).comap_subtype
  have hdvd : ¬ 2 ∣ ((B ⊓ H).subgroupOf H).index := by
    have : ((B ⊓ H).subgroupOf H).index = (B ⊓ H).relIndex H := rfl
    rw [this]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hoddH)
  let S : Sylow 2 ↥H := IsPGroup.toSylow hBH2 hdvd
  have hS : (S : Subgroup ↥H) = (B ⊓ H).subgroupOf H := rfl
  have hHcore : pPrimeCore 2 ↥H = ⊥ := pPrimeCore_eq_bot_of_normal hG H
  obtain ⟨N, hNn, hNodd, k, hk⟩ :=
    ClassicalInvolution.glauberman_sylowFixingAut_normal_complement_index hHcore S
  have := hNn
  set Y : Subgroup G := centralizer (B : Set G) with hY
  let Ψ : ↥Y →* MulAut ↥H := (MulAut.conjNormal (H := H)).comp Y.subtype
  have hΨC : ∀ y : ↥Y, Ψ y ∈ ClassicalInvolution.sylowFixingAut (S : Subgroup ↥H) := by
    intro y
    rw [ClassicalInvolution.mem_sylowFixingAut]
    intro s hs
    have hsB : (s : G) ∈ B := (hs : (s : G) ∈ B ⊓ H).1
    have hcomm : (s : G) * y = y * s := Subgroup.mem_centralizer_iff.mp y.2 (s : G) hsB
    apply Subtype.ext
    show (y : G) * s * (y : G)⁻¹ = s
    rw [← hcomm]
    group
  set N' : Subgroup (MulAut ↥H) :=
    N.map (ClassicalInvolution.sylowFixingAut (S : Subgroup ↥H)).subtype with hN'
  have hN'odd : Odd (Nat.card N') := by
    rw [hN', Subgroup.card_map_of_injective
      (ClassicalInvolution.sylowFixingAut (S : Subgroup ↥H)).subtype_injective]
    exact hNodd
  have hodd_mem : ∀ y : ↥Y, Odd (orderOf y) → Ψ y ∈ N' := by
    intro y hy
    have hyC : (⟨Ψ y, hΨC y⟩ : ↥(ClassicalInvolution.sylowFixingAut (S : Subgroup ↥H))) ∈ N := by
      refine mem_of_odd_orderOf_of_index N hk ?_
      rw [Subgroup.orderOf_mk]
      exact hy.of_dvd_nat (orderOf_map_dvd Ψ y)
    exact ⟨_, hyC, rfl⟩
  have hNP : NPlus ↥Y ≤ N'.comap Ψ := NPlus_le_of_odd (N'.comap Ψ) fun y hy => hodd_mem y hy
  have hO2B : O2 ≤ B := by
    have hP : IsPGroup 2 ↥(B ⊔ O2) := hB.to_sup_of_normal_right pCore_isPGroup
    have hBP : B ≤ B ⊔ O2 := le_sup_left
    have hPK : B ⊔ O2 ≤ M ⊔ B := sup_le le_sup_right (le_sup_of_le_left le_sup_right)
    have h1 := Subgroup.relIndex_mul_relIndex (H := B) (K := B ⊔ O2) (L := M ⊔ B) hBP hPK
    have hodd' : Odd (B.relIndex (M ⊔ B)) := by
      rw [sup_comm M B, relIndex_sup_eq (H := M) B]
      exact hodd
    rw [← h1] at hodd'
    have hodd1 : Odd (B.relIndex (B ⊔ O2)) := (Nat.odd_mul.mp hodd').1
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hdvd2 : B.relIndex (B ⊔ O2) ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card B (B ⊔ O2)
    have hcop : Nat.Coprime (B.relIndex (B ⊔ O2)) (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd1)
    have hle : B ⊔ O2 ≤ B := Subgroup.relIndex_eq_one.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd2)
    exact le_sup_right.trans hle
  have hLayer : layer G ≤ H := by
    rw [hH, LPlus_eq_EPlus hG]
    exact le_sup_left.trans le_sup_left
  have hgF : generalizedFitting G ≤ M := by
    rw [generalizedFitting, Fitting_eq_pcore G 2 hG]
    exact sup_le le_sup_right (hLayer.trans le_sup_left)
  intro u hu h2u
  obtain ⟨y, hy, rfl⟩ := hu
  have hy2 : TwoElt y := TwoElt.of_injective (f := Y.subtype) Y.subtype_injective h2u
  have hΨy : Ψ y ∈ N' := hNP hy
  have hΨ1 : Ψ y = 1 := eq_one_of_twoElt_of_odd_card N' hN'odd hΨy (hy2.map Ψ)
  have hHle : H ≤ centralizer ({(y : G)} : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have e := congrArg (fun φ : MulAut ↥H => ((φ ⟨h, hh⟩ : ↥H) : G)) hΨ1
    have e' : (y : G) * h * (y : G)⁻¹ = h := by simpa [Ψ] using e
    rw [mul_inv_eq_iff_eq_mul] at e'
    exact e'
  have hO2le : O2 ≤ centralizer ({(y : G)} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (Subgroup.mem_centralizer_iff.mp y.2 z (hO2B hz)).symm
  have hMle : M ≤ centralizer ({(y : G)} : Set G) := sup_le hHle hO2le
  have hcM : (y : G) ∈ centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have := Subgroup.mem_centralizer_iff.mp (hMle hm) (y : G) rfl
    exact this.symm
  have hfit : (y : G) ∈ generalizedFitting G :=
    centralizer_generalizedFitting_le G
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hgF) hcM)
  exact hgF hfit

end CFSG.OddStandard.Solomon75
