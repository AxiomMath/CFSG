module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase4Ext
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase3Finite

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open MulAction
open CFSG.Quasithin.AutQ8D8 (fixSub mem_fixSub fixedPoints_zpowers card_fixSub_eq_two)

theorem three_le_card_fixSub_of_order_three {Q : Type*} [Group Q] [Finite Q]
    (hT : Nat.card {x : Q // x * x = 1} = 12) {g : MulAut Q} (hg : orderOf g = 3) :
    3 ≤ Nat.card (fixSub g) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg]; simp)
  let Tsub : SubMulAction (Subgroup.zpowers g) Q :=
    { carrier := {x | x * x = 1}
      smul_mem' := fun c x hx => by
        have : (c : MulAut Q) x * (c : MulAut Q) x = 1 := by
          rw [← map_mul, show x * x = 1 from hx, map_one]
        exact this }
  have h := hP.card_modEq_card_fixedPoints Tsub
  have hcard : Nat.card Tsub = 12 := hT
  have hle : Nat.card (fixedPoints (Subgroup.zpowers g) Tsub) ≤ Nat.card (fixSub g) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨x.1.1, ?_⟩ : fixSub g)) ?_
    · have hx := x.2 ⟨g, Subgroup.mem_zpowers g⟩
      refine mem_fixSub.mpr ?_
      have h := congrArg (fun y : Tsub => (y : Q)) hx
      simpa using h
    · intro x y hxy
      have h2 := congrArg (fun z : fixSub g => (z : Q)) hxy
      exact Subtype.ext (Subtype.ext h2)
  have hpos : 0 < Nat.card (fixedPoints (Subgroup.zpowers g) Tsub) := by
    haveI : Nonempty (fixedPoints (Subgroup.zpowers g) Tsub) := by
      refine ⟨⟨⟨(1 : Q), ?_⟩, ?_⟩⟩
      · show (1 : Q) * (1 : Q) = 1
        simp
      · intro c
        apply Subtype.ext
        simpa using map_one (c : MulAut Q)
    exact Nat.card_pos
  rw [hcard] at h
  unfold Nat.ModEq at h
  omega

theorem le_normalizer_of_conjNormal_eq_one {X : Type*} [Group X] {N Q : Subgroup X}
    [N.Normal] {q : X} (hQ : Subgroup.zpowers q = Q)
    (hq : MulAut.conjNormal (H := N) q = 1) :
    N ≤ Subgroup.normalizer (Q : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro n hn p hp
  have hcent : ∀ m : N, q * (m : X) = (m : X) * q := by
    intro m
    have hval : q * (m : X) * q⁻¹ = (m : X) := by
      have h := congrArg (fun f : MulAut N => (f m : N)) hq
      simpa [MulAut.conjNormal_apply] using congrArg (fun y : N => (y : X)) h
    calc q * (m : X) = (q * (m : X) * q⁻¹) * q := by group
      _ = (m : X) * q := by rw [hval]
  have hp' : p ∈ Subgroup.zpowers q := by rwa [hQ]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp'
  have hcomm : (n : X) * p = p * (n : X) := by
    rw [← hk]
    exact ((show Commute q (n : X) from hcent ⟨n, hn⟩).zpow_left k).eq.symm
  have heq : (n : X) * p * (n : X)⁻¹ = p := by
    calc (n : X) * p * (n : X)⁻¹ = p * (n : X) * (n : X)⁻¹ := by rw [hcomm]
      _ = p := by group
  rw [heq]
  exact hp


theorem mem_normalizer_of_conj_eq_self {X : Type*} [Group X] {x : X} {P : Subgroup X}
    [Finite P] (h : ∀ p ∈ P, x * p * x⁻¹ = p) : x ∈ Subgroup.normalizer (P : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : P.map (MulAut.conj x) ≤ P := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
    change x * q * x⁻¹ ∈ P
    rw [h q hq]
    exact hq
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  change Nat.card P ≤ Nat.card (P.map (MulAut.conj x).toMonoidHom)
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
    (MulAut.conj x).injective]

theorem threeTenCase4ExtSylowFiveNontrivialInput_holds :
    ThreeTenCase4ExtSylowFiveNontrivialInput := by
  intro X _ _ N _ P E hNtype hA5 hP hE hPn hEn
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hNcard : Nat.card N = 32 := natCard_of_isQ8D8Type hNtype
  have hZcard : Nat.card (Subgroup.center N) = 2 := natCard_center_of_isQ8D8Type hNtype
  have hInvol : Nat.card {x : N // x * x = 1} = 12 :=
    natCard_involutions_of_isQ8D8Type hNtype
  obtain ⟨eN⟩ := hA5
  have hXcard : Nat.card X = 1920 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hNcard]
    have h60 : Nat.card (X ⧸ N) = 60 := by
      rw [Nat.card_congr eN.toEquiv]
      exact natCard_alternatingGroup_fin_five
    rw [h60]
  have hPcard : Nat.card P = 3 := by
    rw [hP.card_eq, Subgroup.card_top, hXcard]
    decide +kernel
  have hEcard : Nat.card E = 5 := by
    rw [hE.card_eq, Subgroup.card_top, hXcard]
    decide +kernel
  haveI hPnt : Nontrivial P :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hPcard]; norm_num)
  obtain ⟨p0, hp0ne⟩ := exists_ne (1 : P)
  have hp0ordP : orderOf p0 = 3 := by
    have hdvd : orderOf p0 ∣ 3 := by
      have := orderOf_dvd_natCard p0
      rwa [hPcard] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hp0ne
    · exact h3
  have hp0ordX : orderOf ((p0 : P) : X) = 3 := by
    rw [Subgroup.orderOf_coe, hp0ordP]
  have hPzX : Subgroup.zpowers ((p0 : P) : X) = P := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr p0.2) ?_
    rw [Nat.card_zpowers, hp0ordX, hPcard]
  haveI hEnt : Nontrivial E :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hEcard]; norm_num)
  obtain ⟨e0, he0ne⟩ := exists_ne (1 : E)
  have he0ordE : orderOf e0 = 5 := by
    have hdvd : orderOf e0 ∣ 5 := by
      have := orderOf_dvd_natCard e0
      rwa [hEcard] at this
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) he0ne
    · exact h5
  have he0ordX : orderOf ((e0 : E) : X) = 5 := by
    rw [Subgroup.orderOf_coe, he0ordE]
  have hEzX : Subgroup.zpowers ((e0 : E) : X) = E := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr e0.2) ?_
    rw [Nat.card_zpowers, he0ordX, hEcard]
  let βP : MulAut N := MulAut.conjNormal (H := N) ((p0 : P) : X)
  let βE : MulAut N := MulAut.conjNormal (H := N) ((e0 : E) : X)
  have hβPne : βP ≠ 1 := by
    intro hβ
    exact hPn (le_normalizer_of_conjNormal_eq_one hPzX hβ)
  have hβEne : βE ≠ 1 := by
    intro hβ
    exact hEn (le_normalizer_of_conjNormal_eq_one hEzX hβ)
  have hβP3 : orderOf βP = 3 := by
    have hdvd : orderOf βP ∣ 3 := by
      rw [← hp0ordX]
      exact orderOf_map_dvd (MulAut.conjNormal (H := N)) ((p0 : P) : X)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hβPne
    · exact h3
  have hβE5 : orderOf βE = 5 := by
    have hdvd : orderOf βE ∣ 5 := by
      rw [← he0ordX]
      exact orderOf_map_dvd (MulAut.conjNormal (H := N)) ((e0 : E) : X)
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hβEne
    · exact h5
  let W : Subgroup X :=
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X)
  have hPleW : P ≤ W := Subgroup.le_normalizer.trans le_sup_left
  have hEleW : E ≤ W := Subgroup.le_normalizer.trans le_sup_right
  have hWsupN : W ⊔ N = ⊤ := by
    let π : X →* X ⧸ N := QuotientGroup.mk' N
    have hpW : ((p0 : P) : X) ∈ W := hPleW p0.2
    have heW : ((e0 : E) : X) ∈ W := hEleW e0.2
    have hpN : ((p0 : P) : X) ∉ N := by
      intro hmem
      have h : orderOf ((p0 : P) : X) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmem
      rw [hp0ordX, hNcard] at h
      norm_num at h
    have heN : ((e0 : E) : X) ∉ N := by
      intro hmem
      have h : orderOf ((e0 : E) : X) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmem
      rw [he0ordX, hNcard] at h
      norm_num at h
    have hπp : orderOf (π ((p0 : P) : X)) = 3 := by
      have hdvd : orderOf (π ((p0 : P) : X)) ∣ 3 := by
        rw [← hp0ordX]
        exact orderOf_map_dvd π _
      have hne : π ((p0 : P) : X) ≠ 1 := by
        intro h1
        exact hpN ((QuotientGroup.eq_one_iff _).mp h1)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact h3
    have hπe : orderOf (π ((e0 : E) : X)) = 5 := by
      have hdvd : orderOf (π ((e0 : E) : X)) ∣ 5 := by
        rw [← he0ordX]
        exact orderOf_map_dvd π _
      have hne : π ((e0 : E) : X) ≠ 1 := by
        intro h1
        exact heN ((QuotientGroup.eq_one_iff _).mp h1)
      rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact h5
    have hYmap : W.map π = ⊤ := by
      refine eq_top_of_order_three_and_five_of_mulEquiv (e := eN) (H := W.map π) ?_ ?_
      · exact ⟨π ((p0 : P) : X), Subgroup.mem_map_of_mem π hpW, hπp⟩
      · exact ⟨π ((e0 : E) : X), Subgroup.mem_map_of_mem π heW, hπe⟩
    have h := congrArg (Subgroup.comap π) hYmap
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
    exact h
  let HN : Subgroup N := W.comap N.subtype
  have hHN_mem : ∀ x : N, x ∈ HN ↔ (x : X) ∈ W := by
    intro x
    change N.subtype x ∈ W ↔ (x : X) ∈ W
    rfl
  have hcenter_le_fixP : Subgroup.center N ≤ fixSub βP := by
    intro z hz
    exact mem_fixSub.mpr (CFSG.GroupTheory.mulAut_apply_eq_of_mem_center hZcard βP hz)
  have hfixP_le_HN : fixSub βP ≤ HN := by
    intro x hx
    rw [hHN_mem]
    have hxfix : βP x = x := mem_fixSub.mp hx
    have hconj : ∀ p ∈ P, (x : X) * p * (x : X)⁻¹ = p := by
      intro p hp
      have hp' : p ∈ Subgroup.zpowers ((p0 : P) : X) := by rwa [hPzX]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp'
      have hval : ((βP x : N) : X) = ((p0 : P) : X) * (x : X) * ((p0 : P) : X)⁻¹ := by
        simpa [βP] using MulAut.conjNormal_apply (H := N) ((p0 : P) : X) x
      have h := congrArg (fun y : N => (y : X)) hxfix
      rw [hval] at h
      have hcomm0 : ((p0 : P) : X) * (x : X) = (x : X) * ((p0 : P) : X) := by
        calc ((p0 : P) : X) * (x : X) =
            (((p0 : P) : X) * (x : X) * ((p0 : P) : X)⁻¹) * ((p0 : P) : X) := by group
          _ = (x : X) * ((p0 : P) : X) := by rw [h]
      have hcomm : (x : X) * p = p * (x : X) := by
        rw [← hk]
        exact ((show Commute ((p0 : P) : X) (x : X) from hcomm0).zpow_left k).eq.symm
      calc (x : X) * p * (x : X)⁻¹ = p * (x : X) * (x : X)⁻¹ := by rw [hcomm]
        _ = p := by group
    exact Subgroup.mem_sup_left (mem_normalizer_of_conj_eq_self hconj)
  have hcenter_le_HN : Subgroup.center N ≤ HN := hcenter_le_fixP.trans hfixP_le_HN
  have hfixP_big : 3 ≤ Nat.card (fixSub βP) :=
    three_le_card_fixSub_of_order_three hInvol hβP3
  have hFixE : fixSub βE = Subgroup.center N := by
    have hcard : Nat.card (fixSub βE) = 2 :=
      card_fixSub_eq_two hNcard hβEne ⟨1, by simpa using hβE5⟩
    have hle : Subgroup.center N ≤ fixSub βE := by
      intro z hz
      exact mem_fixSub.mpr (CFSG.GroupTheory.mulAut_apply_eq_of_mem_center hZcard βE hz)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hZcard])).symm
  have hHN_inv : ∀ x : N, x ∈ HN → βE x ∈ HN := by
    intro x hx
    rw [hHN_mem] at hx ⊢
    have heW : ((e0 : E) : X) ∈ W := hEleW e0.2
    have hmem : ((e0 : E) : X) * (x : X) * ((e0 : E) : X)⁻¹ ∈ W :=
      W.mul_mem (W.mul_mem heW hx) (W.inv_mem heW)
    have hval : ((βE x : N) : X) = ((e0 : E) : X) * (x : X) * ((e0 : E) : X)⁻¹ := by
      simpa [βE] using MulAut.conjNormal_apply (H := N) ((e0 : E) : X) x
    rwa [hval]
  have hHNmap : HN.map βE.toMonoidHom = HN := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact hHN_inv x hx
    · rw [Subgroup.card_map_of_injective (f := βE.toMonoidHom) βE.injective]
  let βHN : MulAut HN :=
    (Subgroup.equivMapOfInjective HN βE.toMonoidHom βE.injective).trans
      (MulEquiv.subgroupCongr hHNmap)
  have hβHN_apply : ∀ x : HN, ((βHN x : HN) : N) = βE (x : N) := by
    intro x
    rfl
  have hβEpow : βE ^ 5 = 1 := by
    rw [← hβE5]
    exact pow_orderOf_eq_one βE
  have hβHNpow : βHN ^ 5 = 1 := by
    ext x
    have hpow : ∀ k : ℕ, (((βHN ^ k) x : HN) : N) = (βE ^ k) (x : N) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', MulAut.mul_apply, hβHN_apply, ih, pow_succ', MulAut.mul_apply]
    rw [hpow 5, hβEpow]
    simp
  have hβHN_dvd : orderOf βHN ∣ 5 :=
    orderOf_dvd_iff_pow_eq_one.mpr hβHNpow
  have hZpE : IsPGroup 5 (Subgroup.zpowers βHN) := by
    obtain ⟨k, -, hk⟩ :=
      (Nat.dvd_prime_pow (p := 5) (m := 1) Nat.prime_five).1 (by simpa using hβHN_dvd)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hfixHN_card : Nat.card (fixSub βHN) = 2 := by
    rw [← hZcard]
    refine Nat.card_congr ?_
    refine
      { toFun := fun x =>
          ⟨((x.1 : HN) : N), ?_⟩
        invFun := fun z => ⟨⟨z.1, hcenter_le_HN z.2⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx : βHN x.1 = x.1 := mem_fixSub.mp x.2
      have hxE : βE ((x.1 : HN) : N) = ((x.1 : HN) : N) := by
        have := congrArg (fun y : HN => (y : N)) hx
        simpa [hβHN_apply] using this
      have hmem : ((x.1 : HN) : N) ∈ fixSub βE := mem_fixSub.mpr hxE
      rwa [hFixE] at hmem
    · rw [mem_fixSub]
      apply Subtype.ext
      rw [hβHN_apply]
      exact CFSG.GroupTheory.mulAut_apply_eq_of_mem_center hZcard βE z.2
    · intro x
      apply Subtype.ext
      rfl
    · intro z
      apply Subtype.ext
      rfl
  have hfp_card : Nat.card (fixedPoints (Subgroup.zpowers βHN) HN) = 2 := by
    rw [fixedPoints_zpowers βHN]
    exact hfixHN_card
  have hHN_mod : Nat.card HN ≡ 2 [MOD 5] := by
    have hmod := hZpE.card_modEq_card_fixedPoints HN
    rwa [hfp_card] at hmod
  have hHN_gt : 2 < Nat.card HN := by
    have hle : Nat.card (fixSub βP) ≤ Nat.card HN := Subgroup.card_le_of_le hfixP_le_HN
    omega
  have hHN_dvd : Nat.card HN ∣ 32 := by
    have := Subgroup.card_subgroup_dvd_card HN
    rwa [hNcard] at this
  have hHN_card : Nat.card HN = 32 := by
    obtain ⟨j, hj5, hcard⟩ :=
      (Nat.dvd_prime_pow (p := 2) (m := 5) Nat.prime_two).1 (by simpa using hHN_dvd)
    interval_cases j
    · rw [hcard] at hHN_mod
      norm_num at hHN_mod
    · rw [hcard] at hHN_gt
      norm_num at hHN_gt
    · rw [hcard] at hHN_mod
      norm_num at hHN_mod
    · rw [hcard] at hHN_mod
      norm_num at hHN_mod
    · rw [hcard] at hHN_mod
      norm_num at hHN_mod
    · rw [hcard]; norm_num
  have hHN_top : HN = ⊤ :=
    Subgroup.eq_top_of_card_eq HN (by rw [hHN_card, hNcard])
  have hNleW : N ≤ W := by
    intro n hn
    have hmem : (⟨n, hn⟩ : N) ∈ HN := by rw [hHN_top]; exact Subgroup.mem_top _
    rw [hHN_mem] at hmem
    simpa using hmem
  have hWtop : W = ⊤ := by
    have h := hWsupN
    rw [sup_eq_left.mpr hNleW] at h
    exact h
  exact hWtop

theorem threeTenCase4ExtFiniteInput : ThreeTenCase4ExtFiniteInput :=
  threeTenCase4ExtFiniteInput_of_sylowFiveNontrivial
    threeTenCase4ExtSylowFiveNontrivialInput_holds

end CFSG.LocalAnalysis.AGL81I.Section3
