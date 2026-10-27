module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase234
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSmallCards
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneCaseNSQuot
public import CFSG.Quasithin.EmptyFaithful.S1421QA5Fix
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.RankThree.PartOne.S9.QD32.Basic

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThree.PartOne.QD32Facts
open CFSG.RankThree.GroupTheory
open CFSG.RankThree.GroupTheory.SteinbergBY

attribute [local instance] qdFintypeD

local instance : DecidableRel (QuotientGroup.leftRel quaternionDihedralDiagonal).r :=
  fun x y => decidable_of_iff (qdSameImage x y)
    (QuotientGroup.leftRel_apply.trans
      (mem_zpowers_of_orderOf_eq_two orderOf_quaternionDihedralZ)).symm

local instance : DecidableEq QD32 :=
  Quotient.decidableEq (d := inferInstance)

theorem natCard_center_qd32 : Nat.card (Subgroup.center QD32) = 2 := by
  rw [center_QD32, Nat.card_zpowers, orderOf_qd32Z]

theorem natCard_involutions_qd32 : Nat.card {x : QD32 // x * x = 1} = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem natCard_center_of_isQ8D8Type {N : Type} [Group N] (hN : IsQ8D8Type N) :
    Nat.card (Subgroup.center N) = 2 := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.nonempty_mulEquiv_QD32_of_isQ8D8Type
    hN (natCard_of_isQ8D8Type hN)
  have hmap : Subgroup.map e.toMonoidHom (Subgroup.center N) = Subgroup.center QD32 :=
    Subgroup.map_center_eq e
  rw [← Subgroup.card_map_of_injective (K := Subgroup.center N) (f := e.toMonoidHom) e.injective,
    hmap, natCard_center_qd32]

theorem natCard_involutions_of_isQ8D8Type {N : Type} [Group N] (hN : IsQ8D8Type N) :
    Nat.card {x : N // x * x = 1} = 12 := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.nonempty_mulEquiv_QD32_of_isQ8D8Type
    hN (natCard_of_isQ8D8Type hN)
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => ?_))).trans
    natCard_involutions_qd32
  constructor
  · intro hx
    show e x * e x = 1
    rw [← map_mul, hx, map_one]
  · intro hx
    apply e.injective
    calc e (x * x) = e x * e x := map_mul e x x
      _ = 1 := hx
      _ = e 1 := (map_one e).symm

theorem characteristic_of_isQ8D8Type_of_card {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hN : IsQ8D8Type N) (hXcard : Nat.card X = 160) :
    N.Characteristic := by
  have hNcard : Nat.card N = 32 := natCard_of_isQ8D8Type hN
  have hNp : IsPGroup 2 N := IsPGroup.of_card (n := 5) (by rw [hNcard]; norm_num)
  have hindex : N.index = 5 := by
    rw [Subgroup.index_eq_card_div, hXcard, hNcard]
  have hnot : ¬ 2 ∣ N.index := by rw [hindex]; norm_num
  let P : Sylow 2 X := hNp.toSylow hnot
  have hPcoe : (P : Subgroup X) = N := IsPGroup.toSylow_coe hNp hnot
  have hPnormal : (P : Subgroup X).Normal := by
    simpa [hPcoe] using (inferInstance : N.Normal)
  have hPchar : P.Characteristic := Sylow.characteristic_of_normal P hPnormal
  simpa [hPcoe] using hPchar

theorem threeTenCase3Z5Sylow {X : Type} [Group X] [Finite X]
    (hX : IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) X)
    (P E : Subgroup X) (d : ℕ) (hd : d.Prime) (hd2 : d ≠ 2) (hd5 : d ≠ 5)
    (hP : CFSG.ABGLocalTools.IsSylowOf 5 P ⊤)
    (hE : CFSG.ABGLocalTools.IsSylowOf d E ⊤) :
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤ := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hXcard : Nat.card X = 160 := natCard_of_isExtNotation_zmod_five_q8d8 hX
  have hndvd : ¬ d ∣ Nat.card X := by
    rw [hXcard]
    intro h
    have h' : d ∣ 2 ^ 5 * 5 := by
      rwa [show 2 ^ 5 * 5 = 160 by norm_num]
    rcases hd.dvd_mul.mp h' with h2 | h5
    · have h2' : d ∣ 2 := hd.dvd_of_dvd_pow h2
      exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2')
    · exact hd5 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h5)
  have hEcard : Nat.card E = 1 := by
    rw [hE.card_eq, Subgroup.card_top,
      Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
  have hEbot : E = ⊥ := Subgroup.eq_bot_of_card_eq E hEcard
  rw [hEbot]
  have hbot : Subgroup.normalizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
    Subgroup.normalizer_eq_top (⊥ : Subgroup X)
  rw [hbot, sup_top_eq]

theorem no_order_of_commute_order_five {N : Type} [Group N] [Finite N]
    (hN : IsQ8D8Type N)
    {β γ : MulAut N} (hβ1 : β ≠ 1) (hβ5 : orderOf β = 5)
    (hcomm : γ * β = β * γ)
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd5 : d ≠ 5)
    (hγd : orderOf γ = d) : False := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  have hNcard : Nat.card N = 32 := natCard_of_isQ8D8Type hN
  have hCenter : Nat.card (Subgroup.center N) = 2 := natCard_center_of_isQ8D8Type hN
  have hInv : Nat.card {x : N // x * x = 1} = 12 := natCard_involutions_of_isQ8D8Type hN
  have hγ1 : γ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hγd
    exact hd.ne_one hγd.symm
  have hCenter_le_fixβ : Subgroup.center N ≤ CFSG.Quasithin.AutQ8D8.fixSub β := by
    intro z hz
    rw [CFSG.Quasithin.AutQ8D8.mem_fixSub]
    exact CFSG.GroupTheory.mulAut_apply_eq_of_mem_center hCenter β hz
  have hFixβ_card : Nat.card (CFSG.Quasithin.AutQ8D8.fixSub β) = 2 :=
    CFSG.Quasithin.AutQ8D8.card_fixSub_eq_two hNcard hβ1 ⟨1, hβ5⟩
  have hFixβ' : Subgroup.center N = CFSG.Quasithin.AutQ8D8.fixSub β :=
    Subgroup.eq_of_le_of_card_ge hCenter_le_fixβ (by rw [hFixβ_card, hCenter])
  have hFixβ : CFSG.Quasithin.AutQ8D8.fixSub β = Subgroup.center N := hFixβ'.symm
  have hCenter_le_fixγ : Subgroup.center N ≤ CFSG.Quasithin.AutQ8D8.fixSub γ := by
    intro z hz
    rw [CFSG.Quasithin.AutQ8D8.mem_fixSub]
    exact CFSG.GroupTheory.mulAut_apply_eq_of_mem_center hCenter γ hz
  let C : Subgroup N := CFSG.Quasithin.AutQ8D8.fixSub γ
  have hCenter_le_C : Subgroup.center N ≤ C := hCenter_le_fixγ
  have hcomm' : ∀ z : N, β (γ z) = γ (β z) := by
    intro z
    have h := congrArg (fun f : MulAut N => f z) hcomm
    simpa [MulAut.mul_apply] using h.symm
  have hβCmap : C.map β.toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change β y ∈ CFSG.Quasithin.AutQ8D8.fixSub γ
      change y ∈ CFSG.Quasithin.AutQ8D8.fixSub γ at hy
      rw [CFSG.Quasithin.AutQ8D8.mem_fixSub] at hy ⊢
      rw [← hcomm' y, hy]
    · intro hx
      refine ⟨β.symm x, ?_, by simp⟩
      change β.symm x ∈ CFSG.Quasithin.AutQ8D8.fixSub γ
      rw [CFSG.Quasithin.AutQ8D8.mem_fixSub] at hx ⊢
      have hβγ : Commute β γ := hcomm.symm
      have hγβ' : Commute γ β.symm := hβγ.symm.inv_right
      have h := congrArg (fun f : MulAut N => f x) hγβ'.eq
      simpa [MulAut.mul_apply, hx] using h
  let βC : MulAut C :=
    (MulEquiv.subgroupMap β C).trans (MulEquiv.subgroupCongr hβCmap)
  have hβC_apply : ∀ x : C, (βC x : N) = β x := by
    intro x
    rfl
  have hβ5pow : β ^ 5 = 1 := by
    rw [← hβ5]
    exact pow_orderOf_eq_one β
  have hβCpow : ∀ n : ℕ, ∀ x : C, ((βC ^ n) x : N) = (β ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
        intro x
        calc ((βC ^ (n + 1)) x : N)
            = ((βC ^ n * βC) x : N) := by rw [pow_succ]
          _ = ((βC ^ n) (βC x) : N) := rfl
          _ = (β ^ n) (βC x) := ih (βC x)
          _ = (β ^ n) (β x) := by rw [hβC_apply]
          _ = (β ^ (n + 1)) x := rfl
  have hβC5 : βC ^ 5 = 1 := by
    apply MulEquiv.ext
    intro x
    exact Subtype.ext (by simpa [hβ5pow] using hβCpow 5 x)
  have hβCdvd : orderOf βC ∣ 5 := orderOf_dvd_of_pow_eq_one hβC5
  have hCcard : Nat.card C = 2 := by
    by_cases hβC1 : βC = 1
    · have hC_le_fixβ : C ≤ CFSG.Quasithin.AutQ8D8.fixSub β := by
        intro x hx
        rw [CFSG.Quasithin.AutQ8D8.mem_fixSub]
        have hx' : βC ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hβC1]; rfl
        have h := congrArg Subtype.val hx'
        rw [hβC_apply] at h
        exact h
      have hle : C ≤ Subgroup.center N := hFixβ ▸ hC_le_fixβ
      have hCeq : C = Subgroup.center N := le_antisymm hle hCenter_le_C
      rw [hCeq]
      show Nat.card (Subgroup.center N) = 2
      exact hCenter
    · have hβCorder : orderOf βC = 5 := by
        rcases (Nat.dvd_prime Nat.prime_five).mp hβCdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hβC1
        · exact h
      haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      have hmod := CFSG.Quasithin.AutQ8D8.card_modEq_fixSub βC (r := 5) (k := 1)
        (by simpa using hβCorder)
      have hfixC : Nat.card (CFSG.Quasithin.AutQ8D8.fixSub βC) = 2 := by
        have hCfix : C ⊓ CFSG.Quasithin.AutQ8D8.fixSub β = Subgroup.center N := by
          rw [hFixβ]
          exact inf_eq_right.mpr hCenter_le_C
        let e : CFSG.Quasithin.AutQ8D8.fixSub βC ≃
            ((C ⊓ CFSG.Quasithin.AutQ8D8.fixSub β : Subgroup N)) :=
          { toFun := fun x =>
              ⟨(x.1 : N), x.1.2, by
                have hx2 : βC x.1 = x.1 :=
                  (CFSG.Quasithin.AutQ8D8.mem_fixSub).mp x.2
                have h : β (x.1 : N) = x.1 := by
                  have := congrArg Subtype.val hx2
                  simpa [hβC_apply] using this
                simpa [CFSG.Quasithin.AutQ8D8.mem_fixSub] using h⟩
            invFun := fun x =>
              ⟨⟨x.1, x.2.1⟩, by
                have h : βC ⟨x.1, x.2.1⟩ = ⟨x.1, x.2.1⟩ := by
                  apply Subtype.ext
                  rw [hβC_apply]
                  exact (CFSG.Quasithin.AutQ8D8.mem_fixSub).mp x.2.2
                simpa [CFSG.Quasithin.AutQ8D8.mem_fixSub] using h⟩
            left_inv := fun x => rfl
            right_inv := fun x => rfl }
        rw [Nat.card_congr e, hCfix, hCenter]
      rw [hfixC] at hmod
      have hCdvd : Nat.card C ∣ 32 := by
        rw [← hNcard]
        exact CFSG.Quasithin.AutQ8D8.card_fixSub_dvd γ
      have hClt : Nat.card C < 32 := by
        rw [← hNcard]
        exact CFSG.Quasithin.AutQ8D8.card_fixSub_lt hγ1
      have hCge : 2 ≤ Nat.card C := by
        have := Subgroup.card_le_of_le hCenter_le_C
        rwa [hCenter] at this
      rw [show (32 : ℕ) = 2 ^ 5 by norm_num] at hCdvd
      obtain ⟨j, hj, hCj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hCdvd
      rw [hCj] at hClt hCge hmod ⊢
      interval_cases j
      · norm_num at hmod
      · rfl
      · norm_num at hmod
      · norm_num at hmod
      · norm_num at hmod
      · norm_num at hClt
  have hCeq : C = Subgroup.center N :=
    (Subgroup.eq_of_le_of_card_ge hCenter_le_C (by rw [hCcard, hCenter])).symm
  let T := {x : N // x * x = 1}
  letI : MulAction (MulAut N) T :=
    { smul := fun g x => ⟨g x, by
        show g x * g x = 1
        rw [← map_mul, x.2, map_one]⟩
      one_smul := fun x => rfl
      mul_smul := fun g h x => rfl }
  let γT : Equiv.Perm T := MulAction.toPerm γ
  let γE : Function.End T := γT.toFun
  letI : Fintype T := Fintype.ofFinite T
  letI : DecidableEq T := Classical.decEq T
  have hγpow : γ ^ d = 1 := by
    rw [← hγd]
    exact pow_orderOf_eq_one γ
  have hγTd : γE ^ d = 1 := by
    have h := congrArg (MulAction.toPermHom (MulAut N) T) hγpow
    have h' : (γT : Equiv.Perm T) ^ d = 1 := by
      have h2 : MulAction.toPermHom (MulAut N) T (γ ^ d) = 1 := by
        simpa [MulAction.toPerm_one] using h
      rw [map_pow] at h2
      simpa [γT] using h2
    funext x
    change ((γT : Equiv.Perm T) ^ d) x = x
    exact congrArg (fun e : Equiv.Perm T => e x) h'
  have hcenterInv : Nat.card {x : N // x * x = 1 ∧ x ∈ Subgroup.center N} = 2 := by
    have hz2 : ∀ z : Subgroup.center N, (z : N) * (z : N) = 1 := by
      intro z
      have h : orderOf z ∣ 2 := by
        have := orderOf_dvd_natCard z
        rwa [hCenter] at this
      have h2 : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
      have h3 : ((z : Subgroup.center N) : N) ^ 2 = 1 := by
        simpa using congrArg Subtype.val h2
      simpa [pow_two] using h3
    rw [show Nat.card {x : N // x * x = 1 ∧ x ∈ Subgroup.center N} =
        Nat.card (Subgroup.center N) from Nat.card_congr ?_]
    · exact hCenter
    · refine
        { toFun := fun x => ⟨x.1, x.2.2⟩
          invFun := fun z => ⟨z.1, hz2 z, z.2⟩
          left_inv := fun x => by rfl
          right_inv := fun z => by rfl }
  have hfixT : Nat.card (Function.fixedPoints γE) = 2 := by
    have hset : Function.fixedPoints γE =
        {x : T | (x : N) ∈ CFSG.Quasithin.AutQ8D8.fixSub γ} := by
      ext x
      simp only [Function.fixedPoints, Set.mem_setOf_eq, Function.IsFixedPt]
      rw [CFSG.Quasithin.AutQ8D8.mem_fixSub]
      change (γE x = x) ↔ γ (x : N) = x
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [hset]
    have hCfix : CFSG.Quasithin.AutQ8D8.fixSub γ = Subgroup.center N := hCeq
    rw [hCfix]
    rw [← hcenterInv]
    refine Nat.card_congr ?_
    exact
      { toFun := fun x : {x : T // (x : N) ∈ Subgroup.center N} =>
          ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y : {x : N // x * x = 1 ∧ x ∈ Subgroup.center N} =>
          ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := d) (n := 1)
    (f := γE) (by simpa using hγTd)
  have hmod' : Nat.card T ≡ Nat.card (Function.fixedPoints γE) [MOD d] := by
    simpa using hmod
  rw [hInv, hfixT] at hmod'
  have hdvd10 : d ∣ 10 := by
    have h := (Nat.modEq_iff_dvd' (show 2 ≤ 12 by norm_num)).mp hmod'.symm
    simpa using h
  have hdvd10' : d ∣ 2 * 5 := by simpa using hdvd10
  rcases hd.dvd_mul.mp hdvd10' with h2 | h5
  · exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)
  · exact hd5 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h5)

@[expose] def ThreeTenCase3Z5AutInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) X →
    ∀ d : ℕ, d.Prime → d ≠ 2 → d ≠ 5 →
      d ∣ Nat.card (MulAut X) → d ∣ Nat.card X

@[expose] def ThreeTenCase3Z5FiniteInput : Prop :=
  (∀ (X : Type) [Group X] [Finite X],
    IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) X →
    ∀ d : ℕ, d.Prime → d ≠ 2 → d ≠ 5 →
      d ∣ Nat.card (MulAut X) → d ∣ Nat.card X) ∧
  (∀ (X : Type) [Group X] [Finite X] (P E : Subgroup X) (d : ℕ),
    IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) X →
    d.Prime → d ≠ 2 → d ≠ 5 →
      CFSG.ABGLocalTools.IsSylowOf 5 P ⊤ →
      CFSG.ABGLocalTools.IsSylowOf d E ⊤ →
      Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤)

theorem threeTenCase3Z5FiniteInput_of_aut (hAut : ThreeTenCase3Z5AutInput) :
    ThreeTenCase3Z5FiniteInput :=
  ⟨hAut, fun X _ _ P E d hX hd hd2 hd5 hP hE =>
    threeTenCase3Z5Sylow hX P E d hd hd2 hd5 hP hE⟩

@[expose] def ThreeTenCase3A6TwoFiniteInput : Prop :=
  (∀ (X : Type) [Group X] [Finite X],
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
      (fun B _ => Nat.card B = 2) X →
    ∀ d : ℕ, d.Prime → d ≠ 2 → d ≠ 5 →
      d ∣ Nat.card (MulAut X) → d ∣ Nat.card X) ∧
  (∀ (X : Type) [Group X] [Finite X] (P E : Subgroup X) (d : ℕ),
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
      (fun B _ => Nat.card B = 2) X →
    d.Prime → d ≠ 2 → d ≠ 5 →
      CFSG.ABGLocalTools.IsSylowOf 5 P ⊤ →
      CFSG.ABGLocalTools.IsSylowOf d E ⊤ →
      Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤)

@[expose] def ThreeTenCase3A5Q8D8FiniteInput : Prop :=
  (∀ (X : Type) [Group X] [Finite X],
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X →
    ∀ d : ℕ, d.Prime → d ≠ 2 → d ≠ 5 →
      d ∣ Nat.card (MulAut X) → d ∣ Nat.card X) ∧
  (∀ (X : Type) [Group X] [Finite X] (P E : Subgroup X) (d : ℕ),
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X →
    d.Prime → d ≠ 2 → d ≠ 5 →
      CFSG.ABGLocalTools.IsSylowOf 5 P ⊤ →
      CFSG.ABGLocalTools.IsSylowOf d E ⊤ →
      Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤)

theorem threeTenCase3FiniteInput_of_branches
    (hA6 : ThreeTenCase3A6TwoFiniteInput)
    (hA5 : ThreeTenCase3A5Q8D8FiniteInput)
    (hZ5 : ThreeTenCase3Z5FiniteInput) :
    ThreeTenCase3FiniteInput := by
  refine ⟨?_, ?_⟩
  · intro X _ _ hX d hd hd2 hd5 hdvd
    rw [ThreeTenCase3SmallType] at hX
    rcases hX with hA6X | hA5X | hZ5X
    · exact hA6.1 X hA6X d hd hd2 hd5 hdvd
    · exact hA5.1 X hA5X d hd hd2 hd5 hdvd
    · exact hZ5.1 X hZ5X d hd hd2 hd5 hdvd
  · intro X _ _ P E d hX hd hd2 hd5 hP hE
    rw [ThreeTenCase3SmallType] at hX
    rcases hX with hA6X | hA5X | hZ5X
    · exact hA6.2 X P E d hA6X hd hd2 hd5 hP hE
    · exact hA5.2 X P E d hA5X hd hd2 hd5 hP hE
    · exact hZ5.2 X P E d hZ5X hd hd2 hd5 hP hE

end CFSG.LocalAnalysis.AGL81I.Section3
