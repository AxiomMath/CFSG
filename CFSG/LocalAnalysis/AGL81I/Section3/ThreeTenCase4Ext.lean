module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase4Finite
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSmallCards
public import CFSG.LocalAnalysis.AGL81I.Section3.A5Generation
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneCaseNSQuot
public import CFSG.RankThree.PartOne.S9.QD32.AutCount

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem natCard_of_isExtNotation_alternating_five_q8d8_ext {X : Type} [Group X] [Finite X]
    (hX : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X) : Nat.card X = 1920 :=
  natCard_of_isExtNotation_alternating_five_q8d8 hX

theorem natCard_mulAut_alternatingGroup_five :
    Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_eq_of_bijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
      (by norm_num))]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem dvd_card_of_isExtNotation_alternating_five_q8d8 {X : Type} [Group X] [Finite X]
    (hX : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X)
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd3 : d ≠ 3)
    (hdvd : d ∣ Nat.card (MulAut X)) : d ∣ Nat.card X := by
  classical
  have hcardX : Nat.card X = 1920 := natCard_of_isExtNotation_alternating_five_q8d8_ext hX
  obtain ⟨N, hNnorm, hNtype, hNA5, -⟩ := hX
  haveI hNnormal : N.Normal := hNnorm
  have hNcard : Nat.card N = 32 := natCard_of_isQ8D8Type hNtype
  obtain ⟨eN⟩ := hNA5
  haveI hA5simple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  haveI hsimple : IsSimpleGroup (X ⧸ N) := eN.isSimpleGroup
  have hN2 : IsPGroup 2 N := IsPGroup.of_card (n := 5) (by rw [hNcard]; norm_num)
  have hpres : ∀ α : MulAut X, N.map α.toMonoidHom = N := by
    intro α
    have hle : N.map α.toMonoidHom ≤ N := by
      let M : Subgroup X := N.map α.toMonoidHom
      have hM2 : IsPGroup 2 M := hN2.map α.toMonoidHom
      have hMn : M.Normal := hNnormal.map α.toMonoidHom α.surjective
      let Mq : Subgroup (X ⧸ N) := M.map (QuotientGroup.mk' N)
      have hMq2 : IsPGroup 2 Mq := hM2.map (QuotientGroup.mk' N)
      have hMqn : Mq.Normal :=
        hMn.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      haveI : Mq.Normal := hMqn
      have hMqbot : Mq = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Mq with h | h
        · exact h
        · exfalso
          rw [h] at hMq2
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hMq2
          have h60 : Nat.card (X ⧸ N) = 60 := by
            rw [Nat.card_congr eN.toEquiv]
            exact natCard_alternatingGroup_fin_five
          have h3 : 3 ∣ 2 ^ k := by
            rw [← hk, Subgroup.card_top, h60]
            norm_num
          exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
      intro m hm
      have : QuotientGroup.mk' N m ∈ Mq := Subgroup.mem_map_of_mem _ hm
      rw [hMqbot] at this
      exact (QuotientGroup.eq_one_iff m).mp (Subgroup.mem_bot.mp this)
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (by rw [Subgroup.card_map_of_injective α.injective, hNcard]))
  rcases eq_or_ne d 5 with h5 | hd5
  · subst h5
    rw [hcardX]
    norm_num
  exfalso
  have hd5gt : 5 < d := by
    have h2 := hd.two_le
    rcases Nat.lt_or_ge d 6 with h | h
    · interval_cases d
      · exact absurd rfl hd2
      · exact absurd rfl hd3
      · norm_num at hd
      · exact absurd rfl hd5
    · exact h
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' d hdvd
  have hαN : N.map α.toMonoidHom = N := hpres α
  let β : MulAut N :=
    (Subgroup.equivMapOfInjective N α.toMonoidHom α.injective).trans
      (MulEquiv.subgroupCongr hαN)
  have hβval : ∀ n : N, ((β n : N) : X) = α (n : X) := by
    intro n
    rfl
  have hβpow : β ^ d = 1 := by
    ext n
    have hval : ∀ k : ℕ, ∀ m : N,
        ((((β : MulAut N) ^ k) m : N) : X) = ((α : MulAut X) ^ k) (m : X) := by
      intro k
      induction k with
      | zero => intro m; rfl
      | succ k ih =>
          intro m
          rw [pow_succ', MulAut.mul_apply, hβval, ih, pow_succ', MulAut.mul_apply]
    rw [hval d n]
    rw [show (α : MulAut X) ^ d = 1 by rw [← hα]; exact pow_orderOf_eq_one α]
    rfl
  have hβdvd : orderOf β ∣ d := orderOf_dvd_iff_pow_eq_one.mpr hβpow
  have hAutN : Nat.card (MulAut N) ∣ 2 ^ 7 * 3 * 5 := by
    obtain ⟨e⟩ := CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.nonempty_mulEquiv_QD32_of_isQ8D8Type hNtype hNcard
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.RankThree.PartOne.QD32Facts.card_mulAut_QD32_dvd
  have hndvd235 : ¬ d ∣ 2 ^ 7 * 3 * 5 := by
    intro h
    rcases hd.dvd_mul.mp h with h | h
    · rcases hd.dvd_mul.mp h with h | h
      · have h2 : d ∣ 2 := hd.dvd_of_dvd_pow h
        exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)
      · exact hd3 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp h)
    · exact hd5 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h)
  have hβ1 : β = 1 := by
    have hcop : Nat.Coprime d (2 ^ 7 * 3 * 5) := hd.coprime_iff_not_dvd.mpr hndvd235
    have h : orderOf β ∣ Nat.gcd d (2 ^ 7 * 3 * 5) :=
      Nat.dvd_gcd hβdvd ((orderOf_dvd_natCard β).trans hAutN)
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
  have hfix : ∀ n ∈ N, α n = n := by
    intro n hn
    have h := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : X)) hβ1
    simpa [hβval] using h
  let αbar : MulAut (X ⧸ N) := QuotientGroup.congr N N α hαN
  have hαbar_apply : ∀ y : X,
      αbar (QuotientGroup.mk y) = QuotientGroup.mk (α y) := by
    intro y
    rfl
  have hαbar_pow : αbar ^ d = 1 := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H y =>
        have hpow : ∀ k : ℕ,
            (αbar ^ k) (QuotientGroup.mk y) = QuotientGroup.mk ((α ^ k) y) := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih =>
              rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply,
                hαbar_apply]
        rw [hpow d]
        rw [show (α : MulAut X) ^ d = 1 by rw [← hα]; exact pow_orderOf_eq_one α]
        rfl
  have hαbar_dvd : orderOf αbar ∣ d := orderOf_dvd_iff_pow_eq_one.mpr hαbar_pow
  have hcardAutQuot : Nat.card (MulAut (X ⧸ N)) = 120 := by
    rw [Nat.card_congr (MulAut.congr eN).toEquiv, natCard_mulAut_alternatingGroup_five]
  have hαbar_120 : orderOf αbar ∣ 120 := by
    have := orderOf_dvd_natCard αbar
    rwa [hcardAutQuot] at this
  have hndvd120 : ¬ d ∣ 120 := by
    intro h
    have h' : d ∣ 2 ^ 3 * 3 * 5 := by
      rwa [show 2 ^ 3 * 3 * 5 = 120 by norm_num]
    rcases hd.dvd_mul.mp h' with h | h
    · rcases hd.dvd_mul.mp h with h | h
      · have h2 : d ∣ 2 := hd.dvd_of_dvd_pow h
        exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)
      · exact hd3 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp h)
    · exact hd5 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h)
  have hαbar1 : αbar = 1 := by
    have hcop : Nat.Coprime d 120 := hd.coprime_iff_not_dvd.mpr hndvd120
    have h : orderOf αbar ∣ Nat.gcd d 120 := Nat.dvd_gcd hαbar_dvd hαbar_120
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
  have hαmod : ∀ x : X, x⁻¹ * α x ∈ N := by
    intro x
    have hmk : QuotientGroup.mk (s := N) (α x) = QuotientGroup.mk (s := N) x := by
      have h := congrArg (fun f : MulAut (X ⧸ N) =>
        f (QuotientGroup.mk (s := N) x)) hαbar1
      have h' : αbar (QuotientGroup.mk (s := N) x) =
          QuotientGroup.mk (s := N) (α x) := rfl
      rw [h', MulAut.one_apply] at h
      exact h
    have hmem : (α x)⁻¹ * x ∈ N := (QuotientGroup.eq (s := N)).mp hmk
    simpa using Subgroup.inv_mem N hmem
  have hα1 : α = 1 := by
    ext x
    let n : X := x⁻¹ * α x
    have hnN : n ∈ N := hαmod x
    have hxn : α x = x * n := by
      dsimp [n]
      group
    have hiter : ∀ k : ℕ, (α ^ k) x = x * n ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', MulAut.mul_apply, ih, map_mul,
            hfix _ (Subgroup.pow_mem N hnN k), hxn, pow_succ']
          group
    have hxd : x = x * n ^ d := by
      have := hiter d
      rw [show (α : MulAut X) ^ d = 1 by rw [← hα]; exact pow_orderOf_eq_one α] at this
      simpa using this
    have hnd : n ^ d = 1 := by
      have := congrArg (fun y => x⁻¹ * y) hxd
      simpa using this.symm
    have h32 : orderOf n ∣ 32 := by
      have h : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hnN
      rwa [hNcard] at h
    have hdn : orderOf n ∣ d := orderOf_dvd_of_pow_eq_one hnd
    have hcop32 : Nat.Coprime d 32 :=
      hd.coprime_iff_not_dvd.mpr (by
        intro h
        have h2 : d ∣ 2 := hd.dvd_of_dvd_pow (by
          rwa [show (32 : ℕ) = 2 ^ 5 by norm_num] at h)
        exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2))
    have hn1 : n = 1 := by
      have h : orderOf n ∣ Nat.gcd d 32 := Nat.dvd_gcd hdn h32
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop32] at h
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
    simp [hxn, hn1]
  have hd1 : d = 1 := by
    rw [← hα, hα1, orderOf_one]
  exact hd.ne_one hd1

theorem normalizer_sup_of_isExtNotation_alternating_five_q8d8_of_ne_five
    {X : Type} [Group X] [Finite X]
    (hX : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X)
    (P E : Subgroup X) (d : ℕ) (hd : d.Prime) (hd2 : d ≠ 2) (hd3 : d ≠ 3)
    (hd5 : d ≠ 5)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hE : CFSG.ABGLocalTools.IsSylowOf d E ⊤) :
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤ := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hcardX : Nat.card X = 1920 := natCard_of_isExtNotation_alternating_five_q8d8_ext hX
  have hndvd : ¬ d ∣ Nat.card X := by
    rw [hcardX]
    intro h
    have h' : d ∣ 2 ^ 7 * 3 * 5 := by
      rwa [show 2 ^ 7 * 3 * 5 = 1920 by norm_num]
    rcases hd.dvd_mul.mp h' with h | h
    · rcases hd.dvd_mul.mp h with h | h
      · have h2 : d ∣ 2 := hd.dvd_of_dvd_pow h
        exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)
      · exact hd3 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp h)
    · exact hd5 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h)
  have hEcard : Nat.card E = 1 := by
    rw [hE.card_eq, Subgroup.card_top,
      Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
  have hEbot : E = ⊥ := Subgroup.eq_bot_of_card_eq E hEcard
  rw [hEbot]
  have hbot : Subgroup.normalizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
    Subgroup.normalizer_eq_top (⊥ : Subgroup X)
  rw [hbot, sup_top_eq]

theorem normalizer_sup_of_isExtNotation_alternating_five_q8d8_of_le_normalizer
    {X : Type} [Group X] [Finite X] {N P E : Subgroup X} [hNnormal : N.Normal]
    (hNtype : IsQ8D8Type N)
    (eN : X ⧸ N ≃* alternatingGroup (Fin 5))
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hE : CFSG.ABGLocalTools.IsSylowOf 5 E ⊤)
    (hle : N ≤ Subgroup.normalizer (P : Set X) ∨
      N ≤ Subgroup.normalizer (E : Set X)) :
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤ := by
  classical
  have hNcard : Nat.card N = 32 := natCard_of_isQ8D8Type hNtype
  have hcardX : Nat.card X = 1920 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hNcard]
    have h60 : Nat.card (X ⧸ N) = 60 := by
      rw [Nat.card_congr eN.toEquiv]
      exact natCard_alternatingGroup_fin_five
    rw [h60]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h3dvdP : 3 ∣ Nat.card P := by
    obtain ⟨-, -, hrel⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).mp hP
    rw [Subgroup.relIndex_top_right] at hrel
    have hcard := Subgroup.index_mul_card P
    have h3X : 3 ∣ Nat.card X := by rw [hcardX]; norm_num
    rw [← hcard] at h3X
    rcases (Nat.prime_three.dvd_mul).mp h3X with h | h
    · exact absurd h hrel
    · exact h
  have h5dvdE : 5 ∣ Nat.card E := by
    obtain ⟨-, -, hrel⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).mp hE
    rw [Subgroup.relIndex_top_right] at hrel
    have hcard := Subgroup.index_mul_card E
    have h5X : 5 ∣ Nat.card X := by rw [hcardX]; norm_num
    rw [← hcard] at h5X
    rcases (Nat.prime_five.dvd_mul).mp h5X with h | h
    · exact absurd h hrel
    · exact h
  obtain ⟨p, hpord⟩ := exists_prime_orderOf_dvd_card' 3 (G := ↥P) h3dvdP
  obtain ⟨e, heord⟩ := exists_prime_orderOf_dvd_card' 5 (G := ↥E) h5dvdE
  have hpP : ((p : P) : X) ∈ P := p.2
  have heE : ((e : E) : X) ∈ E := e.2
  have hpordX : orderOf ((p : P) : X) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hpord
  have heordX : orderOf ((e : E) : X) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact heord
  have hpN : ((p : P) : X) ∉ N := by
    intro hmem
    have h : orderOf ((p : P) : X) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmem
    rw [hNcard, hpordX] at h
    norm_num at h
  have heN : ((e : E) : X) ∉ N := by
    intro hmem
    have h : orderOf ((e : E) : X) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmem
    rw [hNcard, heordX] at h
    norm_num at h
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  have hπp : orderOf (π ((p : P) : X)) = 3 := by
    have hdvd : orderOf (π ((p : P) : X)) ∣ 3 := by
      rw [← hpordX]
      exact orderOf_map_dvd π _
    have hne : π ((p : P) : X) ≠ 1 := by
      intro h1
      exact hpN ((QuotientGroup.eq_one_iff _).mp h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hπe : orderOf (π ((e : E) : X)) = 5 := by
    have hdvd : orderOf (π ((e : E) : X)) ∣ 5 := by
      rw [← heordX]
      exact orderOf_map_dvd π _
    have hne : π ((e : E) : X) ≠ 1 := by
      intro h1
      exact heN ((QuotientGroup.eq_one_iff _).mp h1)
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hNle : N ≤ Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) := by
    rcases hle with h | h
    · exact h.trans le_sup_left
    · exact h.trans le_sup_right
  have hpnorm : ((p : P) : X) ∈ Subgroup.normalizer (P : Set X) :=
    Subgroup.le_normalizer hpP
  have henorm : ((e : E) : X) ∈ Subgroup.normalizer (E : Set X) :=
    Subgroup.le_normalizer heE
  have hpnorm' : ((p : P) : X) ∈ Subgroup.normalizer (P : Set X) ⊔
      Subgroup.normalizer (E : Set X) := Subgroup.mem_sup_left hpnorm
  have henorm' : ((e : E) : X) ∈ Subgroup.normalizer (P : Set X) ⊔
      Subgroup.normalizer (E : Set X) := Subgroup.mem_sup_right henorm
  have hpY : π ((p : P) : X) ∈ (Subgroup.normalizer (P : Set X) ⊔
      Subgroup.normalizer (E : Set X)).map π :=
    Subgroup.mem_map_of_mem π hpnorm'
  have heY : π ((e : E) : X) ∈ (Subgroup.normalizer (P : Set X) ⊔
      Subgroup.normalizer (E : Set X)).map π :=
    Subgroup.mem_map_of_mem π henorm'
  have hYmap : (Subgroup.normalizer (P : Set X) ⊔
      Subgroup.normalizer (E : Set X)).map π = ⊤ := by
    refine eq_top_of_order_three_and_five_of_mulEquiv (e := eN)
      (H := (Subgroup.normalizer (P : Set X) ⊔
        Subgroup.normalizer (E : Set X)).map π) ?_ ?_
    · exact ⟨π ((p : P) : X), hpY, hπp⟩
    · exact ⟨π ((e : E) : X), heY, hπe⟩
  have hsup : (Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X)) ⊔ N =
      ⊤ := by
    have h := congrArg (Subgroup.comap π) hYmap
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
    exact h
  have htop : (Subgroup.normalizer (P : Set X) ⊔
      Subgroup.normalizer (E : Set X)) = ⊤ := by
    have h := hsup
    rwa [sup_eq_left.mpr hNle] at h
  exact htop

@[expose] def ThreeTenCase4ExtSylowFiveNontrivialInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X) [N.Normal] (P E : Subgroup X),
    IsQ8D8Type N →
    Nonempty (X ⧸ N ≃* alternatingGroup (Fin 5)) →
    CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ →
    CFSG.ABGLocalTools.IsSylowOf 5 E ⊤ →
    ¬ N ≤ Subgroup.normalizer (P : Set X) →
    ¬ N ≤ Subgroup.normalizer (E : Set X) →
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤

theorem threeTenCase4ExtFiniteInput_of_sylowFiveNontrivial
    (h5 : ThreeTenCase4ExtSylowFiveNontrivialInput) : ThreeTenCase4ExtFiniteInput := by
  refine ⟨?_, ?_⟩
  · intro X _ _ hX d hd hd2 hd3 hdvd
    exact dvd_card_of_isExtNotation_alternating_five_q8d8 hX hd hd2 hd3 hdvd
  · intro X _ _ P E d hX hd hd2 hd3 hP hE
    by_cases hd5 : d = 5
    · subst hd5
      obtain ⟨N, hNnorm, hNtype, hNA5, -⟩ := hX
      haveI : N.Normal := hNnorm
      obtain ⟨eN⟩ := hNA5
      by_cases hleP : N ≤ Subgroup.normalizer (P : Set X)
      · exact normalizer_sup_of_isExtNotation_alternating_five_q8d8_of_le_normalizer
          hNtype eN hP hE (Or.inl hleP)
      · by_cases hleE : N ≤ Subgroup.normalizer (E : Set X)
        · exact normalizer_sup_of_isExtNotation_alternating_five_q8d8_of_le_normalizer
            hNtype eN hP hE (Or.inr hleE)
        · exact h5 X N P E hNtype ⟨eN⟩ hP hE hleP hleE
    · exact normalizer_sup_of_isExtNotation_alternating_five_q8d8_of_ne_five
        hX P E d hd hd2 hd3 hd5 hP hE

end CFSG.LocalAnalysis.AGL81I.Section3
