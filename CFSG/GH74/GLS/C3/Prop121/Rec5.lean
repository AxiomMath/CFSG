module

public import CFSG.GH74.GLS.C3.Prop121.Rec6
public import CFSG.GH74.GLS.C3.Prop121.Rec5Abs
public import CFSG.GH74.GLS.C3.Prop121.Rec5Ord8

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS

@[expose] def tC5 {G : Type} [Group G] (t : G) : ↥(centralizer ({t} : Set G)) :=
  ⟨t, mem_centralizer_singleton_iff.2 rfl⟩

section Config

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem exists_sylow_D5
    (hC : pRank 2 G ≤ 4) (h : IsAConfig 5 x K T Q S a) {t u g : G}
    (hS : Stage3Loc 5 x K Q t u g) :
    ∃ (z : G) (hzC : z ∈ centralizer ({t} : Set G))
      (P : Sylow 2 ↥(centralizer ({t} : Set G))),
      z ∈ K ∧ z * z = 1 ∧ z ≠ 1 ∧
      Nonempty (↥(P : Subgroup ↥(centralizer ({t} : Set G))) ≃* DihedralGroup 4) ∧
      Nat.card ↥(centralizer ({(⟨z, hzC⟩ : ↥(centralizer ({t} : Set G)))} :
        Set ↥(centralizer ({t} : Set G)))) = 24 := by
  classical
  obtain ⟨z, hzK, hzz, hz1, hcardz, D, hDle, hzD, ⟨eD⟩⟩ := exists_D8_data hC (Or.inl rfl) h hS
  have hcardz24 : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) = 24 := by
    simpa using hcardz
  have hzC : z ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (hS.t_comm_K z hzK).symm
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  let z₀ : ↥C := ⟨z, hzC⟩
  have hDC : D ≤ C := hDle.trans inf_le_right
  let D₀ : Subgroup ↥C := D.subgroupOf C
  let e2 : ↥D₀ ≃* DihedralGroup 4 := (Subgroup.subgroupOfEquivOfLe hDC).trans eD
  have hcardD : Nat.card ↥D₀ = 8 := by
    rw [Nat.card_congr e2.toEquiv, DihedralGroup.nat_card]
  have hDpg : IsPGroup 2 ↥D₀ := IsPGroup.of_card (n := 3) (by rw [hcardD]; norm_num)
  have hz₀z : z₀ * z₀ = 1 := Subtype.ext hzz
  have hz₀1 : z₀ ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hz₀D : z₀ ∈ D₀ := Subgroup.mem_subgroupOf.2 hzD
  have hDz : ∀ d ∈ D₀, d * z₀ = z₀ * d := by
    intro d hd
    have hd' : (d : G) ∈ D := Subgroup.mem_subgroupOf.1 hd
    have := mem_centralizer_singleton_iff.1 (hDle hd').1
    exact Subtype.ext this
  have hzn := normalizer_centralizes_of_center e2 hz₀D hz₀1 hz₀z hDz
  have hcardCz : Nat.card ↥(centralizer ({z₀} : Set ↥C)) = 24 := by
    rw [← hcardz24]
    refine Nat.card_congr
      { toFun := fun c => ⟨(c.1 : G), ?_, c.1.2⟩
        invFun := fun c => ⟨⟨c.1, c.2.2⟩, ?_⟩
        left_inv := fun c => rfl
        right_inv := fun c => rfl }
    · exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2))
    · exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 c.2.1))
  have hmax : ∀ P : Subgroup ↥C, IsPGroup 2 P → D₀ ≤ P → (∀ p ∈ P, p * z₀ = z₀ * p) → P = D₀ := by
    intro P hP hDP hPz
    have hPle : P ≤ centralizer ({z₀} : Set ↥C) :=
      fun p hp => mem_centralizer_singleton_iff.2 (hPz p hp)
    have hdvd : Nat.card ↥P ∣ 24 := hcardCz ▸ Subgroup.card_dvd_of_le hPle
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk] at hdvd
    have hk3 : k ≤ 3 := by
      by_contra hk4
      push Not at hk4
      have h16 : 16 ∣ 24 := ((pow_dvd_pow 2 hk4 : 2 ^ 4 ∣ 2 ^ k)).trans hdvd
      omega
    have hPcard : Nat.card ↥P ≤ Nat.card ↥D₀ := by
      rw [hk, hcardD]
      calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
        _ = 8 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge hDP hPcard).symm
  obtain ⟨P, hP⟩ := isSylow_of_maximal_central hDpg hDz hzn hmax
  exact ⟨z, hzC, P, hzK, hzz, hz1, ⟨(MulEquiv.subgroupCongr hP).trans e2⟩, hcardCz⟩

theorem hodd_five
    (hC : pRank 2 G ≤ 4) (h : IsAConfig 5 x K T Q S a)
    (hap : IsApproxTo G (alternatingGroup (Fin (5 + 4)))) {t u g : G}
    (hS : Stage3Loc 5 x K Q t u g) (R : Subgroup ↥(centralizer ({t} : Set G)))
    (hRodd : Odd (Nat.card R))
    (hRn : ∀ m : ↥(centralizer ({t} : Set G)), ∀ r ∈ R, m * r * m⁻¹ ∈ R) :
    R ≤ zpowers (tC5 t) := by
  intro r hr
  let R' : Subgroup G := R.map (centralizer ({t} : Set G)).subtype
  have hR'card : Nat.card ↥R' = Nat.card ↥R :=
    Nat.card_congr (Subgroup.equivMapOfInjective R (centralizer ({t} : Set G)).subtype
      (centralizer ({t} : Set G)).subtype_injective).toEquiv.symm
  have hmem : (r : G) ∈ R' := ⟨r, hr, rfl⟩
  have hRt : ∀ r' ∈ R', r' * t = t * r' := by
    rintro _ ⟨r₁, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 r₁.2
  have hRn' : ∀ c : G, c * t = t * c → ∀ r' ∈ R', c * r' * c⁻¹ ∈ R' := by
    intro c hct
    rintro _ ⟨r₁, hr₁, rfl⟩
    let cC : ↥(centralizer ({t} : Set G)) := ⟨c, mem_centralizer_singleton_iff.2 hct⟩
    exact ⟨cC * r₁ * cC⁻¹, hRn cC r₁ hr₁, rfl⟩
  have hR'odd : Odd (Nat.card ↥R') := by rw [hR'card]; exact hRodd
  have h1 := oddCore_le_zpowers hC (Or.inl rfl) h hap hS R' hR'odd hRt hRn' (r : G) hmem
  obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
  have : r = tC5 t ^ i := Subtype.ext hi.symm
  rw [this]
  exact Subgroup.zpow_mem _ (mem_zpowers (tC5 t)) i

theorem h9_five (hap : IsApproxTo G (alternatingGroup (Fin (5 + 4)))) {t : G}
    (w : ↥(centralizer ({t} : Set G))) (hw : orderOf w = 2) :
    ¬ 9 ∣ Nat.card ↥(centralizer ({w} : Set ↥(centralizer ({t} : Set G)))) := by
  intro h9dvd
  have hwG : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
  have hdvd := card_centralizer_subgroup_dvd (centralizer ({t} : Set G)) w
  have hPat := patternFacts_of_approx (n := 5) (Or.inl rfl) hap
  rcases hPat.1 (w : G) hwG with h1 | h1
  · rw [h1] at hdvd
    have h2 : 9 ∣ 4 * Nat.factorial 5 := h9dvd.trans hdvd
    revert h2
    norm_num [Nat.factorial]
  · rw [h1] at hdvd
    have h2 : 9 ∣ 192 * Nat.factorial (5 - 4) := h9dvd.trans hdvd
    revert h2
    norm_num [Nat.factorial]

theorem recog_five
    (hC : pRank 2 G ≤ 4) (h : IsAConfig 5 x K T Q S a)
    (hap : IsApproxTo G (alternatingGroup (Fin (5 + 4)))) {t u g : G}
    (hS : Stage3Loc 5 x K Q t u g) :
    ∃ L : Subgroup G, (∀ l ∈ L, l * t = t * l) ∧
      (∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) ∧
      (∀ i : ℤ, t ^ i ∈ L → t ^ i = 1) ∧ Nonempty (↥L ≃* alternatingGroup (Fin (5 + 1))) := by
  classical
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have ht1 : t ≠ 1 := by
    intro h1
    have := hS.t_order
    rw [h1, orderOf_one] at this
    omega
  have hc : ∀ m : ↥(centralizer ({t} : Set G)), m * tC5 t = tC5 t * m := fun m =>
    Subtype.ext (mem_centralizer_singleton_iff.1 m.2)
  have ht₃ : tC5 t ^ 3 = 1 := Subtype.ext ht3
  have ht₁ : tC5 t ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
  have hNn : (zpowers (tC5 t)).Normal := zpowers_normal_of_central hc
  obtain ⟨z, hzC, P, hzK, hzz, hz1, ⟨eP⟩, hcardCz⟩ := exists_sylow_D5 hC h hS
  obtain ⟨eK⟩ := hS.K_alt
  have hKC : K ≤ centralizer ({t} : Set G) :=
    fun k hk => mem_centralizer_singleton_iff.2 (hS.t_comm_K k hk).symm
  let eK₀ : ↥(K.subgroupOf (centralizer ({t} : Set G))) ≃* alternatingGroup (Fin 5) :=
    (Subgroup.subgroupOfEquivOfLe hKC).trans eK
  have hKN : ∀ k ∈ K.subgroupOf (centralizer ({t} : Set G)), k ∈ zpowers (tC5 t) → k = 1 := by
    intro k hk hkN
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hkN
    have hkG : (k : G) = t ^ i := by rw [← hi]; rfl
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have h1 : (k : G) = 1 := by
      refine TU.center_K_trivial (n := 5) (by norm_num) eK hkK (fun k' hk' => ?_)
      rw [hkG]
      exact ((show Commute t k' from hS.t_comm_K k' hk').zpow_left i).eq
    exact Subtype.ext h1
  have hzK₀ : (⟨z, hzC⟩ : ↥(centralizer ({t} : Set G))) ∈
      K.subgroupOf (centralizer ({t} : Set G)) := Subgroup.mem_subgroupOf.2 hzK
  have hz₀z : (⟨z, hzC⟩ : ↥(centralizer ({t} : Set G))) * ⟨z, hzC⟩ = 1 := Subtype.ext hzz
  have hz₀1 : (⟨z, hzC⟩ : ↥(centralizer ({t} : Set G))) ≠ 1 := fun h1 =>
    hz1 (congrArg Subtype.val h1)
  obtain ⟨η, hsurj, hker⟩ := exists_hom_alt6 hc ht₃ ht₁
    (fun R hR hRn => hodd_five hC h hap hS R hR hRn) P eP hz₀z hz₀1 hcardCz
    (fun w hw => h9_five hap w hw) eK₀ hKN hzK₀
  have ht'K : g * t * g⁻¹ ∈ K := hS.gt_K
  have ht'C : g * t * g⁻¹ ∈ centralizer ({t} : Set G) := hKC ht'K
  let t' : ↥(centralizer ({t} : Set G)) := ⟨g * t * g⁻¹, ht'C⟩
  have hg2 : g * g = 1 := by rw [← sq]; exact hS.g_sq
  have ht'3G : (g * t * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, ht3]; group
  have ht'3 : t' ^ 3 = 1 := Subtype.ext ht'3G
  have ht'1 : t' ∉ zpowers (tC5 t) := by
    intro hmem
    have h1 : g * t * g⁻¹ = 1 :=
      congrArg Subtype.val (hKN t' (Subgroup.mem_subgroupOf.2 ht'K) hmem)
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨eb, heb3, hebnm, i, hi⟩ := lifts_or_commutator hsurj hker ht'3 ht'1
  have hcommute : eb * t' * eb⁻¹ * t'⁻¹ = 1 := by
    by_contra hx
    have hi3 : i % 3 ≠ 0 := by
      intro h0
      apply hx
      rw [hi, zpow_eq_zpow_emod i (show tC5 t ^ (3 : ℤ) = 1 by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact ht₃), h0, zpow_zero]
    have hiG : (eb : G) * (g * t * g⁻¹) * (eb : G)⁻¹ * (g * t * g⁻¹)⁻¹ = t ^ i := by
      have := congrArg Subtype.val hi
      exact this
    have hab : t * (g * t * g⁻¹) = (g * t * g⁻¹) * t :=
      (mem_centralizer_singleton_iff.1 ht'C).symm
    have hca : (eb : G) * t * (eb : G)⁻¹ = t := by
      have := mem_centralizer_singleton_iff.1 eb.2
      rw [this]; group
    have hcb : ∀ k : ℤ, t ^ i = t ^ k →
        (eb : G) * (g * t * g⁻¹) * (eb : G)⁻¹ = (g * t * g⁻¹) * t ^ k := by
      intro k hk
      have h1 : (eb : G) * (g * t * g⁻¹) * (eb : G)⁻¹ = t ^ i * (g * t * g⁻¹) := by
        calc (eb : G) * (g * t * g⁻¹) * (eb : G)⁻¹
            = ((eb : G) * (g * t * g⁻¹) * (eb : G)⁻¹ * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
          _ = t ^ i * (g * t * g⁻¹) := by rw [hiG]
      rw [h1, hk]
      exact (Commute.zpow_left (show Commute t (g * t * g⁻¹) from hab) k).eq
    have hno8 := no_order_eight_of_approx_nine (G := G) hap
    have h3t : t ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact ht3
    have hti : t ^ i = t ^ (i % 3) := zpow_eq_zpow_emod i h3t
    have hcases : i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hcases with h1 | h2
    · refine false_of_transvection hno8 (a := t) (b := g * t * g⁻¹) (g := g) (c := (eb : G))
        ht3 ht1 ht'3G hab hg2 rfl hca (k := 1) (Or.inl rfl) (hcb 1 ?_)
      rw [hti, h1]
    · refine false_of_transvection hno8 (a := t) (b := g * t * g⁻¹) (g := g) (c := (eb : G))
        ht3 ht1 ht'3G hab hg2 rfl hca (k := -1) (Or.inr rfl) (hcb (-1) ?_)
      rw [hti, h2]
      have : t ^ (2 : ℤ) * t = 1 := by
        rw [← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact ht3
      rw [zpow_neg_one]
      exact eq_inv_of_mul_eq_one_left this
  have hcomm : Commute t' eb := by
    have h1 : eb * t' * eb⁻¹ = t' := mul_inv_eq_one.1 hcommute
    have h2 : eb * t' = t' * eb := by
      calc eb * t' = eb * t' * eb⁻¹ * eb := by group
        _ = t' * eb := by rw [h1]
    exact h2.symm
  obtain ⟨L₀, hL0inf, hL0sup, ⟨eL0⟩⟩ :=
    exists_complement_five hc ht₃ ht₁ hsurj hker hcomm
      (by rw [ht'3]; exact Subgroup.one_mem _) heb3 ht'1 hebnm
  refine ⟨L₀.map (centralizer ({t} : Set G)).subtype, ?_, ?_, ?_,
    ⟨(Subgroup.equivMapOfInjective L₀ (centralizer ({t} : Set G)).subtype
      (centralizer ({t} : Set G)).subtype_injective).symm.trans eL0⟩⟩
  · rintro _ ⟨l₀, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 l₀.2
  · intro c hct
    let cC : ↥(centralizer ({t} : Set G)) := ⟨c, mem_centralizer_singleton_iff.2 hct⟩
    have hcm : cC ∈ L₀ ⊔ zpowers (tC5 t) := by rw [hL0sup]; exact Subgroup.mem_top _
    obtain ⟨y, hy, m, hm, hym⟩ := Subgroup.mem_sup_of_normal_right.1 hcm
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hm
    refine ⟨i, y, ⟨y, hy, rfl⟩, ?_⟩
    have h1 : (y : G) * (t ^ i) = c := by
      have := congrArg Subtype.val hym
      rw [← hi] at this
      exact this
    rw [← h1]
    have : Commute (t ^ i) (y : G) := by
      have hyt : Commute (y : G) t := mem_centralizer_singleton_iff.1 y.2
      exact hyt.symm.zpow_left i
    exact this.eq.symm
  · intro i hi
    obtain ⟨l₀, hl₀, hl₀t⟩ := hi
    have h1 : l₀ = tC5 t ^ i := Subtype.ext hl₀t
    have h2 : l₀ ∈ zpowers (tC5 t) := by
      rw [h1]
      exact Subgroup.zpow_mem _ (mem_zpowers (tC5 t)) i
    have h3 : l₀ ∈ L₀ ⊓ zpowers (tC5 t) := ⟨hl₀, h2⟩
    rw [hL0inf, Subgroup.mem_bot] at h3
    calc t ^ i = (centralizer ({t} : Set G)).subtype l₀ := hl₀t.symm
      _ = (centralizer ({t} : Set G)).subtype 1 := by rw [h3]
      _ = 1 := map_one _

end Config

theorem s_recog_five
    : S_recog 5 :=
  fun _ _ _ hC _ _ _ _ _ _ h hap _ _ _ hS => recog_five hC h hap hS

theorem s_lemma123_core6_of_recog_seven
    (h7 : S_recog 7) : S_lemma123_core6 :=
  s_lemma123_core6_of_recog_five_seven s_recog_five h7

theorem s_prop121_cfg_of_recog_seven
    (h7 : S_recog 7) : S_prop121_cfg :=
  s_prop121_cfg_of_core6 (s_lemma123_core6_of_recog_seven h7)

end CFSG.GH74.GLS.C3.Prop121
