module

public import CFSG.GH74.GLS.C3.Prop121.CzSylow
public import CFSG.GH74.GLS.C3.Prop121.OddCore
public import CFSG.GH74.GLS.C3.Prop121.Rec6Abs

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS

def tC {G : Type} [Group G] (t : G) : ↥(centralizer ({t} : Set G)) :=
  ⟨t, mem_centralizer_singleton_iff.2 rfl⟩

section Config

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem oddCore_le_zpowers
    (hC : pRank 2 G ≤ 4) (hn : n = 5 ∨ n = 6) (h : IsAConfig n x K T Q S a)
    (hap : IsApproxTo G (alternatingGroup (Fin (n + 4)))) {t u g : G}
    (hS : Stage3Loc n x K Q t u g) (R : Subgroup G) (hRodd : Odd (Nat.card R))
    (hRt : ∀ r ∈ R, r * t = t * r)
    (hRn : ∀ c : G, c * t = t * c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) :
    ∀ r ∈ R, r ∈ zpowers t := by
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by omega
  have hG4 : pRank 2 G ≤ 4 := hC
  have hF := fnFacts n hn'
  have hP := patternFacts_of_approx hn' hap
  have hKn : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R :=
    fun k hk r hr => hRn k (hS.t_comm_K k hk).symm r hr
  have hcomm := odd_normal_comm_K hn' hG4 h hF hP hS R hRodd hKn
  intro r hr
  exact centralizer_K_inf_centralizer_t hC hn h hS r (hcomm r hr) (hRt r hr)

theorem exists_sylow_D
    (hC : pRank 2 G ≤ 4) (h : IsAConfig 6 x K T Q S a) {t u g : G}
    (hS : Stage3Loc 6 x K Q t u g) :
    ∃ (z : G) (hzC : z ∈ centralizer ({t} : Set G))
      (P : Sylow 2 ↥(centralizer ({t} : Set G))),
      z ∈ K ∧ z * z = 1 ∧ z ≠ 1 ∧
      Nonempty (↥(P : Subgroup ↥(centralizer ({t} : Set G))) ≃* DihedralGroup 4) ∧
      Nat.card ↥(centralizer ({(⟨z, hzC⟩ : ↥(centralizer ({t} : Set G)))} :
        Set ↥(centralizer ({t} : Set G)))) = 72 := by
  classical
  obtain ⟨z, hzK, hzz, hz1, hcardz, D, hDle, hzD, ⟨eD⟩⟩ := exists_D8_data hC (Or.inr rfl) h hS
  have hcardz72 : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) = 72 := by
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
  have hcardCz : Nat.card ↥(centralizer ({z₀} : Set ↥C)) = 72 := by
    rw [← hcardz72]
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
    have hdvd : Nat.card ↥P ∣ 72 := hcardCz ▸ Subgroup.card_dvd_of_le hPle
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk] at hdvd
    have hk3 : k ≤ 3 := by
      by_contra hk4
      push Not at hk4
      have h16 : 16 ∣ 72 := ((pow_dvd_pow 2 hk4 : 2 ^ 4 ∣ 2 ^ k)).trans hdvd
      omega
    have hPcard : Nat.card ↥P ≤ Nat.card ↥D₀ := by
      rw [hk, hcardD]
      calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
        _ = 8 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge hDP hPcard).symm
  obtain ⟨P, hP⟩ := isSylow_of_maximal_central hDpg hDz hzn hmax
  exact ⟨z, hzC, P, hzK, hzz, hz1, ⟨(MulEquiv.subgroupCongr hP).trans e2⟩, hcardCz⟩

theorem hodd_six
    (hC : pRank 2 G ≤ 4) (h : IsAConfig 6 x K T Q S a)
    (hap : IsApproxTo G (alternatingGroup (Fin (6 + 4)))) {t u g : G}
    (hS : Stage3Loc 6 x K Q t u g) (R : Subgroup ↥(centralizer ({t} : Set G)))
    (hRodd : Odd (Nat.card R))
    (hRn : ∀ m : ↥(centralizer ({t} : Set G)), ∀ r ∈ R, m * r * m⁻¹ ∈ R) :
    R ≤ zpowers (tC t) := by
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
  have h1 := oddCore_le_zpowers hC (Or.inr rfl) h hap hS R' hR'odd hRt hRn' (r : G) hmem
  obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
  have : r = tC t ^ i := Subtype.ext hi.symm
  rw [this]
  exact Subgroup.zpow_mem _ (mem_zpowers (tC t)) i

theorem recog_six
    (hC : pRank 2 G ≤ 4) (h : IsAConfig 6 x K T Q S a)
    (hap : IsApproxTo G (alternatingGroup (Fin (6 + 4)))) {t u g : G}
    (hS : Stage3Loc 6 x K Q t u g) :
    ∃ L : Subgroup G, (∀ l ∈ L, l * t = t * l) ∧
      (∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) ∧
      (∀ i : ℤ, t ^ i ∈ L → t ^ i = 1) ∧ Nonempty (↥L ≃* alternatingGroup (Fin (6 + 1))) := by
  classical
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have ht1 : t ≠ 1 := by
    intro h1
    have := hS.t_order
    rw [h1, orderOf_one] at this
    omega
  have hc : ∀ m : ↥(centralizer ({t} : Set G)), m * tC t = tC t * m := fun m =>
    Subtype.ext (mem_centralizer_singleton_iff.1 m.2)
  have ht₃ : tC t ^ 3 = 1 := Subtype.ext ht3
  have ht₁ : tC t ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
  have hNn : (zpowers (tC t)).Normal := zpowers_normal_of_central hc
  obtain ⟨z, hzC, P, hzK, hzz, hz1, ⟨eP⟩, hcardCz⟩ := exists_sylow_D hC h hS
  obtain ⟨eK⟩ := hS.K_alt
  have hKC : K ≤ centralizer ({t} : Set G) :=
    fun k hk => mem_centralizer_singleton_iff.2 (hS.t_comm_K k hk).symm
  let eK₀ : ↥(K.subgroupOf (centralizer ({t} : Set G))) ≃* alternatingGroup (Fin 6) :=
    (Subgroup.subgroupOfEquivOfLe hKC).trans eK
  have hKN : ∀ k ∈ K.subgroupOf (centralizer ({t} : Set G)), k ∈ zpowers (tC t) → k = 1 := by
    intro k hk hkN
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hkN
    have hkG : (k : G) = t ^ i := by rw [← hi]; rfl
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have h1 : (k : G) = 1 := by
      refine TU.center_K_trivial (n := 6) (by norm_num) eK hkK (fun k' hk' => ?_)
      rw [hkG]
      exact ((show Commute t k' from hS.t_comm_K k' hk').zpow_left i).eq
    exact Subtype.ext h1
  have hzK₀ : (⟨z, hzC⟩ : ↥(centralizer ({t} : Set G))) ∈
      K.subgroupOf (centralizer ({t} : Set G)) := Subgroup.mem_subgroupOf.2 hzK
  have hz₀z : (⟨z, hzC⟩ : ↥(centralizer ({t} : Set G))) * ⟨z, hzC⟩ = 1 := Subtype.ext hzz
  have hz₀1 : (⟨z, hzC⟩ : ↥(centralizer ({t} : Set G))) ≠ 1 := fun h1 =>
    hz1 (congrArg Subtype.val h1)
  obtain ⟨η, hsurj, hker⟩ := exists_hom_alt7 hc ht₃ ht₁
    (fun R hR hRn => hodd_six hC h hap hS R hR hRn) P eP hz₀z hz₀1 hcardCz eK₀ hKN hzK₀
  obtain ⟨L₀, hL0inf, hL0sup, ⟨eL0⟩⟩ := exists_complement_six hc ht₃ ht₁ hsurj hker eK₀ hKN
  refine ⟨L₀.map (centralizer ({t} : Set G)).subtype, ?_, ?_, ?_,
    ⟨(Subgroup.equivMapOfInjective L₀ (centralizer ({t} : Set G)).subtype
      (centralizer ({t} : Set G)).subtype_injective).symm.trans eL0⟩⟩
  · rintro _ ⟨l₀, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 l₀.2
  · intro c hct
    let cC : ↥(centralizer ({t} : Set G)) := ⟨c, mem_centralizer_singleton_iff.2 hct⟩
    have hcm : cC ∈ L₀ ⊔ zpowers (tC t) := by rw [hL0sup]; exact Subgroup.mem_top _
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
    have h1 : l₀ = tC t ^ i := Subtype.ext hl₀t
    have h2 : l₀ ∈ zpowers (tC t) := by
      rw [h1]
      exact Subgroup.zpow_mem _ (mem_zpowers (tC t)) i
    have h3 : l₀ ∈ L₀ ⊓ zpowers (tC t) := ⟨hl₀, h2⟩
    rw [hL0inf, Subgroup.mem_bot] at h3
    calc t ^ i = (centralizer ({t} : Set G)).subtype l₀ := hl₀t.symm
      _ = (centralizer ({t} : Set G)).subtype 1 := by rw [h3]
      _ = 1 := map_one _

end Config

theorem s_recog_six
    : S_recog 6 :=
  fun _ _ _ hC _ _ _ _ _ _ h hap _ _ _ hS => recog_six hC h hap hS

theorem s_lemma123_core6_of_recog_five_seven
    (h5 : S_recog 5) (h7 : S_recog 7) :
    S_lemma123_core6 :=
  s_lemma123_core6_of_recog h5 s_recog_six h7

end CFSG.GH74.GLS.C3.Prop121
