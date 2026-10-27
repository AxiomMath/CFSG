module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoFrattini
public import CFSG.GroupTheory.ABGLocalTools.Basic

import CFSG.RankThree.Asc83Table.E9
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

private theorem centralizes_of_autQuotient_eq_one {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) {P : Subgroup X} (hP : IsPGroup p ↥P) {u : X}
    (huN : u ∈ Subgroup.normalizer (P : Set X)) (hu3 : u ^ 3 = 1)
    (hρ : CFSG.SectionRank.Ccomm.autQuotient (frattini ↥P)
      (Subgroup.normalizerMonoidHom P ⟨u, huN⟩) = 1) :
    u ∈ Subgroup.centralizer (P : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let α : MulAut ↥P := Subgroup.normalizerMonoidHom P ⟨u, huN⟩
  have hαρ : CFSG.SectionRank.Ccomm.autQuotient (frattini ↥P) α = 1 := hρ
  have hker : α ∈ (CFSG.SectionRank.Ccomm.autQuotient (frattini ↥P)).ker :=
    MonoidHom.mem_ker.mpr hαρ
  have hkerP : IsPGroup p (CFSG.SectionRank.Ccomm.autQuotient (frattini ↥P)).ker :=
    CFSG.SectionRank.Ccomm.isPGroup_ker_autQuotient_frattini hP
  obtain ⟨m, hm⟩ := hkerP ⟨α, hker⟩
  have hordp : orderOf α ∣ p ^ m := by
    have h := orderOf_dvd_of_pow_eq_one hm
    simpa [Subgroup.orderOf_coe] using h
  have huN3 : (⟨u, huN⟩ : ↥(Subgroup.normalizer (P : Set X))) ^ 3 = 1 :=
    Subtype.ext hu3
  have hα3 : α ^ 3 = 1 := by
    calc α ^ 3 = Subgroup.normalizerMonoidHom P
          ((⟨u, huN⟩ : ↥(Subgroup.normalizer (P : Set X))) ^ 3) := by rw [map_pow]
      _ = 1 := by rw [huN3, map_one]
  have hord3 : orderOf α ∣ 3 := orderOf_dvd_of_pow_eq_one hα3
  have hα1 : α = 1 := by
    apply orderOf_eq_one_iff.mp
    have hcop : Nat.Coprime (p ^ m) 3 :=
      Nat.Coprime.pow_left m ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
    exact (Nat.Coprime.coprime_dvd_left hordp hcop).eq_one_of_dvd hord3
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hα1' : (Subgroup.normalizerMonoidHom P ⟨u, huN⟩ : MulAut ↥P) = 1 := hα1
  have happ : (Subgroup.normalizerMonoidHom P ⟨u, huN⟩) ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [hα1']
    rfl
  have hconj : u * x * u⁻¹ = x := by
    have := congrArg Subtype.val happ
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  calc x * u = (u * x * u⁻¹) * u := by rw [hconj]
    _ = u * x := by group

private theorem frattini_surjection {X : Type} [Group X] [Finite X]
    {O : Subgroup X} [O.Normal] {P : Subgroup X}
    (hfrattini : Subgroup.normalizer (P : Set X) ⊔ O = ⊤)
    (Lb : Subgroup (X ⧸ O)) :
    ∃ (Y : Subgroup X) (φ : Y →* ↥Lb),
      Y = Subgroup.normalizer (P : Set X) ⊓ Lb.comap (QuotientGroup.mk' O) ∧
      Function.Surjective φ ∧
      ∀ y : Y, ((φ y : ↥Lb) : X ⧸ O) = QuotientGroup.mk' O (y : X) := by
  classical
  let N : Subgroup X := Subgroup.normalizer (P : Set X)
  let fO : X →* X ⧸ O := QuotientGroup.mk' O
  let Y : Subgroup X := N ⊓ Lb.comap fO
  let φ : Y →* ↥Lb :=
    { toFun := fun y => ⟨fO (y : X), show fO (y : X) ∈ Lb from y.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro y z
        apply Subtype.ext
        simp [map_mul] }
  have hφ_apply : ∀ y : Y, ((φ y : ↥Lb) : X ⧸ O) = fO (y : X) := fun _ => rfl
  refine ⟨Y, φ, rfl, ?_, hφ_apply⟩
  intro l
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective O (l : X ⧸ O)
  have hxsup : x ∈ N ⊔ O := by rw [hfrattini]; exact Subgroup.mem_top x
  obtain ⟨n, hnN, o, hoO, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxsup
  have hno : fO n = fO (n * o) := by
    rw [map_mul]
    have ho1 : fO o = 1 := (QuotientGroup.eq_one_iff o).mpr hoO
    rw [ho1, mul_one]
  have hnY : n ∈ Y := by
    refine ⟨hnN, ?_⟩
    change fO n ∈ Lb
    rw [hno, hx]
    exact l.2
  refine ⟨⟨n, hnY⟩, ?_⟩
  apply Subtype.ext
  rw [hφ_apply ⟨n, hnY⟩]
  exact hno.trans hx

private theorem mem_frattiniPreimage_of_cube_one {X : Type} [Group X]
    {O : Subgroup X} [O.Normal] {Lb : Subgroup (X ⧸ O)} {N Y : Subgroup X}
    (hYdef : Y = N ⊓ Lb.comap (QuotientGroup.mk' O))
    (h3 : ∀ x : X ⧸ O, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Lb)
    {u : X} (huN : u ∈ N) (hu3 : u ^ 3 = 1) : u ∈ Y := by
  rw [hYdef]
  refine ⟨huN, ?_⟩
  change QuotientGroup.mk' O u ∈ Lb
  have hdvd : orderOf (QuotientGroup.mk' O u) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hu3, map_one]
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact h3 (QuotientGroup.mk' O u) ⟨0, by rw [h, pow_zero]⟩
  · exact h3 (QuotientGroup.mk' O u) ⟨1, by rw [h, pow_one]⟩

private theorem rho_ker_map_eq_top {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {P : Subgroup X} (hP : IsPGroup p ↥P)
    {H : Type} [Group H] {Lb : Subgroup H} {n : ℕ} (hn : 9 ≤ n)
    (e : ↥Lb ≃* alternatingGroup (Fin n)) {Y : Type} [Group Y] [Finite Y]
    (φ : Y →* ↥Lb) (hφsurj : Function.Surjective φ)
    (ρ : Y →* MulAut (↥P ⧸ frattini ↥P)) (hGL4 : KFactA9NotInvolvedGL4)
    (hVcomm : IsMulCommutative (↥P ⧸ frattini ↥P))
    (hVexp : ∀ v : ↥P ⧸ frattini ↥P, v ^ p = 1)
    (hcard : Nat.card (↥P ⧸ frattini ↥P) ≤ p ^ 4) :
    ρ.ker.map φ = ⊤ := by
  classical
  have hφ'surj : Function.Surjective (e.toMonoidHom.comp φ) := e.surjective.comp hφsurj
  have hnotker' : ¬ ρ.ker ≤ (e.toMonoidHom.comp φ).ker :=
    hGL4 p hp hp5 (V := ↥P ⧸ frattini ↥P) hVcomm hVexp hcard n hn (Y := Y) ρ
      (e.toMonoidHom.comp φ) hφ'surj
  have hkerφ : (e.toMonoidHom.comp φ).ker = φ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      apply e.injective
      simpa using h
    · intro h
      rw [MonoidHom.comp_apply, h, map_one]
  have hnotker : ¬ ρ.ker ≤ φ.ker := by rwa [hkerφ] at hnotker'
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by
      have : 5 ≤ Nat.card (Fin n) := by simpa using (show 5 ≤ n by omega)
      exact this)
  haveI : IsSimpleGroup ↥Lb := e.isSimpleGroup
  have hnormal : (ρ.ker.map φ).Normal := (MonoidHom.normal_ker ρ).map φ hφsurj
  haveI := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map φ) with hbot | htop
  · exfalso
    apply hnotker
    intro y hy
    have hyimage : φ y ∈ ρ.ker.map φ := Subgroup.mem_map_of_mem φ hy
    rw [hbot, Subgroup.mem_bot] at hyimage
    exact MonoidHom.mem_ker.mpr hyimage
  · exact htop

private theorem rho_apply_eq_one_of_cube_one {X : Type} [Group X] [Finite X]
    {O : Subgroup X} [O.Normal] (hO : ¬ 3 ∣ Nat.card O)
    {Lb : Subgroup (X ⧸ O)} {Y : Subgroup X} (φ : Y →* ↥Lb)
    (hφ_apply : ∀ y : Y, ((φ y : ↥Lb) : X ⧸ O) = QuotientGroup.mk' O (y : X))
    {V : Type} [Group V] (ρ : Y →* MulAut V)
    (hKimage : ρ.ker.map φ = ⊤) {u : X} (huY : u ∈ Y) (hu3 : u ^ 3 = 1) :
    ρ ⟨u, huY⟩ = 1 := by
  classical
  let yu : Y := ⟨u, huY⟩
  have hyu3 : yu ^ 3 = 1 := Subtype.ext hu3
  have hφyu : φ yu ∈ ρ.ker.map φ := by rw [hKimage]; exact Subgroup.mem_top _
  obtain ⟨k, hkK, hkφ⟩ := Subgroup.mem_map.mp hφyu
  let o : Y := k⁻¹ * yu
  have hoKφ : o ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkφ, inv_mul_cancel]
  have hρk : ρ k = 1 := MonoidHom.mem_ker.mp hkK
  have hρo_eq : ρ o = ρ yu := by
    dsimp [o]
    rw [map_mul, map_inv, hρk, inv_one, one_mul]
  have hρyu3 : (ρ yu) ^ 3 = 1 := by
    rw [← map_pow, hyu3, map_one]
  have hρo3 : (ρ o) ^ 3 = 1 := by rw [hρo_eq]; exact hρyu3
  have hoO : (o : X) ∈ O := by
    have h1 : QuotientGroup.mk' O (o : X) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hoKφ)
      rw [hφ_apply o] at h
      exact h
    exact (QuotientGroup.eq_one_iff (o : X)).mp h1
  have hoord : orderOf (o : X) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hoO
  have h3not : ¬ 3 ∣ orderOf (o : X) := fun h => hO (h.trans hoord)
  have hcop3 : Nat.Coprime 3 (orderOf (o : X)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3not
  have horddiv : orderOf (ρ o) ∣ orderOf (o : X) := by
    rw [Subgroup.orderOf_coe o]
    exact orderOf_map_dvd ρ o
  have hord3 : orderOf (ρ o) ∣ 3 := orderOf_dvd_of_pow_eq_one hρo3
  have hρo1 : ρ o = 1 := by
    apply orderOf_eq_one_iff.mp
    exact (Nat.Coprime.coprime_dvd_left hord3 hcop3).eq_one_of_dvd horddiv
  rw [← hρo_eq]
  exact hρo1

private theorem exists_sylow_with_frattini_data {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (O : Subgroup X) [O.Normal] (hO : ¬ 3 ∣ Nat.card O)
    {u₁ u₂ : X} (hu₁ : u₁ ^ 3 = 1) (hu₂ : u₂ ^ 3 = 1) (hu : Commute u₁ u₂)
    (hu₁1 : u₁ ≠ 1) (hu₂z : u₂ ∉ Subgroup.zpowers u₁)
    (hrank : ∀ u ∈ Subgroup.closure ({u₁, u₂} : Set X), u ≠ 1 →
      CFSG.Open.pRank p (O ⊓ Subgroup.centralizer ({u} : Set X)) ≤ 1) :
    ∃ P : Subgroup X, CFSG.ABGLocalTools.IsSylowOf p P O ∧
      Subgroup.closure ({u₁, u₂} : Set X) ≤ Subgroup.normalizer (P : Set X) ∧
      Nat.card (↥P ⧸ frattini ↥P) ≤ p ^ 4 ∧
      Subgroup.normalizer (P : Set X) ⊔ O = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let U : Subgroup X := Subgroup.closure ({u₁, u₂} : Set X)
  have hcardU : Nat.card U = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hu₁ hu₂ hu hu₁1 hu₂z
  have hU3 : IsPGroup 3 ↥U := IsPGroup.of_card (n := 2) (by rw [hcardU]; norm_num)
  have hUO : U ≤ Subgroup.normalizer (O : Set X) := by
    rw [Subgroup.normalizer_eq_top O]
    exact le_top
  obtain ⟨Q, hUQ⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three U O hU3 hO hUO p hp
  let P : Subgroup X := (Q : Subgroup ↥O).map O.subtype
  have hP : CFSG.ABGLocalTools.IsSylowOf p P O := ⟨Q, rfl⟩
  have hUP : U ≤ Subgroup.normalizer (P : Set X) := hUQ
  have hPpg : IsPGroup p ↥P := hP.isPGroup
  have hrankP : ∀ u ∈ U, u ≠ 1 →
      CFSG.Open.pRank p (P ⊓ Subgroup.centralizer ({u} : Set X)) ≤ 1 := by
    intro u huU hu1
    refine (CFSG.SectionRank.pRank_mono hp.one_lt (inf_le_inf hP.le le_rfl)).trans
      (hrank u huU hu1)
  have hPcard : Nat.card (↥P ⧸ frattini ↥P) ≤ p ^ 4 :=
    card_frattini_quotient_le_pow_four hp (by omega) (by omega) hPpg hu₁ hu₂ hu hu₁1 hu₂z hUP
      hrankP
  have hfrattini : Subgroup.normalizer (P : Set X) ⊔ O = ⊤ := by
    have := Sylow.normalizer_sup_eq_top Q
    simpa [P] using this
  exact ⟨P, hP, hUP, hPcard, hfrattini⟩

theorem exists_isSylowOf_le_centralizer_of_alternating (hGL4 : KFactA9NotInvolvedGL4)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (O : Subgroup X) [O.Normal] (hO : ¬ 3 ∣ Nat.card O) (Lb : Subgroup (X ⧸ O))
    (h3 : ∀ x : X ⧸ O, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Lb)
    {n : ℕ} (hn : 9 ≤ n) (e : ↥Lb ≃* alternatingGroup (Fin n))
    {u₁ u₂ : X} (hu₁ : u₁ ^ 3 = 1) (hu₂ : u₂ ^ 3 = 1) (hu : Commute u₁ u₂) (hu₁1 : u₁ ≠ 1)
    (hu₂z : u₂ ∉ Subgroup.zpowers u₁)
    (hrank : ∀ u ∈ Subgroup.closure ({u₁, u₂} : Set X), u ≠ 1 →
      CFSG.Open.pRank p (O ⊓ Subgroup.centralizer ({u} : Set X)) ≤ 1) :
    ∃ P : Subgroup X, CFSG.ABGLocalTools.IsSylowOf p P O ∧
      Subgroup.closure ({u₁, u₂} : Set X) ≤ Subgroup.centralizer (P : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let U : Subgroup X := Subgroup.closure ({u₁, u₂} : Set X)
  obtain ⟨P, hP, hUP, hPcard, hfrattini⟩ :=
    exists_sylow_with_frattini_data hp hp5 O hO hu₁ hu₂ hu hu₁1 hu₂z hrank
  have hPpg : IsPGroup p ↥P := hP.isPGroup
  obtain ⟨Y, φ, hYdef, hφsurj, hφ_apply⟩ := frattini_surjection hfrattini Lb
  have hYN : Y ≤ Subgroup.normalizer (P : Set X) := by
    rw [hYdef]
    exact inf_le_left
  have hΦchar : (frattini ↥P).Characteristic :=
    (CFSG.GroupTheory.frattini_elementary_quotient hPpg).1
  letI : (frattini ↥P).Characteristic := hΦchar
  let ρ : Y →* MulAut (↥P ⧸ frattini ↥P) :=
    (CFSG.SectionRank.Ccomm.autQuotient (frattini ↥P)).comp
      ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hYN))
  have hVcomm : IsMulCommutative (↥P ⧸ frattini ↥P) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hPpg).2.1
  have hVexp : ∀ v : ↥P ⧸ frattini ↥P, v ^ p = 1 :=
    (CFSG.GroupTheory.frattini_elementary_quotient hPpg).2.2.1
  have hKimage : ρ.ker.map φ = ⊤ :=
    rho_ker_map_eq_top hp hp5 hPpg hn e φ hφsurj ρ hGL4 hVcomm hVexp hPcard
  have hcentralize : ∀ u ∈ U, u ^ 3 = 1 →
      u ∈ Subgroup.centralizer (P : Set X) := by
    intro u huU hu3
    have huY : u ∈ Y := mem_frattiniPreimage_of_cube_one hYdef h3 (hUP huU) hu3
    have hρ : ρ ⟨u, huY⟩ = 1 :=
      rho_apply_eq_one_of_cube_one hO φ hφ_apply ρ hKimage huY hu3
    have hα : CFSG.SectionRank.Ccomm.autQuotient (frattini ↥P)
        (Subgroup.normalizerMonoidHom P ⟨u, hYN huY⟩) = 1 := hρ
    exact centralizes_of_autQuotient_eq_one hp (by omega) hPpg (hYN huY) hu3 hα
  refine ⟨P, hP, ?_⟩
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  have hx' : x = u₁ ∨ x = u₂ := by simpa using hx
  rcases hx' with h | h
  · rw [h]
    exact hcentralize u₁ (Subgroup.subset_closure (by simp)) hu₁
  · rw [h]
    exact hcentralize u₂ (Subgroup.subset_closure (by simp)) hu₂

theorem pRank_le_one_of_alternating (hGL4 : KFactA9NotInvolvedGL4)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (O : Subgroup X) [O.Normal] (hO : ¬ 3 ∣ Nat.card O) (Lb : Subgroup (X ⧸ O))
    (h3 : ∀ x : X ⧸ O, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Lb)
    {n : ℕ} (hn : 9 ≤ n) (e : ↥Lb ≃* alternatingGroup (Fin n))
    {u₁ u₂ : X} (hu₁ : u₁ ^ 3 = 1) (hu₂ : u₂ ^ 3 = 1) (hu : Commute u₁ u₂) (hu₁1 : u₁ ≠ 1)
    (hu₂z : u₂ ∉ Subgroup.zpowers u₁)
    (hrank : ∀ u ∈ Subgroup.closure ({u₁, u₂} : Set X), u ≠ 1 →
      CFSG.Open.pRank p (O ⊓ Subgroup.centralizer ({u} : Set X)) ≤ 1) :
    CFSG.Open.pRank p O ≤ 1 ∧
      (p ∣ Nat.card O → p ∣ Nat.card ↥(O ⊓ Subgroup.centralizer ({u₁} : Set X))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let U : Subgroup X := Subgroup.closure ({u₁, u₂} : Set X)
  have hu1U : u₁ ∈ U := Subgroup.subset_closure (by simp)
  obtain ⟨P, hP, hUP⟩ :=
    exists_isSylowOf_le_centralizer_of_alternating hGL4 hp hp5 O hO Lb h3 hn e hu₁ hu₂ hu
      hu₁1 hu₂z hrank
  have hPpg : IsPGroup p ↥P := hP.isPGroup
  have hPleC : P ≤ O ⊓ Subgroup.centralizer ({u₁} : Set X) := by
    refine le_inf hP.le ?_
    intro x hxP
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hUP hu1U) x hxP)
  constructor
  · have hrank_eq : CFSG.Open.pRank p P = CFSG.Open.pRank p O :=
      CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow hp hP
    rw [← hrank_eq]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt hPleC).trans
      (hrank u₁ hu1U hu₁1)
  · intro hpO
    have hfac : 1 ≤ (Nat.card O).factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp
        (Nat.card_ne_zero.mpr ⟨⟨1, O.one_mem⟩, inferInstance⟩)).mp hpO
    have hpP : p ∣ Nat.card ↥P := by
      rw [hP.card_eq]
      simpa using Nat.pow_dvd_pow p hfac
    exact hpP.trans (Subgroup.card_dvd_of_le hPleC)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
