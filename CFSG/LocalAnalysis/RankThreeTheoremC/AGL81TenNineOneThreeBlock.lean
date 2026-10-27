module

import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ASevenBlock

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbedding.BlockAltSevenPL
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_two_three {P₂ P₃ : Subgroup G} (h₂ : IsPGroup 2 P₂) (h₃ : IsPGroup 3 P₃)
    {x : G} (hx₂ : x ∈ P₂) (hx₃ : x ∈ P₃) : x = 1 := by
  obtain ⟨i, hi⟩ := h₂ ⟨x, hx₂⟩
  obtain ⟨j, hj⟩ := h₃ ⟨x, hx₃⟩
  have hdi : orderOf x ∣ 2 ^ i :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hi)
  have hdj : orderOf x ∣ 3 ^ j :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hj)
  have hcop : Nat.Coprime (2 ^ i) (3 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hdi) hdj)

theorem perm_fin_seven_pow_three {σ : Equiv.Perm (Fin 7)} (h : σ ^ 9 = 1) : σ ^ 3 = 1 := by
  have hd : orderOf σ ∣ 9 := orderOf_dvd_of_pow_eq_one h
  rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.mpr fun n hn => ?_
  have h1 : n ∣ 3 ^ 2 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans hd
  have h2 : n ≤ 7 := (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
    ((Finset.card_le_univ _).trans (by simp))
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  interval_cases k
  · simp
  · simp
  · norm_num at h2

theorem directProd_of_nineThreeFive (h86 : Asc81bEightSix) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (h5 : NineThreeFive M L) {Q' : Subgroup G} (hQ3 : IsPGroup 3 Q')
    (hQS : Q' ≤ normalizer (S : Set G)) (hQL : Q' ≤ normalizer (L : Set G))
    (h9 : 9 ∣ Nat.card ↥(Q' ⊓ L)) :
    ∃ C : Subgroup G, C ≤ Q' ∧ IsElemAbelian 3 (Q' ⊓ L) ∧ Nat.card ↥(Q' ⊓ L) = 9 ∧
      (∀ a ∈ Q' ⊓ L, ∀ c ∈ C, Commute a c) ∧ (Q' ⊓ L) ⊓ C = ⊥ ∧ (Q' ⊓ L) ⊔ C = Q' := by
  obtain ⟨hsh, ⟨e⟩, hU⟩ := h5
  have hLc := hL.toIsTwoPrimeComponent
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    hLc.le_normalizer (h86 G M S hK hA _ hLc.component) hA.twoRadical.1
  set N := Subgroup.normalizer (L : Set G)
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hNU : N ≤ Subgroup.normalizer (blockU L : Set G) := fun _ hg =>
    QuasithinUnique.C1.mem_normalizer_blockU hg
  set ρ : ↥N →* MulAut ↥(blockU L) := (blockU L).normalizerMonoidHom.comp (Subgroup.inclusion hNU)
  have hρ : ∀ (n : ↥N) (u : ↥(blockU L)), ((ρ n u : ↥(blockU L)) : G) = n * u * n⁻¹ :=
    fun _ _ => rfl
  obtain ⟨hΓ, hΓs⟩ := card_mulAut_eq_and_isSimpleGroup (W := ↥(blockU L))
    (fun a b => Subtype.ext (QuasithinUnique.C1.blockU_comm hsh a a.2 b
      (QuasithinUnique.C1.blockU_le_blockQ hsh b.2)))
    (fun a => Subtype.ext (QuasithinUnique.C1.blockU_sq hsh a a.2)) hU
  have : Finite (MulAut ↥(blockU L)) := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  set π : ↥L →* ↥M ⧸ CFSG.pCore 2 ↥M := (QuotientGroup.mk' _).comp (Subgroup.inclusion hLc.le)
  set ρL : ↥L →* MulAut ↥(blockU L) := ρ.comp (Subgroup.inclusion hLN)
  have hker : π.ker = ρL.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have e1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hLc.le l) = 1 ↔
        Subgroup.inclusion hLc.le l ∈ CFSG.pCore 2 ↥M := QuotientGroup.eq_one_iff _
    change QuotientGroup.mk' _ (Subgroup.inclusion hLc.le l) = 1 ↔ ρ ⟨l, hLN l.2⟩ = 1
    rw [e1, BlockAltSevenPL.conj_eq_one_iff_mem_pCoreOf hsh hρ (n := ⟨l, hLN l.2⟩) l.2,
      ← hLc.inf_twoCore]
    constructor
    · intro h
      have h' : (l : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨_, h, rfl⟩
      exact ⟨l.2, h'⟩
    · rintro ⟨-, m, hm, hml⟩
      rw [show Subgroup.inclusion hLc.le l = m from Subtype.ext hml.symm]
      exact hm
  have himg : ∀ X : Subgroup G, X ≤ L → (X.subgroupOf L).map ρL = (X.subgroupOf N).map ρ :=
    fun X hXL => by rw [← Subgroup.map_map, map_inclusion_subgroupOf hXL hLN]
  set H := (L.subgroupOf N).map ρ
  obtain ⟨θ₀⟩ := nonempty_mulEquiv_range_of_ker_eq hker
  have hHr : ρL.range = H := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self L, himg L le_rfl]
  have hπr : π.range = barM M L := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self L, barM,
      ← map_inclusion_subgroupOf le_rfl hLc.le, Subgroup.map_map]
  let θ : ↥H ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.subgroupCongr hHr.symm).trans (θ₀.symm.trans ((MulEquiv.subgroupCongr hπr).trans e))
  have hH : Nat.card H = 2520 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hNH : ∀ n : ↥N, ρ n ∈ H := fun n => by
    have hn : Subgroup.normalizer ((L.subgroupOf N : Subgroup ↥N) : Set ↥N) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_in_normalizer
    exact mem_of_mem_normalizer_of_index_eight hΓ hH
      (Subgroup.le_normalizer_map ρ ⟨n, by rw [hn]; trivial, rfl⟩)
  set T := (S.subgroupOf N).map ρ
  have hTH : T ≤ H := by
    rintro _ ⟨n, -, rfl⟩
    exact hNH n
  have hT2 : IsPGroup 2 T := (hA.twoRadical.isPGroup.comap_subtype (K := N)).map ρ
  have hT1 : T ≠ ⊥ := by
    obtain ⟨s, hs, hρs⟩ := BlockAltSevenPL.exists_mem_conj_blockU_ne_one hA hL hsh hρ hSL
    intro hbot
    have hmem : ρ ⟨s, hSL hs⟩ ∈ T := ⟨⟨s, hSL hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hρs hmem
  set R := (Q'.subgroupOf N).map ρ
  have hRH : R ≤ H := by
    rintro _ ⟨n, -, rfl⟩
    exact hNH n
  have hRT : R ≤ Subgroup.normalizer (T : Set (MulAut ↥(blockU L))) := by
    rintro _ ⟨n, hn, rfl⟩
    have hnS : n ∈ Subgroup.normalizer ((S.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hSL]
      exact Subgroup.mem_subgroupOf.mpr (hQS (Subgroup.mem_subgroupOf.mp hn))
    exact Subgroup.le_normalizer_map ρ ⟨n, hnS, rfl⟩
  have hR72 := card_dvd_seventyTwo_of_mulEquiv θ (T := T.subgroupOf H) (P := R.subgroupOf H)
    hT2.comap_subtype (fun h => hT1 ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hTH))
    (fun p hp => by
      rw [← Subgroup.subgroupOf_normalizer_eq hTH]
      exact Subgroup.mem_subgroupOf.mpr (hRT (Subgroup.mem_subgroupOf.mp hp)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv] at hR72
  have hR3 : IsPGroup 3 R := (hQ3.comap_subtype (K := N)).map ρ
  have hR9 : Nat.card R ≤ 9 := by
    obtain ⟨k, hk⟩ := hR3.exists_card_eq
    rw [hk] at hR72 ⊢
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have : 3 ^ 3 ∣ 72 := (pow_dvd_pow 3 (by omega)).trans hR72
      exact absurd this (by decide)
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  set A := Q' ⊓ L
  have hAQ : A ≤ Q' := inf_le_left
  have hAL : A ≤ L := inf_le_right
  have hA3 : IsPGroup 3 A := hQ3.to_le hAQ
  have hO2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 L
  have hinjA : ∀ a (ha : a ∈ A), ρ ⟨a, hQL (hAQ ha)⟩ = 1 → a = 1 := fun a ha h1 => by
    have := (BlockAltSevenPL.conj_eq_one_iff_mem_pCoreOf hsh hρ
      (n := ⟨a, hQL (hAQ ha)⟩) (hAL ha)).mp h1
    exact eq_one_of_mem_two_three hO2 hA3 this ha
  set ρA : ↥A →* MulAut ↥(blockU L) := ρ.comp (Subgroup.inclusion (hAQ.trans hQL))
  have hρAinj : Function.Injective ρA := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hinjA a a.2 ha)
  have hρAR : ρA.range ≤ R := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a, hQL (hAQ a.2)⟩, Subgroup.mem_subgroupOf.mpr (hAQ a.2), rfl⟩
  have hcardA : Nat.card A = Nat.card ρA.range :=
    Nat.card_congr (MonoidHom.ofInjective hρAinj).toEquiv
  have hA9 : Nat.card A = 9 := by
    have h1 : Nat.card A ≤ 9 := hcardA ▸ (Subgroup.card_le_of_le hρAR).trans hR9
    obtain ⟨k, hk⟩ := h9
    have : 0 < Nat.card A := Nat.card_pos
    have : k = 1 := by
      rcases k with _ | _ | k <;> omega
    omega
  have hρAeq : ρA.range = R :=
    Subgroup.eq_of_le_of_card_ge hρAR (by rw [← hcardA, hA9]; exact hR9)
  set C : Subgroup G := Q' ⊓ ρ.ker.map N.subtype
  have hCQ : C ≤ Q' := inf_le_left
  have hCker : ∀ c ∈ C, ∃ hc : c ∈ N, ρ ⟨c, hc⟩ = 1 := by
    rintro c ⟨-, n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  have hdisj : A ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxC⟩
    obtain ⟨hxN, hx1⟩ := hCker x hxC
    exact (Subgroup.mem_bot).mpr (hinjA x hxA hx1)
  have hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c := by
    intro a ha c hc
    obtain ⟨hcN, hc1⟩ := hCker c hc
    have haN : a ∈ N := hQL (hAQ ha)
    set k := a * c * a⁻¹ * c⁻¹
    have hkL : k ∈ L := by
      have h1 : c * a⁻¹ * c⁻¹ ∈ L := (mem_normalizer_iff.mp hcN a⁻¹).mp (L.inv_mem (hAL ha))
      have : k = a * (c * a⁻¹ * c⁻¹) := by simp only [k]; group
      rw [this]
      exact L.mul_mem (hAL ha) h1
    have hkQ : k ∈ Q' :=
      Q'.mul_mem (Q'.mul_mem (Q'.mul_mem (hAQ ha) (hCQ hc)) (Q'.inv_mem (hAQ ha)))
        (Q'.inv_mem (hCQ hc))
    have hk1 : ρ ⟨k, hQL hkQ⟩ = 1 := by
      have : (⟨k, hQL hkQ⟩ : ↥N) = ⟨a, haN⟩ * ⟨c, hcN⟩ * ⟨a, haN⟩⁻¹ * ⟨c, hcN⟩⁻¹ :=
        Subtype.ext (by simp [k])
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hc1]
      group
    have hkO := (BlockAltSevenPL.conj_eq_one_iff_mem_pCoreOf hsh hρ
      (n := ⟨k, hQL hkQ⟩) hkL).mp hk1
    have hk : k = 1 := eq_one_of_mem_two_three hO2 hQ3 hkO hkQ
    have : a * c = c * a := by
      have := congrArg (· * (c * a)) hk
      simp only [k, one_mul] at this
      rw [← this]; group
    exact this
  have hgen : A ⊔ C = Q' := by
    refine le_antisymm (sup_le hAQ hCQ) fun q hq => ?_
    have hqR : ρ ⟨q, hQL hq⟩ ∈ R := ⟨⟨q, hQL hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [← hρAeq] at hqR
    obtain ⟨a, ha⟩ := hqR
    have hcN : (a : G)⁻¹ * q ∈ N := N.mul_mem (N.inv_mem (hQL (hAQ a.2))) (hQL hq)
    have hc : (a : G)⁻¹ * q ∈ C := by
      refine ⟨Q'.mul_mem (Q'.inv_mem (hAQ a.2)) hq, ⟨(a : G)⁻¹ * q, hcN⟩, ?_, rfl⟩
      change ρ ⟨(a : G)⁻¹ * q, hcN⟩ = 1
      have : (⟨(a : G)⁻¹ * q, hcN⟩ : ↥N) = (⟨a, hQL (hAQ a.2)⟩ : ↥N)⁻¹ * ⟨q, hQL hq⟩ :=
        Subtype.ext (by simp)
      rw [this, map_mul, map_inv]
      change (ρA a)⁻¹ * _ = 1
      rw [ha, inv_mul_cancel]
    have : q = (a : G) * ((a : G)⁻¹ * q) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right hc)
  have hAel : IsElemAbelian 3 A := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hAc := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := ↥A) (by rw [hA9]; norm_num)
    refine ⟨⟨⟨hAc⟩⟩, fun a ha => ?_⟩
    have h9a : (⟨a, ha⟩ : ↥A) ^ 9 = 1 := by
      rw [← hA9]; exact pow_card_eq_one'
    set σ := θ ⟨ρA ⟨a, ha⟩, hNH _⟩
    have hσ9 : ((σ : Equiv.Perm (Fin 7))) ^ 9 = 1 := by
      have : σ ^ 9 = 1 := by
        rw [← map_pow]
        have : (⟨ρA ⟨a, ha⟩, hNH _⟩ : ↥H) ^ 9 = 1 :=
          Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, h9a, map_one, Subgroup.coe_one])
        rw [this, map_one]
      exact congrArg Subtype.val this
    have hσ3 : σ ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]; exact perm_fin_seven_pow_three hσ9)
    have h3 : (⟨a, ha⟩ : ↥A) ^ 3 = 1 := by
      apply hρAinj
      rw [map_pow, map_one]
      have : (⟨ρA ⟨a, ha⟩, hNH _⟩ : ↥H) ^ 3 = 1 := by
        apply θ.injective
        rw [map_pow, map_one]
        exact hσ3
      exact congrArg Subtype.val this
    exact congrArg Subtype.val h3
  exact ⟨C, hCQ, hAel, hA9, hcomm, hdisj, hgen⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.ASevenBlock
