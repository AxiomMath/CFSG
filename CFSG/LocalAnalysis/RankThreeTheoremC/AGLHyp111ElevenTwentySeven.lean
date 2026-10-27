module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySix
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenCfgChain
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111AltSixIrred
import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Exc
import CFSG.Goldschmidt.Steps.Sec82e
import CFSG.HardMathSupport.Cooperstein.Proving.TwoPrimeSup
import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JZeroTwoHolds
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Semidihedral.PrimeOrderCyclicConfinementLift (normalizer_le_of_characteristic_subgroupOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81TenThreeOneAt : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), 3 ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I₀)

variable (G) in
@[expose] def AGL81TenThreeTwoAt : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ I₀ ∈ cZero (H ⊓ L), ¬ IsTwoPrimeComponent I₀ I₀) →
    ∀ q : ℕ, q.Prime → q ∣ Nat.card (jOne H L) → q = 2 ∨ q = 3

variable (G) in
@[expose] def AGL81TenOneCZero : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    IsEmpty (↥(barM M L) ≃* alternatingGroup (Fin 7)) → (cZero (H ⊓ L)).Nonempty

variable (G) in
@[expose] def AGL81TenOneCenterRank : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (L.subgroupOf M).Normal → ∀ V : Subgroup G, V ≤ L → IsElemAbelian 3 V →
    (∀ v ∈ V, ∀ l ∈ L, v * l * v⁻¹ * l⁻¹ ∈ pCoreOf 2 L) → Nat.card V ≤ 3

theorem not_two_dvd_index_sup_of_centralizes {A T Y : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hc : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ ∈ pCoreOf 2 Y)
    (hmax : ∀ S : Subgroup G, S ≤ T ⊔ Y → IsPGroup 2 S →
      A ≤ Subgroup.normalizer (S : Set G) → T ≤ S → S = T) :
    ¬ 2 ∣ (T.subgroupOf (T ⊔ Y)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := T ⊔ Y with hD
  obtain ⟨S, hS⟩ := (hT2.comap_subtype (K := D)).exists_le_sylow
  set S' : Subgroup G := (S : Subgroup D).map D.subtype with hS'
  have hTS' : T ≤ S' := fun t ht => ⟨⟨t, (le_sup_left : T ≤ D) ht⟩, hS ht, rfl⟩
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  have hS'D : S' ≤ D := Subgroup.map_subtype_le _
  have hDY : D ≤ Subgroup.normalizer (Y : Set G) := sup_le hTY Subgroup.le_normalizer
  have hOD : pCoreOf 2 Y ≤ D :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 Y).trans le_sup_right
  have hOn : ((pCoreOf 2 Y).subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOD).mpr
      (hDY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
  have hOS : pCoreOf 2 Y ≤ S' := by
    intro x hx
    have h1 := (IsPGroup.le_sylow_of_normal (N := (pCoreOf 2 Y).subgroupOf D)
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Y).comap_subtype) S)
      (show (⟨x, hOD hx⟩ : D) ∈ (pCoreOf 2 Y).subgroupOf D from hx)
    exact ⟨_, h1, rfl⟩
  have hAS : A ≤ Subgroup.normalizer ((S' ⊓ Y : Subgroup G) : Set G) := by
    intro a ha
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have hc' := hc a ha x hx.2
    have hy : a * x * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hAY ha) x).mp hx.2
    refine ⟨?_, hy⟩
    have : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
    rw [this]
    exact S'.mul_mem (hOS hc') hx.1
  have heq := hmax (T ⊔ (S' ⊓ Y)) (sup_le le_sup_left (inf_le_right.trans le_sup_right))
    (hS'2.to_le (sup_le hTS' inf_le_left))
    (CFSG.Goldschmidt.G310.le_normalizer_sup hAT hAS) le_sup_left
  have hSYT : S' ⊓ Y ≤ T := heq ▸ le_sup_right
  have hS'T : S' ≤ T := by
    intro x hx
    have hxD : x ∈ (T : Set G) * (Y : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T Y hTY]
      exact hS'D hx
    obtain ⟨t, ht, y, hy, rfl⟩ := Set.mem_mul.mp hxD
    have hyS : y ∈ S' := by
      have := S'.mul_mem (S'.inv_mem (hTS' ht)) hx
      simpa using this
    exact T.mul_mem ht (hSYT ⟨hyS, hy⟩)
  have hSeq : (S : Subgroup D) = T.subgroupOf D := by
    have h1 : S' = T := le_antisymm hS'T hTS'
    rw [← h1, hS']
    exact (Subgroup.comap_map_eq_self_of_injective D.subtype_injective _).symm
  rw [← hSeq]
  exact S.not_dvd_index

theorem isElemAbelian_sylow_of_isAltTwoP {K : Type} [Group K] [Finite K] (hK : IsAltTwoP 3 K)
    (S : Sylow 3 K) : IsElemAbelian 3 (S : Subgroup K) ∧ Nat.card (S : Subgroup K) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hK
  have hcard : Nat.card K = 360 := card_of_isAltTwoP_three ⟨e⟩
  have hS9 : Nat.card (S : Subgroup K) = 9 := by
    have hf : Nat.factorization (Nat.card K) 3 = 2 := by
      rw [hcard, Nat.factorization_def _ Nat.prime_three,
        show (360 : ℕ) = 3 ^ 2 * 40 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [Sylow.card_eq_multiplicity, hf]
    norm_num
  have hcomm : ∀ a b : (S : Subgroup K), a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [hS9]; norm_num)
  refine ⟨⟨⟨⟨hcomm⟩⟩, fun x hx => ?_⟩, hS9⟩
  have h9 : (⟨x, hx⟩ : (S : Subgroup K)) ^ 9 = 1 := by
    have := pow_card_eq_one' (G := (S : Subgroup K)) (x := ⟨x, hx⟩)
    rwa [hS9] at this
  have h9' : x ^ 9 = 1 := by
    have := congrArg (fun y : (S : Subgroup K) => (y : K)) h9
    simpa using this
  have h9'' : ((e x : alternatingGroup (Fin (2 * 3))) : Equiv.Perm (Fin 6)) ^ 9 = 1 := by
    have := congrArg (fun y : alternatingGroup (Fin (2 * 3)) => (y : Equiv.Perm (Fin 6)))
      (show e x ^ 9 = 1 by rw [← map_pow, h9', map_one])
    simpa using this
  have h3 := CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.perm_six_pow_nine _ h9''
  have he3 : e (x ^ 3) = 1 := by
    rw [map_pow]
    exact Subtype.ext (by simpa using h3)
  exact (map_eq_one_iff e e.injective).mp he3

theorem d1LiftX_facts {P : Sylow 3 G} {M H R : Subgroup G} (he : D1Escape 3 P M H R)
    (hA6 : IsAltTwoP 3 (d1KBar 3 M H)) [(d1KBar 3 M H).Normal] :
    d1LiftX 3 H R (d1KBar 3 M H) ⊓ d1PlusCore 3 H (d1KBar 3 M H) = ⊥ ∧
      IsElemAbelian 3 (d1LiftX 3 H R (d1KBar 3 M H)) ∧
      Nat.card (d1LiftX 3 H R (d1KBar 3 M H)) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := d1KBar 3 M H with hKdef
  set O := primeComplementCore (G := H) 3 with hOdef
  set π := QuotientGroup.mk' O with hπ
  set A := d1LiftX 3 H R K with hA
  have hAR : A ≤ R := d1LiftX_le 3 H R K
  have hAH : A ≤ H := hAR.trans he.le_H
  set A' := A.subgroupOf H with hA'
  have hA'3 : IsPGroup 3 A' := (he.isPGroup.to_le hAR).comap_subtype
  have hAO : A' ⊓ O = ⊥ := by
    obtain ⟨n, hn⟩ := hA'3.exists_card_eq
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hn]
    exact (primeComplementCore_coprime (G := H) 3).pow_left n
  have hinj : ∀ a ∈ A', π a = 1 → a = 1 := fun a ha h1 => by
    have hO : a ∈ O := (QuotientGroup.eq_one_iff a).mp h1
    have : a ∈ A' ⊓ O := ⟨ha, hO⟩
    rwa [hAO, Subgroup.mem_bot] at this
  obtain ⟨e⟩ := hA6
  have hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1 := by
    intro k hk
    have hc : e k ∈ Subgroup.center (alternatingGroup (Fin (2 * 3))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hk k']
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    exact (map_eq_one_iff e e.injective).mp hc
  refine ⟨?_, ?_⟩
  ·
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ⟨haR, haK⟩, rfl⟩, ⟨b, hbC, hba⟩⟩
    have hab : b = a := Subtype.ext hba
    subst hab
    have hz : π b = 1 := by
      have := hZ ⟨π b, haK⟩ fun k' =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hbC) k' k'.2).symm
      exact congrArg Subtype.val this
    have hbA : b ∈ A' := by
      show (b : G) ∈ A
      exact ⟨b, ⟨haR, haK⟩, rfl⟩
    rw [Subgroup.mem_bot, hinj b hbA hz]
    rfl
  ·
    obtain ⟨S₀, hS₀⟩ := he.isSylow
    obtain ⟨S, hS⟩ := sylowK_of_sylow (K := K) S₀ hS₀
    have hmap : A'.map π = (S : Subgroup K).map K.subtype := by
      rw [hS, hA', hA, map_d1LiftX]
    set φ : A' →* H ⧸ O := π.comp A'.subtype with hφ
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro a ha
      exact Subtype.ext (hinj a a.2 ha)
    have hφr : φ.range = (S : Subgroup K).map K.subtype := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hmap]
    let f : A ≃* S :=
      ((Subgroup.subgroupOfEquivOfLe hAH).symm.trans (MonoidHom.ofInjective hφinj)).trans
        ((MulEquiv.subgroupCongr hφr).trans
          (Subgroup.equivMapOfInjective (S : Subgroup K) K.subtype K.subtype_injective).symm)
    obtain ⟨hSe, hS9⟩ := isElemAbelian_sylow_of_isAltTwoP ⟨e⟩ S
    refine ⟨⟨⟨⟨fun a b => f.injective ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · rw [map_mul, map_mul]
      exact isMulCommutative_iff.mp hSe.1 _ _
    · have h1 : f (⟨x, hx⟩ ^ 3) = 1 := by
        rw [map_pow]
        exact Subtype.ext (hSe.2 _ (f ⟨x, hx⟩).2)
      have h2 := (map_eq_one_iff f f.injective).mp h1
      simpa using congrArg Subtype.val h2
    · rw [Nat.card_congr f.toEquiv, hS9]

theorem exists_centralizing_of_three_dvd {A V : Subgroup G} (hA : IsPGroup 3 A)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (h3 : 3 ∣ Nat.card V) :
    ∃ y ∈ V, orderOf y = 3 ∧ ∀ a ∈ A, a * y = y * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := A ⊔ V with hW
  have hWV : W ≤ Subgroup.normalizer (V : Set G) := sup_le hAV Subgroup.le_normalizer
  obtain ⟨P, hP⟩ := (hA.comap_subtype (K := W)).exists_le_sylow
  set P' : Subgroup G := (P : Subgroup W).map W.subtype with hP'
  have hP'W : P' ≤ W := Subgroup.map_subtype_le _
  have hAP' : A ≤ P' := fun a ha => ⟨⟨a, (le_sup_left : A ≤ W) ha⟩, hP ha, rfl⟩
  have hP'3 : IsPGroup 3 P' := P.isPGroup'.map _
  have hP'V : P' ≤ Subgroup.normalizer (V : Set G) := hP'W.trans hWV
  have hne : P' ⊓ V ≠ ⊥ := by
    intro hb
    have hprod := card_sup_mul_card_inf_of_le_normalizer hP'V
    rw [hb, Subgroup.card_bot, mul_one] at hprod
    have hle : P' ⊔ V ≤ W := sup_le hP'W le_sup_right
    have hri : P'.relIndex (P' ⊔ V) = Nat.card V := by
      have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) P' (P' ⊔ V) bot_le le_sup_left
      rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h1
      have hpos : 0 < Nat.card P' := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [h1, hprod]
    have hdvd : P'.relIndex (P' ⊔ V) ∣ P'.relIndex W :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex P' (P' ⊔ V) W le_sup_left hle)
    have hPi : P'.relIndex W = (P : Subgroup W).index := by
      show (P'.comap W.subtype).index = _
      rw [hP', Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
    exact P.not_dvd_index (hPi ▸ (hri ▸ h3).trans hdvd)
  haveI : Group.IsNilpotent P' := hP'3.isNilpotent
  set N : Subgroup P' := (P' ⊓ V).subgroupOf P' with hN
  haveI hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnV : (n : G) ∈ V := hn.2
    refine ⟨P'.mul_mem (P'.mul_mem g.2 n.2) (P'.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hP'V g.2) n).mp hnV
  have hN1 : N ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : P') ∈ N := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  obtain ⟨⟨z, hzN, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
  set y₀ : G := ((z : P') : G) with hy₀
  have hy₀V : y₀ ∈ V := hzN.2
  have hy₀1 : y₀ ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext (Subtype.ext h))
  have hy₀c : ∀ a ∈ A, a * y₀ = y₀ * a := by
    intro a ha
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨a, hAP' ha⟩)
    simp only [Subgroup.coe_mul] at this
    exact this
  obtain ⟨n, hn⟩ := hP'3 (z : P')
  have hord : orderOf y₀ ∣ 3 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hy₀1 (orderOf_eq_one_iff.mp (by simpa using hk))
  refine ⟨y₀ ^ (3 ^ (k - 1)), V.pow_mem hy₀V _, ?_, fun a ha => ?_⟩
  · rw [orderOf_pow' _ (pow_ne_zero _ (by norm_num)), hk,
      Nat.gcd_eq_right (pow_dvd_pow 3 (Nat.sub_le k 1)), Nat.pow_div (Nat.sub_le k 1) (by norm_num),
      show k - (k - 1) = 1 by omega, pow_one]
  · exact (Commute.pow_right (hy₀c a ha) _).eq

theorem normalizer_le_of_three_dvd (hS : Setting G) (h9 : AGL81NineCompetitorQ G)
    (h98 : AGL81NineEightTwo G) (h984 : AGL81NineEightFour G)
    (h101 : AGL81TenOneExists G) (h115 : AGL81ElevenFiveAt G) (h3σ : 3 ∈ rankThreeSigmaA G)
    (hKR : KFactNineThreeRankOne)
    (hKA : KFactNineThreeInvolvedA6L34)
    (hKC : KFactNineThreeComponentL34) {P : Sylow 3 G} {M H R : Subgroup G}
    (he : D1Escape 3 P M H R) (hA6 : IsAltTwoP 3 (d1KBar 3 M H))
    (hcex : ¬ ElevenTwentyConcl M) {A T Y C : Subgroup G} (hA : IsAGLQ 3 M A) (hAH : A ≤ H)
    (hAe : IsElemAbelian 3 A) (hAc : Nat.card A = 9)
    (hT : IsMaxInvariantTwoIn A T (d1PlusCore 3 H (d1KBar 3 M H))) (hYM : Y ≤ M)
    (hAY : A ⊓ Y = ⊥) (hAYn : A ≤ Subgroup.normalizer (Y : Set G)) (hCT : C ≤ T) (hC1 : C ≠ ⊥)
    (hCc : (C.subgroupOf T).Characteristic)
    (h3 : 3 ∣ Nat.card (Y ⊓ Subgroup.normalizer (C : Set G) : Subgroup G)) :
    Subgroup.normalizer (C : Set G) ≤ H := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hatH, -, -, hOH, hHM, hKX⟩ := escape_local hS h9 h98 h984 hKC he hA6
  have hNTC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    normalizer_le_of_characteristic_subgroupOf
      hCT hCc
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := hT.2.2.1.trans hNTC
  set V := Y ⊓ Subgroup.normalizer (C : Set G) with hV
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    (le_inf hAYn (hAC.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨y, hyV, hy3, hyc⟩ := exists_centralizing_of_three_dvd hA.2.1 hAV h3
  have hyA : y ∉ A := fun hyA => by
    have : y ∈ A ⊓ Y := ⟨hyA, hyV.1⟩
    rw [hAY, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hy3
    norm_num at hy3
  have hy3' : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
  obtain ⟨hEe, hEc⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers hp hAc hAe.2 hy3' hyA
    (fun a ha => hyc a ha)
  set E := A ⊔ Subgroup.zpowers y with hE
  have hE3 : 3 ≤ Open.pRank 3 E := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEe hEc
  have hEM : E ≤ M := sup_le hA.1 ((Subgroup.zpowers_le).mpr (hYM hyV.1))
  have hEC : E ≤ Subgroup.normalizer (C : Set G) := sup_le hAC ((Subgroup.zpowers_le).mpr hyV.2)
  have hfac : AGLCompetitorFactorAt 3 M H (d1KBar 3 M H) E := fun N hN hNM hEN hcov =>
    factor_of_cover hS h9 h98 h984 h101 h115 h3σ hKR hKA hKC he hA6 hcex hN hNM hA hAH
      (le_sup_left.trans hEN) (le_inf hEN hEM) hE3 hcov
  have habs := absorbsAt_of_factorAt he.maxTwoLocal_M.1 he.maxTwoLocal_H hOH hHM hatH.core_le
    hatH.nineThree.factor hfac
  have hcov := cover_normalizer hp (by norm_num) hAH hA.2.1 hT
  have hcovC : AGLCovers 3 H (Subgroup.normalizer (C : Set G)) (d1KBar 3 M H) :=
    hcov.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNTC hx.2⟩)
  have hNM : ¬ Subgroup.normalizer (C : Set G) ≤ M := fun hNM =>
    hKX (hcovC.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNM hx.2⟩))
  exact habs _ ⟨C, hC1, hT.2.1.to_le hCT, rfl⟩ hNM hEC hcovC

theorem inf_pCoreOf_le {L X : Subgroup G} (hLX : L ≤ X) : L ⊓ pCoreOf 2 X ≤ pCoreOf 2 L := by
  intro x hx
  obtain ⟨hxL, hxT⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, hy, hyx⟩ := CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.mp hxT
  let ι : ↥L →* ↥X := Subgroup.inclusion hLX
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective _
  let N : Subgroup ↥L := (CFSG.pCore 2 ↥X).comap ι
  have hNn : N.Normal := (CFSG.pCore_normal (p := 2) (G := ↥X)).comap ι
  have hNp : IsPGroup 2 ↥N :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).comap_of_injective ι hιinj
  have hN : N ≤ CFSG.pCore 2 ↥L := le_sSup ⟨hNn, hNp⟩
  have hz : (⟨x, hxL⟩ : ↥L) ∈ N := by
    show ι ⟨x, hxL⟩ ∈ CFSG.pCore 2 ↥X
    have : ι ⟨x, hxL⟩ = y := Subtype.ext hyx.symm
    rw [this]
    exact hy
  exact CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.mpr ⟨⟨x, hxL⟩, hN hz, rfl⟩

theorem isTwoPrimeComponent_of_self {I D : Subgroup G} (hI : IsTwoPrimeComponent I I)
    (hID : I ≤ D) (hsub : IsSubnormal I D) : IsTwoPrimeComponent D I := by
  have hOI : pCoreOf 2 I ≤ I := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 I
  have hh : I ⊓ pCoreOf 2 I = I ⊓ pCoreOf 2 D := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans
        (CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2 hsub))
    · exact le_inf inf_le_left (inf_pCoreOf_le hID)
  have hqs : CFSG.Open.IsQuasisimple ↥(barM D I) :=
    CFSG.HardMathSupport.Cooperstein.Proving.isQuasisimple_of_mulEquiv'
      (CFSG.HardMathSupport.Cooperstein.Proving.barMEquiv le_rfl hID hh) hI.component.2.2
  have hbarTop : IsSubnormal (barM D I) ⊤ := by
    have h1 := IsSubnormal.of_mathlib (CFSG.Open.IsSubnormal.subgroupOf hsub)
    have h2 := h1.map (QuotientGroup.mk' (CFSG.pCore 2 ↥D))
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  exact
    { le := hID
      subnormal := hsub
      perfect := hI.perfect
      component := ⟨le_top, hbarTop, hqs⟩ }

theorem eq_of_isPGroup_of_le_of_not_two_dvd {T Z D : Subgroup G} (hTZ : T ≤ Z) (hZD : Z ≤ D)
    (hZ2 : IsPGroup 2 Z) (hT : ¬ 2 ∣ (T.subgroupOf D).index) : Z = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : T.relIndex Z ∣ T.relIndex D :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex T Z D hTZ hZD)
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hri : T.relIndex Z ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card T Z
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hri
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ T.relIndex Z := hk ▸ dvd_pow_self 2 hk0
    exact hT (h2.trans hdvd)
  rw [hk0, pow_zero, Subgroup.relIndex_eq_one] at hk
  exact le_antisymm hk hTZ

theorem prime_dvd_card_jZero {H L : Subgroup G}
    (h : ∀ q : ℕ, q.Prime → q ∣ Nat.card (jOne H L) → q = 2 ∨ q = 3) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card (jZero H L) → q = 2 ∨ q = 3 := by
  intro q hq hqd
  by_cases hq2 : q = 2
  · exact Or.inl hq2
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := jZero H L) q hqd
  obtain ⟨k, hk⟩ := exists_two_pow_mem_jOne H L x.2
  have hxk : orderOf ((x : G) ^ (2 ^ k)) = q := by
    rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), Subgroup.orderOf_coe, hx,
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)).gcd_eq_one,
      Nat.div_one]
  exact h q hq (hxk ▸ Subgroup.orderOf_dvd_natCard _ hk)

theorem normalizer_le_of_maxInvariant (hS : Setting G) (h9 : AGL81NineCompetitorQ G)
    (h98 : AGL81NineEightTwo G) (h984 : AGL81NineEightFour G)
    (h101 : AGL81TenOneExists G) (h115 : AGL81ElevenFiveAt G) (h3σ : 3 ∈ rankThreeSigmaA G)
    (hKR : KFactNineThreeRankOne)
    (hKA : KFactNineThreeInvolvedA6L34)
    (hKC : KFactNineThreeComponentL34) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h526 : AGL81FiveTwentySix G) (h1031 : AGL81TenThreeOneAt G) (h1032 : AGL81TenThreeTwoAt G)
    {P : Sylow 3 G} {M H R : Subgroup G} (he : D1Escape 3 P M H R)
    (hA6 : IsAltTwoP 3 (d1KBar 3 M H)) (hcex : ¬ ElevenTwentyConcl M)
    (hd : AGL81CfgData 3 P M H R (d1KBar 3 M H)) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    (hJX : jZero H L ≤ d1PlusCore 3 H (d1KBar 3 M H)) (hJ3 : 3 ∣ Nat.card (jZero H L))
    (hAJ : ∀ a ∈ d1LiftX 3 H R (d1KBar 3 M H), ∀ x ∈ jZero H L,
      a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))
    (hA : IsAGLQ 3 M (d1LiftX 3 H R (d1KBar 3 M H))) {T : Subgroup G}
    (hT : IsMaxInvariantTwoIn (d1LiftX 3 H R (d1KBar 3 M H)) T (d1PlusCore 3 H (d1KBar 3 M H)))
    (hOT : pCoreOf 2 H ≤ T) :
    Subgroup.normalizer (T : Set G) ≤ H := by
  have hg := aglGlobal_of_setting hS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hatH, -, -, -, -, -⟩ := escape_local hS h9 h98 h984 hKC he hA6
  haveI := hatH.nineThree.normal
  set K := d1KBar 3 M H with hKdef
  set X := d1PlusCore 3 H K with hXdef
  set A := d1LiftX 3 H R K with hAdef
  set J₀ := jZero H L with hJdef
  obtain ⟨hAX, hAe, hAc⟩ := d1LiftX_facts he hA6
  have hXH : X ≤ H := Subgroup.map_subtype_le _
  have hXM : X ≤ M := hatH.nineThree.plusCore_le
  have hAH : A ≤ H := (d1LiftX_le 3 H R K).trans he.le_H
  have hAM : A ≤ M := (d1LiftX_le 3 H R K).trans he.le_M
  have hT2 : IsPGroup 2 T := hT.2.1
  have hTH : T ≤ H := hT.1.trans hXH
  have hTM : T ≤ M := hT.1.trans hXM
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hNHL : ∀ B : Subgroup G, B ≤ H → B ≤ M →
      B ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := fun B hBH hBM b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hBH hb)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hMn (hBM hb)) y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hTJ : T ≤ Subgroup.normalizer (J₀ : Set G) :=
    (hNHL T hTH hTM).trans (le_normalizer_jZero H L)
  have hAJn : A ≤ Subgroup.normalizer (J₀ : Set G) :=
    (hNHL A hAH hAM).trans (le_normalizer_jZero H L)
  have hXJ : X ≤ Subgroup.normalizer (J₀ : Set G) :=
    (hNHL X hXH hXM).trans (le_normalizer_jZero H L)
  have hAJ0 : A ⊓ J₀ = ⊥ := le_bot_iff.mp (hAX ▸ inf_le_inf_left A hJX)
  have hJM : J₀ ≤ M := hJX.trans hXM
  have hJH : J₀ ≤ H := hJX.trans hXH
  set D := T ⊔ J₀ with hDdef
  have hDH : D ≤ H := sup_le hTH hJH
  have hTD : ¬ 2 ∣ (T.subgroupOf D).index :=
    not_two_dvd_index_sup_of_centralizes hT2 hTJ hT.2.2.1 hAJn hAJ fun S hSD hS2 hAS hTS =>
      hT.2.2.2 S (hSD.trans (sup_le hT.1 hJX)) hS2 hAS hTS
  have hDtop : D ≠ ⊤ := fun htop => by
    have hHt : H = ⊤ := top_le_iff.mp (htop ▸ hDH)
    exact he.not_le (le_of_eq
      (he.maxTwoLocal_M.2 H he.maxTwoLocal_H.1 (hHt ▸ le_top)))
  have hK' : Open.IsKGroup ↥D :=
    isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper hg.kProper D hDtop)
  have hOD : pCoreOf 2 H ≤ pCoreOf 2 D :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ (hOT.trans le_sup_left)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hOT.trans le_sup_left)).mpr
        (hDH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  have hcharH : CharTwo H := hg.charTwo H he.maxTwoLocal_H.1
  have hchar : CharTwo D := fun x hx =>
    hOD (hcharH ⟨hDH hx.1, Subgroup.centralizer_le hOD hx.2⟩)
  have hJnD : (J₀.subgroupOf D).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTJ
  have hXn : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr
      (le_normalizer_d1PlusCore hatH.nineThree.normal)
  have hJnX : (J₀.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).mpr hXJ
  have hnoblock : ∀ Y : Subgroup G, Y ≤ D → IsSubnormal Y D → InClassXBlock Y → False := by
    intro Y hYD hYsub hYX
    have hYJ : Y ≤ J₀ := le_of_le_sup_of_isShort2 hT2 hTJ (sup_comm T J₀ ▸ hYD) hYX.1.1
    have hYsubJ : IsSubnormal Y J₀ := by
      have h := isSubnormal_inf_of_normal hYsub le_sup_right hJnD
      rwa [inf_eq_left.mpr hYJ] at h
    exact hD2 H Y he.maxTwoLocal_H (hYJ.trans hJH)
      (isSubnormal_of_isSubnormal_of_normal
        (isSubnormal_of_isSubnormal_of_normal hYsubJ hJX hJnX) hXH hXn) hYX
  have key : ∃ C : Subgroup G, C ≤ T ∧ C ≠ ⊥ ∧ (C.subgroupOf T).Characteristic ∧
      3 ∣ Nat.card (J₀ ⊓ Subgroup.normalizer (C : Set G) : Subgroup G) := by
    by_contra hno
    push Not at hno
    by_cases hperf : ∃ I₀ ∈ cZero (H ⊓ L), IsTwoPrimeComponent I₀ I₀
    · obtain ⟨I₀, hI₀, hIp⟩ := hperf
      have hIJ : I₀ ≤ J₀ := IsCZeroMember.le_jZero hI₀
      have hJn' : (J₀.subgroupOf (H ⊓ L)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (jZero_le H L)).mpr
          (Subgroup.le_normalizer.trans (le_normalizer_jZero H L))
      have hIsubJ : IsSubnormal I₀ J₀ := by
        have h := isSubnormal_inf_of_normal hI₀.subnormal (jZero_le H L) hJn'
        rwa [inf_eq_left.mpr hIJ] at h
      have hID : IsTwoPrimeComponent D I₀ := isTwoPrimeComponent_of_self hIp
        (hIJ.trans le_sup_right) (isSubnormal_of_isSubnormal_of_normal hIsubJ le_sup_right hJnD)
      have h3I : 3 ∣ Nat.card I₀ := (h1031 hS 3 P M H R K hd L hL I₀ hI₀).trans
        (Subgroup.card_dvd_of_le (oUpperTwo_le_self I₀))
      have h5 := h526 hS D T I₀ ⟨le_sup_left, hT2, hTD⟩ hchar hnoblock hID h3I
      have hbot : I₀ ≤ ⊥ := h5.trans (iSup_le fun C => iSup_le fun hCT => iSup_le fun hC1 =>
        iSup_le fun hCc => iSup_le fun h3 => absurd ((h3.trans (Subgroup.card_dvd_of_le
          (inf_le_inf_right _ hIJ)))) (hno C hCT hC1 hCc))
      rw [le_bot_iff.mp hbot, Subgroup.card_bot] at h3I
      norm_num at h3I
    · push Not at hperf
      have h23 := prime_dvd_card_jZero (h1032 hS 3 P M H R K hd L hL hperf)
      have hcgs : cgsIn D T = D := by
        by_contra hne
        obtain ⟨Y, hYD, hYsub, hYX, -⟩ := hCGT G D T hK' hchar ⟨le_sup_left, hT2, hTD⟩ hne
        exact hnoblock Y hYD hYsub hYX
      have hDC : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
          D ⊓ Subgroup.normalizer (C : Set G) ≤ T := by
        intro C hCT hC1 hCc
        have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
          Subgroup.le_normalizer.trans
            (normalizer_le_of_characteristic_subgroupOf
              hCT hCc)
        set W := J₀ ⊓ Subgroup.normalizer (C : Set G) with hW
        have hW2 : IsPGroup 2 W := by
          refine IsPGroup.of_card (n := (Nat.card W).primeFactorsList.length) ?_
          refine Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := W)).ne'
            fun {q} hq hqd => ?_
          rcases h23 q hq (hqd.trans (Subgroup.card_dvd_of_le inf_le_left)) with h | h
          · exact h
          · exact absurd (h ▸ hqd) (hno C hCT hC1 hCc)
        have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
          (le_inf hTJ (hTC.trans Subgroup.le_normalizer)).trans
            Subgroup.inf_normalizer_le_normalizer_inf
        have hZ2 : IsPGroup 2 (T ⊔ W : Subgroup G) := hT2.to_sup_of_normal_right' hW2 hTW
        have hZ := eq_of_isPGroup_of_le_of_not_two_dvd (le_sup_left : T ≤ T ⊔ W)
          (sup_le le_sup_left (inf_le_left.trans le_sup_right)) hZ2 hTD
        intro x hx
        have hxD : x ∈ (T : Set G) * (J₀ : Set G) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right T J₀ hTJ]
          exact hx.1
        obtain ⟨t, ht, j, hj, rfl⟩ := Set.mem_mul.mp hxD
        have hjC : j ∈ Subgroup.normalizer (C : Set G) := by
          have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTC ht)) hx.2
          simpa using this
        rw [← hZ]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right ⟨hj, hjC⟩)
      have hDT : D ≤ T := by
        rw [← hcgs]
        exact iSup_le fun C => iSup_le fun hCT => iSup_le fun hC1 => iSup_le fun hCc =>
          hDC C hCT hC1 hCc
      have hJ2 : IsPGroup 2 J₀ := hT2.to_le (le_sup_right.trans hDT)
      obtain ⟨n, hn⟩ := hJ2.exists_card_eq
      rw [hn] at hJ3
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hJ3)) (by norm_num)
  obtain ⟨C, hCT, hC1, hCc, h3⟩ := key
  exact (normalizer_le_of_characteristic_subgroupOf
    hCT hCc).trans (normalizer_le_of_three_dvd hS h9 h98 h984 h101 h115 h3σ hKR hKA hKC he
      hA6 hcex hA hAH hAe hAc hT hJM hAJ0 hAJn hCT hC1 hCc h3)

theorem isMaxInvariantTwo_of_normalizer_le {A T H X : Subgroup G}
    (hT : IsMaxInvariantTwoIn A T X) (hNT : Subgroup.normalizer (T : Set G) ≤ H)
    (hb3 : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → A ≤ Subgroup.normalizer (S : Set G) → S ≤ X) :
    ∀ S : Subgroup G, IsPGroup 2 S → A ≤ Subgroup.normalizer (S : Set G) → T ≤ S → S = T := by
  intro S hS2 hAS hTS
  set U := S ⊓ Subgroup.normalizer (T : Set G) with hU
  have hU2 : IsPGroup 2 U := hS2.to_le inf_le_left
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    (le_inf hAS (hT.2.2.1.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hUT : U = T := hT.2.2.2 U (hb3 U hU2 (inf_le_right.trans hNT) hAU) hU2 hAU
    (le_inf hTS Subgroup.le_normalizer)
  by_contra hST
  have hlt : T.subgroupOf S ≠ ⊤ := fun htop =>
    hST (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hTS)
  haveI : Group.IsNilpotent S := hS2.isNilpotent
  obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (T.subgroupOf S) (lt_top_iff_ne_top.mpr hlt))
  have hmapT : (T.subgroupOf S).map S.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTS]
  have hxN' : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
    have := Subgroup.le_normalizer_map S.subtype ⟨x, hxN, rfl⟩
    rwa [hmapT] at this
  have hxU : (x : G) ∈ U := ⟨x.2, hxN'⟩
  rw [hUT] at hxU
  exact hxT hxU

theorem le_of_maxInvariant (hS : Setting G) (h9 : AGL81NineCompetitorQ G)
    (h98 : AGL81NineEightTwo G) (h984 : AGL81NineEightFour G)
    (h101 : AGL81TenOneExists G) (h115 : AGL81ElevenFiveAt G) (h3σ : 3 ∈ rankThreeSigmaA G)
    (hKR : KFactNineThreeRankOne)
    (hKA : KFactNineThreeInvolvedA6L34)
    (hKC : KFactNineThreeComponentL34) (hD2 : NoXBlockFor G) (h526 : AGL81FiveTwentySix G)
    {P : Sylow 3 G} {M H R : Subgroup G} (he : D1Escape 3 P M H R)
    (hA6 : IsAltTwoP 3 (d1KBar 3 M H)) (hcex : ¬ ElevenTwentyConcl M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    (h3L : 3 ∣ Nat.card L) (hA : IsAGLQ 3 M (d1LiftX 3 H R (d1KBar 3 M H)))
    (hAL : ⁅d1LiftX 3 H R (d1KBar 3 M H), L⁆ ≤ pCoreOf 2 L)
    (hAL0 : d1LiftX 3 H R (d1KBar 3 M H) ⊓ L = ⊥) {T : Subgroup G}
    (hT : IsMaxInvariantTwoIn (d1LiftX 3 H R (d1KBar 3 M H)) T (d1PlusCore 3 H (d1KBar 3 M H)))
    (hOT : pCoreOf 2 H ≤ T) (hNT : Subgroup.normalizer (T : Set G) ≤ H)
    (hb3A : Hyp111B3 3 H (d1LiftX 3 H R (d1KBar 3 M H)) (d1KBar 3 M H)) : L ≤ H := by
  have hg := aglGlobal_of_setting hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hatH, -, -, hOH, -, -⟩ := escape_local hS h9 h98 h984 hKC he hA6
  haveI := hatH.nineThree.normal
  set K := d1KBar 3 M H with hKdef
  set X := d1PlusCore 3 H K with hXdef
  set A := d1LiftX 3 H R K with hAdef
  obtain ⟨-, hAe, hAc⟩ := d1LiftX_facts he hA6
  have hAH : A ≤ H := (d1LiftX_le 3 H R K).trans he.le_H
  have hM := he.maxTwoLocal_M
  have hT2 : IsPGroup 2 T := hT.2.1
  have hTM : T ≤ M := hT.1.trans hatH.nineThree.plusCore_le
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hTM.trans hMn
  have hAL' : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 L := fun a ha l hl =>
    hAL (Subgroup.commutator_mem_commutator ha hl)
  have hTG := isMaxInvariantTwo_of_normalizer_le hT hNT hb3A
  have hTsyl : ¬ 2 ∣ (T.subgroupOf (T ⊔ L)).index :=
    not_two_dvd_index_sup_of_centralizes hT2 hTL hT.2.2.1 (hA.1.trans hMn) hAL'
      fun S _ hS2 hAS hTS => hTG S hS2 hAS hTS
  set D := L ⊔ T with hDdef
  have hTD : ¬ 2 ∣ (T.subgroupOf D).index := by rwa [hDdef, sup_comm]
  have hDM : D ≤ M := sup_le hL.le hTM
  have hQT : pCoreOf 2 M ≤ T := hOH.trans hOT
  have hQD : pCoreOf 2 M ≤ D := hQT.trans le_sup_right
  have hQcore : pCoreOf 2 M ≤ pCoreOf 2 D :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hQD
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr
        (hDM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  have hcharM : CharTwo M := hg.charTwo M hM.1
  have hchar : CharTwo D := fun x hx =>
    hQcore (hcharM ⟨hDM hx.1, Subgroup.centralizer_le hQcore hx.2⟩)
  have hLnD : (L.subgroupOf D).Normal := normal_subgroupOf_sup_of_le_normalizer_left hTL
  have hnoblock : ∀ Y : Subgroup G, Y ≤ D → IsSubnormal Y D → InClassXBlock Y → False := by
    intro Y hYD hYsub hYX
    have hYL : Y ≤ L := le_of_le_sup_of_isShort2 hT2 hTL hYD hYX.1.1
    have hYsubL : IsSubnormal Y L := by
      have h := isSubnormal_inf_of_normal hYsub le_sup_left hLnD
      rwa [inf_eq_left.mpr hYL] at h
    exact hD2 M Y hM (hYL.trans hL.le)
      (isSubnormal_of_isSubnormal_of_normal hYsubL hL.le hLn) hYX
  have hLc : IsTwoPrimeComponent D L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent
      hTM hT2 hTL
  have h5 := h526 hS D T L ⟨le_sup_right, hT2, hTD⟩ hchar hnoblock hLc h3L
  refine h5.trans (iSup_le fun C => iSup_le fun hCT => iSup_le fun hC1 => iSup_le fun hCc =>
    iSup_le fun h3 => inf_le_right.trans ?_)
  exact normalizer_le_of_three_dvd hS h9 h98 h984 h101 h115 h3σ hKR hKA hKC he hA6 hcex hA
    hAH hAe hAc hT hL.le hAL0 (hA.1.trans hMn) hCT hC1 hCc h3

theorem elevenTwentyConcl_of_isAltTwoP (hS : Setting G) (h9 : AGL81NineCompetitorQ G)
    (h98 : AGL81NineEightTwo G) (h984 : AGL81NineEightFour G)
    (h101 : AGL81TenOneExists G) (h115 : AGL81ElevenFiveAt G) (h3σ : 3 ∈ rankThreeSigmaA G)
    (hKR : KFactNineThreeRankOne)
    (hKA : KFactNineThreeInvolvedA6L34)
    (hKC : KFactNineThreeComponentL34) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h526 : AGL81FiveTwentySix G) (h1031 : AGL81TenThreeOneAt G) (h1032 : AGL81TenThreeTwoAt G)
    (h10Z : AGL81TenOneCenterRank G) (h10C : AGL81TenOneCZero G) (h91 : AGL81TenNineOneCfg G)
    (h6 : AGL81ElevenSixCfg G) (h7 : AGL81ElevenSevenCfgThree G) (h11 : AGL81ElevenElevenCfg G)
    (h4 : AGL81ElevenTwelveOne G) {P : Sylow 3 G} {M H R : Subgroup G}
    (he : D1Escape 3 P M H R) (hA6 : IsAltTwoP 3 (d1KBar 3 M H)) : ElevenTwentyConcl M := by
  by_contra hcex
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := cfgData_of_escape hS h9 h98 h984 h101 h115 h3σ hKR hKA hKC he hA6 hcex
  obtain ⟨hatH, hb3R, hsylR, hOH, hHM, hKX⟩ := escape_local hS h9 h98 h984 hKC he hA6
  haveI := hatH.nineThree.normal
  set K := d1KBar 3 M H with hKdef
  set X := d1PlusCore 3 H K with hXdef
  set A := d1LiftX 3 H R K with hAdef
  obtain ⟨hAX, hAe, hAc⟩ := d1LiftX_facts he hA6
  have hAR : A ≤ R := d1LiftX_le 3 H R K
  have hAH : A ≤ H := hAR.trans he.le_H
  obtain ⟨L, hL⟩ := h101 hS 3 P M H R he H R hd.base hd.le_H hd.maxH hd.not_le hsylR hb3R
  have hK := exists_component_of_d1KBar_ne_bot (d1KBar_ne_bot_of_isAltTwoP hA6)
  have hnc : ¬ HasPrimeConstraint (G := H) 3 := by
    obtain ⟨L', hL', -⟩ := hK
    exact not_hasPrimeConstraint_of_component hL'
  have hH3 : 3 ≤ Open.pRank 3 H :=
    he.three_le_pRank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three
      he.le_H)
  obtain ⟨hLn, hAQ, hAL⟩ := agl81ElevenCfgChain_of h6 h11 h4 hS h3σ hd hA6 hnc hH3 hL
  have hno : ¬ AGL81ElevenFiveOne 3 H K L := by
    rintro ⟨-, -, hI⟩
    have := h4 hS P M H R K h3σ hd hA6 hnc L hL hI
    omega
  obtain ⟨-, -, hJ0, hAJ⟩ := h7 hS P M H R K h3σ hd hnc L hL hLn hno
  have hJX : jZero H L ≤ X := by
    refine hJ0.resolve_right fun h => ?_
    have h1 := card_of_isLinThreeFour h
    rw [card_of_isAltTwoP_three hA6] at h1
    norm_num at h1
  have hAJ' := hAJ hJX
  obtain ⟨I₀, hI₀⟩ := h10C hS 3 P M H R K hd L hL (h91 hS 3 P M H R K hd L hL)
  have hJ3 : 3 ∣ Nat.card (jZero H L) := (h1031 hS 3 P M H R K hd L hL I₀ hI₀).trans
    (Subgroup.card_dvd_of_le ((IsCZeroMember.oUpperTwo_le_jOne hI₀).trans (jOne_le_jZero H L)))
  have h3L : 3 ∣ Nat.card L :=
    hJ3.trans (Subgroup.card_dvd_of_le ((jZero_le H L).trans inf_le_right))
  have hsylA : ∃ S : Sylow 3 K, (S : Subgroup K).map K.subtype =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓ K := by
    obtain ⟨S, hS'⟩ := hsylR
    refine ⟨S, ?_⟩
    rw [hAdef, map_d1LiftX, inf_assoc, inf_idem, hS']
  have hb3A : Hyp111B3 3 H A K := by
    rcases h98 hS 3 P M H R he H A hAQ hAH he.maxTwoLocal_H he.not_le hsylA with
      hb3 | ⟨-, L', hL', hLX, hLt⟩
    · exact hb3
    · exfalso
      have h1 := hKC _ _ _ (hatH.list (d1KBar_ne_bot_of_isAltTwoP hA6)) hL' (le_d1KBar hL' hLX) hLt
      have h2 := card_of_isLinThreeFour h1
      rw [card_of_isAltTwoP_three hA6] at h2
      norm_num at h2
  have hAL0 : A ⊓ L = ⊥ := by
    by_contra hne
    have hVe : IsElemAbelian 3 (A ⊓ L : Subgroup G) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hAe.2 x hx.1⟩
      have := congrArg Subtype.val (isMulCommutative_iff.mp hAe.1 ⟨a, a.2.1⟩ ⟨b, b.2.1⟩)
      simpa using this
    have hV3 := h10Z hS 3 P M H R K hd L hL hLn (A ⊓ L) inf_le_right hVe fun v hv l hl =>
      hAL (Subgroup.commutator_mem_commutator hv.1 hl)
    have hAM : Subgroup.normalizer (A : Set G) ≤ M := normalizer_le_of_isAGLQ_of_escape he hAQ
    have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
    have hA3 : IsPGroup 3 A := he.isPGroup.to_le hAR
    have hirr : A ⊓ L = A := by
      obtain ⟨S, hS'⟩ := hsylR
      refine eq_of_le_of_normalizer_le hA6 hAH hA3 ⟨S, ?_⟩ inf_le_left hne ?_
      · rw [hS', hAdef, map_d1LiftX]
      · exact (le_inf inf_le_right (inf_le_right.trans (hAM.trans hMn))).trans
          Subgroup.inf_normalizer_le_normalizer_inf
    rw [hirr, hAc] at hV3
    norm_num at hV3
  have hO2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hOX : pCoreOf 2 H ≤ X :=
    hb3R _ hO2 (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) (he.le_H.trans hHO)
  obtain ⟨T, hOT, hTmax⟩ := Finite.exists_le_maximal
    (p := fun S : Subgroup G => S ≤ X ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G))
    ⟨hOX, hO2, hAH.trans hHO⟩
  have hT : IsMaxInvariantTwoIn A T X := ⟨hTmax.1.1, hTmax.1.2.1, hTmax.1.2.2,
    fun S hSX hS2 hAS hTS => le_antisymm (hTmax.2 ⟨hSX, hS2, hAS⟩ hTS) hTS⟩
  have hNT := normalizer_le_of_maxInvariant hS h9 h98 h984 h101 h115 h3σ hKR hKA hKC hCGT
    hD2 h526 h1031 h1032 he hA6 hcex hd hL hLn hJX hJ3 hAJ' hAQ hT hOT
  have hLH := le_of_maxInvariant hS h9 h98 h984 h101 h115 h3σ hKR hKA hKC hD2 h526 he hA6
    hcex hL hLn h3L hAQ hAL hAL0 hT hOT hNT hb3A
  exact hL.not_le_normalizer (hLH.trans hHO)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
