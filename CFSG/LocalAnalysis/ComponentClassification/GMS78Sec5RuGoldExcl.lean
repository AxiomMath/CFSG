module

public import CFSG.LocalAnalysis.ComponentClassification.AS81QbarComp
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.Goldschmidt.Steps.G37Basic
import CFSG.Walter.W67.W2Cor32A

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  benderBorel_sylowCenter normalizer_transitive_center)

namespace GoldExcl

@[expose] def GoldschmidtComponents : Prop :=
  ∀ (H : Type) [Group H] [Finite H], goldschmidtOddCore H = ⊥ → ∀ (S : Sylow 2 H)
    (A : Subgroup H), A ≤ (S : Subgroup H) → IsMulCommutative A →
    fusionStronglyClosed (A : Set H) (S : Subgroup H) →
    (∀ K : Subgroup H, CFSG.IsComponent K → K ≤ normalClosure (A : Set H) →
        goldschmidtSimpleType (K ⧸ center K) ∧ InducesOmega1 A K S ∧
        ∀ a ∈ A, ∃ x ∈ A ⊓ K, ∀ y ∈ K, a⁻¹ * y * a = x⁻¹ * y * x) ∧
      ((∀ K : Subgroup H, CFSG.IsComponent K → ¬ K ≤ normalClosure (A : Set H)) → A.Normal)

theorem not_isPGroup_of_isComponent {H : Type*} [Group H] [Finite H] {K : Subgroup H}
    (hK : CFSG.IsComponent K) : ¬ IsPGroup 2 K := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperf, hsimp, -⟩ := hK.1
  have : Group.IsPerfect K := hperf
  have : Nontrivial (K ⧸ center K) := hsimp.toNontrivial
  have : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact Group.IsPerfect.not_isNilpotent K hp.isNilpotent

open scoped IsMulCommutative in
theorem eq_one_of_mem_center {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (P : Sylow 2 K) [IsMulCommutative (P : Subgroup K)] {z : K} (hz : z ∈ center K)
    (hz2 : z ^ 2 = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ : K →* (P : Subgroup K) := MonoidHom.transfer (MonoidHom.id (P : Subgroup K)) with hτ
  have h1 : τ z = 1 := Abelianization.commutator_subset_ker τ Group.IsPerfect.mem_commutator
  have hkey : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup K) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    rw [mul_assoc, ← (mem_center_iff.mp (pow_mem hz k) g₀)]
    group
  have h2 := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup K)) z hkey
  rw [← hτ, h1, MonoidHom.id_apply] at h2
  have h3 : z ^ (P : Subgroup K).index = 1 := congrArg Subtype.val h2.symm
  have hodd : Odd (P : Subgroup K).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp P.not_dvd_index)
  obtain ⟨m, hm⟩ := hodd
  rw [hm, pow_succ, pow_mul, hz2, one_pow, one_mul] at h3
  exact h3

theorem inf_center_ne_bot {G : Type*} [Group G] [Finite G] {X N : Subgroup G}
    (hX : IsPGroup 2 X) (hNX : N ≤ X) (hNn : X ≤ normalizer (N : Set G)) (hN : N ≠ ⊥) :
    N ⊓ (X ⊓ centralizer (X : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent X := hX.isNilpotent
  have hnormal : (N.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNn
  have hne : N.subgroupOf X ≠ ⊥ := by
    intro h
    apply hN
    rw [← Subgroup.map_subgroupOf_eq_of_le hNX, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (X : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ N ⊓ (X ⊓ centralizer (X : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

variable {H : Type} [Group H] [Finite H]

theorem false_of_unitary
    {A K : Subgroup H} (hA2 : ∀ a ∈ A, a ^ 2 = 1) {f : H} (hfA : f ∈ A)
    (hcard : Nat.card A = 8 ∨ Nat.card A = 32)
    (hC : ∀ a ∈ A, a ∉ zpowers f → IsPGroup 2 (centralizer ({a} : Set H)))
    (hAK : A ≤ K) (Tb : Sylow 2 (K ⧸ center K))
    (hT3 : Omega1 (Tb : Subgroup (K ⧸ center K)) =
      (A.subgroupOf K).map (QuotientGroup.mk' (center K)))
    (hT4 : Nat.card (Omega1 (Tb : Subgroup (K ⧸ center K))) * 2 = Nat.card A)
    {q' : ℕ} (e : K ⧸ center K ≃* PSU3 2 q') (hq' : 2 ≤ q') : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center K) with hπ
  have : Finite (PSU3 2 q') := Finite.of_equiv _ e.toEquiv
  have hB := (bender_psu3_borel_full q' hq').map_mulEquiv e.symm
  obtain ⟨hSE, hZ2, hZc, hTc⟩ := benderBorel_sylowCenter hB Tb
  have h11c := (N11c (K ⧸ center K) (Or.inr ⟨q', hq', ⟨e⟩⟩) Tb).1
  set Zs := sylowCenter (Tb : Subgroup (K ⧸ center K)) with hZs
  have hq24 : q' = 2 ∨ q' = 4 := by
    rw [h11c, hZc] at hT4
    have h2 : 2 ^ (q' + 1) = Nat.card A := by rw [← hT4]; ring
    rcases hcard with h | h
    · rw [h, show (8 : ℕ) = 2 ^ 3 by norm_num] at h2
      have := Nat.pow_right_injective (le_refl 2) h2
      omega
    · rw [h, show (32 : ℕ) = 2 ^ 5 by norm_num] at h2
      have := Nat.pow_right_injective (le_refl 2) h2
      omega
  have hcardK : Nat.card (K ⧸ center K) =
      (2 ^ q') ^ 3 * (((2 ^ q') ^ 2 - 1) * ((2 ^ q') ^ 3 + 1)) := by
    have h1 := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd
      (p := q') (by omega)
    have hgcd : Nat.gcd 3 (2 ^ q' + 1) = 1 := by rcases hq24 with rfl | rfl <;> norm_num
    rw [hgcd, mul_one, ← Nat.card_congr e.toEquiv] at h1
    exact h1
  have hX : fusionIsBenderGroup (K ⧸ center K) := Or.inr (Or.inl ⟨q', hq', ⟨e⟩⟩)
  have hsyl := GoldType.card_sylow_of_bender hX Tb
  rw [hTc] at hsyl
  set N := normalizer ((Tb : Subgroup (K ⧸ center K)) : Set (K ⧸ center K)) with hN
  have hNcard : Nat.card N * ((2 ^ q') ^ 3 + 1) = Nat.card (K ⧸ center K) := by
    rw [← hsyl, Sylow.card_eq_index_normalizer Tb]
    exact N.card_mul_index
  obtain ⟨-, ⟨D, hDcyc, hDodd, hTD, hTDN⟩, -, -, -⟩ := hB Tb
  have hDN : D ≤ N := by
    rw [hN, ← hTDN]
    exact le_sup_right
  have hTDcard := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hDN
  rw [hTDN, hTD, card_bot, mul_one, hTc] at hTDcard
  have hDcard : Nat.card D = (2 ^ q') ^ 2 - 1 := by
    have h1 := hNcard
    rw [hcardK, hTDcard] at h1
    have hq3 : 0 < (2 ^ q') ^ 3 * ((2 ^ q') ^ 3 + 1) := by positivity
    refine Nat.eq_of_mul_eq_mul_left hq3 ?_
    rw [← mul_assoc] at h1
    linarith [h1]
  have hconj : ∀ d ∈ D, ∀ z ∈ Zs, d⁻¹ * z * d ∈ Zs := by
    intro d hd z hz
    have hdN : d ∈ N := hDN hd
    rw [hZs, mem_sylowCenter] at hz ⊢
    obtain ⟨hzT, hzc⟩ := hz
    refine ⟨?_, fun t ht => ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hdN) z).mp hzT
      simpa using this
    · have ht' : d * t * d⁻¹ ∈ (Tb : Subgroup (K ⧸ center K)) :=
        (mem_normalizer_iff.mp hdN t).mp ht
      have h1 := hzc _ ht'
      calc t * (d⁻¹ * z * d) = d⁻¹ * ((d * t * d⁻¹) * z) * d := by group
        _ = d⁻¹ * (z * (d * t * d⁻¹)) * d := by rw [h1]
        _ = d⁻¹ * z * d * t := by group
  have hZne : Zs ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hZc
    have : 2 ≤ 2 ^ q' := Nat.le_self_pow (by omega) 2
    omega
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  let φ : D → Zs := fun d => ⟨(d : K ⧸ center K)⁻¹ * z₀ * d, hconj d d.2 z₀ hz₀⟩
  have hnotinj : ¬ Function.Injective φ := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [hDcard, hZc] at h1
    rcases hq24 with rfl | rfl <;> norm_num at h1
  simp only [Function.Injective, not_forall] at hnotinj
  obtain ⟨d₁, d₂, h12, hne⟩ := hnotinj
  set d : K ⧸ center K := (d₁ : K ⧸ center K) * (d₂ : K ⧸ center K)⁻¹ with hd
  have hdD : d ∈ D := mul_mem d₁.2 (inv_mem d₂.2)
  have hd1 : d ≠ 1 := fun h => hne (Subtype.ext (mul_inv_eq_one.mp h))
  have hdz₀ : d⁻¹ * z₀ * d = z₀ := by
    have h1 : (d₁ : K ⧸ center K)⁻¹ * z₀ * d₁ = (d₂ : K ⧸ center K)⁻¹ * z₀ * d₂ :=
      congrArg Subtype.val h12
    calc d⁻¹ * z₀ * d =
        (d₂ : K ⧸ center K) * ((d₁ : K ⧸ center K)⁻¹ * z₀ * d₁) * (d₂ : K ⧸ center K)⁻¹ := by
          rw [hd]; group
      _ = (d₂ : K ⧸ center K) * ((d₂ : K ⧸ center K)⁻¹ * z₀ * d₂) *
          (d₂ : K ⧸ center K)⁻¹ := by rw [h1]
      _ = z₀ := by group
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    let : CommGroup D := IsCyclic.commGroup
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : D) ⟨y, hy⟩)
  have hdZ : ∀ z ∈ Zs, d⁻¹ * z * d = z := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      group
    obtain ⟨n, hn, hnz⟩ := normalizer_transitive_center hSE hZ2 hz₀ hz hz₀1' hz1
    have hn' : n ∈ D ⊔ (Tb : Subgroup (K ⧸ center K)) := by
      rw [sup_comm, hTDN]
      exact hn
    obtain ⟨w, hw, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hDN hn'
    have hwz : w⁻¹ * z₀ * w ∈ Zs := hconj w hw z₀ hz₀
    have htw : t * (w⁻¹ * z₀ * w) = (w⁻¹ * z₀ * w) * t := (mem_sylowCenter.mp hwz).2 t ht
    have hz' : z = w⁻¹ * z₀ * w := by
      rw [← hnz]
      calc (w * t)⁻¹ * z₀ * (w * t) = t⁻¹ * ((w⁻¹ * z₀ * w) * t) := by group
        _ = t⁻¹ * (t * (w⁻¹ * z₀ * w)) := by rw [htw]
        _ = w⁻¹ * z₀ * w := by group
    have hdw := hDcomm d hdD w hw
    rw [hz']
    calc d⁻¹ * (w⁻¹ * z₀ * w) * d = (w * d)⁻¹ * z₀ * (w * d) := by group
      _ = (d * w)⁻¹ * z₀ * (d * w) := by rw [← hdw]
      _ = w⁻¹ * (d⁻¹ * z₀ * d) * w := by group
      _ = w⁻¹ * z₀ * w := by rw [hdz₀]
  have hdodd : Odd (orderOf d) := hDodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hdD)
  obtain ⟨d₀, hd₀⟩ := QuotientGroup.mk'_surjective (center K) d
  obtain ⟨j, m, hm, hjm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d₀).ne'
  set c₁ := d₀ ^ (2 ^ j) with hc₁
  have hc₁m : c₁ ^ m = 1 := by rw [hc₁, ← pow_mul, ← hjm, pow_orderOf_eq_one]
  have hc₁odd : Odd (orderOf c₁) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hc₁m)
  have hπc₁ : π c₁ = d ^ (2 ^ j) := by rw [hc₁, map_pow, hπ, hd₀]
  have hπc₁1 : π c₁ ≠ 1 := by
    rw [hπc₁]
    intro h
    apply hd1
    have hcop := Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hdodd)
    exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one h))
  have hπc₁Z : ∀ z ∈ Zs, π c₁ * z = z * π c₁ := by
    intro z hz
    have h1 := hdZ z hz
    have hc : Commute d z := by
      show d * z = z * d
      calc d * z = d * (d⁻¹ * z * d) := by rw [h1]
        _ = z * d := by group
    rw [hπc₁]
    exact (hc.pow_left (2 ^ j)).eq
  have hcomm : ∀ a ∈ A, (c₁ : H) * a = a * c₁ := by
    intro a ha
    set a' : K := ⟨a, hAK ha⟩ with ha'
    have ha'Z : π a' ∈ Zs := by
      have h1 : π a' ∈ Omega1 (Tb : Subgroup (K ⧸ center K)) := by
        rw [hT3]
        exact ⟨a', mem_subgroupOf.mpr ha, rfl⟩
      rw [h11c] at h1
      exact h1
    set c : K := a'⁻¹ * (c₁ * a' * c₁⁻¹) with hc
    have hcZ : c ∈ center K := by
      have h1 := hπc₁Z _ ha'Z
      have h2 : π c = 1 := by
        rw [hc, map_mul, map_inv, map_mul, map_mul, map_inv, h1]
        group
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hca : c₁ * a' * c₁⁻¹ = a' * c := by rw [hc]; group
    have ha'2 : a' ^ 2 = 1 := Subtype.ext (hA2 a ha)
    have hc2 : c ^ 2 = 1 := by
      have h1 : (c₁ * a' * c₁⁻¹) ^ 2 = 1 := by
        rw [show (c₁ * a' * c₁⁻¹) ^ 2 = c₁ * a' ^ 2 * c₁⁻¹ by rw [sq, sq]; group, ha'2]
        group
      rw [hca, (show Commute a' c from (mem_center_iff.mp hcZ a')).mul_pow, ha'2, one_mul] at h1
      exact h1
    have hpow : ∀ k : ℕ, c₁ ^ k * a' * (c₁ ^ k)⁻¹ = a' * c ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hck : c₁ * c ^ k * c₁⁻¹ = c ^ k := by
          rw [mem_center_iff.mp (pow_mem hcZ k) c₁]
          group
        calc c₁ ^ (k + 1) * a' * (c₁ ^ (k + 1))⁻¹ =
            c₁ * (c₁ ^ k * a' * (c₁ ^ k)⁻¹) * c₁⁻¹ := by rw [pow_succ']; group
          _ = c₁ * (a' * c ^ k) * c₁⁻¹ := by rw [ih]
          _ = (c₁ * a' * c₁⁻¹) * (c₁ * c ^ k * c₁⁻¹) := by group
          _ = a' * c * c ^ k := by rw [hca, hck]
          _ = a' * c ^ (k + 1) := by rw [pow_succ', mul_assoc]
    have h1 := hpow (orderOf c₁)
    rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at h1
    have hco : c ^ orderOf c₁ = 1 := by
      have := congrArg (a'⁻¹ * ·) h1
      simpa using this.symm
    have hc1 : c = 1 := by
      obtain ⟨r, hr⟩ := hc₁odd
      rw [hr, pow_succ, pow_mul, hc2, one_pow, one_mul] at hco
      exact hco
    have h3 : c₁ * a' = a' * c₁ := by
      have := hca
      rw [hc1, mul_one] at this
      calc c₁ * a' = c₁ * a' * c₁⁻¹ * c₁ := by group
        _ = a' * c₁ := by rw [this]
    exact congrArg Subtype.val h3
  obtain ⟨a, ha, haf⟩ : ∃ a ∈ A, a ∉ zpowers f := by
    by_contra h
    push Not at h
    have h1 := card_le_of_le (show A ≤ zpowers f from h)
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf f ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA2 f hfA))
    rcases hcard with h | h <;> omega
  have hc₁C : (c₁ : H) ∈ centralizer ({a} : Set H) :=
    mem_centralizer_singleton_iff.mpr (hcomm a ha)
  obtain ⟨k, hk⟩ := hC a ha haf ⟨c₁, hc₁C⟩
  have hk' : c₁ ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hcop := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hc₁odd)
  have : orderOf c₁ = 1 := hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hk')
  apply hπc₁1
  rw [orderOf_eq_one_iff.mp this, map_one]

theorem false_of_component
    (S : Sylow 2 H) {A K : Subgroup H} (hAab : IsMulCommutative A) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAS : A ≤ (S : Subgroup H)) {f : H} (hfA : f ∈ A) (hf1 : f ≠ 1)
    (hfc : ∀ h : H, h * f = f * h) (hcard : Nat.card A = 8 ∨ Nat.card A = 32)
    (hC : ∀ a ∈ A, a ∉ zpowers f → IsPGroup 2 (centralizer ({a} : Set H)))
    (hK : CFSG.IsComponent K) (hAK : A ≤ K)
    (htype : goldschmidtSimpleType (K ⧸ center K)) (hind : InducesOmega1 A K S) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : ∀ a ∈ A, (∀ y ∈ K, y * a = a * y) → a ∈ zpowers f := fun a ha hc => by
    by_contra haf
    exact not_isPGroup_of_isComponent hK ((hC a ha haf).to_le fun y hy =>
      mem_centralizer_singleton_iff.mpr (hc y hy))
  have hfK : f ∈ K := hAK hfA
  have hf2 : f ^ 2 = 1 := hA2 f hfA
  have hzf : ∀ z ∈ zpowers f, ∀ h : H, h * z = z * h := by
    rintro _ ⟨k, rfl⟩ h
    exact ((Commute.zpow_right (hfc h) k))
  have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  have : Group.IsPerfect K := hK.1.1
  obtain ⟨P, hP⟩ := AS81.Qbar.isSylowOf_inf_component S hK
  set π := QuotientGroup.mk' (center K) with hπ
  set Tb : Sylow 2 (K ⧸ center K) := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
    with hTb
  have hTbcoe : (Tb : Subgroup (K ⧸ center K)) = (P : Subgroup K).map π :=
    Sylow.coe_mapSurjective _ _
  set A' : Subgroup K := A.subgroupOf K with hA'
  have hPS : ∀ t ∈ (P : Subgroup K), (t : H) ∈ (S : Subgroup H) := fun t ht => by
    have : (t : H) ∈ (P : Subgroup K).map K.subtype := ⟨t, ht, rfl⟩
    rw [hP] at this
    exact this.1
  have hA'P : A' ≤ (P : Subgroup K) := fun a ha => by
    have h1 : (a : H) ∈ (S : Subgroup H) ⊓ K := ⟨hAS (mem_subgroupOf.mp ha), a.2⟩
    rw [← hP] at h1
    obtain ⟨b, hb, hba⟩ := h1
    rwa [← Subtype.ext hba]
  have hT1 : ∀ t ∈ (P : Subgroup K), π t ^ 2 = 1 → π t ∈ A'.map π := by
    intro t ht ht2
    have ht2' : (t : H) ^ 2 ∈ centralizer (K : Set H) := by
      rw [hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
        mem_center_iff] at ht2
      refine mem_centralizer_iff.mpr fun g hg => ?_
      have := congrArg Subtype.val (ht2 ⟨g, hg⟩)
      simpa using this
    obtain ⟨a, ha, hat⟩ := hind.2 t ⟨hPS t ht, t.2⟩ ht2'
    refine ⟨⟨a, hAK ha⟩, mem_subgroupOf.mpr ha, ?_⟩
    exact AS81.Qbar.mk_eq_of_sameOn (t := ⟨a, hAK ha⟩) (t' := t) hat
  have hT3 : Omega1 (Tb : Subgroup (K ⧸ center K)) = A'.map π := by
    refine le_antisymm ((closure_le _).mpr ?_) ?_
    · rintro w ⟨hw, hw2⟩
      rw [hTbcoe] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      exact hT1 t ht hw2
    · rintro _ ⟨a, ha, rfl⟩
      refine GoldType.mem_omega1 ?_ ?_
      · rw [hTbcoe]
        exact ⟨a, hA'P ha, rfl⟩
      · rw [← map_pow, show a ^ 2 = 1 from Subtype.ext (hA2 _ (mem_subgroupOf.mp ha)), map_one]
  have hT4 : Nat.card (Omega1 (Tb : Subgroup (K ⧸ center K))) * 2 = Nat.card A := by
    rw [hT3]
    set φ : A' →* K ⧸ center K := π.comp A'.subtype with hφ
    have hrange : φ.range = A'.map π := by
      rw [hφ, MonoidHom.range_comp, range_subtype]
    have hker : Nat.card φ.ker = 2 := by
      have hzK : zpowers f ≤ K := zpowers_le.mpr hfK
      have hzA : zpowers f ≤ A := zpowers_le.mpr hfA
      have e : φ.ker ≃ zpowers f :=
        { toFun := fun k => ⟨((k : A') : H), by
            refine hcen _ (mem_subgroupOf.mp (k : A').2) fun y hy => ?_
            have h1 : π ((k : A') : K) = 1 := k.2
            rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff] at h1
            have := congrArg Subtype.val (h1 ⟨y, hy⟩)
            simpa using this⟩
          invFun := fun z => ⟨⟨⟨z, hzK z.2⟩, mem_subgroupOf.mpr (hzA z.2)⟩, by
            show π ⟨z, hzK z.2⟩ = 1
            rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff]
            intro g
            exact Subtype.ext (hzf z z.2 g)⟩
          left_inv := fun k => rfl
          right_inv := fun z => rfl }
      rw [Nat.card_congr e, Nat.card_zpowers, orderOf_eq_prime hf2 hf1]
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hrange, hker, Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv] at h1
    linarith
  have hW := AS81.Qbar.isMulCommutative_omega1 htype Tb
  obtain ⟨h11ab, h11na⟩ := N11a (K ⧸ center K) htype Tb hW
  by_cases hTab : IsMulCommutative (Tb : Subgroup (K ⧸ center K))
  ·
    have hsq := h11ab hTab
    have hdec : ∀ t ∈ (P : Subgroup K), ∃ a ∈ A', a⁻¹ * t ∈ center K := by
      intro t ht
      have h1 := hT1 t ht (hsq _ (by rw [hTbcoe]; exact ⟨t, ht, rfl⟩))
      obtain ⟨a, ha, hat⟩ := h1
      refine ⟨a, ha, ?_⟩
      rw [← QuotientGroup.eq]
      exact hat
    have key : ∀ a b u v : K, a * b = b * a → (∀ g, g * u = u * g) → (∀ g, g * v = v * g) →
        (a * u) * (b * v) = (b * v) * (a * u) := by
      intro a b u v hab hu hv
      calc (a * u) * (b * v) = a * (u * b) * v := by group
        _ = a * (b * u) * v := by rw [← hu b]
        _ = (a * b) * (u * v) := by group
        _ = (b * a) * (v * u) := by rw [hab, hv u]
        _ = b * (a * v) * u := by group
        _ = b * (v * a) * u := by rw [hv a]
        _ = (b * v) * (a * u) := by group
    have hPab : IsMulCommutative (P : Subgroup K) := by
      refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      obtain ⟨a, ha, hax⟩ := hdec x x.2
      obtain ⟨b, hb, hby⟩ := hdec y y.2
      have hab0 : (a : H) * b = b * a := congrArg Subtype.val (hAab.is_comm.comm
        ⟨(a : H), mem_subgroupOf.mp ha⟩ ⟨(b : H), mem_subgroupOf.mp hb⟩)
      have hab : a * b = b * a := Subtype.ext hab0
      have hx : (x : K) = a * (a⁻¹ * x) := by group
      have hy : (y : K) = b * (b⁻¹ * y) := by group
      show (x : K) * y = y * x
      rw [hx, hy]
      exact key a b _ _ hab (mem_center_iff.mp hax) (mem_center_iff.mp hby)
    have hz : (⟨f, hfK⟩ : K) ∈ center K := mem_center_iff.mpr fun g => Subtype.ext (hfc g)
    have hz2 : (⟨f, hfK⟩ : K) ^ 2 = 1 := Subtype.ext hf2
    exact hf1 (congrArg Subtype.val (eq_one_of_mem_center P hz hz2))
  · rcases h11na hTab with ⟨n, hn, ⟨e⟩⟩ | ⟨q', hq', ⟨e⟩⟩
    ·
      have hB := (bender_suzuki_borel_full n hn).map_mulEquiv e.symm
      obtain ⟨-, -, hZc, -⟩ := benderBorel_sylowCenter hB Tb
      have h11c := (N11c (K ⧸ center K) (Or.inl ⟨n, hn, ⟨e⟩⟩) Tb).1
      rw [h11c, hZc] at hT4
      have h2 : 2 ^ (2 * n + 2) = Nat.card A := by rw [← hT4]; ring
      rcases hcard with h | h
      · rw [h, show (8 : ℕ) = 2 ^ 3 by norm_num] at h2
        have := Nat.pow_right_injective (le_refl 2) h2
        omega
      · rw [h, show (32 : ℕ) = 2 ^ 5 by norm_num] at h2
        have := Nat.pow_right_injective (le_refl 2) h2
        omega
    ·
      exact false_of_unitary hA2 hfA hcard hC hAK Tb hT3 hT4 e hq'

theorem normal_of_components
    (S : Sylow 2 H) {A : Subgroup H} (hAS : A ≤ (S : Subgroup H)) (hAab : IsMulCommutative A)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hSA : (S : Subgroup H) ≤ normalizer (A : Set H))
    {f : H} (hfA : f ∈ A) (hf1 : f ≠ 1) (hfc : ∀ h : H, h * f = f * h)
    (hZS : (S : Subgroup H) ⊓ centralizer ((S : Subgroup H) : Set H) = zpowers f)
    (hcard : Nat.card A = 8 ∨ Nat.card A = 32)
    (hC : ∀ a ∈ A, a ∉ zpowers f → IsPGroup 2 (centralizer ({a} : Set H)))
    (hcomp : ∀ K : Subgroup H, CFSG.IsComponent K → K ≤ normalClosure (A : Set H) →
      goldschmidtSimpleType (K ⧸ center K) ∧ InducesOmega1 A K S ∧
      ∀ a ∈ A, ∃ x ∈ A ⊓ K, ∀ y ∈ K, a⁻¹ * y * a = x⁻¹ * y * x)
    (hnone : (∀ K : Subgroup H, CFSG.IsComponent K → ¬ K ≤ normalClosure (A : Set H)) →
      A.Normal) :
    A.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hAn
  obtain ⟨K, hK, hKM⟩ : ∃ K : Subgroup H, CFSG.IsComponent K ∧
      K ≤ normalClosure (A : Set H) := by
    by_contra h
    push Not at h
    exact hAn (hnone h)
  obtain ⟨htype, hind, hcov⟩ := hcomp K hK hKM
  have hzf : ∀ z ∈ zpowers f, ∀ h : H, h * z = z * h := by
    rintro _ ⟨k, rfl⟩ h
    exact Commute.zpow_right (hfc h) k
  have hcen : ∀ L : Subgroup H, CFSG.IsComponent L → ∀ a ∈ A,
      (∀ y ∈ L, y * a = a * y) → a ∈ zpowers f := fun L hL a ha hc => by
    by_contra haf
    exact not_isPGroup_of_isComponent hL ((hC a ha haf).to_le fun y hy =>
      mem_centralizer_singleton_iff.mpr (hc y hy))
  obtain ⟨x, hxAK, y, hyK, hxy⟩ : ∃ x ∈ A ⊓ K, ∃ y ∈ K, x⁻¹ * y * x ≠ y := by
    obtain ⟨a, ha, y, hy, hay⟩ := AS81.Qbar.exists_mem_conj_ne S hK htype hind
    obtain ⟨x, hx, hxa⟩ := hcov a ha
    exact ⟨x, hx, y, hy, by rwa [← hxa y hy]⟩
  have hxf : x ∉ zpowers f := fun h => hxy (by rw [mul_assoc, hzf x h y]; group)
  have huniq : ∀ L : Subgroup H, CFSG.IsComponent L → L ≤ normalClosure (A : Set H) →
      L = K := by
    intro L hL hLM
    by_contra hLK
    have hne : (⟨K, hK⟩ : ComponentIndex H) ≠ ⟨L, hL⟩ := fun h =>
      hLK (congrArg Subtype.val h).symm
    have hxL : ∀ w ∈ L, w * x = x * w := fun w hw =>
      ((componentIndex_commute hne x w (mem_inf.mp hxAK).2 hw).eq).symm
    exact hxf (hcen L hL x (mem_inf.mp hxAK).1 hxL)
  have hKn : K.Normal := by
    refine ⟨fun k hk h => ?_⟩
    have hc : CFSG.IsComponent (K.map (MulAut.conj h).toMonoidHom) :=
      isComponent_map_mulEquiv _ hK
    have hcM : K.map (MulAut.conj h).toMonoidHom ≤ normalClosure (A : Set H) := by
      rintro _ ⟨k', hk', rfl⟩
      exact normalClosure_normal.conj_mem _ (hKM hk') h
    rw [← huniq _ hc hcM]
    exact ⟨k, hk, rfl⟩
  have hfK : f ∈ K := by
    have hle : A ⊓ K ≤ (S : Subgroup H) := inf_le_left.trans hAS
    have hnorm : (S : Subgroup H) ≤ normalizer ((A ⊓ K : Subgroup H) : Set H) := fun s hs => by
      rw [mem_normalizer_iff]
      intro z
      have h1 := mem_normalizer_iff.mp (hSA hs) z
      have h2 : z ∈ K ↔ s * z * s⁻¹ ∈ K := ⟨fun hz => hKn.conj_mem z hz s, fun hz => by
        have := hKn.conj_mem _ hz s⁻¹
        simpa [mul_assoc] using this⟩
      simp only [mem_inf]
      exact and_congr h1 h2
    have hne : A ⊓ K ≠ ⊥ := fun h => by
      have h1 : x ∈ A ⊓ K := hxAK
      rw [h, mem_bot] at h1
      exact hxf (h1 ▸ one_mem _)
    have h1 := GoldExcl.inf_center_ne_bot S.isPGroup' hle hnorm hne
    rw [hZS] at h1
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
    obtain ⟨hzAK, hzf'⟩ := mem_inf.mp hz
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hzf'
    have hof : orderOf f = 2 := orderOf_eq_prime (hA2 f hfA) hf1
    have hmod : f ^ n = f ^ (n % 2) := by
      have h1 := zpow_mod_orderOf f n
      rw [hof] at h1
      exact_mod_cast h1.symm
    rcases Int.emod_two_eq_zero_or_one n with h0 | h0
    · exfalso
      apply hz1
      apply Subtype.ext
      show f ^ n = 1
      rw [hmod, h0, zpow_zero]
    · have := (mem_inf.mp hzAK).2
      rwa [hmod, h0, zpow_one] at this
  have hAK : A ≤ K := by
    intro a ha
    obtain ⟨w, hw, hwa⟩ := hcov a ha
    have hcent : ∀ y ∈ K, y * (a * w⁻¹) = (a * w⁻¹) * y := by
      intro y hy
      have h1 := hwa y hy
      calc y * (a * w⁻¹) = a * (a⁻¹ * y * a) * w⁻¹ := by group
        _ = a * (w⁻¹ * y * w) * w⁻¹ := by rw [h1]
        _ = a * w⁻¹ * y := by group
    have h2 := hcen K hK (a * w⁻¹) (mul_mem ha (inv_mem (mem_inf.mp hw).1)) hcent
    have h3 : a * w⁻¹ ∈ K := zpowers_le.mpr hfK h2
    have h4 := mul_mem h3 (mem_inf.mp hw).2
    simpa using h4
  exact false_of_component S hAab hA2 hAS hfA hf1 hfc hcard hC hK hAK htype hind

theorem normal_of_stronglyClosed
    (hG : GoldschmidtComponents) (hO : goldschmidtOddCore H = ⊥) (S : Sylow 2 H)
    {A : Subgroup H} (hAS : A ≤ (S : Subgroup H)) (hAab : IsMulCommutative A)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hSA : (S : Subgroup H) ≤ normalizer (A : Set H))
    {f : H} (hfA : f ∈ A) (hf1 : f ≠ 1) (hfc : ∀ h : H, h * f = f * h)
    (hZS : (S : Subgroup H) ⊓ centralizer ((S : Subgroup H) : Set H) = zpowers f)
    (hcard : Nat.card A = 8 ∨ Nat.card A = 32)
    (hC : ∀ a ∈ A, a ∉ zpowers f → IsPGroup 2 (centralizer ({a} : Set H)))
    (hcl : fusionStronglyClosed (A : Set H) (S : Subgroup H)) : A.Normal :=
  normal_of_components S hAS hAab hA2 hSA hfA hf1 hfc hZS hcard hC
    (hG H hO S A hAS hAab hcl).1 (hG H hO S A hAS hAab hcl).2

end GoldExcl

end CFSG.ComponentClassification.GMS78
