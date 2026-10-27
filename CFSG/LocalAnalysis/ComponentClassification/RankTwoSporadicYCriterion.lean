module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicActionHom
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Basic

variable {G : Type*} [Group G]

theorem mem_normalizer_of_commute_of_tightlyEmbedded [Finite G] {Q : Subgroup G}
    (hQ : TightlyEmbedded Q) {t c : G} (htQ : t ∈ Q) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hc : c * t = t * c) : c ∈ normalizer (Q : Set G) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  StandardSubgroupAPI.centralizer_le_normalizer_of_mem_of_orderOf_eq_two hQ htQ
    (orderOf_eq_prime ht2 ht1) (mem_centralizer_singleton_iff.2 hc)

theorem sq_eq_one_of_isPGroup_zpowers [Finite G] {K : Subgroup G}
    (hR : ∀ R : Subgroup G, IsSylowOf 2 R K → IsElemAbelian 2 R) {x : G} (hx : x ∈ K)
    (h2 : IsPGroup 2 (zpowers x)) : x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (h2.comap_subtype (K := K)).exists_le_sylow
  have hsyl : IsSylowOf 2 ((S : Subgroup K).map K.subtype) K := ⟨S, rfl⟩
  refine (hR _ hsyl).2 x ⟨⟨x, hx⟩, hS ?_, rfl⟩
  exact mem_zpowers _

theorem tightlyEmbedded_centralizer_of_standard {A : Subgroup G}
    (hA : standardComponentIsStandard A) : TightlyEmbedded (centralizer (A : Set G)) :=
  hA.tightlyEmbedded_centralizer

theorem tightlyEmbedded_rightConjugate' {K : Subgroup G} (hK : TightlyEmbedded K) (g : G) :
    TightlyEmbedded (rightConjugate K g) :=
  StandardSubgroupAPI.tightlyEmbedded_rightConjugate hK g

theorem four_dvd_card_of_one_lt_pRank [Finite G] {K : Subgroup G} (hK : 1 < Open.pRank 2 K) :
    4 ∣ Nat.card K := by
  set S := {k : ℕ | ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}
  have hne : S.Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty] at hS
    have : Open.pRank 2 K = 0 := by
      change sSup S = 0
      rw [hS, csSup_empty]
      rfl
    omega
  obtain ⟨k, ⟨E, hEK, -, hE⟩, hk⟩ := exists_lt_of_lt_csSup hne hK
  have h4 : 4 ∣ Nat.card E := by
    rw [hE]
    exact (pow_dvd_pow 2 hk : 2 ^ 2 ∣ 2 ^ k)
  exact h4.trans (card_dvd_of_le hEK)

theorem card_map_eq_of_inf_centralizer {W : Type*} [Group W] {A T : Subgroup G}
    {X : Subgroup W} {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    (hTC : T ⊓ centralizer (A : Set G) = ⊥) :
    Nat.card ((T.subgroupOf (normalizer (A : Set G))).map ψ) =
      Nat.card (T.subgroupOf (normalizer (A : Set G))) := by
  refine (Nat.card_congr (Equiv.ofBijective _ ⟨?_, ψ.subgroupMap_surjective _⟩)).symm
  intro x y hxy
  have hxy' : ψ (x : normalizer (A : Set G)) = ψ (y : normalizer (A : Set G)) :=
    congrArg Subtype.val hxy
  have h : ψ ((x : normalizer (A : Set G))⁻¹ * (y : normalizer (A : Set G))) = 1 := by
    rw [map_mul, map_inv, hxy', inv_mul_cancel]
  have hC := (hψ.eq_one_iff _).mp h
  have hT : (((x : normalizer (A : Set G))⁻¹ * (y : normalizer (A : Set G)) :
      normalizer (A : Set G)) : G) ∈ T := by
    simp only [coe_mul, coe_inv]
    exact T.mul_mem (T.inv_mem x.2) y.2
  have h1 : (((x : normalizer (A : Set G))⁻¹ * (y : normalizer (A : Set G)) :
      normalizer (A : Set G)) : G) = 1 := by
    rw [← mem_bot, ← hTC]
    exact ⟨hT, hC⟩
  have h2 : (x : normalizer (A : Set G)) = y := by
    rw [← inv_mul_eq_one]
    exact Subtype.ext h1
  exact Subtype.ext h2

end Basic

section HypII

theorem hypII_of_yCensus {X₀ W : Type*} [Group X₀] [Group W] [Finite W] {X : Subgroup W}
    (hW : AutModel X₀ W X) (hc : YCensus X (· ≤ X)) {A : Type*} [Group A]
    (hA : commutator A = ⊤) (e : A ⧸ center A ≃* X₀) : AS76b.HypII A := by
  intro H _ _ B T ⟨f⟩ hT hXh
  obtain ⟨hTab, hT4, hTN, hTC⟩ := hT
  obtain ⟨Xh, hXle, hTsyl, -, htight⟩ := hXh
  by_contra hnot
  have hB : commutator ↥B = ⊤ := by
    have hAp : Group.IsPerfect A := (Group.isPerfect_def).2 hA
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective)
  let eB : ↥B ⧸ center ↥B ≃* X₀ :=
    (QuotientGroup.congr (center ↥B) (center A) f (map_center_eq f)).trans e
  obtain ⟨ψ, hψ⟩ := exists_isActionHom hW hB eB
  have hTX : T ≤ Xh := hTsyl.le
  have hXN : Xh ≤ normalizer (B : Set H) := hXle.trans (sup_le hTN le_normalizer)
  have hTsyl' : IsSylowOf 2 T (Xh ⊓ normalizer (B : Set H)) := by
    rwa [inf_eq_left.mpr hXN]
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ B, c * t = t * c → c ∈ normalizer (Xh : Set H) := by
    intro t ht ht1 c hc hct
    have hn := mem_normalizer_of_commute_of_tightlyEmbedded htight
      (t := ⟨t, le_sup_left (a := T) (b := B) ht⟩) (c := ⟨c, le_sup_right (a := T) hc⟩)
      (hTX ht) (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext (hTab.2 t ht))
      (Subtype.ext hct)
    rw [mem_normalizer_iff]
    intro x
    by_cases hx : x ∈ T ⊔ B
    · have := (mem_normalizer_iff.mp hn) ⟨x, hx⟩
      simpa [mem_subgroupOf] using this
    · have hcx : c * x * c⁻¹ ∉ T ⊔ B := by
        intro h
        apply hx
        have := (T ⊔ B).mul_mem ((T ⊔ B).mul_mem ((T ⊔ B).inv_mem
          (le_sup_right (a := T) hc)) h) (le_sup_right (a := T) hc)
        simpa [mul_assoc] using this
      exact ⟨fun h => absurd (hXle h) hx, fun h => absurd (hXle h) hcx⟩
  refine not_yWitness_map hψ hTsyl' hTab.2 hQ (hc _ ?_ ?_ ?_)
  ·
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [coe_mul]
      exact congrArg Subtype.val (hTab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hTab.2 _ hx)
      rw [this, map_one]
  ·
    rw [card_map_eq_of_inf_centralizer hψ hTC,
      Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv]
    exact hT4
  ·
    intro hle
    apply hnot
    intro t ht
    obtain ⟨b, hb, hbt⟩ := hψ.exists_eq _ (hle ⟨⟨t, hTN ht⟩, ht, rfl⟩)
    have h1 : ψ ((⟨b, le_normalizer hb⟩ : normalizer (B : Set H))⁻¹ * ⟨t, hTN ht⟩) = 1 := by
      rw [map_mul, map_inv, hbt, inv_mul_cancel]
    have hC := (hψ.eq_one_iff _).mp h1
    simp only [coe_mul, coe_inv] at hC
    rw [show t = b * (b⁻¹ * t) by group]
    exact mul_mem_sup hb hC

end HypII

section Standard

theorem commute_of_sq_eq_one {G : Type*} [Group G] {T : Subgroup G}
    (h : ∀ x ∈ T, x ^ 2 = 1) {x y : G} (hx : x ∈ T) (hy : y ∈ T) : x * y = y * x := by
  have hxy := h _ (T.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h y hy)
  have : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hxy)).symm
  rw [this, mul_inv_rev, hx', hy']

theorem exc_of_yCensus (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) {G : Type} [Group G]
    [Finite G] {A : Subgroup G} (hA : AS76b.Hyp31 A) {X₀ W : Type*} [Group X₀] [Group W]
    [Finite W] {X : Subgroup W} (hW : AutModel X₀ W X) (e : ↥A ⧸ center ↥A ≃* X₀) :
    ∃ ψ : normalizer (A : Set G) →* W, IsActionHom A X ψ ∧
      ∃ g : G, g ∉ normalizer (A : Set G) ∧ ∃ T : Subgroup G,
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) ∧
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) ∧
        ∀ Exc : Subgroup W → Prop, YCensus X Exc →
          Exc ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, T, hT1, hT2⟩ := h33 G A hA
  have hR := h32 G A hA
  obtain ⟨ψ, hψ⟩ := exists_isActionHom hW hA.standard.1.1 e
  refine ⟨ψ, hψ, g, hg, T, hT1, hT2, fun Exc hc => ?_⟩
  by_contra hExc
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hA.standard.2.2.2.1]
    exact hg
  have hTab : ∀ x ∈ T, x ^ 2 = 1 := by
    intro x hx
    have hxK : g * x * g⁻¹ ∈ centralizer (A : Set G) :=
      (mem_rightConjugate_iff _ g x).mp (hT2.le hx)
    have h2 : IsPGroup 2 (zpowers (g * x * g⁻¹)) := by
      have hx2 : IsPGroup 2 (zpowers x) := hT2.isPGroup.to_le (zpowers_le.mpr hx)
      have := hx2.map (MulAut.conj g).toMonoidHom
      rwa [MonoidHom.map_zpowers] at this
    have hsq := sq_eq_one_of_isPGroup_zpowers hR hxK h2
    have hc' : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
    rw [hc'] at hsq
    have := congrArg (fun y => g⁻¹ * y * g) hsq
    simpa [mul_assoc] using this
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c →
      c ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) :=
    fun t ht ht1 c _ hct => mem_normalizer_of_commute_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate' hK g) (hT2.le ht) ht1 (hTab t ht) hct
  refine not_yWitness_map hψ hT1 hTab hQ (hc _ ?_ ?_ hExc)
  ·
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact commute_of_sq_eq_one hTab hx hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hTab _ hx)
      rw [this, map_one]
  ·
    have hTN : T ≤ normalizer (A : Set G) := hT1.le.trans inf_le_right
    have hTC : T ⊓ centralizer (A : Set G) = ⊥ := by
      refine two_subgroup_of_odd_eq_bot _ (centralizer (A : Set G) ⊓
        rightConjugate (centralizer (A : Set G)) g) (hT2.isPGroup.to_inf_left) (hK.2 g hgK) ?_
      exact le_inf inf_le_right (inf_le_left.trans hT2.le)
    rw [card_map_eq_of_inf_centralizer hψ hTC,
      Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv, hT2.card_eq, rightConjugate_card]
    have h4 := four_dvd_card_of_one_lt_pRank hA.rank
    have hpos : Nat.card (centralizer (A : Set G)) ≠ 0 := Nat.card_pos.ne'
    have hle : 2 ≤ (Nat.card (centralizer (A : Set G))).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hpos).mp (by simpa using h4)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hle

theorem sporadicCaseOdd_of_yCensus (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    {s : TauCeti.SporadicName} {W : Type*} [Group W] [Finite W] {X : Subgroup W}
    (hW : AutModel (Blueprint.NativeSporadic.Carrier s) W X) (hc : YCensus X (fun _ => False)) :
    SporadicCaseOdd s := by
  intro G _ _ A hH hodd ⟨e⟩
  have hcII : YCensus X (· ≤ X) := fun E h1 h2 _ => hc E h1 h2 id
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus hW hcII hH.standard.1.1 e, hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  obtain ⟨ψ, -, g, -, T, -, -, hExc⟩ := exc_of_yCensus h32 h33 hyp hW e
  exact hExc _ hc

end Standard

end CFSG.ComponentClassification.RankTwoSporadic
