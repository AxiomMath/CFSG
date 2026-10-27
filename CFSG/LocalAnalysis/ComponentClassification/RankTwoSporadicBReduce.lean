module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39Final
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMovedPerfect
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoClassical CFSG.ComponentClassification.RankTwoExceptional
open scoped commutatorElement

section Perfect

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_eq {a b c d : G} (hcb : c * b = b * c) (hcd : c * d = d * c)
    (hda : d * a = a * d) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hda' : d * a⁻¹ = a⁻¹ * d := (Commute.inv_right (show Commute d a from hda)).eq
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
    _ = a * b * (c * d * c⁻¹) * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hcb]; group
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by rw [hcd, mul_inv_cancel_right]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hda']; group

theorem commutator_closure_pair {a b : G} {p q r : ℕ} (ha : a ^ p = 1) (hb : b ^ q = 1)
    (hab : (a * b) ^ r = 1) (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r) :
    ⁅closure ({a, b} : Set G), closure ({a, b} : Set G)⁆ = closure ({a, b} : Set G) := by
  set H := closure ({a, b} : Set G)
  refine le_antisymm (commutator_le_self H) ?_
  have key : ∀ x : ↥H, Abelianization.of x = 1 → (x : G) ∈ ⁅H, H⁆ := by
    intro x hx
    rw [← map_subtype_commutator, ← Abelianization.ker_of]
    exact ⟨x, hx, rfl⟩
  have haH : a ∈ H := subset_closure (Set.mem_insert a {b})
  have hbH : b ∈ H := subset_closure (Set.mem_insert_of_mem a rfl)
  have hα : Abelianization.of (⟨a, haH⟩ : ↥H) ^ p = 1 := by
    have h : (⟨a, haH⟩ : ↥H) ^ p = 1 := Subtype.ext (by simpa using ha)
    rw [← map_pow, h, map_one]
  have hβ : Abelianization.of (⟨b, hbH⟩ : ↥H) ^ q = 1 := by
    have h : (⟨b, hbH⟩ : ↥H) ^ q = 1 := Subtype.ext (by simpa using hb)
    rw [← map_pow, h, map_one]
  have hαβ :
      Abelianization.of (⟨a, haH⟩ : ↥H) ^ r * Abelianization.of (⟨b, hbH⟩ : ↥H) ^ r = 1 := by
    have h : ((⟨a, haH⟩ : ↥H) * ⟨b, hbH⟩) ^ r = 1 := Subtype.ext (by simpa using hab)
    rw [← mul_pow, ← map_mul, ← map_pow, h, map_one]
  have h1 : Abelianization.of (⟨a, haH⟩ : ↥H) = 1 := by
    have h : Abelianization.of (⟨a, haH⟩ : ↥H) ^ (r * q) = 1 := by
      rw [pow_mul, eq_inv_of_mul_eq_one_left hαβ, inv_pow, ← pow_mul, mul_comm, pow_mul, hβ,
        one_pow, inv_one]
    have hg : p.gcd (r * q) = 1 := Nat.Coprime.mul_right hpr hpq
    have := pow_gcd_eq_one.mpr ⟨hα, h⟩
    rwa [hg, pow_one] at this
  have h2 : Abelianization.of (⟨b, hbH⟩ : ↥H) = 1 := by
    have h : Abelianization.of (⟨b, hbH⟩ : ↥H) ^ (r * p) = 1 := by
      rw [pow_mul, eq_inv_of_mul_eq_one_right hαβ, inv_pow, ← pow_mul, mul_comm, pow_mul, hα,
        one_pow, inv_one]
    have hg : q.gcd (r * p) = 1 := Nat.Coprime.mul_right hqr hpq.symm
    have := pow_gcd_eq_one.mpr ⟨hβ, h⟩
    rwa [hg, pow_one] at this
  refine (closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · exact key _ h1
  · exact key _ h2

end Perfect

section Lift

variable {G W : Type*} [Group G] [Group W]

theorem exists_perfect_lift_centralizer {A : Subgroup G} {ψ : normalizer (A : Set G) →* W}
    (hψ : IsActionHom A ⊤ ψ) {t : G} (ht : t ∈ normalizer (A : Set G)) {P : Subgroup W}
    (hP : ⁅P, P⁆ = P) (hPt : P ≤ centralizer {ψ ⟨t, ht⟩}) :
    ∃ Q : Subgroup G, ⁅Q, Q⁆ = Q ∧ Q ≤ A ⊓ centralizer {t} ∧
      ∀ p ∈ P, ∃ (q : G) (hq : q ∈ A), q ∈ Q ∧ ψ ⟨q, le_normalizer hq⟩ = p := by
  set n : normalizer (A : Set G) := ⟨t, ht⟩
  set AN : Subgroup (normalizer (A : Set G)) := A.subgroupOf (normalizer (A : Set G))
  set K : Subgroup (normalizer (A : Set G)) := AN ⊓ P.comap ψ
  have hcen : ∀ k : normalizer (A : Set G), ψ k = 1 → ∀ a ∈ AN, k * a = a * k := by
    intro k hk a ha
    have hk' := (hψ.eq_one_iff k).mp hk
    exact Subtype.ext ((mem_centralizer_iff.mp hk') a ha).symm
  have hKmap : K.map ψ = P := by
    refine le_antisymm ?_ fun p hp => ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact hk.2
    · obtain ⟨a, ha, hap⟩ := hψ.exists_eq p (mem_top p)
      refine ⟨⟨a, le_normalizer ha⟩, ⟨ha, ?_⟩, hap⟩
      change ψ ⟨a, le_normalizer ha⟩ ∈ P
      rw [hap]
      exact hp
  have hconj : ∀ k ∈ K, ∃ z : normalizer (A : Set G), n * k * n⁻¹ = k * z ∧ z ∈ AN ∧
      ∀ a ∈ AN, z * a = a * z := by
    intro k hk
    refine ⟨k⁻¹ * (n * k * n⁻¹), by group, ?_, hcen _ ?_⟩
    · have hkA : (k : G) ∈ A := hk.1
      have hnk : (n : G) * k * (n : G)⁻¹ ∈ A := (mem_normalizer_iff.mp ht k).mp hkA
      change ((k⁻¹ * (n * k * n⁻¹) : normalizer (A : Set G)) : G) ∈ A
      simp only [coe_mul, coe_inv]
      exact A.mul_mem (A.inv_mem hkA) hnk
    · have hc : ψ k * ψ n = ψ n * ψ k := mem_centralizer_singleton_iff.mp (hPt hk.2)
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, ← hc]
      group
  have hK1 : ⁅K, K⁆ ≤ centralizer {n} := by
    rw [commutator_le]
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨z₁, hz₁, hzA₁, hc₁⟩ := hconj k₁ hk₁
    obtain ⟨z₂, hz₂, hzA₂, hc₂⟩ := hconj k₂ hk₂
    have h := map_commutatorElement (MulAut.conj n).toMonoidHom k₁ k₂
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [hz₁, hz₂, commutatorElement_mul_mul_eq (hc₁ k₂ hk₂.1) (hc₁ z₂ hzA₂) (hc₂ k₁ hk₁.1)] at h
    rw [mem_centralizer_singleton_iff]
    calc ⁅k₁, k₂⁆ * n = n * ⁅k₁, k₂⁆ * n⁻¹ * n := by rw [h]
      _ = n * ⁅k₁, k₂⁆ := by group
  set K1 := ⁅K, K⁆
  set K2 := ⁅K1, K1⁆
  have hK1map : K1.map ψ = P := by rw [map_commutator, hKmap, hP]
  have hK2map : K2.map ψ = P := by rw [map_commutator, hK1map, hP]
  have hK1K : K1 ≤ K := commutator_le_self K
  have hK2K1 : K2 ≤ K1 := commutator_le_self K1
  have hlift : ∀ k ∈ K, ∃ k' ∈ K2, ∃ c : normalizer (A : Set G), k = k' * c ∧
      ∀ a ∈ AN, c * a = a * c := by
    intro k hk
    have hk' : ψ k ∈ K2.map ψ := by rw [hK2map]; exact hk.2
    obtain ⟨k', hk'K, hkk⟩ := hk'
    refine ⟨k', hk'K, k'⁻¹ * k, by group, hcen _ ?_⟩
    rw [map_mul, map_inv, hkk, inv_mul_cancel]
  have hK2perf : ⁅K2, K2⁆ = K2 := by
    refine le_antisymm (commutator_le_self K2) (hK2K1.trans (commutator_le.mpr ?_))
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨k₁', hk₁', c₁, rfl, hc₁⟩ := hlift k₁ hk₁
    obtain ⟨k₂', hk₂', c₂, rfl, hc₂⟩ := hlift k₂ hk₂
    have hA₁ : k₁' ∈ AN := (hK2K1.trans hK1K) hk₁' |>.1
    have hA₂ : k₂' ∈ AN := (hK2K1.trans hK1K) hk₂' |>.1
    have hc₂A : c₂ ∈ AN := by
      have h := (hK2K1.trans hK1K) hk₂' |>.1
      have := AN.mul_mem (AN.inv_mem h) hk₂.1
      simpa using this
    rw [commutatorElement_mul_mul_eq (hc₁ k₂' hA₂) (hc₁ c₂ hc₂A) (hc₂ k₁' hA₁)]
    exact commutator_mem_commutator hk₁' hk₂'
  refine ⟨K2.map (normalizer (A : Set G)).subtype, ?_, ?_, fun p hp => ?_⟩
  · rw [← map_commutator, hK2perf]
  · rintro _ ⟨k, hk, rfl⟩
    have hk1 := hK2K1 hk
    refine ⟨(hK1K hk1).1, ?_⟩
    have hkn := mem_centralizer_singleton_iff.mp (hK1 hk1)
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hkn)
  · rw [← hK2map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    exact ⟨k, ((hK2K1.trans hK1K) hk).1, ⟨k, hk, rfl⟩, rfl⟩

end Lift

section Case

@[expose] def PerfectCentralizerBound {W : Type*} [Group W] (r : W → ℕ) : Prop :=
  ∀ x : W, x ^ 2 = 1 → x ≠ 1 → ∃ P : Subgroup W, ⁅P, P⁆ = P ∧ P ≤ centralizer {x} ∧
    ∀ y ∈ centralizer (P : Set W), y * x = x * y → y ^ 2 = 1 → y ≠ 1 → y ≠ x → r y < r x

theorem center_eq_bot_of_quasisimple {A Q : Type*} [Group A] [Group Q]
    (hA : Open.IsQuasisimple A)
    (e : A ⧸ center A ≃* Q) : center Q = ⊥ := by
  have hs : IsSimpleGroup (A ⧸ center A) := hA.2
  have hp : commutator (A ⧸ center A) = ⊤ := by
    have : Group.IsPerfect A := (Group.isPerfect_def).2 hA.1
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center A))
        (QuotientGroup.mk'_surjective _))
  have hZ : center (A ⧸ center A) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (A ⧸ center A)) with h | h
    · exact h
    · exfalso
      have hc : commutator (A ⧸ center A) = ⊥ := by
        rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer, coe_top,
          centralizer_univ, h]
      rw [hp] at hc
      exact top_ne_bot hc
  rw [← map_center_eq e, hZ, Subgroup.map_bot]

theorem odd_card_commutator_outer_of_allInner {X : Type*} [Group X]
    (h : ∀ α : MulAut X, ∃ g : X, α = MulAut.conj g) :
    Odd (Nat.card (commutator (Outer X))) := by
  have hs : Subsingleton (Outer X) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H α =>
      induction b using QuotientGroup.induction_on with
      | H β =>
        rw [QuotientGroup.eq]
        obtain ⟨g, hg⟩ := h (α⁻¹ * β)
        exact ⟨g, hg.symm⟩
  exact odd_card_commutator_of_comm fun a b => Subsingleton.elim _ _

theorem sporadicCaseOdd_of_perfectCentralizerBound
    (h32 : Lemma32) (h33 : Lemma33Three) {s : TauCeti.SporadicName}
    (hinn : ∀ α : MulAut (Blueprint.NativeSporadic.Carrier s), ∃ g, α = MulAut.conj g)
    {r : Blueprint.NativeSporadic.Carrier s → ℕ} (hr : PerfectCentralizerBound r) :
    SporadicCaseOdd s := by
  intro G _ _ A hH hodd ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Open.IsQuasisimple ↥A := hH.standard.1
  have : Finite (Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv _ e.toEquiv
  have hW := autModel_top (center_eq_bot_of_quasisimple hq e) hinn
  have hyp : Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus hW (fun _ _ _ hE => absurd le_top hE) hq.1 e, hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  have hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))) :=
    odd_card_commutator_outer_of_quot hq.1
      (odd_card_commutator_outer_of_equiv e (odd_card_commutator_outer_of_allInner hinn))
  obtain ⟨g, hg, T, hT1, hT2⟩ := h33 G A hyp
  obtain ⟨ψ, hψ⟩ := exists_isActionHom hW hq.1 e
  have hR := h32 G A hyp
  have hK := tightlyEmbedded_centralizer_of_standard hyp.standard
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hyp.standard.2.2.2.1]
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
  have hTN : T ≤ normalizer (A : Set G) := hT1.le.trans inf_le_right
  have hTC : T ⊓ centralizer (A : Set G) = ⊥ := by
    refine two_subgroup_of_odd_eq_bot _ (centralizer (A : Set G) ⊓
      rightConjugate (centralizer (A : Set G)) g) (hT2.isPGroup.to_inf_left) (hK.2 g hgK) ?_
    exact le_inf inf_le_right (inf_le_left.trans hT2.le)
  have hT4 : 4 ≤ Nat.card T := by
    rw [hT2.card_eq, rightConjugate_card]
    have h4 := four_dvd_card_of_one_lt_pRank hyp.rank
    have hpos : Nat.card (centralizer (A : Set G)) ≠ 0 := Nat.card_pos.ne'
    have hle : 2 ≤ (Nat.card (centralizer (A : Set G))).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hpos).mp (by simpa using h4)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hle
  have hinj : ∀ (a b : G) (ha : a ∈ T) (hb : b ∈ T),
      ψ ⟨a, hTN ha⟩ = ψ ⟨b, hTN hb⟩ → a = b := by
    intro a b ha hb hab
    have h1 : ψ ((⟨a, hTN ha⟩ : normalizer (A : Set G))⁻¹ * ⟨b, hTN hb⟩) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hC := (hψ.eq_one_iff _).mp h1
    have hab' : a⁻¹ * b ∈ T ⊓ centralizer (A : Set G) :=
      ⟨T.mul_mem (T.inv_mem ha) hb, by simpa using hC⟩
    rw [hTC, mem_bot, inv_mul_eq_one] at hab'
    exact hab'
  have key : ∀ (t : G) (ht : t ∈ T), t ≠ 1 → ∀ P : Subgroup (Blueprint.NativeSporadic.Carrier s),
      ⁅P, P⁆ = P → P ≤ centralizer {ψ ⟨t, hTN ht⟩} →
        ∀ (b : G) (hb : b ∈ T), ψ ⟨b, hTN hb⟩ ∈ centralizer (P : Set _) := by
    intro t ht ht1 P hP hPt b hb
    obtain ⟨Q, hQ, hQle, hQP⟩ := exists_perfect_lift_centralizer hψ (hTN ht) hP hPt
    have hQres : Q ≤ admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆) := by
      refine le_admResidual_of_perfect ?_ hQ
      calc Q = ⁅Q, Q⁆ := hQ.symm
        _ ≤ ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆ :=
          commutator_mono hQle hQle
        _ ≤ _ := le_sup_right
    obtain ⟨h1, h2⟩ := AS76b.Lemma39.lemma39_one_of_lemma32 h32 hyp hT2 ht ht1 hOut
    have hQT : Q ≤ centralizer (T : Set G) := hQres.trans (h1.trans h2)
    rw [mem_centralizer_iff]
    intro p hp
    obtain ⟨q, hqA, hqQ, rfl⟩ := hQP p hp
    have hc : b * q = q * b := (mem_centralizer_iff.mp (hQT hqQ)) b hb
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext hc.symm)
  obtain ⟨t, htT, ht0⟩ := exists_not_mem_zpowers_of_isElemAbelian hT4 (one_pow 2)
  have ht1 : t ≠ 1 := fun h => ht0 (by rw [h]; exact one_mem _)
  obtain ⟨b, hbT, hb0⟩ := exists_not_mem_zpowers_of_isElemAbelian hT4 (hTab t htT)
  have hb1 : b ≠ 1 := fun h => hb0 (by rw [h]; exact one_mem _)
  have hbt : b ≠ t := fun h => hb0 (by rw [h]; exact mem_zpowers _)
  have hsq : ∀ (a : G) (ha : a ∈ T), ψ ⟨a, hTN ha⟩ ^ 2 = 1 := by
    intro a ha
    rw [← map_pow]
    have : (⟨a, hTN ha⟩ : normalizer (A : Set G)) ^ 2 = 1 := Subtype.ext (by simpa using hTab a ha)
    rw [this, map_one]
  have hne1 : ∀ (a : G) (ha : a ∈ T), a ≠ 1 → ψ ⟨a, hTN ha⟩ ≠ 1 := by
    intro a ha ha1 h
    apply ha1
    have h1 : ψ ⟨1, hTN (one_mem T)⟩ = 1 := by
      rw [show (⟨1, hTN (one_mem T)⟩ : normalizer (A : Set G)) = 1 from rfl, map_one]
    exact hinj a 1 ha (one_mem T) (h.trans h1.symm)
  have hcomm : ψ ⟨b, hTN hbT⟩ * ψ ⟨t, hTN htT⟩ = ψ ⟨t, hTN htT⟩ * ψ ⟨b, hTN hbT⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (commute_of_sq_eq_one hTab hbT htT))
  have hne : ψ ⟨b, hTN hbT⟩ ≠ ψ ⟨t, hTN htT⟩ := fun h => hbt (hinj b t hbT htT h)
  obtain ⟨P, hP, hPt, hPb⟩ := hr _ (hsq t htT) (hne1 t htT ht1)
  have hlt1 := hPb _ (key t htT ht1 P hP hPt b hbT) hcomm (hsq b hbT) (hne1 b hbT hb1) hne
  obtain ⟨P', hP', hPb', hPt'⟩ := hr _ (hsq b hbT) (hne1 b hbT hb1)
  have hlt2 := hPt' _ (key b hbT hb1 P' hP' hPb' t htT) hcomm.symm (hsq t htT)
    (hne1 t htT ht1) (Ne.symm hne)
  omega

end Case

end CFSG.ComponentClassification.RankTwoSporadic
