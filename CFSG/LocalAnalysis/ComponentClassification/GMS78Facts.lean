module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma311
public import CFSG.LocalAnalysis.ComponentClassification.GMS78BenderLift
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma36
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev gmsW (L T : Subgroup G) : Subgroup G := (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G))

abbrev gmsA (L T : Subgroup G) : Subgroup G :=
  (T ⊓ L) ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G)

abbrev gmsV (L T : Subgroup G) : Subgroup G := gmsA L T ⊔ (T ⊓ centralizer (L : Set G))

abbrev gmsDelta (L T : Subgroup G) : Set (Subgroup G) :=
  {Q | (∃ x, rightConjugate (T ⊓ centralizer (L : Set G)) x = Q) ∧ Q ≤ gmsV L T}

theorem card_mul_card_le {A B T : Subgroup G} (hAT : A ≤ T) (hBT : B ≤ T) :
    Nat.card A * Nat.card B ≤ Nat.card T * Nat.card (A ⊓ B : Subgroup G) := by
  have h1 := relIndex_mul_card B A
  have h2 := relIndex_mul_card B T
  rw [inf_eq_left.mpr hBT] at h2
  have hne : B.relIndex T ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact Nat.card_pos.ne' h2.symm
  have h3 : B.relIndex A ≤ B.relIndex T := relIndex_le_of_le_right hAT hne
  rw [inf_comm] at h1
  calc Nat.card A * Nat.card B = B.relIndex A * Nat.card (A ⊓ B : Subgroup G) * Nat.card B := by
        rw [h1]
    _ ≤ B.relIndex T * Nat.card (A ⊓ B : Subgroup G) * Nat.card B :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
    _ = Nat.card T * Nat.card (A ⊓ B : Subgroup G) := by rw [← h2]; ring

theorem card_mul_eq_of_cover {ι : Type*} [Fintype ι] {V W : Subgroup G} (hWV : W ≤ V)
    (H : ι → Subgroup G) (hti : ∀ i j, i ≠ j → H i ⊓ H j = ⊥) (hV : ∀ i, H i ≤ V) {c : ℕ}
    (hc : ∀ i, Nat.card (H i) = c) (hcov : ∀ v ∈ V, v ∉ W ↔ ∃ i, v ∈ H i ∧ v ≠ 1) :
    Fintype.card ι * (c - 1) = Nat.card V - Nat.card W := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hcard : ∀ K : Subgroup G, (Finset.univ.filter (· ∈ K)).card = Nat.card K := by
    intro K
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let t : ι → Finset G := fun i => Finset.univ.filter (fun g => g ∈ H i ∧ g ≠ 1)
  let D : Finset G := Finset.univ.filter (fun g => g ∈ V ∧ g ∉ W)
  have ht : ∀ i, (t i).card = c - 1 := by
    intro i
    have h1 : t i = (Finset.univ.filter (· ∈ H i)).erase 1 := by
      ext g
      simp [t, and_comm]
    rw [h1, Finset.card_erase_of_mem (by simp [one_mem]), hcard, hc]
  have hD : D.card = Nat.card V - Nat.card W := by
    have h1 : D = Finset.univ.filter (· ∈ V) \ Finset.univ.filter (· ∈ W) := by
      ext g
      simp [D]
    rw [h1, Finset.card_sdiff, Finset.inter_eq_left.mpr (fun g hg => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact hWV hg), hcard, hcard]
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint t := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro g hgi hgj
    simp only [Finset.mem_filter, t] at hgi hgj
    have : g ∈ H i ⊓ H j := ⟨hgi.2.1, hgj.2.1⟩
    rw [hti i j hij, mem_bot] at this
    exact hgi.2.2 this
  have hEq : Finset.univ.biUnion t = D := by
    ext g
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, t, D]
    constructor
    · rintro ⟨i, hgi, hg1⟩
      exact ⟨hV i hgi, (hcov g (hV i hgi)).mpr ⟨i, hgi, hg1⟩⟩
    · rintro ⟨hgV, hgW⟩
      exact (hcov g hgV).mp hgW
  rw [← hD, ← hEq, Finset.card_biUnion hdisj]
  simp [ht]

omit [Finite G] in
theorem even_card_of_isPGroup {H : Subgroup G} (hH : IsPGroup 2 H) (h1 : H ≠ ⊥) :
    Even (Nat.card H) := by
  rcases hH.card_eq_or_dvd with h | h
  · exact absurd (card_eq_one.mp h) h1
  · exact even_iff_two_dvd.mpr h

theorem sylow_of_benderBorel {L P : Subgroup G} (hZ : Odd (Nat.card (center L))) {q k : ℕ}
    (hq : 2 ≤ q) (hB : fusionBenderBorel (rankTwoQuot L) q k) (hP : IsSylowOf 2 P L) :
    Nat.card P = q ^ k ∧ Nat.card (P ⊓ centralizer (P : Set G) : Subgroup G) = q ∧
      (∀ a ∈ P ⊓ centralizer (P : Set G), a ^ 2 = 1) ∧
      (∀ x ∈ P, x ^ 2 = 1 → x ∈ P ⊓ centralizer (P : Set G)) := by
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hinj := sylowProj_injective hZ hP.isPGroup hP.le
  set ρ := sylowProj hP.le with hρ
  have hcen := mem_center_iff_sylowProj hZ hP hR
  obtain ⟨-, hZ2, hZcard, hRcard⟩ := benderBorel_sylowCenter hB R
  let ι : P ≃* (R : Subgroup (rankTwoQuot L)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hR)
  have hρR : ∀ p, ρ p ∈ (R : Subgroup (rankTwoQuot L)) := fun p => hR ▸ ⟨p, rfl⟩
  refine ⟨?_, ?_, fun a ha => ?_, fun x hx hx2 => ?_⟩
  · rw [Nat.card_congr ι.toEquiv, hRcard]
  · rw [← hZcard]
    refine Nat.card_congr (Equiv.ofBijective
      (fun a => ⟨ρ ⟨a, a.2.1⟩, (hcen ⟨a, a.2.1⟩).mp a.2⟩) ⟨fun a b hab => ?_, fun z => ?_⟩)
    · have h1 := hinj (congrArg Subtype.val hab)
      have h2 := congrArg Subtype.val h1
      exact Subtype.ext h2
    · have hzR : (z : rankTwoQuot L) ∈ ρ.range := by
        rw [hR]
        exact sylowCenter_le _ z.2
      obtain ⟨p, hp⟩ := hzR
      refine ⟨⟨p, (hcen p).mpr (hp ▸ z.2)⟩, Subtype.ext ?_⟩
      exact hp
  · have h1 := hZ2 _ ((hcen ⟨a, ha.1⟩).mp ha)
    rw [← map_pow] at h1
    have h2 := congrArg Subtype.val (hinj (h1.trans (map_one ρ).symm))
    simpa using h2
  · have h1 : ρ ⟨x, hx⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : P) ^ 2 = 1 := Subtype.ext hx2
      rw [this, map_one]
    exact (hcen ⟨x, hx⟩).mpr
      ⟨hρR _, Asc76X.mem_centralizer_of_fusionBenderBorel hB hq R (hρR _) h1⟩

namespace Sec3

variable {L T : Subgroup G}

theorem vFacts (h : Sec3 G L T)
    (hF : Foundation) (hZ : Odd (Nat.card (center L))) {q k : ℕ} (hq : 2 ≤ q)
    (hB : fusionBenderBorel (rankTwoQuot L) q k) :
    Nat.card (gmsV L T) = q * Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) ∧
    IsElemAbelian 2 (gmsV L T) ∧ gmsV L T ≤ gmsW L T ∧
    gmsV L T ≤ centralizer (gmsW L T : Set G) ∧
    (∀ x ∈ gmsW L T, x ^ 2 = 1 → x ∈ gmsV L T) := by
  set K := centralizer (L : Set G) with hKdef
  set T₁ := T ⊓ L with hT₁def
  set T₀ := T ⊓ K with hT₀def
  set W := T₁ ⊔ T₀ with hWdef
  set A₁ := T₁ ⊓ centralizer (T₁ : Set G) with hA₁def
  set V := A₁ ⊔ T₀ with hVdef
  obtain ⟨-, hA₁card, hA₁sq, hinvA⟩ := sylow_of_benderBorel hZ hq hB h.isSylowOf_T₁
  have hT₀el : IsElemAbelian 2 T₀ := h.isElemAbelian_T₀ hF
  have hinf : T₁ ⊓ T₀ = ⊥ := h.inf_eq_bot_of_odd hZ
  have hT₀C : T₀ ≤ centralizer (T₁ : Set G) := fun t ht => mem_centralizer_iff.mpr fun x hx =>
    mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2
  have hT₁N : T₁ ≤ normalizer (T₀ : Set G) :=
    (le_centralizer_iff.mp hT₀C).trans (Subgroup.centralizer_le_normalizer _)
  have hA₁T₁ : A₁ ≤ T₁ := inf_le_left
  have hT₀CA : T₀ ≤ centralizer (A₁ : Set G) := fun t ht => mem_centralizer_iff.mpr fun a ha =>
    mem_centralizer_iff.mp (hT₀C ht) a (hA₁T₁ ha)
  have hA₁N : A₁ ≤ normalizer (T₀ : Set G) := hA₁T₁.trans hT₁N
  have hVcard : Nat.card V = q * Nat.card T₀ := by
    have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hA₁N
    have hbot : T₀ ⊓ A₁ = ⊥ := le_bot_iff.mp (fun x hx => by
      rw [← hinf]
      exact mem_inf.mpr ⟨hA₁T₁ (mem_inf.mp hx).2, (mem_inf.mp hx).1⟩)
    rw [hbot, card_bot, mul_one, sup_comm, hA₁card] at h1
    rw [hVdef, h1, mul_comm]
  have hA₁el : IsElemAbelian 2 A₁ := ⟨⟨⟨fun a b => Subtype.ext
    (show (a : G) * b = b * a from mem_centralizer_iff.mp (mem_inf.mp b.2).2 a (hA₁T₁ a.2))⟩⟩,
    hA₁sq⟩
  have hVel : IsElemAbelian 2 V := isElemAbelian_sup hA₁el hT₀el hT₀CA
  have hVW : V ≤ W := sup_le (hA₁T₁.trans le_sup_left) le_sup_right
  have hVC : V ≤ centralizer (W : Set G) := by
    have hT₀T₀ : T₀ ≤ centralizer (T₀ : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr hT₀el.1
    have hWV : W ≤ centralizer (V : Set G) := sup_le
      (le_centralizer_iff.mp (sup_le inf_le_right hT₀C))
      (le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hT₀CA) hT₀T₀))
    exact le_centralizer_iff.mp hWV
  have hΩ : ∀ x ∈ W, x ^ 2 = 1 → x ∈ V := by
    intro x hx hx2
    obtain ⟨x₁, hx₁, x₀, hx₀, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hT₁N hx
    have hc : x₁ * x₀ = x₀ * x₁ := mem_centralizer_iff.mp (hT₀C hx₀) x₁ hx₁
    have hx₁2 : x₁ ^ 2 = 1 := by
      rw [Commute.mul_pow hc 2, hT₀el.2 x₀ hx₀, mul_one] at hx2
      exact hx2
    exact mul_mem (mem_sup_left (hinvA x₁ hx₁ hx₁2)) (mem_sup_right hx₀)
  exact ⟨hVcard, hVel, hVW, hVC, hΩ⟩

theorem gmsV_inf_eq (h : Sec3 G L T) (hZ : Odd (Nat.card (center L))) :
    gmsV L T ⊓ L = gmsA L T := by
  have hinf := h.inf_eq_bot_of_odd hZ
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxL⟩ := mem_inf.mp hx
    have hA₁N : gmsA L T ≤ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
      fun a ha => (le_centralizer_iff.mp
        (show T ⊓ centralizer (L : Set G) ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) from
        fun t ht => mem_centralizer_iff.mpr fun x hx =>
          mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2)).trans
        (Subgroup.centralizer_le_normalizer _) (mem_inf.mp ha).1
    obtain ⟨a, ha, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N hxV
    have haL : a ∈ L := (mem_inf.mp (mem_inf.mp ha).1).2
    have htL : t ∈ L := by
      have := mul_mem (inv_mem haL) hxL
      rwa [inv_mul_cancel_left] at this
    have ht1 : t ∈ (T ⊓ L) ⊓ (T ⊓ centralizer (L : Set G)) :=
      mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp ht).1, htL⟩, ht⟩
    rw [hinf, mem_bot] at ht1
    rw [ht1, mul_one]
    exact ha
  · exact le_inf le_sup_left fun a ha => (mem_inf.mp (mem_inf.mp ha).1).2

omit [Finite G] in
theorem inf_normalizer_le_normalizer :
    L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ normalizer (gmsV L T : Set G) := by
  have hA₁N : gmsA L T ≤ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun a ha => (le_centralizer_iff.mp
      (show T ⊓ centralizer (L : Set G) ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) from
        fun t ht => mem_centralizer_iff.mpr fun x hx =>
          mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2)).trans
      (Subgroup.centralizer_le_normalizer _) (mem_inf.mp ha).1
  have hconj : ∀ g ∈ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G), ∀ v ∈ gmsV L T,
      g * v * g⁻¹ ∈ gmsV L T := by
    intro g hg v hv
    obtain ⟨hgL, hgN⟩ := mem_inf.mp hg
    obtain ⟨a, ha, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N hv
    have hgt : g * t * g⁻¹ = t := by
      rw [mem_centralizer_iff.mp (mem_inf.mp ht).2 g hgL, mul_inv_cancel_right]
    have hga : g * a * g⁻¹ ∈ gmsA L T := by
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hgN a).mp (mem_inf.mp ha).1,
        mem_centralizer_iff.mpr fun p hp => ?_⟩
      have hp' : g⁻¹ * p * g ∈ T ⊓ L := by
        simpa using (mem_normalizer_iff.mp (inv_mem hgN) p).mp hp
      have h1 : g⁻¹ * p * g * a = a * (g⁻¹ * p * g) :=
        mem_centralizer_iff.mp (mem_inf.mp ha).2 _ hp'
      calc p * (g * a * g⁻¹) = g * (g⁻¹ * p * g * a) * g⁻¹ := by group
        _ = g * (a * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
        _ = g * a * g⁻¹ * p := by group
    rw [show g * (a * t) * g⁻¹ = (g * a * g⁻¹) * (g * t * g⁻¹) by group, hgt]
    exact mul_mem (mem_sup_left hga) (mem_sup_right ht)
  intro g hg
  exact mem_normalizer_of_conj_mem (hconj g hg)
    (fun v hv => by simpa using hconj g⁻¹ (inv_mem hg) v hv)

theorem inf_eq_bot_of_conj (h : Sec3 G L T) {V : Subgroup G} (hV : IsPGroup 2 V) {x₁ x₂ : G}
    (h₁ : rightConjugate (T ⊓ centralizer (L : Set G)) x₁ ≤ V)
    (h₂ : rightConjugate (T ⊓ centralizer (L : Set G)) x₂ ≤ V)
    (hne : rightConjugate (T ⊓ centralizer (L : Set G)) x₁ ≠
      rightConjugate (T ⊓ centralizer (L : Set G)) x₂) :
    rightConjugate (T ⊓ centralizer (L : Set G)) x₁ ⊓
      rightConjugate (T ⊓ centralizer (L : Set G)) x₂ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  have hKte := AS76b.tightlyEmbedded_centralizer h.hyp.standard
  have hK1te := AS76b.tightlyEmbedded_rightConjugate hKte x₁
  have hR₁ := AschbacherTheorem3.isSylowOf_rightConjugate h.isSylowOf_T₀ x₁
  have hR₂ := AschbacherTheorem3.isSylowOf_rightConjugate h.isSylowOf_T₀ x₂
  by_cases hu : x₁⁻¹ * x₂ ∈ normalizer (rightConjugate K x₁ : Set G)
  · exfalso
    apply hne
    have hK : rightConjugate K x₂ = rightConjugate K x₁ := by
      rw [show x₂ = x₁ * (x₁⁻¹ * x₂) by group, ← rightConjugate_mul,
        (rightConjugate_eq_self_iff _ _).mpr hu]
    rw [hK] at hR₂
    have hX : IsPGroup 2 (V ⊓ rightConjugate K x₁ : Subgroup G) := hV.to_le inf_le_left
    have e₁ := hR₁.eq_of_le (le_inf h₁ hR₁.le) inf_le_right hX
    have e₂ := hR₂.eq_of_le (le_inf h₂ hR₂.le) inf_le_right hX
    rw [← e₁, e₂]
  · have hle : rightConjugate T₀ x₂ ≤
        rightConjugate (rightConjugate K x₁) (x₁⁻¹ * x₂) := by
      rw [rightConjugate_mul, mul_inv_cancel_left]
      exact hR₂.le
    have h1 := two_subgroup_inf_conjugate_eq_bot _ _ hK1te (hR₂.isPGroup) _ hu hle
    rw [eq_bot_iff, ← h1]
    exact le_inf inf_le_right (inf_le_left.trans hR₁.le)

structure Facts (L T : Subgroup G) (q : ℕ) : Prop where
  four_le : 4 ≤ q
  oddCenter : Odd (Nat.card (center L))
  borel : ∃ k, fusionBenderBorel (rankTwoQuot L) q k
  sq_mem : ∀ x ∈ T ⊓ L, x ^ 2 ∈ gmsA L T
  weakClosure : ∀ z : G, rightConjugate (gmsW L T) z ≤ T →
    rightConjugate (gmsV L T) z = gmsV L T

namespace Facts

variable {q : ℕ}

theorem sylow (hX : Facts L T q) (h : Sec3 G L T) :
    Nat.card (gmsA L T) = q ∧ (∀ a ∈ gmsA L T, a ^ 2 = 1) ∧
      (∀ x ∈ T ⊓ L, x ^ 2 = 1 → x ∈ gmsA L T) := by
  obtain ⟨k, hB⟩ := hX.borel
  have hq := hX.four_le
  obtain ⟨-, hA₁, hsq, hinv⟩ := sylow_of_benderBorel hX.oddCenter (by omega) hB h.isSylowOf_T₁
  exact ⟨hA₁, hsq, hinv⟩

theorem vFacts (hX : Facts L T q)
    (h : Sec3 G L T) (hF : Foundation) :
    Nat.card (gmsV L T) = q * Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) ∧
    IsElemAbelian 2 (gmsV L T) ∧ gmsV L T ≤ gmsW L T ∧
    gmsV L T ≤ centralizer (gmsW L T : Set G) ∧
    (∀ x ∈ gmsW L T, x ^ 2 = 1 → x ∈ gmsV L T) := by
  obtain ⟨k, hB⟩ := hX.borel
  have hq := hX.four_le
  exact h.vFacts hF hX.oddCenter (by omega) hB

theorem exists_mem_normalizer
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) {x : G}
    (hx : rightConjugate (T ⊓ centralizer (L : Set G)) x ≤ gmsV L T) :
    ∃ z ∈ normalizer (gmsV L T : Set G),
      rightConjugate (rightConjugate (T ⊓ centralizer (L : Set G)) x) z =
        T ⊓ centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hVC, -⟩ := hX.vFacts h hF
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀def
  set M := normalizer (L : Set G) with hMdef
  set Q := rightConjugate T₀ x with hQdef
  have hWQ : gmsW L T ≤ centralizer (Q : Set G) :=
    le_centralizer_iff.mp (hx.trans hVC)
  have hQx : rightConjugate Q x⁻¹ = T₀ := by
    rw [hQdef, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hW' : rightConjugate (gmsW L T) x⁻¹ ≤ centralizer (T₀ : Set G) := by
    rw [← hQx, AS76b.centralizer_rightConjugate]
    exact map_mono hWQ
  have hNT₀ : normalizer (T₀ : Set G) ≤ M := by
    have h1 := AS76b.Lemma36.normalizer_le h.hyp.hyp31 h.isSylowOf_T₀ 1
    rwa [rightConjugate_one, rightConjugate_one] at h1
  set C := M ⊓ centralizer (T₀ : Set G) with hCdef
  have hTN₀ : T ≤ normalizer (T₀ : Set G) := le_normalizer_of_conj_mem fun t ht p hp =>
    h.conj_mem_T₀ ht hp
  have hTsyl : IsSylowOf 2 (T ⊓ C) C := by
    have h1 : IsSylowOf 2 T (M ⊓ normalizer (T₀ : Set G)) :=
      h.sylow.of_le (le_inf h.sylow.le hTN₀) inf_le_left
    exact h1.inf_of_le_normalizer (N := C)
      (inf_le_inf_left M (Subgroup.centralizer_le_normalizer _))
      (fun y hy => mem_normalizer_inf (le_normalizer (mem_inf.mp hy).1)
        (AS76b.Lemma22.normalizer_le_normalizer_centralizer T₀ (mem_inf.mp hy).2))
  have hW'C : rightConjugate (gmsW L T) x⁻¹ ≤ C :=
    le_inf (hW'.trans ((Subgroup.centralizer_le_normalizer _).trans hNT₀)) hW'
  have hW'2 : IsPGroup 2 (rightConjugate (gmsW L T) x⁻¹) :=
    (h.sylow.isPGroup.to_le (sup_le inf_le_left inf_le_left)).map _
  obtain ⟨S, hS, hW'S⟩ := AS76b.exists_isSylowOf_le hW'C hW'2
  obtain ⟨c, hc, hcS⟩ := IsSylowOf.exists_map_conj hS hTsyl
  set z := x⁻¹ * c⁻¹ with hzdef
  have hWz : rightConjugate (gmsW L T) z ≤ T := by
    have h1 : rightConjugate (gmsW L T) z = (rightConjugate (gmsW L T) x⁻¹).map
        (MulAut.conj c).toMonoidHom := by
      rw [Sec3.map_conj_rightConjugate, hzdef]
    rw [h1]
    exact (map_mono hW'S).trans (hcS ▸ inf_le_left)
  have hVz := hX.weakClosure z hWz
  refine ⟨z, (rightConjugate_eq_self_iff _ z).mp hVz, ?_⟩
  rw [hQdef, rightConjugate_mul, hzdef, ← mul_assoc, mul_inv_cancel, one_mul]
  have hcc : c⁻¹ ∈ centralizer (T₀ : Set G) := inv_mem (mem_inf.mp hc).2
  exact (rightConjugate_eq_self_iff T₀ c⁻¹).mpr (Subgroup.centralizer_le_normalizer _ hcc)

theorem sec3W_le_centralizer
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) {h₀ : G}
    (hD : rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ≤
      T ⊓ (L ⊔ centralizer (L : Set G)))
    (hDK : rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ⊓ centralizer (L : Set G) = ⊥) :
    AS76b.sec3W (T ⊓ centralizer (L : Set G)) (rightConjugate (T ⊓ centralizer (L : Set G)) h₀) ≤
      centralizer (gmsV L T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hVel, hVW, -, hΩ⟩ := hX.vFacts h hF
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  set T₁ := T ⊓ L with hT₁def
  set D := rightConjugate T₀ h₀ with hDdef
  have hZ := hX.oddCenter
  obtain ⟨k, hB⟩ := hX.borel
  have hT₁syl : IsSylowOf 2 T₁ L := h.isSylowOf_T₁
  have hT₀el : IsElemAbelian 2 T₀ := h.isElemAbelian_T₀ hF
  have hNT₀ : normalizer (T₀ : Set G) ≤ normalizer (L : Set G) := by
    have h1 := AS76b.Lemma36.normalizer_le h.hyp.hyp31 h.isSylowOf_T₀ 1
    rwa [rightConjugate_one, rightConjugate_one] at h1
  have hDel : IsElemAbelian 2 D := isElemAbelian_map _ hT₀el
  have hDV : D ≤ gmsV L T := fun d hd => hΩ d (by rw [gmsW, ← h.inf_sup_eq]; exact hD hd)
    (hDel.2 d hd)
  have hD1 : D ≠ ⊥ := by
    intro hb
    apply h.T₀_ne_bot
    have h1 := rightConjugate_card T₀ h₀
    rw [← hDdef, hb, card_bot] at h1
    exact (card_eq_one.mp h1.symm)
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hD1
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  have hA₁N : gmsA L T ≤ normalizer (T₀ : Set G) := fun a ha =>
    (le_centralizer_iff.mp (show T₀ ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) from
      fun t ht => mem_centralizer_iff.mpr fun x hx =>
        mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2)).trans
      (Subgroup.centralizer_le_normalizer _) (mem_inf.mp ha).1
  obtain ⟨a₀, ha₀, t₀, ht₀, hat⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N (hDV hdD)
  have ha₀1 : a₀ ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hat
    have hdK : d ∈ D ⊓ K := mem_inf.mpr ⟨hdD, hat ▸ (mem_inf.mp ht₀).2⟩
    rw [hDK, mem_bot] at hdK
    exact hd1' hdK
  have ha₀T₁ : a₀ ∈ T₁ := (mem_inf.mp ha₀).1
  refine iSup₂_le fun y hy => ?_
  intro q hq
  have hqC := hy hq
  have hqt : ∀ t ∈ T₀, t * q = q * t := fun t ht =>
    mem_centralizer_iff.mp hqC t (mem_sup_left ht)
  have hqd : d * q = q * d := mem_centralizer_iff.mp hqC d (mem_sup_right hdD)
  have hqa : a₀ * q = q * a₀ := by
    have ht₀q := hqt t₀ ht₀
    have ha₀d : a₀ = d * t₀⁻¹ := by rw [← hat]; group
    rw [ha₀d]
    calc d * t₀⁻¹ * q = d * (t₀⁻¹ * q) := by group
      _ = d * (q * t₀⁻¹) := by
          rw [show t₀⁻¹ * q = q * t₀⁻¹ by
            calc t₀⁻¹ * q = t₀⁻¹ * (q * t₀) * t₀⁻¹ := by group
              _ = t₀⁻¹ * (t₀ * q) * t₀⁻¹ := by rw [ht₀q]
              _ = q * t₀⁻¹ := by group]
      _ = (d * q) * t₀⁻¹ := by group
      _ = q * (d * t₀⁻¹) := by rw [hqd]; group
  have hqM : q ∈ normalizer (L : Set G) :=
    hNT₀ (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht => hqt t ht))
  have hq2 : q * q = 1 := by
    rw [← sq]
    exact (isElemAbelian_map _ hT₀el).2 q hq
  have hqT₁ : rightConjugate T₁ q = T₁ := by
    have hP₂ : IsSylowOf 2 (rightConjugate T₁ q) L := by
      have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hT₁syl q
      rwa [(rightConjugate_eq_self_iff L q).mpr hqM] at h1
    have ha₀P₂ : a₀ ∈ rightConjugate T₁ q := by
      rw [mem_rightConjugate_iff, ← hqa, mul_inv_cancel_right]
      exact ha₀T₁
    exact (eq_of_mem_of_mem hZ hT₁syl hP₂ hB ha₀T₁ ha₀P₂ ha₀1).symm
  have hqN : q ∈ normalizer (T₁ : Set G) := (rightConjugate_eq_self_iff T₁ q).mp hqT₁
  have hqLK : q ∈ L ⊔ K := AS76b.conj_le_sup_centralizer hF.lemma33Two h.hyp.hyp31
    h.isSylowOf_T₀ ⟨y, rfl⟩ (hy.trans (Subgroup.centralizer_le fun r hr => mem_sup_left hr)) hq
  have hqA : ∀ a ∈ gmsA L T, q * a = a * q := by
    have hKL : K ≤ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _
    rw [sup_comm] at hqLK
    obtain ⟨k, hk, l, hl, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hKL hqLK
    have hkN : k ∈ normalizer (T₁ : Set G) := mem_normalizer_of_conj_mem
      (fun p hp => by
        have hc : p * k = k * p := mem_centralizer_iff.mp hk p (mem_inf.mp hp).2
        rw [← hc, mul_inv_cancel_right]
        exact hp)
      (fun p hp => by
        have hc : p * k = k * p := mem_centralizer_iff.mp hk p (mem_inf.mp hp).2
        rw [show k⁻¹ * p * k = p by rw [mul_assoc, hc, inv_mul_cancel_left]]
        exact hp)
    have hlN : l ∈ normalizer (T₁ : Set G) := by
      have := mul_mem (inv_mem hkN) hqN
      rwa [inv_mul_cancel_left] at this
    have hkl : k * l = l * k := (mem_centralizer_iff.mp hk l hl).symm
    have hl2 : (⟨l, hl⟩ : L) ^ 2 ∈ center L := by
      rw [mem_center_iff]
      intro m
      apply Subtype.ext
      have h1 : l ^ 2 = (k ^ 2)⁻¹ := by
        have h2 : (k * l) * (k * l) = 1 := hq2
        rw [show (k * l) * (k * l) = k ^ 2 * l ^ 2 by
          rw [sq, sq]
          calc k * l * (k * l) = k * (l * k) * l := by group
            _ = k * (k * l) * l := by rw [hkl]
            _ = k * k * (l * l) := by group] at h2
        exact eq_inv_of_mul_eq_one_right h2
      show (m : G) * (l ^ 2) = l ^ 2 * m
      rw [h1]
      have hk2 : (k ^ 2)⁻¹ ∈ K := inv_mem (pow_mem hk 2)
      exact mem_centralizer_iff.mp hk2 m m.2
    have hπl : QuotientGroup.mk' (center L) ⟨l, hl⟩ ^ 2 ^ 1 = 1 := by
      rw [pow_one, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hl2
    have hla := commute_of_normalizer hT₁syl hl hlN hπl
    intro a ha
    have hka : k * a = a * k :=
      (mem_centralizer_iff.mp hk a ((mem_inf.mp (mem_inf.mp ha).1).2)).symm
    calc k * l * a = k * (l * a) := by group
      _ = k * (a * l) := by rw [hla a ha]
      _ = (k * a) * l := by group
      _ = (a * k) * l := by rw [hka]
      _ = a * (k * l) := by group
  refine mem_centralizer_iff.mpr fun v hv => ?_
  obtain ⟨a, ha, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N hv
  calc a * t * q = a * (t * q) := by group
    _ = a * (q * t) := by rw [hqt t ht]
    _ = (a * q) * t := by group
    _ = (q * a) * t := by rw [hqA a ha]
    _ = q * (a * t) := by group

theorem exists_mul_mem
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) {h₀ : G}
    (hD : rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ≤
      T ⊓ (L ⊔ centralizer (L : Set G)))
    (hDK : rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ⊓ centralizer (L : Set G) = ⊥) :
    rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ≤ gmsV L T ∧
      ∃ a₀ ∈ gmsA L T, a₀ ≠ 1 ∧ ∃ t₀ ∈ T ⊓ centralizer (L : Set G),
        a₀ * t₀ ∈ rightConjugate (T ⊓ centralizer (L : Set G)) h₀ := by
  obtain ⟨-, -, -, -, hΩ⟩ := hX.vFacts h hF
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  set D := rightConjugate T₀ h₀ with hDdef
  have hT₀el : IsElemAbelian 2 T₀ := h.isElemAbelian_T₀ hF
  have hDel : IsElemAbelian 2 D := isElemAbelian_map _ hT₀el
  have hDV : D ≤ gmsV L T := fun d hd => hΩ d (by rw [gmsW, ← h.inf_sup_eq]; exact hD hd)
    (hDel.2 d hd)
  have hD1 : D ≠ ⊥ := by
    intro hb
    apply h.T₀_ne_bot
    have h1 := rightConjugate_card T₀ h₀
    rw [← hDdef, hb, card_bot] at h1
    exact (card_eq_one.mp h1.symm)
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hD1
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  have hA₁N : gmsA L T ≤ normalizer (T₀ : Set G) := fun a ha =>
    (le_centralizer_iff.mp (show T₀ ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) from
      fun t ht => mem_centralizer_iff.mpr fun x hx =>
        mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2)).trans
      (Subgroup.centralizer_le_normalizer _) (mem_inf.mp ha).1
  obtain ⟨a₀, ha₀, t₀, ht₀, hat⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N (hDV hdD)
  refine ⟨hDV, a₀, ha₀, fun h1 => ?_, t₀, ht₀, hat ▸ hdD⟩
  rw [h1, one_mul] at hat
  have hdK : d ∈ D ⊓ K := mem_inf.mpr ⟨hdD, hat ▸ (mem_inf.mp ht₀).2⟩
  rw [hDK, mem_bot] at hdK
  exact hd1' hdK

theorem sec3V_eq
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) {h₀ : G}
    (hD : rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ≤
      T ⊓ (L ⊔ centralizer (L : Set G)))
    (hDK : rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ⊓ centralizer (L : Set G) = ⊥) :
    AS76b.sec3V (T ⊓ centralizer (L : Set G)) (rightConjugate (T ⊓ centralizer (L : Set G)) h₀) =
      gmsV L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  obtain ⟨hDV, a₀, ha₀, ha₀1, t₀, ht₀, hat⟩ := hX.exists_mul_mem h hF hD hDK
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  set T₁ := T ⊓ L with hT₁def
  set D := rightConjugate T₀ h₀ with hDdef
  have hZ := hX.oddCenter
  obtain ⟨k, hB⟩ := hX.borel
  have hT₁syl : IsSylowOf 2 T₁ L := h.isSylowOf_T₁
  obtain ⟨-, -, hinvA⟩ := hX.sylow h
  have hW := hX.sec3W_le_centralizer h hF hD hDK
  have hVW' : gmsV L T ≤ centralizer (AS76b.sec3W T₀ D : Set G) := le_centralizer_iff.mp hW
  have hRT := AS76b.le_sec3V_of (R := T₀) (T := D) ⟨h₀, rfl⟩
  obtain ⟨y, hy, -, htrans, -⟩ := exists_torus hZ hT₁syl hB
  have hA₁S : gmsA L T ≤ AS76b.sec3V T₀ D := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact one_mem _
    obtain ⟨m, hm⟩ := htrans a₀ ha₀ a ha ha₀1 ha1
    set g := y ^ m with hgdef
    have hg : g ∈ L ⊓ normalizer (T₁ : Set G) := pow_mem hy m
    have hDg : rightConjugate D g ≤ gmsV L T := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have h1 := inf_normalizer_le_normalizer (inv_mem hg)
      have h2 := (mem_normalizer_iff.mp h1 _).mp (hDV hx)
      simpa [mul_assoc] using h2
    have hDgS : rightConjugate D g ≤ AS76b.sec3V T₀ D := by
      have h1 : rightConjugate D g = rightConjugate T₀ (h₀ * g) := by
        rw [hDdef, rightConjugate_mul]
      rw [h1]
      exact AS76b.le_sec3V (h1 ▸ (hDg.trans hVW'))
    have hmem : g⁻¹ * (a₀ * t₀) * g ∈ rightConjugate D g := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hat
    have hgt : g⁻¹ * t₀ * g = t₀ := by
      rw [mul_assoc, ← mem_centralizer_iff.mp (mem_inf.mp ht₀).2 g (mem_inf.mp hg).1,
        inv_mul_cancel_left]
    have heq : g⁻¹ * (a₀ * t₀) * g = a * t₀ := by
      rw [show g⁻¹ * (a₀ * t₀) * g = (g⁻¹ * a₀ * g) * (g⁻¹ * t₀ * g) by group, hgt, hm]
    have h2 := hDgS hmem
    rw [heq] at h2
    have h3 : t₀ ∈ AS76b.sec3V T₀ D := hRT (mem_sup_left ht₀)
    have h4 := mul_mem h2 (inv_mem h3)
    simpa using h4
  apply le_antisymm
  ·
    obtain ⟨hS, hST, -⟩ := AS76b.lemma35 hF.lemma32 hF.lemma33Two h.hyp.hyp31 h.isSylowOf_T₀
      (AschbacherTheorem3.isSylowOf_rightConjugate h.isSylowOf_T₀ h₀)
      (fun d hd => mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (hVel.1.is_comm.comm ⟨t, mem_sup_right ht⟩ ⟨d, hDV hd⟩))
    have hSL : AS76b.sec3V T₀ D ⊓ L ≤ gmsA L T := by
      intro x hx
      obtain ⟨hxS, hxL⟩ := mem_inf.mp hx
      have hxa : x * a₀ = a₀ * x :=
        congrArg Subtype.val (hS.1.is_comm.comm ⟨x, hxS⟩ ⟨a₀, hA₁S ha₀⟩)
      have hxN := mem_normalizer_of_commute hZ hT₁syl hB ha₀ ha₀1 hxL hxa
      have hx2 : x ^ 2 = 1 := hS.2 x hxS
      have hπ : QuotientGroup.mk' (center L) ⟨x, hxL⟩ ^ 2 ^ 1 = 1 := by
        rw [pow_one, ← map_pow]
        have : (⟨x, hxL⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
        rw [this, map_one]
      obtain ⟨R, hR⟩ := exists_sylow_range hT₁syl
      have hxT₁ := mem_of_mk_mem hZ hT₁syl hR hxL (mk_mem_of_normalizer hT₁syl hR hxL hxN hπ)
        (n := 1) (by rw [pow_one]; exact hx2)
      exact hinvA x hxT₁ hx2
    rw [hST]
    exact sup_le le_sup_right (hSL.trans le_sup_left)
  · exact sup_le hA₁S (le_sup_left.trans hRT)

theorem exists_torus_conj (hX : Facts L T q) (h : Sec3 G L T) :
    ∃ y ∈ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G), Odd (orderOf y) ∧
      (∀ a ∈ gmsA L T, ∀ b ∈ gmsA L T, a ≠ 1 → b ≠ 1 → ∃ m : ℕ, (y ^ m)⁻¹ * a * y ^ m = b) ∧
      ∀ w ∈ normalizer (L : Set G) ⊓ normalizer (gmsV L T : Set G),
        w⁻¹ * y * w ∈ zpowers y ⊔ centralizer (gmsV L T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  set T₁ := T ⊓ L with hT₁def
  set V := gmsV L T with hVdef
  have hZ := hX.oddCenter
  obtain ⟨k, hB⟩ := hX.borel
  have hT₁syl : IsSylowOf 2 T₁ L := h.isSylowOf_T₁
  obtain ⟨hA₁card, -, -⟩ := hX.sylow h
  have hq := hX.four_le
  have hVL := h.gmsV_inf_eq hZ
  obtain ⟨y, hy, hyodd, htrans, hact⟩ := exists_torus hZ hT₁syl hB
  obtain ⟨hyL, hyN⟩ := mem_inf.mp hy
  obtain ⟨a₁, ha₁, ha₁1⟩ : ∃ a ∈ gmsA L T, a ≠ 1 := by
    have h1 : 1 < Nat.card (gmsA L T) := by
      rw [hA₁card]
      omega
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
    exact ⟨a, ha, fun h1 => ha1 (Subtype.ext h1)⟩
  have hLT₀ : ∀ g ∈ L, ∀ t ∈ T₀, g * t = t * g := fun g hg t ht =>
    mem_centralizer_iff.mp (mem_inf.mp ht).2 g hg
  have hA₁N : gmsA L T ≤ normalizer (T₀ : Set G) := fun a ha =>
    (le_centralizer_iff.mp (show T₀ ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) from
      fun t ht => mem_centralizer_iff.mpr fun x hx =>
        mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2)).trans
      (Subgroup.centralizer_le_normalizer _) (mem_inf.mp ha).1
  have hyV : y ∈ normalizer (V : Set G) := inf_normalizer_le_normalizer hy
  have hcV : ∀ g ∈ L, (∀ a ∈ gmsA L T, g * a = a * g) → g ∈ centralizer (V : Set G) := by
    intro g hg hga
    refine mem_centralizer_iff.mpr fun v hv => ?_
    obtain ⟨a, ha, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N hv
    calc a * t * g = a * (g * t) := by rw [mul_assoc, ← hLT₀ g hg t ht]
      _ = (g * a) * t := by rw [← mul_assoc, hga a ha]
      _ = g * (a * t) := by group
  have hbase : ∀ w ∈ normalizer (L : Set G) ⊓ normalizer (V : Set G),
      w⁻¹ * y * w ∈ zpowers y ⊔ centralizer (V : Set G) := by
    intro w hw
    obtain ⟨hwL, hwV⟩ := mem_inf.mp hw
    have hwA₁ : w⁻¹ * a₁ * w ∈ gmsA L T := by
      rw [← hVL]
      refine mem_inf.mpr ⟨?_, ?_⟩
      · simpa using (mem_normalizer_iff.mp (inv_mem hwV) a₁).mp (mem_sup_left ha₁)
      · simpa using (mem_normalizer_iff.mp (inv_mem hwL) a₁).mp (mem_inf.mp (mem_inf.mp ha₁).1).2
    have hP₂ : IsSylowOf 2 (rightConjugate T₁ w) L := by
      have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hT₁syl w
      rwa [(rightConjugate_eq_self_iff L w).mpr hwL] at h1
    have hmem : w⁻¹ * a₁ * w ∈ rightConjugate T₁ w := by
      rw [mem_rightConjugate_iff, show w * (w⁻¹ * a₁ * w) * w⁻¹ = a₁ by group]
      exact (mem_inf.mp ha₁).1
    have hwa1 : w⁻¹ * a₁ * w ≠ 1 := fun h1 => ha₁1 (by
      have := congrArg (fun u => w * u * w⁻¹) h1
      simpa [mul_assoc] using this)
    have hT₁w := eq_of_mem_of_mem hZ hT₁syl hP₂ hB (mem_inf.mp hwA₁).1 hmem hwa1
    have hwT₁ : w ∈ normalizer (T₁ : Set G) := (rightConjugate_eq_self_iff T₁ w).mp hT₁w.symm
    set n := w⁻¹ * y * w with hn
    have hnL : n ∈ L := by
      simpa using (mem_normalizer_iff.mp (inv_mem hwL) y).mp hyL
    have hnN : n ∈ normalizer (T₁ : Set G) :=
      mul_mem (mul_mem (inv_mem hwT₁) hyN) hwT₁
    obtain ⟨k, hk⟩ := hact n (mem_inf.mpr ⟨hnL, hnN⟩)
    have hcent : (y ^ k)⁻¹ * n ∈ centralizer (V : Set G) := by
      refine hcV _ (mul_mem (inv_mem (pow_mem hyL k)) hnL) fun a ha => ?_
      have h1 := hk a ha
      calc (y ^ k)⁻¹ * n * a = (y ^ k)⁻¹ * (n * a * n⁻¹) * n := by group
        _ = (y ^ k)⁻¹ * (y ^ k * a * (y ^ k)⁻¹) * n := by rw [h1]
        _ = a * ((y ^ k)⁻¹ * n) := by group
    have h2 : n = y ^ k * ((y ^ k)⁻¹ * n) := by group
    rw [h2]
    exact mul_mem (mem_sup_left (pow_mem (mem_zpowers y) k)) (mem_sup_right hcent)
  exact ⟨y, hy, hyodd, htrans, hbase⟩

theorem star36
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) :
    AS76b.Star36 L (T ⊓ centralizer (L : Set G)) (gmsV L T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  set V := gmsV L T with hVdef
  have hVL := h.gmsV_inf_eq hX.oddCenter
  have htight := AS76b.tightlyEmbedded_centralizer h.hyp.standard
  have hNK := AS76b.normalizer_centralizer_eq h.hyp.standard
  obtain ⟨y, hy, hyodd, htrans, hbase⟩ := hX.exists_torus_conj h
  have hyL : y ∈ L := (mem_inf.mp hy).1
  have hyV : y ∈ normalizer (V : Set G) := inf_normalizer_le_normalizer hy
  intro x hx
  obtain ⟨z, hzV, hzQ⟩ := hX.exists_mem_normalizer h hF hx
  rw [← hKdef, ← hT₀def] at hzQ
  have hxz : x * z ∈ normalizer (L : Set G) := by
    rw [← hNK]
    by_contra hn
    have hodd := htight.2 (x * z) hn
    rw [rightConjugate_mul] at hzQ
    have hle : T₀ ≤ K ⊓ rightConjugate K (x * z) := by
      intro t ht
      refine mem_inf.mpr ⟨(mem_inf.mp ht).2, ?_⟩
      rw [← hzQ] at ht
      exact map_mono inf_le_right ht
    exact h.T₀_ne_bot (two_subgroup_of_odd_eq_bot T₀ _ h.isSylowOf_T₀.isPGroup hodd hle)
  have hLx : rightConjugate L x = rightConjugate L z⁻¹ := by
    have h1 : rightConjugate L (x * z) = L := (rightConjugate_eq_self_iff L _).mpr hxz
    calc rightConjugate L x = rightConjugate (rightConjugate L (x * z)) z⁻¹ := by
          rw [rightConjugate_mul, mul_inv_cancel_right]
      _ = rightConjugate L z⁻¹ := by rw [h1]
  rw [hLx]
  set y' := z * y * z⁻¹ with hy'
  have hy'L : y' ∈ rightConjugate L z⁻¹ := by
    rw [mem_rightConjugate_iff, hy']
    simpa [mul_assoc] using hyL
  have hy'V : y' ∈ normalizer (V : Set G) := mul_mem (mul_mem hzV hyV) (inv_mem hzV)
  refine ⟨y', mem_inf.mpr ⟨hy'L, hy'V⟩, ?_, ?_, ?_⟩
  · rw [hy', show z * y * z⁻¹ = (MulAut.conj z).toMonoidHom y from rfl,
      orderOf_injective _ (MulAut.conj z).injective]
    exact hyodd
  · intro b hb c hc hb1 hc1
    have hconjA : ∀ u ∈ V ⊓ rightConjugate L z⁻¹, z⁻¹ * u * z ∈ gmsA L T := by
      intro u hu
      rw [← hVL]
      refine mem_inf.mpr ⟨?_, ?_⟩
      · simpa using (mem_normalizer_iff.mp (inv_mem hzV) u).mp (mem_inf.mp hu).1
      · have := (mem_rightConjugate_iff L z⁻¹ u).mp (mem_inf.mp hu).2
        simpa using this
    have hne : ∀ u, u ≠ 1 → z⁻¹ * u * z ≠ 1 := fun u hu h1 => hu (by
      have := congrArg (fun v => z * v * z⁻¹) h1
      simpa [mul_assoc] using this)
    obtain ⟨m, hm⟩ := htrans _ (hconjA b hb) _ (hconjA c hc) (hne b hb1) (hne c hc1)
    refine ⟨m, ?_⟩
    rw [hy', conj_pow]
    calc (z * y ^ m * z⁻¹)⁻¹ * b * (z * y ^ m * z⁻¹)
        = z * ((y ^ m)⁻¹ * (z⁻¹ * b * z) * y ^ m) * z⁻¹ := by group
      _ = z * (z⁻¹ * c * z) * z⁻¹ := by rw [hm]
      _ = c := by group
  · intro w hw
    obtain ⟨hwL, hwV⟩ := mem_inf.mp hw
    have hw' : z⁻¹ * w * z ∈ normalizer (L : Set G) ⊓ normalizer (V : Set G) := by
      refine mem_inf.mpr ⟨?_, mul_mem (mul_mem (inv_mem hzV) hwV) hzV⟩
      rw [← rightConjugate_eq_self_iff] at hwL ⊢
      calc rightConjugate L (z⁻¹ * w * z)
          = rightConjugate (rightConjugate (rightConjugate L z⁻¹) w) z := by
            rw [rightConjugate_mul, rightConjugate_mul, mul_assoc]
        _ = L := by rw [hwL, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
    have h1 := hbase _ hw'
    have hzpow : zpowers y ≤ normalizer (centralizer (V : Set G) : Set G) :=
      zpowers_le.mpr (AS76b.Lemma22.normalizer_le_normalizer_centralizer V hyV)
    obtain ⟨u, hu, c, hc, huc⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hzpow h1
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hu
    have hzc : z * c * z⁻¹ ∈ centralizer (V : Set G) :=
      (mem_normalizer_iff.mp (AS76b.Lemma22.normalizer_le_normalizer_centralizer V hzV) c).mp hc
    have heq : w⁻¹ * y' * w = (z * y * z⁻¹) ^ j * (z * c * z⁻¹) := by
      rw [show (z * y * z⁻¹) ^ j = z * y ^ j * z⁻¹ by
        rw [show z * y * z⁻¹ = (MulAut.conj z) y from rfl, ← map_zpow]; rfl]
      calc w⁻¹ * y' * w = z * ((z⁻¹ * w * z)⁻¹ * y * (z⁻¹ * w * z)) * z⁻¹ := by
            rw [hy']; group
        _ = z * (y ^ j * c) * z⁻¹ := by rw [huc]
        _ = z * y ^ j * z⁻¹ * (z * c * z⁻¹) := by group
    rw [heq]
    exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers _) j)) (mem_sup_right hzc)

theorem lemma36
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) {h₀ : G}
    (hh₀M : h₀ ∉ normalizer (L : Set G))
    (hD : rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ≤
      T ⊓ (L ⊔ centralizer (L : Set G)))
    (hDK : rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ⊓ centralizer (L : Set G) = ⊥) :
    (⁅L ⊓ normalizer (gmsV L T : Set G), gmsV L T⁆ =
        rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ∧
      ⁅rightConjugate L h₀ ⊓ normalizer (gmsV L T : Set G), gmsV L T⁆ =
        T ⊓ centralizer (L : Set G) ∧
      ∀ x : G, rightConjugate (T ⊓ centralizer (L : Set G)) x ≤ gmsV L T →
        rightConjugate (T ⊓ centralizer (L : Set G)) x = T ⊓ centralizer (L : Set G) ∨
          rightConjugate (T ⊓ centralizer (L : Set G)) x =
            rightConjugate (T ⊓ centralizer (L : Set G)) h₀) ∨
    (⁅L ⊓ normalizer (gmsV L T : Set G), gmsV L T⁆ =
        ⁅rightConjugate L h₀ ⊓ normalizer (gmsV L T : Set G), gmsV L T⁆ ∧
      (∀ v ∈ gmsV L T, v ∉ ⁅L ⊓ normalizer (gmsV L T : Set G), gmsV L T⁆ ↔
        ∃ x : G, rightConjugate (T ⊓ centralizer (L : Set G)) x ≤ gmsV L T ∧
          v ∈ rightConjugate (T ⊓ centralizer (L : Set G)) x ∧ v ≠ 1) ∧
      ∀ x₁ x₂ x₁' x₂' : G, rightConjugate (T ⊓ centralizer (L : Set G)) x₁ ≤ gmsV L T →
        rightConjugate (T ⊓ centralizer (L : Set G)) x₂ ≤ gmsV L T →
        rightConjugate (T ⊓ centralizer (L : Set G)) x₁' ≤ gmsV L T →
        rightConjugate (T ⊓ centralizer (L : Set G)) x₂' ≤ gmsV L T →
        rightConjugate (T ⊓ centralizer (L : Set G)) x₁ ≠
          rightConjugate (T ⊓ centralizer (L : Set G)) x₂ →
        rightConjugate (T ⊓ centralizer (L : Set G)) x₁' ≠
          rightConjugate (T ⊓ centralizer (L : Set G)) x₂' →
        ∃ n ∈ normalizer (gmsV L T : Set G),
          rightConjugate (rightConjugate (T ⊓ centralizer (L : Set G)) x₁) n =
            rightConjugate (T ⊓ centralizer (L : Set G)) x₁' ∧
          rightConjugate (rightConjugate (T ⊓ centralizer (L : Set G)) x₂) n =
            rightConjugate (T ⊓ centralizer (L : Set G)) x₂') := by
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  have hsec := hX.sec3V_eq h hF hD hDK
  obtain ⟨hDV, -⟩ := hX.exists_mul_mem h hF hD hDK
  have hDsyl : IsSylowOf 2 (rightConjugate (T ⊓ centralizer (L : Set G)) h₀)
      (rightConjugate (centralizer (L : Set G)) h₀) :=
    AschbacherTheorem3.isSylowOf_rightConjugate h.isSylowOf_T₀ h₀
  have hDC : rightConjugate (T ⊓ centralizer (L : Set G)) h₀ ≤
      centralizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := fun d hd =>
    mem_centralizer_iff.mpr fun t ht =>
      congrArg Subtype.val (hVel.1.is_comm.comm ⟨t, mem_sup_right ht⟩ ⟨d, hDV hd⟩)
  have h36 := AS76b.lemma36 hF.lemma32 hF.lemma33Two G L (T ⊓ centralizer (L : Set G))
    (rightConjugate (T ⊓ centralizer (L : Set G)) h₀) h₀ h.hyp.hyp31 h.isSylowOf_T₀ hh₀M
    hDsyl hDC (by rw [hsec]; exact hX.star36 h hF)
  rwa [hsec] at h36

theorem odd_card
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) (hTG : IsSylowOf 2 T ⊤) :
    Odd (Nat.card (gmsDelta L T)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  set V := gmsV L T with hVdef
  set N := normalizer (V : Set G) with hNdef
  set S := N ⊓ normalizer (T₀ : Set G) with hSdef
  have hT₀V : T₀ ≤ V := le_sup_right
  have hTT₀ : T ≤ normalizer (T₀ : Set G) := le_normalizer_of_conj_mem fun t ht p hp =>
    h.conj_mem_T₀ ht hp
  have hTV : T ≤ N := by
    apply le_normalizer_of_conj_mem
    intro t ht v hv
    have hA₁N : gmsA L T ≤ normalizer (T₀ : Set G) := fun a ha =>
      (le_centralizer_iff.mp (show T₀ ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) from
        fun t ht => mem_centralizer_iff.mpr fun x hx =>
          mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2)).trans
        (Subgroup.centralizer_le_normalizer _) (mem_inf.mp ha).1
    obtain ⟨a, ha, t', ht', rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N hv
    have htN := h.mem_normalizer_T₁ ht
    have hta : t * a * t⁻¹ ∈ gmsA L T := by
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp htN a).mp (mem_inf.mp ha).1,
        mem_centralizer_iff.mpr fun p hp => ?_⟩
      have hp' : t⁻¹ * p * t ∈ T ⊓ L := by
        simpa using (mem_normalizer_iff.mp (inv_mem htN) p).mp hp
      have h1 : t⁻¹ * p * t * a = a * (t⁻¹ * p * t) :=
        mem_centralizer_iff.mp (mem_inf.mp ha).2 _ hp'
      calc p * (t * a * t⁻¹) = t * (t⁻¹ * p * t * a) * t⁻¹ := by group
        _ = t * (a * (t⁻¹ * p * t)) * t⁻¹ := by rw [h1]
        _ = t * a * t⁻¹ * p := by group
    rw [show t * (a * t') * t⁻¹ = (t * a * t⁻¹) * (t * t' * t⁻¹) by group]
    exact mul_mem (mem_sup_left hta) (mem_sup_right (h.conj_mem_T₀ ht ht'))
  have hTS : T ≤ S := le_inf hTV hTT₀
  have hidx : ¬ 2 ∣ S.relIndex N := by
    have hTN : IsSylowOf 2 T N := hTG.of_le hTV le_top
    have h1 := (isSylowOf_iff.mp hTN).2.2
    have h2 := relIndex_mul_relIndex T S N hTS inf_le_left
    intro h3
    apply h1
    rw [← h2]
    exact h3.mul_left _
  set S' := S.subgroupOf N with hS'def
  have hconjV : ∀ n ∈ N, rightConjugate T₀ n⁻¹ ≤ V := fun n hn =>
    (map_mono hT₀V).trans (le_of_eq ((rightConjugate_eq_self_iff V n⁻¹).mpr (inv_mem hn)))
  let Φ : N ⧸ S' → gmsDelta L T :=
    Quotient.lift (fun n => ⟨rightConjugate T₀ (n : G)⁻¹, ⟨_, rfl⟩, hconjV n n.2⟩)
      (fun a b hab => by
        have hab₀ : a⁻¹ * b ∈ S' := QuotientGroup.leftRel_apply.mp hab
        have hab' : (a : G)⁻¹ * b ∈ S := hab₀
        have hN : ((a : G)⁻¹ * b)⁻¹ ∈ normalizer (T₀ : Set G) := inv_mem (mem_inf.mp hab').2
        apply Subtype.ext
        show rightConjugate T₀ (a : G)⁻¹ = rightConjugate T₀ (b : G)⁻¹
        rw [show ((b : G))⁻¹ = ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ by group, ← rightConjugate_mul,
          (rightConjugate_eq_self_iff T₀ _).mpr hN])
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun u v huv => ?_, fun Q => ?_⟩
    · induction u using QuotientGroup.induction_on with | H a => ?_
      induction v using QuotientGroup.induction_on with | H b => ?_
      apply QuotientGroup.eq.mpr
      have h1 : rightConjugate T₀ (a : G)⁻¹ = rightConjugate T₀ (b : G)⁻¹ :=
        congrArg Subtype.val huv
      have h2 : rightConjugate T₀ ((a : G)⁻¹ * b) = T₀ := by
        have := congrArg (fun X => rightConjugate X (b : G)) h1
        simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at this
        exact this
      exact mem_inf.mpr ⟨(a⁻¹ * b).2, (rightConjugate_eq_self_iff T₀ _).mp h2⟩
    · obtain ⟨⟨x, hx⟩, hQV⟩ := Q.2
      obtain ⟨z, hzN, hzQ⟩ := hX.exists_mem_normalizer h hF (hx ▸ hQV)
      rw [← hKdef, ← hT₀def] at hzQ
      refine ⟨QuotientGroup.mk (⟨z, hzN⟩ : N), Subtype.ext ?_⟩
      show rightConjugate T₀ z⁻¹ = Q.1
      calc rightConjugate T₀ z⁻¹ = rightConjugate (rightConjugate (rightConjugate T₀ x) z) z⁻¹ := by
            rw [hzQ]
        _ = rightConjugate T₀ x := by
            rw [rightConjugate_mul, rightConjugate_mul, mul_inv_cancel, mul_one]
        _ = Q.1 := hx
  have hcard : Nat.card (gmsDelta L T) = S.relIndex N := by
    rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ)]
    rfl
  rw [hcard]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx)

theorem not_isSylowOf_top
    (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) : ¬ IsSylowOf 2 T ⊤ := by
  intro hTG
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₀, hh₀M, hD, hDK⟩ := h.exists_conj hF
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  obtain ⟨hDV, -⟩ := hX.exists_mul_mem h hF hD hDK
  have h36 := hX.lemma36 h hF hh₀M hD hDK
  have hodd := hX.odd_card h hF hTG
  apply Nat.not_even_iff_odd.mpr hodd
  have hT₀1 : T ⊓ centralizer (L : Set G) ≠ ⊥ := h.T₀_ne_bot
  have hT₀V : T ⊓ centralizer (L : Set G) ≤ gmsV L T := le_sup_right
  have hV2 : IsPGroup 2 (gmsV L T) := fun v => ⟨1, Subtype.ext (by simpa using hVel.2 v v.2)⟩
  rcases h36 with ⟨-, -, h3⟩ | ⟨-, hcov, -⟩
  ·
    have hne : T ⊓ centralizer (L : Set G) ≠ rightConjugate (T ⊓ centralizer (L : Set G)) h₀ := by
      intro hTD
      apply hT₀1
      have h1 : (T ⊓ centralizer (L : Set G)) ⊓ centralizer (L : Set G) =
          T ⊓ centralizer (L : Set G) := inf_eq_left.mpr inf_le_right
      rw [← h1]
      nth_rewrite 1 [hTD]
      exact hDK
    have h2 : Nat.card (gmsDelta L T) = 2 := by
      refine Nat.card_eq_two_iff.mpr ⟨⟨_, ⟨1, rightConjugate_one _⟩, hT₀V⟩,
        ⟨_, ⟨h₀, rfl⟩, hDV⟩, fun h1 => hne (congrArg Subtype.val h1), ?_⟩
      refine Set.eq_univ_of_forall fun Q => ?_
      obtain ⟨⟨x, hx⟩, hQV⟩ := Q.2
      rcases h3 x (hx ▸ hQV) with h4 | h4
      · exact Or.inl (Subtype.ext (hx.symm.trans h4))
      · exact Or.inr (Subtype.ext (hx.symm.trans h4))
    rw [h2]
    exact even_two
  ·
    set V₀ := ⁅L ⊓ normalizer (gmsV L T : Set G), gmsV L T⁆ with hV₀def
    have hV₀V : V₀ ≤ gmsV L T := by
      rw [hV₀def, commutator_le]
      intro g hg v hv
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp (mem_inf.mp hg).2 v).mp hv) (inv_mem hv)
    have : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G))
      SetLike.coe_injective
    have : Fintype (gmsDelta L T) := Fintype.ofFinite _
    have hcount := card_mul_eq_of_cover (ι := gmsDelta L T) hV₀V (fun Q => Q.1)
      (fun i j hij => by
        obtain ⟨⟨x₁, hx₁⟩, hi⟩ := i.2
        obtain ⟨⟨x₂, hx₂⟩, hj⟩ := j.2
        have hne : rightConjugate (T ⊓ centralizer (L : Set G)) x₁ ≠
            rightConjugate (T ⊓ centralizer (L : Set G)) x₂ := fun h1 =>
          hij (Subtype.ext (hx₁.symm.trans (h1.trans hx₂)))
        show i.1 ⊓ j.1 = ⊥
        rw [← hx₁, ← hx₂]
        exact h.inf_eq_bot_of_conj hV2 (hx₁ ▸ hi) (hx₂ ▸ hj) hne)
      (fun i => i.2.2) (c := Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
      (fun i => by
        obtain ⟨⟨x, hx⟩, -⟩ := i.2
        show Nat.card i.1 = _
        rw [← hx, rightConjugate_card])
      (fun v hv => by
        rw [hcov v hv]
        constructor
        · rintro ⟨x, hxV, hvx, hv1⟩
          exact ⟨⟨_, ⟨x, rfl⟩, hxV⟩, hvx, hv1⟩
        · rintro ⟨⟨Q, ⟨x, rfl⟩, hQV⟩, hvQ, hv1⟩
          exact ⟨x, hQV, hvQ, hv1⟩)
    have hZ := hX.oddCenter
    obtain ⟨k, hB⟩ := hX.borel
    have hT₁syl : IsSylowOf 2 (T ⊓ L) L := h.isSylowOf_T₁
    obtain ⟨hA₁card, hA₁sq, -⟩ := hX.sylow h
    obtain ⟨y, hy, -, htrans, -⟩ := exists_torus hZ hT₁syl hB
    have hq4 := hX.four_le
    obtain ⟨a, ha, ha1⟩ : ∃ a ∈ gmsA L T, a ≠ 1 := by
      have h1 : 1 < Nat.card (gmsA L T) := by rw [hA₁card]; omega
      obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
        ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
      exact ⟨a, ha, fun h1 => ha1 (Subtype.ext h1)⟩
    obtain ⟨b, hb, hbz⟩ : ∃ b ∈ gmsA L T, b ∉ zpowers a := by
      by_contra hall
      push Not at hall
      have hle : gmsA L T ≤ zpowers a := hall
      have h1 := card_le_of_le hle
      rw [Nat.card_zpowers, hA₁card, orderOf_eq_prime (hA₁sq a ha) ha1] at h1
      omega
    have hb1 : b ≠ 1 := fun h1 => hbz (h1 ▸ one_mem _)
    have hba : b ≠ a := fun h1 => hbz (h1 ▸ mem_zpowers a)
    have hmove : ∃ c ∈ gmsA L T, y * c ≠ c * y := by
      by_contra hall
      push Not at hall
      obtain ⟨m, hm⟩ := htrans a ha b hb ha1 hb1
      have hc : y ^ m * a = a * y ^ m := (Commute.pow_left (hall a ha) m)
      apply hba
      rw [← hm, mul_assoc, ← hc, inv_mul_cancel_left]
    obtain ⟨c, hc, hyc⟩ := hmove
    have hyV : y ∈ normalizer (gmsV L T : Set G) := inf_normalizer_le_normalizer hy
    have hV₀1 : V₀ ≠ ⊥ := by
      intro hb'
      have h1 : ⁅y, c⁆ ∈ V₀ :=
        commutator_mem_commutator (mem_inf.mpr ⟨(mem_inf.mp hy).1, hyV⟩) (mem_sup_left hc)
      rw [hb', mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hyc h1
    have hV1 : gmsV L T ≠ ⊥ := fun hb' => hT₀1 (le_bot_iff.mp (hb' ▸ hT₀V))
    have hEV : Even (Nat.card (gmsV L T)) := even_card_of_isPGroup hV2 hV1
    have hEV₀ : Even (Nat.card V₀) := even_card_of_isPGroup (hV2.to_le hV₀V) hV₀1
    have hET₀ : Even (Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G)) :=
      even_card_of_isPGroup (h.sylow.isPGroup.to_le inf_le_left) hT₀1
    have hodd₀ : Odd (Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) - 1) := by
      have hpos : 0 < Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) := Nat.card_pos
      obtain ⟨k, hk⟩ := hET₀
      exact ⟨k - 1, by omega⟩
    have hEdiff : Even (Nat.card (gmsV L T) - Nat.card V₀) := by
      obtain ⟨k₁, hk₁⟩ := hEV
      obtain ⟨k₂, hk₂⟩ := hEV₀
      exact ⟨k₁ - k₂, by omega⟩
    rw [← hcount] at hEdiff
    rw [Nat.card_eq_fintype_card]
    rcases Nat.even_mul.mp hEdiff with h1 | h1
    · exact h1
    · exact absurd h1 (Nat.not_even_iff_odd.mpr hodd₀)

end Facts

end Sec3

end CFSG.ComponentClassification.GMS78
