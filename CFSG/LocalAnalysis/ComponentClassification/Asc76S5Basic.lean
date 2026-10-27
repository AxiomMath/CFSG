module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3Config
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem le_centerOf_or_eq_of_le_normalizer {A X : Subgroup G} (hq : Open.IsQuasisimple A)
    (hXA : X ≤ A) (hAX : A ≤ normalizer (X : Set G)) :
    X ≤ A ⊓ centralizer (A : Set G) ∨ X = A := by
  have hn : (X.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hXA).mpr hAX
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (X.subgroupOf A) with h | h
  · refine Or.inl fun x hx => ⟨hXA hx, ?_⟩
    show x ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have hc := mem_center_iff.mp (h (show (⟨x, hXA hx⟩ : A) ∈ X.subgroupOf A from hx)) ⟨a, ha⟩
    exact congrArg Subtype.val hc
  · refine Or.inr (le_antisymm hXA fun a ha => ?_)
    have : (⟨a, ha⟩ : A) ∈ X.subgroupOf A := h ▸ mem_top _
    exact this

theorem commutator_eq_bot_of_commutator_commutator_eq_bot {X A : Subgroup G}
    (hA : ⁅A, A⁆ = A) (h : ⁅⁅X, A⁆, A⁆ = ⊥) : ⁅X, A⁆ = ⊥ := by
  have h1 : ⁅⁅A, X⁆, A⁆ = ⊥ := by rw [commutator_comm A X]; exact h
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h
  rw [hA] at h3
  rw [commutator_comm]
  exact h3

theorem commutator_self_of_isQuasisimple {A : Subgroup G} (hq : Open.IsQuasisimple A) :
    ⁅A, A⁆ = A := by
  have h1 := hq.1
  have h2 : (commutator A).map A.subtype = ⁅A, A⁆ := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rw [← h2, h1, ← MonoidHom.range_eq_map, range_subtype]

theorem commutator_eq_bot_of_inf_le_centerOf {X A : Subgroup G} (hq : Open.IsQuasisimple A)
    (hXA : X ≤ normalizer (A : Set G)) (hAX : A ≤ normalizer (X : Set G))
    (hZ : X ⊓ A ≤ centralizer (A : Set G)) : ⁅X, A⁆ = ⊥ := by
  have hle : ⁅X, A⁆ ≤ X ⊓ A := by
    rw [commutator_le]
    intro x hx a ha
    refine ⟨?_, ?_⟩
    · have h := (mem_normalizer_iff.mp (hAX ha) x⁻¹).mp (X.inv_mem hx)
      have : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [this]
      exact X.mul_mem hx h
    · have h := (mem_normalizer_iff.mp (hXA hx) a).mp ha
      have : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := by group
      rw [this]
      exact A.mul_mem h (A.inv_mem ha)
  refine commutator_eq_bot_of_commutator_commutator_eq_bot
    (commutator_self_of_isQuasisimple hq) ?_
  rw [eq_bot_iff, commutator_le]
  intro c hc a ha
  have hcA := mem_centralizer_iff.mp (hZ (hle hc)) a ha
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hcA.symm

theorem inf_normalizer_eq_inf_centralizer {R T : Subgroup G} (hTR : T ≤ normalizer (R : Set G))
    (hRT : R ⊓ T = ⊥) : R ⊓ normalizer (T : Set G) = R ⊓ centralizer (T : Set G) := by
  refine le_antisymm (fun r hr => ⟨hr.1, ?_⟩)
    (inf_le_inf_left R (centralizer_le_normalizer _))
  show r ∈ centralizer (T : Set G)
  rw [mem_centralizer_iff]
  intro t ht
  have h1 : r * t * r⁻¹ * t⁻¹ ∈ T := T.mul_mem ((mem_normalizer_iff.mp hr.2 t).mp ht) (T.inv_mem ht)
  have h2 : r * t * r⁻¹ * t⁻¹ ∈ R := by
    have h3 := (mem_normalizer_iff.mp (hTR ht) r⁻¹).mp (R.inv_mem hr.1)
    have h4 := R.mul_mem hr.1 h3
    simpa [mul_assoc] using h4
  have h5 : r * t * r⁻¹ * t⁻¹ ∈ R ⊓ T := ⟨h2, h1⟩
  rw [hRT, mem_bot] at h5
  have : r * t * r⁻¹ = t := mul_inv_eq_one.mp h5
  calc t * r = r * t * r⁻¹ * r := by rw [this]
    _ = r * t := by group

variable [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_of_tightlyEmbedded {K V : Subgroup G} (hK : TightlyEmbedded K)
    (hVK : V ≤ K) (hV : Even (Nat.card V)) :
    normalizer (V : Set G) ≤ normalizer (K : Set G) :=
  CFSG.StandardSubgroupAPI.normalizer_le_normalizer_of_le_of_even hK hVK hV

theorem card_le_of_isSylowOf {P Q H : Subgroup G} (hP : IsSylowOf 2 P H) (hQH : Q ≤ H)
    (hQ : IsPGroup 2 Q) : Nat.card Q ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hQS⟩ := exists_isSylowOf_le hQH hQ
  rw [hP.card_eq, ← hS.card_eq]
  exact card_le_of_le hQS

theorem card_le_card_of_overlap {K T P : Subgroup G} (hK : TightlyEmbedded K) {g : G}
    (hg : g ∉ normalizer (K : Set G))
    (hT : IsSylowOf 2 T (rightConjugate K g ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥)
    (hP : IsSylowOf 2 P (K ⊓ normalizer (rightConjugate K g : Set G))) :
    Nat.card T ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_le (le_sup_right : T ≤ K ⊔ T) hT.isPGroup
  have hR : IsSylowOf 2 (S ⊓ K) K := hS.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTN)
  have hTR : T ≤ normalizer ((S ⊓ K : Subgroup G) : Set G) := by
    intro t ht
    have h1 := mem_normalizer_iff.mp (le_normalizer (hTS ht) : t ∈ normalizer (S : Set G))
    have h2 := mem_normalizer_iff.mp (hTN ht)
    rw [mem_normalizer_iff]
    intro x
    rw [mem_inf, mem_inf, h1 x, h2 x]
  obtain ⟨e⟩ := inf_centralizer_mulEquiv_of_tightlyEmbedded hK hg hT hT1 hR hTR
  have hTeven : Even (Nat.card T) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT.isPGroup
    rcases n with _ | n
    · exact absurd (card_eq_one.mp (by simpa using hn)) hT1
    · rw [hn, pow_succ]
      exact even_two.mul_left _
  have hCle : (S ⊓ K) ⊓ centralizer (T : Set G) ≤ K ⊓ normalizer (rightConjugate K g : Set G) :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans ((centralizer_le_normalizer _).trans
      (normalizer_le_normalizer_of_tightlyEmbedded (tightlyEmbedded_rightConjugate hK g)
        (hT.le.trans inf_le_left) hTeven)))
  have hCp : IsPGroup 2 ((S ⊓ K) ⊓ centralizer (T : Set G) : Subgroup G) :=
    hR.isPGroup.to_le inf_le_left
  rw [← Nat.card_congr e.toEquiv]
  exact card_le_of_isSylowOf hP hCle hCp

theorem card_eq_card_of_overlap {K T P : Subgroup G} (hK : TightlyEmbedded K) {g : G}
    (hg : g ∉ normalizer (K : Set G))
    (hT : IsSylowOf 2 T (rightConjugate K g ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥)
    (hP : IsSylowOf 2 P (K ⊓ normalizer (rightConjugate K g : Set G))) :
    Nat.card P = Nat.card T := by
  have hle := card_le_card_of_overlap hK hg hT hT1 hP
  have hKg : rightConjugate (rightConjugate K g) g⁻¹ = K := by
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hg' : g⁻¹ ∉ normalizer (rightConjugate K g : Set G) := by
    intro h
    apply hg
    have h2 := (rightConjugate_eq_self_iff _ _).mpr h
    rw [hKg] at h2
    exact (rightConjugate_eq_self_iff K g).mp h2.symm
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hle
    have hTc : Nat.card T = 1 := le_antisymm hle Nat.card_pos
    exact hT1 (card_eq_one.mp hTc)
  have hP' : IsSylowOf 2 P (rightConjugate (rightConjugate K g) g⁻¹ ⊓
      normalizer (rightConjugate K g : Set G)) := by rwa [hKg]
  have hT' : IsSylowOf 2 T (rightConjugate K g ⊓
      normalizer (rightConjugate (rightConjugate K g) g⁻¹ : Set G)) := by rwa [hKg]
  exact le_antisymm (card_le_card_of_overlap (tightlyEmbedded_rightConjugate hK g) hg' hP' hP1
    hT') hle

theorem le_normalizer_of_weaklyClosed {K R T : Subgroup G} (hRK : R ≤ K) (hRp : IsPGroup 2 R)
    (hTp : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G)) (hTR : T ≤ normalizer (R : Set G))
    (hW : ∀ k ∈ K, rightConjugate T k ≤ R ⊔ T → rightConjugate T k = T) :
    R ⊔ T ≤ normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := R ⊔ T with hS
  have hSp : IsPGroup 2 S := hRp.to_sup_of_normal_left' hTp hTR
  have : Group.IsNilpotent S := hSp.isNilpotent
  set H : Subgroup S := (S ⊓ normalizer (T : Set G)).subgroupOf S with hH
  by_contra hcon
  have hHlt : H < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hcon fun x hx => ?_
    have : (⟨x, hx⟩ : S) ∈ H := h ▸ mem_top _
    exact (mem_subgroupOf.mp this).2
  obtain ⟨s, hsN, hsH⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent H hHlt)
  have hsT : (s : G) ∉ normalizer (T : Set G) := fun h => hsH (mem_subgroupOf.mpr ⟨s.2, h⟩)
  have hTsS : rightConjugate T s ≤ S := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have hxS : (s : G) * x * (s : G)⁻¹ ∈ S := (le_sup_right : T ≤ S) hx
    have hy : (⟨(s : G) * x * (s : G)⁻¹, hxS⟩ : S) ∈ H :=
      mem_subgroupOf.mpr ⟨hxS, le_normalizer hx⟩
    have h1 := (mem_normalizer_iff.mp hsN (s⁻¹ * ⟨(s : G) * x * (s : G)⁻¹, hxS⟩ * s)).mpr
      (by simpa [mul_assoc] using hy)
    have h2 := (mem_subgroupOf.mp h1).1
    simpa [mul_assoc] using h2
  have hsRT : (s : G) ∈ ((R : Set G) * (T : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left R T hTR]
    exact s.2
  obtain ⟨r, hr, t, ht, hrt⟩ := hsRT
  have hk : t⁻¹ * r * t ∈ K := by
    have := (mem_normalizer_iff.mp (hTK (T.inv_mem ht)) r).mp (hRK hr)
    simpa using this
  have hrt' : r * t = s := hrt
  have hTt : rightConjugate T t⁻¹ = T :=
    (rightConjugate_eq_self_iff T t⁻¹).mpr (le_normalizer (T.inv_mem ht))
  have hTk : rightConjugate T (t⁻¹ * r * t) = rightConjugate T s := by
    rw [← hrt', ← rightConjugate_mul T (t⁻¹ * r) t, ← rightConjugate_mul T t⁻¹ r, hTt,
      rightConjugate_mul T r t]
  have hEq := hW _ hk (hTk ▸ hTsS)
  rw [hTk] at hEq
  exact hsT ((rightConjugate_eq_self_iff T s).mp hEq)

end CFSG.ComponentClassification.Asc76.Sec5
