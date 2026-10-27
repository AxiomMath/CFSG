module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39Core
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma36

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma39

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open scoped commutatorElement

section Elementary

variable {G : Type*} [Group G]

theorem isMulCommutative_map {Q' : Type*} [Group Q'] {H : Subgroup G} (hH : IsMulCommutative H)
    (f : G →* Q') : IsMulCommutative (H.map f) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨_, x, hx, rfl⟩ := a
  obtain ⟨_, y, hy, rfl⟩ := b
  apply Subtype.ext
  change f x * f y = f y * f x
  rw [← map_mul, ← map_mul]
  exact congrArg f (congrArg Subtype.val (hH.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

theorem commutator_le_self (C : Subgroup G) : ⁅C, C⁆ ≤ C := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem normal_inf_subgroupOf {X B : Subgroup G} (hXB : X ≤ normalizer (B : Set G)) :
    ((X ⊓ B).subgroupOf X).Normal := by
  refine ⟨fun n hn x => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨hnX, hnB⟩ := mem_inf.mp hn
  simp only [coe_mul, coe_inv]
  exact mem_inf.mpr ⟨mul_mem (mul_mem x.2 hnX) (inv_mem x.2),
    (mem_normalizer_iff.mp (hXB x.2) n).mp hnB⟩

end Elementary

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_normalizer_rightConjugate {A : Subgroup G} (hA : Hyp31 A) (g : G) {t : G}
    (ht : t ∈ rightConjugate (centralizer (A : Set G)) g) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    centralizer ({t} : Set G) ≤ normalizer (rightConjugate A g : Set G) := by
  have hKte := tightlyEmbedded_rightConjugate (tightlyEmbedded_centralizer hA.standard) g
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hp : IsPGroup 2 ↥(zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hle : zpowers t ≤ rightConjugate (centralizer (A : Set G)) g := zpowers_le.mpr ht
  have hne : zpowers t ≠ ⊥ := by rwa [Ne, zpowers_eq_bot]
  have h1 := centralizer_two_subgroup_le _ _ hKte hp hle hne
  intro c hc
  have hc' : c ∈ centralizer (zpowers t : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp hc).symm k).eq
  have h2 := h1 hc'
  rw [mem_normalizer_rightConjugate_iff] at h2 ⊢
  rwa [← normalizer_centralizer_eq hA.standard]

theorem absSylow_centralizer_rightConjugate {A T : Subgroup G} {g : G} (hTe : IsElemAbelian 2 T)
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    ∀ P : Sylow 2 ↥(centralizer (rightConjugate A g : Set G)),
      IsMulCommutative (P : Subgroup ↥(centralizer (rightConjugate A g : Set G))) := by
  rw [centralizer_rightConjugate]
  intro P
  have hP : IsSylowOf 2 ((P : Subgroup _).map (rightConjugate (centralizer (A : Set G)) g).subtype)
      (rightConjugate (centralizer (A : Set G)) g) := ⟨P, rfl⟩
  obtain ⟨h, -, hh⟩ := Lemma22.exists_conj_eq_of_isSylowOf hT hP
  refine isMulCommutative_of_injective _ (subtype_injective _) le_rfl ?_
  rw [hh]
  exact isMulCommutative_map hTe.1 _

@[expose] noncomputable def oddOuter (A : Subgroup G) (g : G) : Subgroup G :=
  ((oUpperTwo (⊤ : Subgroup (outerAutomorphismGroup ↥A)) ⊔
      commutator (outerAutomorphismGroup ↥A)).comap (outerMap A g)).map
    (normalizer (rightConjugate A g : Set G)).subtype

omit [Finite G] in
theorem oUpperTwo_le_oddOuter {A C : Subgroup G} {g : G}
    (hC : C ≤ normalizer (rightConjugate A g : Set G)) : oUpperTwo C ≤ oddOuter A g := by
  refine (closure_le _).mpr fun z hz => ?_
  refine ⟨⟨z, hC hz.1⟩, ?_, rfl⟩
  refine mem_comap.mpr (mem_sup_left (subset_closure ⟨mem_top _, ?_⟩))
  refine Odd.of_dvd_nat hz.2 ((orderOf_map_dvd _ _).trans ?_)
  rw [Subgroup.orderOf_mk]

omit [Finite G] in
theorem commutator_le_oddOuter {A C : Subgroup G} {g : G}
    (hC : C ≤ normalizer (rightConjugate A g : Set G)) : ⁅C, C⁆ ≤ oddOuter A g := by
  rw [commutator_le]
  intro a ha b hb
  refine ⟨⁅(⟨a, hC ha⟩ : ↥(normalizer (rightConjugate A g : Set G))), ⟨b, hC hb⟩⁆, ?_, rfl⟩
  refine mem_comap.mpr (mem_sup_right ?_)
  rw [map_commutatorElement]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

theorem odd_card_oUpperTwo_sup_commutator {A : Subgroup G}
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) :
    Odd (Nat.card ↥(oUpperTwo (⊤ : Subgroup (outerAutomorphismGroup ↥A)) ⊔
      commutator (outerAutomorphismGroup ↥A))) := by
  have : Finite (outerAutomorphismGroup ↥A) :=
    inferInstanceAs (Finite (MulAut ↥A ⧸ innerAutomorphismSubgroup ↥A))
  apply Lemma22.odd_card_of_forall_orderOf_ne_two
  intro x hx h2
  have := orderOf_odd_of_mem_oUpperTwo_sup_commutator hOut hx
  rw [h2] at this
  exact (by decide : ¬ Odd 2) this

theorem solvAbSylow_of_le_oddOuter (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A T : Subgroup G} {g t : G} (hA : Hyp31 A)
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) (ht : t ∈ T) (ht1 : t ≠ 1)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) {X : Subgroup G}
    (hXC : X ≤ A ⊓ centralizer ({t} : Set G)) (hXW : X ≤ oddOuter A g)
    [((X ⊓ rightConjugate A g).subgroupOf X).Normal] :
    SolvAbSylow (X ⧸ (X ⊓ rightConjugate A g).subgroupOf X) := by
  have : Finite (outerAutomorphismGroup ↥A) :=
    inferInstanceAs (Finite (MulAut ↥A ⧸ innerAutomorphismSubgroup ↥A))
  have hTe := isElemAbelian_of_isSylowOf_rightConjugate h32 hA hT
  have htK : t ∈ rightConjugate (centralizer (A : Set G)) g := hT.le ht
  have hCN := centralizer_le_normalizer_rightConjugate hA g htK ht1 (hTe.2 t ht)
  have hXN : X ≤ normalizer (rightConjugate A g : Set G) := (hXC.trans inf_le_right).trans hCN
  have htB : t ∈ centralizer (rightConjugate A g : Set G) := by
    rw [centralizer_rightConjugate]
    exact htK
  have hS : Group.IsSolvable
      ↥(centralizer (rightConjugate A g : Set G) ⊓ centralizer ({t} : Set G)) := by
    rw [centralizer_rightConjugate]
    have htight := tightlyEmbedded_rightConjugate (tightlyEmbedded_centralizer hA.standard) g
    exact (lemma21 h4 htight hT hTe (h34 G A hA).2
      (not_normal_rightConjugate_centralizer hA g)).2 t ht ht1
  refine solvAbSylow_quotient htB hXN (hXC.trans inf_le_right) hS
    (absSylow_centralizer_rightConjugate hTe hT) (outerMap A g)
    (fun x hx => outerMap_eq_one A g x hx) (fun x hx => mem_sup_of_outerMap_eq_one A g x hx)
    (odd_card_oUpperTwo_sup_commutator hOut) ?_
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hXW hx
  have hxy : (⟨x, hXN hx⟩ : ↥(normalizer (rightConjugate A g : Set G))) = y := Subtype.ext hyx.symm
  rw [hxy]
  exact hy

theorem le_oddOuter (h32 : Lemma32) {A T : Subgroup G} {g t : G} (hA : Hyp31 A)
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) (ht : t ∈ T)
    (ht1 : t ≠ 1) :
    A ⊓ centralizer ({t} : Set G) ≤ normalizer (rightConjugate A g : Set G) := by
  have hTe := isElemAbelian_of_isSylowOf_rightConjugate h32 hA hT
  exact inf_le_right.trans
    (centralizer_le_normalizer_rightConjugate hA g (hT.le ht) ht1 (hTe.2 t ht))

theorem lemma39_one (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A T : Subgroup G} {g t : G} (hA : Hyp31 A)
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) (ht : t ∈ T) (ht1 : t ≠ 1)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) :
    admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆) ≤ rightConjugate A g ∧
      rightConjugate A g ≤ centralizer (T : Set G) := by
  have hCN := le_oddOuter h32 hA hT ht ht1
  have hXC : oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
      ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆ ≤
      A ⊓ centralizer ({t} : Set G) :=
    sup_le (Lemma36.oUpperTwo_le _) (commutator_le_self _)
  have hXW := sup_le (oUpperTwo_le_oddOuter hCN) (commutator_le_oddOuter hCN)
  have := normal_inf_subgroupOf (B := rightConjugate A g) (hXC.trans hCN)
  refine ⟨(admResidual_le inf_le_left
    (solvAbSylow_of_le_oddOuter h4 h32 h34 hA hT ht ht1 hOut hXC hXW)).trans inf_le_right, ?_⟩
  rw [le_centralizer_iff, centralizer_rightConjugate]
  exact hT.le

theorem admResidual_oUpperTwo_le (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A T : Subgroup G} {g t : G} (hA : Hyp31 A)
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) (ht : t ∈ T) (ht1 : t ≠ 1)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) :
    admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G))) ≤ centralizer (T : Set G) := by
  have hCN := le_oddOuter h32 hA hT ht ht1
  have hXC := Lemma36.oUpperTwo_le (A ⊓ centralizer ({t} : Set G))
  have := normal_inf_subgroupOf (B := rightConjugate A g) (hXC.trans hCN)
  refine ((admResidual_le inf_le_left (solvAbSylow_of_le_oddOuter h4 h32 h34 hA hT ht ht1 hOut
    hXC (oUpperTwo_le_oddOuter hCN))).trans inf_le_right).trans ?_
  rw [← le_centralizer_iff, centralizer_rightConjugate]
  exact hT.le

theorem admissible_two_four (h2 : Asc76Theorem2) (h32 : Lemma32) {A T : Subgroup G} {g : G}
    (hA : Hyp31 A) (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    Nat.card T = 4 ∨ ∀ a ∈ A, T ⊓ normalizer (rightConjugate T a : Set G) ≤
      centralizer (rightConjugate T a : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTe := isElemAbelian_of_isSylowOf_rightConjugate h32 hA hT
  by_cases hT4 : Nat.card T = 4
  · exact Or.inl hT4
  refine Or.inr fun a _ => ?_
  have hKte := tightlyEmbedded_centralizer hA.standard
  have hTae : IsElemAbelian 2 (rightConjugate T a) := isElemAbelian_rightConjugate hTe a
  by_cases haN : a ∈ normalizer (rightConjugate A g : Set G)
  ·
    have haK : a ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) := by
      rw [← centralizer_rightConjugate]
      exact Lemma22.normalizer_le_normalizer_centralizer _ haN
    have hTa : IsSylowOf 2 (rightConjugate T a) (rightConjugate (centralizer (A : Set G)) g) := by
      have := AschbacherTheorem3.isSylowOf_rightConjugate hT a
      rwa [(rightConjugate_eq_self_iff _ _).mpr haK] at this
    have hle : T ⊓ normalizer (rightConjugate T a : Set G) ⊔ rightConjugate T a ≤
        rightConjugate (centralizer (A : Set G)) g := sup_le (inf_le_left.trans hT.le) hTa.le
    have hp : IsPGroup 2 ↥(T ⊓ normalizer (rightConjugate T a : Set G) ⊔ rightConjugate T a) :=
      IsPGroup.to_sup_of_normal_right' (hT.isPGroup.to_le inf_le_left) hTa.isPGroup inf_le_right
    have heq := hTa.eq_of_le le_sup_right hle hp
    calc T ⊓ normalizer (rightConjugate T a : Set G)
        ≤ T ⊓ normalizer (rightConjugate T a : Set G) ⊔ rightConjugate T a := le_sup_left
      _ = rightConjugate T a := heq
      _ ≤ centralizer (rightConjugate T a : Set G) := le_centralizer_self_of_isElemAbelian hTae
  ·
    rcases eq_or_ne (T ⊓ normalizer (rightConjugate T a : Set G)) ⊥ with h0 | h0
    · rw [h0]
      exact bot_le
    have hT1 : T ≠ ⊥ := Lemma22.ne_bot_of_isSylowOf_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate hKte g) hT
    have hcard1 : ∀ {Q : Subgroup G} (x : G), Q ≠ ⊥ → rightConjugate Q x ≠ ⊥ := by
      intro Q x hQ h
      apply hQ
      have hc := rightConjugate_card Q x
      rw [h, card_bot] at hc
      exact card_eq_one.mp hc.symm
    have hR' : IsSylowOf 2 (rightConjugate T g⁻¹) (centralizer (A : Set G)) := by
      have := AschbacherTheorem3.isSylowOf_rightConjugate hT g⁻¹
      rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
    have hg' : g * a⁻¹ * g⁻¹ ∉ normalizer (A : Set G) := by
      intro h
      apply haN
      have h1 : a⁻¹ ∈ normalizer (rightConjugate A g : Set G) :=
        (mem_normalizer_rightConjugate_iff A g a⁻¹).mpr h
      simpa using inv_mem h1
    have hS₀K : rightConjugate (T ⊓ normalizer (rightConjugate T a : Set G)) (g * a)⁻¹ ≤
        rightConjugate (centralizer (A : Set G)) (g * a⁻¹ * g⁻¹) := by
      have h1 : rightConjugate (T ⊓ normalizer (rightConjugate T a : Set G)) (g * a)⁻¹ ≤
          rightConjugate (rightConjugate (centralizer (A : Set G)) g) (g * a)⁻¹ :=
        map_mono (inf_le_left.trans hT.le)
      rwa [rightConjugate_mul, show g * (g * a)⁻¹ = g * a⁻¹ * g⁻¹ by group] at h1
    have hS₀N : rightConjugate (T ⊓ normalizer (rightConjugate T a : Set G)) (g * a)⁻¹ ≤
        normalizer (A : Set G) := by
      intro z hz
      rw [mem_rightConjugate_iff] at hz
      have hz' := (mem_inf.mp hz).2
      have hTaK : rightConjugate T a ≤ rightConjugate (centralizer (A : Set G)) (g * a) := by
        rw [← rightConjugate_mul]
        exact map_mono hT.le
      have h1 := normalizer_two_subgroup_le _ _ (tightlyEmbedded_rightConjugate hKte (g * a))
        (hT.isPGroup.map _) hTaK (hcard1 a hT1) hz'
      rw [mem_normalizer_rightConjugate_iff, normalizer_centralizer_eq hA.standard] at h1
      have h2' : g * a * ((g * a)⁻¹ * z * (g * a)⁻¹⁻¹) * (g * a)⁻¹ = z := by group
      rwa [h2'] at h1
    have hS₀p : IsPGroup 2
        ↥(rightConjugate (T ⊓ normalizer (rightConjugate T a : Set G)) (g * a)⁻¹) :=
      (hT.isPGroup.to_le inf_le_left).map _
    obtain ⟨T', hT', hS₀T'⟩ := exists_isSylowOf_le (le_inf hS₀K hS₀N) hS₀p
    have hT'1 : T' ≠ ⊥ := by
      intro h
      apply hcard1 (g * a)⁻¹ h0
      rw [eq_bot_iff, ← h]
      exact hS₀T'
    rcases h2 G A hA.oddCore hA.standard (asc76HypII_of_hypII hA.standard.1 hA.hypII) hA.rank _ hR'
        _ hg' T' hT' hT'1 with ⟨h4', -⟩ | ⟨-, -, hcomm⟩
    · exact absurd (by rw [← h4', rightConjugate_card]) hT4
    · have hTac : rightConjugate (rightConjugate T a) (g * a)⁻¹ = rightConjugate T g⁻¹ := by
        rw [rightConjugate_mul]
        congr 1
        group
      have h1 : rightConjugate (T ⊓ normalizer (rightConjugate T a : Set G)) (g * a)⁻¹ ≤
          T' ⊓ normalizer (rightConjugate T g⁻¹ : Set G) := by
        refine le_inf hS₀T' ?_
        rw [← hTac]
        intro z hz
        rw [mem_normalizer_rightConjugate_iff]
        rw [mem_rightConjugate_iff] at hz
        exact (mem_inf.mp hz).2
      have h3 : ⁅rightConjugate (T ⊓ normalizer (rightConjugate T a : Set G)) (g * a)⁻¹,
          rightConjugate (rightConjugate T a) (g * a)⁻¹⁆ = ⊥ := by
        rw [hTac, eq_bot_iff, ← hcomm]
        exact commutator_mono h1 le_rfl
      have h5 : ⁅T ⊓ normalizer (rightConjugate T a : Set G), rightConjugate T a⁆ = ⊥ := by
        have h6 : rightConjugate ⁅T ⊓ normalizer (rightConjugate T a : Set G), rightConjugate T a⁆
            (g * a)⁻¹ = ⁅rightConjugate (T ⊓ normalizer (rightConjugate T a : Set G)) (g * a)⁻¹,
              rightConjugate (rightConjugate T a) (g * a)⁻¹⁆ := map_commutator _ _ _
        rw [h3] at h6
        exact (map_eq_bot_iff_of_injective _ (MulAut.conj (g * a)⁻¹⁻¹).injective).mp h6
      exact commutator_eq_bot_iff_le_centralizer.mp h5

theorem lemma39_three (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (h2 : Asc76Theorem2) {A T : Subgroup G} {g : G} (hA : Hyp31 A)
    (hg : g ∉ normalizer (A : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTA : T ≤ normalizer (A : Set G))
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) : IsAdmissible T A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTe := isElemAbelian_of_isSylowOf_rightConjugate h32 hA hT
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 (centralizer (A : Set G))
  obtain ⟨x, hTx, -⟩ := Lemma36.exists_conj_eq hR hT
  have hT4 : 4 ≤ Nat.card T := by
    rw [hTx, rightConjugate_card]
    exact Lemma36.four_le_card hA hR
  have hTK : T ⊓ centralizer (A : Set G) = ⊥ := by
    have hKte := tightlyEmbedded_centralizer hA.standard
    have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
      rwa [normalizer_centralizer_eq hA.standard]
    exact two_subgroup_inf_conjugate_eq_bot _ T hKte hT.isPGroup g hgK hT.le
  unfold IsAdmissible NoncyclicFaithful
  exact ⟨⟨hTe, hT4, hTA, hTK⟩, sylowInTightTwoNilpotent_of_hyp31 h32 h4 h34 hA hT A,
    admissible_two_four h2 h32 hA hT,
    fun t ht ht1 => admResidual_oUpperTwo_le h4 h32 h34 hA hT ht ht1 hOut⟩

end Lemma39

end CFSG.ComponentClassification.AS76b
