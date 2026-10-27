module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Main
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Steps
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxQuot

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

@[expose] def IsCoverPair (A R : Subgroup X) (m : ℕ) : Prop :=
  A ≠ ⊥ ∧ IsPGroup 2 A ∧ IsTwoComponentIn R (centralizer (A : Set X)) ∧ Odd m ∧ 9 ≤ m ∧
    Open.fusionZStar ↥R ≠ pPrimeCore 2 ↥R ∧
    Nonempty (↥R ⧸ Open.fusionZStar ↥R ≃* alternatingGroup (Fin m))

@[expose] noncomputable def coverMeasure (A R : Subgroup X) : ℕ :=
  2 ^ (Nat.card ↥(centralizer (A : Set X) ⊓ coreActionKernel R)).factorization 2

omit [Group X] in
theorem fusionZStar_eq_iff_of_mulEquiv {P P' : Type*} [Group P] [Group P'] (e : P ≃* P') :
    Open.fusionZStar P = pPrimeCore 2 P ↔ Open.fusionZStar P' = pPrimeCore 2 P' := by
  rw [Sol78.fusionZStar_eq_iff, Sol78.fusionZStar_eq_iff,
    ← Sol78.map_center_eq_of_mulEquiv (Sol78.coreQuotCongr e)]
  constructor
  · intro h
    rw [h, Subgroup.map_bot]
  · intro h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).mp h

theorem centralizer_mk_eq_top {A : Subgroup X} {a : X} (haA : a ∈ A)
    (haC : a ∈ centralizer (A : Set X)) :
    centralizer ({(⟨a, haC⟩ : ↥(centralizer (A : Set X)))} : Set ↥(centralizer (A : Set X))) =
      ⊤ := by
  refine eq_top_iff.mpr fun w _ => ?_
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext ((mem_centralizer_iff.mp w.2) a haA).symm

variable [Finite X]

theorem card_le_coverMeasure {A R P : Subgroup X} (hP : IsPGroup 2 P)
    (hPD : P ≤ centralizer (A : Set X) ⊓ coreActionKernel R) :
    Nat.card P ≤ coverMeasure A R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ :=
    (hP.comap_subtype (K := centralizer (A : Set X) ⊓ coreActionKernel R)).exists_le_sylow
  have h1 : Nat.card (P.comap (centralizer (A : Set X) ⊓ coreActionKernel R).subtype) =
      Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv
  rw [← h1, coverMeasure, ← Sylow.card_eq_multiplicity S]
  exact Subgroup.card_le_of_le hS

theorem coverMeasure_le_card (A R : Subgroup X) : coverMeasure A R ≤ Nat.card X := by
  rw [coverMeasure]
  calc 2 ^ (Nat.card ↥(centralizer (A : Set X) ⊓ coreActionKernel R)).factorization 2
      ≤ Nat.card ↥(centralizer (A : Set X) ⊓ coreActionKernel R) :=
        Nat.ordProj_le 2 Nat.card_pos.ne'
    _ ≤ Nat.card X := Subgroup.card_le_card_group _

theorem exists_involution_mem_center {A : Subgroup X} (hA : A ≠ ⊥) (hA2 : IsPGroup 2 A) :
    ∃ a : X, orderOf a = 2 ∧ a ∈ A ∧ a ∈ centralizer (A : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA
  have hZA := hA2.center_nontrivial
  have hZ2 : 2 ∣ Nat.card (center ↥A) := by
    rcases (hA2.to_subgroup (center ↥A)).card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hZA).ne'
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥A)) 2 hZ2
  refine ⟨((w : ↥A) : X), by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw], (w : ↥A).2,
    ?_⟩
  rw [mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val (mem_center_iff.mp w.2 ⟨b, hb⟩)

theorem IsCoverPair.isDoublePair {A R : Subgroup X} {m : ℕ} (hP : IsCoverPair A R m) {a : X}
    (ha : orderOf a = 2) (haA : a ∈ A) (haC : a ∈ centralizer (A : Set X)) :
    Sol78.IsDoublePair (⟨a, haC⟩ : ↥(centralizer (A : Set X)))
      (R.subgroupOf (centralizer (A : Set X))) m := by
  obtain ⟨-, -, ⟨hRC, hR⟩, hm, hm9, hne, ⟨e⟩⟩ := hP
  have htop := centralizer_mk_eq_top haA haC
  refine ⟨by rw [Subgroup.orderOf_mk]; exact ha, by rw [htop]; exact le_top, ?_, hm, by omega,
    ?_, ⟨(Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hRC)).trans e⟩⟩
  · rw [htop]
    exact (isPComponent_subgroupOf_top_iff _).mpr hR
  · rwa [Ne, fusionZStar_eq_iff_of_mulEquiv (subgroupOfEquivOfLe hRC)]

theorem IsCoverPair.coreQuotient (hSchur : SolAltLit.SchurAlternatingMultiplierInput)
    {A R : Subgroup X} {m : ℕ} (hP : IsCoverPair A R m) :
    IsQuasisimple (↥R ⧸ pPrimeCore 2 ↥R) ∧ Nat.card (center (↥R ⧸ pPrimeCore 2 ↥R)) = 2 := by
  obtain ⟨a, ha, haA, haC⟩ := exists_involution_mem_center hP.1 hP.2.1
  obtain ⟨-, hq, hZ2, -⟩ := (hP.isDoublePair ha haA haC).coreQuotient hSchur
  have hRC := hP.2.2.1.1
  set e := Sol78.coreQuotCongr (subgroupOfEquivOfLe hRC)
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv e hq, ?_⟩
  rw [← Sol78.map_center_eq_of_mulEquiv e, Subgroup.card_map_of_injective e.injective, hZ2]

theorem IsCoverPair.exists_sylow_centralizing (hSchur : SolAltLit.SchurAlternatingMultiplierInput)
    {A R : Subgroup X} {m : ℕ} (hP : IsCoverPair A R m) :
    ∃ y : X, orderOf y = 2 ∧ y ∈ R ∧
      (∀ l ∈ R, l⁻¹ * y⁻¹ * l * y ∈ (pPrimeCore 2 ↥R).map R.subtype) ∧
      ∃ Q : Subgroup X, IsPGroup 2 Q ∧ Q ≤ centralizer (A : Set X) ⊓ coreActionKernel R ∧
        Q ≤ centralizer ({y} : Set X) ∧ Nat.card Q = coverMeasure A R := by
  obtain ⟨a, ha, haA, haC⟩ := exists_involution_mem_center hP.1 hP.2.1
  have hRC := hP.2.2.1.1
  set C := centralizer (A : Set X) with hC
  obtain ⟨y', hy', hy'L, hy'K, Q', hQ', -, hQ'L, hQ'y, hQ'card⟩ :=
    Sol78.exists_sylow_centralizing hSchur (hP.isDoublePair ha haA haC)
  have hmap : (coreActionKernel (R.subgroupOf C)).map C.subtype = C ⊓ coreActionKernel R := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact mem_inf.mpr ⟨c.2, (mem_coreActionKernel_subgroupOf_iff hRC c).mp hc⟩
    · intro hg
      obtain ⟨hgC, hgK⟩ := mem_inf.mp hg
      exact ⟨⟨g, hgC⟩, (mem_coreActionKernel_subgroupOf_iff hRC _).mpr hgK, rfl⟩
  have hcard : Nat.card ↥(Sol78.pairKernel (⟨a, haC⟩ : ↥C) (R.subgroupOf C)) =
      Nat.card ↥(C ⊓ coreActionKernel R) := by
    rw [Sol78.pairKernel, centralizer_mk_eq_top haA haC, top_inf_eq, ← hmap,
      Subgroup.card_map_of_injective C.subtype_injective]
  refine ⟨(y' : X), by rw [Subgroup.orderOf_coe]; exact hy', mem_subgroupOf.mp hy'L, ?_,
    Q'.map C.subtype, hQ'.map _, ?_, ?_, ?_⟩
  · intro l hl
    have h1 := mem_map_of_mem C.subtype (hy'K ⟨l, hRC hl⟩ (mem_subgroupOf.mpr hl))
    rw [pPrimeCore_map_subgroupOf 2 R C hRC] at h1
    simpa using h1
  · rintro _ ⟨q, hq, rfl⟩
    exact mem_inf.mpr ⟨q.2, Sol78.mem_coreActionKernel_of_subgroupOf hRC (hQ'L hq)⟩
  · rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hQ'y hq))
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hQ'card, Sol78.pairMeasure,
      coverMeasure, hcard]

omit [Group X] [Finite X] in
theorem fusionZStar_le_sup_zpowers {P : Type*} [Group P] [Finite P] {y : P}
    (hy : orderOf y = 2)
    (hyc : QuotientGroup.mk' (pPrimeCore 2 P) y ∈ center (P ⧸ pPrimeCore 2 P))
    (hZ : Nat.card (center (P ⧸ pPrimeCore 2 P)) ≤ 2) :
    Open.fusionZStar P ≤ pPrimeCore 2 P ⊔ zpowers y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 P with hO
  set π := QuotientGroup.mk' O with hπ
  have hZ' : Nat.card (center (P ⧸ O)) ≤ 2 := hZ
  have hy1 : π y ≠ 1 := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have h2 := O.orderOf_dvd_natCard h
    rw [hy] at h2
    exact absurd (Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := P)) h2)
      (by norm_num)
  intro z hz
  rw [Sol78.fusionZStar_eq_comap, mem_comap] at hz
  have hcases : π z = 1 ∨ π z = π y := by
    by_contra hc
    push Not at hc
    obtain ⟨hz1, hzy⟩ := hc
    have hsub : ({1, π y, π z} : Set (P ⧸ O)) ⊆ (center (P ⧸ O) : Set (P ⧸ O)) := by
      intro a ha
      rcases ha with rfl | rfl | rfl
      · exact one_mem _
      · exact hyc
      · exact hz
    have hc3 : ({1, π y, π z} : Set (P ⧸ O)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hzy)]
      rintro (h | h)
      · exact hy1 h.symm
      · exact hz1 h.symm
    have h3 : 3 ≤ Nat.card (center (P ⧸ O)) := by
      calc 3 = ({1, π y, π z} : Set (P ⧸ O)).ncard := hc3.symm
        _ ≤ (center (P ⧸ O) : Set (P ⧸ O)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card (center (P ⧸ O)) := (Nat.card_coe_set_eq _).symm
    omega
  rcases hcases with h | h
  · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact mem_sup_left h
  · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
    have hz' : z = y * (z⁻¹ * y)⁻¹ := by group
    rw [hz']
    exact mul_mem (mem_sup_right (mem_zpowers y)) (mem_sup_left (inv_mem h))

theorem fusionZStar_ne_of_central_mem_sup {Y M₁ M₂ : Subgroup X} (hM₁ : IsTwoComponentIn M₁ Y)
    (hM₂ : IsTwoComponentIn M₂ Y) (hne : M₁ ≠ M₂) {y : X} (hy : orderOf y = 2) (hyY : y ∈ Y)
    (hyc : ∀ g ∈ Y, g * y = y * g) (hyM : y ∈ M₁ ⊔ M₂) :
    Open.fusionZStar ↥M₁ ≠ pPrimeCore 2 ↥M₁ ∨ Open.fusionZStar ↥M₂ ≠ pPrimeCore 2 ↥M₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  set N := pPrimeCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  have hne' : M₁.subgroupOf Y ≠ M₂.subgroupOf Y := by
    intro h
    apply hne
    rwa [subgroupOf_inj, inf_of_le_left hM₁.1, inf_of_le_left hM₂.1] at h
  obtain ⟨-, -, -, hcomm⟩ := UnbalancingLocal.Correspondence.image_components hM₁.2 hM₂.2 hne'
  have hZ : ∀ {M : Subgroup X}, IsTwoComponentIn M Y → Open.fusionZStar ↥M = pPrimeCore 2 ↥M →
      center ↥((M.subgroupOf Y).map π) = ⊥ := by
    intro M hM hex
    have hsub : (M.subgroupOf Y).IsSubnormal := by
      obtain ⟨_, _, h, _, _⟩ := hM.2
      exact h
    let e : ↥M ⧸ pPrimeCore 2 ↥M ≃* ↥((M.subgroupOf Y).map π) :=
      (Sol78.coreQuotCongr (subgroupOfEquivOfLe hM.1).symm).trans
        (CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage 2 (M.subgroupOf Y) hsub)
    rw [← Sol78.map_center_eq_of_mulEquiv e, (Sol78.fusionZStar_eq_iff _).mp hex,
      Subgroup.map_bot]
  have hZ₁ := hZ hM₁ h₁
  have hZ₂ := hZ hM₂ h₂
  set A := (M₁.subgroupOf Y).map π with hA
  set B := (M₂.subgroupOf Y).map π with hB
  set y' : ↥Y := ⟨y, hyY⟩ with hy'
  have hπy : π y' ∈ A ⊔ B := by
    rw [hA, hB, ← Subgroup.map_sup, ← subgroupOf_sup hM₁.1 hM₂.1]
    exact mem_map_of_mem π (mem_subgroupOf.mpr hyM)
  have hle : B ≤ normalizer (A : Set (↥Y ⧸ N)) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 := hcomm a ha b hb
      rw [show b * a * b⁻¹ = a by rw [← h1]; group]
      exact ha
    · intro ha
      have h1 := hcomm _ ha b hb
      have e : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹ * b) := by group
          _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [h1]
          _ = b * a * b⁻¹ := by group
      rw [e]
      exact ha
  obtain ⟨u, hu, v, hv, huv⟩ := Sol76.exists_mul_of_mem_sup_normalizer hle hπy
  have hyZ : ∀ w : ↥Y ⧸ N, π y' * w = w * π y' := by
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N w
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyc w w.2).symm
  have hu1 : u = 1 := by
    have huZ : (⟨u, hu⟩ : ↥A) ∈ center ↥A := by
      rw [mem_center_iff]
      intro a
      apply Subtype.ext
      have h1 := hyZ a
      rw [huv] at h1
      have h2 : v * a = a * v := (hcomm a a.2 v hv).symm
      have h3 : u * a * v = a * u * v := by
        calc u * a * v = u * (a * v) := by group
          _ = u * (v * a) := by rw [h2]
          _ = u * v * a := by group
          _ = a * (u * v) := h1
          _ = a * u * v := by group
      exact (mul_right_cancel h3).symm
    rw [hZ₁, mem_bot] at huZ
    exact congrArg Subtype.val huZ
  have hv1 : v = 1 := by
    have hvZ : (⟨v, hv⟩ : ↥B) ∈ center ↥B := by
      rw [mem_center_iff]
      intro b
      apply Subtype.ext
      have h1 := hyZ b
      rw [huv] at h1
      have h2 : u * b = b * u := hcomm u hu b b.2
      have h3 : u * (v * b) = u * (b * v) := by
        calc u * (v * b) = u * v * b := by group
          _ = b * (u * v) := h1
          _ = b * u * v := by group
          _ = u * b * v := by rw [h2]
          _ = u * (b * v) := by group
      exact (mul_left_cancel h3).symm
    rw [hZ₂, mem_bot] at hvZ
    exact congrArg Subtype.val hvZ
  rw [hu1, hv1, mul_one, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at huv
  have h2 := N.orderOf_dvd_natCard huv
  rw [hy', Subgroup.orderOf_mk, hy] at h2
  exact absurd (Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := ↥Y)) h2)
    (by norm_num)

end CFSG.ComponentClassification.SolMax
