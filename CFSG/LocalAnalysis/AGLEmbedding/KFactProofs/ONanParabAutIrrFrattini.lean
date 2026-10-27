module

public import Mathlib.GroupTheory.Frattini

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open scoped commutatorElement

theorem commutator_top_le_frattini {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ frattini P := by
  have : Group.IsNilpotent P := hP.isNilpotent
  unfold frattini Order.radical
  refine le_iInf₂ fun M hM => ?_
  have : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M
    (Group.normalizerCondition_of_isNilpotent (G := P)) hM
  have : IsSimpleGroup (P ⧸ M) := Group.isSimpleGroup_of_isCoatom hM
  have hprime : (Nat.card (P ⧸ M)).Prime := Group.is_simple_iff_prime_card.1 inferInstance
  have : Fact (Nat.card (P ⧸ M)).Prime := ⟨hprime⟩
  have : IsCyclic (P ⧸ M) := isCyclic_of_prime_card rfl
  rw [Subgroup.commutator_le]
  intro g _ h _
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem eq_top_of_sup_commutator_eq_top {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {K : Subgroup P} (h : K ⊔ ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤) :
    K = ⊤ :=
  frattini_nongenerating (eq_top_iff.2 (h ▸ sup_le_sup_left (commutator_top_le_frattini hP) K))

variable {G : Type*} [Group G]

theorem eq_of_sup_commutator_eq {p : ℕ} [Fact p.Prime] {U K : Subgroup G} [Finite U]
    (hU : IsPGroup p U) (hKU : K ≤ U) (h : K ⊔ ⁅U, U⁆ = U) : K = U := by
  have hmap : (K.subgroupOf U ⊔ ⁅(⊤ : Subgroup U), (⊤ : Subgroup U)⁆).map U.subtype =
      (⊤ : Subgroup U).map U.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hKU, h]
  have h1 : K.subgroupOf U ⊔ ⁅(⊤ : Subgroup U), (⊤ : Subgroup U)⁆ = ⊤ :=
    Subgroup.map_injective U.subtype_injective hmap
  have h2 := eq_top_of_sup_commutator_eq_top hU h1
  rw [Subgroup.subgroupOf_eq_top] at h2
  exact le_antisymm hKU h2

theorem mem_normalizer_sup {y : G} {A B : Subgroup G}
    (hA : y ∈ Subgroup.normalizer (A : Set G)) (hB : y ∈ Subgroup.normalizer (B : Set G)) :
    y ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ z : G, z ∈ Subgroup.normalizer (A : Set G) → z ∈ Subgroup.normalizer (B : Set G) →
      ∀ x ∈ A ⊔ B, z * x * z⁻¹ ∈ A ⊔ B := by
    intro z hzA hzB
    have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj z).toMonoidHom :=
      sup_le (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hzA a).1 ha))
        (fun b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hzB b).1 hb))
    exact fun x hx => h hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key y hA hB x, fun hx => ?_⟩
  have := key y⁻¹ (inv_mem hA) (inv_mem hB) _ hx
  simpa [mul_assoc] using this

@[expose] def IrrAct (y : G) (U Z : Subgroup G) : Prop :=
  Z ≤ U ∧ ∀ W : Subgroup G, Z ≤ W → W ≤ U → y ∈ Subgroup.normalizer (W : Set G) → W = Z ∨ W = U

theorem IrrAct.le_or_sup_eq {y : G} {U Z : Subgroup G} (h : IrrAct y U Z) {K : Subgroup G}
    (hKU : K ≤ U) (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hyZ : y ∈ Subgroup.normalizer (Z : Set G)) : K ≤ Z ∨ K ⊔ Z = U := by
  rcases h.2 (K ⊔ Z) le_sup_right (sup_le hKU h.1) (mem_normalizer_sup hyK hyZ) with h1 | h1
  · exact Or.inl (le_sup_left.trans h1.le)
  · exact Or.inr h1

theorem mem_normalizer_of_powerMap [Finite G] {y : G} {U Z W : Subgroup G} (hZW : Z ≤ W)
    (hpow : ∀ u ∈ U, ∃ k : ℕ, y * u * y⁻¹ * (u ^ k)⁻¹ ∈ Z) (hWU : W ≤ U) :
    y ∈ Subgroup.normalizer (W : Set G) := by
  have hle : ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro w hw
    obtain ⟨k, hk⟩ := hpow w (hWU hw)
    have : y * w * y⁻¹ = (y * w * y⁻¹ * (w ^ k)⁻¹) * w ^ k := by group
    rw [this]
    exact mul_mem (hZW hk) (pow_mem hw k)
  have hmap : W.map (MulAut.conj y).toMonoidHom ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact hle w hw
  have heq : W.map (MulAut.conj y).toMonoidHom = W :=
    Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hle x hx, fun hx => ?_⟩
  have hx' : y * x * y⁻¹ ∈ W.map (MulAut.conj y).toMonoidHom := by
    rw [heq]
    exact hx
  obtain ⟨w, hw, hwx⟩ := hx'
  have h2 : y * w * y⁻¹ = y * x * y⁻¹ := hwx
  have : w = x := by
    have := congrArg (fun t => y⁻¹ * t * y) h2
    simpa [mul_assoc] using this
  rwa [this] at hw

theorem map_conj_eq_of_mem_normalizer {y : G} {A : Subgroup G}
    (h : y ∈ Subgroup.normalizer (A : Set G)) : A.map (MulAut.conj y).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 h w).1 hw
  · intro hx
    refine ⟨y⁻¹ * x * y, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.1 h (y⁻¹ * x * y)).2 (by simpa [mul_assoc] using hx)
    exact this

theorem mem_normalizer_of_map_conj_eq {y : G} {A : Subgroup G}
    (h : A.map (MulAut.conj y).toMonoidHom = A) : y ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have : y * x * y⁻¹ ∈ A.map (MulAut.conj y).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at this
  · have hx' : y * x * y⁻¹ ∈ A.map (MulAut.conj y).toMonoidHom := by
      rw [h]
      exact hx
    obtain ⟨w, hw, hwx⟩ := hx'
    have h2 : y * w * y⁻¹ = y * x * y⁻¹ := hwx
    have : w = x := by
      have := congrArg (fun t => y⁻¹ * t * y) h2
      simpa [mul_assoc] using this
    rwa [this] at hw

theorem mem_normalizer_commutator {y : G} {A B : Subgroup G}
    (hA : y ∈ Subgroup.normalizer (A : Set G)) (hB : y ∈ Subgroup.normalizer (B : Set G)) :
    y ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]

theorem exists_zpowers_eq_of_isCyclic (K : Subgroup G) [IsCyclic K] :
    ∃ g ∈ K, K = Subgroup.zpowers g := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  refine ⟨g, g.2, le_antisymm (fun x hx => ?_) ((Subgroup.zpowers_le).2 g.2)⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
  exact Subgroup.mem_zpowers_iff.2 ⟨n, congrArg Subtype.val hn⟩

theorem closure_pair_self (a : G) : Subgroup.closure {a, a} = Subgroup.zpowers a := by
  rw [Set.pair_eq_singleton, Subgroup.zpowers_eq_closure]

end CFSG.AGLEmbedding.ParabAutIrr
