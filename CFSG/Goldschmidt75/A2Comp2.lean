module

public import CFSG.Goldschmidt75.A2Comp
public import CFSG.Goldschmidt75.A2TypeI

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_odd_index_of_isPGroup {Y H : Subgroup G} (hY : IsPGroup 2 Y)
    (hodd : Odd (H.subgroupOf Y).index) : Y ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  have hdvd : (H.subgroupOf Y).index ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card _
  obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm0 : m = 0 := by
    by_contra hne
    rw [hm'] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
  rw [hm0, pow_zero, Subgroup.index_eq_one] at hm'
  intro y hy
  have : (⟨y, hy⟩ : Y) ∈ H.subgroupOf Y := hm' ▸ mem_top _
  exact mem_subgroupOf.mp this

namespace A2Comp

variable {T : Sylow 2 G} {S₁ S₂ K : Subgroup G}

theorem inner_typeII
    (h : A2Comp T S₁ S₂ K) (hII : IsGoldTypeII K) :
    S₁ ≤ K ⊔ centralizer (K : Set G) := by
  have : K.Normal := h.normal
  obtain ⟨hΩK, hΩab, hΩ2, hΩmax, -⟩ :=
    G3b.sstar_typeII_facts h.quasi hII h.sstar h.omega1_ne_bot
  have hYA : S₁ ≤ centralizer (Omega1 ((T : Subgroup G) ⊓ K) : Set G) :=
    h.le_centralizer₁.trans (centralizer_le h.omega1_le)
  have hS₁p : IsPGroup 2 S₁ := T.isPGroup'.to_le h.le₁
  rcases hII.2 with ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩ | hJR
  · have := hp
    exact le_of_odd_index_of_isPGroup hS₁p
      (G3b.G35_one_L2 h.quasi e hpodd hf h5 h8 hΩK hΩab hΩ2 hΩmax hYA).1
  · exact le_of_odd_index_of_isPGroup hS₁p
      (G3b.G35_one_JR h.quasi hII.1 hJR hΩK hΩab hΩ2 hΩmax h.omega1_ne_bot hYA).1

theorem le_inf_of_typeII
    (h : A2Comp T S₁ S₂ K) (hII : IsGoldTypeII K) :
    (T : Subgroup G) ⊓ K ≤ S₁ ⊓ S₂ := by
  have : K.Normal := h.normal
  obtain ⟨-, -, -, hΩmax, -⟩ := G3b.sstar_typeII_facts h.quasi hII h.sstar h.omega1_ne_bot
  have heq := hΩmax _ inf_le_right (T.isPGroup'.to_le inf_le_left) (omega1_le_self _)
  rw [heq]
  exact h.omega1_le

theorem dichotomy_typeI
    (h : A2Comp T S₁ S₂ K) (hI : IsGoldTypeI K) :
    S₁ ⊓ ((T : Subgroup G) ⊓ K) = Omega1 ((T : Subgroup G) ⊓ K) ∨
      S₁ ⊓ ((T : Subgroup G) ⊓ K) = (T : Subgroup G) ⊓ K := by
  have : IsSimpleGroup K := h.isSimpleGroup
  obtain ⟨h1, -⟩ := typeI_facts_of_le hI h.center_eq h.sylowIn
  refine h1 _ inf_le_right (le_inf (h.omega1_le.trans inf_le_left) (omega1_le_self _)) ?_
  intro n _ hnR x hx
  refine mem_inf.mpr ⟨?_, hnR x (mem_inf.mp hx).2⟩
  exact h.sc₁ x (mem_inf.mp hx).1 n (mem_inf.mp (hnR x (mem_inf.mp hx).2)).1

theorem trichotomy
    (h : A2Comp T S₁ S₂ K) :
    (T : Subgroup G) ⊓ K ≤ S₁ ∨ (T : Subgroup G) ⊓ K ≤ S₂ ∨
      (IsGoldTypeI K ∧ S₁ ⊓ ((T : Subgroup G) ⊓ K) ≤ Omega1 ((T : Subgroup G) ⊓ K) ∧
        S₂ ⊓ ((T : Subgroup G) ⊓ K) ≤ Omega1 ((T : Subgroup G) ⊓ K)) := by
  rcases h.type with hI | hII
  · rcases h.dichotomy_typeI hI with h1 | h1
    · rcases h.symm.dichotomy_typeI hI with h2 | h2
      · exact Or.inr (Or.inr ⟨hI, h1.le, h2.le⟩)
      · right; left
        rw [← h2]
        exact inf_le_left
    · left
      rw [← h1]
      exact inf_le_left
  · exact Or.inl ((h.le_inf_of_typeII hII).trans inf_le_left)

theorem inner_typeI
    (h : A2Comp T S₁ S₂ K) (hI : IsGoldTypeI K)
    (hc : ∀ α ∈ S₁, ∀ t ∈ (T : Subgroup G) ⊓ K,
      α⁻¹ * t * α * t⁻¹ ∈ Omega1 ((T : Subgroup G) ⊓ K)) :
    S₁ ≤ K ⊔ centralizer (K : Set G) := by
  intro α hα
  have hα1 := G33 G K (Omega1 ((T : Subgroup G) ⊓ K)) ((T : Subgroup G) ⊓ K) h.normal h.quasi hI
    h.sstar h.normalClosureIn_eq h.sylowIn (omega1_le_self _) α
    (h.le_centralizer₁.trans (centralizer_le h.omega1_le) hα) (h.le_normalizer₁ hα) (hc α hα)
  have hle : (T : Subgroup G) ⊓ K ⊔ centralizer (K : Set G) ≤ K ⊔ centralizer (K : Set G) :=
    sup_le_sup_right inf_le_right _
  exact hle hα1

theorem inner
    (h : A2Comp T S₁ S₂ K) :
    S₁ ≤ K ⊔ centralizer (K : Set G) ∨ S₂ ≤ K ⊔ centralizer (K : Set G) := by
  rcases h.type with hI | hII
  · rcases h.dichotomy_typeI hI with h1 | h1
    · left
      refine h.inner_typeI hI fun α hα t ht => ?_
      rw [← h1]
      exact h.mem_inf_of_mem hα ht
    · right
      refine h.symm.inner_typeI hI fun α hα t ht => ?_
      have htS₁ : t ∈ S₁ := by
        rw [← h1] at ht
        exact (mem_inf.mp ht).1
      have hS₂C : S₂ ≤ centralizer (S₁ : Set G) := by
        rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
        exact h.comm
      have hct := mem_centralizer_iff.mp (hS₂C hα) t htS₁
      have e : α⁻¹ * t * α * t⁻¹ = 1 := by
        rw [mul_assoc α⁻¹, hct]
        group
      rw [e]
      exact one_mem _
  · exact Or.inl (h.inner_typeII hII)

theorem exists_borel
    (h : A2Comp T S₁ S₂ K) (hI : IsGoldTypeI K) :
    ∃ d ∈ K, (∀ r ∈ (T : Subgroup G) ⊓ K, d⁻¹ * r * d ∈ (T : Subgroup G) ⊓ K) ∧
      ∀ r ∈ (T : Subgroup G) ⊓ K, d⁻¹ * r * d = r → r = 1 := by
  have : IsSimpleGroup K := h.isSimpleGroup
  exact (typeI_facts_of_le hI h.center_eq h.sylowIn).2

end A2Comp

end CFSG.Goldschmidt75
