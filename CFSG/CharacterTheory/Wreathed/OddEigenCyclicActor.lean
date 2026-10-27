module

public import CFSG.CharacterTheory.Wreathed.OddEigenCyclicActorSupport
public import CFSG.CharacterTheory.Wreathed.BrauerWongOmega
public import CFSG.CharacterTheory.Wreathed.SplitCyclicActor

public section

namespace CFSG.Wreathed.OddEigenCyclicActor

open scoped Pointwise

universe u

theorem odd_eigensubgroup_cyclic_actor_centralizer_has_quaternion_factorization
    {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (E : Subgroup G) (hE : E ≠ ⊥) (hEodd : Odd (Nat.card E))
    (A : Subgroup G) (hAE : A ≤ Subgroup.normalizer (E : Set G)) (hAc : IsCyclic A)
    (hAcard : Nat.card A = 2 ^ n)
    (a : G) (haA : a ∈ A) (ha2 : orderOf a = 2) (hinv : ∀ x ∈ E, a * x * a⁻¹ = x⁻¹) :
    let K := Subgroup.centralizer (E : Set G)
    ((∃ N : Subgroup K, N.Normal ∧ Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k) ∨
      ((∀ P : Sylow 2 K, Nonempty ((P : Subgroup K) ≃* Original.Y (2 ^ n)) ∧
          Nat.card P = 2 * 2 ^ n) ∧
        (¬ ∃ K₀ : Subgroup K, K₀.Normal ∧ K₀.index = 2) ∧
        ∀ i : K, orderOf i = 2 → CFSG.oddCore K ⊔ Subgroup.centralizer ({i} : Set K) = ⊤)) ∧
    ∀ i u : K, orderOf i = 2 → Odd (orderOf u) → i * u * i⁻¹ = u⁻¹ →
      u ∈ CFSG.oddCore K := by
  intro K
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    hAE.trans (BrauerWong.normalizer_le_normalizer_centralizer E)
  have hKAbot : K ⊓ A = ⊥ := centralizer_inf_eq_bot E A hE hEodd hAc hAcard a haA ha2 hinv
  let H := K ⊔ A
  have hKH : K ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hK₁ : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (sup_le Subgroup.le_normalizer hAK)
  have hA₁c : IsCyclic (A.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hAH).isCyclic.mpr hAc
  have hA₁card : Nat.card (A.subgroupOf H) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hAcard]
  have hsup : K.subgroupOf H ⊔ A.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hAH, Subgroup.map_top, Subgroup.range_subtype]
  have hinf : K.subgroupOf H ⊓ A.subgroupOf H = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxA⟩
    have hx : (x : G) ∈ K ⊓ A := ⟨hxK, hxA⟩
    rw [hKAbot, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr (Subtype.ext hx)
  let P₀ : Sylow 2 H := default
  let φ : (P₀ : Subgroup H) →* G := H.subtype.comp (P₀ : Subgroup H).subtype
  have hφ : Function.Injective φ := H.subtype_injective.comp (P₀ : Subgroup H).subtype_injective
  obtain ⟨T, hT⟩ := (P₀.isPGroup'.map H.subtype).exists_le_sylow
  let ι : (P₀ : Subgroup H) →* (T : Subgroup G) := φ.codRestrict (T : Subgroup G)
    (fun p => hT ⟨p, p.property, rfl⟩)
  have hι : Function.Injective ι := by
    intro p q hpq
    have h1 := congrArg (fun x : (T : Subgroup G) => (x : G)) hpq
    exact hφ h1
  let ψ : (P₀ : Subgroup H) →* Wreath (2 ^ n) :=
    e.toMonoidHom.comp ((Sylow.equiv T S).toMonoidHom.comp ι)
  have hψ : Function.Injective ψ := e.injective.comp ((Sylow.equiv T S).injective.comp hι)
  have hsplit :=
    @SplitCyclicActor.split_maximal_cyclic_actor_forces_quaternion_kernel_or_odd_complement
      H _ _ n hn P₀ ψ hψ (K.subgroupOf H) (A.subgroupOf H) hK₁ hA₁c hA₁card hsup hinf
  let f : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  have hmain : (∃ N : Subgroup K, N.Normal ∧ Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k) ∨
      ((∀ P : Sylow 2 K, Nonempty ((P : Subgroup K) ≃* Original.Y (2 ^ n)) ∧
          Nat.card P = 2 * 2 ^ n) ∧
        (¬ ∃ K₀ : Subgroup K, K₀.Normal ∧ K₀.index = 2) ∧
        ∀ i : K, orderOf i = 2 → CFSG.oddCore K ⊔ Subgroup.centralizer ({i} : Set K) = ⊤) := by
    rcases hsplit with ⟨N, hN, hodd, hidx⟩ | ⟨hsyl, hno2, hfac⟩
    · left
      have := hN
      exact normal_two_complement_of_equiv f
        (normal_two_complement_subgroupOf N hodd hidx (K.subgroupOf H))
    · right
      exact ⟨sylow_quaternion_of_equiv n f hsyl, no_index_two_of_equiv f hno2,
        involution_factorization_of_equiv f hfac⟩
  refine ⟨hmain, ?_⟩
  intro i u hi hu hiu
  rcases hmain with h | ⟨-, -, hfac⟩
  · exact mem_oddCore_of_normal_two_complement h u hu
  · exact mem_oddCore_of_inverted_of_factorization i u (hfac i hi) hu hiu

end CFSG.Wreathed.OddEigenCyclicActor
