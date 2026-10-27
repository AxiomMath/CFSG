module

public import CFSG.YGroups.DoubleCosetPoints
public import Mathlib.Data.Set.Card.Arithmetic

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBFiveCent

open Subgroup CFSG.YGroups

theorem ncard_orderOf_le {K : Type*} [Group K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (Q : Sylow p K) :
    {x : K | orderOf x = p}.ncard ≤ Nat.card (Sylow p K) * (Nat.card Q - 1) := by
  classical
  haveI : Fintype (Sylow p K) := Fintype.ofFinite _
  have hsub : {x : K | orderOf x = p} ⊆
      ⋃ R ∈ (Finset.univ : Finset (Sylow p K)), ((R : Set K) \ {1}) := by
    intro x hx
    have hx' : orderOf x = p := hx
    have hpg : IsPGroup p (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx', pow_one])
    obtain ⟨R, hR⟩ := hpg.exists_le_sylow
    refine Set.mem_biUnion (Finset.mem_univ R) ⟨hR (mem_zpowers x), ?_⟩
    intro h1
    rw [Set.mem_singleton_iff] at h1
    rw [h1, orderOf_one] at hx'
    exact hp.out.one_lt.ne hx'
  calc {x : K | orderOf x = p}.ncard
      ≤ (⋃ R ∈ (Finset.univ : Finset (Sylow p K)), ((R : Set K) \ {1})).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ∑ R ∈ (Finset.univ : Finset (Sylow p K)), ((R : Set K) \ {1}).ncard :=
        Finset.set_ncard_biUnion_le _ _
    _ = ∑ _R ∈ (Finset.univ : Finset (Sylow p K)), (Nat.card Q - 1) := by
        refine Finset.sum_congr rfl fun R _ => ?_
        have h1 : (1 : K) ∈ (R : Set K) := (R : Subgroup K).one_mem
        rw [Set.ncard_diff_singleton_of_mem h1]
        have h2 : ((R : Set K)).ncard = Nat.card (R : Subgroup K) := by
          rw [← Nat.card_coe_set_eq]
          rfl
        rw [h2, Sylow.card_eq_multiplicity R, Sylow.card_eq_multiplicity Q]
    _ = Nat.card (Sylow p K) * (Nat.card Q - 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Nat.card_eq_fintype_card (α := Sylow p K)]

theorem ncard_orderOf_le_of_normalizer {G : Type*} [Group G] [Finite G] {p a : ℕ}
    [hp : Fact p.Prime] {K P N : Subgroup G} (hPK : P ≤ K) (hNK : N ≤ K)
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : p ^ a ≤ Nat.card P)
    (hK : ¬ p ^ (a + 1) ∣ Nat.card K) (hN : N ≤ Subgroup.normalizer (P : Set G)) :
    {σ : G | σ ∈ K ∧ orderOf σ = p}.ncard ≤ Nat.card K / Nat.card N * (p ^ a - 1) := by
  classical
  have hP' : IsPGroup p ↥(P.subgroupOf K) := fun g => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    exact hexp _ g.2⟩
  have hPc : Nat.card ↥(P.subgroupOf K) = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv
  have hNc : Nat.card ↥(N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNK).toEquiv
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP'
  rw [hPc] at hm
  have hdvd : Nat.card P ∣ Nat.card K := Subgroup.card_dvd_of_le hPK
  have hma : m = a := by
    have h1 : a ≤ m := by
      rw [hm] at hcard
      exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hcard
    by_contra hne
    apply hK
    exact (pow_dvd_pow p (by omega : a + 1 ≤ m)).trans (hm ▸ hdvd)
  subst hma
  have hidx : ¬ p ∣ (P.subgroupOf K).index := by
    intro hpi
    apply hK
    have hmul := Subgroup.card_mul_index (P.subgroupOf K)
    rw [hPc, hm] at hmul
    rw [pow_succ, ← hmul]
    exact Nat.mul_dvd_mul_left _ hpi
  set Q := hP'.toSylow hidx with hQ
  have hQc : (Q : Subgroup ↥K) = P.subgroupOf K := IsPGroup.toSylow_coe hP' hidx
  have hNQ : N.subgroupOf K ≤ Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K) := by
    intro n hn
    rw [hQc, Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.1 (hN (Subgroup.mem_subgroupOf.1 hn))) (h : G)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hsyl := Sylow.card_eq_index_normalizer Q
  have hmul := Subgroup.index_mul_card (Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K))
  have hNle := Subgroup.card_le_of_le hNQ
  rw [hNc] at hNle
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hcount : Nat.card (Sylow p ↥K) ≤ Nat.card K / Nat.card N := by
    rw [Nat.le_div_iff_mul_le hNpos, hsyl]
    calc (Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K)).index * Nat.card N
        ≤ (Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K)).index *
            Nat.card (Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K)) :=
          Nat.mul_le_mul_left _ hNle
      _ = Nat.card K := hmul
  have himg : {σ : G | σ ∈ K ∧ orderOf σ = p} = Subtype.val '' {x : ↥K | orderOf x = p} := by
    ext σ
    constructor
    · rintro ⟨hσ, ho⟩
      exact ⟨⟨σ, hσ⟩, by rwa [Set.mem_setOf_eq, Subgroup.orderOf_mk], rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, by rwa [Set.mem_setOf_eq, Subgroup.orderOf_coe] at *⟩
  rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hQcard : Nat.card Q = p ^ m := by
    rw [← hm, ← hPc]
    exact congrArg (fun H : Subgroup ↥K => Nat.card H) hQc
  calc {x : ↥K | orderOf x = p}.ncard ≤ Nat.card (Sylow p ↥K) * (Nat.card Q - 1) :=
        ncard_orderOf_le Q
    _ ≤ Nat.card K / Nat.card N * (p ^ m - 1) := by
        rw [hQcard]
        exact Nat.mul_le_mul_right _ hcount

theorem pow_eq_one_of_mem_closure {G : Type*} [Group G] {p : ℕ} {S : Set G}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hS : ∀ x ∈ S, x ^ p = 1) :
    ∀ x ∈ closure S, x ^ p = 1 := by
  have hc : ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := fun x hx y hy =>
    Set.centralizer_centralizer_comm_of_comm (fun a ha b hb _ => hcomm a ha b hb) x
      (closure_le_centralizer_centralizer S hx) y (closure_le_centralizer_centralizer S hy)
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy => rw [(Commute.mul_pow (hc x hx y hy) p), ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem closure_le_normalizer {G : Type*} [Group G] [Finite G] {S T : Set G}
    (hT : ∀ n ∈ T, ∀ g ∈ S, n * g * n⁻¹ ∈ closure S) :
    closure T ≤ Subgroup.normalizer ((closure S : Subgroup G) : Set G) := by
  rw [closure_le]
  intro n hn
  set P := closure S with hP
  have hmap : ∀ x ∈ P, n * x * n⁻¹ ∈ P := by
    have hle : P ≤ P.comap (MulAut.conj n).toMonoidHom := by
      rw [hP, closure_le]
      intro g hg
      exact hT n hn g hg
    intro x hx
    exact hle hx
  let f : P → P := fun x => ⟨n * x * n⁻¹, hmap x x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : n * (x : G) * n⁻¹ = n * y * n⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h1)
  have hfs : Function.Surjective f := Finite.injective_iff_surjective.1 hf
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hmap h hh, fun hh => ?_⟩
  obtain ⟨y, hy⟩ := hfs ⟨n * h * n⁻¹, hh⟩
  have h1 : n * (y : G) * n⁻¹ = n * h * n⁻¹ := congrArg Subtype.val hy
  have h2 : (y : G) = h := by simpa using h1
  rw [← h2]
  exact y.2

theorem card_chainStab_le_step {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (β : ℕ → Fin n)
    (l : ℕ) :
    Nat.card (chainStab S β l) ≤
      (MulAction.orbit (chainStab S β l) (β l)).ncard * Nat.card (chainStab S β (l + 1)) := by
  set Z := chainStab S β l with hZ
  have h2 : Nat.card (MulAction.orbit Z (β l)) * Nat.card (MulAction.stabilizer Z (β l)) =
      Nat.card Z := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Z (β l))]
  have h3 : Nat.card (MulAction.stabilizer Z (β l)) = Nat.card (chainStab S β (l + 1)) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.1, g.1.2.1, fun m hm => ?_⟩
        invFun := fun g => ⟨⟨g.1, g.2.1, fun m hm => g.2.2 m (by omega)⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | rfl
      · exact g.1.2.2 m h
      · exact MulAction.mem_stabilizer_iff.1 g.2
    · exact g.2.2 l (Nat.lt_succ_self l)
  rw [← h2, ← h3, Nat.card_coe_set_eq]

theorem card_le_prod_of_chain {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (k : ℕ)
    (β : ℕ → Fin n) (a : ℕ → ℕ)
    (ha : ∀ l < k, (MulAction.orbit (chainStab S β l) (β l)).ncard ≤ a l)
    (hbot : chainStab S β k = ⊥) :
    Nat.card S ≤ ∏ l ∈ Finset.range k, a l := by
  have key : ∀ j ≤ k, Nat.card S ≤ (∏ l ∈ Finset.range j, a l) * Nat.card (chainStab S β j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [chainStab_zero]
      simp
    | succ j ih =>
      intro hj
      calc Nat.card S ≤ (∏ l ∈ Finset.range j, a l) * Nat.card (chainStab S β j) := ih (by omega)
        _ ≤ (∏ l ∈ Finset.range j, a l) *
            ((MulAction.orbit (chainStab S β j) (β j)).ncard *
              Nat.card (chainStab S β (j + 1))) :=
          Nat.mul_le_mul_left _ (card_chainStab_le_step S β j)
        _ ≤ (∏ l ∈ Finset.range j, a l) * (a j * Nat.card (chainStab S β (j + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (ha j (by omega)))
        _ = (∏ l ∈ Finset.range (j + 1), a l) * Nat.card (chainStab S β (j + 1)) := by
          rw [Finset.prod_range_succ]
          ring
  have h := key k le_rfl
  rwa [hbot, Subgroup.card_bot, mul_one] at h

end CFSG.HardMathSupport.Dickson.I271.TabBFiveCent
