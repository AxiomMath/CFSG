module

public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def conjAct (N : Subgroup G) (X : Set G) (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) :
    ↥N →* Equiv.Perm ↥X where
  toFun n :=
    Equiv.subtypeEquiv (MulAut.conj (n : G)).toEquiv (fun x => by
      simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply]
      constructor
      · exact fun hx => hX n n.2 x hx
      · intro hx
        have h1 := hX ((n : G)⁻¹) (inv_mem n.2) _ hx
        simpa [mul_assoc] using h1)
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro n m
    ext x
    simp [mul_assoc]

theorem conjAct_apply (N : Subgroup G) (X : Set G) (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (n : ↥N) (x : ↥X) : ((conjAct N X hX n x : ↥X) : G) = (n : G) * x * (n : G)⁻¹ := rfl

theorem conjAct_eq_one_iff (N : Subgroup G) (X : Set G) (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (n : ↥N) : conjAct N X hX n = 1 ↔ ∀ x ∈ X, (n : G) * x * (n : G)⁻¹ = x := by
  constructor
  · intro h x hx
    have := congrArg (fun σ : Equiv.Perm ↥X => ((σ ⟨x, hx⟩ : ↥X) : G)) h
    simp only [conjAct_apply, Equiv.Perm.coe_one, id_eq] at this
    exact this
  · intro h
    ext x
    simp only [conjAct_apply, Equiv.Perm.coe_one, id_eq]
    exact h x x.2

@[expose] def nonid (F : Subgroup G) : Set G := {f | f ∈ F ∧ f ≠ 1}

theorem conj_mem_nonid {N F : Subgroup G} (hNF : ∀ n ∈ N, ∀ f ∈ F, n * f * n⁻¹ ∈ F) :
    ∀ n ∈ N, ∀ x ∈ nonid F, n * x * n⁻¹ ∈ nonid F := by
  intro n hn x hx
  refine ⟨hNF n hn x hx.1, fun h => hx.2 ?_⟩
  calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
    _ = 1 := by rw [h]; group

theorem card_nonid {F : Subgroup G} (hF : Nat.card F = 4) : Nat.card ↥(nonid F) = 3 := by
  have hset : nonid F = (F : Set G) \ {1} := by
    ext f
    simp [nonid, Set.mem_diff]
  rw [hset, Nat.card_coe_set_eq,
    Set.ncard_diff_singleton_of_mem (by simp : (1 : G) ∈ (F : Set G))]
  have h4 : (F : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hF
  omega

theorem centralizer_nonid (F : Subgroup G) :
    centralizer (nonid F) = centralizer (F : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h f hf
    by_cases hf1 : f = 1
    · rw [hf1]
      simp
    · exact h f ⟨hf, hf1⟩
  · intro h f hf
    exact h f hf.1

theorem perm_fin3_aux : ∀ σ u : Equiv.Perm (Fin 3),
    (u ^ 3 = 1 ∧ u ≠ 1 ∧ σ ^ 2 = 1 ∧ (u * σ * u⁻¹ * σ⁻¹) ^ 2 = 1) → σ = 1 := by
  decide +kernel

theorem perm_three_comm_aux {X : Type} [Finite X] (hX : Nat.card X = 3) (σ u : Equiv.Perm X)
    (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (hσ2 : σ ^ 2 = 1) (hc : (u * σ * u⁻¹ * σ⁻¹) ^ 2 = 1) :
    σ = 1 := by
  have : Fintype X := Fintype.ofFinite X
  have hX' : Fintype.card X = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hX
  let e : X ≃ Fin 3 := Fintype.equivFinOfCardEq hX'
  let E : Equiv.Perm X ≃* Equiv.Perm (Fin 3) := Equiv.permCongrHom e
  have hc' : (E u * E σ * (E u)⁻¹ * (E σ)⁻¹) ^ 2 = 1 := by
    have := congrArg E hc
    simpa [map_mul, map_inv, map_pow] using this
  have h := perm_fin3_aux (E σ) (E u) ⟨by rw [← map_pow, hu3, map_one],
    fun h => hu1 (E.injective (by rw [h, map_one])), by rw [← map_pow, hσ2, map_one], hc'⟩
  exact E.injective (by rw [h, map_one])

theorem card_perm_three {X : Type} [Finite X] (hX : Nat.card X = 3) :
    Nat.card (Equiv.Perm X) = 6 := by
  rw [Nat.card_perm, hX]
  norm_num [Nat.factorial]

theorem perm_sq_eq_one_of_two_pow {X : Type} [Finite X] (hX : Nat.card X = 3)
    (σ : Equiv.Perm X) {k : ℕ} (h : σ ^ 2 ^ k = 1) : σ ^ 2 = 1 := by
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  have h6 : orderOf σ ∣ 6 := by
    have := orderOf_dvd_natCard σ
    rwa [card_perm_three hX] at this
  rw [hj'] at h6
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    exact absurd (h4.trans h6) (by norm_num)
  have : orderOf σ ∣ 2 := by
    rw [hj']
    exact (Nat.pow_dvd_pow 2 hj1).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem conjAct_surjective_of_card_three {K : Subgroup G} {X : Set G}
    (hX : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ ∈ X) (hcard : Nat.card X = 3) {ρ lam : G}
    (hρ : ρ ∈ K) (hl : lam ∈ K) (hρ3 : ρ ^ 3 = 1) (hl2 : lam * lam = 1)
    (hρm : ∃ x ∈ X, ρ * x * ρ⁻¹ ≠ x) (hlm : ∃ x ∈ X, lam * x * lam⁻¹ ≠ x) :
    Function.Surjective (conjAct K X hX) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha3 : (conjAct K X hX ⟨ρ, hρ⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨ρ, hρ⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hρ3)
    rw [this, map_one]
  have ha1 : conjAct K X hX ⟨ρ, hρ⟩ ≠ 1 := by
    intro h
    obtain ⟨x, hx, hne⟩ := hρm
    exact hne ((conjAct_eq_one_iff K X hX _).mp h x hx)
  have hb2 : (conjAct K X hX ⟨lam, hl⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨lam, hl⟩ : ↥K) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hl2)
    rw [this, map_one]
  have hb1 : conjAct K X hX ⟨lam, hl⟩ ≠ 1 := by
    intro h
    obtain ⟨x, hx, hne⟩ := hlm
    exact hne ((conjAct_eq_one_iff K X hX _).mp h x hx)
  have ho3 : orderOf (conjAct K X hX ⟨ρ, hρ⟩) = 3 := orderOf_eq_prime ha3 ha1
  have ho2 : orderOf (conjAct K X hX ⟨lam, hl⟩) = 2 := orderOf_eq_prime hb2 hb1
  have h3 : 3 ∣ Nat.card (conjAct K X hX).range := by
    have := Subgroup.orderOf_dvd_natCard (conjAct K X hX).range
      (MonoidHom.mem_range.mpr ⟨⟨ρ, hρ⟩, rfl⟩)
    rwa [ho3] at this
  have h2 : 2 ∣ Nat.card (conjAct K X hX).range := by
    have := Subgroup.orderOf_dvd_natCard (conjAct K X hX).range
      (MonoidHom.mem_range.mpr ⟨⟨lam, hl⟩, rfl⟩)
    rwa [ho2] at this
  have h6 : 6 ∣ Nat.card (conjAct K X hX).range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3
  have hdvd : Nat.card (conjAct K X hX).range ∣ Nat.card (Equiv.Perm ↥X) :=
    Subgroup.card_subgroup_dvd_card _
  have hperm : Nat.card (Equiv.Perm ↥X) = 6 := card_perm_three hcard
  have hr : Nat.card (conjAct K X hX).range = 6 :=
    Nat.dvd_antisymm (hperm ▸ hdvd) h6
  have htop : (conjAct K X hX).range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (hr.trans hperm.symm)
  exact MonoidHom.range_eq_top.mp htop

theorem exists_conj_of_surjective {N : Subgroup G} {X : Set G}
    (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) (hs : Function.Surjective (conjAct N X hX))
    (σ : Equiv.Perm ↥X) : ∃ n ∈ N, ∀ x : ↥X, ((σ x : ↥X) : G) = n * x * n⁻¹ := by
  obtain ⟨n, rfl⟩ := hs σ
  exact ⟨n, n.2, fun x => rfl⟩

theorem surjective_of_exists_conj {N : Subgroup G} {X : Set G}
    (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (h : ∀ σ : Equiv.Perm ↥X, ∃ n ∈ N, ∀ x : ↥X, ((σ x : ↥X) : G) = n * x * n⁻¹) :
    Function.Surjective (conjAct N X hX) := by
  intro σ
  obtain ⟨n, hn, hσ⟩ := h σ
  refine ⟨⟨n, hn⟩, ?_⟩
  ext x
  exact (hσ x).symm

theorem centralizes_of_normal_two {N Q : Subgroup G} {X : Set G}
    (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) (hcard : Nat.card X = 3) (hQN : Q ≤ N)
    (hnorm : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q) (hQ : IsPGroup 2 Q) {ρ : G} (hρ : ρ ∈ N)
    (hρ3 : ρ ^ 3 = 1) (hρm : ∃ x ∈ X, ρ * x * ρ⁻¹ ≠ x) :
    ∀ q ∈ Q, ∀ x ∈ X, q * x * q⁻¹ = x := by
  intro q hq
  have hsq : ∀ q' (hq' : q' ∈ Q), (conjAct N X hX ⟨q', hQN hq'⟩) ^ 2 = 1 := by
    intro q' hq'
    obtain ⟨k, hk⟩ := hQ ⟨q', hq'⟩
    refine perm_sq_eq_one_of_two_pow hcard _ (k := k) ?_
    rw [← map_pow]
    have : (⟨q', hQN hq'⟩ : ↥N) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, map_one]
  have hu3 : (conjAct N X hX ⟨ρ, hρ⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨ρ, hρ⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hρ3)
    rw [this, map_one]
  have hu1 : conjAct N X hX ⟨ρ, hρ⟩ ≠ 1 := by
    intro h
    obtain ⟨x, hx, hne⟩ := hρm
    exact hne ((conjAct_eq_one_iff N X hX _).mp h x hx)
  have hqN : q ∈ N := hQN hq
  have hcQ : ρ * q * ρ⁻¹ * q⁻¹ ∈ Q :=
    Subgroup.mul_mem _ (hnorm ρ hρ q hq) (Subgroup.inv_mem _ hq)
  have hc : ((conjAct N X hX ⟨ρ, hρ⟩) * (conjAct N X hX ⟨q, hqN⟩) *
      (conjAct N X hX ⟨ρ, hρ⟩)⁻¹ * (conjAct N X hX ⟨q, hqN⟩)⁻¹) ^ 2 = 1 := by
    have h2 := hsq _ hcQ
    have e : (⟨ρ * q * ρ⁻¹ * q⁻¹, hQN hcQ⟩ : ↥N) =
        ⟨ρ, hρ⟩ * ⟨q, hqN⟩ * ⟨ρ, hρ⟩⁻¹ * ⟨q, hqN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact h2
  have h1 : conjAct N X hX ⟨q, hqN⟩ = 1 :=
    perm_three_comm_aux hcard _ _ hu3 hu1 (hsq q hq) hc
  intro x hx
  exact (conjAct_eq_one_iff N X hX _).mp h1 x hx

theorem card_eq_six_mul {N : Subgroup G} {X : Set G} (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hcard : Nat.card X = 3) (hsurj : Function.Surjective (conjAct N X hX)) :
    Nat.card N = 6 * Nat.card ↥(N ⊓ centralizer X) := by
  have hker : (conjAct N X hX).ker = (N ⊓ centralizer X).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, conjAct_eq_one_iff N X hX n, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨n.2, fun x hx => ?_⟩
      have := h x hx
      calc x * (n : G) = ((n : G) * x * (n : G)⁻¹) * (n : G) := by rw [this]
        _ = (n : G) * x := by group
    · rintro ⟨-, h⟩ x hx
      have hc := h x hx
      calc (n : G) * x * (n : G)⁻¹ = (x * (n : G)) * (n : G)⁻¹ := by rw [← hc]
        _ = x := by group
  have h1 := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker, card_perm_three hcard,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ centralizer X ≤ N)).toEquiv]
    at h1
  omega

theorem exists_mul_centralizes {N K : Subgroup G} {X : Set G}
    (hX : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hK : ∀ σ : Equiv.Perm ↥X, ∃ k ∈ K, ∀ x : ↥X, ((σ x : ↥X) : G) = k * x * k⁻¹)
    {n : G} (hn : n ∈ N) : ∃ k ∈ K, ∀ x ∈ X, (n * k) * x * (n * k)⁻¹ = x := by
  obtain ⟨k, hk, hkx⟩ := hK ((conjAct N X hX ⟨n, hn⟩)⁻¹)
  refine ⟨k, hk, fun x hx => ?_⟩
  have h1 := hkx ⟨x, hx⟩
  have h2 : (((conjAct N X hX ⟨n, hn⟩)⁻¹ ⟨x, hx⟩ : ↥X) : G) = n⁻¹ * x * (n⁻¹)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [h2] at h1
  calc (n * k) * x * (n * k)⁻¹ = n * (k * x * k⁻¹) * n⁻¹ := by group
    _ = n * (n⁻¹ * x * (n⁻¹)⁻¹) * n⁻¹ := by rw [← h1]
    _ = x := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
