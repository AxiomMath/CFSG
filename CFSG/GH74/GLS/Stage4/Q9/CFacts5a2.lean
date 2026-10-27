module

public import CFSG.GH74.GLS.Stage4.Q9.CFacts5a1

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem fac7200_two : (7200 : ℕ).factorization 2 = 5 := by
  have : (7200 : ℕ) = 2 ^ 5 * (3 ^ 2 * 5 ^ 2) := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow,
    Nat.prime_two.factorization, Nat.prime_three.factorization, Nat.prime_five.factorization]
  simp

theorem card_inf_centralizer_of_mulEquiv {G H : Type*} [Group G] [Group H] {K : Subgroup G}
    (ψ : K ≃* H) {x : G} (hx : x ∈ K) :
    Nat.card ↥(K ⊓ centralizer ({x} : Set G)) = Nat.card ↥(centralizer ({ψ ⟨x, hx⟩} : Set H)) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun g => ⟨ψ ⟨g.1, g.2.1⟩, ?_⟩
      invFun := fun h => ⟨((ψ.symm h : K) : G), (ψ.symm h).2, ?_⟩
      left_inv := fun g => ?_
      right_inv := fun h => ?_ }
  · have hg := mem_centralizer_singleton_iff.mp g.2.2
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hg
  · have hh := mem_centralizer_singleton_iff.mp h.2
    refine mem_centralizer_singleton_iff.mpr ?_
    have : ψ.symm h * ⟨x, hx⟩ = ⟨x, hx⟩ * ψ.symm h := by
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hh
    exact congrArg Subtype.val this
  · apply Subtype.ext
    simp
  · apply Subtype.ext
    simp

theorem card_sup_mul_card_inf_of_commute {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    (h : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) :
    Nat.card ↥(H₁ ⊔ H₂) * Nat.card ↥(H₁ ⊓ H₂) = Nat.card H₁ * Nat.card H₂ := by
  have hle' : H₁ ≤ centralizer (H₂ : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (h x hx y hy).symm
  have hle : H₁ ≤ normalizer (H₂ : Set G) :=
    hle'.trans (Subgroup.centralizer_le_normalizer (H₂ : Set G))
  exact CFSG.ShultStronglyClosedTI.LinearChain.RootQuotientClasses.card_sup_mul_card_inf hle

namespace Q9Setting

variable {G : Type} [Group G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
  (S : Q9Setting G z K₁ K₂ F₁ F₂)

include S

theorem card_K₁_inf_centralizer_five :
    ∀ x ∈ K₁, orderOf x = 5 →
    Nat.card ↥(K₁ ⊓ centralizer ({x} : Set G)) = 10 := by
  intro x hx hx5
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  rw [card_inf_centralizer_of_mulEquiv ψ₁ hx]
  apply card_centralizer_order5
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx5]

theorem K₂_le_centralizer_of_mem₁ {x : G} (hx : x ∈ K₁) : K₂ ≤ centralizer ({x} : Set G) := by
  intro k hk
  rw [mem_centralizer_singleton_iff]
  exact (S.comm x hx k hk).symm

theorem t_comm_of_mem_Hs {x : G} (hx : x ∈ S.Hs) : S.t * x = x * S.t := by
  have h := S.Hs_le hx
  rw [mem_centralizer_iff] at h
  exact h S.t (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem card_C_inf_centralizer_five :
    ∀ x ∈ K₁ ⊓ S.Hs, orderOf x = 5 →
    Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G)) = 7200 := by
  intro x hxK hx5
  obtain ⟨hx, hxH⟩ := hxK
  have hxt := S.t_comm_of_mem_Hs hxH
  have hH₁ := S.card_K₁_inf_centralizer_five x hx hx5
  have hK₂x := S.K₂_le_centralizer_of_mem₁ hx
  set H₁ : Subgroup G := K₁ ⊓ centralizer ({x} : Set G) with hH₁def
  set Kx : Subgroup G := (K₁ ⊔ K₂) ⊓ centralizer ({x} : Set G) with hKxdef
  have hsup : H₁ ⊔ K₂ = Kx := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · exact inf_le_inf_right _ le_sup_left
      · exact le_inf le_sup_right hK₂x
    · intro g hg
      obtain ⟨hgK, hgx⟩ := hg
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Lemma82.mem_sup_of_commute S.comm hgK
      have hk₂x : k₂ ∈ centralizer ({x} : Set G) := hK₂x hk₂
      have hk₁x : k₁ ∈ centralizer ({x} : Set G) := by
        have : k₁ = k₁ * k₂ * k₂⁻¹ := by group
        rw [this]
        exact mul_mem hgx (inv_mem hk₂x)
      exact mul_mem (mem_sup_left ⟨hk₁, hk₁x⟩) (mem_sup_right hk₂)
  have hinf : H₁ ⊓ K₂ = zpowers z := by
    apply le_antisymm
    · intro g hg
      have : g ∈ K₁ ⊓ K₂ := ⟨hg.1.1, hg.2⟩
      rwa [S.inter_eq] at this
    · intro g hg
      have hgz : g ∈ K₁ ⊓ K₂ := by rwa [S.inter_eq]
      refine ⟨⟨hgz.1, ?_⟩, hgz.2⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine mem_centralizer_singleton_iff.mpr ?_
      have hxz : z * x = x * z := S.z_comm₁ hx
      exact ((Commute.zpow_left (show Commute z x from hxz) n).eq)
  have hcard3600 : Nat.card ↥Kx = 3600 := by
    have h := card_sup_mul_card_inf_of_commute (H₁ := H₁) (H₂ := K₂)
      (fun a ha b hb => S.comm a ha.1 b hb)
    rw [hsup, hinf, Nat.card_zpowers, S.z_ord, hH₁, S.card_K₂] at h
    omega
  set B : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) with hB
  have hKC : K₁ ⊔ K₂ ≤ centralizer ({z} : Set G) := sup_le S.le_centralizer₁ S.le_centralizer₂
  have hKxB : Kx ≤ B := fun g hg => ⟨hg.2, hKC hg.1⟩
  have htB : S.t ∈ B := ⟨mem_centralizer_singleton_iff.mpr hxt, S.t_mem⟩
  have htt : S.t * S.t = 1 := by
    have := pow_orderOf_eq_one S.t
    rw [S.t_ord] at this
    simpa [pow_two] using this
  have hrel : Kx.relIndex B = 2 := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨S.t, htB⟩, ?_⟩
    intro b
    have hbx : (b : G) ∈ centralizer ({x} : Set G) := b.2.1
    have hbC : (b : G) ∈ centralizer ({z} : Set G) := b.2.2
    have htx : S.t ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hxt
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf, hKxdef]
    rcases S.mem_C_cases _ hbC with hbK | ⟨k, hk, hbk⟩
    · right
      refine ⟨⟨hbK, hbx⟩, ?_⟩
      rintro ⟨hbtK, -⟩
      apply S.t_notin
      have : S.t = (b : G)⁻¹ * ((b : G) * S.t) := by group
      rw [this]
      exact mul_mem (inv_mem hbK) hbtK
    · left
      have hkx : k ∈ centralizer ({x} : Set G) := by
        have : k = (b : G) * S.t⁻¹ := by rw [hbk]; group
        rw [this]
        exact mul_mem hbx (inv_mem htx)
      have hbtk : (b : G) * S.t = k := by rw [hbk, mul_assoc, htt, mul_one]
      refine ⟨⟨by rw [hbtk]; exact hk, by rw [hbtk]; exact hkx⟩, ?_⟩
      rintro ⟨hbK, -⟩
      apply S.t_notin
      have : S.t = k⁻¹ * (b : G) := by rw [hbk]; group
      rw [this]
      exact mul_mem (inv_mem hk) hbK
  have hfin := Subgroup.relIndex_mul_card Kx B
  rw [hrel, inf_eq_left.mpr hKxB, hcard3600] at hfin
  omega

theorem card_C_inf_centralizer_five_two :
    ∀ x ∈ K₁ ⊓ S.Hs, orderOf x = 5 →
    (Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G))).factorization 2 = 5 := by
  intro x hx hx5
  rw [S.card_C_inf_centralizer_five x hx hx5, fac7200_two]

theorem oddC_x5
    [Finite G] : ∀ x ∈ K₁ ⊓ S.Hs, orderOf x = 5 → ∀ M : Subgroup G,
    M ≤ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) →
    (∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G), ∀ m ∈ M, c * m * c⁻¹ ∈ M) →
    Odd (Nat.card M) → M ≤ zpowers x := by
  intro x hxK hx5 M hMle hMnorm hodd
  obtain ⟨hx, hxH⟩ := hxK
  have hK₂B : K₂ ≤ centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf (S.K₂_le_centralizer_of_mem₁ hx) (fun k hk =>
      mem_centralizer_singleton_iff.mpr (S.comm z S.z_mem₁ k hk).symm)
  have hMK₂ : ∀ k ∈ K₂, ∀ m ∈ M, k * m * k⁻¹ ∈ M := fun k hk m hm => hMnorm k (hK₂B hk) m hm
  have htriv := S.K₂_odd_normal M hMK₂ hodd
  intro m hm
  have hmB := hMle hm
  have hmC : m ∈ centralizer ({z} : Set G) := hmB.2
  have hcomm : ∀ k ∈ K₂, m * k = k * m := by
    intro k hk
    have h1 : m * k * m⁻¹ ∈ K₂ := S.normal₂ m hmC k hk
    have h2 : k * m⁻¹ * k⁻¹ ∈ M := hMK₂ k hk m⁻¹ (inv_mem hm)
    have h3 : (m * k * m⁻¹) * k⁻¹ ∈ M := by
      have : (m * k * m⁻¹) * k⁻¹ = m * (k * m⁻¹ * k⁻¹) := by group
      rw [this]
      exact mul_mem hm h2
    have h4 : (m * k * m⁻¹) * k⁻¹ ∈ K₂ := mul_mem h1 (inv_mem hk)
    have h5 : (m * k * m⁻¹) * k⁻¹ = 1 := htriv _ h4 h3
    have h6 : m * k * m⁻¹ = k := mul_inv_eq_one.mp h5
    calc m * k = (m * k * m⁻¹) * m := by group
      _ = k * m := by rw [h6]
  have hm₁ : m ∈ K₁ := S.centralizer_K₂_le_K₁ m hmC hcomm
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  have hmx : m ∈ centralizer ({x} : Set G) := hmB.1
  have hmodd : Odd (orderOf m) := by
    refine Odd.of_dvd_nat hodd ?_
    have := orderOf_dvd_natCard (⟨m, hm⟩ : M)
    rwa [Subgroup.orderOf_mk] at this
  have hM₀ : orderOf (ψ₁ ⟨x, hx⟩) = 5 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx5]
  have hN : ψ₁ ⟨m, hm₁⟩ ∈ centralizer ({ψ₁ ⟨x, hx⟩} : Set SL2) := by
    refine mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hmx)
  have hNodd : Odd (orderOf (ψ₁ ⟨m, hm₁⟩)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hmodd
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (centralizer_order5_odd _ hM₀ _ hN hNodd)
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  have h1 : (⟨x, hx⟩ : ↥K₁) ^ n = ⟨m, hm₁⟩ := by
    apply ψ₁.injective
    rw [map_zpow]
    exact hn
  have := congrArg Subtype.val h1
  simpa using this

end Q9Setting

end CFSG.GH74.GLS.Stage4.Q9
