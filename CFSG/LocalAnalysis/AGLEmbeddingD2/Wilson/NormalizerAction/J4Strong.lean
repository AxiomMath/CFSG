module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Normalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4HeisLocalEq

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open scoped commutatorElement Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_inf_centralizer_mul_orbit {G : Type*} [Group G] [Finite G] (N : Subgroup G) (g : G) :
    Nat.card ↥(N ⊓ Subgroup.centralizer ({g} : Set G)) *
      Nat.card ↥({x | ∃ n ∈ N, x = n * g * n⁻¹} : Set G) = Nat.card N := by
  set S : Subgroup N := (Subgroup.centralizer ({g} : Set G)).subgroupOf N with hS
  have h1 := Subgroup.card_mul_index S
  have hS_eq : Nat.card S = Nat.card ↥(N ⊓ Subgroup.centralizer ({g} : Set G)) := by
    rw [← Subgroup.card_map_of_injective N.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have key : ∀ a b : N, a⁻¹ * b ∈ S ↔ (a : G) * g * (a : G)⁻¹ = b * g * (b : G)⁻¹ := by
    intro a b
    rw [hS, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      have := h g (Set.mem_singleton g)
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at this
      calc (a : G) * g * (a : G)⁻¹ = (a : G) * (g * ((a : G)⁻¹ * (b : G))) * (b : G)⁻¹ := by group
        _ = (a : G) * (((a : G)⁻¹ * (b : G)) * g) * (b : G)⁻¹ := by rw [this]
        _ = _ := by group
    · intro h g' hg'
      rw [Set.mem_singleton_iff] at hg'
      subst hg'
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      calc g' * ((a : G)⁻¹ * b) = (a : G)⁻¹ * (a * g' * (a : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * (b * g' * (b : G)⁻¹) * b := by rw [h]
        _ = _ := by group
  have h2 : S.index = Nat.card ↥({x | ∃ n ∈ N, x = n * g * n⁻¹} : Set G) := by
    rw [Subgroup.index]
    let f : N ⧸ S → ↥({x | ∃ n ∈ N, x = n * g * n⁻¹} : Set G) :=
      Quotient.lift (fun n : N => (⟨n * g * (n : G)⁻¹, n, n.2, rfl⟩ :
        ↥({x | ∃ n ∈ N, x = n * g * n⁻¹} : Set G))) (by
        intro a b hab
        exact Subtype.ext ((key a b).1 (QuotientGroup.leftRel_apply.1 hab)))
    refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
    · intro x y hxy
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      exact Quotient.sound (QuotientGroup.leftRel_apply.2 ((key _ _).2 (congrArg Subtype.val hxy)))
    · rintro ⟨_, n, hn, rfl⟩
      exact ⟨QuotientGroup.mk ⟨n, hn⟩, rfl⟩
  rw [← hS_eq, ← h2]
  exact h1

theorem card_conj_orbit_ge {G : Type*} [Group G] [Finite G] (N : Subgroup G) (g : G) :
    Nat.card N ≤ Nat.card ↥(Subgroup.centralizer ({g} : Set G)) *
      Nat.card ↥({x | ∃ n ∈ N, x = n * g * n⁻¹} : Set G) := by
  rw [← card_inf_centralizer_mul_orbit N g]
  refine Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective (fun s => ⟨s.1, s.2.2⟩) ?_)
  intro a b hab
  exact Subtype.ext (by simpa using congrArg Subtype.val hab)

theorem conj_mem_inf_centralizer {G : Type*} [Group G] (Q : Subgroup G) {n : G}
    (hn : n ∈ Subgroup.normalizer (Q : Set G)) {x : G}
    (hx : x ∈ Q ⊓ Subgroup.centralizer (Q : Set G)) :
    n * x * n⁻¹ ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
  obtain ⟨hxQ, hxC⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.1 hn x).1 hxQ, ?_⟩
  show n * x * n⁻¹ ∈ Subgroup.centralizer (Q : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : n⁻¹ * q * n ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) q).1 hq
    simpa using this
  have h : n⁻¹ * q * n * x = x * (n⁻¹ * q * n) := Subgroup.mem_centralizer_iff.1 hxC _ hq'
  calc q * (n * x * n⁻¹) = n * ((n⁻¹ * q * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * q * n)) * n⁻¹ := by rw [h]
    _ = n * x * n⁻¹ * q := by group

theorem conj_mem_inf_centralizer_iff {G : Type*} [Group G] (Q : Subgroup G) {n : G}
    (hn : n ∈ Subgroup.normalizer (Q : Set G)) {x : G} :
    n * x * n⁻¹ ∈ Q ⊓ Subgroup.centralizer (Q : Set G) ↔
      x ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
  refine ⟨fun h => ?_, conj_mem_inf_centralizer Q hn⟩
  have := conj_mem_inf_centralizer Q (Subgroup.inv_mem _ hn) h
  have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
  rwa [e] at this

section Classes

@[expose] def fixDim (g : J) : ℕ := Module.finrank (ZMod 2) (rowFix (φ g))

theorem rowFix_eq_ker (M : Matrix (Fin 112) (Fin 112) (ZMod 2)) :
    rowFix M = LinearMap.ker (Matrix.mulVecLin (M - 1)ᵀ) := by
  ext v
  rw [mem_rowFix, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose,
    Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero]

theorem fixDim_add_rank (g : J) : fixDim g + (φ g - 1).rank = 112 := by
  unfold fixDim
  rw [rowFix_eq_ker]
  exact finrank_ker_transpose_add_rank _

theorem fixDim_conj (c g : J) : fixDim (c * g * c⁻¹) = fixDim g := by
  have h1 := fixDim_add_rank (c * g * c⁻¹)
  have h2 := fixDim_add_rank g
  have h3 := rank_conj c g
  omega

theorem fixDim_one : fixDim (1 : J) = 112 := by
  have h := fixDim_add_rank (1 : J)
  have : ((φ (1 : J)) - 1 : Matrix (Fin 112) (Fin 112) (ZMod 2)) = 0 := by
    rw [map_one, sub_self]
  rw [this, Matrix.rank_zero] at h
  omega

theorem vecMul_zpow_of_fixed {a : J} {v : Fin 112 → ZMod 2} (hv : v ᵥ* φ a = v) (k : ℤ) :
    v ᵥ* φ (a ^ k) = v := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, map_mul, ← Matrix.vecMul_vecMul, ih, hv]
  | pred k ih =>
    have e : v ᵥ* φ (a ^ (-(k : ℤ) - 1)) = (v ᵥ* φ (a ^ (-(k : ℤ)))) ᵥ* φ a⁻¹ := by
      rw [Matrix.vecMul_vecMul, ← map_mul, zpow_sub_one]
    rw [e, ih]
    have h2 : v ᵥ* φ a⁻¹ = (v ᵥ* φ a) ᵥ* φ a⁻¹ := by rw [hv]
    rw [h2, Matrix.vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one, Matrix.vecMul_one]

theorem rowFix_le_of_mem_zpowers {a b : J} (hb : b ∈ Subgroup.zpowers a) :
    rowFix (φ a) ≤ rowFix (φ b) := by
  intro v hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [mem_rowFix] at hv ⊢
  exact vecMul_zpow_of_fixed hv k

theorem fixDim_eq_of_mem_zpowers {g h : J} (hg : g ∈ Subgroup.zpowers h)
    (hh : h ∈ Subgroup.zpowers g) : fixDim g = fixDim h := by
  unfold fixDim
  rw [le_antisymm (rowFix_le_of_mem_zpowers hh) (rowFix_le_of_mem_zpowers hg)]



theorem conj_mem_zpowers_iff {n : J} (hn : n ∈ Subgroup.normalizer (Q11 : Set J)) {x : J} :
    n * x * n⁻¹ ∈ Subgroup.zpowers qz ↔ x ∈ Subgroup.zpowers qz := by
  rw [← inf_centralizer_Q11]
  exact conj_mem_inf_centralizer_iff Q11 hn

theorem qx_not_mem_zpowers : qx ∉ Subgroup.zpowers qz := by
  intro h
  rw [← inf_centralizer_Q11] at h
  have hc : qx ∈ Subgroup.centralizer (Q11 : Set J) := h.2
  have := Subgroup.mem_centralizer_iff.1 hc qy qy_mem
  apply qz_ne_one
  show ⁅qx, qy⁆ = 1
  exact commutatorElement_eq_one_iff_mul_comm.2 this.symm

theorem exists_conj_of_mem_Q11
    (hC : Nat.card (Subgroup.centralizer ({qx} : Set J)) ≤ 242) :
    ∀ u ∈ Q11, u ∉ Subgroup.zpowers qz →
      ∃ n ∈ Subgroup.normalizer (Q11 : Set J), u = n * qx * n⁻¹ := by
  set X : Set J := {x | ∃ n ∈ (Subgroup.normalizer (Q11 : Set J) : Subgroup J),
    x = n * qx * n⁻¹} with hX
  set Y : Set J := (Q11 : Set J) \ (Subgroup.zpowers qz : Set J) with hY
  have hXY : X ⊆ Y := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 hn qx).1 qx_mem, ?_⟩
    intro h
    exact qx_not_mem_zpowers ((conj_mem_zpowers_iff hn).1 h)
  have hYcard : Y.ncard = 1320 := by
    have hsub : (Subgroup.zpowers qz : Set J) ⊆ (Q11 : Set J) := by
      rw [SetLike.coe_subset_coe, Subgroup.zpowers_le]; exact qz_mem
    rw [hY, Set.ncard_sdiff hsub, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    have h1 : Nat.card (Q11 : Set J) = 1331 := by
      rw [show (Q11 : Set J) = ↑Q11 from rfl]; exact card_Q11
    have h2 : Nat.card (Subgroup.zpowers qz) = 11 := by
      rw [Nat.card_zpowers, orderOf_qz]
    rw [h1]
    exact (congrArg (1331 - ·) h2 : _)
  have hXcard : 1320 ≤ X.ncard := by
    have h := card_conj_orbit_ge (Subgroup.normalizer (Q11 : Set J)) qx
    rw [card_normalizer_Q11, Nat.card_coe_set_eq] at h
    have h2 : 11 ^ 3 * 240 ≤ 242 * X.ncard := le_trans h (Nat.mul_le_mul_right _ hC)
    omega
  intro u hu hnu
  by_contra hne
  have hu' : u ∈ Y \ X := ⟨⟨hu, hnu⟩, fun hx => by
    obtain ⟨n, hn, hun⟩ := hx
    exact hne ⟨n, hn, hun⟩⟩
  have hlt : X.ncard < Y.ncard :=
    Set.ncard_lt_ncard ⟨hXY, fun hYX => hu'.2 (hYX hu'.1)⟩ (Set.toFinite _)
  omega

end Classes

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
