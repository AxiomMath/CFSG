module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NoncentralCenter

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "ℬ₁" => ptSub φ z hb e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)

theorem degree64_noncentral_alternatives [Finite G] {D₁ C₁ C₂ K₀ M E₁C₂ : Subgroup G}
    {ε : ZMod 2} (hD₁N : D₁ ≤ 𝒩₁) (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hZc : Nat.card (center C₁) = 4)
    (hCF : (C₁ : Set G) ∩ {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)} =
      ((𝒜₁ ⊔ (center C₁).map C₁.subtype : Subgroup G) : Set G))
    (hb₁c : ∀ m ∈ 𝒩₁, m * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * m)
    (hZB : (center C₁).map C₁.subtype ⊓ ℬ₁ ≤ zpowers (ptB₁ he hb φ hzC hz))
    (hZK : (center C₁).map C₁.subtype ≤ K₀) (hKC : K₀ ≤ C₂) (hMK : M ≤ K₀)
    (hZE : (center C₁).map C₁.subtype ≤ E₁C₂) {J : Subgroup G} (hJE' : J ≤ E₁C₂)
    {g : G} (hgZ : g ∈ (center C₁).map C₁.subtype) (hgB : g ∉ ℬ₁)
    (hgz : z⁻¹ * (g⁻¹ * z * g) = ptB₁ he hb φ hzC hz) (hgsq : g ^ 2 = ptB₁ he hb φ hzC hz ^ ε.val)
    (hK₀eq : (K₀ : Set G) = (M : Set G) * (zpowers g : Set G))
    (hE₁C₂eq : (E₁C₂ : Set G) = (J : Set G) * (zpowers g : Set G)) :
    (center C₁).map C₁.subtype ⊓ 𝒜₁ = zpowers (ptB₁ he hb φ hzC hz) ∧
    (center C₁).map C₁.subtype ≤ C₂ ∧
    (K₀ : Set G) = (M : Set G) * ((center C₁).map C₁.subtype : Set G) ∧
    (E₁C₂ : Set G) = (J : Set G) * ((center C₁).map C₁.subtype : Set G) ∧
    (ε = 0 → Nonempty (↥(center C₁) ≃* Multiplicative (ZMod 2 × ZMod 2))) ∧
    (ε = 1 → Nonempty (↥(center C₁) ≃* Multiplicative (ZMod 4))) ∧
    closure {x | ∃ y ∈ (center C₁).map C₁.subtype, y ^ 2 = x} =
      zpowers (ptB₁ he hb φ hzC hz ^ ε.val) := by
  classical
  set Z := (center C₁).map C₁.subtype with hZdef
  set b₁ := ptB₁ he hb φ hzC hz with hb₁def
  have hb₁ord : orderOf b₁ = 2 := orderOf_ptB₁ he hb φ hzC hz
  have hb₁sq : b₁ ^ 2 = 1 := by rw [← hb₁ord, pow_orderOf_eq_one]
  have hb₁ne : b₁ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hb₁ord
    exact absurd hb₁ord (by norm_num)
  have hb₁A : b₁ ∈ 𝒜₁ := by
    rw [hb₁def, ptB₁, ptHom_pt]
    exact (mem_ptA_iff he hb φ).2 ⟨_, rfl⟩
  have hAC : 𝒜₁ ≤ C₁ := fun a ha => by
    have h : a ∈ C₁ ⊓ ℬ₁ := by
      rw [hC₁B]
      exact ha
    exact (mem_inf.1 h).1
  have hb₁Z : b₁ ∈ Z := by
    rw [hZdef, mem_map_center_subtype_iff]
    exact ⟨hAC hb₁A, fun c hc => hb₁c c (hD₁N (hC₁D hc))⟩
  have hIZ : zpowers b₁ ≤ Z := zpowers_le.2 hb₁Z
  have hgZ' : zpowers g ≤ Z := zpowers_le.2 hgZ
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy => by
    obtain ⟨hxC, -⟩ := mem_map_center_subtype_iff.1 hx
    obtain ⟨-, hyc⟩ := mem_map_center_subtype_iff.1 hy
    exact hyc x hxC
  have hZ2 : ∀ x ∈ Z, x ∈ zpowers b₁ ∨ x * g⁻¹ ∈ zpowers b₁ := by
    intro x hx
    by_cases hxB : x ∈ ℬ₁
    · exact Or.inl (hZB (mem_inf.2 ⟨hx, hxB⟩))
    · right
      have hxF : x ∈ (C₁ : Set G) ∩ {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers b₁} := by
        rw [hCF]
        exact mem_sup_right hx
      have hxz : z⁻¹ * (x⁻¹ * z * x) = b₁ := by
        rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord hxF.2.2 with h | h
        · exfalso
          apply hxB
          rw [← hD₁H]
          refine mem_inf.2 ⟨hxF.2.1, mem_centralizer_singleton_iff.2 ?_⟩
          have h1 : x⁻¹ * z * x = z := by
            calc x⁻¹ * z * x = z * (z⁻¹ * (x⁻¹ * z * x)) := by group
              _ = z := by rw [h, mul_one]
          calc x * z = x * (x⁻¹ * z * x) := by rw [h1]
            _ = z * x := by group
        · exact h
      have hxg : x * g⁻¹ ∈ Z := mul_mem hx (inv_mem hgZ)
      refine hZB (mem_inf.2 ⟨hxg, ?_⟩)
      have hgC : g ∈ C₁ := (mem_map_center_subtype_iff.1 hgZ).1
      have hxC : x ∈ C₁ := (mem_map_center_subtype_iff.1 hx).1
      have hb₁g : g * b₁ = b₁ * g := hb₁c g (hD₁N (hC₁D hgC))
      have h1 : x⁻¹ * z * x = z * b₁ := by rw [← hxz]; group
      have h2 : g⁻¹ * z * g = z * b₁ := by rw [← hgz]; group
      have h3 : g * z * g⁻¹ = z * b₁⁻¹ := by
        calc g * z * g⁻¹ = g * (g⁻¹ * z * g * b₁⁻¹) * g⁻¹ := by
              rw [h2, mul_inv_cancel_right]
          _ = z * (g * b₁⁻¹ * g⁻¹) := by group
          _ = z * b₁⁻¹ := by
            have hb₁g' : g * b₁⁻¹ = b₁⁻¹ * g := by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, hb₁g, inv_mul_cancel_left]
            rw [hb₁g', mul_inv_cancel_right]
      rw [← hD₁H]
      refine mem_inf.2 ⟨mul_mem (hC₁D hxC) (inv_mem (hC₁D hgC)),
        mem_centralizer_singleton_iff.2 ?_⟩
      have h4 : (x * g⁻¹)⁻¹ * z * (x * g⁻¹) = z := by
        calc (x * g⁻¹)⁻¹ * z * (x * g⁻¹) = g * (x⁻¹ * z * x) * g⁻¹ := by group
          _ = g * z * g⁻¹ * (g * b₁ * g⁻¹) := by rw [h1]; group
          _ = z * b₁⁻¹ * b₁ := by rw [h3, hb₁g, mul_inv_cancel_right]
          _ = z := by group
      calc x * g⁻¹ * z = x * g⁻¹ * ((x * g⁻¹)⁻¹ * z * (x * g⁻¹)) := by rw [h4]
        _ = z * (x * g⁻¹) := by group
  have hgnI : g ∉ zpowers b₁ := fun h =>
    hgB (mem_sup_left ((zpowers_le.2 hb₁A) h))
  refine ⟨?_, ?_, ?_, ?_, fun h0 => ?_, fun h1 => ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      exact hZB (mem_inf.2 ⟨(mem_inf.1 hx).1, mem_sup_left (mem_inf.1 hx).2⟩)
    · exact le_inf hIZ (zpowers_le.2 hb₁A)
  · exact hZK.trans hKC
  · apply Set.Subset.antisymm
    · rw [hK₀eq]
      exact Set.mul_subset_mul_left hgZ'
    · rintro _ ⟨m, hm, x, hx, rfl⟩
      exact mul_mem (hMK hm) (hZK hx)
  · apply Set.Subset.antisymm
    · rw [hE₁C₂eq]
      exact Set.mul_subset_mul_left hgZ'
    · rintro _ ⟨j, hj, x, hx, rfl⟩
      exact mul_mem (hJE' hj) (hZE hx)
  ·
    subst h0
    rw [ZMod.val_zero, pow_zero] at hgsq
    let Ψ₀ : Multiplicative (ZMod 2 × ZMod 2) →* G :=
      { toFun := fun x => g ^ (Multiplicative.toAdd x).1.val * b₁ ^ (Multiplicative.toAdd x).2.val
        map_one' := by
          change g ^ (0 : ZMod 2).val * b₁ ^ (0 : ZMod 2).val = 1
          rw [ZMod.val_zero, pow_zero, pow_zero, one_mul]
        map_mul' := fun x y => by
          change g ^ ((Multiplicative.toAdd x).1 + (Multiplicative.toAdd y).1).val *
            b₁ ^ ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2).val =
            g ^ (Multiplicative.toAdd x).1.val * b₁ ^ (Multiplicative.toAdd x).2.val *
              (g ^ (Multiplicative.toAdd y).1.val * b₁ ^ (Multiplicative.toAdd y).2.val)
          rw [ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ hgsq, ← pow_eq_pow_mod _ hb₁sq,
            pow_add, pow_add]
          have hc : b₁ ^ (Multiplicative.toAdd x).2.val * g ^ (Multiplicative.toAdd y).1.val =
              g ^ (Multiplicative.toAdd y).1.val * b₁ ^ (Multiplicative.toAdd x).2.val :=
            hZcomm _ (pow_mem hb₁Z _) _ (pow_mem hgZ _)
          calc g ^ (Multiplicative.toAdd x).1.val * g ^ (Multiplicative.toAdd y).1.val *
              (b₁ ^ (Multiplicative.toAdd x).2.val * b₁ ^ (Multiplicative.toAdd y).2.val) =
              g ^ (Multiplicative.toAdd x).1.val * (g ^ (Multiplicative.toAdd y).1.val *
                b₁ ^ (Multiplicative.toAdd x).2.val) * b₁ ^ (Multiplicative.toAdd y).2.val := by
                group
            _ = g ^ (Multiplicative.toAdd x).1.val * (b₁ ^ (Multiplicative.toAdd x).2.val *
                g ^ (Multiplicative.toAdd y).1.val) * b₁ ^ (Multiplicative.toAdd y).2.val := by
                rw [hc]
            _ = _ := by group }
    have hΨZ : ∀ x, Ψ₀ x ∈ Z := fun x => mul_mem (pow_mem hgZ _) (pow_mem hb₁Z _)
    have hΨinj : Function.Injective Ψ₀ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      obtain ⟨⟨i, j⟩, rfl⟩ : ∃ p, Multiplicative.ofAdd p = x := ⟨Multiplicative.toAdd x, rfl⟩
      change g ^ i.val * b₁ ^ j.val = 1 at hx
      rcases zmod_two_eq_zero_or_eq_one i with rfl | rfl <;>
        rcases zmod_two_eq_zero_or_eq_one j with rfl | rfl
      · rfl
      · rw [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul] at hx
        exact absurd hx hb₁ne
      · rw [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, mul_one] at hx
        exact absurd (hx ▸ one_mem _) hgnI
      · rw [ZMod.val_one, pow_one, pow_one] at hx
        exact absurd ((eq_inv_of_mul_eq_one_left hx) ▸ inv_mem (mem_zpowers b₁)) hgnI
    let Ψ : Multiplicative (ZMod 2 × ZMod 2) →* Z := Ψ₀.codRestrict Z hΨZ
    have hΨbij : Function.Bijective Ψ := by
      refine Function.Injective.bijective_of_nat_card_le (fun x y h => hΨinj ?_) ?_
      · exact congrArg Subtype.val h
      · rw [hZdef, card_map_of_injective C₁.subtype_injective, hZc, Nat.card_eq_fintype_card]
        rfl
    exact ⟨((center C₁).equivMapOfInjective C₁.subtype C₁.subtype_injective).trans
      (MulEquiv.ofBijective Ψ hΨbij).symm⟩
  ·
    subst h1
    rw [ZMod.val_one, pow_one] at hgsq
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hg4 : orderOf g = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g)
        (by rw [pow_one, hgsq]; exact hb₁ne)
        (by rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hgsq, hb₁sq])
      rw [h]
      rfl
    obtain ⟨hgC, hgc⟩ := mem_map_center_subtype_iff.1 hgZ
    set g' : center C₁ := ⟨⟨g, hgC⟩, mem_center_iff.2 fun y => Subtype.ext (hgc y y.2)⟩ with hg'
    have hcard : Nat.card (center C₁) = Nat.card (Multiplicative (ZMod 4)) := by
      rw [hZc, Nat.card_eq_fintype_card]
      rfl
    have hcyc : IsCyclic (center C₁) := by
      refine isCyclic_of_orderOf_eq_card g' ?_
      rw [hZc, ← hg4, ← orderOf_coe g', ← orderOf_coe (g' : C₁)]
    exact ⟨mulEquivOfCyclicCardEq hcard⟩
  ·
    apply le_antisymm
    · rw [closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hZ2 y hy with h | h
      · have h1 : y ^ 2 = 1 := by
          obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 h
          rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hb₁sq,
            _root_.one_zpow]
        rw [h1]
        exact one_mem _
      · have hy' : y = y * g⁻¹ * g := by group
        have h1 : y ^ 2 = g ^ 2 := by
          obtain ⟨n, hn⟩ := mem_zpowers_iff.1 h
          rw [hy', ← hn]
          have hc : b₁ ^ n * g = g * b₁ ^ n := hZcomm _ (zpow_mem hb₁Z n) _ hgZ
          rw [sq, sq]
          calc b₁ ^ n * g * (b₁ ^ n * g) = b₁ ^ n * (g * b₁ ^ n) * g := by group
            _ = b₁ ^ n * (b₁ ^ n * g) * g := by rw [hc]
            _ = (b₁ ^ 2) ^ n * (g * g) := by group
            _ = g * g := by rw [hb₁sq, _root_.one_zpow, one_mul]
        rw [h1, hgsq]
        exact mem_zpowers _
    · rw [zpowers_le, ← hgsq]
      exact subset_closure ⟨g, hgZ, rfl⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
