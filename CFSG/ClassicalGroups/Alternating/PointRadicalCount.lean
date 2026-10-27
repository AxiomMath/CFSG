module

public import CFSG.ClassicalGroups.Alternating.PointRadical
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

theorem siegel_add_smul_self_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : BilinForm K V} (h2 : (2 : K) = 0) (hB : B.IsAlt) {v w : V} (hvw : B v w = 0)
    (s c : K) : siegel B hB v (w + s • v) c = siegel B hB v w c := by
  have hvw' : B v (w + s • v) = 0 := by
    rw [map_add, hvw, map_smul, hB.self_eq_zero, smul_zero, add_zero]
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [siegel_apply hB hvw', siegel_apply hB hvw]
  have key : (2 * (s * B x v)) • v = 0 := by rw [h2, zero_mul, zero_smul]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination (norm := module) key

theorem siegel_apply_sub {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : BilinForm K V} (hB : B.IsAlt) {v w : V} (hvw : B v w = 0) (c : K) (x : V) :
    (siegel B hB v w c : V →ₗ[K] V) x - x = B x v • w + (B x w + c * B x v) • v := by
  rw [siegel_apply hB hvw]
  module

theorem card_le_of_no_c2 {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : BilinForm K V} (hB : B.IsAlt)
    (hBn : B.Nondegenerate) {u : V} (hu : u ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (hdim : Module.finrank K V = 2 * m)
    (P : Subgroup (LinearMap.GeneralLinearGroup K V)) (hP : P ≤ pointRadical B hB u)
    (hno : ∀ (w : V) (c : K), B u w = 0 → siegel B hB u w c ∈ P →
      c = 0 ∨ ∃ s : K, w = s • u) :
    Nat.card ↥P ≤ Nat.card K ^ (m - 1) := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  haveI : Finite V := Module.finite_of_finite K
  have hK : 0 < Nat.card K := Nat.card_pos
  have hrep : ∀ g ∈ P, ∃ w c, B u w = 0 ∧ siegel B hB u w c = g :=
    fun g hg => mem_pointRadical.mp (hP hg)
  obtain ⟨y, hy⟩ : ∃ y : V, B y u = 1 := by
    obtain ⟨y0, hy0⟩ : ∃ y0 : V, B y0 u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (hBn.2 u hcon)
    refine ⟨(B y0 u)⁻¹ • y0, ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hy0]
  have hyu : B y u ≠ 0 := by rw [hy]; exact one_ne_zero
  have huy : B u y = -1 := by rw [← hB.neg_eq y u, hy]
  by_cases hA : ∀ (w : V) (c : K), B u w = 0 → siegel B hB u w c ∈ P → ∃ s : K, w = s • u
  ·
    have hcentre : ∀ g ∈ P, ∃ c : K, siegel B hB u 0 c = g := by
      intro g hg
      obtain ⟨w, c, hw, rfl⟩ := hrep g hg
      obtain ⟨s, rfl⟩ := hA w c hw hg
      refine ⟨c, ?_⟩
      have e := siegel_add_smul_self_eq h2 hB (map_zero (B u)) s c
      rw [zero_add] at e
      exact e.symm
    have hmemA : ∀ g ∈ P, ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y - y ∈
        Submodule.span K {u} := by
      intro g hg
      obtain ⟨c, rfl⟩ := hcentre g hg
      rw [siegel_apply_sub hB (map_zero (B u))]
      simp only [smul_zero, map_zero, zero_add]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    let Ψ : P → Submodule.span K {u} := fun g =>
      ⟨((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y - y, hmemA g.1 g.2⟩
    have hΨinj : Function.Injective Ψ := by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ hgg'
      have hval : ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y - y =
          ((g' : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y - y :=
        congrArg Subtype.val hgg'
      obtain ⟨c, hc⟩ := hcentre g hg
      obtain ⟨c', hc'⟩ := hcentre g' hg'
      rw [← hc, ← hc', siegel_apply_sub hB (map_zero (B u)),
        siegel_apply_sub hB (map_zero (B u))] at hval
      simp only [smul_zero, map_zero, zero_add] at hval
      have hcc : c * B y u = c' * B y u := smul_left_injective K hu hval
      have hcc' : c = c' := mul_right_cancel₀ hyu hcc
      apply Subtype.ext
      show g = g'
      rw [← hc, ← hc', hcc']
    have hspan : Nat.card (Submodule.span K {u}) =
        Nat.card K ^ Module.finrank K (Submodule.span K {u}) :=
      Module.natCard_eq_pow_finrank
    have hcard := Nat.card_le_card_of_injective Ψ hΨinj
    rw [hspan, finrank_span_singleton hu, pow_one] at hcard
    have h1 : Nat.card K ^ 1 ≤ Nat.card K ^ (m - 1) := Nat.pow_le_pow_right hK (by omega)
    rw [pow_one] at h1
    exact hcard.trans h1
  ·
    push Not at hA
    obtain ⟨w₀, c₀, hw₀, hg₀, hw₀ne⟩ := hA
    have hc₀ : c₀ = 0 := by
      rcases hno w₀ c₀ hw₀ hg₀ with h | ⟨s, hs⟩
      · exact h
      · exact absurd hs (hw₀ne s)
    subst hc₀
    have hcoef : ∀ (v : V) (c : K), B u v = 0 → siegel B hB u v c ∈ P → c = 0 := by
      intro v c hv hvP
      by_contra hc
      obtain ⟨s, rfl⟩ := (hno v c hv hvP).resolve_left hc
      have hw₀u : B w₀ u = 0 := by rw [← hB.neg_eq u w₀, hw₀, neg_zero]
      have hBs : B w₀ (s • u) = 0 := by rw [map_smul, hw₀u, smul_zero]
      have hmul := P.mul_mem hvP hg₀
      rw [siegel_mul hB hv hw₀ c 0, hBs, add_zero, add_zero] at hmul
      have hsum : B u (s • u + w₀) = 0 := by rw [map_add, hv, hw₀, add_zero]
      obtain ⟨t, ht⟩ := (hno (s • u + w₀) c hsum hmul).resolve_left hc
      apply hw₀ne (t - s)
      rw [sub_smul, ← ht]
      abel
    set W : Set V := {w | B u w = 0 ∧ siegel B hB u w 0 ∈ P}
    have hmemW : ∀ w, w ∈ W ↔ B u w = 0 ∧ siegel B hB u w 0 ∈ P := fun w => Iff.rfl
    have hWW : ∀ a ∈ W, ∀ b ∈ W, B b a = 0 := by
      intro a ha b hb
      obtain ⟨ha1, ha2⟩ := (hmemW a).mp ha
      obtain ⟨hb1, hb2⟩ := (hmemW b).mp hb
      have hmul := P.mul_mem hb2 ha2
      rw [siegel_mul hB hb1 ha1 0 0] at hmul
      have h0 := hcoef _ _ (by rw [map_add, hb1, ha1, add_zero]) hmul
      have h1 : B a b = 0 := by simpa using h0
      have h3 := hB.neg_eq b a
      rw [h1] at h3
      exact neg_eq_zero.mp h3
    set X : Submodule K V := Submodule.span K W
    have huW : u ∈ W := by
      refine (hmemW u).mpr ⟨hB.self_eq_zero u, ?_⟩
      have e := siegel_add_smul_self_eq h2 hB (map_zero (B u)) 1 0
      rw [zero_add, one_smul, siegel_zero] at e
      rw [e]
      exact P.one_mem
    have huX : u ∈ X := Submodule.subset_span huW
    have hXortho : ∀ w ∈ W, ∀ n ∈ X, B n w = 0 := by
      intro w hw n hn
      have hle : Submodule.span K W ≤ LinearMap.ker (B.flip w) := by
        refine Submodule.span_le.mpr fun w' hw' => ?_
        exact hWW w hw w' hw'
      have h := hle hn
      exact LinearMap.mem_ker.mp h
    have hXX : X ≤ B.orthogonal X := by
      refine Submodule.span_le.mpr fun w hw => ?_
      exact Submodule.mem_orthogonalBilin.mpr (hXortho w hw)
    have hXdim : Module.finrank K X ≤ m := by
      have h1 := LinearMap.BilinForm.finrank_orthogonal hBn X
      have h2' : Module.finrank K X ≤ Module.finrank K (B.orthogonal X) :=
        Submodule.finrank_mono hXX
      have h3 : Module.finrank K X ≤ Module.finrank K V := Submodule.finrank_le X
      omega
    set M : Submodule K V := X ⊓ LinearMap.ker (B.flip y) with hM
    have hMmem : ∀ x, x ∈ M ↔ x ∈ X ∧ B x y = 0 := fun x => Iff.rfl
    have hKuM : Submodule.span K {u} ⊓ M = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx1
      have hBa : B (a • u) y = 0 := ((hMmem _).mp hx2).2
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, huy, mul_neg_one, neg_eq_zero] at hBa
      rw [hBa, zero_smul]
      exact Submodule.zero_mem _
    have hsup : Submodule.span K {u} ⊔ M ≤ X :=
      sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huX)) inf_le_left
    have hMdim : Module.finrank K M + 1 ≤ m := by
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {u}) M
      rw [hKuM, finrank_bot, finrank_span_singleton hu] at hsum
      have hle : Module.finrank K ↥(Submodule.span K {u} ⊔ M) ≤ Module.finrank K X :=
        Submodule.finrank_mono hsup
      omega
    have hform : ∀ w : V, B u w = 0 →
        (siegel B hB u w 0 : V →ₗ[K] V) y - y = w + B y w • u := by
      intro w hw
      rw [siegel_apply_sub hB hw, hy, zero_mul, add_zero, one_smul]
    have hMker : ∀ w : V, B (w + B y w • u) y = 0 := by
      intro w
      have e1 := hB.neg_eq y w
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← e1, huy]
      linear_combination (-(B y w)) * h2
    have hΨB : ∀ g ∈ P, ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y - y ∈ M := by
      intro g hg
      obtain ⟨w, c, hw, rfl⟩ := hrep g hg
      have hc : c = 0 := hcoef w c hw hg
      subst hc
      have hwW : w ∈ W := (hmemW w).mpr ⟨hw, hg⟩
      rw [hform w hw, hMmem]
      exact ⟨X.add_mem (Submodule.subset_span hwW) (X.smul_mem _ huX), hMker w⟩
    let Ψ : P → M := fun g =>
      ⟨((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y - y, hΨB g.1 g.2⟩
    have hΨinj : Function.Injective Ψ := by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ hgg'
      have hval : ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y - y =
          ((g' : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y - y :=
        congrArg Subtype.val hgg'
      obtain ⟨w, c, hw, hgeq⟩ := hrep g hg
      obtain ⟨w', c', hw', hgeq'⟩ := hrep g' hg'
      have hc : c = 0 := hcoef w c hw (by rw [hgeq]; exact hg)
      have hc' : c' = 0 := hcoef w' c' hw' (by rw [hgeq']; exact hg')
      subst hc hc'
      rw [← hgeq, ← hgeq', hform w hw, hform w' hw'] at hval
      have hw'eq : w' = w + (B y w - B y w') • u := by
        calc w' = (w' + B y w' • u) - B y w' • u := by abel
          _ = (w + B y w • u) - B y w' • u := by rw [hval]
          _ = w + (B y w - B y w') • u := by rw [sub_smul]; abel
      apply Subtype.ext
      show g = g'
      rw [← hgeq, ← hgeq', hw'eq, siegel_add_smul_self_eq h2 hB hw]
    have hMcard : Nat.card ↥M = Nat.card K ^ Module.finrank K M :=
      Module.natCard_eq_pow_finrank
    have hcard := Nat.card_le_card_of_injective Ψ hΨinj
    rw [hMcard] at hcard
    have h1 : Nat.card K ^ Module.finrank K M ≤ Nat.card K ^ (m - 1) :=
      Nat.pow_le_pow_right hK (by omega)
    exact hcard.trans h1

end CFSG.ClassicalGroups.Alternating
