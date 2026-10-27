module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeCBender

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeC

open Subgroup CFSG.HardMathSupport.Dickson.I271.TabMFive

section Equiv

@[expose] def centralizerMulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (u : K) :
    centralizer ({u} : Set K) ≃* centralizer ({e u} : Set K') where
  toFun x := ⟨e x.1, by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 x.2]⟩
  invFun y := ⟨e.symm y.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.1 y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul e _ _)

@[expose] def centralizerSubtypeEquiv {G : Type*} [Group G] (C : Subgroup G) (u : C) :
    centralizer ({u} : Set C) ≃* ↥(C ⊓ centralizer ({(u : G)} : Set G)) where
  toFun k := ⟨(k.1 : G), k.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp k.2))⟩
  invFun m := ⟨⟨m.1, m.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.2.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Equiv

section Facts

@[expose] def InvolutionFacts (K : Type*) [Group K] (N : ℕ) : Prop :=
  (∀ t : K, orderOf t = 2 → Nat.card ↥(centralizer ({t} : Set K)) = N) ∧
    (∀ t u : K, orderOf t = 2 → orderOf u = 2 → ∃ g : K, g * u * g⁻¹ = t) ∧
    (∃ a b : K, orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b) ∧
    ∃ t₀ : K, orderOf t₀ = 2 ∧ NoOddSections ↥(centralizer ({t₀} : Set K))

theorem InvolutionFacts.of_equiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {N : ℕ}
    (h : InvolutionFacts K N) : InvolutionFacts K' N := by
  obtain ⟨h1, h2, ⟨a, b, ha, hb, hab, hne⟩, t₀, ho₀, hF⟩ := h
  refine ⟨fun t' ht' => ?_, fun t' u' ht' hu' => ?_,
    ⟨e a, e b, ?_, ?_, ?_, ?_⟩, e t₀, ?_, ?_⟩
  · have ht : orderOf (e.symm t') = 2 := by rw [MulEquiv.orderOf_eq]; exact ht'
    have := Nat.card_congr (centralizerMulEquiv e (e.symm t')).toEquiv
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
    exact h1 _ ht
  · obtain ⟨g, hg⟩ := h2 (e.symm t') (e.symm u') (by rw [MulEquiv.orderOf_eq]; exact ht')
      (by rw [MulEquiv.orderOf_eq]; exact hu')
    refine ⟨e g, ?_⟩
    have := congrArg e hg
    simpa using this
  · rw [MulEquiv.orderOf_eq]; exact ha
  · rw [MulEquiv.orderOf_eq]; exact hb
  · rw [← map_mul, ← map_mul, hab]
  · exact fun h => hne (e.injective h)
  · rw [MulEquiv.orderOf_eq]; exact ho₀
  · exact hF.of_equiv (centralizerMulEquiv e t₀)

theorem card_centralizer_le_of_involutionFacts {G : Type} [Group G]
    [Finite G] {p N : ℕ} {k α : G} {H : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : orderOf k = p) (hα : α * k * α⁻¹ = k⁻¹) (hHα : H ≤ centralizer ({α} : Set G))
    (hHk : H ≤ centralizer ({k} : Set G)) (hF : InvolutionFacts ↥H N)
    (hup : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) ≤ p * N) :
    Nat.card ↥(centralizer ({k} : Set G)) ≤ p * Nat.card ↥H := by
  obtain ⟨h1, h2, ⟨a, b, ha, hb, hab, hne⟩, t₀, ho₀, hF₀⟩ := hF
  have hcard : ∀ t ∈ H, orderOf t = 2 → Nat.card ↥(H ⊓ centralizer ({t} : Set G)) = N :=
    fun t ht ho => by
      rw [← card_centralizer_subtype (⟨t, ht⟩ : ↥H)]
      exact h1 ⟨t, ht⟩ (by rw [← Subgroup.orderOf_coe]; exact ho)
  refine (centralizer_eq_prodSub (H := H) hp hp2 hk hα hHα hHk ?_ ?_ (a := (a : G)) (b := (b : G))
    a.2 b.2 (by rw [Subgroup.orderOf_coe]; exact ha) (by rw [Subgroup.orderOf_coe]; exact hb)
    (congrArg Subtype.val hab) (fun h => hne (Subtype.ext h)) (t₀ := (t₀ : G)) t₀.2
    (by rw [Subgroup.orderOf_coe]; exact ho₀) ?_).2
  · intro t ht ho
    rw [hcard t ht ho]
    exact hup t ht ho
  · intro t ht u hu hto huo
    obtain ⟨g, hg⟩ := h2 ⟨t, ht⟩ ⟨u, hu⟩ (by rw [← Subgroup.orderOf_coe]; exact hto)
      (by rw [← Subgroup.orderOf_coe]; exact huo)
    exact ⟨g, g.2, congrArg Subtype.val hg⟩
  · exact hF₀.of_equiv (centralizerSubtypeEquiv H t₀)

end Facts

end CFSG.HardMathSupport.Dickson.I271.TabMThreeC
