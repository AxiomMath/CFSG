module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreLA
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

open CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem comm_of_mem {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {g h : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) (hh : h ∈ E) : g * h = h * g :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)

theorem pow3_eq_one_of_mem {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) : g ^ 3 = 1 :=
  hE.2 g hg

theorem cube_apply {ρ : V ≃ₗ[ZMod 2] V} (h : ρ ^ 3 = 1) (x : V) :
    ρ (ρ (ρ x)) = x := by
  have h3 : (ρ ^ 3) x = x := by rw [h]; rfl
  simpa [pow_succ, LinearEquiv.mul_apply] using h3

theorem pow_one_apply (ρ : V ≃ₗ[ZMod 2] V) (x : V) : (ρ ^ (1 : ℕ)) x = ρ x := by
  rw [pow_one]

theorem pow_two_apply (ρ : V ≃ₗ[ZMod 2] V) (x : V) : (ρ ^ (2 : ℕ)) x = ρ (ρ x) := by
  rw [pow_two, LinearEquiv.mul_apply]

theorem pow_zero_apply (ρ : V ≃ₗ[ZMod 2] V) (x : V) : (ρ ^ (0 : ℕ)) x = x := by
  rw [pow_zero]; rfl

theorem fixed_free {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {X : Submodule (ZMod 2) V} (hXinv : Inv2 E X) (hirr : IsIrrE E X)
    {ρ : V ≃ₗ[ZMod 2] V} (hρ : ρ ∈ E) (hnf : ∃ x ∈ X, ρ x ≠ x) :
    ∀ x ∈ X, ρ x = x → x = 0 := by
  classical
  let Fx : Submodule (ZMod 2) V :=
    X ⊓ LinearMap.ker ((ρ : V →ₗ[ZMod 2] V) - LinearMap.id)
  have hFx_mem : ∀ x, x ∈ Fx ↔ x ∈ X ∧ ρ x = x := by
    intro x
    simp only [Fx, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]
  have hFinv : Inv2 E Fx := by
    intro g hg x hx
    rw [hFx_mem] at hx ⊢
    refine ⟨hXinv g hg x hx.1, ?_⟩
    have hc := comm_of_mem hE hρ hg
    have : ρ (g x) = g (ρ x) := by
      rw [← LinearEquiv.mul_apply, hc, LinearEquiv.mul_apply]
    rw [this, hx.2]
  obtain ⟨x₀, hx₀X, hx₀⟩ := hnf
  have hne : Fx ≠ X := by
    intro h
    have hmem : x₀ ∈ Fx := h ▸ hx₀X
    exact hx₀ ((hFx_mem x₀).1 hmem).2
  rcases hirr.2 Fx (fun x hx => ((hFx_mem x).1 hx).1) hFinv with h | h
  · intro x hx hfix
    have hmem : x ∈ Fx := (hFx_mem x).2 ⟨hx, hfix⟩
    rw [h] at hmem
    exact (Submodule.mem_bot _).1 hmem
  · exact absurd h hne

theorem quad_of_fixed {E : Subgroup (V ≃ₗ[ZMod 2] V)} {X : Submodule (ZMod 2) V}
    (hXinv : Inv2 E X) {ρ : V ≃ₗ[ZMod 2] V} (hρ : ρ ∈ E)
    (hfix : ∀ x ∈ X, ρ x = x → x = 0) (hρ3 : ∀ x ∈ X, ρ (ρ (ρ x)) = x) :
    ∀ x ∈ X, ρ (ρ x) + ρ x + x = 0 := by
  intro x hx
  have hρx : ρ x ∈ X := hXinv ρ hρ x hx
  have hyX : ρ (ρ x) + ρ x + x ∈ X :=
    X.add_mem (X.add_mem (hXinv ρ hρ _ hρx) hρx) hx
  apply hfix _ hyX
  rw [map_add, map_add, hρ3 x hx]
  abel

theorem uniform_exponent {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {X : Submodule (ZMod 2) V} (hXinv : Inv2 E X) (hirr : IsIrrE E X)
    {ρ : V ≃ₗ[ZMod 2] V} (hρ : ρ ∈ E)
    (hfix : ∀ x ∈ X, ρ x = x → x = 0) (hρ3 : ∀ x ∈ X, ρ (ρ (ρ x)) = x)
    (hquad : ∀ x ∈ X, ρ (ρ x) + ρ x + x = 0)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) :
    ∃ k : Fin 3, ∀ x ∈ X, g x = (ρ ^ (k : ℕ)) x := by
  classical
  have hρpow : ∀ k : ℕ, ρ ^ k ∈ E := fun k => E.pow_mem hρ k
  let K : Fin 3 → Submodule (ZMod 2) V := fun k =>
    X ⊓ LinearMap.ker ((g : V →ₗ[ZMod 2] V) - ((ρ ^ (k : ℕ) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V))
  have hKmem : ∀ (k : Fin 3) (x : V), x ∈ K k ↔ x ∈ X ∧ g x = (ρ ^ (k : ℕ)) x := by
    intro k x
    simp only [K, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      LinearEquiv.coe_coe]
  have hKinv : ∀ k : Fin 3, Inv2 E (K k) := by
    intro k h hh x hx
    rw [hKmem] at hx ⊢
    refine ⟨hXinv h hh x hx.1, ?_⟩
    have hc1 := comm_of_mem hE hg hh
    have hc2 := comm_of_mem hE (hρpow k) hh
    have e1 : g (h x) = h (g x) := by rw [← LinearEquiv.mul_apply, hc1, LinearEquiv.mul_apply]
    have e2 : (ρ ^ (k : ℕ)) (h x) = h ((ρ ^ (k : ℕ)) x) := by
      rw [← LinearEquiv.mul_apply, hc2, LinearEquiv.mul_apply]
    rw [e1, e2, hx.2]
  by_contra hcon
  push Not at hcon
  have hbot : ∀ k : Fin 3, K k = ⊥ := by
    intro k
    rcases hirr.2 (K k) inf_le_left (hKinv k) with h | h
    · exact h
    · obtain ⟨x, hx, hne⟩ := hcon k
      have hmem : x ∈ K k := h ▸ hx
      exact absurd ((hKmem k x).1 hmem).2 hne
  have hinj : ∀ k : Fin 3, ∀ x ∈ X, g x - (ρ ^ (k : ℕ)) x = 0 → x = 0 := by
    intro k x hx h0
    have : x ∈ K k := (hKmem k x).2 ⟨hx, sub_eq_zero.1 h0⟩
    rw [hbot k] at this
    exact (Submodule.mem_bot _).1 this
  obtain ⟨x, hxX, hx0⟩ : ∃ x ∈ X, x ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hirr.1
    rw [eq_bot_iff]
    intro y hy
    exact (Submodule.mem_bot _).2 (hall y hy)
  set u : V := g x - ρ (ρ x) with hu
  have huX : u ∈ X := X.sub_mem (hXinv g hg x hxX) (hXinv ρ hρ _ (hXinv ρ hρ x hxX))
  set v : V := g u - ρ u with hv
  have hvX : v ∈ X := X.sub_mem (hXinv g hg u huX) (hXinv ρ hρ u huX)
  set w : V := g v - v with hw
  have hA : ∀ y, g (ρ y) = ρ (g y) := fun y => by
    rw [← LinearEquiv.mul_apply, comm_of_mem hE hg hρ, LinearEquiv.mul_apply]
  have hg3 : ∀ y, g (g (g y)) = y := fun y => cube_apply (pow3_eq_one_of_mem hE hg) y
  have hρ3x : ρ (ρ (ρ x)) = x := cube_apply (pow3_eq_one_of_mem hE hρ) x
  have hz : g x ∈ X := hXinv g hg x hxX
  have hz' : g (g x) ∈ X := hXinv g hg _ hz
  have hquadz : ρ (ρ (g x)) + ρ (g x) + g x = 0 :=
    quad_of_fixed hXinv hρ hfix (fun y _ => cube_apply (pow3_eq_one_of_mem hE hρ) y) _ hz
  have hquadz' : ρ (ρ (g (g x))) + ρ (g (g x)) + g (g x) = 0 :=
    quad_of_fixed hXinv hρ hfix (fun y _ => cube_apply (pow3_eq_one_of_mem hE hρ) y) _ hz'
  have hwexpr : w = (ρ (ρ (g x)) + ρ (g x) + g x) - (ρ (ρ (g (g x))) + ρ (g (g x)) + g (g x)) := by
    simp only [hw, hv, hu, map_sub, map_add, hA, hg3, hρ3x]
    abel
  have hwzero : w = 0 := by
    rw [hwexpr, hquadz, hquadz', sub_zero]
  have hu0 : u ≠ 0 := fun h0 => hx0 (hinj 2 x hxX (by
    show g x - (ρ ^ (2 : ℕ)) x = 0
    rw [pow_two_apply, ← hu]; exact h0))
  have hv0 : v ≠ 0 := fun h0 => hu0 (hinj 1 u huX (by
    show g u - (ρ ^ (1 : ℕ)) u = 0
    rw [pow_one_apply, ← hv]; exact h0))
  have hw0 : w ≠ 0 := fun h0 => hv0 (hinj 0 v hvX (by
    show g v - (ρ ^ (0 : ℕ)) v = 0
    rw [pow_zero_apply, ← hw]; exact h0))
  exact hw0 hwzero

theorem exists_ne_zero_of_ne_bot {X : Submodule (ZMod 2) V} (h : X ≠ ⊥) :
    ∃ x ∈ X, x ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h
  rw [eq_bot_iff]
  intro y hy
  exact (Submodule.mem_bot _).2 (hall y hy)

theorem add_self_eq_zero' (y : V) : y + y = 0 := by
  rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem irr_trichotomy {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {X : Submodule (ZMod 2) V} (hXinv : Inv2 E X) (hirr : IsIrrE E X) :
    ((∀ g ∈ E, ∀ x ∈ X, g x = x) ∧ Module.finrank (ZMod 2) X = 1) ∨
    ∃ ρ ∈ E, Module.finrank (ZMod 2) X = 2 ∧ (∀ x ∈ X, ρ x = x → x = 0) ∧
      (∀ x ∈ X, ρ (ρ x) + ρ x + x = 0) ∧
      (∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X, g x = (ρ ^ (k : ℕ)) x) := by
  classical
  by_cases htriv : ∀ g ∈ E, ∀ x ∈ X, g x = x
  · left
    refine ⟨htriv, ?_⟩
    obtain ⟨x, hxX, hx0⟩ := exists_ne_zero_of_ne_bot hirr.1
    have hS : Submodule.span (ZMod 2) {x} = X := by
      have hinv : Inv2 E (Submodule.span (ZMod 2) {x}) := by
        intro g hg y hy
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
        rw [map_smul, htriv g hg x hxX]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x)
      rcases hirr.2 _ (Submodule.span_le.2 (Set.singleton_subset_iff.2 hxX)) hinv with h | h
      · exact absurd (Submodule.span_singleton_eq_bot.1 h) hx0
      · exact h
    rw [← hS, finrank_span_singleton hx0]
  · right
    push Not at htriv
    obtain ⟨ρ, hρ, x₀, hx₀X, hx₀⟩ := htriv
    have hfix := fixed_free hE hXinv hirr hρ ⟨x₀, hx₀X, hx₀⟩
    have hρ3 : ∀ x ∈ X, ρ (ρ (ρ x)) = x := fun x _ => cube_apply (pow3_eq_one_of_mem hE hρ) x
    have hquad := quad_of_fixed hXinv hρ hfix hρ3
    have huni : ∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X, g x = (ρ ^ (k : ℕ)) x :=
      fun g hg => uniform_exponent hE hXinv hirr hρ hfix hρ3 hquad hg
    refine ⟨ρ, hρ, ?_, hfix, hquad, huni⟩
    obtain ⟨x₁, hx₁X, hx₁⟩ := exists_ne_zero_of_ne_bot hirr.1
    have hr : Set.range ![x₁, ρ x₁] = {x₁, ρ x₁} := by
      ext y
      simp [Fin.exists_fin_two, or_comm]
    set S : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (Set.range ![x₁, ρ x₁]) with hS
    have hmemS : ∀ y, y ∈ S ↔ ∃ a b : ZMod 2, a • x₁ + b • ρ x₁ = y := by
      intro y
      rw [hS, hr, Submodule.mem_span_pair]
    have hx₁S : x₁ ∈ S := (hmemS x₁).2 ⟨1, 0, by simp⟩
    have hSX : S ≤ X := by
      rw [hS]
      refine Submodule.span_le.2 ?_
      rw [hr]
      intro y hy
      rcases hy with rfl | rfl
      · exact hx₁X
      · exact hXinv ρ hρ x₁ hx₁X
    have hρS : ∀ y ∈ S, ρ y ∈ S := by
      intro y hy
      obtain ⟨a, b, rfl⟩ := (hmemS y).1 hy
      rw [map_add, map_smul, map_smul]
      have hneg : ∀ y : V, -y = y := fun y => neg_eq_of_add_eq_zero_left (add_self_eq_zero' y)
      have h2 : ρ (ρ x₁) = ρ x₁ + x₁ := by
        calc ρ (ρ x₁) = -(ρ x₁) - x₁ := by
              calc ρ (ρ x₁) = (ρ (ρ x₁) + ρ x₁ + x₁) - ρ x₁ - x₁ := by abel
                _ = -(ρ x₁) - x₁ := by rw [hquad x₁ hx₁X, zero_sub]
          _ = ρ x₁ + x₁ := by rw [hneg (ρ x₁), sub_eq_add_neg, hneg x₁]
      refine (hmemS _).2 ⟨b, a + b, ?_⟩
      rw [h2]
      simp only [smul_add, add_smul]
      abel
    have hSinv : Inv2 E S := by
      intro g hg y hy
      obtain ⟨k, hk⟩ := huni g hg
      have hyX : y ∈ X := hSX hy
      rw [hk y hyX]
      fin_cases k
      · show (ρ ^ (0 : ℕ)) y ∈ S
        rw [pow_zero_apply]
        exact hy
      · show (ρ ^ (1 : ℕ)) y ∈ S
        rw [pow_one_apply]
        exact hρS y hy
      · show (ρ ^ (2 : ℕ)) y ∈ S
        rw [pow_two_apply]
        exact hρS _ (hρS y hy)
    have hSne : S ≠ ⊥ := by
      intro h0
      rw [h0] at hx₁S
      exact hx₁ ((Submodule.mem_bot _).1 hx₁S)
    have hSeq : S = X := (hirr.2 S hSX hSinv).resolve_left hSne
    have hZ : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    have hli : LinearIndependent (ZMod 2) ![x₁, ρ x₁] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      rcases hZ s with rfl | rfl <;> rcases hZ t with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · exfalso
        simp only [zero_smul, one_smul, zero_add] at hst
        apply hx₁
        rw [← hρ3 x₁ hx₁X, hst, map_zero, map_zero]
      · exfalso
        simp only [one_smul, zero_smul, add_zero] at hst
        exact hx₁ hst
      · exfalso
        simp only [one_smul] at hst
        have hρx : ρ x₁ = x₁ := by
          calc ρ x₁ = ρ x₁ + (x₁ + x₁) := by rw [add_self_eq_zero', add_zero]
            _ = (x₁ + ρ x₁) + x₁ := by abel
            _ = x₁ := by rw [hst, zero_add]
        exact hx₁ (hfix x₁ hx₁X hρx)
    have hfr : Module.finrank (ZMod 2) S = 2 := by
      rw [hS, finrank_span_eq_card hli]
      simp
    rw [← hSeq]
    exact hfr

theorem pow_fin3_unique {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {X : Submodule (ZMod 2) V} (hirr : IsIrrE E X) {ρ : V ≃ₗ[ZMod 2] V} (hρ : ρ ∈ E)
    (hfix : ∀ x ∈ X, ρ x = x → x = 0) {k k' : Fin 3}
    (h : ∀ x ∈ X, (ρ ^ (k : ℕ)) x = (ρ ^ (k' : ℕ)) x) : k = k' := by
  obtain ⟨x, hxX, hx0⟩ := exists_ne_zero_of_ne_bot hirr.1
  have hρ3 : ∀ y, ρ (ρ (ρ y)) = y := fun y => cube_apply (pow3_eq_one_of_mem hE hρ) y
  have hkey := h x hxX
  have hfixx : ρ x = x → False := fun h' => hx0 (hfix x hxX h')
  fin_cases k <;> fin_cases k'
  · rfl
  · simp only [pow_zero_apply, pow_one_apply] at hkey
    exact (hfixx hkey.symm).elim
  · simp only [pow_zero_apply, pow_two_apply] at hkey
    have h1 := congrArg ρ hkey
    rw [hρ3 x] at h1
    exact (hfixx h1).elim
  · simp only [pow_zero_apply, pow_one_apply] at hkey
    exact (hfixx hkey).elim
  · rfl
  · simp only [pow_one_apply, pow_two_apply] at hkey
    have h1 := congrArg ρ hkey
    rw [hρ3 x] at h1
    exact (hfixx (hkey.trans h1)).elim
  · simp only [pow_zero_apply, pow_two_apply] at hkey
    have h1 := congrArg ρ hkey
    rw [hρ3 x] at h1
    exact (hfixx h1.symm).elim
  · simp only [pow_one_apply, pow_two_apply] at hkey
    have h1 := congrArg ρ hkey
    rw [hρ3 x] at h1
    exact (hfixx (h1.trans hkey).symm).elim
  · rfl

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

end
