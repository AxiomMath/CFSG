module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

theorem card_modEq_card_fixed_of_pow_eq_one {S : Type*} [Finite S] {r : ℕ} (hr : r.Prime)
    (σ : Equiv.Perm S) (hσ : σ ^ r = 1) :
    Nat.card S ≡ Nat.card {x : S // σ x = x} [MOD r] := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hord : orderOf σ ∣ r := orderOf_dvd_of_pow_eq_one hσ
  have hG : IsPGroup r (Subgroup.zpowers σ) := by
    rcases (Nat.dvd_prime hr).1 hord with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1]; simp)
  have h := hG.card_modEq_card_fixedPoints S
  have hfix : MulAction.fixedPoints (Subgroup.zpowers σ) S = {x | σ x = x} := by
    ext x
    constructor
    · intro hx
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx g
      obtain ⟨g, hg⟩ := g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx k
  rw [hfix] at h
  exact h

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Module.Finite F V]

theorem card_fixed_eq_pow (g : V ≃ₗ[F] V) :
    ∃ k : ℕ, k ≤ Module.finrank F V ∧ Nat.card {x : V // g x = x} = Nat.card F ^ k ∧
      (k = Module.finrank F V → g = 1) ∧ (k = 0 → ∀ x : V, g x = x → x = 0) := by
  haveI : Finite V := Module.finite_of_finite F
  let C : Submodule F V := LinearMap.ker (g.toLinearMap - LinearMap.id)
  have hC : ∀ x : V, x ∈ C ↔ g x = x := fun x => by
    simp [C, LinearMap.mem_ker, sub_eq_zero]
  refine ⟨Module.finrank F C, Submodule.finrank_le C, ?_, ?_, ?_⟩
  · have h1 : Nat.card {x : V // g x = x} = Nat.card C :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => (hC x).symm)
    rw [h1, Module.natCard_eq_pow_finrank (K := F)]
  · intro hk
    have htop : C = ⊤ := Submodule.eq_top_of_finrank_eq hk
    ext x
    exact (hC x).1 (htop ▸ Submodule.mem_top)
  · intro hk x hx
    have hbot : C = ⊥ := Submodule.finrank_eq_zero.1 hk
    have : x ∈ C := (hC x).2 hx
    rwa [hbot, Submodule.mem_bot] at this

theorem pow_modEq_one_of_invariant {r : ℕ} (hr : r.Prime) (g : V ≃ₗ[F] V) (hg : g ^ r = 1)
    (W : Submodule F V) (hW : ∀ v ∈ W, g v ∈ W) (hfix : ∀ x : V, x ∈ W → g x = x → x = 0) :
    Nat.card F ^ Module.finrank F W ≡ 1 [MOD r] := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite W := inferInstance
  have hinj : Function.Injective fun w : W => (⟨g w, hW w w.2⟩ : W) := by
    intro a b hab
    exact Subtype.ext (g.injective (congrArg Subtype.val hab))
  let σ : Equiv.Perm W := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσw : ∀ w : W, ((σ w : W) : V) = g w := fun w => rfl
  have hσ : σ ^ r = 1 := by
    ext w
    have key : ∀ (n : ℕ) (w : W), (((σ ^ n) w : W) : V) = (g ^ n) w := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, LinearEquiv.mul_apply, ih (σ w), hσw]
    have := key r w
    rw [hg] at this
    simpa using this
  have h := card_modEq_card_fixed_of_pow_eq_one hr σ hσ
  have h1 : Nat.card {x : W // σ x = x} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, ?_⟩⟩⟩
    · apply Subtype.ext
      apply Subtype.ext
      have ha := hfix a.1.1 a.1.2 (by rw [← hσw]; exact congrArg Subtype.val a.2)
      have hb := hfix b.1.1 b.1.2 (by rw [← hσw]; exact congrArg Subtype.val b.2)
      rw [ha, hb]
    · apply Subtype.ext
      rw [hσw]
      simp
  rw [h1, Module.natCard_eq_pow_finrank (K := F)] at h
  exact h

theorem submodule_eq_bot_or_top_of_ppd {r : ℕ} (hr : r.Prime) (g : V ≃ₗ[F] V) (hg : g ^ r = 1)
    (hg1 : g ≠ 1) (hdvd : r ∣ Nat.card F ^ Module.finrank F V - 1)
    (hmin : ∀ k : ℕ, 0 < k → k < Module.finrank F V → ¬ r ∣ Nat.card F ^ k - 1)
    (W : Submodule F V) (hW : ∀ v ∈ W, g v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  haveI : Finite V := Module.finite_of_finite F
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hVfix : ∀ x : V, g x = x → x = 0 := by
    obtain ⟨k, hkd, hcard, hkn, hk0⟩ := card_fixed_eq_pow g
    have hkey : ∀ (n : ℕ) (x : V), (g.toEquiv ^ n) x = (g ^ n) x := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
        intro x
        rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, LinearEquiv.mul_apply, ih]
        rfl
    have hmod := card_modEq_card_fixed_of_pow_eq_one hr g.toEquiv (by
      ext x
      rw [hkey, hg]
      rfl)
    rw [Module.natCard_eq_pow_finrank (K := F)] at hmod
    have h1 : 1 ≡ Nat.card F ^ Module.finrank F V [MOD r] :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq)).2 hdvd
    have h2 : Nat.card {x : V // g.toEquiv x = x} = Nat.card F ^ k := hcard
    have h3 : Nat.card F ^ k ≡ 1 [MOD r] := by
      rw [h2] at hmod
      exact hmod.symm.trans h1.symm
    have h4 : r ∣ Nat.card F ^ k - 1 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq)).1 h3.symm
    have hk : k = 0 := by
      by_contra hne
      rcases Nat.lt_or_ge k (Module.finrank F V) with hlt | hge
      · exact hmin k (Nat.pos_of_ne_zero hne) hlt h4
      · exact hg1 (hkn (le_antisymm hkd hge))
    exact hk0 hk
  have hWfix : ∀ x : V, x ∈ W → g x = x → x = 0 := fun x _ hx => hVfix x hx
  have hmod := pow_modEq_one_of_invariant hr g hg W hW hWfix
  have h4 : r ∣ Nat.card F ^ Module.finrank F W - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq)).1 hmod.symm
  have hd : Module.finrank F W ≤ Module.finrank F V := Submodule.finrank_le W
  by_cases h0 : Module.finrank F W = 0
  · left
    exact Submodule.finrank_eq_zero.1 h0
  · right
    rcases Nat.lt_or_ge (Module.finrank F W) (Module.finrank F V) with hlt | hge
    · exact absurd h4 (hmin _ (Nat.pos_of_ne_zero h0) hlt)
    · exact Submodule.eq_top_of_finrank_eq (le_antisymm hd hge)

variable [CharP F 2]

theorem exists_ne_zero_fixed [Nontrivial V] (R : Subgroup (V ≃ₗ[F] V)) (hR : IsPGroup 2 R) :
    ∃ v : V, v ≠ 0 ∧ ∀ g ∈ R, g v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite V := Module.finite_of_finite F
  by_contra hno
  push Not at hno
  have h := hR.card_modEq_card_fixedPoints V
  have hfix : MulAction.fixedPoints R V = {0} := by
    ext v
    constructor
    · intro hv
      by_contra hv0
      obtain ⟨g, hg, hgv⟩ := hno v hv0
      exact hgv (hv ⟨g, hg⟩)
    · intro hv g
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact map_zero g.1
  rw [hfix] at h
  have hcard1 : Nat.card (({0} : Set V) : Type _) = 1 := by simp
  rw [hcard1] at h
  have heven : Even (Nat.card V) := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    have hfin : 0 < Module.finrank F V := Module.finrank_pos
    have hF : Even (Nat.card F) := by
      haveI : Fintype F := Fintype.ofFinite F
      have := FiniteField.even_card_of_char_two (F := F) (ringChar.eq F 2)
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr this
    exact hF.pow_of_ne_zero (by omega)
  have h2 : Nat.card V % 2 = 1 % 2 := h
  have h3 := Nat.even_iff.mp heven
  omega

theorem eq_bot_of_irreducible_normalizing [Nontrivial V] (R : Subgroup (V ≃ₗ[F] V))
    (hR : IsPGroup 2 R) (g : V ≃ₗ[F] V) (hg : ∀ x ∈ R, g⁻¹ * x * g ∈ R)
    (hirr : ∀ W : Submodule F V, (∀ v ∈ W, g v ∈ W) → W = ⊥ ∨ W = ⊤) : R = ⊥ := by
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_fixed R hR
  let W : Submodule F V :=
    { carrier := {w | ∀ x ∈ R, x w = w}
      add_mem' := fun {a b} ha hb x hx => by rw [map_add, ha x hx, hb x hx]
      zero_mem' := fun x _ => map_zero x
      smul_mem' := fun c w hw x hx => by rw [map_smul, hw x hx] }
  have hWg : ∀ w ∈ W, g w ∈ W := by
    intro w hw x hx
    have hx' : g⁻¹ * x * g ∈ R := hg x hx
    have h1 : (g⁻¹ * x * g) w = w := hw _ hx'
    have h2 : g⁻¹ (x (g w)) = w := by simpa [LinearEquiv.mul_apply] using h1
    have h3 : g (g⁻¹ (x (g w))) = x (g w) := by
      have : (g * g⁻¹) (x (g w)) = x (g w) := by simp
      simpa [LinearEquiv.mul_apply] using this
    rw [← h3, h2]
  have hWne : W ≠ ⊥ := by
    intro hbot
    have : v ∈ W := hv
    rw [hbot, Submodule.mem_bot] at this
    exact hv0 this
  have hWtop : W = ⊤ := (hirr W hWg).resolve_left hWne
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  ext w
  have hw : w ∈ W := hWtop ▸ Submodule.mem_top
  simpa using hw x hx

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
