module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L218

open Module

theorem card_mulAut_two {E : Type} [CommGroup E] [Finite E] (h2 : ∀ e : E, e * e = 1) (n : ℕ)
    (hn : Nat.card E = 2 ^ n) :
    Nat.card (MulAut E) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  classical
  have : Finite (Additive E) := inferInstanceAs (Finite E)
  have hV : ∀ x : Additive E, (2 : ℕ) • x = 0 := by
    intro x
    have := h2 (Additive.toMul x)
    rw [two_nsmul]
    exact this
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfr : Module.finrank (ZMod 2) (Additive E) = n := by
    have := FiniteField.pow_finrank_eq_natCard 2 (Additive E)
    have h3 : Nat.card (Additive E) = 2 ^ n := hn
    rw [h3] at this
    exact Nat.pow_right_injective (le_refl 2) this
  have : Module.Finite (ZMod 2) (Additive E) := inferInstance
  let L : Additive E ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hfr])
  let Φ : MulAut E ≃ (Additive E ≃ₗ[ZMod 2] Additive E) :=
    (MulEquiv.toAdditive (G := E) (H := E)).trans
      { toFun := fun e => { e with map_smul' := fun c x => ZMod.map_smul e c x }
        invFun := fun f => f.toAddEquiv
        left_inv := fun e => rfl
        right_inv := fun f => rfl }
  let Ψ : (Additive E ≃ₗ[ZMod 2] Additive E) ≃ GL (Fin n) (ZMod 2) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive E)).symm.toEquiv.trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv L).toEquiv).trans
      (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := ZMod 2)).symm.toEquiv
  rw [Nat.card_congr (Φ.trans Ψ), Matrix.card_GL_field n]
  simp [ZMod.card]

theorem exists_linearEquiv_apply_eq (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ g : V ≃ₗ[K] V, g a = b := by
  let f : (K ∙ a) ≃ₗ[K] (K ∙ b) :=
    (LinearEquiv.toSpanNonzeroSingleton K V a ha).symm ≪≫ₗ
      (LinearEquiv.toSpanNonzeroSingleton K V b hb)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  have := hg ⟨a, Submodule.mem_span_singleton_self a⟩
  rw [← this]
  have h1 : (LinearEquiv.toSpanNonzeroSingleton K V a ha).symm
      ⟨a, Submodule.mem_span_singleton_self a⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp
  simp [f, h1]

theorem exists_mulAut_apply {E : Type} [CommGroup E] [Finite E] (h2 : ∀ e : E, e * e = 1) (a b : E)
    (ha : a ≠ 1) (hb : b ≠ 1) : ∃ σ : MulAut E, σ a = b := by
  classical
  have : Finite (Additive E) := inferInstanceAs (Finite E)
  have hV : ∀ x : Additive E, (2 : ℕ) • x = 0 := by
    intro x
    have := h2 (Additive.toMul x)
    rw [two_nsmul]
    exact this
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule hV
  have : Module.Finite (ZMod 2) (Additive E) := inferInstance
  have ha' : (Additive.ofMul a) ≠ 0 := fun h => ha (by simpa using h)
  have hb' : (Additive.ofMul b) ≠ 0 := fun h => hb (by simpa using h)
  obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq (ZMod 2) (Additive E) _ _ ha' hb'
  let σ : MulAut E :=
    { toFun := fun e => Additive.toMul (g (Additive.ofMul e))
      invFun := fun e => Additive.toMul (g.symm (Additive.ofMul e))
      left_inv := fun e => by simp
      right_inv := fun e => by simp
      map_mul' := fun x y => by
        have := g.map_add (Additive.ofMul x) (Additive.ofMul y)
        exact this }
  refine ⟨σ, ?_⟩
  show Additive.toMul (g (Additive.ofMul a)) = b
  rw [hg]; rfl

@[expose] def fixE {E : Type} [CommGroup E] (g : MulAut E) : Subgroup E :=
  MonoidHom.eqLocus g.toMonoidHom (MonoidHom.id E)

theorem mem_fixE {E : Type} [CommGroup E] (g : MulAut E) (e : E) : e ∈ fixE g ↔ g e = e :=
  Iff.rfl

theorem card_le_fix_sq {V : Type} [CommGroup V] [Finite V] (hsq : ∀ a : V, a * a = 1)
    (σ : V →* V) (hσ : ∀ v, σ (σ v) = v) :
    Nat.card V ≤ Nat.card {v : V // σ v = v} ^ 2 := by
  classical
  let δ : V →* V := MonoidHom.mk' (fun w => w * σ w) (by
    intro a b
    simp only [map_mul]
    exact mul_mul_mul_comm a b (σ a) (σ b))
  have hδ : ∀ w, δ w = w * σ w := fun w => rfl
  let Fx : Subgroup V := MonoidHom.eqLocus σ (MonoidHom.id V)
  have hFx : ∀ v, v ∈ Fx ↔ σ v = v := fun v => Iff.rfl
  have hinv : ∀ a : V, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  have hker : δ.ker ≤ Fx := by
    intro w hw
    rw [MonoidHom.mem_ker, hδ] at hw
    rw [hFx]
    have : σ w = w⁻¹ := eq_inv_of_mul_eq_one_right hw
    rw [this, hinv]
  have hrange : δ.range ≤ Fx := by
    rintro _ ⟨w, rfl⟩
    rw [hFx, hδ]
    simp only [map_mul, hσ]
    exact mul_comm _ _
  have hFxcard : Nat.card Fx = Nat.card {v : V // σ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hFx)
  have h1 : Nat.card V = Nat.card (V ⧸ δ.ker) * Nat.card δ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
  have h2 : Nat.card (V ⧸ δ.ker) = Nat.card δ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv
  have h3 : Nat.card δ.range ≤ Nat.card Fx := Subgroup.card_le_of_le hrange
  have h4 : Nat.card δ.ker ≤ Nat.card Fx := Subgroup.card_le_of_le hker
  rw [h1, h2, ← hFxcard, sq]
  exact Nat.mul_le_mul h3 h4

theorem card_le_fixE_sq {E : Type} [CommGroup E] [Finite E] (h2 : ∀ e : E, e * e = 1)
    (g : MulAut E) (hg : g * g = 1) : Nat.card E ≤ Nat.card (fixE g) ^ 2 := by
  have hgg : ∀ v : E, g.toMonoidHom (g.toMonoidHom v) = v := by
    intro v
    have := congrArg (fun m : MulAut E => m v) hg
    simpa using this
  have := card_le_fix_sq h2 g.toMonoidHom hgg
  have e : {v : E // g.toMonoidHom v = v} ≃ fixE g := Equiv.refl _
  rwa [Nat.card_congr e] at this

theorem card_le_fixE_sq_sub {E : Type} [CommGroup E] [Finite E] (h2 : ∀ e : E, e * e = 1)
    (g : MulAut E) (hg : g * g = 1) (W : Subgroup E) (hW : ∀ e ∈ W, g e ∈ W) :
    Nat.card W ≤ Nat.card ↥(W ⊓ fixE g) ^ 2 := by
  let σ : W →* W :=
    { toFun := fun w => ⟨g (w : E), hW w w.2⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun a b => Subtype.ext (map_mul g (a : E) (b : E)) }
  have hσσ : ∀ w : W, σ (σ w) = w := by
    intro w
    apply Subtype.ext
    have := congrArg (fun m : MulAut E => m (w : E)) hg
    simpa [σ] using this
  have hsq : ∀ a : W, a * a = 1 := fun a => Subtype.ext (h2 a)
  have := card_le_fix_sq hsq σ hσσ
  have e : {w : W // σ w = w} ≃ ↥(W ⊓ fixE g) :=
    { toFun := fun w => ⟨w.1.1, w.1.2, congrArg Subtype.val w.2⟩
      invFun := fun e => ⟨⟨e.1, e.2.1⟩, Subtype.ext e.2.2⟩
      left_inv := fun w => rfl
      right_inv := fun e => rfl }
  rwa [Nat.card_congr e] at this

theorem lemmaG {E : Type} [CommGroup E] (h2 : ∀ e : E, e * e = 1) (s g : MulAut E)
    (hs : s * s = 1) (hcomm : g * s = s * g) (hfix : ∀ e, s e = e → g e = e) :
    g * g = 1 := by
  have hss : ∀ e : E, s (s e) = e := by
    intro e
    have := congrArg (fun m : MulAut E => m e) hs
    simpa using this
  have hgs : ∀ e : E, g (s e) = s (g e) := by
    intro e
    have := congrArg (fun m : MulAut E => m e) hcomm
    simpa using this
  have hinv : ∀ a : E, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (h2 a)
  ext e
  have hδ : g e * s (g e) = e * s e := by
    rw [← hgs, ← map_mul]
    apply hfix
    rw [map_mul, hss, mul_comm]
  have h3 : s (g e * e) = g e * e := by
    have hsa : s (g e) = g e * (e * s e) := by
      have : s (g e) = (g e)⁻¹ * (e * s e) := by
        rw [← hδ]; group
      rw [this, hinv]
    rw [map_mul, hsa]
    calc g e * (e * s e) * s e = g e * e * (s e * s e) := by group
      _ = g e * e := by rw [h2 (s e), mul_one]
  have h4 := hfix _ h3
  rw [map_mul] at h4
  show g (g e) = e
  have : g (g e) = g e * e * (g e)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]; exact h4
  rw [this, hinv, mul_comm (g e) e, mul_assoc, h2, mul_one]

theorem card_fix_modEq {E : Type} [CommGroup E] [Finite E] (g : MulAut E) (D : Subgroup E)
    (hD : ∀ e, e ∈ D → g e ∈ D) (p n : ℕ) [Fact p.Prime] (hg : g ^ p ^ n = 1) :
    Nat.card D ≡ Nat.card {d : D // g d = d} [MOD p] := by
  classical
  have : Fintype D := Fintype.ofFinite D
  let f : Function.End D := fun d => ⟨g d, hD d d.2⟩
  have hf : ∀ k : ℕ, ∀ d : D, ((f ^ k) d : E) = (g ^ k) d := by
    intro k
    induction k with
    | zero => intro d; rfl
    | succ k ih =>
      intro d
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f d) : E) = (g ^ k) (g d)
      rw [ih]
  have hfp : f ^ p ^ n = 1 := by
    funext d
    apply Subtype.ext
    rw [hf, hg]
    rfl
  have := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := n) hfp
  rw [Nat.card_eq_fintype_card]
  have h2 : Nat.card {d : D // g d = d} = Fintype.card f.fixedPoints := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun d => by
      show g d = d ↔ f d = d
      constructor
      · intro h; exact Subtype.ext h
      · intro h; exact congrArg Subtype.val h)
  rw [h2]
  exact this

theorem fix_card_cases {E : Type} [CommGroup E] [Finite E] (s g : MulAut E)
    (hcomm : g * s = s * g) (p : ℕ) [Fact p.Prime] (hg : g ^ p = 1)
    (hD : Nat.card (fixE s) = 4) :
    Nat.card ↥(fixE s ⊓ fixE g) ∣ 4 ∧ Nat.card ↥(fixE s ⊓ fixE g) ≡ 4 [MOD p] := by
  have hDinv : ∀ e, e ∈ fixE s → g e ∈ fixE s := by
    intro e he
    rw [mem_fixE] at he ⊢
    have := congrArg (fun m : MulAut E => m e) hcomm
    simp only [MulAut.mul_apply] at this
    rw [← this, he]
  have hmod := card_fix_modEq g (fixE s) hDinv p 1 (by simpa using hg)
  have e : {d : fixE s // g d = d} ≃ ↥(fixE s ⊓ fixE g) :=
    { toFun := fun d => ⟨d.1.1, d.1.2, (mem_fixE g _).mpr d.2⟩
      invFun := fun d => ⟨⟨d.1, d.2.1⟩, (mem_fixE g _).mp d.2.2⟩
      left_inv := fun d => rfl
      right_inv := fun d => rfl }
  rw [Nat.card_congr e, hD] at hmod
  refine ⟨?_, hmod.symm⟩
  rw [← hD]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem fixE_trivial_of_free {E : Type} [CommGroup E] [Finite E] (h2 : ∀ e : E, e * e = 1)
    (s u : MulAut E) (hs : s * s = 1) (hD : Nat.card (fixE s) = 4) (hcomm : u * s = s * u)
    (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) : ∀ e, u e = e → e = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdvd, hmod⟩ := fix_card_cases s u hcomm 3 hu3 hD
  have hc : Nat.card ↥(fixE s ⊓ fixE u) = 1 ∨ Nat.card ↥(fixE s ⊓ fixE u) = 4 := by
    have hmem : Nat.card ↥(fixE s ⊓ fixE u) ∈ Nat.divisors 4 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h4 : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [h4] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact Or.inl h
    · rw [h] at hmod
      exact absurd hmod (by decide)
    · exact Or.inr h
  have hss : ∀ e : E, s (s e) = e := by
    intro e
    have := congrArg (fun m : MulAut E => m e) hs
    simpa using this
  have hus : ∀ e : E, u (s e) = s (u e) := by
    intro e
    have := congrArg (fun m : MulAut E => m e) hcomm
    simpa using this
  rcases hc with h1 | h4
  · have hbot : fixE s ⊓ fixE u = ⊥ := Subgroup.card_eq_one.mp h1
    intro e he
    have hd : e * s e ∈ fixE s ⊓ fixE u := by
      refine ⟨(mem_fixE s _).mpr ?_, (mem_fixE u _).mpr ?_⟩
      · rw [map_mul, hss, mul_comm]
      · rw [map_mul, hus, he]
    rw [hbot] at hd
    have hd' : e * s e = 1 := hd
    have hse : s e = e := by
      have h5 : s e = e⁻¹ := eq_inv_of_mul_eq_one_right hd'
      rw [h5]; exact inv_eq_of_mul_eq_one_right (h2 e)
    have he' : e ∈ fixE s ⊓ fixE u := ⟨(mem_fixE s _).mpr hse, (mem_fixE u _).mpr he⟩
    rw [hbot] at he'
    exact he'
  · exfalso
    have hle : fixE s ⊓ fixE u = fixE s :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hD])
    have hfix : ∀ e, s e = e → u e = e := by
      intro e he
      have : e ∈ fixE s ⊓ fixE u := by rw [hle]; exact he
      exact (mem_fixE u _).mp this.2
    have huu := lemmaG h2 s u hs hcomm hfix
    apply hu1
    have : u ^ 3 = u := by rw [pow_succ, pow_two, huu, one_mul]
    rw [← this, hu3]

theorem fixE_card_four {E : Type} [CommGroup E] [Finite E] (h2 : ∀ e : E, e * e = 1)
    (hE : Nat.card E = 16) (s t : MulAut E) (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t = t * s) (hs1 : s ≠ 1) (hint : Nat.card ↥(fixE s ⊓ fixE t) = 2) :
    Nat.card (fixE s) = 4 := by
  have hsq := card_le_fixE_sq h2 s hs
  rw [hE] at hsq
  have hdvd : Nat.card (fixE s) ∣ 16 := hE ▸ Subgroup.card_subgroup_dvd_card (fixE s)
  have hge : 4 ≤ Nat.card (fixE s) := by
    by_contra hlt
    have hlt' : Nat.card (fixE s) < 4 := not_le.mp hlt
    have : Nat.card (fixE s) ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hne16 : Nat.card (fixE s) ≠ 16 := by
    intro h
    apply hs1
    have htop : fixE s = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h, hE])
    ext e
    have : e ∈ fixE s := by rw [htop]; trivial
    exact this
  have hne8 : Nat.card (fixE s) ≠ 8 := by
    intro h8
    have hinv : ∀ e, e ∈ fixE s → t e ∈ fixE s := by
      intro e he
      rw [mem_fixE] at he ⊢
      have := congrArg (fun m : MulAut E => m e) hst
      simp only [MulAut.mul_apply] at this
      rw [this, he]
    have := card_le_fixE_sq_sub h2 t ht (fixE s) hinv
    rw [h8, hint] at this
    omega
  have hmem : Nat.card (fixE s) ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h16 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
  rw [h16] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem card_aut_E {E : Type} [CommGroup E] [Finite E] (h2 : ∀ e : E, e * e = 1)
    (hE : Nat.card E = 16) : Nat.card (MulAut E) = 20160 := by
  rw [card_mulAut_two h2 4 (by rw [hE]; norm_num)]
  decide

theorem card_stab {E : Type} [CommGroup E] [Finite E] (h2 : ∀ e : E, e * e = 1)
    (hE : Nat.card E = 16) (e₀ : E) (he₀ : e₀ ≠ 1) :
    Nat.card (MulAction.stabilizer (MulAut E) e₀) = 1344 := by
  classical
  have hA := card_aut_E h2 hE
  have horb : MulAction.orbit (MulAut E) e₀ = {e | e ≠ 1} := by
    ext e
    constructor
    · rintro ⟨σ, rfl⟩ h
      apply he₀
      have : σ e₀ = σ 1 := by rw [map_one]; exact h
      exact σ.injective this
    · intro he
      obtain ⟨σ, hσ⟩ := exists_mulAut_apply h2 e₀ e he₀ he
      exact ⟨σ, hσ⟩
  have h15 : Nat.card {e : E // e ≠ 1} = 15 := by
    have := Fintype.ofFinite E
    have hE' := hE
    rw [Nat.card_eq_fintype_card] at hE' ⊢
    have h := Fintype.card_subtype_compl (fun e : E => e = 1)
    simp only [Fintype.card_subtype_eq] at h
    rw [hE'] at h
    exact h
  have hcard : Nat.card (MulAction.orbit (MulAut E) e₀) = 15 := by
    rw [horb]
    exact h15
  have hcard' : (MulAction.orbit (MulAut E) e₀).ncard = 15 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (MulAut E) e₀)
  rw [MulAction.index_stabilizer, hcard', hA] at h1
  omega

end L218

end CFSG.GH74.GLS.Bg.TwoGroups
