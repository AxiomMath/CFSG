module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpStruct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.E81C

open CFSG.Open Matrix Module

variable {K : Type} [Field K] [Algebra (ZMod 2) K] {n : ℕ}

private noncomputable def restrictHom (G : Subgroup (GL (Fin n) K))
    (W : Submodule (ZMod 2) (Fin n → K))
    (hW : ∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) :
    G →* (W ≃ₗ[ZMod 2] W) where
  toFun g :=
    { toFun := fun w => ⟨((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K),
        hW g g.2 w w.2⟩
      invFun := fun w => ⟨(((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (w : Fin n → K), hW _ (G.inv_mem g.2) w w.2⟩
      map_add' := fun a b => Subtype.ext (by
        change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((a : Fin n → K) + (b : Fin n → K)) =
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (a : Fin n → K) +
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (b : Fin n → K)
        exact Matrix.mulVec_add _ _ _)
      map_smul' := fun c a => Subtype.ext (by
        change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (c • (a : Fin n → K)) =
          c • (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (a : Fin n → K))
        exact Matrix.mulVec_smul _ c _)
      left_inv := fun w => Subtype.ext (by
        change (((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K)) = w
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec])
      right_inv := fun w => Subtype.ext (by
        change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          ((((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            (w : Fin n → K)) = w
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]) }
  map_one' := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    change ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = w
    rw [Units.val_one, Matrix.one_mulVec]
  map_mul' g g' := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    change (((g * g' : G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
    rw [Matrix.mulVec_mulVec, Subgroup.coe_mul, Units.val_mul]

theorem card_le_of_faithful [Finite K] (G : Subgroup (GL (Fin n) K)) (hG : IsElemAbelian 3 G)
    (W : Submodule (ZMod 2) (Fin n → K))
    (hW : ∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hfaith : ∀ g ∈ G, (∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w) → g = 1) :
    Nat.card G ≤ 3 ^ (finrank (ZMod 2) W / 2) := by
  have hinj : Function.Injective (restrictHom G W hW) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    apply hfaith g g.2
    intro w hw
    have h := congrArg (fun φ : W ≃ₗ[ZMod 2] W => ((φ ⟨w, hw⟩ : W) : Fin n → K)) hg
    have e1 : ((restrictHom G W hW g ⟨w, hw⟩ : W) : Fin n → K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w := rfl
    have e2 : (((1 : W ≃ₗ[ZMod 2] W) ⟨w, hw⟩ : W) : Fin n → K) = w := rfl
    rw [e1, e2] at h
    exact h
  have hE : IsElemAbelian 3 (restrictHom G W hW).range := by
    haveI := hG.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha⟩ := a.2
      obtain ⟨b', hb⟩ := b.2
      apply Subtype.ext
      change (a : W ≃ₗ[ZMod 2] W) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm' a' b']
    · obtain ⟨x', rfl⟩ := hx
      rw [← map_pow]
      have h3 : x' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hG.2 x' x'.2)
      rw [h3, map_one]
  haveI : Finite G := inferInstance
  haveI : Finite (restrictHom G W hW).range :=
    Finite.of_equiv _ (MonoidHom.ofInjective hinj).toEquiv
  haveI : Fintype (restrictHom G W hW).range := Fintype.ofFinite _
  haveI : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have h1 := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.card_le_three_pow_half
    (restrictHom G W hW).range hE
  have h2 : Nat.card G = Nat.card (restrictHom G W hW).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [h2, Nat.card_eq_fintype_card]
  exact h1

private theorem two_eq_zero : (2 : K) = 0 := by
  have h : (2 : K) = algebraMap (ZMod 2) K 2 := by rw [map_ofNat]
  rw [h, show (2 : ZMod 2) = 0 from rfl, map_zero]

private def fixSpace (B : GL (Fin n) K) : Submodule (ZMod 2) (Fin n → K) where
  carrier := {v | (B : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  add_mem' {a b} ha hb := by
    change (B : Matrix (Fin n) (Fin n) K) *ᵥ (a + b) = a + b
    rw [Matrix.mulVec_add, show (B : Matrix (Fin n) (Fin n) K) *ᵥ a = a from ha,
      show (B : Matrix (Fin n) (Fin n) K) *ᵥ b = b from hb]
  zero_mem' := Matrix.mulVec_zero _
  smul_mem' c v hv := by
    change (B : Matrix (Fin n) (Fin n) K) *ᵥ (c • v) = c • v
    rw [Matrix.mulVec_smul, show (B : Matrix (Fin n) (Fin n) K) *ᵥ v = v from hv]

theorem eq_one_of_mulVec {g : GL (Fin n) K}
    (h : ∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v) : g = 1 := by
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, Units.val_one, Matrix.one_mulVec]

theorem card_le_of_commute_involution [Finite K] (G : Subgroup (GL (Fin n) K))
    (hG : IsElemAbelian 3 G) {B : GL (Fin n) K} (hB2 : B * B = 1) (hB1 : B ≠ 1)
    (hcomm : ∀ g ∈ G, g * B = B * g) :
    Nat.card G ≤ 3 ^ ((finrank (ZMod 2) (Fin n → K) - 1) / 2) := by
  have hgB : ∀ g ∈ G, ∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
    intro g hg v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hcomm g hg]
  have hW : ∀ g ∈ G, ∀ w ∈ fixSpace B, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ fixSpace B := by
    intro g hg w hw
    change (B : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) =
      (g : Matrix (Fin n) (Fin n) K) *ᵥ w
    rw [← hgB g hg, show (B : Matrix (Fin n) (Fin n) K) *ᵥ w = w from hw]
  have hBB : ∀ v, (B : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, hB2, Units.val_one, Matrix.one_mulVec]
  have h2K : (2 : K) = 0 := two_eq_zero
  have hfaith : ∀ g ∈ G, (∀ w ∈ fixSpace B, (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w) → g = 1 := by
    intro g hg hfix
    have hu : ∀ v, (B : Matrix (Fin n) (Fin n) K) *ᵥ v + v ∈ fixSpace B := by
      intro v
      change (B : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ v + v) =
        (B : Matrix (Fin n) (Fin n) K) *ᵥ v + v
      rw [Matrix.mulVec_add, hBB, add_comm]
    have hsq : ∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
      intro v
      have h1 := hfix _ (hu v)
      rw [Matrix.mulVec_add, hgB g hg] at h1
      have h3 : (g : Matrix (Fin n) (Fin n) K) *ᵥ v + v ∈ fixSpace B := by
        change (B : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v + v) =
          (g : Matrix (Fin n) (Fin n) K) *ᵥ v + v
        rw [Matrix.mulVec_add]
        funext i
        have h1i := congrFun h1 i
        simp only [Pi.add_apply] at h1i ⊢
        linear_combination h1i + (((B : Matrix (Fin n) (Fin n) K) *ᵥ v) i -
          ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) i) * h2K
      have h4 := hfix _ h3
      rw [Matrix.mulVec_add] at h4
      exact add_right_cancel (h4.trans (add_comm _ _))
    have hg2 : (g : GL (Fin n) K) * g = 1 := by
      refine eq_one_of_mulVec fun v => ?_
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hsq]
    have hg3 : (g : GL (Fin n) K) ^ 3 = 1 := hG.2 g hg
    calc g = g ^ 3 * (g * g)⁻¹ := by group
      _ = 1 := by rw [hg3, hg2, inv_one, one_mul]
  have hlt : finrank (ZMod 2) (fixSpace B) < finrank (ZMod 2) (Fin n → K) := by
    haveI : FiniteDimensional (ZMod 2) (Fin n → K) := Module.Finite.of_finite
    apply Submodule.finrank_lt
    intro htop
    apply hB1
    refine eq_one_of_mulVec fun v => ?_
    have hv : v ∈ fixSpace B := by
      rw [htop]
      exact Submodule.mem_top
    exact hv
  calc Nat.card G ≤ 3 ^ (finrank (ZMod 2) (fixSpace B) / 2) :=
        card_le_of_faithful G hG _ hW hfaith
    _ ≤ 3 ^ ((finrank (ZMod 2) (Fin n → K) - 1) / 2) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (by omega))

@[expose] def InnerOfFix (S : Type) [Group S] : Prop :=
  ∀ E : Subgroup S, IsElemAbelian 3 E → Nat.card E = 3 ^ 4 →
    ∀ t : MulAut S, t ^ 2 = 1 → (∀ e ∈ E, t e = e) → ∃ g : S, t = MulAut.conj g

theorem InnerOfFix.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : InnerOfFix S) : InnerOfFix S' := by
  intro E' hE' hcard t' ht' hfix'
  set E : Subgroup S := E'.comap (e : S →* S') with hEdef
  have hEmap : E.map (e : S →* S') = E' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective E'
  have hEcard : Nat.card E = 3 ^ 4 := by
    rw [← hcard, ← hEmap, Subgroup.card_map_of_injective e.injective]
  have hEab : IsElemAbelian 3 E := by
    obtain ⟨hc, hp⟩ := hE'
    refine ⟨⟨⟨fun a b => Subtype.ext (e.injective ?_)⟩⟩, fun x hx => e.injective ?_⟩
    · have h1 := congrArg Subtype.val (hc.is_comm.comm (⟨e a, a.2⟩ : E') ⟨e b, b.2⟩)
      simpa only [Subgroup.coe_mul, map_mul] using h1
    · rw [map_pow, map_one]
      exact hp (e x) hx
  have ht'x : ∀ y, t' (t' y) = y := fun y => by
    have h1 := congrArg (fun s : MulAut S' => s y) ht'
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h1
  set t : MulAut S := (e.trans t').trans e.symm with htdef
  have htx : ∀ x, t x = e.symm (t' (e x)) := fun x => rfl
  have ht : t ^ 2 = 1 := by
    refine MulEquiv.ext fun x => ?_
    rw [pow_two, MulAut.mul_apply, htx, htx, MulEquiv.apply_symm_apply, ht'x,
      MulEquiv.symm_apply_apply, MulAut.one_apply]
  have hfix : ∀ x ∈ E, t x = x := fun x hx => by
    rw [htx, hfix' (e x) hx, MulEquiv.symm_apply_apply]
  obtain ⟨g, hg⟩ := h E hEab hEcard t ht hfix
  refine ⟨e g, MulEquiv.ext fun y => ?_⟩
  have h1 : t (e.symm y) = g * e.symm y * g⁻¹ := by rw [hg, MulAut.conj_apply]
  rw [htx, MulEquiv.apply_symm_apply] at h1
  have h2 := congrArg e h1
  rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
  rw [MulAut.conj_apply, h2]

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.E81C

end
