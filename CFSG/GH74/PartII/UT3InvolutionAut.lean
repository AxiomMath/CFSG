module

public import CFSG.GH74.PartII.SylowAhat8Model

public section

namespace CFSG.GH74.PartII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.HarrisU33.Outside

theorem elemAbelian_U4 (E : Subgroup U4) (hE : ∀ x ∈ E, x * x = 1) :
    (∀ x ∈ E, x.b = 0) ∨ (∀ x ∈ E, x.a = 0) := by
  have hab : ∀ g : U4, g * g = 1 → g.a * g.b = 0 := by
    intro g hg
    rw [L26.sq_UT3, UT3.one_def] at hg
    have hc : g.c + g.c + g.a * g.b = 0 := congrArg UT3.c hg
    rw [L26.two_add_F4c, zero_add] at hc
    exact hc
  by_cases hb : ∀ x ∈ E, x.b = 0
  · exact Or.inl hb
  · right
    push Not at hb
    obtain ⟨x, hxE, hxb⟩ := hb
    intro y hyE
    by_contra hya
    have hxa : x.a = 0 := by
      rcases mul_eq_zero.mp (hab x (hE x hxE)) with h | h
      · exact h
      · exact absurd h hxb
    have hyb : y.b = 0 := by
      rcases mul_eq_zero.mp (hab y (hE y hyE)) with h | h
      · exact absurd h hya
      · exact h
    have hxyE : x * y ∈ E := E.mul_mem hxE hyE
    have hxy := hab (x * y) (hE (x * y) hxyE)
    rw [UT3.mul_def, hxa, hyb, zero_add, add_zero] at hxy
    exact (mul_ne_zero hya hxb) hxy

private def A1 : Subgroup U4 where
  carrier := {x : U4 | x.b = 0}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    change (x * y).b = 0
    rw [UT3.mul_def, hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    change (x⁻¹).b = 0
    simpa [UT3.inv_def] using hx

private lemma invol_of_b_zero (x : U4) (hx : x.b = 0) : x * x = 1 := by
  rw [L26.sq_UT3, hx, mul_zero, add_zero]
  ext <;> simp [UT3.one_def, L26.two_add_F4c]

theorem b_eq_zero_of_a_preserving (α : MulAut U4) (h : ∀ x : U4, x.a = 0 → (α x).a = 0) :
    ∀ x : U4, x.b = 0 → (α x).b = 0 := by
  intro x hx
  have hmap : ∀ y ∈ A1.map α.toMonoidHom, y * y = 1 := by
    rintro y ⟨z, hz, rfl⟩
    rw [← map_mul, invol_of_b_zero z hz, map_one]
  rcases elemAbelian_U4 (A1.map α.toMonoidHom) hmap with hb | ha
  · exact hb (α x) ⟨x, hx, rfl⟩
  · exfalso
    have hall : ∀ w : U4, (α w).a = 0 := by
      intro w
      have hw : w = (⟨w.a, 0, 0⟩ : U4) * ⟨0, w.b, w.c + w.a * w.b⟩ := by
        refine UT3.ext ?_ ?_ ?_
        · simp only [UT3.mul_def, add_zero, zero_add]
        · simp only [UT3.mul_def, add_zero, zero_add]
        · simp only [UT3.mul_def, add_zero, zero_add]
          rw [add_assoc, L26.two_add_F4c, add_zero]
      rw [hw, map_mul, UT3.mul_def]
      have h1 : (α ⟨w.a, 0, 0⟩).a = 0 :=
        ha (α ⟨w.a, 0, 0⟩) ⟨⟨w.a, 0, 0⟩, rfl, rfl⟩
      have h2 : (α ⟨0, w.b, w.c + w.a * w.b⟩).a = 0 := h _ rfl
      rw [h1, h2, add_zero]
    have hcontra := hall (α.symm ⟨1, 0, 0⟩)
    rw [MulEquiv.apply_symm_apply] at hcontra
    exact one_ne_zero hcontra

private lemma mapsTo_center (α : MulAut U4) {z : U4} (hz : z ∈ center U4) :
    α z ∈ center U4 := by
  obtain ⟨ha, hb⟩ := (mem_center_U4 z).1 hz
  have hz' : z = ⟨0, 0, z.c⟩ := UT3.ext ha hb rfl
  rw [hz', aut_center_eq, mem_center_U4]
  exact ⟨rfl, rfl⟩

theorem exists_center_ne_of_inverts (α δ : MulAut U4) (hδ3 : δ ^ 3 = 1)
    (hδ : ∀ x : U4, δ x = x → x = 1) (hαδ : α * δ * α⁻¹ = δ⁻¹) :
    ∃ z ∈ center U4, α z ≠ z := by
  by_contra h
  push Not at h
  have hzero : (⟨0, 0, 1⟩ : U4) ∈ center U4 := (mem_center_U4 _).2 ⟨rfl, rfl⟩
  have hzero_ne : (⟨0, 0, 1⟩ : U4) ≠ 1 := by
    intro h1
    rw [UT3.one_def] at h1
    have h1c : (1 : F4c) = 0 := congrArg UT3.c h1
    exact one_ne_zero h1c
  have hfix : ∀ z : U4, z ∈ center U4 → z = 1 := by
    intro z hz
    have hαz : α z = z := h z hz
    have hαz_c : α⁻¹ z ∈ center U4 := mapsTo_center α⁻¹ hz
    have hinv : α⁻¹ z = z := by
      have h1 : α (α⁻¹ z) = z := α.apply_symm_apply z
      have h2 : α (α⁻¹ z) = α⁻¹ z := h (α⁻¹ z) hαz_c
      rw [h2] at h1
      exact h1
    have hconj : α (δ (α⁻¹ z)) = δ⁻¹ z := by
      have := congrArg (fun γ : MulAut U4 => γ z) hαδ
      simpa only [MulAut.mul_apply] using this
    rw [hinv] at hconj
    have hδz : δ z ∈ center U4 := mapsTo_center δ hz
    have hαδz : α (δ z) = δ z := h (δ z) hδz
    have hδinv : δ z = δ⁻¹ z := by rw [← hconj, hαδz]
    have hδδ : δ (δ z) = z := by
      have h := congrArg (fun w : U4 => δ w) hδinv
      have h2 : δ (δ⁻¹ z) = z := δ.apply_symm_apply z
      rw [h2] at h
      exact h
    have hδz_eq : δ z = z := by
      have hpow : (δ ^ 3) z = δ (δ (δ z)) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_succ, pow_one]
        rfl
      have hz3 : (δ ^ 3) z = z := by rw [hδ3, MulAut.one_apply]
      rw [hpow, hδδ] at hz3
      exact hz3
    exact hδ z hδz_eq
  exact hzero_ne (hfix ⟨0, 0, 1⟩ hzero)

private def z2 : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)

private lemma z2_mul_self : z2 * z2 = 1 := by decide +kernel

private lemma z2_cases (g : Multiplicative (ZMod 2)) : g = 1 ∨ g = z2 := by
  revert g
  decide +kernel

private lemma invAct_z2 (α : MulAut U4) (hα : α * α = 1) : invAct α hα z2 = α := by
  have hval : (Multiplicative.toAdd z2).val = 1 := by decide +kernel
  show α ^ (Multiplicative.toAdd z2).val = α
  rw [hval, pow_one]

private abbrev semi (α : MulAut U4) (hα : α * α = 1) : Type :=
  U4 ⋊[invAct α hα] Multiplicative (ZMod 2)

private lemma inr_mul_inl {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (g : G) (n : N) :
    (SemidirectProduct.inr g : N ⋊[φ] G) * SemidirectProduct.inl n =
      SemidirectProduct.inl (φ g n) * SemidirectProduct.inr g := by
  have h := SemidirectProduct.inl_aut (φ := φ) g n
  have h' : SemidirectProduct.inl (φ g n) =
      (SemidirectProduct.inr g : N ⋊[φ] G) * SemidirectProduct.inl n *
        (SemidirectProduct.inr g)⁻¹ := by
    simpa only [map_inv] using h
  have h1 : (SemidirectProduct.inr g * SemidirectProduct.inl n *
      (SemidirectProduct.inr g)⁻¹) * SemidirectProduct.inr g =
      (SemidirectProduct.inr g : N ⋊[φ] G) * SemidirectProduct.inl n := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  calc (SemidirectProduct.inr g : N ⋊[φ] G) * SemidirectProduct.inl n
      = (SemidirectProduct.inr g * SemidirectProduct.inl n * (SemidirectProduct.inr g)⁻¹) *
          SemidirectProduct.inr g := h1.symm
    _ = SemidirectProduct.inl (φ g n) * SemidirectProduct.inr g := by rw [← h']

theorem nonempty_mulEquiv_invAct_of_twist {α φ : MulAut U4} (hα : α * α = 1) (hφ : φ * φ = 1)
    (β : MulAut U4) (t : U4) (ht : t * α t = 1) (h : MulAut.conj t * α = β * φ * β⁻¹) :
    Nonempty (U4 ⋊[invAct α hα] Multiplicative (ZMod 2) ≃*
      U4 ⋊[invAct φ hφ] Multiplicative (ZMod 2)) := by
  let u : U4 := β⁻¹ t⁻¹
  let w : semi φ hφ := SemidirectProduct.inl u * SemidirectProduct.inr z2
  have ht' : α t = t⁻¹ := (inv_eq_of_mul_eq_one_right ht).symm
  have hconj_t : (β * φ * β⁻¹) t = t⁻¹ := by
    have hh := congrArg (fun γ : MulAut U4 => γ t) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, ht'] at hh
    simpa using hh.symm
  have hβt : β (φ (β⁻¹ t)) = t⁻¹ := by
    simpa only [MulAut.mul_apply] using hconj_t
  have hβt' : β (φ (β⁻¹ t⁻¹)) = t := by
    have hmap : (β * φ * β⁻¹) t⁻¹ = ((β * φ * β⁻¹) t)⁻¹ := MulEquiv.map_inv _ t
    rw [hconj_t, inv_inv] at hmap
    simpa only [MulAut.mul_apply] using hmap
  have hu : u * φ u = 1 := by
    apply β.injective
    rw [map_mul, map_one]
    have hbu : β u = t⁻¹ := by simp [u]
    have hbpu : β (φ u) = t := by simpa [u] using hβt'
    rw [hbu, hbpu, inv_mul_cancel]
  have hgen_inv : z2⁻¹ = z2 := inv_eq_of_mul_eq_one_right z2_mul_self
  have hgen_inr_mul : (SemidirectProduct.inr z2 : semi φ hφ) *
      SemidirectProduct.inr z2 = 1 := by
    rw [← map_mul, z2_mul_self, map_one]
  have hgen_inr_inv : (SemidirectProduct.inr z2 : semi φ hφ)⁻¹ =
      SemidirectProduct.inr z2 := inv_eq_of_mul_eq_one_right hgen_inr_mul
  have hw_inv : w⁻¹ = (SemidirectProduct.inr z2 : semi φ hφ) *
      SemidirectProduct.inl u⁻¹ := by
    change (SemidirectProduct.inl u * SemidirectProduct.inr z2)⁻¹ =
      SemidirectProduct.inr z2 * SemidirectProduct.inl u⁻¹
    rw [mul_inv_rev, hgen_inr_inv, ← map_inv]
  have hww : w * w = 1 := by
    have hgen_inr : (SemidirectProduct.inr z2 : semi φ hφ) *
        SemidirectProduct.inr z2 = 1 := by
      rw [← map_mul, z2_mul_self, map_one]
    calc w * w
        = SemidirectProduct.inl u * (SemidirectProduct.inr z2 *
            SemidirectProduct.inl u) * SemidirectProduct.inr z2 := by
          simp [w, mul_assoc]
      _ = SemidirectProduct.inl u * (SemidirectProduct.inl ((invAct φ hφ) z2 u) *
            SemidirectProduct.inr z2) * SemidirectProduct.inr z2 := by
          rw [inr_mul_inl]
      _ = (SemidirectProduct.inl u * SemidirectProduct.inl ((invAct φ hφ) z2 u)) *
            (SemidirectProduct.inr z2 * SemidirectProduct.inr z2) := by
          simp [mul_assoc]
      _ = SemidirectProduct.inl (u * (invAct φ hφ) z2 u) * 1 := by
          rw [← map_mul, hgen_inr]
      _ = 1 := by
          rw [invAct_z2, hu, map_one, mul_one]
  have hconj_inr : ∀ y : U4,
      (SemidirectProduct.inr z2 : semi φ hφ) * SemidirectProduct.inl y *
        SemidirectProduct.inr z2 =
      SemidirectProduct.inl ((invAct φ hφ) z2 y) := by
    intro y
    have h := SemidirectProduct.inl_aut (φ := invAct φ hφ) z2 y
    have h' : SemidirectProduct.inl ((invAct φ hφ) z2 y) =
        (SemidirectProduct.inr z2 : semi φ hφ) * SemidirectProduct.inl y *
          (SemidirectProduct.inr z2)⁻¹ := by
      simpa only [map_inv] using h
    rw [hgen_inr_inv] at h'
    exact h'.symm
  have hwconj : ∀ y : U4, w * SemidirectProduct.inl (β⁻¹ y) * w⁻¹ =
      SemidirectProduct.inl (β⁻¹ (α y)) := by
    intro y
    have hkey : u * φ (β⁻¹ y) * u⁻¹ = β⁻¹ (α y) := by
      apply β.injective
      have hbu : β u = t⁻¹ := by simp [u]
      have hbpu : β u⁻¹ = t := by rw [MulEquiv.map_inv, hbu, inv_inv]
      have hβφ : β (φ (β⁻¹ y)) = t * α y * t⁻¹ := by
        have hh := congrArg (fun γ : MulAut U4 => γ y) h
        simp only [MulAut.mul_apply, MulAut.conj_apply] at hh
        exact hh.symm
      have hβsymm : β (β⁻¹ (α y)) = α y := β.apply_symm_apply (α y)
      rw [map_mul, map_mul, hbu, hbpu, hβφ, hβsymm]
      simp [mul_assoc]
    calc w * SemidirectProduct.inl (β⁻¹ y) * w⁻¹
        = SemidirectProduct.inl u * (SemidirectProduct.inr z2 *
            SemidirectProduct.inl (β⁻¹ y) * SemidirectProduct.inr z2) *
            SemidirectProduct.inl u⁻¹ := by
          simp [w, hw_inv, mul_assoc]
      _ = SemidirectProduct.inl u *
            SemidirectProduct.inl ((invAct φ hφ) z2 (β⁻¹ y)) *
            SemidirectProduct.inl u⁻¹ := by
          rw [hconj_inr]
      _ = SemidirectProduct.inl (u * (invAct φ hφ) z2 (β⁻¹ y) * u⁻¹) := by
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = SemidirectProduct.inl (β⁻¹ (α y)) := by
          rw [invAct_z2, hkey]
  let f₁ : U4 →* semi φ hφ :=
    (SemidirectProduct.inl : U4 →* semi φ hφ).comp β.symm.toMonoidHom
  let f₂ : Multiplicative (ZMod 2) →* semi φ hφ :=
    { toFun := fun e => w ^ (Multiplicative.toAdd e).val
      map_one' := by
        show w ^ (Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val = 1
        simp
      map_mul' := by
        intro a b
        have h2 : w ^ 2 = 1 := by rw [pow_two, hww]
        rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ h2, pow_add] }
  have hf1 : ∀ z : U4, f₁ z = SemidirectProduct.inl (β⁻¹ z) := fun z => rfl
  have hf2z2 : f₂ z2 = w := by
    have hval : (Multiplicative.toAdd z2).val = 1 := by decide +kernel
    show w ^ (Multiplicative.toAdd z2).val = w
    rw [hval, pow_one]
  have hcompat : ∀ g : Multiplicative (ZMod 2),
      f₁.comp ((invAct α hα g).toMonoidHom) =
        (MulAut.conj (f₂ g)).toMonoidHom.comp f₁ := by
    intro g
    apply MonoidHom.ext
    intro y
    rcases z2_cases g with rfl | rfl
    · simp only [MonoidHom.comp_apply, map_one]
      rw [hf1, hf1]
      simp
    · rw [invAct_z2]
      simp only [MonoidHom.comp_apply]
      rw [hf1, hf1, hf2z2]
      exact (hwconj y).symm
  let F : semi α hα →* semi φ hφ := SemidirectProduct.lift f₁ f₂ hcompat
  have hsurj : Function.Surjective F := by
    intro y
    have hy : y = (SemidirectProduct.inl y.left : semi φ hφ) *
        SemidirectProduct.inr y.right := (SemidirectProduct.inl_left_mul_inr_right y).symm
    rw [hy]
    rcases z2_cases y.right with hr | hr
    · refine ⟨SemidirectProduct.inl (β y.left), ?_⟩
      rw [SemidirectProduct.lift_inl, hr]
      simp [hf1]
    · refine ⟨SemidirectProduct.inl (β (y.left * u⁻¹)) * SemidirectProduct.inr z2, ?_⟩
      rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr, hr]
      rw [hf1, hf2z2]
      simp [w, mul_assoc]
  have hcard : Fintype.card (semi α hα) = Fintype.card (semi φ hφ) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      SemidirectProduct.card, SemidirectProduct.card, card_UT3c]
  have hbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_surjective_and_card]
    exact ⟨hsurj, hcard⟩
  exact ⟨MulEquiv.ofBijective F hbij⟩

private lemma swapAut_swapAut (x : U4) : swapAut (swapAut x) = x := by
  refine UT3.ext rfl rfl ?_
  change (x.c + x.a * x.b) + x.b * x.a = x.c
  rw [add_assoc, mul_comm x.b x.a, L26.two_add_F4c, add_zero]

private lemma a_eq_zero_of_b_preserving (α : MulAut U4)
    (h : ∀ x : U4, x.b = 0 → (α x).b = 0) :
    ∀ x : U4, x.a = 0 → (α x).a = 0 := by
  have hβ : ∀ x : U4, x.a = 0 → ((swapAut * α * swapAut) x).a = 0 := by
    intro x hx
    have h1 : (swapAut x).b = 0 := by simpa [swapAut] using hx
    have h2 : (α (swapAut x)).b = 0 := h (swapAut x) h1
    simpa [MulAut.mul_apply, swapAut] using h2
  have hb := b_eq_zero_of_a_preserving (swapAut * α * swapAut) hβ
  intro x hx
  have hy : (swapAut x).b = 0 := by simpa [swapAut] using hx
  have hz := hb (swapAut x) hy
  have hz' : ((swapAut * α * swapAut) (swapAut x)).b = (α x).a := by
    simp only [MulAut.mul_apply]
    rw [swapAut_swapAut x]
    rfl
  rw [hz'] at hz
  exact hz

private lemma linAdd_block_diag (α : MulAut U4)
    (hA : ∀ x : U4, x.b = 0 → (α x).b = 0) (a b : F4c) :
    linAdd α (a, b) = ((α ⟨a, 0, 0⟩).a, (α ⟨0, b, 0⟩).b) := by
  have h1 : linAdd α (a, 0) = ((α ⟨a, 0, 0⟩).a, 0) := by
    rw [linAdd_apply α ⟨a, 0, 0⟩]
    exact Prod.ext rfl (hA ⟨a, 0, 0⟩ rfl)
  have h2 : linAdd α (0, b) = (0, (α ⟨0, b, 0⟩).b) := by
    have ha := a_eq_zero_of_b_preserving α hA ⟨0, b, 0⟩ rfl
    rw [linAdd_apply α ⟨0, b, 0⟩]
    exact Prod.ext ha rfl
  calc linAdd α (a, b) = linAdd α ((a, 0) + (0, b)) := by
        rw [show (a, 0) + (0, b) = (a, b) from by ext <;> simp]
    _ = linAdd α (a, 0) + linAdd α (0, b) := map_add _ _ _
    _ = ((α ⟨a, 0, 0⟩).a, (α ⟨0, b, 0⟩).b) := by
        rw [h1, h2]
        ext <;> simp

private lemma diag_classify_aux : ∀ p q r s : F4c, p ≠ 0 → r ≠ 0 →
    (∀ a b : F4c, sigOf (p, q) a * sigOf (r, s) b = sigOf (p, q) (a * b) * r) →
    ((∀ a : F4c, sigOf (p, q) a = p * a) ∧ ∀ b : F4c, sigOf (r, s) b = r * b) ∨
    ((∀ a : F4c, sigOf (p, q) a = p * (a * a)) ∧
      ∀ b : F4c, sigOf (r, s) b = r * (b * b)) := by
  decide +kernel

private lemma linAdd_diag_classify (α : MulAut U4) (hA : ∀ x : U4, x.b = 0 → (α x).b = 0) :
    ∃ l m : F4c, l ≠ 0 ∧ m ≠ 0 ∧
      ((∀ v : V4, linAdd α v = (l * v.1, m * v.2)) ∨
        ∀ v : V4, linAdd α v = (l * (v.1 * v.1), m * (v.2 * v.2))) := by
  let L₁ : F4c →+ F4c :=
    (AddMonoidHom.fst F4c F4c).comp ((linAdd α).comp (AddMonoidHom.inl F4c F4c))
  let L₂ : F4c →+ F4c :=
    (AddMonoidHom.snd F4c F4c).comp ((linAdd α).comp (AddMonoidHom.inr F4c F4c))
  have hdiag : ∀ v : V4, linAdd α v = (L₁ v.1, L₂ v.2) := by
    intro v
    simp only [L₁, L₂, AddMonoidHom.comp_apply, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply,
      AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, linAdd_block_diag α hA]
  have hsq : ∀ a b : F4c, L₁ a * L₂ b = sigAdd α (a * b) := by
    intro a b
    have h := sqF_linAdd α (a, b)
    rwa [hdiag] at h
  have hcond : ∀ a b : F4c, sigOf (L₁ 1, L₁ omg) a * sigOf (L₂ 1, L₂ omg) b =
      sigOf (L₁ 1, L₁ omg) (a * b) * L₂ 1 := by
    intro a b
    rw [sigOf_apply, sigOf_apply, sigOf_apply, hsq, hsq, mul_one]
  have hne : ∀ v : V4, v ≠ 0 → linAdd α v ≠ 0 := fun v hv h0 =>
    hv (linAdd_injective α (h0.trans (map_zero (linAdd α)).symm))
  have hp : L₁ 1 ≠ 0 := by
    intro h0
    apply hne (1, 0) (by simp)
    rw [hdiag, h0, map_zero]
    rfl
  have hr : L₂ 1 ≠ 0 := by
    intro h0
    apply hne (0, 1) (by simp)
    rw [hdiag, h0, map_zero]
    rfl
  refine ⟨L₁ 1, L₂ 1, hp, hr, ?_⟩
  rcases diag_classify_aux (L₁ 1) (L₁ omg) (L₂ 1) (L₂ omg) hp hr hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    intro v
    rw [hdiag, ← sigOf_apply L₁ v.1, ← sigOf_apply L₂ v.2, h1, h2]
  · right
    intro v
    rw [hdiag, ← sigOf_apply L₁ v.1, ← sigOf_apply L₂ v.2, h1, h2]

private lemma alpha_form_of_frob (α : MulAut U4) (l m : F4c)
    (hlin : ∀ v : V4, linAdd α v = (l * (v.1 * v.1), m * (v.2 * v.2)))
    (hσ : ∀ c : F4c, sigAdd α c = l * m * (c * c)) (x : U4) :
    α x = ⟨l * (x.a * x.a), m * (x.b * x.b),
      l * m * (x.c * x.c) + (α ⟨x.a, x.b, 0⟩).c⟩ := by
  have hx : x = (⟨x.a, x.b, 0⟩ : U4) * ⟨0, 0, x.c⟩ := by
    refine UT3.ext ?_ ?_ ?_
    · simp only [UT3.mul_def, add_zero, mul_zero, zero_add]
    · simp only [UT3.mul_def, add_zero, mul_zero, zero_add]
    · simp only [UT3.mul_def, add_zero, mul_zero, zero_add]
  have hx0 : α ⟨x.a, x.b, 0⟩ = ⟨l * (x.a * x.a), m * (x.b * x.b),
      (α ⟨x.a, x.b, 0⟩).c⟩ := by
    refine UT3.ext ?_ ?_ rfl
    · have h := congrArg Prod.fst (linAdd_apply α ⟨x.a, x.b, 0⟩)
      rw [hlin] at h
      exact h.symm
    · have h := congrArg Prod.snd (linAdd_apply α ⟨x.a, x.b, 0⟩)
      rw [hlin] at h
      exact h.symm
  have hcent : α ⟨0, 0, x.c⟩ = ⟨0, 0, l * m * (x.c * x.c)⟩ := by
    rw [aut_center_eq, hσ]
  have hx' : α x = α ((⟨x.a, x.b, 0⟩ : U4) * ⟨0, 0, x.c⟩) := congrArg α hx
  rw [hx', map_mul, hx0, hcent, UT3.mul_def]
  refine UT3.ext ?_ ?_ ?_
  · simp
  · simp
  · simp [add_comm]

private lemma G_add_of_frob (α : MulAut U4) (l m : F4c)
    (hform : ∀ x : U4, α x = ⟨l * (x.a * x.a), m * (x.b * x.b),
      l * m * (x.c * x.c) + (α ⟨x.a, x.b, 0⟩).c⟩)
    (a b a' b' : F4c) :
    (α ⟨a + a', b + b', 0⟩).c =
      (α ⟨a, b, 0⟩).c + (α ⟨a', b', 0⟩).c := by
  have hxy : (⟨a, b, 0⟩ : U4) * ⟨a', b', 0⟩ = ⟨a + a', b + b', a * b'⟩ := by
    ext <;> simp [UT3.mul_def]
  have hL : (α ⟨a + a', b + b', a * b'⟩).c =
      l * m * ((a * b') * (a * b')) + (α ⟨a + a', b + b', 0⟩).c := by
    have := hform ⟨a + a', b + b', a * b'⟩
    simpa using congrArg UT3.c this
  have hR : (α ⟨a, b, 0⟩ * α ⟨a', b', 0⟩).c =
      (α ⟨a, b, 0⟩).c + (α ⟨a', b', 0⟩).c +
        (α ⟨a, b, 0⟩).a * (α ⟨a', b', 0⟩).b := by
    rw [UT3.mul_def]
  have hRa : (α ⟨a, b, 0⟩).a = l * (a * a) := by
    have := hform ⟨a, b, 0⟩
    simpa using congrArg UT3.a this
  have hRb : (α ⟨a', b', 0⟩).b = m * (b' * b') := by
    have := hform ⟨a', b', 0⟩
    simpa using congrArg UT3.b this
  have hmul := congrArg UT3.c (map_mul α (⟨a, b, 0⟩ : U4) (⟨a', b', 0⟩ : U4))
  rw [hxy, hL, hR, hRa, hRb] at hmul
  have hcross : l * m * ((a * b') * (a * b')) = (l * (a * a)) * (m * (b' * b')) := by
    ring
  rw [hcross] at hmul
  have hcomm : (α ⟨a, b, 0⟩).c + (α ⟨a', b', 0⟩).c +
        (l * (a * a)) * (m * (b' * b')) =
      (l * (a * a)) * (m * (b' * b')) +
        ((α ⟨a, b, 0⟩).c + (α ⟨a', b', 0⟩).c) := by
    ring
  rw [hcomm] at hmul
  exact add_left_cancel hmul

private lemma torusAut_apply (u v : F4c) (hu : u ≠ 0) (hv : v ≠ 0) (x : U4) :
    torusAut u v hu hv x = ⟨u * x.a, v * x.b, u * v * x.c⟩ := rfl

private lemma torusAut_inv_apply (u v : F4c) (hu : u ≠ 0) (hv : v ≠ 0) (x : U4) :
    (torusAut u v hu hv)⁻¹ x =
      ⟨u⁻¹ * x.a, v⁻¹ * x.b, u⁻¹ * v⁻¹ * x.c⟩ := rfl

private lemma f4_sq_mul_sq_mul (x y : F4c) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * x * (y * y)) * (x * y) = 1 := by
  revert x y
  decide +kernel

private lemma f4_sq_mul_sq_inv (x y : F4c) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * x * (y * y))⁻¹ = x * y :=
  inv_eq_of_mul_eq_one_right (f4_sq_mul_sq_mul x y hx hy)

private lemma torus_a_coord : ∀ l a : F4c, l ≠ 0 →
    (l * l)⁻¹ * (l * ((l * l * a) * (l * l * a))) = a * a := by
  decide +kernel

private lemma torus_b_coord : ∀ m b : F4c, m ≠ 0 →
    (m * m)⁻¹ * (m * ((m * m * b) * (m * m * b))) = b * b := by
  decide +kernel

private lemma torus_c_coord : ∀ l m c : F4c, l ≠ 0 → m ≠ 0 →
    (l * l)⁻¹ * (m * m)⁻¹ *
        (l * m * (((l * l) * (m * m) * c) * ((l * l) * (m * m) * c))) = c * c := by
  decide +kernel

private lemma torus_conj_action (α : MulAut U4) (l m : F4c) (hl : l ≠ 0) (hm : m ≠ 0)
    (G : F4c → F4c → F4c)
    (hform : ∀ x : U4, α x = ⟨l * (x.a * x.a), m * (x.b * x.b),
      l * m * (x.c * x.c) + G x.a x.b⟩) (x : U4) :
    ((torusAut (l * l) (m * m) (mul_ne_zero hl hl) (mul_ne_zero hm hm))⁻¹ * α *
        torusAut (l * l) (m * m) (mul_ne_zero hl hl) (mul_ne_zero hm hm)) x =
      ⟨x.a * x.a, x.b * x.b, x.c * x.c + l * m * G (l * l * x.a) (m * m * x.b)⟩ := by
  rw [MulAut.mul_apply, MulAut.mul_apply, torusAut_apply, hform, torusAut_inv_apply]
  refine UT3.ext ?_ ?_ ?_
  · rw [torus_a_coord l x.a hl]
  · rw [torus_b_coord m x.b hm]
  · rw [mul_add, torus_c_coord l m x.c hl hm]
    have hcoef : (l * l)⁻¹ * (m * m)⁻¹ = l * m := by
      have h1 : (l * l * (m * m))⁻¹ = l * m := f4_sq_mul_sq_inv l m hl hm
      rw [← h1, mul_inv_rev]
      ring
    rw [hcoef]

private lemma f4_decomp (a : F4c) :
    (if a.a = 0 then 0 else (1 : F4c)) + (if a.b = 0 then 0 else omg) = a := by
  revert a
  decide +kernel

private lemma additive_sq_form_aux :
    ∀ u a : F4c,
      (if a.a = 0 then 0 else u + u * u) + (if a.b = 0 then 0 else u) =
        (⟨u.a + u.b, 0⟩ : F4c) * a + (⟨u.a, 0⟩ : F4c) * (a * a) := by
  decide +kernel

private lemma additive_sq_form (f : F4c → F4c) (h0 : f 0 = 0)
    (hadd : ∀ a b : F4c, f (a + b) = f a + f b)
    (hsq : ∀ a : F4c, f (a * a) = f a * f a) (a : F4c) :
    f a = (⟨(f omg).a + (f omg).b, 0⟩ : F4c) * a +
      (⟨(f omg).a, 0⟩ : F4c) * (a * a) := by
  have homg : omg * omg = omg + 1 := by decide +kernel
  have h1 : f 1 = f omg + f omg * f omg := by
    have h := hsq omg
    rw [homg, hadd] at h
    have h' : f omg + (f omg + f 1) = f omg + f omg * f omg := by rw [h]
    rwa [← add_assoc, L26.two_add_F4c, zero_add] at h'
  have hpt := f4_decomp a
  calc f a = f ((if a.a = 0 then 0 else (1 : F4c)) +
        (if a.b = 0 then 0 else omg)) := by rw [hpt]
    _ = f (if a.a = 0 then 0 else (1 : F4c)) +
        f (if a.b = 0 then 0 else omg) := hadd _ _
    _ = (if a.a = 0 then 0 else f 1) + (if a.b = 0 then 0 else f omg) := by
        by_cases ha : a.a = 0 <;> by_cases hb : a.b = 0 <;> simp [ha, hb, h0]
    _ = (if a.a = 0 then 0 else f omg + f omg * f omg) +
        (if a.b = 0 then 0 else f omg) := by rw [h1]
    _ = (⟨(f omg).a + (f omg).b, 0⟩ : F4c) * a +
        (⟨(f omg).a, 0⟩ : F4c) * (a * a) := additive_sq_form_aux (f omg) a

private lemma f4_mul_self_eq_one : ∀ x : F4c, x * x = 1 → x = 1 := by
  decide +kernel

private lemma linear_case_impossible (α : MulAut U4) (hα : α * α = 1)
    (hZ : ∃ z ∈ center U4, α z ≠ z) (l m : F4c)
    (hlinAdd : ∀ v : V4, linAdd α v = (l * v.1, m * v.2)) : False := by
  have hσ : ∀ c : F4c, sigAdd α c = l * m * c := by
    intro c
    have hv := sqF_linAdd α (c, 1)
    rw [hlinAdd] at hv
    simpa [sqF, mul_assoc, mul_comm, mul_left_comm] using hv.symm
  have hlm2 : l * m * (l * m) = 1 := by
    have hz : α (α (⟨0, 0, 1⟩ : U4)) = ⟨0, 0, 1⟩ := by
      rw [← MulAut.mul_apply, hα, MulAut.one_apply]
    rw [aut_center_eq, aut_center_eq, hσ, hσ] at hz
    simpa [mul_assoc] using congrArg UT3.c hz
  have hlm : l * m = 1 := f4_mul_self_eq_one (l * m) hlm2
  obtain ⟨z, hz, hzne⟩ := hZ
  obtain ⟨ha, hb⟩ := (mem_center_U4 z).1 hz
  have hz' : z = ⟨0, 0, z.c⟩ := UT3.ext ha hb rfl
  exact hzne (by rw [hz', aut_center_eq, hσ, hlm, one_mul])

private lemma f4_bit_cases (a : ZMod 2) : (⟨a, 0⟩ : F4c) = 0 ∨ (⟨a, 0⟩ : F4c) = 1 := by
  revert a
  decide +kernel

private lemma f4_bit_pair_cases (a b : ZMod 2) :
    (⟨a + b, 0⟩ : F4c) = 0 ∨ (⟨a + b, 0⟩ : F4c) = 1 := by
  revert a b
  decide +kernel

private lemma add_sq_F4c : ∀ x y : F4c, (x + y) * (x + y) = x * x + y * y := by
  decide +kernel

private def cAut (p q : F4c) : MulAut U4 where
  toFun x := ⟨x.a, x.b, x.c + p * (x.a * x.a) + q * (x.b * x.b)⟩
  invFun x := ⟨x.a, x.b, x.c + p * (x.a * x.a) + q * (x.b * x.b)⟩
  left_inv x := by
    refine UT3.ext rfl rfl ?_
    have hA : p * (x.a * x.a) + p * (x.a * x.a) = 0 := L26.two_add_F4c _
    have hB : q * (x.b * x.b) + q * (x.b * x.b) = 0 := L26.two_add_F4c _
    calc x.c + p * (x.a * x.a) + q * (x.b * x.b) + p * (x.a * x.a) +
          q * (x.b * x.b)
        = x.c + (p * (x.a * x.a) + p * (x.a * x.a)) +
            (q * (x.b * x.b) + q * (x.b * x.b)) := by abel
      _ = x.c := by rw [hA, hB]; simp
  right_inv x := by
    refine UT3.ext rfl rfl ?_
    have hA : p * (x.a * x.a) + p * (x.a * x.a) = 0 := L26.two_add_F4c _
    have hB : q * (x.b * x.b) + q * (x.b * x.b) = 0 := L26.two_add_F4c _
    calc x.c + p * (x.a * x.a) + q * (x.b * x.b) + p * (x.a * x.a) +
          q * (x.b * x.b)
        = x.c + (p * (x.a * x.a) + p * (x.a * x.a)) +
            (q * (x.b * x.b) + q * (x.b * x.b)) := by abel
      _ = x.c := by rw [hA, hB]; simp
  map_mul' x y := by
    refine UT3.ext rfl rfl ?_
    simp only [UT3.mul_def]
    rw [add_sq_F4c, add_sq_F4c]
    ring

private def Hw (r1 s1 r2 s2 : F4c) (a b : F4c) : F4c :=
  r1 * a + s1 * (a * a) + r2 * b + s2 * (b * b)

private def hautW (r1 s1 r2 s2 : F4c) (x : U4) : U4 :=
  ⟨x.a * x.a, x.b * x.b, x.c * x.c + Hw r1 s1 r2 s2 x.a x.b⟩

private def zWit (r1 s1 r2 s2 : F4c) : F4c :=
  if r1 * s2 + r2 * s1 + s1 * s2 = 0 then 0 else omg

private def tWit (r1 s1 r2 s2 : F4c) : U4 :=
  ⟨s2, s1, zWit r1 s1 r2 s2⟩

private lemma twist_witness_check :
    ∀ r1 s1 r2 s2 : F4c,
      (r1 = 0 ∨ r1 = 1) → (s1 = 0 ∨ s1 = 1) →
      (r2 = 0 ∨ r2 = 1) → (s2 = 0 ∨ s2 = 1) →
      let t := tWit r1 s1 r2 s2
      let β : MulAut U4 := cAut (r1 * omg) (r2 * omg)
      t * hautW r1 s1 r2 s2 t = 1 ∧
        ∀ x : U4, t * hautW r1 s1 r2 s2 (β x) * t⁻¹ = β (frobAut x) := by
  decide +kernel

private lemma H_sq_of_form (α₁ : MulAut U4) (H : F4c → F4c → F4c)
    (hform : ∀ x : U4, α₁ x = ⟨x.a * x.a, x.b * x.b, x.c * x.c + H x.a x.b⟩)
    (hα₁ : α₁ * α₁ = 1) (a b : F4c) :
    H (a * a) (b * b) = H a b * H a b := by
  have hx : α₁ (⟨a, b, 0⟩ : U4) = ⟨a * a, b * b, H a b⟩ := by
    rw [hform]
    refine UT3.ext ?_ ?_ ?_
    · simp
    · simp
    · simp
  have h2 : α₁ (α₁ (⟨a, b, 0⟩ : U4)) = ⟨a, b, 0⟩ := by
    rw [← MulAut.mul_apply, hα₁, MulAut.one_apply]
  have hy : α₁ (α₁ (⟨a, b, 0⟩ : U4)) =
      ⟨(a * a) * (a * a), (b * b) * (b * b),
        (H a b) * (H a b) + H (a * a) (b * b)⟩ := by
    rw [hx, hform]
  rw [hy] at h2
  have hc : (H a b) * (H a b) + H (a * a) (b * b) = 0 := congrArg UT3.c h2
  calc H (a * a) (b * b) = H (a * a) (b * b) + 0 := (add_zero _).symm
    _ = H (a * a) (b * b) + ((H a b) * (H a b) + H (a * a) (b * b)) := by rw [hc]
    _ = (H (a * a) (b * b) + H (a * a) (b * b)) + (H a b) * (H a b) := by abel
    _ = 0 + (H a b) * (H a b) := by rw [L26.two_add_F4c]
    _ = H a b * H a b := zero_add _

theorem nonempty_mulEquiv_sylAhat8_of_aut (α : MulAut U4) (hα : α * α = 1)
    (hA : ∀ x : U4, x.b = 0 → (α x).b = 0) (hZ : ∃ z ∈ center U4, α z ≠ z) :
    Nonempty (U4 ⋊[invAct α hα] Multiplicative (ZMod 2) ≃* SylAhat8) := by
  obtain ⟨l, m, hl, hm, hlinAdd | hlinAdd⟩ := linAdd_diag_classify α hA
  · exact (linear_case_impossible α hα hZ l m hlinAdd).elim
  · have hσ : ∀ c : F4c, sigAdd α c = l * m * (c * c) := by
      intro c
      have hv := sqF_linAdd α (c, 1)
      rw [hlinAdd] at hv
      simpa [sqF, mul_assoc, mul_comm, mul_left_comm] using hv.symm
    let G : F4c → F4c → F4c := fun a b => (α ⟨a, b, 0⟩).c
    have hform : ∀ x : U4, α x = ⟨l * (x.a * x.a), m * (x.b * x.b),
        l * m * (x.c * x.c) + G x.a x.b⟩ := by
      intro x
      simpa [G] using alpha_form_of_frob α l m hlinAdd hσ x
    have hGadd : ∀ a b a' b' : F4c,
        G (a + a') (b + b') = G a b + G a' b' := by
      intro a b a' b'
      simpa [G] using G_add_of_frob α l m hform a b a' b'
    let H : F4c → F4c → F4c := fun a b => l * m * G (l * l * a) (m * m * b)
    have hHadd : ∀ a b a' b' : F4c,
        H (a + a') (b + b') = H a b + H a' b' := by
      intro a b a' b'
      change l * m * G (l * l * (a + a')) (m * m * (b + b')) =
        l * m * G (l * l * a) (m * m * b) + l * m * G (l * l * a') (m * m * b')
      rw [show l * l * (a + a') = l * l * a + l * l * a' by ring,
        show m * m * (b + b') = m * m * b + m * m * b' by ring, hGadd]
      ring
    let T : MulAut U4 := torusAut (l * l) (m * m) (mul_ne_zero hl hl) (mul_ne_zero hm hm)
    let α₁ : MulAut U4 := T⁻¹ * α * T
    have hα₁ : α₁ * α₁ = 1 := by
      change (T⁻¹ * α * T) * (T⁻¹ * α * T) = 1
      have hgroup : (T⁻¹ * α * T) * (T⁻¹ * α * T) = T⁻¹ * (α * α) * T := by
        group
      rw [hgroup, hα]
      group
    have hα₁form : ∀ x : U4,
        α₁ x = ⟨x.a * x.a, x.b * x.b, x.c * x.c + H x.a x.b⟩ := by
      intro x
      simpa [α₁, T, H] using torus_conj_action α l m hl hm G hform x
    have hHsq : ∀ a b : F4c, H (a * a) (b * b) = H a b * H a b :=
      fun a b => H_sq_of_form α₁ H hα₁form hα₁ a b
    have hG00 : G 0 0 = 0 := by
      change (α ⟨0, 0, 0⟩).c = 0
      rw [show (⟨0, 0, 0⟩ : U4) = 1 from UT3.one_def.symm, map_one]
      rfl
    have hH0 : H 0 0 = 0 := by
      simp [H, hG00]
    let f : F4c → F4c := fun a => H a 0
    let g : F4c → F4c := fun b => H 0 b
    have hf0 : f 0 = 0 := by simpa [f] using hH0
    have hfadd : ∀ a a' : F4c, f (a + a') = f a + f a' := by
      intro a a'
      have h := hHadd a 0 a' 0
      simpa [f] using h
    have hfsq : ∀ a : F4c, f (a * a) = f a * f a := by
      intro a
      have h := hHsq a 0
      simpa [f] using h
    let r1 : F4c := ⟨(f omg).a + (f omg).b, 0⟩
    let s1 : F4c := ⟨(f omg).a, 0⟩
    let r2 : F4c := ⟨(g omg).a + (g omg).b, 0⟩
    let s2 : F4c := ⟨(g omg).a, 0⟩
    have hf : ∀ a : F4c, f a = r1 * a + s1 * (a * a) := by
      intro a
      have h := additive_sq_form f hf0 hfadd hfsq a
      simpa [r1, s1] using h
    have hg : ∀ b : F4c, g b = r2 * b + s2 * (b * b) := by
      intro b
      have h := additive_sq_form g (by simpa [g] using hH0)
        (by
          intro b b'
          have h := hHadd 0 b 0 b'
          simpa [g] using h)
        (by
          intro b
          have h := hHsq 0 b
          simpa [g] using h) b
      simpa [r2, s2] using h
    have hHform : ∀ a b : F4c,
        H a b = r1 * a + s1 * (a * a) + r2 * b + s2 * (b * b) := by
      intro a b
      have hsplit : H a b = f a + g b := by
        have h := hHadd a 0 0 b
        simpa [f, g] using h
      rw [hsplit, hf a, hg b]
      ring
    have hr1 : r1 = 0 ∨ r1 = 1 := by
      simpa [r1] using f4_bit_pair_cases (f omg).a (f omg).b
    have hs1 : s1 = 0 ∨ s1 = 1 := by
      simpa [s1] using f4_bit_cases (f omg).a
    have hr2 : r2 = 0 ∨ r2 = 1 := by
      simpa [r2] using f4_bit_pair_cases (g omg).a (g omg).b
    have hs2 : s2 = 0 ∨ s2 = 1 := by
      simpa [s2] using f4_bit_cases (g omg).a
    let t₁ : U4 := tWit r1 s1 r2 s2
    let β₁ : MulAut U4 := cAut (r1 * omg) (r2 * omg)
    have hfin := twist_witness_check r1 s1 r2 s2 hr1 hs1 hr2 hs2
    have hfin1 : t₁ * hautW r1 s1 r2 s2 t₁ = 1 := by
      simpa [t₁, β₁] using hfin.1
    have hfin2 : ∀ x : U4,
        t₁ * hautW r1 s1 r2 s2 (β₁ x) * t₁⁻¹ = β₁ (frobAut x) := by
      intro x
      simpa [t₁, β₁] using hfin.2 x
    have hhaut : ∀ x : U4, hautW r1 s1 r2 s2 x = α₁ x := by
      intro x
      rw [hα₁form x]
      simp [hautW, Hw, hHform x.a x.b]
    let tT : U4 := T t₁
    let β : MulAut U4 := T * β₁
    have ht : tT * α tT = 1 := by
      have hαT : α = T * α₁ * T⁻¹ := by
        change α = T * (T⁻¹ * α * T) * T⁻¹
        group
      rw [hαT]
      change T t₁ * (T * α₁ * T⁻¹) (T t₁) = 1
      rw [MulAut.mul_apply, MulAut.mul_apply]
      have hTin : T⁻¹ (T t₁) = t₁ := by
        change T.symm (T t₁) = t₁
        exact T.symm_apply_apply t₁
      rw [hTin, ← map_mul]
      have h1 : t₁ * α₁ t₁ = 1 := by
        simpa [hhaut t₁] using hfin1
      rw [h1, map_one]
    have hconj₁ : MulAut.conj t₁ * α₁ = β₁ * frobAut * β₁⁻¹ := by
      apply MulEquiv.ext
      intro x
      simp only [MulAut.mul_apply, MulAut.conj_apply]
      rw [← hhaut x]
      have h := hfin2 (β₁⁻¹ x)
      have hβinv : β₁ (β₁⁻¹ x) = x := β₁.apply_symm_apply x
      rw [hβinv] at h
      simpa using h
    have htconj : MulAut.conj tT = T * MulAut.conj t₁ * T⁻¹ := by
      apply MulEquiv.ext
      intro x
      simp [tT, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    have hconj : MulAut.conj tT * α = β * frobAut * β⁻¹ := by
      have hαT : α = T * α₁ * T⁻¹ := by
        change α = T * (T⁻¹ * α * T) * T⁻¹
        group
      calc MulAut.conj tT * α
          = (T * MulAut.conj t₁ * T⁻¹) * (T * α₁ * T⁻¹) := by rw [htconj, hαT]
        _ = T * (MulAut.conj t₁ * α₁) * T⁻¹ := by group
        _ = T * (β₁ * frobAut * β₁⁻¹) * T⁻¹ := by rw [hconj₁]
        _ = β * frobAut * β⁻¹ := by simp [β, mul_assoc]
    exact nonempty_mulEquiv_invAct_of_twist hα frobAut_mul_self β tT ht hconj

end CFSG.GH74.PartII

