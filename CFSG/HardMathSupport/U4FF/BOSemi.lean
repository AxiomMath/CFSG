module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDescent
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix CFSG.LocalAnalysis.RankThreeUC CFSG.Open

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem bo_add_apply (a a' : AddAut (ι → F)) (x : ι → F) : (a + a') x = a (a' x) :=
  rfl

theorem bo_zero_apply (x : ι → F) : (0 : AddAut (ι → F)) x = x :=
  rfl

theorem bo_neg_apply (a : AddAut (ι → F)) (x : ι → F) : (-a) x = a.symm x :=
  rfl

@[expose] def boIsLin (a : AddAut (ι → F)) : Prop :=
  ∀ (c : F) (x : ι → F), a (c • x) = c • a x

theorem bo_isLin_zero : boIsLin (0 : AddAut (ι → F)) :=
  fun _ _ => rfl

theorem bo_isLin_add {a a' : AddAut (ι → F)} (ha : boIsLin a) (ha' : boIsLin a') :
    boIsLin (a + a') := by
  intro c x
  rw [bo_add_apply, bo_add_apply, ha' c x, ha c]

theorem bo_isLin_neg {a : AddAut (ι → F)} (ha : boIsLin a) : boIsLin (-a) := by
  intro c x
  rw [bo_neg_apply, bo_neg_apply]
  have key : a (c • a.symm x) = c • x := by
    rw [ha c, AddEquiv.apply_symm_apply]
  calc a.symm (c • x) = a.symm (a (c • a.symm x)) := by rw [key]
    _ = c • a.symm x := AddEquiv.symm_apply_apply a _

theorem bo_invol_apply {a : AddAut (ι → F)} (h : a + a = 0) (x : ι → F) : a (a x) = x := by
  have := congrArg (fun e : AddAut (ι → F) => e x) h
  simpa only [bo_add_apply, bo_zero_apply] using this

theorem bo_symm_apply {a : AddAut (ι → F)} (h : a + a = 0) (x : ι → F) : a.symm x = a x := by
  rw [AddEquiv.symm_apply_eq, bo_invol_apply h]

theorem bo_ringHom_invol [Nonempty ι] {a : AddAut (ι → F)} (h : a + a = 0) {θ : F →+* F}
    (hθ : ∀ (c : F) (x : ι → F), a (c • x) = θ c • a x) (c : F) : θ (θ c) = c := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 : ∀ x : ι → F, c • x = θ (θ c) • x := fun x => by
    calc c • x = a (a (c • x)) := (bo_invol_apply h _).symm
      _ = a (θ c • a x) := by rw [hθ c x]
      _ = θ (θ c) • a (a x) := hθ (θ c) (a x)
      _ = θ (θ c) • x := by rw [bo_invol_apply h x]
  have h2 := congrFun (h1 (Pi.single i 1)) i
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
  exact h2.symm

theorem bo_exists_ne {a : AddAut (ι → F)} {θ : F →+* F}
    (hθ : ∀ (c : F) (x : ι → F), a (c • x) = θ c • a x) (hna : ¬ boIsLin a) :
    ∃ c, θ c ≠ c := by
  by_contra h
  have h' : ∀ c, θ c = c := fun c => by_contra fun hc => h ⟨c, hc⟩
  exact hna fun c x => by rw [hθ c x, h' c]

theorem bo_isLin_add_of_semilinear [Finite F] {a a' : AddAut (ι → F)} {θ θ' : F →+* F}
    (hθ : ∀ (c : F) (x : ι → F), a (c • x) = θ c • a x)
    (hθ' : ∀ (c : F) (x : ι → F), a' (c • x) = θ' c • a' x)
    (hθi : ∀ c, θ (θ c) = c) (hθ'i : ∀ c, θ' (θ' c) = c)
    (hne : ∃ c, θ c ≠ c) (hne' : ∃ c, θ' c ≠ c) :
    boIsLin (a + a') := by
  let e₁ : F ≃+* F := RingEquiv.ofRingHom θ θ (RingHom.ext hθi) (RingHom.ext hθi)
  let e₂ : F ≃+* F := RingEquiv.ofRingHom θ' θ' (RingHom.ext hθ'i) (RingHom.ext hθ'i)
  have hE : e₁ = e₂ := ringAut_involution_unique e₁ e₂ hθi hθ'i hne hne'
  have heq : ∀ c, θ c = θ' c := fun c => congrArg (fun e : F ≃+* F => e c) hE
  intro c x
  rw [bo_add_apply, bo_add_apply, hθ' c x, hθ (θ' c) (a' x), ← heq c, hθi c]

@[expose] def boLinSub (B : AddSubgroup (AddAut (ι → F))) : AddSubgroup (AddAut (ι → F)) where
  carrier := {a | a ∈ B ∧ boIsLin a}
  add_mem' := fun ha ha' => ⟨B.add_mem ha.1 ha'.1, bo_isLin_add ha.2 ha'.2⟩
  zero_mem' := ⟨B.zero_mem, bo_isLin_zero⟩
  neg_mem' := fun ha => ⟨B.neg_mem ha.1, bo_isLin_neg ha.2⟩

theorem mem_boLinSub {B : AddSubgroup (AddAut (ι → F))} {a : AddAut (ι → F)} :
    a ∈ boLinSub B ↔ a ∈ B ∧ boIsLin a :=
  Iff.rfl

theorem bo_card_le_two [Finite F] [Nonempty ι] (B : AddSubgroup (AddAut (ι → F)))
    (h2 : ∀ a ∈ B, a + a = 0)
    (hsemi : ∀ a ∈ B, ∃ θ : F →+* F, ∀ (c : F) (x : ι → F), a (c • x) = θ c • a x)
    {s : AddAut (ι → F)} (hsB : s ∈ B) (hsnl : ¬ boIsLin s) :
    Nat.card B ≤ 2 * Nat.card (boLinSub B) := by
  classical
  obtain ⟨θs, hθs⟩ := hsemi s hsB
  have hmul : ∀ a ∈ B, ¬ boIsLin a → s + a ∈ boLinSub B := fun a ha hna => by
    obtain ⟨θ, hθ⟩ := hsemi a ha
    exact ⟨B.add_mem hsB ha, bo_isLin_add_of_semilinear hθs hθ
      (bo_ringHom_invol (h2 s hsB) hθs) (bo_ringHom_invol (h2 a ha) hθ)
      (bo_exists_ne hθs hsnl) (bo_exists_ne hθ hna)⟩
  let f : B → Bool × ↥(boLinSub B) := fun a =>
    if h : boIsLin (a : AddAut (ι → F)) then (false, ⟨a.1, a.2, h⟩)
    else (true, ⟨s + a.1, hmul a.1 a.2 h⟩)
  have hf : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [f] at hab
    by_cases hal : boIsLin a <;> by_cases hbl : boIsLin b
    · rw [dif_pos hal, dif_pos hbl] at hab
      exact Subtype.ext (congrArg (fun p : Bool × ↥(boLinSub B) => p.2.1) hab)
    · rw [dif_pos hal, dif_neg hbl] at hab
      cases hab
    · rw [dif_neg hal, dif_pos hbl] at hab
      cases hab
    · rw [dif_neg hal, dif_neg hbl] at hab
      have h3 : s + a = s + b := congrArg (fun p : Bool × ↥(boLinSub B) => p.2.1) hab
      exact Subtype.ext (add_left_cancel h3)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  exact h1

@[expose] def boLinFix (B : AddSubgroup (AddAut (ι → F))) : Submodule F (ι → F) where
  carrier := {x | ∀ a ∈ boLinSub B, a x = x}
  add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
  zero_mem' := fun a _ => map_zero a
  smul_mem' := fun c {x} hx a ha => by rw [(mem_boLinSub.mp ha).2 c x, hx a ha]

theorem mem_boLinFix {B : AddSubgroup (AddAut (ι → F))} {x : ι → F} :
    x ∈ boLinFix B ↔ ∀ a ∈ boLinSub B, a x = x :=
  Iff.rfl

theorem bo_nonlin_fix_sq [Finite F] [CharP F 2] [Nonempty ι] (B : AddSubgroup (AddAut (ι → F)))
    (h2 : ∀ a ∈ B, a + a = 0) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a + b = b + a)
    (hsemi : ∀ a ∈ B, ∃ θ : F →+* F, ∀ (c : F) (x : ι → F), a (c • x) = θ c • a x)
    {s : AddAut (ι → F)} (hsB : s ∈ B) (hsnl : ¬ boIsLin s) :
    Nat.card {x : ι → F // ∀ a ∈ B, a x = x} ^ 2 ≤ Nat.card (boLinFix B) := by
  obtain ⟨θ, hθ⟩ := hsemi s hsB
  have hθi : ∀ c, θ (θ c) = c := bo_ringHom_invol (h2 s hsB) hθ
  have hne : ∃ c, θ c ≠ c := bo_exists_ne hθ hsnl
  have hmem : ∀ x ∈ boLinFix B, s x ∈ boLinFix B := fun x hx a ha => by
    have h1 := congrArg (fun e : AddAut (ι → F) => e x) (hcomm a (mem_boLinSub.mp ha).1 s hsB)
    simp only [bo_add_apply] at h1
    rw [hx a ha] at h1
    exact h1
  let s' : ↥(boLinFix B) ≃+ ↥(boLinFix B) :=
    { toFun := fun x => ⟨s x.1, hmem x.1 x.2⟩
      invFun := fun x => ⟨s x.1, hmem x.1 x.2⟩
      left_inv := fun x => Subtype.ext (bo_invol_apply (h2 s hsB) x.1)
      right_inv := fun x => Subtype.ext (bo_invol_apply (h2 s hsB) x.1)
      map_add' := fun x y => Subtype.ext (map_add s x.1 y.1) }
  have hs' : ∀ (c : F) (x : ↥(boLinFix B)), s' (c • x) = θ c • s' x :=
    fun c x => Subtype.ext (hθ c x.1)
  have hss : ∀ x : ↥(boLinFix B), s' (s' x) = x :=
    fun x => Subtype.ext (bo_invol_apply (h2 s hsB) x.1)
  have hsq := card_fix_sq_of_semilinear_involution (K := F) (C := ↥(boLinFix B)) θ hθi hne
    s' hs' hss
  have hinj : Nat.card {x : ι → F // ∀ a ∈ B, a x = x} ≤
      Nat.card {y : ↥(boLinFix B) // s' y = y} := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨⟨x.1, fun a ha => x.2 a (mem_boLinSub.mp ha).1⟩, Subtype.ext (x.2 s hsB)⟩ :
        {y : ↥(boLinFix B) // s' y = y})) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1.1) hxy)
  calc Nat.card {x : ι → F // ∀ a ∈ B, a x = x} ^ 2
      ≤ Nat.card {y : ↥(boLinFix B) // s' y = y} ^ 2 := Nat.pow_le_pow_left hinj 2
    _ = Nat.card (boLinFix B) := hsq

theorem bo_exists_matrix {a : AddAut (ι → F)} (ha : boIsLin a) :
    ∃ A : Matrix ι ι F, ∀ x, A *ᵥ x = a x := by
  let L : (ι → F) →ₗ[F] (ι → F) :=
    { toFun := a, map_add' := fun x y => map_add a x y, map_smul' := fun c x => ha c x }
  exact ⟨LinearMap.toMatrix' L, fun x => LinearMap.toMatrix'_mulVec L x⟩

theorem bo_matrix_eq_of_mulVec {M N : Matrix ι ι F} (h : ∀ x : ι → F, M *ᵥ x = N *ᵥ x) : M = N :=
  (LinearEquiv.injective Matrix.toLin') (LinearMap.ext h)

end Generic

abbrev OIdx : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2

section Omega

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem bo_exists_semilinear_omega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {a : AddAut (OIdx → F)} (h : a + a = 0)
    (hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c), ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∀ x : OIdx → F, a (((g : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ x) =
        ((g' : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ (a x)) :
    ∃ θ : F →+* F, ∀ (c : F) (x : OIdx → F), a (c • x) = θ c • a x := by
  refine omega_semilinear hirr a (fun g hg => ?_)
  obtain ⟨g', hg', hx⟩ := hN g hg
  exact ⟨g', hg', fun x => by simpa only [bo_symm_apply h] using hx x⟩

theorem bo_isometry_of_isLin (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {a : AddAut (OIdx → F)} (h : a + a = 0) (hlin : boIsLin a)
    (hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c), ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∀ x : OIdx → F, a (((g : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ x) =
        ((g' : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ (a x)) :
    ∀ x : OIdx → F, StatedQuadMinus 3 F b c (a x) = StatedQuadMinus 3 F b c x := by
  obtain ⟨A, hA⟩ := bo_exists_matrix hlin
  have hAA : A * A = 1 := bo_matrix_eq_of_mulVec fun x => by
    rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hA, hA, bo_invol_apply h]
  have key := omega_isometry_of_normalizes hirr A hAA (fun g hg => by
    obtain ⟨g', hg', hx⟩ := hN g hg
    exact ⟨g', hg', fun x => by simpa only [hA] using hx x⟩)
  intro x
  rw [← hA]
  exact key x

end Omega

end CFSG.HardMathSupport.U4FF
