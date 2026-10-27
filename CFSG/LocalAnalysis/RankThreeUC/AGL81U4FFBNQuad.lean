module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Norm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFQuad

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.ClassicalGroups.Unitary CFSG.Open
open CFSG.LieType.Universal.Unitary (SUid conjTr)

theorem bnq_add_apply {F : Type} [Field F] (a a' : AddAut (Fin 4 → F)) (x : Fin 4 → F) :
    (a + a') x = a (a' x) :=
  rfl

theorem bnq_zero_apply {F : Type} [Field F] (x : Fin 4 → F) :
    (0 : AddAut (Fin 4 → F)) x = x :=
  rfl

theorem bnq_neg_apply {F : Type} [Field F] (a : AddAut (Fin 4 → F)) (x : Fin 4 → F) :
    (-a) x = a.symm x :=
  rfl

section Semilinear

variable {F : Type} [Field F]

@[expose] def bnqIsLin (a : AddAut (Fin 4 → F)) : Prop :=
  ∀ (c : F) (x : Fin 4 → F), a (c • x) = c • a x

theorem bnq_isLin_zero : bnqIsLin (0 : AddAut (Fin 4 → F)) :=
  fun _ _ => rfl

theorem bnq_isLin_add {a a' : AddAut (Fin 4 → F)} (ha : bnqIsLin a)
    (ha' : bnqIsLin a') : bnqIsLin (a + a') := by
  intro c x
  rw [bnq_add_apply, bnq_add_apply, ha' c x, ha c]

theorem bnq_isLin_neg {a : AddAut (Fin 4 → F)} (ha : bnqIsLin a) :
    bnqIsLin (-a) := by
  intro c x
  rw [bnq_neg_apply, bnq_neg_apply]
  have key : a (c • a.symm x) = c • x := by
    rw [ha c, AddEquiv.apply_symm_apply]
  calc a.symm (c • x) = a.symm (a (c • a.symm x)) := by rw [key]
    _ = c • a.symm x := AddEquiv.symm_apply_apply a _

theorem bnq_invol_apply {a : AddAut (Fin 4 → F)} (h : a + a = 0) (x : Fin 4 → F) :
    a (a x) = x := by
  have := congrArg (fun e : AddAut (Fin 4 → F) => e x) h
  simpa only [bnq_add_apply, bnq_zero_apply] using this

theorem bnq_symm_apply {a : AddAut (Fin 4 → F)} (h : a + a = 0) (x : Fin 4 → F) :
    a.symm x = a x := by
  rw [AddEquiv.symm_apply_eq, bnq_invol_apply h]

theorem bnq_exists_semilinear {n : ℕ} [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    {a : AddAut (Fin 4 → F)} (h : a + a = 0)
    (hN : ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x : Fin 4 → F,
      a (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (a x)) :
    ∃ θ : F →+* F, ∀ (c : F) (x : Fin 4 → F), a (c • x) = θ c • a x := by
  refine exists_semilinear_statedSU hF a fun g hg => ?_
  obtain ⟨g', hg', hx⟩ := hN g hg
  exact ⟨g', hg', fun x => by simpa only [bnq_symm_apply h] using hx x⟩

theorem bnq_ringHom_invol {a : AddAut (Fin 4 → F)} (h : a + a = 0) {θ : F →+* F}
    (hθ : ∀ (c : F) (x : Fin 4 → F), a (c • x) = θ c • a x) (c : F) : θ (θ c) = c := by
  have h1 : ∀ x : Fin 4 → F, c • x = θ (θ c) • x := fun x => by
    calc c • x = a (a (c • x)) := (bnq_invol_apply h _).symm
      _ = a (θ c • a x) := by rw [hθ c x]
      _ = θ (θ c) • a (a x) := hθ (θ c) (a x)
      _ = θ (θ c) • x := by rw [bnq_invol_apply h x]
  have h2 := congrFun (h1 (Pi.single 0 1)) 0
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
  exact h2.symm

theorem bnq_exists_ne {a : AddAut (Fin 4 → F)} {θ : F →+* F}
    (hθ : ∀ (c : F) (x : Fin 4 → F), a (c • x) = θ c • a x) (hna : ¬ bnqIsLin a) :
    ∃ c, θ c ≠ c := by
  by_contra h
  have h' : ∀ c, θ c = c := fun c => by_contra fun hc => h ⟨c, hc⟩
  exact hna fun c x => by rw [hθ c x, h' c]

theorem bnq_isLin_add_of_semilinear [Finite F] {a a' : AddAut (Fin 4 → F)}
    {θ θ' : F →+* F}
    (hθ : ∀ (c : F) (x : Fin 4 → F), a (c • x) = θ c • a x)
    (hθ' : ∀ (c : F) (x : Fin 4 → F), a' (c • x) = θ' c • a' x)
    (hθi : ∀ c, θ (θ c) = c) (hθ'i : ∀ c, θ' (θ' c) = c)
    (hne : ∃ c, θ c ≠ c) (hne' : ∃ c, θ' c ≠ c) :
    bnqIsLin (a + a') := by
  let e₁ : F ≃+* F := RingEquiv.ofRingHom θ θ (RingHom.ext hθi) (RingHom.ext hθi)
  let e₂ : F ≃+* F := RingEquiv.ofRingHom θ' θ' (RingHom.ext hθ'i) (RingHom.ext hθ'i)
  have hE : e₁ = e₂ := ringAut_involution_unique e₁ e₂ hθi hθ'i hne hne'
  have heq : ∀ c, θ c = θ' c := fun c => congrArg (fun e : F ≃+* F => e c) hE
  intro c x
  rw [bnq_add_apply, bnq_add_apply, hθ' c x, hθ (θ' c) (a' x), ← heq c, hθi c]

@[expose] def bnqLinSub (B : AddSubgroup (AddAut (Fin 4 → F))) :
    AddSubgroup (AddAut (Fin 4 → F)) where
  carrier := {a | a ∈ B ∧ bnqIsLin a}
  add_mem' := fun ha ha' => ⟨B.add_mem ha.1 ha'.1, bnq_isLin_add ha.2 ha'.2⟩
  zero_mem' := ⟨B.zero_mem, bnq_isLin_zero⟩
  neg_mem' := fun ha => ⟨B.neg_mem ha.1, bnq_isLin_neg ha.2⟩

theorem mem_bnqLinSub {B : AddSubgroup (AddAut (Fin 4 → F))} {a : AddAut (Fin 4 → F)} :
    a ∈ bnqLinSub B ↔ a ∈ B ∧ bnqIsLin a :=
  Iff.rfl

@[expose] def bnqGlAct (g : GL (Fin 4) F) : AddAut (Fin 4 → F) where
  toFun x := (g : Matrix (Fin 4) (Fin 4) F) *ᵥ x
  invFun x := ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x
  left_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add _ x y

@[simp] theorem bnqGlAct_apply (g : GL (Fin 4) F) (y : Fin 4 → F) :
    bnqGlAct g y = (g : Matrix (Fin 4) (Fin 4) F) *ᵥ y :=
  rfl

theorem bnqGlAct_mul (g h : GL (Fin 4) F) : bnqGlAct (g * h) = bnqGlAct g + bnqGlAct h :=
  AddEquiv.ext fun x => by
    show ((g * h : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x =
      (g : Matrix (Fin 4) (Fin 4) F) *ᵥ ((h : Matrix (Fin 4) (Fin 4) F) *ᵥ x)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem bnqGlAct_one : bnqGlAct (1 : GL (Fin 4) F) = 0 :=
  AddEquiv.ext fun x => by
    show ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x
    rw [Units.val_one, Matrix.one_mulVec]

theorem bnqGlAct_inv (g : GL (Fin 4) F) : bnqGlAct g⁻¹ = -bnqGlAct g :=
  AddEquiv.ext fun _ => rfl

theorem bnq_matrix_eq_of_mulVec {M N : Matrix (Fin 4) (Fin 4) F}
    (h : ∀ x : Fin 4 → F, M *ᵥ x = N *ᵥ x) : M = N :=
  (LinearEquiv.injective Matrix.toLin') (LinearMap.ext h)

theorem bnqGlAct_injective : Function.Injective (bnqGlAct : GL (Fin 4) F → AddAut (Fin 4 → F)) := by
  intro g h hgh
  have hx : ∀ x : Fin 4 → F,
      (g : Matrix (Fin 4) (Fin 4) F) *ᵥ x = (h : Matrix (Fin 4) (Fin 4) F) *ᵥ x :=
    fun x => congrArg (fun e : AddAut (Fin 4 → F) => e x) hgh
  exact Units.ext (bnq_matrix_eq_of_mulVec hx)

theorem bnq_exists_matrix {a : AddAut (Fin 4 → F)} (ha : bnqIsLin a) :
    ∃ A : Matrix (Fin 4) (Fin 4) F, ∀ x, A *ᵥ x = a x := by
  let L : (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
    { toFun := a, map_add' := fun x y => map_add a x y, map_smul' := fun c x => ha c x }
  exact ⟨LinearMap.toMatrix' L, fun x => LinearMap.toMatrix'_mulVec L x⟩

theorem bnq_add_self_eq_one {A : Matrix (Fin 4) (Fin 4) F} {a : AddAut (Fin 4 → F)}
    (hA : ∀ x, A *ᵥ x = a x) (ha : a + a = 0) : A * A = 1 := by
  refine bnq_matrix_eq_of_mulVec fun x => ?_
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hA, hA, bnq_invol_apply ha]

theorem bnq_exists_statedSU {n : ℕ} [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (B : AddSubgroup (AddAut (Fin 4 → F))) (h2 : ∀ a ∈ B, a + a = 0)
    (hN : ∀ a ∈ B, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x,
      a (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (a x))
    {a : AddAut (Fin 4 → F)} (ha : a ∈ bnqLinSub B) :
    ∃ g ∈ StatedSU 4 (2 ^ n) F, bnqGlAct g = a := by
  obtain ⟨A, hA⟩ := bnq_exists_matrix (mem_bnqLinSub.mp ha).2
  have hAA : A * A = 1 := bnq_add_self_eq_one hA (h2 a (mem_bnqLinSub.mp ha).1)
  obtain ⟨g, hg, hgA⟩ := exists_mem_statedSU_of_normalizes hF A hAA fun g hg => by
    obtain ⟨g', hg', hx⟩ := hN a (mem_bnqLinSub.mp ha).1 g hg
    exact ⟨g', hg', fun x => by simpa only [hA] using hx x⟩
  refine ⟨g, hg, AddEquiv.ext fun x => ?_⟩
  show (g : Matrix (Fin 4) (Fin 4) F) *ᵥ x = a x
  rw [hgA, hA]

@[expose] def bnqLinMat (B : AddSubgroup (AddAut (Fin 4 → F))) : Subgroup (GL (Fin 4) F) where
  carrier := {g | bnqGlAct g ∈ bnqLinSub B}
  mul_mem' := fun {g h} hg hh => by
    show bnqGlAct (g * h) ∈ bnqLinSub B
    rw [bnqGlAct_mul]
    exact (bnqLinSub B).add_mem hg hh
  one_mem' := by
    show bnqGlAct 1 ∈ bnqLinSub B
    rw [bnqGlAct_one]
    exact (bnqLinSub B).zero_mem
  inv_mem' := fun {g} hg => by
    show bnqGlAct g⁻¹ ∈ bnqLinSub B
    rw [bnqGlAct_inv]
    exact (bnqLinSub B).neg_mem hg

theorem mem_bnqLinMat {B : AddSubgroup (AddAut (Fin 4 → F))} {g : GL (Fin 4) F} :
    g ∈ bnqLinMat B ↔ bnqGlAct g ∈ bnqLinSub B :=
  Iff.rfl

theorem bnq_card_linMat {n : ℕ} [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (B : AddSubgroup (AddAut (Fin 4 → F))) (h2 : ∀ a ∈ B, a + a = 0)
    (hN : ∀ a ∈ B, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x,
      a (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (a x)) :
    Nat.card (bnqLinMat B) = Nat.card (bnqLinSub B) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun g : bnqLinMat B => (⟨bnqGlAct g.1, g.2⟩ : bnqLinSub B)) ⟨?_, ?_⟩)
  · intro g h hgh
    exact Subtype.ext (bnqGlAct_injective (congrArg Subtype.val hgh))
  · intro a
    obtain ⟨g, -, hga⟩ := bnq_exists_statedSU hF B h2 hN a.2
    exact ⟨⟨g, mem_bnqLinMat.mpr (by rw [hga]; exact a.2)⟩, Subtype.ext hga⟩

@[expose] def bnqLinFix (B : AddSubgroup (AddAut (Fin 4 → F))) :
    Submodule F (Fin 4 → F) where
  carrier := {x | ∀ a ∈ bnqLinSub B, a x = x}
  add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
  zero_mem' := fun a _ => map_zero a
  smul_mem' := fun c {x} hx a ha => by rw [(mem_bnqLinSub.mp ha).2 c x, hx a ha]

theorem bnq_sub_one_mulVec (g : GL (Fin 4) F) (y : Fin 4 → F) :
    ((g : Matrix (Fin 4) (Fin 4) F) - 1) *ᵥ y = bnqGlAct g y - y := by
  rw [bnqGlAct_apply, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem bnq_quad_matrix {g g' : GL (Fin 4) F}
    (hq : ∀ x, bnqGlAct g (bnqGlAct g' x - x) = bnqGlAct g' x - x) :
    ((g : Matrix (Fin 4) (Fin 4) F) - 1) * ((g' : Matrix (Fin 4) (Fin 4) F) - 1) = 0 := by
  refine bnq_matrix_eq_of_mulVec fun x => ?_
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, bnq_sub_one_mulVec g, bnq_sub_one_mulVec g',
    hq x, sub_self]

end Semilinear

section Linear

variable {F : Type} [Field F]

theorem bnq_linear_part {n : ℕ} [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (B : AddSubgroup (AddAut (Fin 4 → F))) (h2 : ∀ a ∈ B, a + a = 0)
    (hquad : ∀ a ∈ B, ∀ b ∈ B, ∀ x, a (b x - x) = b x - x)
    (hN : ∀ a ∈ B, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x,
      a (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (a x)) :
    ∃ r : ℕ, r ≤ 2 ∧ Nat.card (bnqLinFix B) = Nat.card F ^ (4 - r) ∧
      Nat.card (bnqLinSub B) ^ 2 ≤ Nat.card F ^ (r ^ 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_sq (p := 2) (f := n) hF
  obtain ⟨σ, hσ, -, hS⟩ := statedSU_data hF
  have hmemB : ∀ g ∈ bnqLinMat B, bnqGlAct g ∈ B := fun g hg =>
    (mem_bnqLinSub.mp (mem_bnqLinMat.mp hg)).1
  have hsub : ∀ g ∈ bnqLinMat B, g ∈ StatedSU 4 (2 ^ n) F := by
    intro g hg
    obtain ⟨g₀, hg₀, h₀⟩ := bnq_exists_statedSU hF B h2 hN (mem_bnqLinMat.mp hg)
    rw [← bnqGlAct_injective h₀]
    exact hg₀
  have hBU : bnqLinMat B ≤ SUid σ 4 := by
    rw [hS]
    exact hsub
  have hquadM : ∀ b ∈ bnqLinMat B, ∀ b' ∈ bnqLinMat B,
      ((b : Matrix (Fin 4) (Fin 4) F) - 1) * ((b' : Matrix (Fin 4) (Fin 4) F) - 1) = 0 :=
    fun b hb b' hb' => bnq_quad_matrix (g := b) (g' := b')
      (fun x => hquad (bnqGlAct b) (hmemB b hb) (bnqGlAct b') (hmemB b' hb') x)
  have hinv : ∀ b ∈ bnqLinMat B, b * b = 1 := fun b hb =>
    bnqGlAct_injective (by
      rw [bnqGlAct_mul, bnqGlAct_one]
      exact h2 _ (hmemB b hb))
  obtain ⟨r, hr, hcard, hsq⟩ := su4_quadratic_card_le σ hσ (bnqLinMat B) hBU hinv hquadM
  refine ⟨r, hr, ?_, ?_⟩
  · rw [← hcard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨fun hx b hb => hx (bnqGlAct b) hb,
      fun hx a ha => ?_⟩)
    obtain ⟨g, -, hga⟩ := bnq_exists_statedSU hF B h2 hN ha
    rw [← hga]
    exact hx g (mem_bnqLinMat.mpr (by rw [hga]; exact ha))
  · rw [bnq_card_linMat hF B h2 hN] at hsq
    exact hsq

theorem bnq_nonlin_fix_sq {n : ℕ} [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (B : AddSubgroup (AddAut (Fin 4 → F))) (h2 : ∀ a ∈ B, a + a = 0)
    (hquad : ∀ a ∈ B, ∀ b ∈ B, ∀ x, a (b x - x) = b x - x)
    (hN : ∀ a ∈ B, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x,
      a (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (a x))
    {s : AddAut (Fin 4 → F)} (hsB : s ∈ B) (hsnl : ¬ bnqIsLin s) :
    Nat.card {x : Fin 4 → F // ∀ a ∈ B, a x = x} ^ 2 ≤ Nat.card (bnqLinFix B) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_sq (p := 2) (f := n) hF
  obtain ⟨θ, hθ⟩ := bnq_exists_semilinear hF (h2 s hsB) (hN s hsB)
  have hθi : ∀ c, θ (θ c) = c := bnq_ringHom_invol (h2 s hsB) hθ
  have hne : ∃ c, θ c ≠ c := bnq_exists_ne hθ hsnl
  have hmem : ∀ x ∈ bnqLinFix B, s x ∈ bnqLinFix B := fun x hx a ha => by
    have h1 := hquad a (mem_bnqLinSub.mp ha).1 s hsB x
    rw [map_sub, hx a ha] at h1
    exact sub_left_inj.mp h1
  let s' : ↥(bnqLinFix B) ≃+ ↥(bnqLinFix B) :=
    { toFun := fun x => ⟨s x.1, hmem x.1 x.2⟩
      invFun := fun x => ⟨s x.1, hmem x.1 x.2⟩
      left_inv := fun x => Subtype.ext (bnq_invol_apply (h2 s hsB) x.1)
      right_inv := fun x => Subtype.ext (bnq_invol_apply (h2 s hsB) x.1)
      map_add' := fun x y => Subtype.ext (map_add s x.1 y.1) }
  have hs' : ∀ (c : F) (x : ↥(bnqLinFix B)), s' (c • x) = θ c • s' x :=
    fun c x => Subtype.ext (hθ c x.1)
  have hss : ∀ x : ↥(bnqLinFix B), s' (s' x) = x :=
    fun x => Subtype.ext (bnq_invol_apply (h2 s hsB) x.1)
  have hsq := card_fix_sq_of_semilinear_involution (K := F) (C := ↥(bnqLinFix B)) θ hθi hne
    s' hs' hss
  have hinj : Nat.card {x : Fin 4 → F // ∀ a ∈ B, a x = x} ≤
      Nat.card {y : ↥(bnqLinFix B) // s' y = y} := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨⟨x.1, fun a ha => x.2 a (mem_bnqLinSub.mp ha).1⟩, Subtype.ext (x.2 s hsB)⟩ :
        {y : ↥(bnqLinFix B) // s' y = y})) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1.1) hxy)
  calc Nat.card {x : Fin 4 → F // ∀ a ∈ B, a x = x} ^ 2
      ≤ Nat.card {y : ↥(bnqLinFix B) // s' y = y} ^ 2 := Nat.pow_le_pow_left hinj 2
    _ = Nat.card (bnqLinFix B) := hsq

theorem bnq_card_le_two {n : ℕ} [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (B : AddSubgroup (AddAut (Fin 4 → F))) (h2 : ∀ a ∈ B, a + a = 0)
    (hN : ∀ a ∈ B, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x,
      a (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (a x))
    {s : AddAut (Fin 4 → F)} (hsB : s ∈ B) (hsnl : ¬ bnqIsLin s) :
    Nat.card B ≤ 2 * Nat.card (bnqLinSub B) := by
  classical
  obtain ⟨θs, hθs⟩ := bnq_exists_semilinear hF (h2 s hsB) (hN s hsB)
  have hmul : ∀ a ∈ B, ¬ bnqIsLin a → s + a ∈ bnqLinSub B := fun a ha hna => by
    obtain ⟨θ, hθ⟩ := bnq_exists_semilinear hF (h2 a ha) (hN a ha)
    exact ⟨B.add_mem hsB ha, bnq_isLin_add_of_semilinear hθs hθ
      (bnq_ringHom_invol (h2 s hsB) hθs) (bnq_ringHom_invol (h2 a ha) hθ)
      (bnq_exists_ne hθs hsnl) (bnq_exists_ne hθ hna)⟩
  let f : B → Bool × ↥(bnqLinSub B) := fun a =>
    if h : bnqIsLin (a : AddAut (Fin 4 → F)) then (false, ⟨a.1, a.2, h⟩)
    else (true, ⟨s + a.1, hmul a.1 a.2 h⟩)
  have hf : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [f] at hab
    by_cases hal : bnqIsLin a <;> by_cases hbl : bnqIsLin b
    · rw [dif_pos hal, dif_pos hbl] at hab
      exact Subtype.ext (congrArg (fun p : Bool × ↥(bnqLinSub B) => p.2.1) hab)
    · rw [dif_pos hal, dif_neg hbl] at hab
      cases hab
    · rw [dif_neg hal, dif_pos hbl] at hab
      cases hab
    · rw [dif_neg hal, dif_neg hbl] at hab
      have h3 : s + a = s + b := congrArg (fun p : Bool × ↥(bnqLinSub B) => p.2.1) hab
      exact Subtype.ext (add_left_cancel h3)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  exact h1

end Linear

section Arithmetic

theorem bnq_le_of_sq_le {x y : ℕ} (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (Nat.pow_le_pow_iff_left two_ne_zero).mp h

theorem bnq_arith_lin {b c q r : ℕ} (hq : 0 < q) (hr : r ≤ 2) (hb : b ^ 2 ≤ q ^ (r ^ 2))
    (hc : c = q ^ (4 - r)) : b * c ≤ q ^ 4 := by
  have hexp : r ^ 2 + (4 - r) * 2 ≤ 8 := by
    interval_cases r <;> norm_num
  have h1 : (b * c) ^ 2 ≤ (q ^ 4) ^ 2 := by
    calc (b * c) ^ 2 = b ^ 2 * c ^ 2 := mul_pow b c 2
      _ ≤ q ^ (r ^ 2) * c ^ 2 := Nat.mul_le_mul_right _ hb
      _ = q ^ (r ^ 2 + (4 - r) * 2) := by rw [hc, ← pow_mul, pow_add]
      _ ≤ q ^ 8 := Nat.pow_le_pow_right hq hexp
      _ = (q ^ 4) ^ 2 := by ring
  exact bnq_le_of_sq_le h1

theorem bnq_arith_nonlin {b c l q r : ℕ} (hq : 4 ≤ q) (hr : r ≤ 2) (hb : b ≤ 2 * l)
    (hl : l ^ 2 ≤ q ^ (r ^ 2)) (hc : c ^ 2 ≤ q ^ (4 - r)) : b * c ≤ q ^ 4 := by
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  have hexp : r ^ 2 + (4 - r) ≤ 6 := by
    interval_cases r <;> norm_num
  have h6 : q ^ (r ^ 2) * q ^ (4 - r) ≤ q ^ 6 := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) hexp
  have hkey : 4 * q ^ (r ^ 2) * q ^ (4 - r) ≤ q ^ 8 := by
    calc 4 * q ^ (r ^ 2) * q ^ (4 - r) = 4 * (q ^ (r ^ 2) * q ^ (4 - r)) := by ring
      _ ≤ 4 * q ^ 6 := Nat.mul_le_mul_left 4 h6
      _ ≤ q ^ 2 * q ^ 6 := Nat.mul_le_mul_right _ h4
      _ = q ^ 8 := by ring
  have hb2 : b ^ 2 ≤ 4 * l ^ 2 := by
    calc b ^ 2 ≤ (2 * l) ^ 2 := Nat.pow_le_pow_left hb 2
      _ = 4 * l ^ 2 := by ring
  have h1 : (b * c) ^ 2 ≤ (q ^ 4) ^ 2 := by
    calc (b * c) ^ 2 = b ^ 2 * c ^ 2 := mul_pow b c 2
      _ ≤ (4 * l ^ 2) * c ^ 2 := Nat.mul_le_mul_right _ hb2
      _ ≤ (4 * q ^ (r ^ 2)) * q ^ (4 - r) := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hl) hc
      _ ≤ q ^ 8 := hkey
      _ = (q ^ 4) ^ 2 := by ring
  exact bnq_le_of_sq_le h1

end Arithmetic

theorem partB_N_quadratic {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (B : AddSubgroup (AddAut (Fin 4 → F)))
    (h2 : ∀ a ∈ B, a + a = 0)
    (hquad : ∀ a ∈ B, ∀ b ∈ B, ∀ x, a (b x - x) = b x - x)
    (hN : ∀ a ∈ B, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F, ∀ x,
      a (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
        ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (a x)) :
    Nat.card B * Nat.card {x : Fin 4 → F // ∀ a ∈ B, a x = x} ≤ Nat.card (Fin 4 → F) := by
  have hq : 4 ≤ Nat.card F := by
    have h2n : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2n 2
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have hF4 : Nat.card (Fin 4 → F) = Nat.card F ^ 4 := by
    rw [Nat.card_fun, h4]
  rw [hF4]
  obtain ⟨r, hr, hLF, hL⟩ := bnq_linear_part hF B h2 hquad hN
  by_cases hall : ∀ a ∈ B, bnqIsLin a
  · have hBc : Nat.card B = Nat.card (bnqLinSub B) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun a =>
        ⟨fun ha => ⟨ha, hall a ha⟩, fun h => h.1⟩)
    have hfix : Nat.card {x : Fin 4 → F // ∀ a ∈ B, a x = x} = Nat.card (bnqLinFix B) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x =>
        ⟨fun hx a ha => hx a (mem_bnqLinSub.mp ha).1, fun hx a ha => hx a ⟨ha, hall a ha⟩⟩)
    rw [hBc, hfix]
    exact bnq_arith_lin (by omega) hr hL hLF
  · obtain ⟨s, hsB, hsnl⟩ : ∃ s ∈ B, ¬ bnqIsLin s := by
      by_contra h
      exact hall fun a ha => by_contra fun hna => h ⟨a, ha, hna⟩
    have hb := bnq_card_le_two hF B h2 hN hsB hsnl
    have hc := bnq_nonlin_fix_sq hF B h2 hquad hN hsB hsnl
    rw [hLF] at hc
    exact bnq_arith_nonlin hq hr hb hL hc

end CFSG.LocalAnalysis.RankThreeUC
