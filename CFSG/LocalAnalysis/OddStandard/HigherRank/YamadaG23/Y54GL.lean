module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1 Module

variable {F : Type} [Group F]

private lemma mul_comm_of_isE (hF : IsE 3 F) : ∀ a b : F, a * b = b * a := by
  haveI : IsMulCommutative (⊤ : Subgroup F) := hF.1.1
  intro a b
  exact congrArg Subtype.val
    (mul_comm' (M := (⊤ : Subgroup F)) ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)

private lemma exists_ne_three {F : Type} [Finite F] (hcard : 4 ≤ Nat.card F) (x y z : F) :
    ∃ w : F, w ≠ x ∧ w ≠ y ∧ w ≠ z := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : 4 ≤ Fintype.card F := by rwa [Fintype.card_eq_nat_card]
  have h3 : ({x, y, z} : Finset F).card ≤ 3 := Finset.card_le_three
  have hsne : ({x, y, z} : Finset F) ≠ ⊤ := by
    intro h
    have hc : ({x, y, z} : Finset F).card = Fintype.card F := by rw [h]; simp
    omega
  obtain ⟨w, hw⟩ := SetLike.exists_not_mem_of_ne_top ({x, y, z} : Finset F) hsne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  exact ⟨w, hw.1, hw.2.1, hw.2.2⟩

private def addEquivLinearEquiv (A : Type*) [AddCommGroup A] [Module (ZMod 2) A] :
    (A ≃+ A) ≃ (A ≃ₗ[ZMod 2] A) where
  toFun f := f.toLinearEquiv fun c x => ZMod.map_smul (f : A →+ A) c x
  invFun g := g.toAddEquiv
  left_inv f := AddEquiv.ext fun x => rfl
  right_inv g := LinearEquiv.ext fun x => rfl

private def linearEquivToMulAut {F : Type} [CommGroup F] [Module (ZMod 2) (Additive F)]
    (E : Additive F ≃ₗ[ZMod 2] Additive F) : MulAut F where
  toFun x := (E (Additive.ofMul x)).toMul
  invFun x := (E.symm (Additive.ofMul x)).toMul
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp [ofMul_mul, toMul_add]

@[simp]
private lemma linearEquivToMulAut_apply {F : Type} [CommGroup F] [Module (ZMod 2) (Additive F)]
    (E : Additive F ≃ₗ[ZMod 2] Additive F) (x : F) :
    linearEquivToMulAut E x = (E (Additive.ofMul x)).toMul := rfl

private lemma exists_basis_pair {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (hfin : Module.finrank (ZMod 2) A = 3) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) : ∃ B : Basis (Fin 3) (ZMod 2) A, B 0 = a ∧ B 1 = b := by
  have hli2 : LinearIndependent (ZMod 2) ![a, b] := by
    rw [LinearIndependent.pair_iff' ha]
    intro c
    have hc : c = 0 ∨ c = 1 := by
      have h : c.val = 0 ∨ c.val = 1 := by have := c.val_lt; omega
      rcases h with h | h
      · left; exact (ZMod.val_eq_zero c).mp h
      · right
        rw [← ZMod.natCast_zmod_val c, h]
        norm_num
    rcases hc with rfl | rfl
    · simpa using (Ne.symm hb)
    · simpa using hab
  have hproper : Submodule.span (ZMod 2) (Set.range ![a, b]) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have h1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range ![a, b])) = 2 := by
      rw [finrank_span_eq_card hli2]; simp
    rw [htop] at h1
    have : Module.finrank (ZMod 2) A = 2 := by simpa using h1
    omega
  obtain ⟨c, -, hc⟩ := SetLike.exists_of_lt hproper
  have hli3 : LinearIndependent (ZMod 2) (Fin.snoc ![a, b] c) :=
    LinearIndependent.finSnoc hli2 hc
  have hcard : Fintype.card (Fin 3) = Module.finrank (ZMod 2) A := by simp [hfin]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli3 hcard, ?_, ?_⟩
  · simp
  · simp

theorem gl_card (hF : IsE 3 F) : Nat.card (MulAut F) = 168 := by
  have hcomm := mul_comm_of_isE hF
  letI : CommGroup F := { ‹Group F› with mul_comm := hcomm }
  have h2 : ∀ x : F, x ^ 2 = 1 := fun x => hF.1.2 x trivial
  letI : Module (ZMod 2) (Additive F) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      rw [← toMul_eq_one, toMul_nsmul, h2]
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF.2]; norm_num)
  haveI : Fintype (Additive F) := Fintype.ofFinite (Additive F)
  have hcardV : Fintype.card (Additive F) = 8 := by
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr Additive.ofMul, hF.2]
    norm_num
  have hfr := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive F)
  rw [hcardV, ZMod.card] at hfr
  have hfin : Module.finrank (ZMod 2) (Additive F) = 3 := by
    have h : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive F) = 2 ^ 3 := by
      rw [← hfr]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  let e : Additive F ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    LinearEquiv.ofFinrankEq (Additive F) (Fin 3 → ZMod 2) (by rw [hfin, Module.finrank_fin_fun])
  let φ : (Additive F ≃ₗ[ZMod 2] Additive F) ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive F)).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
        (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).symm)
  calc Nat.card (MulAut F)
      = Nat.card (AddAut (Additive F)) :=
          Nat.card_congr (MulEquiv.toAdditive (G := F) (H := F))
      _ = Nat.card (Additive F ≃ₗ[ZMod 2] Additive F) :=
          Nat.card_congr (addEquivLinearEquiv (Additive F))
      _ = Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
          Nat.card_congr φ.toEquiv
      _ = 168 := by
          rw [Matrix.card_GL_field]
          decide

theorem gl_trans2 (hF : IsE 3 F) {a b a' b' : F} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (ha' : a' ≠ 1) (hb' : b' ≠ 1) (hab' : a' ≠ b') :
    ∃ α : MulAut F, α a = a' ∧ α b = b' := by
  have hcomm := mul_comm_of_isE hF
  letI : CommGroup F := { ‹Group F› with mul_comm := hcomm }
  have h2 : ∀ x : F, x ^ 2 = 1 := fun x => hF.1.2 x trivial
  letI : Module (ZMod 2) (Additive F) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      rw [← toMul_eq_one, toMul_nsmul, h2]
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF.2]; norm_num)
  haveI : Fintype (Additive F) := Fintype.ofFinite (Additive F)
  have hcardV : Fintype.card (Additive F) = 8 := by
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr Additive.ofMul, hF.2]
    norm_num
  have hfr := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive F)
  rw [hcardV, ZMod.card] at hfr
  have hfin : Module.finrank (ZMod 2) (Additive F) = 3 := by
    have h : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive F) = 2 ^ 3 := by
      rw [← hfr]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  have ha0 : Additive.ofMul a ≠ 0 := fun h => ha (ofMul_eq_zero.mp h)
  have hb0 : Additive.ofMul b ≠ 0 := fun h => hb (ofMul_eq_zero.mp h)
  have hab0 : Additive.ofMul a ≠ Additive.ofMul b :=
    fun h => hab (Additive.ofMul.injective h)
  obtain ⟨B, hB0, hB1⟩ := exists_basis_pair hfin ha0 hb0 hab0
  have ha0' : Additive.ofMul a' ≠ 0 := fun h => ha' (ofMul_eq_zero.mp h)
  have hb0' : Additive.ofMul b' ≠ 0 := fun h => hb' (ofMul_eq_zero.mp h)
  have hab0' : Additive.ofMul a' ≠ Additive.ofMul b' :=
    fun h => hab' (Additive.ofMul.injective h)
  obtain ⟨B', hB0', hB1'⟩ := exists_basis_pair hfin ha0' hb0' hab0'
  refine ⟨linearEquivToMulAut (B.equiv B' (Equiv.refl (Fin 3))), ?_, ?_⟩
  · rw [linearEquivToMulAut_apply, ← hB0, Basis.equiv_apply, Equiv.refl_apply, hB0']; rfl
  · rw [linearEquivToMulAut_apply, ← hB1, Basis.equiv_apply, Equiv.refl_apply, hB1']; rfl

theorem gl_trans1 (hF : IsE 3 F) {a a' : F} (ha : a ≠ 1) (ha' : a' ≠ 1) :
    ∃ α : MulAut F, α a = a' := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF.2]; norm_num)
  have hcard : 4 ≤ Nat.card F := by rw [hF.2]; norm_num
  obtain ⟨b, hb1, hba, -⟩ := exists_ne_three hcard 1 a 1
  obtain ⟨b', hb'1, hb'a', -⟩ := exists_ne_three hcard 1 a' 1
  obtain ⟨α, hα, -⟩ := gl_trans2 hF ha hb1 (Ne.symm hba) ha' hb'1 (Ne.symm hb'a')
  exact ⟨α, hα⟩

end CFSG.OddStandard.HigherRank.YamadaG23
