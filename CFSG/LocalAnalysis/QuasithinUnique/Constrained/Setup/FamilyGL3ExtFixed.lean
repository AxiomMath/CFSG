module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Fixed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Classify
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Ext
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Sub

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace Matrix

section Conj

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem rep_mul_apply (ρ : G →* (E ≃ₗ[ZMod 2] E)) (g h : G) (x : E) :
    ρ (g * h) x = ρ g (ρ h x) := by
  rw [map_mul]
  rfl

theorem natCard_fixedSub_conj (ρ : G →* (E ≃ₗ[ZMod 2] E)) (A : Subgroup G) (m : G) :
    Nat.card (fixedSub ρ (A.map (MulAut.conj m).toMonoidHom)) = Nat.card (fixedSub ρ A) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨ρ m⁻¹ x.1, fun a ha => ?_⟩
      invFun := fun y => ⟨ρ m y.1, fun a' ha' => ?_⟩
      left_inv := fun x => Subtype.ext ?_
      right_inv := fun y => Subtype.ext ?_ }
  · have hmem : m * a * m⁻¹ ∈ A.map (MulAut.conj m).toMonoidHom := ⟨a, ha, rfl⟩
    have h1 := x.2 _ hmem
    have h2 : a * m⁻¹ = m⁻¹ * (m * a * m⁻¹) := by group
    calc ρ a (ρ m⁻¹ x.1) = ρ (a * m⁻¹) x.1 := (rep_mul_apply ρ a m⁻¹ x.1).symm
      _ = ρ (m⁻¹ * (m * a * m⁻¹)) x.1 := by rw [h2]
      _ = ρ m⁻¹ (ρ (m * a * m⁻¹) x.1) := rep_mul_apply ρ _ _ _
      _ = ρ m⁻¹ x.1 := by rw [h1]
  · obtain ⟨a, ha, rfl⟩ := ha'
    have h1 := y.2 a ha
    have h2 : m * a * m⁻¹ * m = m * a := by group
    calc ρ ((MulAut.conj m).toMonoidHom a) (ρ m y.1) = ρ (m * a * m⁻¹ * m) y.1 := by
          rw [rep_mul_apply]; rfl
      _ = ρ (m * a) y.1 := by rw [h2]
      _ = ρ m (ρ a y.1) := rep_mul_apply ρ _ _ _
      _ = ρ m y.1 := by rw [h1]
  · show ρ m (ρ m⁻¹ x.1) = x.1
    rw [← rep_mul_apply, mul_inv_cancel, map_one]
    rfl
  · show ρ m⁻¹ (ρ m y.1) = y.1
    rw [← rep_mul_apply, inv_mul_cancel, map_one]
    rfl

end Conj

@[expose] def congList : List Mat3 :=
  [!![0, 1, 1; 1, 1, 0; 1, 1, 1], !![0, 0, 1; 0, 1, 0; 1, 0, 1], !![0, 1, 0; 0, 1, 1; 1, 1, 1],
    !![0, 0, 1; 1, 0, 1; 1, 1, 0], !![0, 1, 1; 1, 0, 1; 1, 1, 1], !![0, 0, 1; 0, 1, 1; 1, 1, 1],
    !![0, 0, 1; 0, 1, 0; 1, 1, 0], !![0, 1, 0; 1, 0, 1; 1, 1, 0], !![0, 0, 1; 1, 0, 1; 1, 1, 1],
    !![0, 0, 1; 0, 1, 1; 1, 0, 1], !![0, 1, 0; 1, 1, 0; 1, 1, 1], !![0, 1, 0; 0, 1, 1; 1, 1, 0],
    !![1, 0, 1; 1, 1, 0; 1, 1, 1], !![0, 0, 1; 0, 1, 1; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    !![0, 1, 0; 0, 1, 1; 1, 0, 0], !![1, 0, 0; 1, 0, 1; 1, 1, 1], !![0, 0, 1; 0, 1, 1; 1, 1, 0],
    !![0, 1, 0; 1, 0, 0; 1, 0, 1], !![0, 1, 0; 1, 0, 0; 1, 1, 1], !![0, 0, 1; 1, 0, 0; 1, 1, 0],
    !![1, 0, 0; 1, 1, 0; 1, 1, 1], !![0, 1, 0; 0, 1, 1; 1, 0, 1], !![0, 0, 1; 1, 0, 0; 1, 1, 1],
    !![0, 1, 1; 1, 0, 0; 1, 1, 0], !![1, 0, 0; 1, 0, 1; 1, 1, 0], !![0, 1, 1; 1, 0, 0; 1, 0, 1],
    !![0, 0, 1; 0, 1, 0; 1, 1, 1]]

theorem sym_congruent : ∀ s00 s01 s02 s10 s11 s12 s20 s21 s22 : ZMod 2,
    s10 = s01 → s20 = s02 → s21 = s12 →
    s00 * s11 * s22 - s00 * s12 * s21 - s01 * s10 * s22 + s01 * s12 * s20 + s02 * s10 * s21 -
      s02 * s11 * s20 = 1 →
    ∃ M ∈ congList, M * !![s00, s01, s02; s10, s11, s12; s20, s21, s22] * Mᵀ = 1 := by
  decide +kernel

theorem tGen_sIncl_sq (s : GL32) : (sIncl s * tGen) * (sIncl s * tGen) = sIncl (s * tauHom s) := by
  calc sIncl s * tGen * (sIncl s * tGen) = sIncl s * (tGen * sIncl s) * tGen := by group
    _ = sIncl s * (sIncl (tauHom s) * tGen) * tGen := by rw [tGen_mul_sIncl]
    _ = sIncl s * sIncl (tauHom s) * (tGen * tGen) := by group
    _ = sIncl (s * tauHom s) := by rw [tGen_mul_self, mul_one, ← map_mul]

theorem exists_conj_tGen {a : H32} (ha : a ∉ (sIncl : GL32 →* H32).range) (ha2 : a * a = 1) :
    ∃ m : GL32, sIncl m * a * (sIncl m)⁻¹ = tGen := by
  rcases exists_eq_sIncl_mul a with h | h
  · exact absurd ⟨a.left, h.symm⟩ ha
  set s : GL32 := a.left with hsdef
  have hs : s * tauHom s = 1 := by
    rw [h, tGen_sIncl_sq] at ha2
    have h1 : sIncl (s * tauHom s) = sIncl 1 := ha2.trans (map_one sIncl).symm
    exact SemidirectProduct.inl_injective h1
  have hsinv : tauHom s = s⁻¹ := eq_inv_of_mul_eq_one_right hs
  have hu : ((s⁻¹ : GL32) : Mat3)ᵀ = ((s⁻¹ : GL32) : Mat3) := by
    have := congrArg (fun x : GL32 => (x : Mat3)) hsinv
    rw [tauHom_val] at this
    exact this
  have hsym : (s : Mat3)ᵀ = (s : Mat3) := by
    have h1 : ((s⁻¹ : GL32) : Mat3) * (s : Mat3) = 1 := Units.inv_mul s
    have h2 : (s : Mat3)ᵀ * ((s⁻¹ : GL32) : Mat3) = 1 := by
      have := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_mul, hu, Matrix.transpose_one] at this
    calc (s : Mat3)ᵀ = (s : Mat3)ᵀ * (((s⁻¹ : GL32) : Mat3) * (s : Mat3)) := by
          rw [h1, Matrix.mul_one]
      _ = ((s : Mat3)ᵀ * ((s⁻¹ : GL32) : Mat3)) * (s : Mat3) := by rw [Matrix.mul_assoc]
      _ = (s : Mat3) := by rw [h2, Matrix.one_mul]
  have hdet : (s : Mat3).det = 1 := eq_one_of_isUnit_zmod_two (Matrix.isUnits_det_units s)
  rw [Matrix.det_fin_three] at hdet
  have s10 : (s : Mat3) 1 0 = (s : Mat3) 0 1 := congrFun (congrFun hsym 0) 1
  have s20 : (s : Mat3) 2 0 = (s : Mat3) 0 2 := congrFun (congrFun hsym 0) 2
  have s21 : (s : Mat3) 2 1 = (s : Mat3) 1 2 := congrFun (congrFun hsym 1) 2
  obtain ⟨M, -, hMeq⟩ := sym_congruent ((s : Mat3) 0 0) ((s : Mat3) 0 1) ((s : Mat3) 0 2)
    ((s : Mat3) 1 0) ((s : Mat3) 1 1) ((s : Mat3) 1 2) ((s : Mat3) 2 0) ((s : Mat3) 2 1)
    ((s : Mat3) 2 2) s10 s20 s21 hdet
  rw [← Matrix.eta_fin_three (s : Mat3)] at hMeq
  have hM1 : M * ((s : Mat3) * Mᵀ) = 1 := by rw [← Matrix.mul_assoc]; exact hMeq
  have hM2 : ((s : Mat3) * Mᵀ) * M = 1 := mul_eq_one_comm.1 hM1
  let m : GL32 := ⟨M, (s : Mat3) * Mᵀ, hM1, hM2⟩
  refine ⟨m, ?_⟩
  rw [h]
  have hm1 : m * s * tauHom m⁻¹ = 1 := Units.ext (by
    rw [Units.val_mul, Units.val_mul, tauHom_val, inv_inv, Units.val_one]
    exact hMeq)
  calc sIncl m * (sIncl s * tGen) * (sIncl m)⁻¹
      = sIncl (m * s) * (tGen * sIncl m⁻¹) := by rw [map_inv, map_mul]; group
    _ = sIncl (m * s) * (sIncl (tauHom m⁻¹) * tGen) := by rw [tGen_mul_sIncl]
    _ = sIncl (m * s * tauHom m⁻¹) * tGen := by simp only [map_mul, mul_assoc]
    _ = tGen := by rw [hm1, map_one, one_mul]

section FixT

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def fixT (ρ : H32 →* (E ≃ₗ[ZMod 2] E)) : Submodule (ZMod 2) E where
  carrier := {x | ρ tGen x = x}
  add_mem' := fun {x y} hx hy => by
    show ρ tGen (x + y) = x + y
    rw [map_add, (hx : ρ tGen x = x), (hy : ρ tGen y = y)]
  zero_mem' := map_zero _
  smul_mem' := fun c x hx => by
    show ρ tGen (c • x) = c • x
    rw [map_smul, (hx : ρ tGen x = x)]

theorem natCard_fixT_repP : Nat.card (fixT repP) = 8 := by
  rw [← natCard_Vec3]
  refine Nat.card_congr
    { toFun := fun x => x.1.1
      invFun := fun a => ⟨(a, a), by
        show repP tGen (a, a) = (a, a)
        rw [repP_tGen]
        rfl⟩
      left_inv := fun x => Subtype.ext ?_
      right_inv := fun a => rfl }
  have h : repP tGen x.1 = x.1 := x.2
  rw [repP_tGen] at h
  have h1 : x.1.2 = x.1.1 := (Prod.ext_iff.1 h).1
  exact Prod.ext rfl h1.symm

theorem natCard_fixT_repQ : Nat.card (fixT repQ) = 32 := by
  have e : fixT repQ ≃ {X : Mat3 | X ∈ traceZero ∧ Xᵀ = X} :=
    { toFun := fun x => ⟨(x.1 : Mat3), x.1.2, by
        have h : repQ tGen x.1 = x.1 := x.2
        rw [repQ_tGen] at h
        exact congrArg Subtype.val h⟩
      invFun := fun X => ⟨⟨X.1, X.2.1⟩, by
        show repQ tGen ⟨X.1, X.2.1⟩ = ⟨X.1, X.2.1⟩
        rw [repQ_tGen]
        exact Subtype.ext X.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun X => rfl }
  rw [Nat.card_congr e, natCard_traceZero_setOf (fun X : Mat3 => Xᵀ = X)]
  decide +kernel

end FixT

section SPart

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem fixedSub_map_sIncl (ρ : H32 →* (E ≃ₗ[ZMod 2] E)) (B : Subgroup GL32) :
    fixedSub ρ (B.map sIncl) = fixedSub (ρ.comp sIncl) B := by
  ext x
  constructor
  · intro hx g hg
    exact hx (sIncl g) ⟨g, hg, rfl⟩
  · rintro hx _ ⟨g, hg, rfl⟩
    exact hx g hg

theorem repP_comp_sIncl : repP.comp sIncl = repPS := MonoidHom.ext repP_sIncl

theorem repQ_comp_sIncl : repQ.comp sIncl = repA := MonoidHom.ext repQ_sIncl

theorem natCard_fixedSub_repA (B : Subgroup GL32) :
    Nat.card (fixedSub repA B) = Nat.card (fixTrace3 B) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : Mat3), x.1.2, fun g hg => congrArg Subtype.val (x.2 g hg)⟩
      invFun := fun X => ⟨⟨X.1, X.2.1⟩, fun g hg => Subtype.ext (X.2.2 g hg)⟩
      left_inv := fun x => rfl
      right_inv := fun X => rfl }

theorem natCard_fixedSub_repPS (B : Subgroup GL32) :
    Nat.card (fixedSub repPS B) = Nat.card (fixVec3 B) * Nat.card (fixDual3 B) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun x => (⟨x.1.1, fun g hg => congrArg Prod.fst (x.2 g hg)⟩,
        ⟨x.1.2, fun g hg => congrArg Prod.snd (x.2 g hg)⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), fun g hg => Prod.ext (p.1.2 g hg) (p.2.2 g hg)⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }

end SPart

theorem sIncl_injective : Function.Injective sIncl := SemidirectProduct.inl_injective

theorem fixed_data_le_S {A : Subgroup H32} (hA : A ≤ (sIncl : GL32 →* H32).range) (hA0 : A ≠ ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a ^ 2 = 1) :
    (Nat.card A = 2 ∧ Nat.card (fixedSub repP A) = 16 ∧ Nat.card (fixedSub repQ A) = 16) ∨
    (Nat.card A = 4 ∧ Nat.card (fixedSub repP A) = 8 ∧ Nat.card (fixedSub repQ A) = 4) := by
  obtain ⟨B, rfl⟩ : ∃ B : Subgroup GL32, A = B.map sIncl :=
    ⟨A.comap sIncl, (Subgroup.map_comap_eq_self hA).symm⟩
  have hB0 : B ≠ ⊥ := fun h => hA0 (by rw [h, Subgroup.map_bot])
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => by
    apply sIncl_injective
    rw [map_mul, map_mul]
    exact hcomm (sIncl a) ⟨a, ha, rfl⟩ (sIncl b) ⟨b, hb, rfl⟩
  have hsqB : ∀ a ∈ B, a ^ 2 = 1 := fun a ha => by
    apply sIncl_injective
    rw [map_pow, map_one]
    exact hsq (sIncl a) ⟨a, ha, rfl⟩
  have hdata := GL3_elementary_abelian_fixed_codimensions hB0 hcommB hsqB
  have hcard : Nat.card (B.map sIncl) = Nat.card B :=
    Subgroup.card_map_of_injective sIncl_injective
  have hP : Nat.card (fixedSub repP (B.map sIncl)) =
      Nat.card (fixVec3 B) * Nat.card (fixDual3 B) := by
    rw [fixedSub_map_sIncl, repP_comp_sIncl, natCard_fixedSub_repPS]
  have hQ : Nat.card (fixedSub repQ (B.map sIncl)) = Nat.card (fixTrace3 B) := by
    rw [fixedSub_map_sIncl, repQ_comp_sIncl, natCard_fixedSub_repA]
  rw [hcard, hP, hQ]
  rcases hdata with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · left
    exact ⟨h1, by rw [h2, h3], h4⟩
  · right
    refine ⟨h1, ?_, h3⟩
    rcases h2 with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · rw [h5, h6]
    · rw [h5, h6]

theorem fixedSub_eq_fixT {A : Subgroup H32} (ht : tGen ∈ A) (hA : ∀ a ∈ A, a = 1 ∨ a = tGen)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] (ρ : H32 →* (E ≃ₗ[ZMod 2] E)) :
    fixedSub ρ A = fixT ρ := by
  ext x
  constructor
  · intro hx
    exact hx tGen ht
  · intro hx a ha
    rcases hA a ha with rfl | rfl
    · rw [map_one]
      rfl
    · exact hx

theorem fixed_data_with_t {A : Subgroup H32} (ht : tGen ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a ^ 2 = 1) :
    (Nat.card A = 2 ∧ Nat.card (fixedSub repP A) = 8 ∧ Nat.card (fixedSub repQ A) = 32) ∨
    (Nat.card A = 4 ∧ Nat.card (fixedSub repP A) = 4 ∧ Nat.card (fixedSub repQ A) ≤ 16) := by
  set B : Subgroup GL32 := A.comap sIncl with hB
  have hBmem : ∀ n, n ∈ B ↔ sIncl n ∈ A := fun n => Iff.rfl
  have hc2 : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
  have hinr : ∀ ε : Multiplicative (ZMod 2), (SemidirectProduct.inr ε : H32) ∈ A := by
    intro ε
    rcases hc2 ε with rfl | rfl
    · rw [map_one]
      exact A.one_mem
    · exact ht
  have hleft : ∀ a ∈ A, a.left ∈ B := fun a ha => by
    have h1 : sIncl a.left = a * (SemidirectProduct.inr a.right)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact SemidirectProduct.inl_left_mul_inr_right a
    rw [hBmem, h1]
    exact A.mul_mem ha (A.inv_mem (hinr _))
  have hdecomp : ∀ a : H32, a = sIncl a.left * SemidirectProduct.inr a.right := fun a =>
    (SemidirectProduct.inl_left_mul_inr_right a).symm
  let e : A ≃ B × Multiplicative (ZMod 2) :=
    { toFun := fun a => (⟨a.1.left, hleft a.1 a.2⟩, a.1.right)
      invFun := fun p => ⟨sIncl p.1.1 * SemidirectProduct.inr p.2, A.mul_mem p.1.2 (hinr _)⟩
      left_inv := fun a => Subtype.ext (SemidirectProduct.inl_left_mul_inr_right a.1)
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext
          simp [sIncl, SemidirectProduct.mul_left]
        · simp [sIncl, SemidirectProduct.mul_right] }
  have hcardA : Nat.card A = Nat.card B * 2 := by
    rw [Nat.card_congr e, Nat.card_prod]
    congr 1
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hτ : ∀ n ∈ B, tauHom n = n := fun n hn => by
    have h1 := hcomm tGen ht (sIncl n) hn
    rw [tGen_mul_sIncl] at h1
    exact sIncl_injective (mul_right_cancel h1)
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => by
    apply sIncl_injective
    rw [map_mul, map_mul]
    exact hcomm _ ha _ hb
  have hsqB : ∀ a ∈ B, a ^ 2 = 1 := fun a ha => by
    apply sIncl_injective
    rw [map_pow, map_one]
    exact hsq _ ha
  by_cases hB0 : B = ⊥
  · left
    have hBcard : Nat.card B = 1 := by rw [hB0]; exact Subgroup.card_bot
    have hA : ∀ a ∈ A, a = 1 ∨ a = tGen := fun a ha => by
      have h1 : a.left = 1 := Subgroup.mem_bot.1 (hB0 ▸ hleft a ha)
      have h2 : a = SemidirectProduct.inr a.right := by
        rw [hdecomp a, h1, map_one, one_mul]
        simp
      rcases hc2 a.right with h3 | h3
      · left
        rw [h2, h3, map_one]
      · right
        rw [h2, h3]
        rfl
    refine ⟨by rw [hcardA, hBcard], ?_, ?_⟩
    · rw [fixedSub_eq_fixT ht hA, natCard_fixT_repP]
    · rw [fixedSub_eq_fixT ht hA, natCard_fixT_repQ]
  · right
    have hdata := GL3_elementary_abelian_fixed_codimensions hB0 hcommB hsqB
    have hgt : ∀ g ∈ B, ((g⁻¹ : GL32) : Mat3)ᵀ = (g : Mat3) := fun g hg =>
      (tauHom_val g).symm.trans (congrArg Units.val (hτ g hg))
    have hdual : fixDual3 B = fixVec3 B := by
      ext v
      refine ⟨fun h g hg => ?_, fun h g hg => ?_⟩
      · have := h g hg
        rwa [hgt g hg] at this
      · show ((g⁻¹ : GL32) : Mat3)ᵀ *ᵥ v = v
        rw [hgt g hg]
        exact h g hg
    rcases hdata with ⟨hB2, hV, hD, hT⟩ | ⟨hB4, hVD, hT⟩
    swap
    · exfalso
      have h1 : Nat.card (fixDual3 B) = Nat.card (fixVec3 B) := by rw [hdual]
      rcases hVD with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> omega
    · refine ⟨by rw [hcardA, hB2], ?_, ?_⟩
      · rw [← hV]
        refine Nat.card_congr
          { toFun := fun x => ⟨x.1.1, fun g hg => ?_⟩
            invFun := fun v => ⟨(v.1, v.1), fun a ha => ?_⟩
            left_inv := fun x => Subtype.ext ?_
            right_inv := fun v => rfl }
        · have h1 : repP (sIncl g) x.1 = x.1 := x.2 (sIncl g) ((hBmem g).1 hg)
          rw [repP_sIncl] at h1
          exact congrArg Prod.fst h1
        · have hvV : ∀ g ∈ B, (g : Mat3) *ᵥ (v : Vec3) = v := v.2
          have hvD : ∀ g ∈ B, ((g⁻¹ : GL32) : Mat3)ᵀ *ᵥ (v : Vec3) = v := by
            have : (v : Vec3) ∈ fixDual3 B := by rw [hdual]; exact v.2
            exact this
          show repP a (v.1, v.1) = (v.1, v.1)
          rw [hdecomp a, map_mul, LinearEquiv.mul_apply]
          have h1 : repP (SemidirectProduct.inr a.right) (v.1, v.1) = (v.1, v.1) := by
            rcases hc2 a.right with h | h
            · rw [h, map_one, map_one]
              rfl
            · rw [h]
              change repP tGen (v.1, v.1) = _
              rw [repP_tGen]
              rfl
          rw [h1, repP_sIncl]
          exact Prod.ext (hvV _ (hleft a ha)) (hvD _ (hleft a ha))
        · have h : repP tGen x.1 = x.1 := x.2 tGen ht
          rw [repP_tGen] at h
          exact Prod.ext rfl (Prod.ext_iff.1 h).1.symm
      · have hle : fixedSub repQ A ≤ fixedSub repQ (B.map sIncl) := fun x hx a ha => by
          obtain ⟨g, hg, rfl⟩ := ha
          exact hx _ ((hBmem g).1 hg)
        calc Nat.card (fixedSub repQ A) ≤ Nat.card (fixedSub repQ (B.map sIncl)) :=
              Nat.card_le_card_of_injective (Submodule.inclusion hle)
                (Submodule.inclusion_injective _)
          _ = Nat.card (fixTrace3 B) := by
              rw [fixedSub_map_sIncl, repQ_comp_sIncl, natCard_fixedSub_repA]
          _ = 16 := hT

theorem fixed_data_not_S {A : Subgroup H32} (hA : ¬ A ≤ (sIncl : GL32 →* H32).range)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a ^ 2 = 1) :
    (Nat.card A = 2 ∧ Nat.card (fixedSub repP A) = 8 ∧ Nat.card (fixedSub repQ A) = 32) ∨
    (Nat.card A = 4 ∧ Nat.card (fixedSub repP A) = 4 ∧ Nat.card (fixedSub repQ A) ≤ 16) := by
  obtain ⟨a, haA, haS⟩ := Set.not_subset.1 hA
  have ha2 : a * a = 1 := by
    have := hsq a haA
    rwa [pow_two] at this
  obtain ⟨m, hm⟩ := exists_conj_tGen haS ha2
  have ht : tGen ∈ A.map (MulAut.conj (sIncl m)).toMonoidHom := ⟨a, haA, by
    rw [← hm]
    rfl⟩
  have hcomm' : ∀ x ∈ A.map (MulAut.conj (sIncl m)).toMonoidHom,
      ∀ y ∈ A.map (MulAut.conj (sIncl m)).toMonoidHom, x * y = y * x := by
    rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a₁ ha₁ a₂ ha₂]
  have hsq' : ∀ x ∈ A.map (MulAut.conj (sIncl m)).toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨a₁, ha₁, rfl⟩
    rw [← map_pow, hsq a₁ ha₁, map_one]
  have hcard : Nat.card (A.map (MulAut.conj (sIncl m)).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj (sIncl m)).injective
  rw [← hcard, ← natCard_fixedSub_conj repP A (sIncl m), ← natCard_fixedSub_conj repQ A (sIncl m)]
  exact fixed_data_with_t ht hcomm' hsq'

theorem fixed_bounds {A : Subgroup H32} (hA0 : A ≠ ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ≤ 4 ∧ Nat.card A * Nat.card (fixedSub repP A) < 64 ∧
      Nat.card A * Nat.card (fixedSub repQ A) < 256 := by
  by_cases hS : A ≤ (sIncl : GL32 →* H32).range
  · rcases fixed_data_le_S hS hA0 hcomm hsq with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      rw [h1, h2, h3] <;> norm_num
  · rcases fixed_data_not_S hS hcomm hsq with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2, h3]
      norm_num
    · refine ⟨by omega, ?_, ?_⟩
      · rw [h1, h2]
        norm_num
      · rw [h1]
        omega

end CFSG.QuasithinUnique.Setup.Family