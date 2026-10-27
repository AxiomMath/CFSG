module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Ext
public import CFSG.GH74.Generic.BProg.B2.GenLocDiag
public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Subgroup Matrix

namespace GenLocL4Inner

variable {F : Type} [Field F]

theorem proportional_of_slConjugation_eq {u v : GL (Fin 4) F}
    (h : CatalogueBHigherLinearAction.slConjugation 4 F u =
      CatalogueBHigherLinearAction.slConjugation 4 F v) :
    ∃ l : F, l ≠ 0 ∧ (u : Matrix (Fin 4) (Fin 4) F) = l • (v : Matrix (Fin 4) (Fin 4) F) := by
  have hw : CatalogueBHigherLinearAction.slConjugation 4 F (v⁻¹ * u) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨l, hl⟩ := GenLocL4Ext.exists_scalar_of_commute_sl (n := 4)
    (M := ((v⁻¹ * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) (fun g => by
      have h1 := congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F) =>
        ((φ g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hw
      simp only [LinearFlag.coe_slConjugation, MulAut.one_apply] at h1
      calc (g : Matrix (Fin 4) (Fin 4) F) * ((v⁻¹ * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
          = (((v⁻¹ * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
              (((v⁻¹ * u)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) *
              ((v⁻¹ * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by rw [h1]
        _ = ((v⁻¹ * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) := by
            simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one])
  have hu : (u : Matrix (Fin 4) (Fin 4) F) = l • (v : Matrix (Fin 4) (Fin 4) F) := by
    have h2 : (u : Matrix (Fin 4) (Fin 4) F) =
        (v : Matrix (Fin 4) (Fin 4) F) * ((v⁻¹ * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
      rw [← Units.val_mul, mul_inv_cancel_left]
    rw [h2, hl, Matrix.mul_smul, Matrix.mul_one]
  refine ⟨l, fun h0 => ?_, hu⟩
  have h3 := u.mul_inv
  rw [hu, h0, zero_smul, zero_mul] at h3
  exact zero_ne_one h3

theorem eq_one_or_neg_one_of_det_eq {u v : GL (Fin 4) F} {l : F} (hneg : ¬ IsSquare (-1 : F))
    (hdet : (u : Matrix (Fin 4) (Fin 4) F).det = (v : Matrix (Fin 4) (Fin 4) F).det)
    (h : (u : Matrix (Fin 4) (Fin 4) F) = l • (v : Matrix (Fin 4) (Fin 4) F)) : l = 1 ∨ l = -1 := by
  have hv : (v : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 v.isUnit).ne_zero
  have h1 : (v : Matrix (Fin 4) (Fin 4) F).det = l ^ 4 * (v : Matrix (Fin 4) (Fin 4) F).det := by
    conv_lhs => rw [← hdet, h, Matrix.det_smul, Fintype.card_fin]
  have h4 : l ^ 4 = 1 := by
    have h2 : (l ^ 4 - 1) * (v : Matrix (Fin 4) (Fin 4) F).det = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hv
  have h5 : (l ^ 2 - 1) * (l ^ 2 + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.1 h5 with h6 | h6
  · have h7 : (l - 1) * (l + 1) = 0 := by linear_combination h6
    rcases mul_eq_zero.1 h7 with h8 | h8
    · exact Or.inl (sub_eq_zero.1 h8)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h8)
  · exact absurd ⟨l, by linear_combination -h6⟩ hneg

theorem comm_or_anticomm (hneg : ¬ IsSquare (-1 : F)) {A : Type} [Group A]
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (ρ : A → GL (Fin 4) F)
    (hρ : ∀ (a : A) (g : Matrix.SpecialLinearGroup (Fin 4) F),
      ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (ρ a : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((ρ a)⁻¹ : GL (Fin 4) F))
    (a b : A) (hab : α a * α b = α b * α a) :
    ρ a * ρ b = ρ b * ρ a ∨
      (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ b : Matrix (Fin 4) (Fin 4) F) =
        -((ρ b : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F)) := by
  obtain ⟨l, -, hl⟩ := proportional_of_slConjugation_eq (u := ρ a * ρ b) (v := ρ b * ρ a) (by
    rw [map_mul, map_mul, ← GenLocL4Ext.alpha_eq α ρ hρ a, ← GenLocL4Ext.alpha_eq α ρ hρ b, hab])
  have hdet : ((ρ a * ρ b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det =
      ((ρ b * ρ a : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm]
  rcases eq_one_or_neg_one_of_det_eq hneg hdet hl with h | h
  · left
    apply Units.ext
    rw [hl, h, one_smul]
  · right
    rw [Units.val_mul, Units.val_mul] at hl
    rw [hl, h, neg_smul, one_smul]

section Transfer

variable {J : Type} [Group J]

theorem gammaAct_eq_of_range_eq {A A' : Type} [Group A] [Group A'] [Finite A] [Finite A']
    (hA : CFSG.IsElementaryAbelian 2 A) (hA' : CFSG.IsElementaryAbelian 2 A')
    (α : A →* MulAut J) (α' : A' →* MulAut J) (h : α.range = α'.range) :
    gammaAct α = gammaAct α' := by
  have h1 : gammaAct α = gammaAct α.range.subtype := by
    have := GenLocBasic.gammaAct_comp_surj hA α.range.subtype α.rangeRestrict
      α.rangeRestrict_surjective
    rwa [show α.range.subtype.comp α.rangeRestrict = α from MonoidHom.ext fun _ => rfl] at this
  have h2 : gammaAct α' = gammaAct α'.range.subtype := by
    have := GenLocBasic.gammaAct_comp_surj hA' α'.range.subtype α'.rangeRestrict
      α'.rangeRestrict_surjective
    rwa [show α'.range.subtype.comp α'.rangeRestrict = α' from MonoidHom.ext fun _ => rfl] at this
  have h3 : ∀ D D' : Subgroup (MulAut J), D = D' → gammaAct D.subtype = gammaAct D'.subtype := by
    rintro D D' rfl
    rfl
  rw [h1, h2, h3 _ _ h]

theorem gammaAct_eq_top_of_conj {A : Type} [Group A] (α : A →* MulAut J) (β : MulAut J)
    (h : gammaAct ((MulAut.conj β).toMonoidHom.comp α) = ⊤) : gammaAct α = ⊤ := by
  let α' : A →* MulAut J := (MulAut.conj β).toMonoidHom.comp α
  have hc : ∀ a x, α' a (β x) = β (α a x) := by
    intro a x
    change (β * α a * β⁻¹) (β x) = β (α a x)
    simp
  have h2 := GenLocBasic.gammaAct_map_equiv (β : J ≃* J) α α' hc
  have h4 : (gammaAct α).map (β : J ≃* J).toMonoidHom = ⊤ := h2.symm.trans h
  have h5 := Subgroup.comap_map_eq_self_of_injective (f := (β : J ≃* J).toMonoidHom)
    (β : J ≃* J).injective (gammaAct α)
  rw [h4, Subgroup.comap_top] at h5
  exact h5.symm

theorem gammaAct_eq_top_of_range_conj {A A' : Type} [Group A] [Group A'] [Finite A] [Finite A']
    (hA : CFSG.IsElementaryAbelian 2 A) (hA' : CFSG.IsElementaryAbelian 2 A')
    (α : A →* MulAut J) (α' : A' →* MulAut J) (β : MulAut J)
    (h : α'.range = α.range.map (MulAut.conj β).toMonoidHom) (htop : gammaAct α' = ⊤) :
    gammaAct α = ⊤ := by
  refine gammaAct_eq_top_of_conj α β ?_
  rw [gammaAct_eq_of_range_eq hA hA' _ α' (by rw [MonoidHom.range_comp, h])]
  exact htop

end Transfer

section Diagonal

theorem exists_unit_smul (u : GL (Fin 4) F) {μ : F} (hμ : μ ≠ 0) :
    ∃ u' : GL (Fin 4) F, (u' : Matrix (Fin 4) (Fin 4) F) = μ • (u : Matrix (Fin 4) (Fin 4) F) := by
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 μ hμ) * u, ?_⟩
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]
  rfl

theorem gammaAct_of_commuting_squares [Finite F] (hF : ringChar F ≠ 2) {A : Type} [Group A] [Finite A]
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (ρ : A → GL (Fin 4) F)
    (hρ : ∀ (a : A) (g : Matrix.SpecialLinearGroup (Fin 4) F),
      ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (ρ a : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((ρ a)⁻¹ : GL (Fin 4) F))
    (hab : ∀ a b, ρ a * ρ b = ρ b * ρ a)
    (hsq : ∀ a, ∃ μ : F, μ ≠ 0 ∧ (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F) =
      (μ * μ) • (1 : Matrix (Fin 4) (Fin 4) F)) : gammaAct α = ⊤ := by
  choose μ hμ0 hμ using hsq
  choose ρ' hρ' using fun a => exists_unit_smul (ρ a) (inv_ne_zero (hμ0 a))
  have hα : ∀ a, α a = CatalogueBHigherLinearAction.slConjugation 4 F (ρ' a) := fun a => by
    rw [GenLocL4Ext.alpha_eq α ρ hρ a]
    exact GenLocL4Ext.slConjugation_congr (ρ a) (ρ' a) (hμ0 a)
      (by rw [hρ' a, smul_smul, mul_inv_cancel₀ (hμ0 a), one_smul])
  have hsq' : ∀ a, ρ' a * ρ' a = 1 := fun a => by
    apply Units.ext
    rw [Units.val_mul, hρ' a, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hμ a, smul_smul,
      show (μ a)⁻¹ * (μ a)⁻¹ * (μ a * μ a) = 1 by have := hμ0 a; field_simp, one_smul]
    rfl
  have hcomm' : ∀ a b, ρ' a * ρ' b = ρ' b * ρ' a := fun a b => by
    apply Units.ext
    have h1 := congrArg Units.val (hab a b)
    rw [Units.val_mul, Units.val_mul] at h1
    rw [Units.val_mul, Units.val_mul, hρ' a, hρ' b, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, smul_smul, mul_comm (μ a)⁻¹, h1]
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Subgroup (GL (Fin 4) F), S₀ = Subgroup.closure (Set.range ρ') := ⟨_, rfl⟩
  have hρ'mem : ∀ a, ρ' a ∈ S₀ := fun a => hS₀ ▸ Subgroup.subset_closure ⟨a, rfl⟩
  have hcomm₀ : ∀ x ∈ S₀, ∀ y ∈ S₀, x * y = y * x := by
    have h1 : S₀ ≤ Subgroup.centralizer (Set.range ρ' : Set (GL (Fin 4) F)) := by
      rw [hS₀, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, rfl⟩
      exact hcomm' b a
    have h2 : S₀ ≤ Subgroup.centralizer (S₀ : Set (GL (Fin 4) F)) := by
      conv_lhs => rw [hS₀]
      rw [Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.1 (h1 hy) (ρ' a) ⟨a, rfl⟩).symm
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y hy).symm
  have hsq₀ : ∀ x ∈ S₀, x * x = 1 := by
    intro x hx
    rw [hS₀] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        exact hsq' a
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
        have hxS : x ∈ S₀ := hS₀ ▸ hx
        have hyS : y ∈ S₀ := hS₀ ▸ hy
        calc x * y * (x * y) = x * (y * x) * y := by rw [mul_assoc, mul_assoc, ← mul_assoc y]
          _ = x * (x * y) * y := by rw [hcomm₀ y hyS x hxS]
          _ = (x * x) * (y * y) := by simp only [mul_assoc]
          _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x hx ihx => rw [← _root_.mul_inv_rev, ihx, inv_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime (F := F)
    (n := 4) (p := 2) ⟨-1, IsPrimitiveRoot.neg_one (ringChar F) hF⟩ S₀ hcomm₀
    (fun x hx => by rw [pow_two]; exact hsq₀ x hx)
  let c : GL (Fin 4) F →* GL (Fin 4) F := (MulAut.conj g).toMonoidHom
  have hc : ∀ x, c x = g * x * g⁻¹ := fun x => rfl
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Subgroup (GL (Fin 4) F), S₁ = S₀.map c := ⟨_, rfl⟩
  have hS₁mem : ∀ s ∈ S₁, ∃ x ∈ S₀, c x = s := fun s hs => by
    rw [hS₁] at hs
    exact hs
  have hA₁ : CFSG.IsElementaryAbelian 2 ↥S₁ := by
    refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
    · obtain ⟨x, hx, rfl⟩ := hS₁mem u hu
      obtain ⟨y, hy, rfl⟩ := hS₁mem v hv
      rw [← map_mul, ← map_mul, hcomm₀ x hx y hy]
    · obtain ⟨x, hx, rfl⟩ := hS₁mem u hu
      rw [← map_mul, hsq₀ x hx, map_one]
  let ρ₁ : ↥S₁ →* GL (Fin 4) F := S₁.subtype
  let α₁ : ↥S₁ →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F) :=
    (CatalogueBHigherLinearAction.slConjugation 4 F).comp ρ₁
  have htop : gammaAct α₁ = ⊤ := by
    refine gammaAct_sl_of_diag hA₁ α₁ ρ₁ (fun s => ?_) (fun s => ?_)
      (fun s h => LinearFlag.coe_slConjugation (ρ₁ s) h)
    · obtain ⟨x, hx, hxs⟩ := hS₁mem s s.2
      intro i j hij
      have := hg x hx i j hij
      rw [show ((ρ₁ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((g * x * g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) by
          rw [← hc, hxs]; rfl]
      exact this
    · obtain ⟨x, hx, hxs⟩ := hS₁mem s s.2
      have h1 : (s : GL (Fin 4) F) * s = 1 := by
        rw [← hxs, ← map_mul, hsq₀ x hx, map_one]
      exact h1
  refine gammaAct_eq_top_of_range_conj hA hA₁ α α₁
    (CatalogueBHigherLinearAction.slConjugation 4 F g) ?_ htop
  have hconj : ∀ x : GL (Fin 4) F, CatalogueBHigherLinearAction.slConjugation 4 F (c x) =
      CatalogueBHigherLinearAction.slConjugation 4 F g *
        CatalogueBHigherLinearAction.slConjugation 4 F x *
          (CatalogueBHigherLinearAction.slConjugation 4 F g)⁻¹ := fun x => by
    rw [hc, map_mul, map_mul, map_inv]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨s, rfl⟩
    obtain ⟨x, hx, hxs⟩ := hS₁mem s s.2
    have hxr : CatalogueBHigherLinearAction.slConjugation 4 F x ∈ α.range := by
      have : S₀ ≤ α.range.comap (CatalogueBHigherLinearAction.slConjugation 4 F) := by
        rw [hS₀, Subgroup.closure_le]
        rintro _ ⟨a, rfl⟩
        exact ⟨a, hα a⟩
      exact this hx
    refine ⟨_, hxr, ?_⟩
    change (CatalogueBHigherLinearAction.slConjugation 4 F g) *
      CatalogueBHigherLinearAction.slConjugation 4 F x *
        (CatalogueBHigherLinearAction.slConjugation 4 F g)⁻¹ = CatalogueBHigherLinearAction.slConjugation 4 F (s : GL (Fin 4) F)
    rw [← hxs, hconj]
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    have hmem : c (ρ' a) ∈ S₁ := by
      rw [hS₁]
      exact Subgroup.mem_map_of_mem _ (hρ'mem a)
    refine ⟨⟨c (ρ' a), hmem⟩, ?_⟩
    change CatalogueBHigherLinearAction.slConjugation 4 F (c (ρ' a)) = _
    rw [hconj, hα a]
    rfl

end Diagonal

section Inner

@[expose] def Sl4QuatStmt (F : Type) [Field F] [Finite F] : Prop :=
  ringChar F ≠ 2 → Nat.card F % 4 = 3 → 7 ≤ Nat.card F →
    ∀ {A : Type} [Group A] [Finite A] (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)),
      IsRank23 A →
      (∀ c : A, ∃ x : GL (Fin 4) F, ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        ((α c g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
            ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) →
      SectionalTwoRankLE ↥(innJoin α) 4 →
      ∀ (x y : GL (Fin 4) F) (a b : A),
        (∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
          ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
            (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
              ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) →
        (∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
          ((α b g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
            (y : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
              ((y⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) →
        (x * y : Matrix (Fin 4) (Fin 4) F) = -(y * x : Matrix (Fin 4) (Fin 4) F) →
        gammaAct α = ⊤

theorem not_isSquare_neg_one [Finite F] (hF4 : Nat.card F % 4 = 3) : ¬ IsSquare (-1 : F) := by
  have := Fintype.ofFinite F
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF4]
  simp

theorem gammaAct_sl4_inner_of_quat [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3)
    (h7 : 7 ≤ Nat.card F) (hQuat : Sl4QuatStmt F) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A)
    (hinner : ∀ c : A, ∃ x : GL (Fin 4) F, ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α c g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) : gammaAct α = ⊤ := by
  choose ρ hρ using hinner
  have hneg := not_isSquare_neg_one hF4
  have hEA := hA.1
  have hcomm_aut : ∀ a b : A, α a * α b = α b * α a := fun a b => by
    rw [← map_mul, ← map_mul, mul_comm' a b]
  by_cases hanti : ∃ a b : A, (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ b : Matrix (Fin 4) (Fin 4) F) =
      -((ρ b : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F))
  · obtain ⟨a, b, hab⟩ := hanti
    exact hQuat hF hF4 h7 α hA (fun c => ⟨ρ c, hρ c⟩) hsect (ρ a) (ρ b) a b (hρ a) (hρ b) hab
  · push Not at hanti
    have hab : ∀ a b, ρ a * ρ b = ρ b * ρ a := fun a b =>
      (comm_or_anticomm hneg α ρ hρ a b (hcomm_aut a b)).resolve_right (hanti a b)
    by_cases hall : ∀ a, ∃ μ : F, μ ≠ 0 ∧
        (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F) =
          (μ * μ) • (1 : Matrix (Fin 4) (Fin 4) F)
    · exact gammaAct_of_commuting_squares hF hEA α ρ hρ hab hall
    · push Not at hall
      obtain ⟨a₀, ha₀⟩ := hall
      obtain ⟨l, hl0, hl⟩ := GenLocL4Ext.rho_sq_scalar α ρ hEA hρ a₀
      have hlns : ¬ IsSquare l := by
        rintro ⟨μ, hμ⟩
        have hμ0 : μ ≠ 0 := fun h => hl0 (by rw [hμ, h, mul_zero])
        exact ha₀ μ hμ0 (by rw [hl, hμ])
      exact gammaAct_sl4_ext_odd hF α hA ρ hρ hab a₀ l hlns (by
        rw [Units.val_mul, hl, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal])

end Inner

end GenLocL4Inner

end CFSG.GH74.Generic.BProg.B2
