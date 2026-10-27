module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixPointRadicalCoordinates

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank SymplecticTorusWeyl
open LinearMap (BilinForm)
open scoped Pointwise

theorem tauSym_mul_eq_one_iff {n : ℕ} (B B' : Multiplicative (binarySymMatrices n)) :
    tauSym n B * tauSym n B' = 1 ↔
      (B.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) + (B'.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
        0 := by
  rw [← map_mul, ← map_one (tauSym n), (tauSym_injective (n := n)).eq_iff]
  constructor
  · intro h
    have h' := congrArg (fun C : Multiplicative (binarySymMatrices n) =>
      ((Multiplicative.toAdd C : binarySymMatrices n) : Matrix (Fin n) (Fin n) (ZMod 2))) h
    simpa using h'
  · intro h
    apply Multiplicative.toAdd.injective
    exact Subtype.ext (by simpa using h)

theorem tauSym_mul_eq_iff {n : ℕ} (B₁ B₂ B₃ B₄ : Multiplicative (binarySymMatrices n)) :
    tauSym n B₁ * tauSym n B₂ = tauSym n B₃ * tauSym n B₄ ↔
      (B₁.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) + (B₂.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
        (B₃.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) +
          (B₄.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  rw [← map_mul, ← map_mul, (tauSym_injective (n := n)).eq_iff]
  constructor
  · intro h
    have h' := congrArg (fun C : Multiplicative (binarySymMatrices n) =>
      ((Multiplicative.toAdd C : binarySymMatrices n) : Matrix (Fin n) (Fin n) (ZMod 2))) h
    simpa using h'
  · intro h
    apply Multiplicative.toAdd.injective
    exact Subtype.ext (by simpa using h)

theorem matrix_eq_of_add_eq_zero {n : ℕ} {M N : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : M + N = 0) : N = M := by
  have h2 : M + M = 0 := by
    ext i j
    exact zmod_two_add_self_eq_zero (M i j)
  calc N = (M + M) + N := by rw [h2, zero_add]
    _ = M + (M + N) := by rw [add_assoc]
    _ = M := by rw [h, add_zero]

theorem tauSym_leviSp_sq (S : Multiplicative (binarySymMatrices 3)) (D : GL (Fin 3) (ZMod 2))
    (hD : D * D = 1) :
    (tauSym 3 S * leviSp D) * (tauSym 3 S * leviSp D) =
      tauSym 3 S * tauSym 3 (Multiplicative.ofAdd ⟨(D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (S.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ,
        congr_mem_binarySymMatrices _ _⟩) := by
  rw [← leviSp_mul_tauSym_mul_inv D S]
  have h : leviSp D * leviSp D = 1 := by rw [← map_mul, hD, map_one]
  calc (tauSym 3 S * leviSp D) * (tauSym 3 S * leviSp D)
      = tauSym 3 S * (leviSp D * tauSym 3 S * (leviSp D)⁻¹) * (leviSp D * leviSp D) := by group
    _ = _ := by rw [h, mul_one]

theorem tauSym_leviSp_mul (S S' : Multiplicative (binarySymMatrices 3))
    (D D' : GL (Fin 3) (ZMod 2)) :
    (tauSym 3 S * leviSp D) * (tauSym 3 S' * leviSp D') =
      tauSym 3 S * tauSym 3 (Multiplicative.ofAdd ⟨(D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (S'.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ,
        congr_mem_binarySymMatrices _ _⟩) * (leviSp D * leviSp D') := by
  rw [← leviSp_mul_tauSym_mul_inv D S']
  group

theorem t0Unit_mul_self (a a' : ZMod 2) : t0Unit a a' * t0Unit a a' = 1 :=
  Units.ext (t0Mat_mul_self a a')

theorem t0Unit_mul (a a' c c' : ZMod 2) : t0Unit a a' * t0Unit c c' = t0Unit (a + c) (a' + c') :=
  Units.ext (t0Mat_mul a a' c c')

theorem jMat_of_square_commute (S₁ S₂ : Multiplicative (binarySymMatrices 3))
    (h1 : (tauSym 3 S₁ * leviSp (t0Unit 1 0)) * (tauSym 3 S₁ * leviSp (t0Unit 1 0)) = 1)
    (h2 : (tauSym 3 S₂ * leviSp (t0Unit 0 1)) * (tauSym 3 S₂ * leviSp (t0Unit 0 1)) = 1)
    (h12 : (tauSym 3 S₁ * leviSp (t0Unit 1 0)) * (tauSym 3 S₂ * leviSp (t0Unit 0 1)) =
      (tauSym 3 S₂ * leviSp (t0Unit 0 1)) * (tauSym 3 S₁ * leviSp (t0Unit 1 0))) :
    (S₁.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        jMat ((S₁.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0)
          ((S₁.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1)
          ((S₁.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2) ∧
      (S₂.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        jMat ((S₂.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0)
          ((S₂.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1)
          ((S₂.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2) := by
  have hcomm : t0Unit 1 0 * t0Unit 0 1 = t0Unit 0 1 * t0Unit 1 0 := by
    rw [t0Unit_mul, t0Unit_mul, add_comm (1 : ZMod 2), add_comm (0 : ZMod 2)]
  rw [tauSym_leviSp_sq S₁ _ (t0Unit_mul_self 1 0), tauSym_mul_eq_one_iff, toAdd_ofAdd] at h1
  rw [tauSym_leviSp_sq S₂ _ (t0Unit_mul_self 0 1), tauSym_mul_eq_one_iff, toAdd_ofAdd] at h2
  rw [tauSym_leviSp_mul, tauSym_leviSp_mul, ← map_mul leviSp (t0Unit 1 0) (t0Unit 0 1),
    ← map_mul leviSp (t0Unit 0 1) (t0Unit 1 0), hcomm, mul_left_inj, tauSym_mul_eq_iff,
    toAdd_ofAdd, toAdd_ofAdd] at h12
  simp only [coe_t0Unit] at h1 h2 h12
  have hs₁ : (S₁.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = S₁.toAdd :=
    binarySym_transpose S₁.toAdd
  have hs₂ : (S₂.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = S₂.toAdd :=
    binarySym_transpose S₂.toAdd
  have e₁ := symMat_symCoord hs₁
  have e₂ := symMat_symCoord hs₂
  have key := t0_square_commute_symMat (symCoord (S₁.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (symCoord (S₂.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (by rw [e₁]; exact matrix_eq_of_add_eq_zero h1)
    (by rw [e₂]; exact matrix_eq_of_add_eq_zero h2)
    (by rw [e₁, e₂]; exact h12)
  rw [e₁, e₂] at key
  exact key

theorem eq_tauSym_mul_leviSp {g : StatedSp 3 (ZMod 2)}
    (hg : g ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3)) :
    ∃ S : Multiplicative (binarySymMatrices 3),
      g = tauSym 3 S * leviSp (lagrangianLevi 3 ⟨g, hg⟩) := by
  obtain ⟨C, hC⟩ := exists_eq_leviSp_mul_tauSym_of_mem_stabilizer hg
  refine ⟨Multiplicative.ofAdd ⟨((lagrangianLevi 3 ⟨g, hg⟩ : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) * (C.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((lagrangianLevi 3 ⟨g, hg⟩ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ,
      congr_mem_binarySymMatrices _ _⟩, ?_⟩
  rw [← leviSp_mul_tauSym_mul_inv, inv_mul_cancel_right]
  exact hC

theorem zmod_two_add_add_add_add : ∀ c t t' : ZMod 2, c + t + t' + t + t' = c := by
  decide

abbrev ZetaGroup : Type := ℤˣ

abbrev zeta : ZetaGroup := -1

theorem card_zetaGroup : Nat.card ZetaGroup = 2 :=
  Nat.card_eq_fintype_card.trans Fintype.card_units_int

theorem zeta_ne_one : zeta ≠ 1 := by
  decide

theorem eq_one_or_eq_zeta (z : ZetaGroup) : z = 1 ∨ z = zeta :=
  Int.units_eq_one_or z

section Basis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (hb : b.IsAlt) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

include he in
theorem pointRadical_le_subspaceStabilizer :
    pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) ≤ subspaceStabilizer b (lagrangianOf e) := by
  rintro _ ⟨⟨w, c⟩, rfl⟩
  have hw' : (w : V) ∈ pointSpan e := by
    rw [pointSpan_eq_pairOrth he]
    exact w.2
  rw [mem_subspaceStabilizer_iff_spCoord he]
  exact unipotent_le_stabilizer (spCoord_pointElt_mem_unipotent he hb hw' c)

include he in
theorem pointRadical_le_normalizer :
    pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) ≤
      Subgroup.normalizer
        (pointwiseStabilizer b (lagrangianOf e) : Set (bilinIsometryGroup b)) := by
  rw [normalizer_pointwiseStabilizer_lagrangianOf he]
  exact pointRadical_le_subspaceStabilizer hb he

include he in
theorem mem_pointRadical_of_spCoord_eq {g : bilinIsometryGroup b} {c x x' a a' : ZMod 2}
    (h : spCoord he g = tauSym 3 (Multiplicative.ofAdd ⟨jMat c x x',
      mem_binarySymMatrices.2 (jMat_transpose c x x')⟩) * leviSp (t0Unit a a')) :
    g ∈ pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) := by
  have hw : pointVec e x x' a a' ∈ pointSpan e := pointVec_mem x x' a a'
  obtain ⟨h1, h2, h3, h4⟩ := pointVec_coords (e := e) x x' a a'
  have hn := spCoord_pointElt_eq he hb hw (c + x * a + x' * a')
  have hS : (Multiplicative.ofAdd ⟨jMat (c + x * a + x' * a' +
      e.repr (pointVec e x x' a a') (Sum.inl 1) * e.repr (pointVec e x x' a a') (Sum.inr 1) +
      e.repr (pointVec e x x' a a') (Sum.inl 2) * e.repr (pointVec e x x' a a') (Sum.inr 2))
      (e.repr (pointVec e x x' a a') (Sum.inl 1)) (e.repr (pointVec e x x' a a') (Sum.inl 2)),
      mem_binarySymMatrices.2 (jMat_transpose _ _ _)⟩ : Multiplicative (binarySymMatrices 3)) =
      Multiplicative.ofAdd ⟨jMat c x x', mem_binarySymMatrices.2 (jMat_transpose c x x')⟩ := by
    congr 2
    rw [h1, h2, h3, h4, zmod_two_add_add_add_add]
  rw [hS, h3, h4, ← h] at hn
  rw [← (spCoord he).injective hn]
  exact pointElt_mem_pointRadical hb (mem_pairOrth_of_mem_pointSpan he hw) _

include he in
theorem mem_pointRadical_inf_iff_jMat {g : bilinIsometryGroup b} :
    g ∈ pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) ⊓ pointwiseStabilizer b (lagrangianOf e) ↔
      ∃ c x x' : ZMod 2, LinearMap.toMatrix e e ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) = fromBlocks 1 (jMat c x x') 0 1 := by
  constructor
  · rintro ⟨⟨⟨w, c⟩, rfl⟩, hR⟩
    have hw' : (w : V) ∈ pointSpan e := by
      rw [pointSpan_eq_pairOrth he]
      exact w.2
    obtain ⟨B, hB⟩ := (mem_pointwiseStabilizer_iff_spCoord he _).1 hR
    have hmat := spMatrixOf_spCoord_pointElt he hb hw' c
    rw [← hB, spMatrixOf_tauSym] at hmat
    obtain ⟨h11, -, -, -⟩ := Matrix.fromBlocks_inj.1 hmat
    refine ⟨c, e.repr w (Sum.inl 1), e.repr w (Sum.inl 2), ?_⟩
    change spMatrixOf (spCoord he _) = _
    rw [spMatrixOf_spCoord_pointElt he hb hw' c, ← h11, transpose_one]
  · rintro ⟨c, x, x', h⟩
    have hτ : spCoord he g = tauSym 3 (Multiplicative.ofAdd ⟨jMat c x x',
        mem_binarySymMatrices.2 (jMat_transpose c x x')⟩) := by
      apply statedSp_ext
      change spMatrixOf (spCoord he g) = spMatrixOf (tauSym 3 _)
      rw [spMatrixOf_tauSym, toAdd_ofAdd]
      exact h
    refine ⟨mem_pointRadical_of_spCoord_eq hb he (c := c) (x := x) (x' := x') (a := 0) (a' := 0) ?_,
      (mem_pointwiseStabilizer_iff_spCoord he g).2 ⟨_, hτ.symm⟩⟩
    rw [hτ, show t0Unit 0 0 = 1 from Units.ext t0Mat_zero, map_one, mul_one]

include he in
theorem card_pointRadical_inf :
    Nat.card (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) ⊓
      pointwiseStabilizer b (lagrangianOf e) : Subgroup (bilinIsometryGroup b)) = 8 := by
  set F : ZMod 2 × ZMod 2 × ZMod 2 → bilinIsometryGroup b := fun p => (spCoord he).symm
    (tauSym 3 (Multiplicative.ofAdd ⟨jMat p.1 p.2.1 p.2.2,
      mem_binarySymMatrices.2 (jMat_transpose _ _ _)⟩)) with hF
  have hinj : Function.Injective F := by
    rintro ⟨c, x, x'⟩ ⟨c', y, y'⟩ hp
    have h1 := tauSym_injective ((spCoord he).symm.injective hp)
    have h2 := congrArg (fun C : Multiplicative (binarySymMatrices 3) =>
      ((Multiplicative.toAdd C : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1
    simp only [toAdd_ofAdd] at h2
    obtain ⟨e1, e2, e3⟩ := jMat_injective _ _ _ _ _ _ h2
    rw [e1, e2, e3]
  have hset : ∀ g : bilinIsometryGroup b,
      g ∈ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) ⊓
        pointwiseStabilizer b (lagrangianOf e) : Subgroup (bilinIsometryGroup b)) ↔
          g ∈ Set.range F := by
    intro g
    rw [mem_pointRadical_inf_iff_jMat hb he]
    constructor
    · rintro ⟨c, x, x', h⟩
      refine ⟨(c, x, x'), (MulEquiv.symm_apply_eq _).2 (statedSp_ext ?_)⟩
      change spMatrixOf (tauSym 3 _) = spMatrixOf (spCoord he g)
      rw [spMatrixOf_tauSym, toAdd_ofAdd]
      exact h.symm
    · rintro ⟨⟨c, x, x'⟩, rfl⟩
      refine ⟨c, x, x', ?_⟩
      change spMatrixOf (spCoord he (F (c, x, x'))) = _
      rw [hF, MulEquiv.apply_symm_apply, spMatrixOf_tauSym, toAdd_ofAdd]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset), Nat.card_range_of_injective hinj,
    Nat.card_prod, Nat.card_prod, Nat.card_zmod]

include he in
theorem mem_pointRadical_of_spCoord_eq_tauSym {g : bilinIsometryGroup b}
    {B : Multiplicative (binarySymMatrices 3)} {a a' : ZMod 2}
    (h : spCoord he g = tauSym 3 B * leviSp (t0Unit a a'))
    (hJ : (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      jMat ((B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0)
        ((B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1)
        ((B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2)) :
    g ∈ pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) := by
  have hB : B = Multiplicative.ofAdd ⟨jMat ((B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0)
      ((B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1)
      ((B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2),
      mem_binarySymMatrices.2 (jMat_transpose _ _ _)⟩ :=
    Multiplicative.toAdd.injective (Subtype.ext hJ)
  rw [hB] at h
  exact mem_pointRadical_of_spCoord_eq hb he h

variable (b e) in
@[expose] def lagrangianRadicalProd : Subgroup (bilinIsometryGroup b × ZetaGroup) :=
  (pointwiseStabilizer b (lagrangianOf e)).prod ⊤

variable (e) in
@[expose] def pointRadicalProd : Subgroup (bilinIsometryGroup b × ZetaGroup) :=
  (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))).prod ⊤

variable (e) in
@[expose] def radicalProduct : Subgroup (bilinIsometryGroup b × ZetaGroup) :=
  pointRadicalProd hb e ⊔ lagrangianRadicalProd b e

omit hb in
theorem mem_lagrangianRadicalProd {x : bilinIsometryGroup b × ZetaGroup} :
    x ∈ lagrangianRadicalProd b e ↔ x.1 ∈ pointwiseStabilizer b (lagrangianOf e) := by
  simp [lagrangianRadicalProd, Subgroup.mem_prod]

theorem mem_pointRadicalProd {x : bilinIsometryGroup b × ZetaGroup} :
    x ∈ pointRadicalProd hb e ↔ x.1 ∈ pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) := by
  simp [pointRadicalProd, Subgroup.mem_prod]

include he in
theorem pointRadicalProd_le_normalizer :
    pointRadicalProd hb e ≤ Subgroup.normalizer (lagrangianRadicalProd b e :
      Set (bilinIsometryGroup b × ZetaGroup)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro r
  rw [mem_lagrangianRadicalProd, mem_lagrangianRadicalProd]
  exact Subgroup.mem_normalizer_iff.1
    (pointRadical_le_normalizer hb he ((mem_pointRadicalProd hb).1 hx)) r.1

include he in
theorem radicalProduct_le_normalizer :
    radicalProduct hb e ≤ Subgroup.normalizer (lagrangianRadicalProd b e :
      Set (bilinIsometryGroup b × ZetaGroup)) :=
  sup_le (pointRadicalProd_le_normalizer hb he) Subgroup.le_normalizer

include he in
theorem coe_radicalProduct :
    (radicalProduct hb e : Set (bilinIsometryGroup b × ZetaGroup)) =
      (pointRadicalProd hb e : Set (bilinIsometryGroup b × ZetaGroup)) *
        (lagrangianRadicalProd b e : Set (bilinIsometryGroup b × ZetaGroup)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _ (pointRadicalProd_le_normalizer hb he)

include he in
theorem radicalProduct_le_prod :
    radicalProduct hb e ≤ (subspaceStabilizer b (lagrangianOf e)).prod ⊤ :=
  sup_le (Subgroup.prod_mono (pointRadical_le_subspaceStabilizer hb he) le_rfl)
    (Subgroup.prod_mono (pointwiseStabilizer_le_subspaceStabilizer _) le_rfl)

theorem spCoord_mem_stabilizer_of_mem {x : bilinIsometryGroup b × ZetaGroup}
    (hx : x ∈ radicalProduct hb e) :
    spCoord he x.1 ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3) :=
  (mem_subspaceStabilizer_iff_spCoord he _).1
    (Subgroup.mem_prod.1 (radicalProduct_le_prod hb he hx)).1

@[expose] def thetaHom : radicalProduct hb e →* GL (Fin 3) (ZMod 2) :=
  (lagrangianLevi 3).comp
    (((spCoord he).toMonoidHom.comp
      ((MonoidHom.fst _ _).comp (radicalProduct hb e).subtype)).codRestrict
        _ fun x => spCoord_mem_stabilizer_of_mem hb he x.2)

theorem thetaHom_apply (x : radicalProduct hb e) :
    thetaHom hb he x = lagrangianLevi 3 ⟨spCoord he (x : bilinIsometryGroup b × ZetaGroup).1,
      spCoord_mem_stabilizer_of_mem hb he x.2⟩ :=
  rfl

theorem thetaHom_eq_one_iff (x : radicalProduct hb e) :
    thetaHom hb he x = 1 ↔ (x : bilinIsometryGroup b × ZetaGroup) ∈ lagrangianRadicalProd b e := by
  rw [thetaHom_apply, ← MonoidHom.mem_ker, ker_lagrangianLevi, Subgroup.mem_subgroupOf,
    mem_lagrangianRadicalProd, mem_pointwiseStabilizer_iff_spCoord he]

theorem ker_thetaHom :
    (thetaHom hb he).ker = (lagrangianRadicalProd b e).subgroupOf (radicalProduct hb e) := by
  ext x
  rw [MonoidHom.mem_ker, thetaHom_eq_one_iff, Subgroup.mem_subgroupOf]

theorem thetaHom_mk_pointElt {w : V} (hw : w ∈ pointSpan e) (c : ZMod 2) (z : ZetaGroup)
    (hx : (pointElt hb (mem_pairOrth_left (mem_pairOrth_of_mem_pointSpan he hw)) c, z) ∈
      radicalProduct hb e) :
    thetaHom hb he ⟨_, hx⟩ = t0Unit (e.repr w (Sum.inr 1)) (e.repr w (Sum.inr 2)) :=
  lagrangianLevi_spCoord_pointElt he hb hw c _

theorem range_thetaHom : (thetaHom hb he).range = lagrangianT0 := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hx' : x ∈ (pointRadicalProd hb e : Set (bilinIsometryGroup b × ZetaGroup)) *
        (lagrangianRadicalProd b e : Set (bilinIsometryGroup b × ZetaGroup)) := by
      rw [← coe_radicalProduct hb he]
      exact hx
    obtain ⟨⟨y₁, y₂⟩, hy, r, hr, rfl⟩ := Set.mem_mul.1 hx'
    have hyX : ((y₁, y₂) : bilinIsometryGroup b × ZetaGroup) ∈ radicalProduct hb e :=
      Subgroup.mem_sup_left hy
    have hrX : r ∈ radicalProduct hb e := Subgroup.mem_sup_right hr
    have hsplit : (⟨(y₁, y₂) * r, hx⟩ : radicalProduct hb e) = ⟨(y₁, y₂), hyX⟩ * ⟨r, hrX⟩ :=
      rfl
    rw [hsplit, map_mul, (thetaHom_eq_one_iff hb he ⟨r, hrX⟩).2 hr, mul_one]
    have hy1 : y₁ ∈ pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) :=
      (mem_pointRadicalProd hb).1 hy
    obtain ⟨⟨w, c⟩, rfl⟩ := hy1
    have hw' : (w : V) ∈ pointSpan e := by
      rw [pointSpan_eq_pairOrth he]
      exact w.2
    rw [show thetaHom hb he ⟨_, hyX⟩ = t0Unit (e.repr w (Sum.inr 1)) (e.repr w (Sum.inr 2)) from
      thetaHom_mk_pointElt hb he hw' c y₂ hyX]
    exact ⟨(_, _), rfl⟩
  · rintro _ ⟨⟨a, a'⟩, rfl⟩
    have hw := pointVec_mem (e := e) 0 0 a a'
    obtain ⟨-, -, h3, h4⟩ := pointVec_coords (e := e) 0 0 a a'
    have hx : (pointElt hb (mem_pairOrth_left (mem_pairOrth_of_mem_pointSpan he hw)) 0,
        (1 : ZetaGroup)) ∈ radicalProduct hb e :=
      Subgroup.mem_sup_left ((mem_pointRadicalProd hb).2
        (pointElt_mem_pointRadical hb (mem_pairOrth_of_mem_pointSpan he hw) 0))
    refine ⟨⟨_, hx⟩, ?_⟩
    rw [thetaHom_mk_pointElt hb he hw 0 1 hx, h3, h4]

theorem thetaHom_mem_lagrangianT0 (x : radicalProduct hb e) : thetaHom hb he x ∈ lagrangianT0 := by
  rw [← range_thetaHom hb he]
  exact ⟨x, rfl⟩

theorem toMatrix_conj_thetaHom (x : radicalProduct hb e) {r : bilinIsometryGroup b}
    {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB : Bᵀ = B)
    (hr : LinearMap.toMatrix e e ((r : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) = fromBlocks 1 B 0 1) :
    LinearMap.toMatrix e e (((((x : bilinIsometryGroup b × ZetaGroup).1 * r *
      ((x : bilinIsometryGroup b × ZetaGroup).1)⁻¹ : bilinIsometryGroup b) :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) =
      fromBlocks 1 ((thetaHom hb he x : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B *
        (thetaHom hb he x : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) 0 1 := by
  have hg : (x : bilinIsometryGroup b × ZetaGroup).1 ∈ subspaceStabilizer b (lagrangianOf e) :=
    (Subgroup.mem_prod.1 (radicalProduct_le_prod hb he x.2)).1
  have h := spMatrixOf_spCoord_conj he ⟨_, hg⟩ hr hB
  have hA : LinearMap.toMatrix (lagrangianBasis e) (lagrangianBasis e)
      ((restrictSubspace b (lagrangianOf e) ⟨_, hg⟩ :
        LinearMap.GeneralLinearGroup (ZMod 2) (lagrangianOf e)) :
          lagrangianOf e →ₗ[ZMod 2] lagrangianOf e) =
      (thetaHom hb he x : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [← coe_basisGL, basisGL_restrictSubspace he]
    rfl
  rw [hA] at h
  exact h

include he in
theorem card_pointRadical_eq (hnd : b.Nondegenerate) :
    Nat.card (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) = 32 := by
  rw [card_pointRadical hb (bilin_f_u he), ← pointSpan_eq_pairOrth he, card_pointSpan he hb hnd]

include he in
theorem card_pointRadicalProd (hnd : b.Nondegenerate) : Nat.card (pointRadicalProd hb e) = 64 := by
  rw [pointRadicalProd, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_pointRadical_eq hb he hnd, Subgroup.card_top, card_zetaGroup]

include he in
theorem card_lagrangianRadicalProd : Nat.card (lagrangianRadicalProd b e) = 128 := by
  rw [lagrangianRadicalProd, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_pointwiseStabilizer_lagrangianOf he, Subgroup.card_top, card_zetaGroup]
  norm_num

include he in
theorem card_radicalProduct : Nat.card (radicalProduct hb e) = 512 := by
  have h := (thetaHom hb he).ker.card_mul_index
  have hle : lagrangianRadicalProd b e ≤ radicalProduct hb e := le_sup_right
  rw [Subgroup.index_ker, range_thetaHom, card_lagrangianT0, ker_thetaHom,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_lagrangianRadicalProd he] at h
  rw [← h]

include he in
theorem eq_of_isElementaryAbelian_of_sup_eq (hnd : b.Nondegenerate)
    {Y : Subgroup (bilinIsometryGroup b × ZetaGroup)} (hYX : Y ≤ radicalProduct hb e)
    (hY : IsElementaryAbelian 2 Y) (hYcard : Nat.card Y = 64)
    (hYR : Y ⊔ lagrangianRadicalProd b e = radicalProduct hb e) :
    Y = pointRadicalProd hb e := by
  have : Finite (bilinIsometryGroup b) := Finite.of_equiv _ (spCoord he).symm.toEquiv
  have hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hY.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ Y, x * x = 1 := by
    intro x hx
    have := hY
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Y) x hx
    rwa [sq] at h
  have hcoe : (radicalProduct hb e : Set (bilinIsometryGroup b × ZetaGroup)) =
      (Y : Set (bilinIsometryGroup b × ZetaGroup)) *
        (lagrangianRadicalProd b e : Set (bilinIsometryGroup b × ZetaGroup)) := by
    rw [← hYR]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (hYX.trans (radicalProduct_le_normalizer hb he))
  have hlift : ∀ D ∈ lagrangianT0, ∃ y, ∃ hy : y ∈ Y, thetaHom hb he ⟨y, hYX hy⟩ = D := by
    intro D hD
    rw [← range_thetaHom hb he] at hD
    obtain ⟨⟨x, hx⟩, rfl⟩ := hD
    have hx' : x ∈ (Y : Set (bilinIsometryGroup b × ZetaGroup)) *
        (lagrangianRadicalProd b e : Set (bilinIsometryGroup b × ZetaGroup)) := by
      rw [← hcoe]
      exact hx
    obtain ⟨y, hy, r, hr, rfl⟩ := Set.mem_mul.1 hx'
    have hrX : r ∈ radicalProduct hb e := Subgroup.mem_sup_right hr
    refine ⟨y, hy, ?_⟩
    have hsplit : (⟨y * r, hx⟩ : radicalProduct hb e) = ⟨y, hYX hy⟩ * ⟨r, hrX⟩ := rfl
    rw [hsplit, map_mul, (thetaHom_eq_one_iff hb he ⟨r, hrX⟩).2 hr, mul_one]
  obtain ⟨y₁, hy₁, hθ₁⟩ := hlift (t0Unit 1 0) ⟨(1, 0), rfl⟩
  obtain ⟨y₂, hy₂, hθ₂⟩ := hlift (t0Unit 0 1) ⟨(0, 1), rfl⟩
  have hYRB : ∀ r ∈ Y, r ∈ lagrangianRadicalProd b e → r ∈ pointRadicalProd hb e := by
    intro r hrY hrR
    obtain ⟨B, hB⟩ := (mem_pointwiseStabilizer_iff_spCoord he _).1
      ((mem_lagrangianRadicalProd (e := e)).1 hrR)
    have hr : LinearMap.toMatrix e e ((r.1 : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) = fromBlocks 1 (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1 := by
      change spMatrixOf (spCoord he r.1) = _
      rw [← hB, spMatrixOf_tauSym]
    have hfix : ∀ y (hy : y ∈ Y), (thetaHom hb he ⟨y, hYX hy⟩ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          (thetaHom hb he ⟨y, hYX hy⟩ : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ =
        (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      intro y hy
      have hc : y.1 * r.1 * y.1⁻¹ = r.1 := by
        have h := congrArg Prod.fst (hcomm y hy r hrY)
        change y.1 * r.1 = r.1 * y.1 at h
        rw [h, mul_inv_cancel_right]
      have hmat := toMatrix_conj_thetaHom hb he ⟨y, hYX hy⟩ (binarySym_transpose B.toAdd) hr
      change LinearMap.toMatrix e e (((y.1 * r.1 * y.1⁻¹ : bilinIsometryGroup b) :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) = _ at hmat
      rw [hc, hr] at hmat
      exact ((Matrix.fromBlocks_inj.1 hmat).2.1).symm
    have h1 := hfix y₁ hy₁
    have h2 := hfix y₂ hy₂
    rw [hθ₁, coe_t0Unit] at h1
    rw [hθ₂, coe_t0Unit] at h2
    have e₁ := symMat_symCoord (binarySym_transpose B.toAdd)
    have hJ := (t0_fixed_symMat (symCoord (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)))).1
      ⟨by rw [e₁]; exact h1, by rw [e₁]; exact h2⟩
    rw [e₁] at hJ
    refine (mem_pointRadicalProd hb).2 (mem_pointRadical_of_spCoord_eq_tauSym hb he
      (a := 0) (a' := 0) ?_ hJ)
    rw [← hB, show t0Unit 0 0 = 1 from Units.ext t0Mat_zero, map_one, mul_one]
  have hdecomp : ∀ y (hy : y ∈ Y) (a a' : ZMod 2), thetaHom hb he ⟨y, hYX hy⟩ = t0Unit a a' →
      ∃ S, spCoord he y.1 = tauSym 3 S * leviSp (t0Unit a a') := by
    intro y hy a a' hθ
    obtain ⟨S, hS⟩ := eq_tauSym_mul_leviSp (spCoord_mem_stabilizer_of_mem hb he (hYX hy))
    have hθ' : lagrangianLevi 3 ⟨spCoord he y.1, spCoord_mem_stabilizer_of_mem hb he (hYX hy)⟩ =
        t0Unit a a' := hθ
    rw [hθ'] at hS
    exact ⟨S, hS⟩
  obtain ⟨S₁, hS₁⟩ := hdecomp y₁ hy₁ 1 0 hθ₁
  obtain ⟨S₂, hS₂⟩ := hdecomp y₂ hy₂ 0 1 hθ₂
  have hsq₁ : (tauSym 3 S₁ * leviSp (t0Unit 1 0)) * (tauSym 3 S₁ * leviSp (t0Unit 1 0)) = 1 := by
    rw [← hS₁, ← map_mul]
    have h : y₁.1 * y₁.1 = 1 := congrArg Prod.fst (hsq y₁ hy₁)
    rw [h, map_one]
  have hsq₂ : (tauSym 3 S₂ * leviSp (t0Unit 0 1)) * (tauSym 3 S₂ * leviSp (t0Unit 0 1)) = 1 := by
    rw [← hS₂, ← map_mul]
    have h : y₂.1 * y₂.1 = 1 := congrArg Prod.fst (hsq y₂ hy₂)
    rw [h, map_one]
  have hcomm₁₂ : (tauSym 3 S₁ * leviSp (t0Unit 1 0)) * (tauSym 3 S₂ * leviSp (t0Unit 0 1)) =
      (tauSym 3 S₂ * leviSp (t0Unit 0 1)) * (tauSym 3 S₁ * leviSp (t0Unit 1 0)) := by
    rw [← hS₁, ← hS₂, ← map_mul, ← map_mul]
    exact congrArg (spCoord he) (congrArg Prod.fst (hcomm y₁ hy₁ y₂ hy₂))
  obtain ⟨hJ₁, hJ₂⟩ := jMat_of_square_commute S₁ S₂ hsq₁ hsq₂ hcomm₁₂
  have hy₁B : y₁ ∈ pointRadicalProd hb e :=
    (mem_pointRadicalProd hb).2 (mem_pointRadical_of_spCoord_eq_tauSym hb he hS₁ hJ₁)
  have hy₂B : y₂ ∈ pointRadicalProd hb e :=
    (mem_pointRadicalProd hb).2 (mem_pointRadical_of_spCoord_eq_tauSym hb he hS₂ hJ₂)
  have hle : Y ≤ pointRadicalProd hb e := by
    intro y hy
    have key : ∀ z (hz : z ∈ Y), z ∈ pointRadicalProd hb e →
        thetaHom hb he ⟨z, hYX hz⟩ = thetaHom hb he ⟨y, hYX hy⟩ → y ∈ pointRadicalProd hb e := by
      intro z hz hzB hθz
      have hyz : y * z⁻¹ ∈ Y := mul_mem hy (inv_mem hz)
      have hθyz : thetaHom hb he ⟨y * z⁻¹, hYX hyz⟩ = 1 := by
        have hsplit : (⟨y * z⁻¹, hYX hyz⟩ : radicalProduct hb e) =
            ⟨y, hYX hy⟩ * (⟨z, hYX hz⟩ : radicalProduct hb e)⁻¹ := rfl
        rw [hsplit, map_mul, map_inv, hθz, mul_inv_cancel]
      have hyzB := hYRB _ hyz ((thetaHom_eq_one_iff hb he _).1 hθyz)
      have h' : y = (y * z⁻¹) * z := by group
      rw [h']
      exact mul_mem hyzB hzB
    obtain ⟨⟨a, a'⟩, hθ⟩ := thetaHom_mem_lagrangianT0 hb he ⟨y, hYX hy⟩
    fin_cases a <;> fin_cases a'
    · refine key 1 (one_mem _) (one_mem _) ?_
      rw [show (⟨1, hYX (one_mem Y)⟩ : radicalProduct hb e) = 1 from rfl, map_one, ← hθ]
      exact Units.ext t0Mat_zero.symm
    · exact key y₂ hy₂ hy₂B (hθ₂.trans hθ)
    · exact key y₁ hy₁ hy₁B (hθ₁.trans hθ)
    · refine key (y₁ * y₂) (mul_mem hy₁ hy₂) (mul_mem hy₁B hy₂B) ?_
      have hsplit : (⟨y₁ * y₂, hYX (mul_mem hy₁ hy₂)⟩ : radicalProduct hb e) =
          ⟨y₁, hYX hy₁⟩ * ⟨y₂, hYX hy₂⟩ := rfl
      rw [hsplit, map_mul, hθ₁, hθ₂, t0Unit_mul, add_zero, zero_add]
      exact hθ
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_pointRadicalProd hb he hnd, hYcard])

end Basis

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
