module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4HPb
public import CFSG.GH74.GLS.Stage2.OddAut.FixStep

public section

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (spScalars)
open scoped MatrixGroups

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

namespace HPSL2

variable {K : Type} [Field K] {e f : Fin 2 ⊕ Fin 2 → K}

@[expose] noncomputable def thLin (e f : Fin 2 ⊕ Fin 2 → K) (g : Matrix (Fin 2) (Fin 2) K) :
    (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
  LinearMap.id + (pairIncl e f).comp ((Matrix.mulVecLin (g - 1)).comp (pairCoord e f))

theorem thLin_apply (e f : Fin 2 ⊕ Fin 2 → K) (g : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 ⊕ Fin 2 → K) :
    thLin e f g v = v + pairIncl e f ((g - 1) *ᵥ pairCoord e f v) := rfl

@[expose] noncomputable def thMat (e f : Fin 2 ⊕ Fin 2 → K) (g : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  LinearMap.toMatrix' (thLin e f g)

theorem thMat_mulVec (e f : Fin 2 ⊕ Fin 2 → K) (g : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 ⊕ Fin 2 → K) : thMat e f g *ᵥ v = thLin e f g v := by
  rw [thMat, LinearMap.toMatrix'_mulVec]

theorem thLin_one (e f v : Fin 2 ⊕ Fin 2 → K) : thLin e f 1 v = v := by
  rw [thLin_apply, sub_self, Matrix.zero_mulVec, map_zero, add_zero]

theorem thLin_mul (hef : spForm 2 K e f = 1) (g g' : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 ⊕ Fin 2 → K) : thLin e f g (thLin e f g' v) = thLin e f (g * g') v := by
  rw [thLin_apply e f g (thLin e f g' v), thLin_apply e f g' v, thLin_apply e f (g * g') v,
    map_add, pairCoord_pairIncl hef, add_assoc, ← map_add]
  congr 2
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_add, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec]
  abel

theorem spForm_thLin (hef : spForm 2 K e f = 1) (g : Matrix (Fin 2) (Fin 2) K)
    (hg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1) (v w : Fin 2 ⊕ Fin 2 → K) :
    spForm 2 K (thLin e f g v) (thLin e f g w) = spForm 2 K v w := by
  rw [thLin_apply, thLin_apply]
  simp only [map_add, LinearMap.add_apply, spForm_pairIncl_right, spForm_pairIncl_left,
    spForm_pairIncl_pairIncl hef]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  linear_combination (pairCoord e f v 0 * pairCoord e f w 1 - pairCoord e f v 1 * pairCoord e f w 0)
    * hg

@[expose] noncomputable def thGL (hef : spForm 2 K e f = 1) (g : SL(2, K)) :
    GL (Fin 2 ⊕ Fin 2) K where
  val := thMat e f (g : Matrix (Fin 2) (Fin 2) K)
  inv := thMat e f ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  val_inv := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, thMat_mulVec, thMat_mulVec, thLin_mul hef,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec, thLin_one]
  inv_val := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, thMat_mulVec, thMat_mulVec, thLin_mul hef,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec, thLin_one]

theorem thGL_mem (hef : spForm 2 K e f = 1) (g : SL(2, K)) : thGL hef g ∈ StatedSp 2 K := by
  rw [mem_statedSp_iff_preserves]
  intro x y
  show spForm 2 K (thMat e f (g : Matrix (Fin 2) (Fin 2) K) *ᵥ x)
    (thMat e f (g : Matrix (Fin 2) (Fin 2) K) *ᵥ y) = _
  rw [thMat_mulVec, thMat_mulVec]
  refine spForm_thLin hef _ ?_ x y
  have := g.det_coe
  rwa [Matrix.det_fin_two] at this

@[expose] noncomputable def thS (hef : spForm 2 K e f = 1) (g : SL(2, K)) : StatedSp 2 K :=
  ⟨thGL hef g, thGL_mem hef g⟩

theorem act_thS (hef : spForm 2 K e f = 1) (g : SL(2, K)) (v : Fin 2 ⊕ Fin 2 → K) :
    act (thS hef g) v = thLin e f (g : Matrix (Fin 2) (Fin 2) K) v :=
  thMat_mulVec e f _ v

@[expose] noncomputable def thHom (hef : spForm 2 K e f = 1) : SL(2, K) →* StatedSp 2 K where
  toFun := thS hef
  map_one' := act_ext fun v => by
    rw [act_thS, act_one, Matrix.SpecialLinearGroup.coe_one, thLin_one]
  map_mul' g g' := act_ext fun v => by
    rw [act_mul, act_thS, act_thS, act_thS, Matrix.SpecialLinearGroup.coe_mul, thLin_mul hef]

theorem act_thHom (hef : spForm 2 K e f = 1) (g : SL(2, K)) (v : Fin 2 ⊕ Fin 2 → K) :
    act (thHom hef g) v = thLin e f (g : Matrix (Fin 2) (Fin 2) K) v :=
  act_thS hef g v

theorem thHom_injective (hef : spForm 2 K e f = 1) : Function.Injective (thHom hef) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ∀ v, thLin e f (g : Matrix (Fin 2) (Fin 2) K) v = v := fun v => by
    rw [← act_thHom hef, hg, act_one]
  have h2 : ∀ x : Fin 2 → K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x := fun x => by
    have h3 := h1 (pairIncl e f x)
    rw [thLin_apply, pairCoord_pairIncl hef, add_eq_left] at h3
    have h4 := congrArg (pairCoord e f) h3
    rw [pairCoord_pairIncl hef, map_zero, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero] at h4
    exact h4
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.ext_iff_mulVec]
  intro x
  rw [h2 x, Matrix.one_mulVec]

theorem thHom_mem_HP {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (H : IsHypFrame P e f) (g : SL(2, K)) :
    thHom H.spForm_e_f g ∈ HP P := by
  intro v hv
  rw [act_thHom, thLin_apply, H.coord_eq_zero hv, Matrix.mulVec_zero, map_zero, add_zero]

@[expose] noncomputable def thHP {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (H : IsHypFrame P e f) :
    SL(2, K) →* HP P :=
  (thHom H.spForm_e_f).codRestrict (HP P) (thHom_mem_HP H)

@[expose] noncomputable def frameMat (e f : Fin 2 ⊕ Fin 2 → K) (h : StatedSp 2 K) :
    Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => pairCoord e f (act h (![e, f] j)) i

theorem frameMat_mulVec (e f : Fin 2 ⊕ Fin 2 → K) (h : StatedSp 2 K) (x : Fin 2 → K) :
    frameMat e f h *ᵥ x = pairCoord e f (act h (pairIncl e f x)) := by
  ext i
  simp only [frameMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, pairIncl_apply,
    act_add, act_smul, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp [mul_comm]

theorem det_frameMat {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (H : IsHypFrame P e f)
    {h : StatedSp 2 K} (hh : h ∈ HP P) : (frameMat e f h).det = 1 := by
  have h1 := H.incl_coord _ (act_mem_HP hh H.mem_e)
  have h2 := H.incl_coord _ (act_mem_HP hh H.mem_f)
  have h3 := spForm_act h e f
  rw [H.spForm_e_f, ← h1, ← h2, spForm_pairIncl_pairIncl H.spForm_e_f] at h3
  rw [Matrix.det_fin_two]
  simp only [frameMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination h3

theorem thHP_surjective {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (H : IsHypFrame P e f) :
    Function.Surjective (thHP H) := by
  rintro ⟨h, hh⟩
  let G : SL(2, K) := ⟨frameMat e f h, det_frameMat H hh⟩
  have hG : (G : Matrix (Fin 2) (Fin 2) K) = frameMat e f h := rfl
  refine ⟨G, Subtype.ext (act_ext fun v => ?_)⟩
  have hfix := hh _ (H.sub_incl_coord_mem_orth v)
  rw [act_sub] at hfix
  have hP := H.incl_coord _ (act_mem_HP hh (H.incl_mem (pairCoord e f v)))
  calc act ((thHP H G : HP P) : StatedSp 2 K) v = thLin e f (G : Matrix (Fin 2) (Fin 2) K) v :=
        act_thHom H.spForm_e_f G v
    _ = act h v := by
      rw [thLin_apply, hG, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, frameMat_mulVec, hP,
        sub_eq_iff_eq_add.mp hfix]
      abel

theorem thHP_bijective {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (H : IsHypFrame P e f) :
    Function.Bijective (thHP H) :=
  ⟨fun _ _ hab => thHom_injective H.spForm_e_f (congrArg Subtype.val hab), thHP_surjective H⟩

end HPSL2

open HPSL2

variable {K : Type} [Field K]

theorem proj_injective_HP {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hP : Module.finrank K P = 2)
    (_hPo : P ⊓ orth P = ⊥) : Function.Injective ((proj 2 K).comp (HP P).subtype) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have h' : (QuotientGroup.mk (h : StatedSp 2 K) : StatedSp 2 K ⧸ spScalars 2 K) = 1 := hh
  have hs : (h : StatedSp 2 K) ∈ spScalars 2 K := (QuotientGroup.eq_one_iff _).mp h'
  rw [spScalars, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hs
  obtain ⟨c, hc⟩ := hs
  have hv : ∀ v : Fin 2 ⊕ Fin 2 → K, act (h : StatedSp 2 K) v = (c : K) • v := by
    intro v
    show mx ((h : StatedSp 2 K) : GL _ K) *ᵥ v = _
    rw [← hc]
    simp only [mx, GeneralLinearGroup.coe_scalar]
    simp [Matrix.scalar_apply]
  have hpos : 0 < Module.finrank K (orth P) := by rw [finrank_orth, hP]; norm_num
  obtain ⟨⟨z, hz⟩, hz0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hz0' : z ≠ 0 := fun h0 => hz0 (Subtype.ext h0)
  have hcz : (c : K) • z = z := by rw [← hv z, h.2 z hz]
  have hc1 : (c : K) = 1 := by
    have : ((c : K) - 1) • z = 0 := by rw [sub_smul, hcz, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz0')
  apply Subtype.ext
  apply act_ext
  intro v
  rw [hv v, hc1, one_smul]
  exact (act_one v).symm

theorem noOddNormal_HP [Finite K]
    (hSL : ∀ N : Subgroup SL(2, K), N.Normal → Odd (Nat.card ↥N) → N = ⊥)
    {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hP : Module.finrank K P = 2) (hPo : P ⊓ orth P = ⊥)
    (r : ℕ) : CFSG.GH74.GLS.Stage2.OddAut.NoOddNormal ((HP P).map (proj 2 K)) r := by
  obtain ⟨e, f, H⟩ := exists_isHypFrame hP hPo
  let φ : SL(2, K) →* StatedProj (StatedSp 2 K) := ((proj 2 K).comp (HP P).subtype).comp (thHP H)
  have hφ : Function.Injective φ := (proj_injective_HP hP hPo).comp (thHP_bijective H).1
  have hrange : φ.range = (HP P).map (proj 2 K) := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(thHP H g : StatedSp 2 K), (thHP H g).2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨g, hg⟩ := (thHP_bijective H).2 ⟨h, hh⟩
      exact ⟨g, by simp [φ, hg]⟩
  rw [← hrange]
  exact CFSG.GH74.GLS.Stage2.OddAut.noOddNormal_of_range φ hφ hSL r

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4
