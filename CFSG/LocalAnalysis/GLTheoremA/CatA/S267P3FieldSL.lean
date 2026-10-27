module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FieldModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Field
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Glue
import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Field

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3 CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin
open CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj proj_surjective fieldAut
  fieldAut_proj conjAut conjAut_proj coe_slConjugation linearAutGroup scalars scalars_eq_center
  conjAut_mem_linearAutGroup)

section Fix

variable {K : Type} [Field K]

theorem c3Mat_rel : (c3Mat : Matrix (Fin 2) (Fin 2) K) * c3Mat + c3Mat + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c3Mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem map_c3 (f : K →+* K) :
    Matrix.SpecialLinearGroup.map f (c3 : SpecialLinearGroup (Fin 2) K) = c3 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_c3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c3Mat]

@[expose] noncomputable def dg (x : K) (hx : x ≠ 0) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![x, 0; 0, x⁻¹], by rw [Matrix.det_fin_two_of]; simp [hx]⟩

theorem exists_apply_ne {σ : K ≃+* K} (hσ : σ ≠ 1) : ∃ x : K, σ x ≠ x := by
  by_contra h
  push Not at h
  exact hσ (RingEquiv.ext h)

theorem ne_zero_and_sq_ne_one {σ : K ≃+* K} {x : K} (hx : σ x ≠ x) : x ≠ 0 ∧ x ^ 2 ≠ 1 := by
  refine ⟨fun h => hx (by rw [h, map_zero]), fun h => hx ?_⟩
  have h1 : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · rw [sub_eq_zero.1 h2, map_one]
  · rw [eq_neg_of_add_eq_zero_left h2, map_neg, map_one]

end Fix

section Data

variable {K : Type} [Field K] (μ : Type) [Fintype μ] [DecidableEq μ]

@[expose] noncomputable def slData (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (x : K) (hx : σ x ≠ x) :
    FieldData K μ where
  G2 := ⊤
  Gl := ⊤
  Gt := ⊤
  blk_top _ _ _ _ := Subgroup.mem_top _
  blk_lam _ _ := Subgroup.mem_top _
  top_inv _ _ := Subgroup.mem_top _
  c := c3
  c_mem := Subgroup.mem_top _
  c_rel := by rw [coe_c3]; exact c3Mat_rel
  c_ne := by rw [coe_c3]; simp [c3Mat]
  x := x
  w := dg x (ne_zero_and_sq_ne_one hx).1
  w_mem := Subgroup.mem_top _
  coe_w := rfl
  x_sq := (ne_zero_and_sq_ne_one hx).2
  negOne_mem := Subgroup.mem_top _
  σ := σ
  σ_cube := hσ3
  σ_x := hx
  map_Gt _ _ := Subgroup.mem_top _
  map_c := map_c3 _

variable {μ} {σ : K ≃+* K} {hσ3 : σ ^ 3 = 1} {x : K} {hx : σ x ≠ x}

theorem FieldData.hZ3_of_card {μ : Type} [Fintype μ] [DecidableEq μ] (D : FieldData K μ)
    (hN : ¬ 3 ∣ Fintype.card (Kap μ)) : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  have hc : (z : SpecialLinearGroup (Kap μ) K) ∈ Subgroup.center _ := Subgroup.mem_subgroupOf.1 hz
  obtain ⟨r, hr1, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hr3 : r ^ 3 = 1 := by
    have := congrArg (fun g : ↥D.Gt =>
      ((g : SpecialLinearGroup (Kap μ) K) : Matrix (Kap μ) (Kap μ) K) (Sum.inl 0) (Sum.inl 0)) hz3
    simp only [Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow, ← hr, Subgroup.coe_one,
      Matrix.SpecialLinearGroup.coe_one] at this
    simpa [scalar_apply, diagonal_pow] using this
  have hg : Nat.gcd (Fintype.card (Kap μ)) 3 = 1 :=
    (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN))
  have hr' : r = 1 := by
    have := pow_gcd_eq_one.2 ⟨hr1, hr3⟩
    rwa [hg, pow_one] at this
  apply Subtype.ext
  apply Subtype.ext
  change (z : SpecialLinearGroup (Kap μ) K).1 = 1
  rw [← hr, hr', map_one]

end Data

section Layer

variable {K : Type} [Field K] [Finite K]

abbrev fixField (σ : K ≃+* K) : Subfield K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)

theorem ringChar_le_card_fixField (σ : K ≃+* K) : ringChar K ≤ Nat.card (fixField σ) := by
  classical
  have hp := CharP.prime_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  set f := ZMod.castHom (dvd_refl (ringChar K)) K with hf
  have hfix : ∀ a, σ (f a) = f a := fun a => by
    have := RingHom.ext_zmod (σ.toRingHom.comp f) f
    exact congrArg (fun g : ZMod (ringChar K) →+* K => g a) this
  let g : ZMod (ringChar K) → fixField σ := fun a => ⟨f a, hfix a⟩
  have hg : Function.Injective g := fun a b h =>
    ZMod.castHom_injective K (congrArg Subtype.val h)
  calc ringChar K = Nat.card (ZMod (ringChar K)) := (Nat.card_zmod _).symm
    _ ≤ Nat.card (fixField σ) := Nat.card_le_card_of_injective g hg

theorem exists_sl_map_eq {ι : Type} [Fintype ι] [DecidableEq ι] (E : Subfield K)
    (B : SpecialLinearGroup ι K) (h : ∀ i j, (B : Matrix ι ι K) i j ∈ E) :
    ∃ B' : SpecialLinearGroup ι E, Matrix.SpecialLinearGroup.map E.subtype B' = B := by
  let M : Matrix ι ι E := Matrix.of fun i j => ⟨(B : Matrix ι ι K) i j, h i j⟩
  have hM : E.subtype.mapMatrix M = B := by
    ext i j
    rfl
  have hdet : M.det = 1 := by
    apply Subtype.val_injective
    change E.subtype M.det = E.subtype 1
    rw [RingHom.map_det, hM, B.2, map_one]
  exact ⟨⟨M, hdet⟩, Subtype.ext hM⟩

variable {μ : Type} [Fintype μ] [DecidableEq μ]

theorem FieldData.layer_of_Gl_eq_top (D : FieldData K μ) (hGl : D.Gl = ⊤) (hK : 5 ≤ ringChar K) :
    GLAPLayer 3 D.Glσ ≠ ⊥ := by
  set σ := D.σ with hσdef
  set E := fixField σ with hE
  set φ : SpecialLinearGroup (Lam μ) E →* ↥D.Gl :=
    (Matrix.SpecialLinearGroup.map E.subtype).codRestrict D.Gl fun _ => hGl ▸ Subgroup.mem_top _
    with hφ
  have hφinj : Function.Injective φ := by
    intro a b h
    have h' := congrArg (fun g : ↥D.Gl =>
      ((g : SpecialLinearGroup (Lam μ) K) : Matrix (Lam μ) (Lam μ) K)) h
    apply Subtype.ext
    ext i j
    exact congrFun (congrFun h' i) j
  have hrange : φ.range = D.Glσ := by
    ext Y
    constructor
    · rintro ⟨Y', rfl⟩
      rw [D.mem_Glσ]
      apply Subtype.ext
      ext i j
      exact ((Y' : Matrix (Lam μ) (Lam μ) E) i j).2
    · intro hY
      rw [D.mem_Glσ] at hY
      have hent : ∀ i j, ((Y : SpecialLinearGroup (Lam μ) K) : Matrix (Lam μ) (Lam μ) K) i j ∈ E :=
        fun i j => by
          have h := congrArg (fun g : SpecialLinearGroup (Lam μ) K =>
            (g : Matrix (Lam μ) (Lam μ) K) i j) hY
          exact h
      obtain ⟨Y', hY'⟩ := exists_sl_map_eq E _ hent
      exact ⟨Y', Subtype.ext hY'⟩
  have hE4 : 4 ≤ Nat.card E := by
    have := ringChar_le_card_fixField σ
    rw [← hE] at this
    omega
  have hq0 : CFSG.IsQuasisimple (SpecialLinearGroup (Fin (Fintype.card (Lam μ))) E) :=
    CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (by simp [Lam]) hE4
  have hq1 : CFSG.IsQuasisimple (SpecialLinearGroup (Lam μ) E) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (CFSG.RankThree.PartTwo.Census.slReindex E (Fintype.equivFin (Lam μ))).symm hq0
  have hq : CFSG.IsQuasisimple ↥D.Glσ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hrange)) hq1
  have hmem : (⟨blk μ (c3, 1), hGl ▸ Subgroup.mem_top _⟩ : ↥D.Gl) ∈ D.Glσ := by
    rw [D.mem_Glσ]
    change Matrix.SpecialLinearGroup.map (σ : K →+* K) (blk μ (c3, 1)) = blk μ (c3, 1)
    rw [FieldData.map_blk, map_c3, map_one]
  set g₀ : ↥D.Glσ := ⟨_, hmem⟩ with hg₀
  have hg₀3 : g₀ ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change blk μ (c3, 1) ^ 3 = 1
    rw [← map_pow, Prod.pow_mk, c3_pow_three, one_pow, blk_one_one]
  have hg₀1 : g₀ ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : ↥D.Glσ => ((g : ↥D.Gl) : SpecialLinearGroup (Lam μ) K)) h
    change blk μ (c3, 1) = 1 at h1
    exact c3_ne_one (congrArg Prod.fst (blk_injective (h1.trans (map_one _).symm)))
  have h3 : 3 ∣ Nat.card ↥D.Glσ := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← orderOf_eq_prime hg₀3 hg₀1]
    exact orderOf_dvd_natCard g₀
  exact CFSG.LocalAnalysis.GLTheoremA.glaPLayer_ne_bot_of_block Nat.prime_three le_rfl hq
    (fun g hg f hf => mul_mem (mul_mem hg hf) (inv_mem hg)) h3

end Layer

section Iso

variable {K : Type} [Field K] {μ : Type} [Fintype μ] [DecidableEq μ]

@[expose] noncomputable def slTopEquiv (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (x : K) (hx : σ x ≠ x)
    {n : ℕ} (eι : Kap μ ≃ Fin n) :
    ↥(slData μ σ hσ3 x hx).Gt ≃* SpecialLinearGroup (Fin n) K :=
  Subgroup.topEquiv.trans (CFSG.RankThree.PartTwo.Census.slReindex K eι)

variable {σ : K ≃+* K} {hσ3 : σ ^ 3 = 1} {x : K} {hx : σ x ≠ x} {n : ℕ}

theorem slData_Zt_eq : (slData μ σ hσ3 x hx).Zt = Subgroup.center ↥(slData μ σ hσ3 x hx).Gt := by
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    exact Subtype.ext (h g)
  · intro h g
    exact congrArg Subtype.val (h ⟨g, Subgroup.mem_top g⟩)

theorem map_Zt_slTopEquiv (eι : Kap μ ≃ Fin n) :
    (slData μ σ hσ3 x hx).Zt.map (slTopEquiv σ hσ3 x hx eι).toMonoidHom = scalars n K := by
  rw [scalars_eq_center, slData_Zt_eq]
  exact Subgroup.map_center_eq (slTopEquiv σ hσ3 x hx eι)

@[expose] noncomputable def slXEquiv (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (x : K) (hx : σ x ≠ x)
    (eι : Kap μ ≃ Fin n) : (slData μ σ hσ3 x hx).XD ≃* projectiveSL n K :=
  QuotientGroup.congr _ _ (slTopEquiv σ hσ3 x hx eι) (map_Zt_slTopEquiv eι)

theorem slXEquiv_mk (eι : Kap μ ≃ Fin n) (g : ↥(slData μ σ hσ3 x hx).Gt) :
    slXEquiv σ hσ3 x hx eι ((slData μ σ hσ3 x hx).πD g) = proj n K (slTopEquiv σ hσ3 x hx eι g) :=
  QuotientGroup.congr_mk' _ _ _ (map_Zt_slTopEquiv eι) g

theorem slTopEquiv_σt (eι : Kap μ ≃ Fin n) (g : ↥(slData μ σ hσ3 x hx).Gt) :
    slTopEquiv σ hσ3 x hx eι ((slData μ σ hσ3 x hx).σt g) =
      Matrix.SpecialLinearGroup.map (σ : K →+* K) (slTopEquiv σ hσ3 x hx eι g) := by
  apply Subtype.ext
  ext i j
  rfl

theorem congr_ψD_eq_fieldAut (eι : Kap μ ≃ Fin n) :
    MulAut.congr (slXEquiv σ hσ3 x hx eι) (slData μ σ hσ3 x hx).ψD = fieldAut n K σ := by
  ext p
  obtain ⟨h, rfl⟩ := proj_surjective n K p
  obtain ⟨g, rfl⟩ := (slTopEquiv σ hσ3 x hx eι).surjective h
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have e1 : (slXEquiv σ hσ3 x hx eι).symm (proj n K (slTopEquiv σ hσ3 x hx eι g)) =
      (slData μ σ hσ3 x hx).πD g := by
    rw [MulEquiv.symm_apply_eq, slXEquiv_mk]
  rw [e1, FieldData.ψD_mk, slXEquiv_mk, slTopEquiv_σt, fieldAut_proj]
  rfl

end Iso

theorem conj_proj_eq_conjAut {K : Type} [Field K] {n : ℕ} (g : SpecialLinearGroup (Fin n) K) :
    MulAut.conj (proj n K g) = conjAut n K (Matrix.SpecialLinearGroup.toGL g) := by
  ext p
  obtain ⟨h, rfl⟩ := proj_surjective n K p
  rw [MulAut.conj_apply, conjAut_proj, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, ← map_inv]
  rfl

theorem congr_conj {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (y : X) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem modelB_projectiveSL {n : ℕ} (hn : n = 4 ∨ n = 5) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ModelB (projectiveSL n K) (fieldAut n K σ) := by
  have hσ3 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  obtain ⟨x, hx⟩ := exists_apply_ne hσ1
  have hp := CharP.prime_ringChar K
  have hK5 : 5 ≤ ringChar K := hp.five_le_of_ne_two_of_ne_three hK2 hK3
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hcast : ∀ m : ℕ, m.Prime → ringChar K ≠ m → ((m : ℕ) : K) ≠ 0 := fun m hm hne h =>
    hne ((Nat.prime_dvd_prime_iff_eq hp hm).1 ((CharP.cast_eq_zero_iff K (ringChar K) m).1 h))
  have h3 : (3 : K) ≠ 0 := by exact_mod_cast hcast 3 Nat.prime_three hK3
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast hcast 2 Nat.prime_two hK2
  have hcard : Fintype.card (Kap (Fin (n - 4))) = n := by
    simp only [Kap, Lam, Fintype.card_sum, Fintype.card_fin]
    omega
  set eι : Kap (Fin (n - 4)) ≃ Fin n := Fintype.equivFinOfCardEq hcard with heι
  set D := slData (Fin (n - 4)) σ hσ3 x hx with hD
  have hK4 : 4 ≤ Nat.card K := by
    have h1 := ringChar_le_card_fixField σ
    have h2 : Nat.card (fixField σ) ≤ Nat.card K :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    omega
  have hl : CFSG.Open.IsQuasisimple ↥D.Gl :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv
      (isQuasisimple_SL (by simp [Lam]) hK4)
  have hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1 := D.hZ3_of_card (by rw [hcard]; omega)
  have hout : D.ψD ∉ (MulAut.conj : D.XD →* MulAut D.XD).range := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg⟩ := proj_surjective n K (slXEquiv σ hσ3 x hx eι y)
    have h1 : fieldAut n K σ = conjAut n K (Matrix.SpecialLinearGroup.toGL g) := by
      rw [← congr_ψD_eq_fieldAut (hσ3 := hσ3) (x := x) (hx := hx) eι, ← hy, congr_conj, ← hg,
        conj_proj_eq_conjAut]
    have h2 : fieldAut n K σ ∈ linearAutGroup n K := h1 ▸ conjAut_mem_linearAutGroup _
    exact hσ1 ((CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_linearAutGroup_iff (by omega)).1 h2)
  have hM := D.modelB h3 h2 hl hZ3 (D.layer_of_Gl_eq_top rfl hK5) hout
  have h := ModelB.congr (slXEquiv σ hσ3 x hx eι) hM
  rwa [congr_ψD_eq_fieldAut (hσ3 := hσ3) (x := x) (hx := hx) eι] at h

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Field

end
