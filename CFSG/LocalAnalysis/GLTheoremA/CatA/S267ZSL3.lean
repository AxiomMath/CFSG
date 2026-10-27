module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Trans
import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
import CFSG.GroupTheory.PLayer.CentralQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def diag3 (d : Fin 3 → F) (hd : ∏ i, d i = 1) : SpecialLinearGroup (Fin 3) F :=
  ⟨diagonal d, by rw [det_diagonal, hd]⟩

theorem coe_diag3 (d : Fin 3 → F) (hd : ∏ i, d i = 1) :
    ((diag3 d hd : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal d :=
  rfl

theorem ne_zero_of_prod_eq_one {d : Fin 3 → F} (hd : ∏ i, d i = 1) (i : Fin 3) : d i ≠ 0 := by
  intro h0
  have : ∏ i, d i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
  rw [hd] at this
  exact one_ne_zero this

theorem mem_centralizer_diag3_iff {d : Fin 3 → F} {hd : ∏ i, d i = 1}
    {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ Subgroup.centralizer ({diag3 d hd} : Set (SpecialLinearGroup (Fin 3) F)) ↔
      ∀ i j, d i ≠ d j → (g : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  have key : ∀ i j, ((g * diag3 d hd : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) i j = (g : Matrix (Fin 3) (Fin 3) F) i j * d j ∧
      ((diag3 d hd * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
        d i * (g : Matrix (Fin 3) (Fin 3) F) i j := fun i j => by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diag3,
      mul_diagonal, diagonal_mul]
    exact ⟨rfl, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, Matrix.SpecialLinearGroup.ext_iff]
  constructor
  · intro h i j hij
    have h1 := h i j
    rw [(key i j).1, (key i j).2] at h1
    have h2 : (d j - d i) * (g : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h2 with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm hij
    · exact h0
  · intro h i j
    rw [(key i j).1, (key i j).2]
    by_cases hij : d i = d j
    · rw [hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

abbrev blk : Finset (Fin 3) := {0}ᶜ

theorem mem_blk {i : Fin 3} : i ∈ blk ↔ i ≠ 0 := by simp

variable {d : Fin 3 → F} {hd : ∏ i, d i = 1}

theorem coordBlockSL_le_centralizer_diag3' {I : Finset (Fin 3)}
    (hI : ∀ i ∈ I, ∀ j ∈ I, d i = d j) :
    coordBlockSL F I ≤
      Subgroup.centralizer ({diag3 d hd} : Set (SpecialLinearGroup (Fin 3) F)) := by
  intro g hg
  rw [mem_centralizer_diag3_iff]
  intro i j hij
  have hg' := mem_coordBlockSL_iff.1 hg
  by_cases hiI : i ∈ I
  · by_cases hjI : j ∈ I
    · exact absurd (hI i hiI j hjI) hij
    · rw [hg' i j (Or.inr hjI), if_neg]
      rintro rfl
      exact hij rfl
  · rw [hg' i j (Or.inl hiI), if_neg]
    rintro rfl
    exact hij rfl

theorem coordBlockSL_le_centralizer_diag3 (h12 : d 1 = d 2) :
    coordBlockSL F blk ≤
      Subgroup.centralizer ({diag3 d hd} : Set (SpecialLinearGroup (Fin 3) F)) := by
  refine coordBlockSL_le_centralizer_diag3' fun i hi j hj => ?_
  have hi' : i = 1 ∨ i = 2 := by
    rw [mem_blk] at hi
    fin_cases i <;> simp_all
  have hj' : j = 1 ∨ j = 2 := by
    rw [mem_blk] at hj
    fin_cases j <;> simp_all
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp [h12]

variable (d hd) in
abbrev cent : Subgroup (SpecialLinearGroup (Fin 3) F) :=
  Subgroup.centralizer ({diag3 d hd} : Set (SpecialLinearGroup (Fin 3) F))

section Corner

variable (hd0 : ∀ j, j ≠ 0 → d 0 ≠ d j)
include hd0

theorem corner_entries {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ cent d hd) {j : Fin 3}
    (hj : j ≠ 0) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 j = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) j 0 = 0 := by
  rw [mem_centralizer_diag3_iff] at hg
  exact ⟨hg 0 j (hd0 j hj), hg j 0 (fun h => hd0 j hj h.symm)⟩

theorem corner_ne_zero {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ cent d hd) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
  intro h0
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 0 :=
    det_eq_zero_of_row_eq_zero 0 fun j => by
      by_cases hj : j = 0
      · rw [hj, h0]
      · exact (corner_entries hd0 hg hj).1
  rw [Matrix.SpecialLinearGroup.det_coe] at hdet
  exact one_ne_zero hdet

theorem corner_mul {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ cent d hd) :
    ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 =
      (g : Matrix (Fin 3) (Fin 3) F) 0 0 * (h : Matrix (Fin 3) (Fin 3) F) 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Finset.sum_eq_single 0]
  · intro b _ hb
    rw [(corner_entries hd0 hg hb).1, zero_mul]
  · simp

@[expose] noncomputable def cornerHom : cent d hd →* Fˣ where
  toFun g := Units.mk0 (((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0)
    (corner_ne_zero hd0 g.2)
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
    exact corner_mul hd0 g.2

theorem cornerHom_apply (g : cent d hd) :
    ((cornerHom hd0 g : Fˣ) : F) =
      ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 :=
  rfl

theorem mem_coordBlockSL_of_corner {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ cent d hd) (h1 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1) :
    g ∈ coordBlockSL F blk := by
  rw [mem_coordBlockSL_iff]
  intro i j hij
  have hij' : i = 0 ∨ j = 0 := by simpa [mem_blk] using hij
  rcases hij' with rfl | rfl
  · by_cases hj : j = 0
    · subst hj
      simp [h1]
    · rw [(corner_entries hd0 hg hj).1, if_neg (Ne.symm hj)]
  · by_cases hi : i = 0
    · subst hi
      simp [h1]
    · rw [(corner_entries hd0 hg hi).2, if_neg hi]

end Corner

theorem corner_of_mem_coordBlockSL {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ coordBlockSL F blk) : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
  rw [mem_coordBlockSL_iff.1 hg 0 0 (Or.inl (by simp [mem_blk])), if_pos rfl]

section Corner2

variable (hd0 : ∀ j, j ≠ 0 → d 0 ≠ d j)
include hd0

theorem coordBlockSL_subgroupOf_eq_ker (h12 : d 1 = d 2) :
    (coordBlockSL F blk).subgroupOf (cent d hd) = (cornerHom hd0).ker := by
  ext g
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro hg
    ext
    rw [cornerHom_apply, Units.val_one]
    exact corner_of_mem_coordBlockSL hg
  · intro hg
    have h1 := congrArg (fun u : Fˣ => (u : F)) hg
    rw [cornerHom_apply, Units.val_one] at h1
    exact mem_coordBlockSL_of_corner hd0 g.2 h1

theorem coordBlockSL_normal (h12 : d 1 = d 2) :
    ((coordBlockSL F blk).subgroupOf (cent d hd)).Normal := by
  rw [coordBlockSL_subgroupOf_eq_ker hd0 h12]
  exact MonoidHom.normal_ker _

theorem commutator_centralizer_le_coordBlockSL :
    ⁅cent d hd, cent d hd⁆ ≤ coordBlockSL F blk := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hgh : ⁅g, h⁆ ∈ cent d hd := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  apply mem_coordBlockSL_of_corner hd0 hgh
  have h1 : cornerHom hd0 ⁅(⟨g, hg⟩ : cent d hd), ⟨h, hh⟩⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact mul_inv_eq_one.2 (by rw [mul_inv_eq_iff_eq_mul, mul_comm])
  have h2 := congrArg (fun u : Fˣ => (u : F)) h1
  simp only [cornerHom_apply, Units.val_one] at h2
  have h3 : ((⁅(⟨g, hg⟩ : cent d hd), ⟨h, hh⟩⁆ : cent d hd) : SpecialLinearGroup (Fin 3) F) =
      ⁅g, h⁆ := rfl
  rwa [h3] at h2

end Corner2

theorem eq_one_of_conj_eq_smul (hd : ∏ i, d i = 1) (h12 : d 1 = d 2)
    {g : SpecialLinearGroup (Fin 3) F} {c : F}
    (h : diagonal d * (g : Matrix (Fin 3) (Fin 3) F) =
      c • ((g : Matrix (Fin 3) (Fin 3) F) * diagonal d)) : c = 1 := by
  by_contra hc
  have hz : ∀ i j, d i = d j → (g : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
    intro i j hij
    have h1 := congrFun (congrFun h i) j
    rw [diagonal_mul, Matrix.smul_apply, mul_diagonal, smul_eq_mul, hij] at h1
    have h2 : (1 - c) * d j * (g : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (by linear_combination -h4 : c = 1) hc
      · exact absurd h4 (ne_zero_of_prod_eq_one hd j)
    · exact h3
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_three, hz 0 0 rfl, hz 1 1 rfl, hz 1 2 h12, hz 2 1 h12.symm, hz 2 2 rfl] at hdet
  simp at hdet

theorem centralizer_proj_diag3 (hd : ∏ i, d i = 1) (h12 : d 1 = d 2) :
    Subgroup.centralizer ({proj 3 F (diag3 d hd)} : Set (projectiveSL 3 F)) =
      (cent d hd).map (proj 3 F) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, proj_eq_proj_iff] at hx
    obtain ⟨c, -, hc⟩ := mem_scalars.1 hx
    set X : SpecialLinearGroup (Fin 3) F := (g * diag3 d hd)⁻¹ * (diag3 d hd * g) with hX
    have hrel : (diag3 d hd * g : SpecialLinearGroup (Fin 3) F) = (g * diag3 d hd) * X := by
      rw [hX]; group
    have hmat : diagonal d * (g : Matrix (Fin 3) (Fin 3) F) =
        (c : F) • ((g : Matrix (Fin 3) (Fin 3) F) * diagonal d) := by
      have h1 : ((diag3 d hd * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          ((g * diag3 d hd * X : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        rw [hrel]
      rw [Matrix.SpecialLinearGroup.coe_mul (g * diag3 d hd) X, hc,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diag3] at h1
      rw [h1]
      ext i j
      simp [scalar_apply, mul_diagonal, Matrix.smul_apply, mul_comm]
    have hc1 := eq_one_of_conj_eq_smul hd h12 hmat
    refine ⟨g, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := congrFun (congrFun hmat i) j
    rw [hc1, one_smul] at this
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diag3]
    exact this.symm
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : g * diag3 d hd = diag3 d hd * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hg'])

variable (F) in
abbrev J3 : Subgroup (projectiveSL 3 F) := (coordBlockSL F blk).map (proj 3 F)

theorem eq_one_of_mem_coordBlockSL_of_proj_eq_one {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ coordBlockSL F blk) (h1 : proj 3 F g = 1) : g = 1 := by
  have hk : g ∈ scalars 3 F := by
    rw [← ker_proj]
    exact h1
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hk
  have h00 := corner_of_mem_coordBlockSL hg
  rw [hc, scalar_apply, diagonal_apply_eq] at h00
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [hc, h00, map_one, Matrix.SpecialLinearGroup.coe_one]

noncomputable def mapProjEquiv (K : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hK : K ≤ coordBlockSL F blk) : ↥K ≃* ↥(K.map (proj 3 F)) :=
  MulEquiv.ofBijective ((proj 3 F).subgroupMap K)
    ⟨fun a b hab => by
      have h1 : proj 3 F ((a : SpecialLinearGroup (Fin 3) F)⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact congrArg Subtype.val hab
      have h2 := eq_one_of_mem_coordBlockSL_of_proj_eq_one
        (hK (mul_mem (inv_mem a.2) b.2)) h1
      exact Subtype.ext (inv_mul_eq_one.1 h2),
     (proj 3 F).subgroupMap_surjective K⟩

theorem prod_diagBlk {ζ : F} (hζ : ζ ≠ 0) : ∏ i, (![1, ζ, ζ⁻¹] : Fin 3 → F) i = 1 := by
  simp [Fin.prod_univ_three, hζ]

theorem diag3_mem_coordBlockSL {ζ : F} (hζ : ζ ≠ 0) :
    diag3 ![1, ζ, ζ⁻¹] (prod_diagBlk hζ) ∈ coordBlockSL F blk := by
  rw [mem_coordBlockSL_iff]
  intro i j hij
  have hi : i = 0 ∨ j = 0 := by simpa [mem_blk] using hij
  rw [coe_diag3]
  by_cases hij' : i = j
  · subst hij'
    rcases hi with rfl | rfl <;> simp
  · rw [diagonal_apply_ne _ hij', if_neg hij']

theorem diag3_mul_transvection_ne {d : Fin 3 → F} (hd : ∏ i, d i = 1) {a b : Fin 3}
    (hab : a ≠ b) (hd_ab : d a ≠ d b) :
    diag3 d hd * Matrix.SpecialLinearGroup.transvection hab 1 ≠
      Matrix.SpecialLinearGroup.transvection hab 1 * diag3 d hd := by
  intro h
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin 3) F =>
    (x : Matrix (Fin 3) (Fin 3) F) a b) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diag3,
    Matrix.SpecialLinearGroup.transvection_coe, diagonal_mul, mul_diagonal] at h1
  have e2 : (1 + Matrix.single a b (1 : F) : Matrix (Fin 3) (Fin 3) F) a b = 1 := by
    rw [Matrix.add_apply, one_apply_ne hab, Matrix.single_apply, if_pos ⟨rfl, rfl⟩, zero_add]
  rw [e2, mul_one, one_mul] at h1
  exact hd_ab h1

section Root

variable [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
  (hF : 4 ≤ Nat.card F)
include hp hp2 hζ hF

theorem isQuasisimple_coordBlockSL_blk : CFSG.Open.IsQuasisimple ↥(coordBlockSL F blk) :=
  isQuasisimple_coordBlockSL (J := blk) (by decide) hF

omit hF in
theorem dvd_card_coordBlockSL_blk :
    p ∣ Nat.card (↥(coordBlockSL F blk) ⧸ Subgroup.center ↥(coordBlockSL F blk)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hab : (1 : Fin 3) ≠ 2 := by decide
  refine CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute hp
    (x := diag3 ![1, ζ, ζ⁻¹] (prod_diagBlk hζ0))
    (y := Matrix.SpecialLinearGroup.transvection hab 1) (diag3_mem_coordBlockSL hζ0)
    (transvection_mem_coordBlockSL (by decide) (by decide) hab 1) ?_ ?_
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_diag3, diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one]
    have hpow : (![1, ζ, ζ⁻¹] : Fin 3 → F) ^ p = 1 := by
      funext k
      fin_cases k <;> simp [hζ.pow_eq_one]
    rw [hpow, show (1 : Fin 3 → F) = fun _ => 1 from rfl, diagonal_one]
  · refine diag3_mul_transvection_ne _ hab ?_
    intro h
    have h1 : ζ = ζ⁻¹ := by simpa using h
    have h2 : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel₀ hζ0
    have h3 : p ∣ 2 := hζ.dvd_of_pow_eq_one 2 h2
    have := Nat.le_of_dvd (by norm_num) h3
    have := hp.two_le
    omega

theorem isQuasisimple_J3 : CFSG.Open.IsQuasisimple ↥(J3 F) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (mapProjEquiv _ le_rfl).symm (isQuasisimple_coordBlockSL_blk hp hp2 hζ hF)

omit hF in
theorem dvd_card_J3 : p ∣ Nat.card (↥(J3 F) ⧸ Subgroup.center ↥(J3 F)) := by
  rw [← CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.natCard_quotient_center_congr
    (mapProjEquiv _ le_rfl)]
  exact dvd_card_coordBlockSL_blk hp hp2 hζ

variable {e : Fin 3 → F} (he : ∏ i, e i = 1) (he12 : e 1 = e 2) (he01 : e 0 ≠ e 1)
include he he12 he01

omit hp hp2 hζ hF in
private theorem he0_of (j : Fin 3) (hj : j ≠ 0) : e 0 ≠ e j := by
  fin_cases j
  · exact absurd rfl hj
  · exact he01
  · show e 0 ≠ e 2
    rw [← he12]; exact he01

theorem glaPComponent_cent_diag3 : GLAPComponent p (cent e he) (coordBlockSL F blk) :=
  CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp
    (IsSubnormal.step (coordBlockSL_le_centralizer_diag3 he12)
      (coordBlockSL_normal (he0_of he he12 he01) he12) (IsSubnormal.refl _))
    (isQuasisimple_coordBlockSL_blk hp hp2 hζ hF) (dvd_card_coordBlockSL_blk hp hp2 hζ)

theorem eq_of_glaPComponent_cent_diag3 {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hK : GLAPComponent p (cent e he) K) : K = coordBlockSL F blk :=
  CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.eq_of_glaPComponent_of_commutator_le
    (coordBlockSL_le_centralizer_diag3 he12) (isQuasisimple_coordBlockSL_blk hp hp2 hζ hF)
    (commutator_centralizer_le_coordBlockSL (he0_of he he12 he01)) hK

omit hp hp2 hζ hF he he12 he01 in
private theorem central_ker (X : Subgroup (SpecialLinearGroup (Fin 3) F)) :
    ∀ y ∈ X ⊓ (proj 3 F).ker, ∀ x ∈ X, x * y = y * x := fun y hy x _ =>
  Subgroup.mem_center_iff.1 (by rw [ker_proj] at hy; exact scalars_le_center 3 F hy.2) x

theorem glaPComponent_centralizer_proj_diag3 :
    GLAPComponent p (Subgroup.centralizer ({proj 3 F (diag3 e he)} : Set (projectiveSL 3 F)))
      (J3 F) := by
  rw [centralizer_proj_diag3 he he12]
  exact (CFSG.glaPComponent_map_bijective_of_ker_le_center hp (proj 3 F)
    (central_ker _)).1 _ (glaPComponent_cent_diag3 hp hp2 hζ hF he he12 he01)

theorem eq_of_glaPComponent_centralizer_proj_diag3 {K : Subgroup (projectiveSL 3 F)}
    (hK : GLAPComponent p (Subgroup.centralizer
      ({proj 3 F (diag3 e he)} : Set (projectiveSL 3 F))) K) : K = J3 F := by
  rw [centralizer_proj_diag3 he he12] at hK
  obtain ⟨K₀, hK₀, rfl⟩ := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp (proj 3 F)
    (central_ker _)).2 K hK
  rw [eq_of_glaPComponent_cent_diag3 hp hp2 hζ hF he he12 he01 hK₀]

theorem glaPLayer_centralizer_proj_diag3 :
    GLAPLayer p (Subgroup.centralizer ({proj 3 F (diag3 e he)} : Set (projectiveSL 3 F))) =
      J3 F :=
  CFSG.LocalAnalysis.GLTheoremA.H81.layer_eq_of_unique
    (glaPComponent_centralizer_proj_diag3 hp hp2 hζ hF he he12 he01)
    (fun _ hK => eq_of_glaPComponent_centralizer_proj_diag3 hp hp2 hζ hF he he12 he01 hK)

end Root

end CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3

end
