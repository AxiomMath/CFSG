module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZSL3
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Trans
import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
import CFSG.GroupTheory.PLayer.CentralQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3 (diag3 coe_diag3 blk mem_blk cent)
open scoped commutatorElement

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem toSLU_diagU (d : Fin 3 → K) (hn : ∀ i, h.bar (d i) * d i = 1) (hd : ∏ i, d i = 1) :
    toSLU h (diagU h d hn hd) = diag3 d hd :=
  rfl

theorem mem_centralizer_iff_toSLU {x g : ↥(SG h)} :
    g ∈ Subgroup.centralizer ({x} : Set ↥(SG h)) ↔
      toSLU h g ∈ Subgroup.centralizer ({toSLU h x} : Set (SpecialLinearGroup (Fin 3) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
    ← map_mul, (toSLU_injective h).eq_iff]

variable {d : Fin 3 → K} {hn : ∀ i, h.bar (d i) * d i = 1} {hd : ∏ i, d i = 1}

theorem mem_centralizer_diagU_iff {g : ↥(SG h)} :
    g ∈ Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h)) ↔
      ∀ i j, d i ≠ d j → ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  rw [mem_centralizer_iff_toSLU, toSLU_diagU, SL3.mem_centralizer_diag3_iff]
  rfl

theorem toSLU_mem_cent {g : ↥(SG h)}
    (hg : g ∈ Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h))) :
    toSLU h g ∈ cent d hd := by
  rw [mem_centralizer_iff_toSLU, toSLU_diagU] at hg
  exact hg

theorem blockU_le_centralizer (h12 : d 1 = d 2) :
    blockU h blk ≤ Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h)) := by
  intro g hg
  rw [mem_centralizer_iff_toSLU, toSLU_diagU]
  exact SL3.coordBlockSL_le_centralizer_diag3 h12 hg

variable (hd0 : ∀ j, j ≠ 0 → d 0 ≠ d j)
include hd0

theorem commutator_centralizer_le_blockU :
    ⁅Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h)),
      Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h))⁆ ≤ blockU h blk := by
  rw [Subgroup.commutator_le]
  intro g hg k hk
  change toSLU h ⁅g, k⁆ ∈ coordBlockSL K blk
  rw [map_commutatorElement]
  exact SL3.commutator_centralizer_le_coordBlockSL hd0
    (Subgroup.commutator_mem_commutator (toSLU_mem_cent hg) (toSLU_mem_cent hk))

theorem blockU_normal (h12 : d 1 = d 2) :
    ((blockU h blk).subgroupOf
      (Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h)))).Normal := by
  refine ⟨fun n hnm g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hnm ⊢
  change toSLU h ((g : ↥(SG h)) * n * (g : ↥(SG h))⁻¹) ∈ coordBlockSL K blk
  rw [map_mul, map_mul, map_inv]
  have hN := SL3.coordBlockSL_normal (hd := hd) hd0 h12
  have h1 : (⟨toSLU h n, SL3.coordBlockSL_le_centralizer_diag3 h12 hnm⟩ : cent d hd) ∈
      (coordBlockSL K blk).subgroupOf (cent d hd) := hnm
  exact hN.conj_mem _ h1 ⟨toSLU h g, toSLU_mem_cent g.2⟩

omit hd0

theorem centralizer_projU_diagU (h12 : d 1 = d 2) :
    Subgroup.centralizer ({projU h (diagU h d hn hd)} : Set (PU h)) =
      (Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h))).map (projU h) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hx
    have hk : (g * diagU h d hn hd)⁻¹ * (diagU h d hn hd * g) ∈ (projU h).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 (ker_projU (h := h) ▸ hk)
    have hrel : ((diagU h d hn hd * g : ↥(SG h)) : GL (Fin 3) K) =
        ((g * diagU h d hn hd : ↥(SG h)) : GL (Fin 3) K) *
          Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      have e1 : diagU h d hn hd * g =
          g * diagU h d hn hd * ((g * diagU h d hn hd)⁻¹ * (diagU h d hn hd * g)) := by group
      rw [← hc, ← Subgroup.coe_mul, ← e1]
    have hmat : diagonal d * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (c : K) • (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d) := by
      have h1 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hrel
      simp only [Subgroup.coe_mul, Units.val_mul, coe_diagU,
        Matrix.GeneralLinearGroup.coe_scalar] at h1
      rw [h1, scalar_apply, ← smul_eq_mul_diagonal]
    have hc1 := SL3.eq_one_of_conj_eq_smul (g := toSLU h g) hd h12 hmat
    refine ⟨g, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
    apply Subtype.ext
    apply Units.ext
    rw [hc1, one_smul] at hmat
    simp only [Subgroup.coe_mul, Units.val_mul, coe_diagU]
    exact hmat.symm
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : g * diagU h d hn hd = diagU h d hn hd * g :=
      Subgroup.mem_centralizer_singleton_iff.1 hg
    exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hg'])

variable (h) in
noncomputable abbrev JU : Subgroup (PU h) := (blockU h blk).map (projU h)

theorem zero_not_mem_blk : (0 : Fin 3) ∉ blk := by simp [mem_blk]

@[expose] def swapMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, 0, -1; 0, 1, 0]

theorem det_swapMat : (swapMat K).det = 1 := by
  simp [swapMat, Matrix.det_fin_three]

variable (h) in
@[expose] noncomputable def swapBlk : ↥(SG h) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (swapMat K) (by rw [det_swapMat]; exact one_ne_zero),
    mem_gramSU.2 ⟨by
      change ((swapMat K).map h.bar)ᵀ * ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        swapMat K = ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      have hmap : (swapMat K).map h.bar = swapMat K := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [swapMat]
      rw [hmap, Units.val_one, Matrix.mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three],
      det_swapMat⟩⟩

theorem coe_swapBlk :
    (((swapBlk h : ↥(SG h)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = swapMat K :=
  rfl

theorem swapBlk_mem_blockU : swapBlk h ∈ blockU h blk := by
  rw [mem_blockU_iff]
  intro i j hij
  have hij' : i = 0 ∨ j = 0 := by simpa [mem_blk] using hij
  rw [coe_swapBlk]
  fin_cases i <;> fin_cases j <;> simp [swapMat] at hij' ⊢

theorem norm_diagBlk {ζ : K} (hζn : h.bar ζ * ζ = 1) :
    ∀ i, h.bar ((![1, ζ, ζ⁻¹] : Fin 3 → K) i) * (![1, ζ, ζ⁻¹] : Fin 3 → K) i = 1 := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζn
  intro i
  fin_cases i
  · simp
  · exact hζn
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, map_inv₀]
    rw [← mul_inv, hζn, inv_one]

theorem prod_diagBlk {ζ : K} (hζ0 : ζ ≠ 0) : ∏ i, (![1, ζ, ζ⁻¹] : Fin 3 → K) i = 1 :=
  SL3.prod_diagBlk hζ0

theorem diagU_blk_mem_blockU {ζ : K} (hζn : h.bar ζ * ζ = 1) (hζ0 : ζ ≠ 0) :
    diagU h ![1, ζ, ζ⁻¹] (norm_diagBlk hζn) (prod_diagBlk hζ0) ∈ blockU h blk := by
  change toSLU h _ ∈ coordBlockSL K blk
  rw [toSLU_diagU]
  exact SL3.diag3_mem_coordBlockSL hζ0

section Root

variable [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
  (hζn : h.bar ζ * ζ = 1)
include hp hp2 hζ hζn

theorem diagU_blk_pow :
    diagU h ![1, ζ, ζ⁻¹] (norm_diagBlk hζn) (prod_diagBlk (hζ.ne_zero hp.ne_zero)) ^ p = 1 := by
  have hpow : (![1, ζ, ζ⁻¹] : Fin 3 → K) ^ p = 1 := by
    funext k
    fin_cases k <;> simp [hζ.pow_eq_one]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_diagU, diagonal_pow, hpow]
  rfl

theorem diagU_blk_mul_swapBlk_ne :
    diagU h ![1, ζ, ζ⁻¹] (norm_diagBlk hζn) (prod_diagBlk (hζ.ne_zero hp.ne_zero)) * swapBlk h ≠
      swapBlk h * diagU h ![1, ζ, ζ⁻¹] (norm_diagBlk hζn) (prod_diagBlk (hζ.ne_zero hp.ne_zero)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  intro hc
  have h1 := congrArg (fun x : ↥(SG h) => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2) hc
  simp only [Subgroup.coe_mul, Units.val_mul, coe_diagU, coe_swapBlk, diagonal_mul,
    mul_diagonal] at h1
  have h2 : ζ = ζ⁻¹ := by simpa [swapMat] using h1
  have h3 : ζ ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h2]
    exact mul_inv_cancel₀ hζ0
  have h4 : p ∣ 2 := hζ.dvd_of_pow_eq_one 2 h3
  have := Nat.le_of_dvd (by norm_num) h4
  have := hp.two_le
  omega

theorem dvd_card_blockU_blk : p ∣ Nat.card (↥(blockU h blk) ⧸ Subgroup.center ↥(blockU h blk)) :=
  CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute hp
    (diagU_blk_mem_blockU hζn (hζ.ne_zero hp.ne_zero)) swapBlk_mem_blockU
    (diagU_blk_pow hp hp2 hζ hζn) (diagU_blk_mul_swapBlk_ne hp hp2 hζ hζn)

theorem dvd_card_JU : p ∣ Nat.card (↥(JU h) ⧸ Subgroup.center ↥(JU h)) := by
  rw [← CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.natCard_quotient_center_congr
    (mapProjUEquiv zero_not_mem_blk _ le_rfl)]
  exact dvd_card_blockU_blk hp hp2 hζ hζn

end Root

section Comp

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hq : 5 ≤ ℓ ^ f)
include hK hq

theorem isQuasisimple_JU : CFSG.Open.IsQuasisimple ↥(JU h) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (mapProjUEquiv zero_not_mem_blk _ le_rfl).symm (isQuasisimple_blockU hK hq (by decide))

variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
  (hζn : h.bar ζ * ζ = 1) (h12 : d 1 = d 2) (hd01 : d 0 ≠ d 1)
include hp hp2 hζ hζn h12 hd01

omit hK hq hp hp2 hζ hζn in
private theorem hd0_of (j : Fin 3) (hj : j ≠ 0) : d 0 ≠ d j := by
  fin_cases j
  · exact absurd rfl hj
  · exact hd01
  · show d 0 ≠ d 2
    rw [← h12]
    exact hd01

theorem glaPComponent_cent_diagU :
    GLAPComponent p (Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h))) (blockU h blk) :=
  CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp
    (IsSubnormal.step (blockU_le_centralizer h12) (blockU_normal (hd0_of h12 hd01) h12)
      (IsSubnormal.refl _))
    (isQuasisimple_blockU hK hq (by decide)) (dvd_card_blockU_blk hp hp2 hζ hζn)

omit hp hp2 hζ hζn in
theorem eq_of_glaPComponent_cent_diagU {L : Subgroup ↥(SG h)}
    (hL : GLAPComponent p (Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h))) L) :
    L = blockU h blk :=
  CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.eq_of_glaPComponent_of_commutator_le
    (blockU_le_centralizer h12) (isQuasisimple_blockU hK hq (by decide))
    (commutator_centralizer_le_blockU (hd0_of h12 hd01)) hL

omit hK hq hp hp2 hζ hζn h12 hd01 in
private theorem central_kerU (X : Subgroup ↥(SG h)) :
    ∀ y ∈ X ⊓ (projU h).ker, ∀ x ∈ X, x * y = y * x := fun y hy x _ =>
  Subgroup.mem_center_iff.1 (normOneScalars_le_center h _ 3 (ker_projU (h := h) ▸ hy.2)) x

theorem glaPComponent_centralizer_projU_diagU :
    GLAPComponent p (Subgroup.centralizer ({projU h (diagU h d hn hd)} : Set (PU h))) (JU h) := by
  rw [centralizer_projU_diagU h12]
  exact (CFSG.glaPComponent_map_bijective_of_ker_le_center hp (projU h)
    (central_kerU _)).1 _ (glaPComponent_cent_diagU hK hq hp hp2 hζ hζn h12 hd01)

theorem eq_of_glaPComponent_centralizer_projU_diagU {L : Subgroup (PU h)}
    (hL : GLAPComponent p (Subgroup.centralizer ({projU h (diagU h d hn hd)} : Set (PU h))) L) :
    L = JU h := by
  rw [centralizer_projU_diagU h12] at hL
  obtain ⟨L₀, hL₀, rfl⟩ := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp (projU h)
    (central_kerU _)).2 L hL
  rw [eq_of_glaPComponent_cent_diagU hK hq h12 hd01 hL₀]

theorem glaPLayer_centralizer_projU_diagU :
    GLAPLayer p (Subgroup.centralizer ({projU h (diagU h d hn hd)} : Set (PU h))) = JU h :=
  CFSG.LocalAnalysis.GLTheoremA.H81.layer_eq_of_unique
    (glaPComponent_centralizer_projU_diagU hK hq hp hp2 hζ hζn h12 hd01)
    (fun _ hL => eq_of_glaPComponent_centralizer_projU_diagU hK hq hp hp2 hζ hζn h12 hd01 hL)

end Comp

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
