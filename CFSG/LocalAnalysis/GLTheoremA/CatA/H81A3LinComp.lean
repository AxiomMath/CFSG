module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinCent
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
import CFSG.GroupTheory.PLayer.CentralQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.LinA3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open scoped commutatorElement

variable {F : Type} [Field F] {p : ℕ} {μ : F}

variable (F) in
abbrev JH : Subgroup (projectiveSL 4 F) := (coordBlockSL F blockJ).map (proj 4 F)

theorem eq_one_of_mem_coordBlockSL_of_proj_eq_one {g : SpecialLinearGroup (Fin 4) F}
    (hg : g ∈ coordBlockSL F blockJ) (h1 : proj 4 F g = 1) : g = 1 := by
  have hk : g ∈ scalars 4 F := by
    rw [← ker_proj]
    exact h1
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hk
  have h00 := corner_of_mem_coordBlockSL hg
  rw [hc, scalar_apply, diagonal_apply_eq] at h00
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [hc, h00, map_one, Matrix.SpecialLinearGroup.coe_one]

noncomputable def mapProjEquiv (K : Subgroup (SpecialLinearGroup (Fin 4) F))
    (hK : K ≤ coordBlockSL F blockJ) : ↥K ≃* ↥(K.map (proj 4 F)) :=
  MulEquiv.ofBijective ((proj 4 F).subgroupMap K)
    ⟨fun a b hab => by
      have h1 : proj 4 F ((a : SpecialLinearGroup (Fin 4) F)⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact congrArg Subtype.val hab
      have h2 := eq_one_of_mem_coordBlockSL_of_proj_eq_one
        (hK (mul_mem (inv_mem a.2) b.2)) h1
      exact Subtype.ext (inv_mul_eq_one.1 h2),
     (proj 4 F).subgroupMap_surjective K⟩

theorem coordBlockSL_mono {I J : Finset (Fin 4)} (h : I ⊆ J) :
    coordBlockSL F I ≤ coordBlockSL F J := by
  intro g hg
  rw [mem_coordBlockSL_iff] at hg ⊢
  intro i j hij
  exact hg i j (hij.imp (fun hi hiI => hi (h hiI)) (fun hj hjI => hj (h hjI)))

theorem natCard_quotient_center_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

theorem diagSL_mul_transvection_ne {d : Fin 4 → F} (hd : ∏ i, d i = 1) {a b : Fin 4}
    (hab : a ≠ b) (hd_ab : d a ≠ d b) :
    diagSL d hd * Matrix.SpecialLinearGroup.transvection hab 1 ≠
      Matrix.SpecialLinearGroup.transvection hab 1 * diagSL d hd := by
  intro h
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin 4) F =>
    (x : Matrix (Fin 4) (Fin 4) F) a b) h
  rw [(diagSL_mul_transvection_apply hd hab 1 a b).1,
    (diagSL_mul_transvection_apply hd hab 1 a b).2] at h1
  have e2 : (1 + Matrix.single a b (1 : F) : Matrix (Fin 4) (Fin 4) F) a b = 1 := by
    rw [Matrix.add_apply, one_apply_ne hab, Matrix.single_apply, if_pos ⟨rfl, rfl⟩, zero_add]
  rw [e2, mul_one, one_mul] at h1
  exact hd_ab h1

section Root

variable [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p) (hF : 4 ≤ Nat.card F)
include hp hp2 hμ

omit [Finite F] in
theorem td_pow (i : Fin 4) : td μ i ^ p = 1 := by
  fin_cases i <;> simp [td, hμ.pow_eq_one]

omit [Finite F] in
theorem t2d_pow (i : Fin 4) : t2d μ i ^ p = 1 := by
  fin_cases i <;> simp [t2d, hμ.pow_eq_one]

omit [Finite F] in
theorem inv_ne_self : μ⁻¹ ≠ μ := by
  have hμ0 := ne_zero_of_root hp hp2 hμ
  intro h
  apply pow_two_ne_one hp hp2 hμ
  calc μ ^ 2 = μ * μ := sq μ
    _ = μ⁻¹ * μ := by rw [h]
    _ = 1 := inv_mul_cancel₀ hμ0

omit [Finite F] in
theorem inv_ne_one : μ⁻¹ ≠ 1 := fun h => ne_one_of_root hp hp2 hμ (inv_eq_one.1 h)

include hF

theorem isQuasisimple_coordBlockSL_blockJ : CFSG.Open.IsQuasisimple ↥(coordBlockSL F blockJ) :=
  isQuasisimple_coordBlockSL (J := blockJ) (by decide) hF

theorem dvd_card_coordBlockSL_blockJ :
    p ∣ Nat.card (↥(coordBlockSL F blockJ) ⧸ Subgroup.center ↥(coordBlockSL F blockJ)) := by
  have hμ0 := ne_zero_of_root hp hp2 hμ
  have hab : (1 : Fin 4) ≠ 2 := by decide
  refine dvd_card_quotient_center_of_not_commute hp (x := diagSL (td μ) (prod_td hμ0))
    (y := Matrix.SpecialLinearGroup.transvection hab 1) ?_
    (transvection_mem_coordBlockSL (by decide) (by decide) hab 1)
    (diagSL_pow_eq_one hp hp2 hμ (td_pow hp hp2 hμ)) ?_
  · rw [mem_coordBlockSL_iff]
    intro i j hij
    rw [coe_diagSL]
    have hi : i = 0 ∨ j = 0 := by simpa [mem_blockJ] using hij
    by_cases hij' : i = j
    · subst hij'
      rcases hi with rfl | rfl <;> simp [td]
    · rw [diagonal_apply_ne _ hij', if_neg hij']
  · exact diagSL_mul_transvection_ne (prod_td hμ0) hab
      (by simpa [td] using (inv_ne_self hp hp2 hμ).symm)

theorem glaPComponent_cent_ySL :
    GLAPComponent p (cent (yd μ) (prod_yd (ne_zero_of_root hp hp2 hμ))) (coordBlockSL F blockJ) :=
  CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp
    (IsSubnormal.step (coordBlockSL_le_centralizer_diagSL (yd_const hp hp2 hμ))
      (coordBlockSL_normal (yd_zero_ne hp hp2 hμ) (yd_const hp hp2 hμ)) (IsSubnormal.refl _))
    (isQuasisimple_coordBlockSL_blockJ hp hp2 hμ hF) (dvd_card_coordBlockSL_blockJ hp hp2 hμ hF)

theorem eq_of_glaPComponent_cent_ySL {K : Subgroup (SpecialLinearGroup (Fin 4) F)}
    (hK : GLAPComponent p (cent (yd μ) (prod_yd (ne_zero_of_root hp hp2 hμ))) K) :
    K = coordBlockSL F blockJ :=
  eq_of_glaPComponent_of_commutator_le (coordBlockSL_le_centralizer_diagSL (yd_const hp hp2 hμ))
    (isQuasisimple_coordBlockSL_blockJ hp hp2 hμ hF)
    (commutator_centralizer_le_coordBlockSL (yd_zero_ne hp hp2 hμ)) hK

omit hp hp2 hμ hF in
private theorem central_ker (X : Subgroup (SpecialLinearGroup (Fin 4) F)) :
    ∀ y ∈ X ⊓ (proj 4 F).ker, ∀ x ∈ X, x * y = y * x := fun y hy x _ =>
  (Subgroup.mem_center_iff.1 (ker_proj_le_center hy.2) x)

theorem glaPComponent_centralizer_proj_ySL :
    GLAPComponent p (Subgroup.centralizer
      ({proj 4 F (ySL (ne_zero_of_root hp hp2 hμ))} : Set (projectiveSL 4 F))) (JH F) := by
  rw [centralizer_proj_ySL hp hp2 hμ]
  exact (CFSG.glaPComponent_map_bijective_of_ker_le_center hp (proj 4 F)
    (central_ker _)).1 _ (glaPComponent_cent_ySL hp hp2 hμ hF)

theorem eq_of_glaPComponent_centralizer_proj_ySL {K : Subgroup (projectiveSL 4 F)}
    (hK : GLAPComponent p (Subgroup.centralizer
      ({proj 4 F (ySL (ne_zero_of_root hp hp2 hμ))} : Set (projectiveSL 4 F))) K) :
    K = JH F := by
  rw [centralizer_proj_ySL hp hp2 hμ] at hK
  obtain ⟨K₀, hK₀, rfl⟩ := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp (proj 4 F)
    (central_ker _)).2 K hK
  rw [eq_of_glaPComponent_cent_ySL hp hp2 hμ hF hK₀]

theorem isQuasisimple_JH : CFSG.Open.IsQuasisimple ↥(JH F) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (mapProjEquiv _ le_rfl).symm (isQuasisimple_coordBlockSL_blockJ hp hp2 hμ hF)

theorem dvd_card_JH : p ∣ Nat.card (↥(JH F) ⧸ Subgroup.center ↥(JH F)) := by
  rw [← natCard_quotient_center_congr (mapProjEquiv _ le_rfl)]
  exact dvd_card_coordBlockSL_blockJ hp hp2 hμ hF

omit hF

theorem proj_zSL_not_mem_zpowers :
    proj 4 F (zSL (ne_zero_of_root hp hp2 hμ)) ∉
      Subgroup.zpowers (proj 4 F (ySL (ne_zero_of_root hp hp2 hμ))) := by
  have hμ0 := ne_zero_of_root hp hp2 hμ
  have hab : (1 : Fin 4) ≠ 2 := by decide
  set u := Matrix.SpecialLinearGroup.transvection hab (1 : F) with hu
  have huJ : u ∈ coordBlockSL F blockJ :=
    transvection_mem_coordBlockSL (by decide) (by decide) hab 1
  have huy : u * ySL hμ0 = ySL hμ0 * u :=
    Subgroup.mem_centralizer_singleton_iff.1
      (coordBlockSL_le_centralizer_diagSL (yd_const hp hp2 hμ) huJ)
  have hyC : proj 4 F (ySL hμ0) ∈ Subgroup.centralizer ({proj 4 F u} : Set (projectiveSL 4 F)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, huy]
  intro hmem
  have hzC := (Subgroup.zpowers_le.2 hyC) hmem
  rw [Subgroup.mem_centralizer_singleton_iff] at hzC
  exact proj_diagSL_mul_transvection_ne (prod_zd hμ0) hab
    (by simpa [zd] using inv_ne_one hp hp2 hμ) hzC

include hF

theorem glaPLayer_JH_inf_centralizer_ne_bot :
    GLAPLayer p (JH F ⊓ Subgroup.centralizer
      ({proj 4 F (zSL (ne_zero_of_root hp hp2 hμ))} : Set (projectiveSL 4 F))) ≠ ⊥ := by
  have hμ0 := ne_zero_of_root hp hp2 hμ
  have hIJ : blockI ⊆ blockJ := by decide
  have hK₂J : coordBlockSL F blockI ≤ coordBlockSL F blockJ := coordBlockSL_mono hIJ
  have hzI : ∀ i ∈ blockI, ∀ j ∈ blockI, zd μ i = zd μ j := by
    intro i hi j hj
    fin_cases i <;> fin_cases j <;> simp_all [blockI, zd]
  have hK₂z : coordBlockSL F blockI ≤ cent (zd μ) (prod_zd hμ0) :=
    coordBlockSL_le_centralizer_diagSL' hzI
  set K₂ := (coordBlockSL F blockI).map (proj 4 F) with hK₂def
  have hle : K₂ ≤ JH F ⊓ Subgroup.centralizer
      ({proj 4 F (zSL hμ0)} : Set (projectiveSL 4 F)) := by
    refine le_inf (Subgroup.map_mono hK₂J) ?_
    rw [centralizer_proj_zSL hp hp2 hμ]
    exact Subgroup.map_mono hK₂z
  have hdist : ∀ i j, (i ∈ blockI ↔ j ∉ blockI) → zd μ i ≠ zd μ j := by
    have h1 := inv_ne_one hp hp2 hμ
    have h2 := ne_one_of_root hp hp2 hμ
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [zd, blockI, eq_comm]
  have hnorm : ∀ m ∈ cent (zd μ) (prod_zd hμ0), ∀ g ∈ coordBlockSL F blockI,
      m * g * m⁻¹ ∈ coordBlockSL F blockI := by
    intro m hm g hg
    refine conj_mem_coordBlockSL ?_ hg
    rw [mem_centralizer_diagSL_iff] at hm
    ext i j
    rw [compIndicator_mul_apply, mul_compIndicator_apply]
    by_cases hi : i ∈ blockI <;> by_cases hj : j ∈ blockI
    · simp [hi, hj]
    · rw [if_pos hi, if_neg hj, hm i j (hdist i j ⟨fun _ => hj, fun _ => hi⟩)]
    · rw [if_neg hi, if_pos hj, hm i j (hdist i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩)]
    · simp [hi, hj]
  have hN : (K₂.subgroupOf (JH F ⊓ Subgroup.centralizer
      ({proj 4 F (zSL hμ0)} : Set (projectiveSL 4 F)))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : projectiveSL 4 F) ∈ (cent (zd μ) (prod_zd hμ0)).map (proj 4 F) := by
      rw [← centralizer_proj_zSL hp hp2 hμ]
      exact g.2.2
    obtain ⟨m, hm, hmg⟩ := hg
    obtain ⟨k, hk, hkn⟩ := hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hmg, ← hkn, ← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (hnorm m hm k hk)
  have hq : CFSG.Open.IsQuasisimple ↥K₂ :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv (mapProjEquiv _ hK₂J).symm
      (isQuasisimple_coordBlockSL (J := blockI) (by decide) hF)
  have hdvd : p ∣ Nat.card (↥K₂ ⧸ Subgroup.center ↥K₂) := by
    rw [← natCard_quotient_center_congr (mapProjEquiv _ hK₂J)]
    have hab : (2 : Fin 4) ≠ 3 := by decide
    refine dvd_card_quotient_center_of_not_commute hp (x := diagSL (t2d μ) (prod_t2d hμ0))
      (y := Matrix.SpecialLinearGroup.transvection hab 1) ?_
      (transvection_mem_coordBlockSL (by decide) (by decide) hab 1)
      (diagSL_pow_eq_one hp hp2 hμ (t2d_pow hp hp2 hμ)) ?_
    · rw [mem_coordBlockSL_iff]
      intro i j hij
      rw [coe_diagSL]
      by_cases hij' : i = j
      · subst hij'
        have : i = 0 ∨ i = 1 := by
          rcases hij with h | h <;> fin_cases i <;> simp_all [blockI]
        rcases this with rfl | rfl <;> simp [t2d]
      · rw [diagonal_apply_ne _ hij', if_neg hij']
    · exact diagSL_mul_transvection_ne (prod_t2d hμ0) hab
        (by simpa [t2d] using (inv_ne_self hp hp2 hμ).symm)
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple hp hle hN hq
    hdvd

end Root

end CFSG.LocalAnalysis.GLTheoremA.H81.LinA3
