module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ffE8Hyp_toSign_neg_one : toSign (-1 : (ZMod 3)ˣ) = -1 := by decide

private def ffE8Hyp_w : Fin 2 → (ZMod 3)ˣ := ![1, -1]

private theorem ffE8Hyp_sq_sub_sq_one :
    ∀ x y : ZMod 3, x ^ 2 - y ^ 2 = 1 → y = 0 ∧ (x = 1 ∨ x = -1) := by
  decide

private theorem ffE8Hyp_sq_sub_sq_neg :
    ∀ x y : ZMod 3, x ^ 2 - y ^ 2 = -1 → x = 0 ∧ (y = 1 ∨ y = -1) := by
  decide

private theorem ffE8Hyp_fin2_decomp (f : Fin 2 → ZMod 3) :
    f = f 0 • Pi.single 0 (1 : ZMod 3) + f 1 • Pi.single 1 (1 : ZMod 3) := by
  funext i
  fin_cases i <;> simp

theorem ffE8Hyp_exists_ab (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (hd : invDim t = 4)
    (hs : invSign t = 1) :
    ∃ a b : V, a ∈ fixSp t ∧ b ∈ fixSp t ∧ Q a = 1 ∧ Q b = -1 ∧ QuadraticMap.polar Q a b = 0 ∧
      ∀ v ∈ fixSp t, ∃ x y : ZMod 3, v = x • a + y • b := by
  let w : Fin 2 → (ZMod 3)ˣ := ffE8Hyp_w
  let Q₀ : QuadraticForm (ZMod 3) (Fin 2 → ZMod 3) :=
    QuadraticMap.weightedSumSquares (ZMod 3) (fun i => (w i : ZMod 3))
  have hPnd : (Q.restrict (fixSp t)).Nondegenerate := nondegenerate_restrict_fixSp hQ htt
  have hPdim : Module.finrank (ZMod 3) (fixSp t) = 2 := by
    have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
    simp only [invDim] at hd
    omega
  have hPsgn : quadSign (Q.restrict (fixSp t)) = 1 := by
    have h := quadSign_fixSp_eq (Q := Q) hQ htt
    rw [hsgn, hs, hd, hdim] at h
    rw [h]
    decide
  have hQ₀ : Q₀.Nondegenerate := by
    refine QuadraticMap.nondegenerate_weightedSumSquares (fun i => ?_)
    rw [isRegular_iff_ne_zero]
    fin_cases i <;> decide
  have hQ₀sign : quadSign Q₀ = 1 := by
    have heq : Q₀ = TauCeti.presentedForm ⟨2, w⟩ :=
      (TauCeti.presentedForm_eq_weightedSumSquares_coe (w := w)).symm
    rw [heq, quadSign_eq_signOf _ (TauCeti.nondegenerate_presentedForm _),
      TauCeti.formClass_presentedForm, signOf_mk_diag]
    have hprod : (∏ i : Fin 2, toSign (w i)) = -1 := by
      rw [Fin.prod_univ_two,
        show w 0 = (1 : (ZMod 3)ˣ) from rfl, show w 1 = (-1 : (ZMod 3)ˣ) from rfl,
        map_one, ffE8Hyp_toSign_neg_one]
      decide
    rw [hprod]
    decide
  have hdim₀ : Module.finrank (ZMod 3) (Fin 2 → ZMod 3) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hPnd hQ₀
    (hPdim.trans hdim₀.symm) (hPsgn.trans hQ₀sign.symm)
  have hQ₀_zero : Q₀ (Pi.single 0 (1 : ZMod 3)) = 1 := by
    show QuadraticMap.weightedSumSquares (ZMod 3) (fun i => (w i : ZMod 3))
      (Pi.single 0 (1 : ZMod 3)) = 1
    rw [QuadraticMap.weightedSumSquares_apply]
    rw [Finset.sum_eq_single 0
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero, smul_zero])
      (fun h => absurd (Finset.mem_univ 0) h)]
    rw [Pi.single_eq_same, mul_one, smul_eq_mul, mul_one]
    rfl
  have hQ₀_one : Q₀ (Pi.single 1 (1 : ZMod 3)) = -1 := by
    show QuadraticMap.weightedSumSquares (ZMod 3) (fun i => (w i : ZMod 3))
      (Pi.single 1 (1 : ZMod 3)) = -1
    rw [QuadraticMap.weightedSumSquares_apply]
    rw [Finset.sum_eq_single 1
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero, smul_zero])
      (fun h => absurd (Finset.mem_univ 1) h)]
    rw [Pi.single_eq_same, mul_one, smul_eq_mul, mul_one]
    rfl
  have hQ₀_polar : QuadraticMap.polar Q₀ (Pi.single 0 (1 : ZMod 3))
      (Pi.single 1 (1 : ZMod 3)) = 0 := by
    show QuadraticMap.polar (QuadraticMap.weightedSumSquares (ZMod 3)
      (fun i => (w i : ZMod 3))) (Pi.single 0 (1 : ZMod 3))
      (Pi.single 1 (1 : ZMod 3)) = 0
    rw [← QuadraticMap.polarBilin_apply_apply]
    have h2 : (2 : ZMod 3) • QuadraticMap.associated (R := ZMod 3)
        (QuadraticMap.weightedSumSquares (ZMod 3) (fun i => (w i : ZMod 3)))
        (Pi.single 0 (1 : ZMod 3)) (Pi.single 1 (1 : ZMod 3)) =
        QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares (ZMod 3)
          (fun i => (w i : ZMod 3))) (Pi.single 0 (1 : ZMod 3))
          (Pi.single 1 (1 : ZMod 3)) := by
      have h := DFunLike.congr_fun (DFunLike.congr_fun
        (QuadraticMap.two_nsmul_associated (S := ZMod 3)
          (QuadraticMap.weightedSumSquares (ZMod 3) (fun i => (w i : ZMod 3))))
        (Pi.single 0 (1 : ZMod 3))) (Pi.single 1 (1 : ZMod 3))
      simp only [LinearMap.smul_apply, Pi.smul_apply, nsmul_eq_mul] at h
      have hcast : (↑(2 : ℕ) : ZMod 3) = 2 := by norm_num
      rw [hcast] at h
      simpa only [smul_eq_mul] using h
    rw [← h2, QuadraticMap.associated_weightedSumSquares]
    have hsum : (∑ m : Fin 2, (w m : ZMod 3) *
        ((Pi.single 0 (1 : ZMod 3) : Fin 2 → ZMod 3) m *
          (Pi.single 1 (1 : ZMod 3) : Fin 2 → ZMod 3) m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      by_cases hm0 : m = 0
      · subst hm0
        rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
          mul_zero, mul_zero]
      · rw [Pi.single_eq_of_ne hm0, zero_mul, mul_zero]
    rw [hsum, smul_zero]
  let a : fixSp t := e.symm (Pi.single 0 (1 : ZMod 3))
  let b : fixSp t := e.symm (Pi.single 1 (1 : ZMod 3))
  refine ⟨(a : V), (b : V), a.2, b.2, ?_, ?_, ?_, ?_⟩
  · exact (e.symm.map_app (Pi.single 0 (1 : ZMod 3))).trans hQ₀_zero
  · exact (e.symm.map_app (Pi.single 1 (1 : ZMod 3))).trans hQ₀_one
  · have hp : QuadraticMap.polar Q (a : V) (b : V) =
        QuadraticMap.polar Q₀ (Pi.single 0 (1 : ZMod 3)) (Pi.single 1 (1 : ZMod 3)) :=
      e.symm.polar_apply _ _
    rw [hp, hQ₀_polar]
  · intro v hv
    have hsym : e.symm (e ⟨v, hv⟩) =
        (e ⟨v, hv⟩) 0 • a + (e ⟨v, hv⟩) 1 • b := by
      conv_lhs => rw [ffE8Hyp_fin2_decomp (e ⟨v, hv⟩)]
      rw [map_add, map_smul, map_smul]
    have hfull : (⟨v, hv⟩ : fixSp t) =
        (e ⟨v, hv⟩) 0 • a + (e ⟨v, hv⟩) 1 • b := by
      conv_lhs => rw [← e.symm_apply_apply (⟨v, hv⟩ : fixSp t)]
      exact hsym
    exact ⟨(e ⟨v, hv⟩) 0, (e ⟨v, hv⟩) 1, by simpa using congrArg Subtype.val hfull⟩

theorem ffE8Hyp_comm (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (hd : invDim t = 4)
    (hs : invSign t = 1) {g h : OGroup Q} (hg : ∀ v ∈ fixSp t, (g : V ≃ₗ[ZMod 3] V) v ∈ fixSp t)
    (hh : ∀ v ∈ fixSp t, (h : V ≃ₗ[ZMod 3] V) v ∈ fixSp t) :
    ∀ v ∈ fixSp t, (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) v) =
      (h : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v) := by
  obtain ⟨a, b, ha, hb, hQa, hQb, hpol, hspan⟩ :=
    ffE8Hyp_exists_ab hQ hdim hsgn htt hd hs
  have hpm : ∀ (g : OGroup Q),
      (∀ v ∈ fixSp t, (g : V ≃ₗ[ZMod 3] V) v ∈ fixSp t) →
      (((g : V ≃ₗ[ZMod 3] V) a = a ∨ (g : V ≃ₗ[ZMod 3] V) a = -a) ∧
       ((g : V ≃ₗ[ZMod 3] V) b = b ∨ (g : V ≃ₗ[ZMod 3] V) b = -b)) := by
    intro g hg
    have hga : (g : V ≃ₗ[ZMod 3] V) a ∈ fixSp t := hg a ha
    obtain ⟨x, y, hxy⟩ := hspan ((g : V ≃ₗ[ZMod 3] V) a) hga
    have hQga : Q ((g : V ≃ₗ[ZMod 3] V) a) = 1 := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.2 a, hQa]
    have hexpa : Q (x • a + y • b) = x ^ 2 - y ^ 2 := by
      simp only [QuadraticMap.map_add, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right, hQa, hQb, hpol, smul_eq_mul]
      ring
    have h1a : x ^ 2 - y ^ 2 = 1 := by
      rw [← hexpa, ← hxy]
      exact hQga
    obtain ⟨hy, hx⟩ := ffE8Hyp_sq_sub_sq_one x y h1a
    have hgb : (g : V ≃ₗ[ZMod 3] V) b ∈ fixSp t := hg b hb
    obtain ⟨x', y', hx'y'⟩ := hspan ((g : V ≃ₗ[ZMod 3] V) b) hgb
    have hQgb : Q ((g : V ≃ₗ[ZMod 3] V) b) = -1 := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.2 b, hQb]
    have hexpb : Q (x' • a + y' • b) = x' ^ 2 - y' ^ 2 := by
      simp only [QuadraticMap.map_add, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right, hQa, hQb, hpol, smul_eq_mul]
      ring
    have h1b : x' ^ 2 - y' ^ 2 = -1 := by
      rw [← hexpb, ← hx'y']
      exact hQgb
    obtain ⟨hx'0, hy'⟩ := ffE8Hyp_sq_sub_sq_neg x' y' h1b
    constructor
    · rcases hx with hx | hx
      · left; rw [hxy, hy, hx]; simp
      · right; rw [hxy, hy, hx]; simp
    · rcases hy' with hy' | hy'
      · left; rw [hx'y', hx'0, hy']; simp
      · right; rw [hx'y', hx'0, hy']; simp
  obtain ⟨hga, hgb⟩ := hpm g hg
  obtain ⟨hha, hhb⟩ := hpm h hh
  have hca : (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) a) =
      (h : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) a) := by
    rcases hga with h1 | h1 <;> rcases hha with h2 | h2 <;> simp [h1, h2, map_neg, neg_neg]
  have hcb : (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) b) =
      (h : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) b) := by
    rcases hgb with h1 | h1 <;> rcases hhb with h2 | h2 <;> simp [h1, h2, map_neg, neg_neg]
  intro v hv
  obtain ⟨p, q, hpq⟩ := hspan v hv
  calc (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) v)
      = p • (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) a) +
          q • (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) b) := by
        rw [hpq]; simp only [map_add, map_smul]
    _ = p • (h : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) a) +
          q • (h : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) b) := by
        rw [hca, hcb]
    _ = (h : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v) := by
        rw [hpq]; simp only [map_add, map_smul]

end CFSG.OddStandard.SmallF3.Omega