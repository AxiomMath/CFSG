module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGD1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec9ci_reflOf_apply {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    (hpol : ∀ i j : Fin n, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    {k : Fin n} (hk : Q (b k) ≠ 0) (m : Fin n) :
    ((reflOf Q (b k) hk : OGroup Q) : V ≃ₗ[ZMod 3] V) (b m) =
      (if m = k then (-1 : ZMod 3) else 1) • b m := by
  letI : Invertible (Q (b k)) := invertibleOfNonzero hk
  rw [reflOf_eq (b k) hk, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  by_cases hmk : m = k
  · subst hmk
    rw [if_pos rfl, TauCeti.QuadraticMap.reflection_apply_self, neg_one_smul]
  · rw [if_neg hmk, TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q (b k)
      (hpol k m (fun h => hmk h.symm)), one_smul]

private theorem sec9ci_piOrth_smul (c : ZMod 3) (x : V) :
    (piOrth Q : V ≃ₗ[ZMod 3] V) (c • x) = (-c) • x := by
  rw [coe_piOrth_apply, ← neg_smul]

private theorem sec9ci_pairCoeff {n : ℕ} {i j m : Fin n} (hij : i ≠ j) :
    (if m ∈ ({i, j} : Finset (Fin n)) then (-1 : ZMod 3) else 1) =
      (if m = j then (-1 : ZMod 3) else 1) * (if m = i then (-1 : ZMod 3) else 1) := by
  by_cases hmi : m = i
  · subst hmi
    simp [hij, Ne.symm hij]
  · by_cases hmj : m = j
    · subst hmj
      simp [hij, hmi]
    · simp [hmi, hmj]

private theorem sec9ci_piCoeff {n : ℕ} {T : Finset (Fin n)} {j : Fin n} (hj : Tᶜ = {j})
    (m : Fin n) :
    (-(if m ∈ T then (-1 : ZMod 3) else 1)) = (if m = j then (-1 : ZMod 3) else 1) := by
  by_cases hm : m ∈ T
  · have hmj : m ≠ j := by
      intro h
      have hmem : j ∈ Tᶜ := by rw [hj]; exact Finset.mem_singleton_self j
      rw [Finset.mem_compl] at hmem
      exact hmem (h ▸ hm)
    rw [if_pos hm, if_neg hmj]
    decide
  · have hmj : m = j := by
      have hmem : m ∈ Tᶜ := by rw [Finset.mem_compl]; exact hm
      rwa [hj, Finset.mem_singleton] at hmem
    rw [if_neg hm, if_pos hmj]

private theorem sec9ci_isSquare_units_zmod3 {u : (ZMod 3)ˣ} (h : IsSquare u) : u = 1 := by
  obtain ⟨w, hw⟩ := h
  have hw1 : w * w = 1 := by
    rcases aux_units_zmod3 w with h | h <;> rw [h] <;> decide
  rw [hw1] at hw
  exact hw

private theorem sec9ci_unit_eq_of_sqclass {u v : (ZMod 3)ˣ}
    (h : TauCeti.squareClassHom u * TauCeti.squareClassHom v = 1) : u = v := by
  have huv : u * v = 1 := by
    apply sec9ci_isSquare_units_zmod3
    rw [← map_mul, TauCeti.squareClassHom_apply, ofAdd_eq_one,
      TauCeti.squareClass_eq_zero_iff] at h
    exact h
  rcases aux_units_zmod3 u with rfl | rfl <;> rcases aux_units_zmod3 v with rfl | rfl
  · rfl
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · rfl

theorem sec9ci_norm_const (hQ : Q.Nondegenerate)
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1) {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod 3) V} {Ft : Subgroup (OGroup Q)} (hb : IsEvenFrame b Ft)
    (hΩ : ∀ g ∈ Ft, SimInOmegaStar hQ (phiSim Q g)) (i j : Fin n) : Q (b i) = Q (b j) := by
  by_cases hij : i = j
  · subst hij; rfl
  have hn : 3 ≤ n := by
    have h := Module.finrank_eq_card_basis b
    rw [hm.1, Fintype.card_fin] at h
    omega
  have hpol : ∀ i j : Fin n, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0 :=
    fun i j hij => IsEvenFrame.polar_eq_zero hb hn hij
  obtain ⟨g, hgFt, hgact⟩ := hb.2 ({i, j} : Finset (Fin n)) (by
    rw [Finset.card_pair hij]; exact even_two)
  have hbi : Q (b i) ≠ 0 := IsEvenFrame.map_ne_zero hQ hb hn i
  have hbj : Q (b j) ≠ 0 := IsEvenFrame.map_ne_zero hQ hb hn j
  have hpi : piOrth Q ∈ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ]
    exact ⟨by rw [hm.1]; decide, by rw [hm.1, hm.2]; decide⟩
  have hgΩ : g ∈ omegaGroup hQ := by
    obtain ⟨y, hy, hyx⟩ := hΩ g hgFt
    obtain ⟨g', hg'Ω, rfl⟩ := Subgroup.mem_map.mp hy
    have hph : phiSim Q g' = phiSim Q g := hyx
    have hker : phiSim Q (g'⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hph, inv_mul_cancel]
    rcases phiSim_eq_one_iff.mp hker with h1 | h1
    · have hgg' : g = g' := by
        have := congrArg (fun z => g' * z) h1
        simpa [mul_assoc] using this
      rw [hgg']; exact hg'Ω
    · have hgg' : g = g' * piOrth Q := by
        have := congrArg (fun z => g' * z) h1
        simpa [mul_assoc] using this
      rw [hgg']
      exact mul_mem hg'Ω hpi
  have hg_eq : g = reflOf Q (b i) hbi * reflOf Q (b j) hbj := by
    apply sec9ci_ext
    intro m
    rw [hgact m, Subgroup.coe_mul, LinearEquiv.mul_apply, sec9ci_reflOf_apply hpol hbj m,
      map_smul, sec9ci_reflOf_apply hpol hbi m, smul_smul, sec9ci_pairCoeff hij]
  have hdet : CFSG.ClassicalInvolution.detSpinorNorm hQ g = 1 := (mem_omegaGroup_iff hQ).mp hgΩ
  rw [hg_eq, map_mul] at hdet
  letI : Invertible (Q (b i)) := invertibleOfNonzero hbi
  letI : Invertible (Q (b j)) := invertibleOfNonzero hbj
  have hii : CFSG.ClassicalInvolution.detSpinorNorm hQ (reflOf Q (b i) hbi) =
      ((-1 : (ZMod 3)ˣ),
        TauCeti.squareClassHom (unitOfInvertible (Q (b i)))) := by
    rw [reflOf_eq (b i) hbi]
    exact CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal hQ (b i)
  have hjj : CFSG.ClassicalInvolution.detSpinorNorm hQ (reflOf Q (b j) hbj) =
      ((-1 : (ZMod 3)ˣ),
        TauCeti.squareClassHom (unitOfInvertible (Q (b j)))) := by
    rw [reflOf_eq (b j) hbj]
    exact CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal hQ (b j)
  rw [hii, hjj] at hdet
  have hsq : TauCeti.squareClassHom (unitOfInvertible (Q (b i))) *
      TauCeti.squareClassHom (unitOfInvertible (Q (b j))) = 1 := by
    simpa using congrArg Prod.snd hdet
  have hunit : unitOfInvertible (Q (b i)) = unitOfInvertible (Q (b j)) :=
    sec9ci_unit_eq_of_sqclass hsq
  have hQi : Q (b i) = Q (b j) := by
    have := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hunit
    simpa [val_unitOfInvertible] using this
  exact hQi

theorem sec9ci_dim_exclusive (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6)
    {x : ProjSim Q} {r r' : ℕ} (hx : SimHasDim x r) (hx' : SimHasDim x r') :
    r' = r ∨ r' = 6 - r := by
  obtain ⟨t, htt, hrt, htx⟩ := hx
  obtain ⟨t', htt', hr't', ht'x⟩ := hx'
  have hph : phiSim Q t' = phiSim Q t := ht'x.trans htx.symm
  have hker : phiSim Q (t' * t⁻¹) = 1 := by
    rw [map_mul, map_inv, hph, mul_inv_cancel]
  rcases phiSim_eq_one_iff.mp hker with h1 | h1
  · left
    have htt' : t' = t := by
      have := congrArg (fun z => z * t) h1
      simpa [mul_assoc] using this
    rw [← hr't', htt', hrt]
  · right
    have ht't : t' = piOrth Q * t := by
      have := congrArg (fun z => z * t) h1
      simpa [mul_assoc] using this
    have hdim : invDim (piOrth Q * t) = Module.finrank (ZMod 3) V - invDim t := by
      have := congrArg Prod.fst (invType_piOrth_mul hQ htt)
      simpa only [invType] using this
    rw [← hr't', ht't, hdim, hrt, h6]

theorem sec9ci_refl_of_i1 (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6) {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod 3) V} {Ft : Subgroup (OGroup Q)} (hb : IsEvenFrame b Ft)
    {x : ProjSim Q} (hx : ∀ g ∈ Ft, x * phiSim Q g = phiSim Q g * x) (h1 : SimHasDim x 1) :
    ∃ (j : Fin n) (r : OGroup Q), phiSim Q r = x ∧
      ∀ i, (r : V ≃ₗ[ZMod 3] V) (b i) = (if i = j then (-1 : ZMod 3) else 1) • b i := by
  have h6n : n = 6 := by
    have h := Module.finrank_eq_card_basis b
    rw [h6, Fintype.card_fin] at h
    omega
  have hn : 3 ≤ n := by omega
  have hsq : ∀ g ∈ Ft, g * g = 1 := by
    intro g hg
    obtain ⟨S, -, hact⟩ := hb.1 g hg
    exact sec9g_mul_self_diag hact
  have hev : ∀ g ∈ Ft, Even (invDim g) := by
    intro g hg
    obtain ⟨S, hS, hact⟩ := hb.1 g hg
    rw [sec9g_invDim_diag hact]
    exact hS
  obtain ⟨g, T, hgx, hgT⟩ := sec9t_lift_diag hQ h6 hb hn hsq hev hx
  have hT : SimHasDim x T.card :=
    ⟨g, sec9g_mul_self_diag hgT, sec9g_invDim_diag hgT, hgx⟩
  rcases sec9ci_dim_exclusive hQ h6 h1 hT with hT1 | hT5
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hT1
    refine ⟨j, g, hgx, ?_⟩
    intro m
    have hcoeff : (if m ∈ T then (-1 : ZMod 3) else 1) =
        (if m = j then (-1 : ZMod 3) else 1) := by
      by_cases hm : m ∈ T
      · have hmj : m = j := by
          have h := hm
          rw [hj, Finset.mem_singleton] at h
          exact h
        rw [if_pos hm, if_pos hmj]
      · have hmj : m ≠ j := by
          intro h
          apply hm
          rw [hj, Finset.mem_singleton]
          exact h
        rw [if_neg hm, if_neg hmj]
    rw [hgT m, hcoeff]
  · have hT5' : T.card = 5 := by omega
    have hcompl : Tᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcompl
    refine ⟨j, piOrth Q * g, ?_, ?_⟩
    · rw [map_mul, (phiSim_eq_one_iff (Q := Q)).mpr (Or.inr rfl), one_mul, hgx]
    · intro m
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hgT m, sec9ci_piOrth_smul,
        sec9ci_piCoeff hj m]

end CFSG.OddStandard.SmallF3.Omega
