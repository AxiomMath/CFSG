module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292NBasics
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonEmb

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292N

open CFSG.Open Subgroup Matrix
open CFSG.RankThree.PartTwo.Sec4 hiding diagHom coe_diagHom diagHom_injective
open CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem isDiag_of_mul_diagonal_comm {d : Fin 3 → K} (hd : ∀ i j, i ≠ j → d i ≠ d j)
    {M : Matrix (Fin 3) (Fin 3) K} (h : M * diagonal d = diagonal d * M) : M.IsDiag := by
  intro i j hij
  have e := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at e
  have h' : (d i - d j) * M i j = 0 := by linear_combination (-1 : K) * e
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (hd i j hij))

theorem tau_entries_ne {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (i j : Fin 3) (hij : i ≠ j) :
    (![τ, τ ^ 2, 1] : Fin 3 → K) i ≠ ![τ, τ ^ 2, 1] j := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | simp [hτ1, hτ2, hττ2, Ne.symm hτ1, Ne.symm hτ2, Ne.symm hττ2]

theorem conj_inv_pow (g x : GL (Fin 3) K) (n : ℕ) : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  have h := (MulAut.conj g⁻¹).toMonoidHom.map_pow x n
  simpa [MulAut.conj_apply] using h.symm

theorem det_conj_inv (g x : GL (Fin 3) K) :
    GeneralLinearGroup.det (g⁻¹ * x * g) = GeneralLinearGroup.det x := by
  rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det g)⁻¹, inv_mul_cancel_right]

theorem det_eq_one_of_mem_slPi (hK : PiField π p f K) {x : GL (Fin 3) K}
    (hx : x ∈ slPi π 3 (p ^ f) K) : GeneralLinearGroup.det x = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_one]
  exact ((mem_slPi_iff hπ).1 hx).2

theorem exists_mem_not_scalar (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {E : Subgroup (GL (Fin 3) K)} (hEs : E ≤ slPi π 3 (p ^ f) K) (hE9 : Nat.card E = 9) :
    ∃ e ∈ E, e ∉ StatedScalars (Fin 3) K := by
  have := hK.finite
  by_contra hall
  push Not at hall
  set φ : ↥(rootsOfUnity 3 K) →* GL (Fin 3) K :=
    (GeneralLinearGroup.scalar (Fin 3)).comp (rootsOfUnity 3 K).subtype
  have hle : E ≤ φ.range := by
    intro x hx
    obtain ⟨c, rfl⟩ := hall x hx
    have hdet := det_eq_one_of_mem_slPi hK (hEs hx)
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
    exact ⟨⟨c, (mem_rootsOfUnity _ _).2 hdet⟩, rfl⟩
  have h1 := Subgroup.card_le_of_le hle
  have h2 : Nat.card φ.range ≤ Nat.card (rootsOfUnity 3 K) :=
    Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  rw [card_rootsOfUnity_three hK hq] at h2
  omega

theorem exists_glPi_eq_conjTorus (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {E : Subgroup (GL (Fin 3) K)} (hEs : E ≤ slPi π 3 (p ^ f) K) (hEa : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) : ∃ g ∈ glPi π 3 (p ^ f) K, E = conjTorus 3 g := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨e, heE, hes⟩ := exists_mem_not_scalar hK hq hEs hE9
  have heH : e ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ (hEs heE)
  have he3 : e ^ 3 = 1 := hEa.2 e heE
  obtain ⟨y, ⟨z, hz, hyz⟩, g, hg, hD⟩ := exists_diag_normal_form hK hq hτ hτ1 heH hes
    (μ := 1) (by rw [one_pow, map_one]; exact he3)
  obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  have hzc : ∀ x : GL (Fin 3) K, x * z = z * x := fun x =>
    commute_of_mem_statedScalars ⟨ξ, hξ⟩ x
  have hdiagTau : g⁻¹ * y * g = diagTau hτ := by
    rcases hD with hD | ⟨ε, hε, hD⟩
    · exact hD
    · exfalso
      have hε3 : (ε : K) ^ 3 = 1 := by
        rcases hε with h | h
        · rw [h, hτ]
        · rw [h, ← pow_mul, mul_comm, pow_mul, hτ, one_pow]
      have hy3 : y ^ 3 = 1 := by
        have h1 : g⁻¹ * y ^ 3 * g = 1 := by rw [← conj_inv_pow, hD, diagE_pow_three hε3]
        calc y ^ 3 = g * (g⁻¹ * y ^ 3 * g) * g⁻¹ := by group
          _ = 1 := by rw [h1]; group
      have hz3 : z ^ 3 = 1 := by
        have hc : Commute e z := hzc e
        rw [hyz, hc.mul_pow, he3, one_mul] at hy3
        exact hy3
      have hξ3 : ξ ^ 3 = 1 := by
        have h1 : GeneralLinearGroup.scalar (Fin 3) (ξ ^ 3) = 1 := by rw [map_pow, hξ, hz3]
        have h2 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) 0 0) h1
        simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
          Units.val_one, Matrix.one_apply_eq] at h2
        exact Units.ext h2
      have hdety : GeneralLinearGroup.det y = 1 := by
        rw [hyz, map_mul, det_eq_one_of_mem_slPi hK (hEs heE), one_mul, ← hξ,
          GeneralLinearGroup.det_scalar, Fintype.card_fin, hξ3]
      have hdetε : ε = 1 := by
        rw [← det_diagE ε, ← hD, det_conj_inv, hdety]
      rcases hε with h | h
      · exact hτ1 (by rw [← h, hdetε, Units.val_one])
      · have hτ0 : τ ≠ 0 := by
          rintro rfl
          simp at hτ
        apply hτ1
        have h2 : τ ^ 2 = 1 := by rw [← h, hdetε, Units.val_one]
        calc τ = τ ^ 3 / τ ^ 2 := by field_simp
          _ = 1 := by rw [hτ, h2, div_one]
  have hEdiag : ∀ x ∈ E, g⁻¹ * x * g ∈ torus3 (rootsOfUnity 3 K) := by
    intro x hx
    have : IsMulCommutative E := hEa.1
    have hxe : x * e = e * x := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨e, heE⟩)
    have hxy : x * y = y * x := by
      rw [hyz, ← mul_assoc, hxe, mul_assoc, hzc x, ← mul_assoc]
    have hM : ((g⁻¹ * x * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![τ, τ ^ 2, 1] =
        diagonal ![τ, τ ^ 2, 1] * ((g⁻¹ * x * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← coe_diagTau_eq_diagonal hτ, ← hdiagTau, ← Units.val_mul, ← Units.val_mul]
      congr 1
      calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
        _ = g⁻¹ * (y * x) * g := by rw [hxy]
        _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
    refine mem_torus3_of_isDiag (by norm_num)
      (isDiag_of_mul_diagonal_comm (tau_entries_ne hτ hτ1) hM) ?_ ?_
    · rw [← GeneralLinearGroup.val_det_apply, det_conj_inv, det_eq_one_of_mem_slPi hK (hEs hx),
        Units.val_one]
    · rw [conj_inv_pow, hEa.2 x hx, mul_one, inv_mul_cancel]
  have hle : E ≤ conjTorus 3 g := fun x hx => mem_conjTorus.2 (hEdiag x hx)
  refine ⟨g, hg, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [card_conjTorus, card_torus3_three hK hq, hE9]

theorem det_pow_succ_of_mem_glPi_false (hU : UnitaryFieldData p f K) {x : GL (Fin 3) K}
    (hx : x ∈ glPi false 3 (p ^ f) K) :
    ((x : Matrix (Fin 3) (Fin 3) K).det) ^ (p ^ f + 1) = 1 := by
  have h1 := congrArg Matrix.det ((mem_glPi_false hU).1 hx)
  have hmap : ((x : Matrix (Fin 3) (Fin 3) K).map hU.bar).det =
      hU.bar (x : Matrix (Fin 3) (Fin 3) K).det :=
    (RingHom.map_det hU.bar _).symm
  rw [det_mul, det_transpose, hmap, hU.bar_apply, det_one, ← pow_succ] at h1
  exact h1

theorem exists_slPi_map_conjTorus (hK : PiField π p f K) {g h : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hh : h ∈ glPi π 3 (p ^ f) K) :
    ∃ a ∈ slPi π 3 (p ^ f) K,
      (conjTorus 3 g).map (MulAut.conj a).toMonoidHom = conjTorus 3 h := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set δ : Kˣ := GeneralLinearGroup.det g * (GeneralLinearGroup.det h)⁻¹ with hδ
  set D : GL (Fin 3) K := diagHom 3 ![δ, 1, 1] with hD
  have hdetD : GeneralLinearGroup.det D = δ := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, hD, det_diagHom_three]
    simp
  have hDH : D ∈ glPi π 3 (p ^ f) K := by
    cases π
    · have hU := hK.unitary
      have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hK.prime.ne_zero
      have hδn : (δ : K) ^ (p ^ f + 1) = 1 := by
        have hgn := det_pow_succ_of_mem_glPi_false hU hg
        have hhn := det_pow_succ_of_mem_glPi_false hU hh
        rw [hδ, Units.val_mul, Units.val_inv_eq_inv_val, mul_pow, inv_pow,
          GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, hgn, hhn, inv_one,
          mul_one]
      refine CFSG.LocalAnalysis.RankThreeUC.S15.ACore.diagHom_mem_statedGU hq0 fun i => ?_
      fin_cases i
      · exact hδn
      · simp
      · simp
    · exact mem_glPi_true _ _
  refine ⟨h * D * g⁻¹, ?_, ?_⟩
  · rw [mem_slPi_iff hπ]
    refine ⟨mul_mem (mul_mem hh hDH) (inv_mem hg), ?_⟩
    rw [← GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv, hdetD, hδ,
      mul_comm (GeneralLinearGroup.det g), ← mul_assoc, mul_inv_cancel, one_mul,
      mul_inv_cancel, Units.val_one]
  · rw [conjTorus, Subgroup.map_map]
    have e : (MulAut.conj (h * D * g⁻¹)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (h * D)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact conjTorus_mul_diagHom 3 h _

theorem exists_slPi_map_eq_threeFrame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) {v : Fin 3 → K} (hv : v ≠ 0)
    (horth : π = false → YFrameOrth (p ^ f) y v) {E : Subgroup (GL (Fin 3) K)}
    (hEs : E ≤ slPi π 3 (p ^ f) K) (hEa : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ a ∈ slPi π 3 (p ^ f) K, E.map (MulAut.conj a).toMonoidHom = threeFrame y v := by
  obtain ⟨g, hg, rfl⟩ := exists_glPi_eq_conjTorus hK hq hEs hEa hE9
  obtain ⟨P, hP, hPn⟩ := exists_glPi_frame hK hq hT hv horth
  rw [threeFrame, hPn 3 (by norm_num)]
  exact exists_slPi_map_conjTorus hK hg hP

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292N
