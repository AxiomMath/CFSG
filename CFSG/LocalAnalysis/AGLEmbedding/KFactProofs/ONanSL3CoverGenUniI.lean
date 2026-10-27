module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary

variable {p f : ℕ} {F : Type} [Field F]

theorem suConj_apply_eq_of_commute (h : UnitaryFieldData p f F) {M : unitaryIsom3 h}
    {t : unitarySU p f F 3}
    (ht : (t : GL (Fin 3) F) * (M : GL (Fin 3) F) = (M : GL (Fin 3) F) * (t : GL (Fin 3) F)) :
    suConj h M t = t := by
  apply Subtype.ext
  rw [coe_suConj]
  change (M : GL (Fin 3) F) * (t : GL (Fin 3) F) * (M : GL (Fin 3) F)⁻¹ = t
  rw [← ht, mul_inv_cancel_right]

theorem closure_fixSet_eq_top_unitary_of_conj (h : UnitaryFieldData p f F) (h3 : 3 ∣ p ^ f + 1)
    (hq : 2 < p ^ f) (E : Subgroup (MulAut (unitarySU p f F 3)))
    (hEab : Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hFix : FixCube E)
    (hconj : ∀ e ∈ E, ∃ B : unitaryIsom3 h, e = suConj h B) :
    Subgroup.closure (fixSet E) = ⊤ := by
  classical
  have hfin := h.finite
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨a, hakernot, s, hs⟩ := SL3LiftUnitary.exists_inner_of_index h h3 (E.subtype)
    (fun a => hconj a a.2) (by
      have : Nat.card (E.subtype : E →* MulAut (unitarySU p f F 3)).ker = 1 := by
        rw [Subgroup.ker_subtype, Subgroup.card_bot]
      omega)
  set e₁ : MulAut (unitarySU p f F 3) := (a : MulAut (unitarySU p f F 3)) with he₁
  have he₁E : e₁ ∈ E := a.2
  have he₁1 : e₁ ≠ 1 := fun hh => hakernot (by
    rw [MonoidHom.mem_ker]
    exact hh)
  have hs' : ∀ t, e₁ t = s * t * s⁻¹ := hs
  have he₁conj : e₁ = MulAut.conj s := MulEquiv.ext fun t => by
    rw [MulAut.conj_apply]
    exact hs' t
  let B₁ : unitaryIsom3 h := ⟨(s : GL (Fin 3) F), unitarySU_le_unitaryIsom3 s.2⟩
  have hB₁ : e₁ = suConj h B₁ := by
    refine MulEquiv.ext fun t => ?_
    apply Subtype.ext
    rw [hs' t, coe_suConj]
    rfl
  obtain ⟨e₂, he₂E, he₂not⟩ := exists_mem_not_mem_zpowers hEab hEcard he₁E
  obtain ⟨B₂, hB₂⟩ := hconj e₂ he₂E
  have he₂3 : e₂ ^ 3 = 1 := hEab.2 e₂ he₂E
  have he₁3 : e₁ ^ 3 = 1 := hEab.2 e₁ he₁E
  have hcomm : e₁ * e₂ = e₂ * e₁ :=
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨e₂, he₂E⟩)
  set w' : unitarySU p f F 3 := s⁻¹ * e₂ s with hw'
  have hw'center : w' ∈ Subgroup.center (unitarySU p f F 3) := by
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨t', rfl⟩ := e₂.surjective t
    have h1 : e₁ (e₂ t') = e₂ (e₁ t') :=
      congrArg (fun m : MulAut (unitarySU p f F 3) => m t') hcomm
    rw [hs' (e₂ t'), hs' t', map_mul, map_mul, map_inv] at h1
    calc e₂ t' * w' = s⁻¹ * (s * e₂ t' * s⁻¹) * e₂ s := by rw [hw']; group
      _ = s⁻¹ * (e₂ s * e₂ t' * (e₂ s)⁻¹) * e₂ s := by rw [h1]
      _ = w' * e₂ t' := by rw [hw']; group
  have hw'sc : w' ∈ unitaryScalars h 3 := by
    rw [← center_unitarySU_three (h := h) hq]
    exact hw'center
  obtain ⟨c, hcN, hc3, hcw'⟩ := hw'sc
  have hθs : e₂ s = s * w' := by rw [hw']; group
  have hconjB₂ : ∀ t : unitarySU p f F 3, ((e₂ t : unitarySU p f F 3) : GL (Fin 3) F) =
      (B₂ : GL (Fin 3) F) * t * (B₂ : GL (Fin 3) F)⁻¹ := fun t => by
    rw [hB₂, coe_suConj]
    rfl
  have hGL : (B₂ : GL (Fin 3) F) * (s : GL (Fin 3) F) * (B₂ : GL (Fin 3) F)⁻¹ =
      (s : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hconjB₂ s, hθs]
    change (s : GL (Fin 3) F) * (w' : GL (Fin 3) F) = _
    rw [hcw']
  have hdet₁ : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    ((mem_unitarySU_iff h).1 s.2).1
  let ssl : SpecialLinearGroup (Fin 3) F :=
    ⟨((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hdet₁⟩
  have hc3' : (c : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hmat : ((B₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (((B₂ : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hGL
    simp only [Units.val_mul, coe_scalar_eq_smul] at this
    rw [this, Matrix.mul_smul, Matrix.mul_one]
  have hc1 : c = 1 := by
    by_contra hc1
    have hc1' : (c : F) ≠ 1 := fun hh => hc1 (Units.ext hh)
    have hs3 : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 :=
      cube_eq_one_of_conj_eq_smul ssl B₂ hc3' hc1' hmat
    have hs3' : s ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      simpa using hs3
    have hfix := hFix e₂ he₂E s hs3' (he₁conj ▸ he₁E)
    have hw'1 : w' = 1 := by
      rw [hfix] at hθs
      exact (mul_eq_left.1 hθs.symm)
    apply hc1
    have h00 : ((w' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by rw [hw'1]; simp
    rw [hcw', coe_scalar_eq_smul] at h00
    apply Units.ext
    simpa using h00
  have hcommg : (B₂ : GL (Fin 3) F) * (s : GL (Fin 3) F) =
      (s : GL (Fin 3) F) * (B₂ : GL (Fin 3) F) := by
    rw [hc1, map_one, mul_one] at hGL
    exact mul_inv_eq_iff_eq_mul.1 hGL
  have hB₁3 : suConj h B₁ ^ 3 = 1 := by rw [← hB₁]; exact he₁3
  have hB₂3 : suConj h B₂ ^ 3 = 1 := by rw [← hB₂]; exact he₂3
  obtain ⟨c₀, hc₀N, hc₀⟩ := exists_scalar_pow_three h hB₁3
  obtain ⟨c₂, hc₂N, hc₂⟩ := exists_scalar_pow_three h hB₂3
  have hs3 : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c₀ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hc₀
    rw [coe_scalar_eq_smul, Units.val_pow_eq_pow_val] at this
    exact this
  have hg3 : ((B₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c₂ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hc₂
    rw [coe_scalar_eq_smul, Units.val_pow_eq_pow_val] at this
    exact this
  obtain ⟨ωu, hωu⟩ : ∃ ω : Fˣ, orderOf ω = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply exists_prime_orderOf_dvd_card' 3
    rw [Nat.card_units, h.card_eq_sq]
    have hq1 : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (p ^ f) 1
      simpa [sq] using this.symm.symm
    rw [hq1]
    exact Dvd.dvd.mul_right h3 _
  have hω3 : (ωu : F) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ωu
    rw [hωu] at this
    simpa [← Units.val_pow_eq_pow_val] using congrArg Units.val this
  have hω1 : (ωu : F) ≠ 1 := by
    intro hh
    have : ωu = 1 := Units.ext hh
    rw [this, orderOf_one] at hωu
    omega
  obtain ⟨η, hη⟩ := exists_cube_root_of_det_one _ hdet₁ hs3
  have hη0 : η ≠ 0 := by
    rintro rfl
    exact c₀.ne_zero (by rw [← hη]; ring)
  have hns : ∀ c : F, ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ c • 1 := by
    intro c hc
    apply he₁1
    rw [hB₁]
    refine MulEquiv.ext fun t => ?_
    apply Subtype.ext
    rw [MulAut.one_apply, coe_suConj]
    apply Units.ext
    have hcm : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [hc]; simp
    have := conj_eq_self_of_comm (M := (s : GL (Fin 3) F)) hcm
    simpa [Units.val_mul] using this
  have hsη : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (η ^ 3) • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [hη]; exact hs3
  have hs_prod := prod_sub_cube_roots ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) hω3 hω1 hsη
  have hsg' : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((B₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((B₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hcommg
    simp only [Units.val_mul] at this
    exact this.symm
  obtain ⟨b, hb⟩ := exists_cube_root_of_commute _ _ hsg' (fun j : Fin 3 => η * (ωu : F) ^ j.val)
    hs_prod hns hg3
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact c₂.ne_zero (by rw [← hb]; ring)
  let ηu : Fˣ := Units.mk0 η hη0
  let bu : Fˣ := Units.mk0 b hb0
  have hηu : ηu ^ 3 = c₀ := Units.ext (by simpa [ηu] using hη)
  have hbu : bu ^ 3 = c₂ := Units.ext (by simpa [bu] using hb)
  have hNη : h.norm (ηu : F) = 1 := norm_eq_one_of_pow_three h h3 ηu (by rw [hηu]; exact hc₀N)
  have hNb : h.norm (bu : F) = 1 := norm_eq_one_of_pow_three h h3 bu (by rw [hbu]; exact hc₂N)
  have hNinv : ∀ u : Fˣ, h.norm (u : F) = 1 → h.norm ((u⁻¹ : Fˣ) : F) = 1 := fun u hu => by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hu, inv_one]
  let t₁ : unitaryIsom3 h :=
    ⟨GeneralLinearGroup.scalar (Fin 3) ηu⁻¹, scalar_mem_unitaryIsom3 h (hNinv ηu hNη)⟩ * B₁
  let t₂ : unitaryIsom3 h :=
    ⟨GeneralLinearGroup.scalar (Fin 3) bu⁻¹, scalar_mem_unitaryIsom3 h (hNinv bu hNb)⟩ * B₂
  have ht₁ : suConj h t₁ = suConj h B₁ := by
    rw [map_mul, suConj_scalar h (hNinv ηu hNη), one_mul]
  have ht₂ : suConj h t₂ = suConj h B₂ := by
    rw [map_mul, suConj_scalar h (hNinv bu hNb), one_mul]
  have hφt₁ : e₁ = suConj h t₁ := hB₁.trans ht₁.symm
  have hφt₂ : e₂ = suConj h t₂ := hB₂.trans ht₂.symm
  have ht₁3 : ((t₁ : unitaryIsom3 h) : GL (Fin 3) F) ^ 3 = 1 := scalar_inv_mul_pow_three hc₀ hηu
  have ht₂3 : ((t₂ : unitaryIsom3 h) : GL (Fin 3) F) ^ 3 = 1 := scalar_inv_mul_pow_three hc₂ hbu
  have hcomm₁₂ : ((t₁ : unitaryIsom3 h) : GL (Fin 3) F) * (t₂ : GL (Fin 3) F) =
      (t₂ : GL (Fin 3) F) * (t₁ : GL (Fin 3) F) := by
    have hc : Commute ((t₁ : unitaryIsom3 h) : GL (Fin 3) F)
        ((t₂ : unitaryIsom3 h) : GL (Fin 3) F) :=
      Commute.mul_left
        (Commute.mul_right (commute_scalar bu⁻¹ (GeneralLinearGroup.scalar (Fin 3) ηu⁻¹))
          (commute_scalar ηu⁻¹ (B₂ : GL (Fin 3) F)).symm)
        (Commute.mul_right (commute_scalar bu⁻¹ (s : GL (Fin 3) F)) hcommg.symm)
    exact hc.eq
  have hq2 : p ^ f ≠ 2 := by omega
  have hT := closure_centralizers_unitarySU_pair (n := 2) h h3 hq2 (mem_primeFormUnitary_one t₁.2)
    (mem_primeFormUnitary_one t₂.2) hcomm₁₂ ht₁3 ht₂3
  have he₂1 : e₂ ≠ 1 := fun hh => he₂not (hh ▸ one_mem _)
  obtain ⟨hne1, hne2⟩ := mul_ne_one_of_not_mem_zpowers (a := e₁) he₂3 he₂not
  rw [eq_top_iff, ← hT]
  refine Subgroup.closure_mono ?_
  rintro x ⟨M, hM, hMx⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact ⟨e₁, he₁E, he₁1, by rw [hφt₁]; exact suConj_apply_eq_of_commute h hMx⟩
  · exact ⟨e₂, he₂E, he₂1, by rw [hφt₂]; exact suConj_apply_eq_of_commute h hMx⟩
  · refine ⟨e₁ * e₂, E.mul_mem he₁E he₂E, hne1, ?_⟩
    rw [hφt₁, hφt₂, ← map_mul]
    exact suConj_apply_eq_of_commute h (M := t₁ * t₂) hMx
  · refine ⟨e₁ * e₂ ^ 2, E.mul_mem he₁E (E.pow_mem he₂E 2), hne2, ?_⟩
    rw [hφt₁, hφt₂, ← map_pow, ← map_mul]
    exact suConj_apply_eq_of_commute h (M := t₁ * t₂ ^ 2) hMx

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
