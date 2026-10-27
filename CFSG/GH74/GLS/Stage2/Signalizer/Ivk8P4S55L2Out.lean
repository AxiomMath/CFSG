module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenT
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenF
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield mem_fixedSubfield)

section Torus

variable {F : Type} [Field F]

@[expose] def l2Diag (t : Fˣ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨Matrix.diagonal ![(t : F), ((t⁻¹ : Fˣ) : F)], by simp⟩

theorem l2Diag_coe (t : Fˣ) :
    ((l2Diag t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(t : F), ((t⁻¹ : Fˣ) : F)] := rfl

@[expose] def l2DiagHom : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun := l2Diag
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [l2Diag_coe]
  map_mul' s t := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [l2Diag_coe, mul_comm]

@[expose] def l2Tor : Fˣ →* PSL2 F :=
  (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp l2DiagHom

theorem l2Tor_eq_iff {s t : Fˣ} (h : l2Tor s = l2Tor t) : (s : F) = t ∨ (s : F) = -t := by
  have h1 : (l2DiagHom s)⁻¹ * l2DiagHom t ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    QuotientGroup.eq.mp h
  obtain ⟨c, hc, hct⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
  have e1 : (l2DiagHom s) * ((l2DiagHom s)⁻¹ * l2DiagHom t) = l2DiagHom t := by group
  have e2 : ((l2DiagHom s : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      Matrix.scalar (Fin 2) c = ((l2DiagHom t : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) := by
    rw [hct, ← Matrix.SpecialLinearGroup.coe_mul, e1]
  have e3 := congrFun (congrFun e2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, l2DiagHom, l2Diag_coe] at e3
  have hc2 : c ^ 2 = 1 := by simpa using hc
  have hc' : (c - 1) * (c + 1) = 0 := by linear_combination hc2
  rcases mul_eq_zero.mp hc' with h0 | h0
  · left
    have : c = 1 := by linear_combination h0
    rw [this] at e3
    simpa using e3
  · right
    have : c = -1 := by linear_combination h0
    rw [this] at e3
    linear_combination -e3

theorem fieldAut_l2Tor (σ : F ≃+* F) (t : Fˣ) :
    psl2RingEquiv σ (l2Tor t) = l2Tor (Units.map σ.toRingHom.toMonoidHom t) := by
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (l2Diag t)) = _
  rw [psl2RingEquiv_mk]
  change QuotientGroup.mk' (Subgroup.center _) _ = QuotientGroup.mk' (Subgroup.center _) (l2Diag _)
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l2Diag_coe]

theorem fieldAut_ne_neg {p : ℕ} (hp : Odd p) (σ : F ≃+* F) (hσ : σ ^ p = 1) {c : F}
    (hc : σ c ≠ c) : σ c ≠ -c := by
  intro h
  have h2 : (σ ^ 2) c = c := by
    rw [pow_two, RingAut.mul_apply, h, map_neg, h, neg_neg]
  have hk : ∀ k : ℕ, (σ ^ (2 * k)) c = c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, RingAut.mul_apply, h2, ih]
  obtain ⟨m, hm⟩ := hp
  have hσ' : σ = σ ^ (2 * (m + 1)) := by
    rw [show 2 * (m + 1) = p + 1 by omega, pow_succ, hσ, one_mul]
  exact hc (calc σ c = (σ ^ (2 * (m + 1))) c := congrArg (fun τ : F ≃+* F => τ c) hσ'
    _ = c := hk _)

end Torus

section Descent

theorem mem_of_odd_pow_eq_one {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2) {x : G}
    {n : ℕ} (hn : Odd n) (hx : x ^ n = 1) : x ∈ H := by
  obtain ⟨m, rfl⟩ := hn
  have h1 : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hx, one_mul]
  have h2 : (x ^ 2) ^ (m + 1) ∈ H := H.pow_mem (Subgroup.sq_mem_of_index_two hH x) (m + 1)
  rwa [← h1] at h2

variable {F : Type} [Field F] [Finite F]

theorem outer_conj_fieldAut {ℓ p f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = ℓ ^ f) {g : PGammaL2 F}
    (hgord : orderOf g = p) (hg : g ∉ pGammaL2PSLRange F) :
    p ∣ f ∧ ∃ (x : PGL2 F) (σ : F ≃+* F), orderOf σ = p ∧
      g = SemidirectProduct.inl x * SemidirectProduct.inr σ * (SemidirectProduct.inl x)⁻¹ ∧
      Nat.card (fixedSubfield F σ) = ℓ ^ (f / p) := by
  classical
  have hOdd : IsOddPrimePower (Nat.card F) := AutL2Facts.isOddPrimePower_of hℓ hℓ2 hf hcard
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have haE : coordinateSemilinearAction F g ∈ coordinateE F := by
    rw [← coordinateSemilinearAction_range_eq_E]
    exact ⟨g, rfl⟩
  have hao : orderOf (coordinateSemilinearAction F g) = p := by
    rw [orderOf_injective _ (coordinateSemilinearAction_injective F) g, hgord]
  have haD : coordinateSemilinearAction F g ∉ coordinateD F := by
    intro haD
    rw [← coordinatePGLAction_range_eq_D] at haD
    obtain ⟨x, hx⟩ := haD
    have hgx : g = SemidirectProduct.inl x := by
      apply coordinateSemilinearAction_injective F
      rw [coordinateSemilinearAction_inl]
      exact hx.symm
    apply hg
    have hxp : x ^ p = 1 := by
      have h1 : g ^ p = 1 := by
        rw [← hgord]
        exact pow_orderOf_eq_one g
      rw [hgx, ← map_pow] at h1
      exact SemidirectProduct.inl_injective (by simpa using h1)
    have hxR : x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
      mem_of_odd_pow_eq_one (pgl2_psl2Range_index_eq_two F hOdd) hpodd hxp
    obtain ⟨y, hy⟩ := hxR
    rw [mem_pGammaL2PSLRange_iff]
    exact ⟨y, by rw [hy, hgx]⟩
  obtain ⟨hpf, σ, hσord, ⟨d, hdD, had⟩, hfix⟩ :=
    CFSG.RankThree.LinearTwo.linear_two_prime_semilinear_field_descent hℓ hp hf F hcard haE haD
      hao
  rw [← coordinatePGLAction_range_eq_D] at hdD
  obtain ⟨x, rfl⟩ := hdD
  refine ⟨hpf, x, σ, hσord, ?_, hfix⟩
  apply coordinateSemilinearAction_injective F
  rw [map_mul, map_mul, map_inv, coordinateSemilinearAction_inl, coordinateSemilinearAction_inr]
  exact had

end Descent

section Outer

variable {Y : Type} [Group Y] {p f : ℕ}

theorem autEquiv_not_psl {F : Type} [Field F] [Finite F] (e : Y ≃* PSL2 F) {α : MulAut Y}
    (hαinn : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    AutL2Facts.autEquiv e α ∉ pGammaL2PSLRange F := by
  intro hg
  rw [← AutL2Facts.map_autEquiv_innAut e] at hg
  obtain ⟨β, hβ, hβg⟩ := Subgroup.mem_map.mp hg
  have : β = α := (AutL2Facts.autEquiv e).injective hβg
  exact hαinn (this ▸ hβ)

theorem l2_outerFalse (hp : p.Prime) (hp2 : p ≠ 2) (h : Blueprint.LieModel Y .PSL 2 p f) :
    OuterFalse p Y := by
  classical
  obtain ⟨-, hf, -, -, F, _, _, hcard, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data h
  have : Fact p.Prime := ⟨hp⟩
  intro α hαinn hαp _hS hHH
  have hα1 : α ≠ 1 := fun h1 => hαinn (h1 ▸ (MonoidHom.range _).one_mem)
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hgord : orderOf (AutL2Facts.autEquiv e α) = p := by
    rw [MulEquiv.orderOf_eq]
    exact hαord
  have hgnot := autEquiv_not_psl e hαinn
  obtain ⟨hpf, x, σ, hσord, hconj, hfix⟩ := outer_conj_fieldAut hp hp2 hp hp2 hf hcard hgord hgnot
  have hα : α = (AutL2Facts.autEquiv e).symm (SemidirectProduct.inl x) *
      (AutL2Facts.autEquiv e).symm (SemidirectProduct.inr σ) *
      ((AutL2Facts.autEquiv e).symm (SemidirectProduct.inl x))⁻¹ := by
    have := congrArg (AutL2Facts.autEquiv e).symm hconj
    simpa only [MulEquiv.symm_apply_apply, map_mul, map_inv] using this
  have hff : ∀ y : Y, e ((AutL2Facts.autEquiv e).symm (SemidirectProduct.inr σ) y) =
      psl2RingEquiv σ (e y) := by
    intro y
    have := AutL2Facts.semilinearAction_autEquiv_apply e
      ((AutL2Facts.autEquiv e).symm (SemidirectProduct.inr σ)) y
    rw [MulEquiv.apply_symm_apply, semilinearAction_inr, psl2FieldAut_apply] at this
    exact this.symm
  have he1 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hcard' : Nat.card F = (p ^ (f / p)) ^ p := by
    rw [hcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have hfix' : Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) =
      p ^ (f / p) := by
    have : CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ = fixedSubfield F σ := by
      ext z
      rw [mem_fixedSubfield, RingHom.mem_eqLocusField]
      simp
    rw [this]
    exact hfix
  obtain ⟨r, c, hr, hr2, hrp, hcr, hσc⟩ := exists_torsion_moved hp hp2 he1 σ hcard' hfix'
  have hσp : σ ^ p = 1 := hσord ▸ pow_orderOf_eq_one σ
  let T₀ : Subgroup (PSL2 F) := (rootsOfUnity r F).map l2Tor
  let T : Subgroup Y := T₀.map e.symm.toMonoidHom
  have hT₀ : IsPGroup r ↥T₀ := by
    rintro ⟨_, t, ht, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, (mem_rootsOfUnity _ _).mp ht, map_one]
  have hT : IsPGroup r ↥T := hT₀.map e.symm.toMonoidHom
  have hfT : ∀ z ∈ T, (AutL2Facts.autEquiv e).symm (SemidirectProduct.inr σ) z ∈ T := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨l2Tor (Units.map σ.toRingHom.toMonoidHom t), ⟨_, ?_, rfl⟩, ?_⟩
    · have ht' := (mem_rootsOfUnity _ _).mp ht
      refine (mem_rootsOfUnity _ _).mpr ?_
      rw [← map_pow, ht', map_one]
    · apply e.injective
      rw [hff]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact (fieldAut_l2Tor σ t).symm
  have hcT : e.symm (l2Tor c) ∈ T := ⟨l2Tor c, ⟨c, (mem_rootsOfUnity _ _).mpr hcr, rfl⟩, rfl⟩
  refine false_of_torus_moved hα hr hr2 hrp hT hfT hcT ?_ hHH
  intro hfix
  have h1 := hff (e.symm (l2Tor c))
  rw [hfix, MulEquiv.apply_symm_apply, fieldAut_l2Tor] at h1
  rcases l2Tor_eq_iff h1 with h2 | h2
  · exact hσc h2.symm
  · have h4 : (c : F) = -σ (c : F) := h2
    exact fieldAut_ne_neg (hp.odd_of_ne_two hp2) σ hσp hσc (by linear_combination h4)

end Outer

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
