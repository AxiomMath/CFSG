module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5aSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.QuasithinUnique.Setup.X5

open Matrix CFSG.LinearGroups.UnitaryThreeOverNine CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35

theorem two_gen_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (Θ : G ≃* G') {D P : Subgroup G}
    (h : ∃ D₁ D₂ : Subgroup G', P.map Θ.toMonoidHom ≤ D₁ ∧ P.map Θ.toMonoidHom ≤ D₂ ∧
      D₁ < D.map Θ.toMonoidHom ∧ D₂ < D.map Θ.toMonoidHom ∧ D₁ ⊔ D₂ = D.map Θ.toMonoidHom) :
    ∃ D₁ D₂ : Subgroup G, P ≤ D₁ ∧ P ≤ D₂ ∧ D₁ < D ∧ D₂ < D ∧ D₁ ⊔ D₂ = D := by
  obtain ⟨D₁, D₂, h1, h2, hD1, hD2, hgen⟩ := h
  have hmm : ∀ H : Subgroup G, (H.map Θ.toMonoidHom).map Θ.symm.toMonoidHom = H := fun H => by
    rw [Subgroup.map_map]
    have : Θ.symm.toMonoidHom.comp Θ.toMonoidHom = MonoidHom.id G :=
      MonoidHom.ext fun x => Θ.symm_apply_apply x
    rw [this, Subgroup.map_id]
  have hinj : Function.Injective Θ.symm.toMonoidHom := Θ.symm.injective
  refine ⟨D₁.map Θ.symm.toMonoidHom, D₂.map Θ.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmm P]; exact Subgroup.map_mono h1
  · rw [← hmm P]; exact Subgroup.map_mono h2
  · rw [← hmm D]; exact (Subgroup.map_lt_map_iff_of_injective hinj).mpr hD1
  · rw [← hmm D]; exact (Subgroup.map_lt_map_iff_of_injective hinj).mpr hD2
  · rw [← Subgroup.map_sup, hgen, hmm]

theorem center_eq_bot_of_simple_of_noncomm {Q : Type*} [Group Q] (hQ : IsSimpleGroup Q)
    (hnc : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases hQ.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

variable {K : Type} [Field K] (hK : Nat.card K = 9)

abbrev PSUThree : Type :=
  primeFormP (unitaryFieldData_of_card hK) ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

@[expose] noncomputable def toPSU : StatedSU 3 3 K →* PSUThree hK :=
  (QuotientGroup.mk' (normOneScalars (unitaryFieldData_of_card hK)
    (gramSU (unitaryFieldData_of_card hK) ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    3)).comp
    (MulEquiv.subgroupCongr (statedSU_eq_gramSU hK (unitaryFieldData_of_card hK))).toMonoidHom

theorem toPSU_surjective : Function.Surjective (toPSU hK) :=
  (QuotientGroup.mk'_surjective _).comp (MulEquiv.surjective _)

theorem toPSU_injective : Function.Injective (toPSU hK) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := unitaryFieldData_of_card hK
  have hmem := (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨c, hcN, hc3, hcg⟩ := hmem
  have hc4 : (c : K) ^ 4 = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hcN
    have : (c : K) * (c : K) ^ 3 = 1 := by simpa using hcN
    calc (c : K) ^ 4 = (c : K) * (c : K) ^ 3 := by ring
      _ = 1 := this
  have hc3' : (c : K) ^ 3 = 1 := by
    have := congrArg Units.val hc3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hc1 : c = 1 := by
    apply Units.ext
    calc (c : K) = (c : K) * (c : K) ^ 3 := by rw [hc3', mul_one]
      _ = (c : K) ^ 4 := by ring
      _ = 1 := hc4
  apply Subtype.ext
  apply Units.ext
  have : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) := by
    exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hcg
  rw [this, hc1, map_one]
  rfl

@[expose] noncomputable def psiBar : MulAut (PSUThree hK) :=
  primeFormFieldHom (unitaryFieldData_of_card hK) (isPrimeFormGram_one' : IsPrimeFormGram (1 : GL (Fin 3) K))
    (barAut hK)

theorem psiBar_toPSU (g : StatedSU 3 3 K) : psiBar hK (toPSU hK g) = toPSU hK (frobSU hK g) := by
  show primeFormFieldAut (unitaryFieldData_of_card hK) (isPrimeFormGram_one' : IsPrimeFormGram (1 : GL (Fin 3) K))
    (barAut hK) (QuotientGroup.mk _) = QuotientGroup.mk _
  rw [primeFormFieldAut_mk]
  rfl

theorem psiBar_mul_self : psiBar hK * psiBar hK = 1 := by
  rw [psiBar, ← map_mul, barAut_mul_self, map_one]

theorem map_psiBar_map_toPSU {A : Subgroup (StatedSU 3 3 K)}
    (hA : A.map (frobSU hK).toMonoidHom = A) :
    (A.map (toPSU hK)).map (psiBar hK).toMonoidHom = A.map (toPSU hK) := by
  rw [Subgroup.map_map]
  have : (psiBar hK).toMonoidHom.comp (toPSU hK) = (toPSU hK).comp (frobSU hK).toMonoidHom :=
    MonoidHom.ext fun g => psiBar_toPSU hK g
  rw [this, ← Subgroup.map_map, hA]

section Aut

omit hK in
theorem norm_det_eq_one_of_unitary {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    h.norm ((Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) : Kˣ) : K) = 1 := by
  have hA : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := A.2
  have hdet := congrArg Matrix.det hA
  simp only [Matrix.det_mul, Matrix.det_transpose, Units.val_one, Matrix.det_one, mul_one]
    at hdet
  have hbar : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar).det =
      h.bar ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det :=
    (RingHom.map_det h.bar _).symm
  rw [hbar] at hdet
  rw [UnitaryFieldData.norm, Matrix.GeneralLinearGroup.val_det_apply, mul_comm]
  exact hdet

theorem exists_gramSU_conj_eq
    (A : primeFormUnitary (unitaryFieldData_of_card hK) ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    ∃ s : gramSU (unitaryFieldData_of_card hK) ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      primeFormConjHom (unitaryFieldData_of_card hK) _ A =
        primeFormConjHom (unitaryFieldData_of_card hK) _ ⟨(s : GL (Fin 3) K), s.2.1⟩ := by
  have h := unitaryFieldData_of_card hK
  set u : Kˣ := Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) with hu
  have hnorm : h.norm (u : K) = 1 := norm_det_eq_one_of_unitary h A
  have hu4 : (u : K) ^ 4 = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hnorm
    calc (u : K) ^ 4 = (u : K) * (u : K) ^ 3 ^ 1 := by simp; ring
      _ = 1 := hnorm
  have hscal : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈
      primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [mem_primeFormUnitary, Matrix.GeneralLinearGroup.coe_scalar]
    have := scalar_barTranspose_mul_mul h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (u : K)
    rw [this, hnorm, one_smul]
  have hdet1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) u *
      (A : GL (Fin 3) K)) = 1 := by
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hu, ← pow_succ]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hu4
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) K) ∈
      gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [mem_gramSU_iff_unitary]
    refine ⟨mul_mem hscal A.2, ?_⟩
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet1, Units.val_one]
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  have hc : ∀ X : GL (Fin 3) K,
      Matrix.GeneralLinearGroup.scalar (Fin 3) u * X * (Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹ = X :=
    fun X => by
      rw [← (commute_scalar u X).eq, mul_assoc, mul_inv_cancel, mul_one]
  show (A : GL (Fin 3) K) * (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
    (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) K)) * (g : GL (Fin 3) K) *
      (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) K))⁻¹
  rw [_root_.mul_inv_rev, show (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) K)) *
    (g : GL (Fin 3) K) * ((A : GL (Fin 3) K)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹) =
    Matrix.GeneralLinearGroup.scalar (Fin 3) u * ((A : GL (Fin 3) K) * (g : GL (Fin 3) K) *
      (A : GL (Fin 3) K)⁻¹) * (Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹ by group, hc]

end Aut

section Main

theorem primeFormConjHom_mem_inner
    (A : primeFormUnitary (unitaryFieldData_of_card hK) ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    primeFormConjHom (unitaryFieldData_of_card hK) _ A ∈
      (MulAut.conj : PSUThree hK →* MulAut (PSUThree hK)).range := by
  obtain ⟨s, hs⟩ := exists_gramSU_conj_eq hK A
  rw [hs]
  show _ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSUThree hK)
  rw [mem_inner_primeFormP]
  exact ⟨s, rfl⟩

theorem barAut_ne_one : barAut hK ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := (unitaryFieldData_of_card hK).exists_bar_ne
  apply hc
  have := congrArg (fun φ : K ≃+* K => φ c) h1
  simpa [barAut, unitaryBarEquiv_apply] using this

theorem ringEquiv_eq_one_or_barAut (φ : K ≃+* K) : φ = 1 ∨ φ = barAut hK := by
  by_cases h1 : φ = 1
  · exact Or.inl h1
  · right
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    have hcard := (card_ringAut_and_isCyclic (p := 3) (n := 2) Nat.prime_three K
      (by rw [hK]; norm_num)).1
    have hfin : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : RingAut K)).mp hcard
    exact (huniq φ h1).trans (huniq _ (barAut_ne_one hK)).symm

theorem psiBar_not_mem_range :
    psiBar hK ∉ (MulAut.conj : PSUThree hK →* MulAut (PSUThree hK)).range := by
  have h := unitaryFieldData_of_card hK
  have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by norm_num
  have hreal := unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_one' : IsPrimeFormGram (1 : GL (Fin 3) K)) (le_refl 3) hq
  have hfac := hreal.2.2.2.2.2.1
  intro hmem
  obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ (psiBar hK)).mp hmem
  have h1 := hfac ⟨(s : GL (Fin 3) K), s.2.1⟩ 1
  have h2 := hfac 1 (barAut hK)
  rw [map_one, mul_one, ← hs] at h1
  rw [map_one, one_mul] at h2
  have h3 : psiBar hK = primeFormFieldHom h (isPrimeFormGram_one' : IsPrimeFormGram (1 : GL (Fin 3) K))
      (barAut hK) := rfl
  rw [h3, h2] at h1
  exact barAut_ne_one hK h1

theorem psi_aut_cases (α : MulAut (PSUThree hK)) :
    α ∈ (MulAut.conj : PSUThree hK →* MulAut (PSUThree hK)).range ∨
      ∃ i ∈ (MulAut.conj : PSUThree hK →* MulAut (PSUThree hK)).range, α = i * psiBar hK := by
  have h := unitaryFieldData_of_card hK
  have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by norm_num
  have hreal := unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_one' : IsPrimeFormGram (1 : GL (Fin 3) K)) (le_refl 3) hq
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := hreal.2.2.2.2.1 α
  have hAin := primeFormConjHom_mem_inner hK A
  rcases ringEquiv_eq_one_or_barAut hK φ with rfl | rfl
  · left
    rw [hA, map_one, mul_one]
    exact hAin
  · right
    exact ⟨_, hAin, hA⟩

theorem map_toPSU_top : (⊤ : Subgroup (StatedSU 3 3 K)).map (toPSU hK) = ⊤ := by
  rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (toPSU_surjective hK)]

theorem exists_two_gen_overgroups_PSUThree
    {D : Subgroup (MulAut (PSUThree hK))}
    (hD : (MulAut.conj : PSUThree hK →* MulAut (PSUThree hK)).range ≤ D)
    {P : Subgroup (MulAut (PSUThree hK))} (hP : IsSylowTwoOf P D) :
    ∃ D₁ D₂ : Subgroup (MulAut (PSUThree hK)), P ≤ D₁ ∧ P ≤ D₂ ∧ D₁ < D ∧ D₂ < D ∧
      D₁ ⊔ D₂ = D := by
  have h := unitaryFieldData_of_card hK
  have hfinS : Finite (StatedSU 3 3 K) :=
    Nat.finite_of_card_ne_zero (by rw [card_statedSU hK]; norm_num)
  have hfinQ : Finite (PSUThree hK) := Finite.of_surjective _ (toPSU_surjective hK)
  obtain ⟨i, hi⟩ := exists_units_orderOf_eq_four hK
  obtain ⟨s, t, w, hs, ht, hw⟩ := (wreath_sylow_model hK i hi).1
  obtain ⟨hS, hSyl, hPc, hAc, hBc, hgen, hAne, hBne, hPA, hPB, ⟨hfrob2, hfrob1⟩, hPfrob, hAfrob,
    hBfrob⟩ := coordinate_sylow_overgroups hK i hi s t w hs ht hw
  obtain ⟨hst, hs4, -, hinter, -, -, hsw, -, -, -, -⟩ :=
    (wreath_sylow_model hK i hi).2 s t w hs ht hw
  have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by norm_num
  have hreal := unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_one' : IsPrimeFormGram (1 : GL (Fin 3) K)) (le_refl 3) hq
  obtain ⟨ψ⟩ := hreal.1
  have hsimple : IsSimpleGroup (PSUThree hK) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    have := (CFSG.ClassicalGroups.Unitary.fam_unitary_projective_simple K 3 1
      (by rw [hK]; norm_num) 3 le_rfl (by norm_num)).2.2
    exact MulEquiv.isSimpleGroup (ψ.trans (unitaryPSUEquiv h (by norm_num)))
  have hnc : ∃ a b : PSUThree hK, a * b ≠ b * a := by
    refine ⟨toPSU hK s, toPSU hK w, fun hc => ?_⟩
    have hc' : s * w = w * s := toPSU_injective hK (by rw [map_mul, map_mul, hc])
    have : w⁻¹ * s * w = s := by
      calc w⁻¹ * s * w = w⁻¹ * (s * w) := mul_assoc _ _ _
        _ = w⁻¹ * (w * s) := by rw [hc']
        _ = s := inv_mul_cancel_left _ _
    rw [this] at hsw
    have hmem : s ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers t :=
      ⟨Subgroup.mem_zpowers s, hsw ▸ Subgroup.mem_zpowers s⟩
    rw [hinter, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hs4
    omega
  have hZ := center_eq_bot_of_simple_of_noncomm hsimple hnc
  have hX₁ : (pointStab hK (coordLine hK 0)).map (toPSU hK) ≠ ⊤ := by
    intro hX
    apply hAne
    exact Subgroup.map_injective (toPSU_injective hK) (hX.trans (map_toPSU_top hK).symm)
  have hX₂ : (frameStab hK (coordFrame hK)).map (toPSU hK) ≠ ⊤ := by
    intro hX
    apply hBne
    exact Subgroup.map_injective (toPSU_injective hK) (hX.trans (map_toPSU_top hK).symm)
  have hXgen : (pointStab hK (coordLine hK 0)).map (toPSU hK) ⊔
      (frameStab hK (coordFrame hK)).map (toPSU hK) = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_toPSU_top]
  have hP₀ : IsSylowTwoOf ((Subgroup.closure {s, t, w}).map (toPSU hK)) ⊤ := by
    have := isSylowTwoOf_map_of_injective (toPSU_injective hK) hSyl
    rwa [map_toPSU_top] at this
  exact exists_two_gen_overgroups_of_aut hZ hX₁ hX₂ hXgen (Subgroup.map_mono hPA)
    (Subgroup.map_mono hPB) hP₀ (psiBar_mul_self hK) (psiBar_not_mem_range hK)
    (map_psiBar_map_toPSU hK hAfrob) (map_psiBar_map_toPSU hK hBfrob)
    (map_psiBar_map_toPSU hK hPfrob) (psi_aut_cases hK) hD hP

end Main

theorem unitary_three_at_three_overgroups_not_minimal {E : Type} [Group E] [Finite E]
    (hE : CFSG.Blueprint.LieModel E .PSU 3 3 1)
    {D : Subgroup (MulAut E)} (hD : (MulAut.conj : E →* MulAut E).range ≤ D)
    {P : Subgroup (MulAut E)} (hP : IsSylowTwoOf P D) :
    ∃ D₁ D₂ : Subgroup (MulAut E), P ≤ D₁ ∧ P ≤ D₂ ∧ D₁ < D ∧ D₂ < D ∧ D₁ ⊔ D₂ = D := by
  rcases hE with ⟨-, hmodel⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩
  · obtain ⟨-, K, hKf, hKfin, hcardK, ⟨e⟩⟩ := hmodel
    let _ := hKf
    have hK : Nat.card K = 9 := by rw [hcardK]; norm_num
    have h := unitaryFieldData_of_card hK
    have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by norm_num
    have hreal := unitary_prime_form_full_semilinear_realization h
      (isPrimeFormGram_one' : IsPrimeFormGram (1 : GL (Fin 3) K)) (le_refl 3) hq
    obtain ⟨ψ⟩ := hreal.1
    let θ : E ≃* PSUThree hK :=
      (e.trans (unitaryPSUEquiv h (by norm_num)).symm).trans ψ.symm
    have hfinS : Finite (StatedSU 3 3 K) :=
      Nat.finite_of_card_ne_zero (by rw [card_statedSU hK]; norm_num)
    have hfinQ : Finite (PSUThree hK) := Finite.of_surjective _ (toPSU_surjective hK)
    let Θ : MulAut E ≃* MulAut (PSUThree hK) := MulAut.congr θ
    have hconj : ∀ x : E, Θ (MulAut.conj x) = MulAut.conj (θ x) := fun x => by
      apply MulEquiv.ext; intro y
      change θ (x * θ.symm y * x⁻¹) = θ x * y * (θ x)⁻¹
      rw [map_mul, map_mul, map_inv, θ.apply_symm_apply]
    have hD' : (MulAut.conj : PSUThree hK →* MulAut (PSUThree hK)).range ≤
        D.map Θ.toMonoidHom := by
      rintro _ ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := θ.surjective q
      exact ⟨MulAut.conj x, hD ⟨x, rfl⟩, hconj x⟩
    have hP' : IsSylowTwoOf (P.map Θ.toMonoidHom) (D.map Θ.toMonoidHom) :=
      isSylowTwoOf_map_of_injective Θ.injective hP
    exact two_gen_of_mulEquiv Θ (exists_two_gen_overgroups_PSUThree hK hD' hP')
  all_goals exact absurd h3 (by norm_num)

end CFSG.QuasithinUnique.Setup.X5
