module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUQ8

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem fieldHom_mem_range_subfieldPSU (h : UnitaryFieldData ℓ f K)
    {σ τ : K ≃+* K} (hστ : σ * τ = τ * σ) {e : ℕ} (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)
    {t : primeFormP h (idGram K 3)} (ht : t ∈ (subfieldPSU h h₀ hbar 3).range) :
    primeFormFieldHom h isPrimeFormGram_one τ t ∈ (subfieldPSU h h₀ hbar 3).range := by
  obtain ⟨s, rfl⟩ := ht
  induction s using QuotientGroup.induction_on with
  | H s₀ =>
    set s : GL (Fin 3) K := subfieldGL (fixSubfield σ) 3
      (s₀ : GL (Fin 3) (fixSubfield σ)) with hs
    have hσs : glAut σ s = s := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      rw [coe_glAut, Matrix.map_apply, hs, coe_subfieldGL, Matrix.map_apply]
      exact (((s₀ : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ)) i j).2
    have hmem : glAut τ s ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      (primeFormFieldSU h isPrimeFormGram_one τ
        ⟨s, subfieldGL_mem_gramSU h h₀ hbar 3 s₀.2⟩).2
    have hfix : glAut σ (glAut τ s) = glAut τ s := by
      rw [← MulAut.mul_apply, ← map_mul, hστ, map_mul, MulAut.mul_apply, hσs]
    obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed 3 hfix
    have hg₀SU := mem_gramSU_of_subfieldGL h 3 h₀ hbar (hg₀ ▸ hmem)
    refine ⟨((⟨g₀, hg₀SU⟩ : gramSU h₀ ((1 : GL (Fin 3) (fixSubfield σ)) :
      Matrix (Fin 3) (Fin 3) (fixSubfield σ))) : primeFormP h₀ _), ?_⟩
    rw [subfieldPSU_mk, subfieldPSU_mk]
    change _ = primeFormFieldAut h isPrimeFormGram_one τ _
    rw [primeFormFieldAut_mk]
    congr 1
    exact Subtype.ext hg₀

theorem eq_one_of_q8_aut (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {D H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H)
    (hy : primeFormFieldHom h isPrimeFormGram_one σ ∈ D)
    {g : MulAut (primeFormP h (idGram K 3))} (hg : g ∈ localDeltaIn 3 H D) : g = 1 := by
  have hn : 3 ≤ 3 := le_rfl
  have hq : ¬(3 = 3 ∧ 2 ^ 3 = 2) := by decide
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Finite K := h.finite
  let h₀ : UnitaryFieldData 2 1 (fixSubfield σ) := fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  set y := primeFormFieldHom h hC σ with hydef
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ
    omega
  have hy1 : y ≠ 1 := by
    intro h1
    exact hσ1 (primeFormFieldHom_injective h 3 hn hq (by rw [← hydef, h1, map_one]))
  have hgN := le_core_of_mem_localDeltaIn hg hy hy1
  have hcomm := commute_of_mem_localDeltaIn hg hy
  have hcop := coprime_orderOf_of_mem_localDeltaIn hp hg hy hy1
  have hinj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h hC hn hq
  have hσfix : ∀ c ∈ fixSubfield σ, σ c = c := fun c hc => hc
  obtain ⟨τ, ⟨A, hA⟩, -⟩ :=
    (unitary_prime_form_full_semilinear_realization h hC hn hq).2.2.2.2.1 g
  have hστ : σ * τ = τ * σ := ringAut_mul_comm K σ τ
  have hfτ : primeFormFieldHom h hC τ * y = y * primeFormFieldHom h hC τ := by
    rw [hydef, ← map_mul, ← map_mul, hστ]
  have hAcomm : primeFormConjHom h (idGram K 3) A * y = y * primeFormConjHom h (idGram K 3) A := by
    rw [hA] at hcomm
    have h1 : primeFormConjHom h (idGram K 3) A * (primeFormFieldHom h hC τ * y) =
        y * primeFormConjHom h (idGram K 3) A * primeFormFieldHom h hC τ := by
      rw [← mul_assoc]; exact hcomm
    rw [hfτ, ← mul_assoc] at h1
    exact mul_right_cancel h1
  have hfixT := apply_eq_of_mem_gLAPPrimeCoreOf hinj hH hgN (subfieldPSU h h₀ hbar 3).range
    (fun t ht => primeFormFieldHom_apply_of_mem_range h 3 h₀ hbar hσfix ht)
    (fun t ht => by
      rw [hA, MulAut.mul_apply]
      exact apply_mem_range_subfieldPSU h hq h₀ hbar A hAcomm
        (fieldHom_mem_range_subfieldPSU h hστ h₀ hbar ht))
    (hO_range h h₀ hbar)
  exact eq_one_of_fixes_range h h₀ hbar hcop hfixT

theorem localDeltaIn_eq_bot_of_q8_of_mem (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {D H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H) {x : MulAut (primeFormP h (idGram K 3))}
    (hx : x ∈ D) {M : primeFormUnitary h (idGram K 3)}
    (hM : (primeFormConjHom h (idGram K 3) M)⁻¹ * x * primeFormConjHom h (idGram K 3) M =
      primeFormFieldHom h isPrimeFormGram_one σ) :
    localDeltaIn 3 H D = ⊥ := by
  set c : MulAut (primeFormP h (idGram K 3)) := primeFormConjHom h (idGram K 3) M with hc
  let φ : MulAut (primeFormP h (idGram K 3)) ≃* MulAut (primeFormP h (idGram K 3)) :=
    MulAut.conj c⁻¹
  have hφ : ∀ a, φ a = c⁻¹ * a * c := fun a => by
    simp [φ]
  have hy' : primeFormFieldHom h isPrimeFormGram_one σ ∈ D.map φ.toMonoidHom :=
    Subgroup.mem_map.2 ⟨x, hx, by rw [MulEquiv.toMonoidHom_eq_coe]; simpa [hφ] using hM⟩
  have hH' : innerAut (primeFormP h (idGram K 3)) ≤ H.map φ.toMonoidHom := by
    intro z hz
    obtain ⟨g, rfl⟩ := hz
    refine Subgroup.mem_map.2 ⟨c * MulAut.conj g * c⁻¹, hH ⟨c g, ?_⟩, ?_⟩
    · exact (mul_conj_mul_inv_apply c g).symm
    · rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hφ]
      group
  rw [eq_bot_iff]
  intro g hg
  have hg' : φ g ∈ localDeltaIn 3 (H.map φ.toMonoidHom) (D.map φ.toMonoidHom) := by
    rw [localDeltaIn_map_mulEquiv]
    exact Subgroup.mem_map.2 ⟨g, hg, rfl⟩
  have h1 := eq_one_of_q8_aut h hσ hH' hy' hg'
  rw [Subgroup.mem_bot]
  exact φ.injective (by rw [h1, map_one])

end CFSG.HardMathSupport.Solomon.Coordinator
