module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldDefs
public import CFSG.RankThree.PartOne.S11d.FixedFactsPSU

public section

namespace CFSG.AGLEmbedding.LieOut

open Matrix CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

theorem fixesNonLocalized_psu {T : Type} [Group T] [Finite T] {p f n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hC : StatedClassicalModel T .PSU n 2 f)
    (hdiag : ¬ p ∣ Nat.gcd n (2 ^ f + 1)) (hq : ¬ (n = 3 ∧ f = p)) {α : MulAut T}
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) : FixesNonLocalized α := by
  classical
  have hM : LieModel T .PSU n 2 f := (lieModel_classical_iff (by decide)).mpr hC
  have hf : 1 ≤ f := hC.1.2.1
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hU, hn3, hq₁, ⟨e⟩⟩ := psu_prime_form_model hC
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hfinP : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv T e.toEquiv
  set α' := MulAut.congr e α with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hαp, map_one]
  have hα'inn : α' ∉ innerAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    fun hmem => hαinn ((mem_innerAut_congr e α).mp hmem)
  have hα'ord : orderOf α' = p := orderOf_eq_prime hα'p (fun h1 => hα'inn (h1 ▸ one_mem _))
  have hσ1 : primeFormFieldFactor hU hC1 hn3 hq₁ α' ≠ 1 := by
    intro hσ1
    have hαD : α' ∈ primeFormD hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor hU hC1 hn3 hq₁]
      exact hσ1
    exact hα'inn (mem_innerAut_of_mem_D hU hn3 hq₁ hp hdiag hαD hα'p)
  set σ := primeFormFieldFactor hU hC1 hn3 hq₁ α' with hσ
  have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hα'p, map_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hpf, -, -, -, -, M, hMconj⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent hU hn3 hq₁ hp hp2 hp2
      α' hα'ord σ rfl hσord
  obtain ⟨f₀, hff⟩ := hpf
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h1 | h1
    · simp [h1] at hff
      omega
    · exact h1
  have hfdiv : f / p = f₀ := by rw [hff]; exact Nat.mul_div_cancel_left f₀ hp.pos
  set β := primeFormFieldHom hU hC1 σ with hβ
  set ψ := (primeFormConjHom hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ with hψ
  have hψα : ψ * α' * ψ⁻¹ = β := by
    rw [hψ, inv_inv]
    exact hMconj
  have hq₀ : ¬(n = 3 ∧ 2 ^ f₀ = 2) := fun hc =>
    hq ⟨hc.1, by
      have h1 : f₀ = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using hc.2)
      rw [hff, h1, mul_one]⟩
  set h₀ := fixSubfield_unitaryFieldData hU hp hp2 hσord with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar hU hp hp2 hσord
  have hΓN : fixSub β = (subfieldPSU hU h₀ hbar n).range :=
    fieldFixedPSU_eq_range hU hp hp2 hσord hn3 hdiag
  obtain ⟨hNperf, hX, hNL⟩ := psu_subfield_group hU hp hp2 hσord hn3 hfdiv hf₀ hq₀
  set N := (subfieldPSU hU h₀ hbar n).range with hN
  let φ : T ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := e.trans ψ
  have hφα : MulAut.congr φ α = β := by
    have : MulAut.congr φ α = ψ * α' * ψ⁻¹ := rfl
    rw [this, hψα]
  have hΓN' : fixSub (MulAut.congr φ α) = N := by rw [hφα, hΓN]
  have hNΓ : N ≤ fixSub (MulAut.congr φ α) := hΓN'.ge
  have hnormT : ∀ W : Subgroup (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      W = N → (N.subgroupOf W).Normal := by
    intro W hW
    subst hW
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hsolvT : ∀ W : Subgroup (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      W = N → ∀ (hn : (N.subgroupOf W).Normal), Group.IsSolvable (↥W ⧸ N.subgroupOf W) := by
    intro W hW hn
    subst hW
    have : Subsingleton (↥N ⧸ N.subgroupOf N) := by
      refine ⟨fun x y => ?_⟩
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq]
          exact Subgroup.mem_subgroupOf.mpr (x⁻¹ * y).2
    exact inferInstance
  have hM' : LieModel T .PSU n 2 (p * f₀) := by rw [← hff]; exact hM
  exact FixesNonLocalized.of_fixedFacts
    (fixedFacts_of_iso φ α hM' hf₀ N hNΓ (hnormT _ hΓN') hNperf
      (hsolvT _ hΓN' (hnormT _ hΓN')) hNL (fun x hx _ => hΓN' ▸ hx)
      (Or.inl fun x hx _ => hΓN' ▸ hx) (Or.inl hX))

end CFSG.AGLEmbedding.LieOut
