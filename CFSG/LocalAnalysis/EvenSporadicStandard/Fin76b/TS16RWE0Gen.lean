module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWE0
public import Certificates.Certificate27830

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Monster.B.Co2

section Gen


theorem admGen_facts {i : ℕ} (hi : i < 60) :
    ∀ y < 128, (∀ g < 128, (admArr[i]!)[g]! = g → mulC y g = mulC g y) →
      ∃ u < 128, ∃ v < 128, (∀ g < 128, (admArr[i]!)[g]! = g → mulC u g = mulC g u) ∧
        (∀ g < 128, (admArr[i]!)[g]! = g → mulC v g = mulC g v) ∧ mulC u u = 0 ∧ mulC v v = 0 ∧
        mulC u v = y := by
  have h := Certificates.certificate27830
  simp only [admGenCheck, List.all_eq_true, List.mem_range] at h
  have hi' := h i hi
  simp only [admGenOK, List.all_eq_true, List.any_eq_true, List.mem_filter, List.mem_range,
    Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hi'
  intro y hy hyc
  obtain ⟨u, ⟨⟨hu, huc⟩, hu2⟩, v, ⟨⟨hv, hvc⟩, hv2⟩, huv⟩ :=
    hi' y ⟨hy, fun g hg => by
      by_cases hgf : (admArr[i]!)[g]! = g
      · exact Or.inr (hyc g hg hgf)
      · exact Or.inl hgf⟩
  refine ⟨u, hu, v, hv, fun g hg hgf => ?_, fun g hg hgf => ?_, hu2, hv2, huv⟩
  · rcases huc g hg with h1 | h1
    · exact absurd hgf h1
    · exact h1
  · rcases hvc g hg with h1 | h1
    · exact absurd hgf h1
    · exact h1

end Gen

namespace DECtx

variable {M : Type*} [Group M] {D E : Subgroup M} {eD : D ≃* DihedralGroup 4} {t : M}
  {eltE : ℕ → M} [hW : (D ⊔ E).Normal] (hctx : DECtx D E eD t eltE)

include hctx

theorem D0_gen {σ : M} (hσ2 : σ * σ = 1) (hσa : σ * sElt eD 1 * σ⁻¹ = sElt eD 1)
    (hσb : σ * sElt eD 4 * σ⁻¹ = sElt eD 2 * sElt eD 4)
    (hσE : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E)
    (hcard : Nat.card ↥(E ⊓ Subgroup.centralizer ({σ} : Set M)) = 8)
    (hx : ∃ x ∈ E, x ≠ 1 ∧ x ≠ t ∧ x * x = 1 ∧ σ * x = x * σ) :
    ∀ y ∈ (D ⊔ E) ⊓ Subgroup.centralizer
        ((((D ⊔ E) ⊓ Subgroup.centralizer ({σ} : Set M) : Subgroup M)) : Set M),
      y ∈ Subgroup.closure {w : M | w ∈ (D ⊔ E) ⊓ Subgroup.centralizer
        ((((D ⊔ E) ⊓ Subgroup.centralizer ({σ} : Set M) : Subgroup M)) : Set M) ∧ w * w = 1} := by
  classical
  obtain ⟨i, hi, hψi⟩ := hctx.adm_index hσ2 hσa hσb hσE hcard hx
  obtain ⟨hrep, -⟩ := adm_facts hi
  set ψ : Equiv.Perm (Fin 128) := ((hctx.Phi σ : ↥Pg) : Equiv.Perm (Fin 128)) with hψdef
  have hψ : ∀ c : Fin 128, σ * labD eD eltE c * σ⁻¹ = labD eD eltE (ψ c : ℕ) :=
    fun c => (hctx.Phi_lab σ c).symm
  have hfixiff : ∀ c : Fin 128, ψ c = c ↔ labD eD eltE c * σ = σ * labD eD eltE c := by
    intro c
    constructor
    · intro h
      have h1 := hψ c
      rw [h] at h1
      calc labD eD eltE c * σ = σ * labD eD eltE c * σ⁻¹ * σ := by rw [h1]
        _ = σ * labD eD eltE c := by group
    · intro h
      have h1 : σ * labD eD eltE c * σ⁻¹ = labD eD eltE c := by
        calc σ * labD eD eltE c * σ⁻¹ = labD eD eltE c * σ * σ⁻¹ := by rw [h]
          _ = labD eD eltE c := by group
      rw [hψ c] at h1
      exact Fin.ext (hctx.lab_inj0 (Fin.is_lt _) (Fin.is_lt _) h1)
  have hψtab : ∀ c : Fin 128, (ψ c : ℕ) = (admArr[i]!)[(c : ℕ)]! := by
    intro c
    rw [hψi]
    exact (hrep c).symm
  have hE0mem : ∀ g : Fin 128, ψ g = g →
      labD eD eltE g ∈ (D ⊔ E) ⊓ Subgroup.centralizer ({σ} : Set M) := fun g hg =>
    Subgroup.mem_inf.2 ⟨hctx.lab_mem _ g.2,
      Subgroup.mem_centralizer_singleton_iff.2 ((hfixiff g).1 hg)⟩
  intro y hy
  obtain ⟨hyW, hyC⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨c, hc, rfl⟩ := hctx.tabLab.surj y hyW
  have hcomm : ∀ g < 128, (admArr[i]!)[g]! = g → mulC c g = mulC g c := by
    intro g hg hgf
    have hgfix : ψ ⟨g, hg⟩ = ⟨g, hg⟩ := by
      apply Fin.ext
      rw [hψtab]
      exact hgf
    have h1 := Subgroup.mem_centralizer_iff.1 hyC _ (hE0mem ⟨g, hg⟩ hgfix)
    rw [← hctx.tabLab.mul _ hg _ hc, ← hctx.tabLab.mul _ hc _ hg] at h1
    exact (hctx.lab_inj0 (mulC_lt hg hc) (mulC_lt hc hg) h1).symm
  obtain ⟨u, hu, v, hv, huc, hvc, hu2, hv2, huv⟩ := admGen_facts hi c hc hcomm
  have hgen : ∀ x : ℕ, x < 128 → (∀ g < 128, (admArr[i]!)[g]! = g → mulC x g = mulC g x) →
      mulC x x = 0 → labD eD eltE x ∈ Subgroup.closure {w : M | w ∈ (D ⊔ E) ⊓
        Subgroup.centralizer ((((D ⊔ E) ⊓ Subgroup.centralizer ({σ} : Set M) :
          Subgroup M)) : Set M) ∧ w * w = 1} := by
    intro x hx128 hxc hx2
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_inf.2 ⟨hctx.lab_mem _ hx128, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨hhW, hhC⟩ := Subgroup.mem_inf.1 hh
      obtain ⟨g, hg, rfl⟩ := hctx.tabLab.surj h hhW
      have hgfix : ψ ⟨g, hg⟩ = ⟨g, hg⟩ := by
        rw [hfixiff]
        exact Subgroup.mem_centralizer_singleton_iff.1 hhC
      have hgt : (admArr[i]!)[g]! = g := by
        have := hψtab ⟨g, hg⟩
        rw [hgfix] at this
        exact this.symm
      rw [← hctx.tabLab.mul _ hg _ hx128, ← hctx.tabLab.mul _ hx128 _ hg]
      exact congrArg _ (hxc g hg hgt).symm
    · rw [← hctx.tabLab.mul _ hx128 _ hx128, hx2, hctx.lab_zero]
  have hu' := hgen u hu huc hu2
  have hv' := hgen v hv hvc hv2
  have e : labD eD eltE c = labD eD eltE u * labD eD eltE v := by
    rw [← hctx.tabLab.mul _ hu _ hv, huv]
  rw [e]
  exact Subgroup.mul_mem _ hu' hv'

end DECtx

end CFSG.EvenSporadicStandard.Fin76b.W16
