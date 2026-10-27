module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcJ

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem excLang_jhom_ker_le_center {p : ℕ} {X J : Subgroup Ω} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hnt : Nontrivial (PSimple p X)) (hJX : J ≤ X) {C : Type} [Group C] (θ : PSimple p X ≃* C) :
    (K155X.l154JHom p hJX θ).ker ≤ Subgroup.center ↥J := by
  intro l hl
  rw [MonoidHom.mem_ker] at hl
  have h1 : chevQuotHom p X ⟨l.1, hJX l.2⟩ = 1 := by
    have : θ (chevQuotHom p X ⟨l.1, hJX l.2⟩) = 1 := hl
    exact (map_eq_one_iff _ θ.injective).1 this
  have h2 : pQuotHom p X ⟨l.1, hJX l.2⟩ ∈ Subgroup.center (PQuot p X) :=
    (QuotientGroup.eq_one_iff _).1 h1
  have hOne : GLAPPrimeCore p ↥X ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PQuot p X) := by
      show Subsingleton (↥X ⧸ GLAPPrimeCore p ↥X)
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have hsub2 : Subsingleton (PSimple p X) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p X))).subsingleton
    exact (not_subsingleton_iff_nontrivial.2 hnt) hsub2
  have hOZ : GLAPPrimeCore p ↥X ≤ Subgroup.center ↥X :=
    le_center_of_normal_of_isQuasisimple hX (GLAPPrimeCore.normal p ↥X) hOne
  have hc : ∀ s : ↥X,
      (⟨l.1, hJX l.2⟩ : ↥X) * s * (⟨l.1, hJX l.2⟩ : ↥X)⁻¹ * s⁻¹ ∈ Subgroup.center ↥X := by
    intro s
    refine hOZ ?_
    have hcomm : pQuotHom p X (⟨l.1, hJX l.2⟩ : ↥X) * pQuotHom p X s =
        pQuotHom p X s * pQuotHom p X (⟨l.1, hJX l.2⟩ : ↥X) :=
      (Subgroup.mem_center_iff.1 h2 (pQuotHom p X s)).symm
    have hker : pQuotHom p X
        ((⟨l.1, hJX l.2⟩ : ↥X) * s * (⟨l.1, hJX l.2⟩ : ↥X)⁻¹ * s⁻¹) = 1 := by
      simp only [map_mul, map_inv, hcomm]
      group
    exact (QuotientGroup.eq_one_iff _).1 hker
  have hZ : (⟨l.1, hJX l.2⟩ : ↥X) ∈ Subgroup.center ↥X :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.mem_center_of_commutator_mem_center hX.1 hc
  refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
  exact congrArg (Subtype.val : ↥X → Ω) (Subgroup.mem_center_iff.1 hZ ⟨j.1, hJX j.2⟩)


theorem excLang_jbar_equiv {p : ℕ} (hp : p.Prime) {X J Y : Subgroup Ω} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hnt : Nontrivial (PSimple p X)) (hJ : GLAPComponent p Y J) (hJX : J ≤ X) {C : Type} [Group C]
    (θ : PSimple p X ≃* C) (hq : CFSG.Open.IsQuasisimple ↥(K155X.l154JImage p X J θ)) :
    Nonempty (PSimple p J ≃*
      (↥(K155X.l154JImage p X J θ) ⧸ Subgroup.center ↥(K155X.l154JImage p X J θ))) := by
  set JI : Subgroup C := K155X.l154JImage p X J θ with hJI
  let ρ' : ↥J →* ↥JI := (K155X.l154JHom p hJX θ).codRestrict JI (K155X.l154JHom_mem hJX θ)
  let Θ : ↥J →* ↥JI ⧸ Subgroup.center ↥JI := (QuotientGroup.mk' (Subgroup.center ↥JI)).comp ρ'
  have hρ'surj : Function.Surjective ρ' := fun z => by
    obtain ⟨l, hl⟩ := K155X.exists_l154JHom_eq hJX θ z.2
    exact ⟨l, Subtype.ext hl⟩
  have hΘsurj : Function.Surjective Θ := (QuotientGroup.mk'_surjective _).comp hρ'surj
  have hperfJ : commutator ↥J = ⊤ :=
    (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)).commutator_eq_top
  have hΘker : Θ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    have hc : ρ' l ∈ Subgroup.center ↥JI := (QuotientGroup.eq_one_iff (ρ' l)).1 hl
    refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.mem_center_of_commutator_mem_center hperfJ fun j => ?_
    apply excLang_jhom_ker_le_center hX hnt hJX θ
    have hcomm : K155X.l154JHom p hJX θ l * K155X.l154JHom p hJX θ j =
        K155X.l154JHom p hJX θ j * K155X.l154JHom p hJX θ l :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hc (ρ' j)).symm
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  obtain ⟨e₀, -⟩ := K155X.l154_exists_pSimple_equiv hp hJ hq.2 Θ hΘsurj hΘker
  exact ⟨e₀⟩


end CFSG.LocalAnalysis.GLTheoremA.I167

end
