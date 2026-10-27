module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaExtend
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaSwap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {C : Type} [Group C] [Finite C] {Q : Subgroup C} [Q.Normal]

theorem AschbacherHyp.exists_central_eq (hC : AschbacherHyp C Q) :
    ∃ z : C, z ≠ 1 ∧ ∀ u : C, (∀ c : C, c * u = u * c) → u = 1 ∨ u = z := by
  obtain ⟨z, -, hz1, -, hzcentre⟩ := hC.exists_centre
  refine ⟨z, hz1, fun u hu => ?_⟩
  have hu' : u ∈ centralizer (commutator C : Set C) := by
    rw [mem_centralizer_iff]
    intro h _
    exact hu h
  exact hzcentre u (hC.centralizer_commutator_le hu').1 (fun y _ => (hu y).symm)

theorem AschbacherHyp.exists_aut_fix_not_inner (hC : AschbacherHyp C Q) {x : C}
    (hx : x ∉ commutator C) (hx2 : x ^ 2 = 1) (Y : Subgroup C) (hYL : Y ≤ commutator C)
    (hYx : ∀ y ∈ Y, x * y = y * x) (ψ : ↥Y →* A5) (hψs : Function.Surjective ψ)
    (hψk : ∀ y : ↥Y, (y : C) ∈ Q → ψ y = 1) :
    ∃ η : C ≃* C, η x = x ∧ (∀ u : C, (∀ c : C, c * u = u * c) → η u = u) ∧
      ¬ ∃ g ∈ Y, ∀ y ∈ Y, η y = g * y * g⁻¹ := by
  classical
  obtain ⟨e, θ, f, c, χ, hθs, hθk, hθb, hc, hf⟩ := AschbacherHyp.exists_field_aut hC
  obtain ⟨x₀, hx₀⟩ := AschbacherHyp.exists_swapAut hC e θ hθs hθb hx hx2
  obtain ⟨g, η, hηx, hηl⟩ := AschbacherHyp.exists_aut_extend hC f hx hx2
  refine ⟨η, hηx, ?_, ?_⟩
  ·
    obtain ⟨z, hz1, hz⟩ := AschbacherHyp.exists_central_eq hC
    intro u hu
    have hηu : ∀ d : C, d * η u = η u * d := by
      intro d
      apply η.symm.injective
      simp only [map_mul, MulEquiv.symm_apply_apply]
      exact hu (η.symm d)
    rcases hz u hu with h | h
    · rw [h, map_one]
    · rcases hz (η u) hηu with h' | h'
      · exfalso
        have hu1 : u = 1 := η.injective (by rw [h', map_one])
        rw [h] at hu1
        exact hz1 hu1
      · rw [h', h]
  · rintro ⟨g', hg'Y, hg'⟩
    let incl : ↥Y →* ↥(commutator C) := Subgroup.inclusion hYL
    let ρ : ↥Y →* A5 := (MonoidHom.snd A5 A5).comp (θ.comp incl)
    have hθY : ∀ y : ↥Y, θ (incl y) = (x₀ * ρ y * x₀⁻¹, ρ y) := by
      intro y
      have h1 : MulAut.conjNormal x (incl y) = incl y := by
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply]
        show x * (y : C) * x⁻¹ = (y : C)
        rw [hYx y y.2]
        group
      have h2 := hx₀ (incl y)
      rw [h1, swapAut_apply] at h2
      have h3 : (θ (incl y)).1 = x₀ * (θ (incl y)).2 * x₀⁻¹ := congrArg Prod.fst h2
      exact Prod.ext h3 rfl
    have hρs : Function.Surjective ρ := by
      have hker : ρ.ker ≤ ψ.ker := by
        intro y hy
        have h1 : ρ y = 1 := hy
        have h2 : θ (incl y) = 1 := by
          rw [hθY y, h1]
          simp
        exact (MonoidHom.mem_ker).mpr (hψk y ((hθk (incl y)).mp h2))
      let φ : ↥Y ⧸ ρ.ker →* A5 := QuotientGroup.lift ρ.ker ψ hker
      have hφs : Function.Surjective φ := by
        intro a
        obtain ⟨y, rfl⟩ := hψs a
        exact ⟨QuotientGroup.mk y, rfl⟩
      have hcard : Nat.card A5 ≤ Nat.card ρ.range :=
        calc Nat.card A5 ≤ Nat.card (↥Y ⧸ ρ.ker) := Nat.card_le_card_of_surjective φ hφs
          _ = Nat.card ρ.range :=
            Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
      exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_le_card ρ.range hcard)
    let g'L : ↥(commutator C) := ⟨g', hYL hg'Y⟩
    let p : A5 × A5 := θ g
    have hrel : ∀ y : ↥Y, θ g'L * θ (incl y) * (θ g'L)⁻¹ = p * θ (f (incl y)) * p⁻¹ := by
      intro y
      have h1 : (g : C) * (f (incl y) : C) * (g : C)⁻¹ = g' * (y : C) * g'⁻¹ :=
        (hηl (incl y)).symm.trans (hg' (y : C) y.2)
      have h2 : g * f (incl y) * g⁻¹ = g'L * incl y * g'L⁻¹ := Subtype.ext h1
      have h3 := congrArg θ h2
      simp only [map_mul, map_inv] at h3
      exact h3.symm
    let Φ₀ : A5 × A5 ≃* A5 × A5 := MulEquiv.prodCongr c χ
    let Ψ : A5 × A5 ≃* A5 × A5 := Φ₀.trans ((MulAut.conj p).trans (MulAut.conj (θ g'L)⁻¹))
    have hΨapp : ∀ u : A5 × A5,
        Ψ u = (θ g'L)⁻¹ * (p * (c u.1, χ u.2) * p⁻¹) * θ g'L := by
      intro u
      have h1 : Φ₀ u = (c u.1, χ u.2) := rfl
      simp [Ψ, MulAut.conj_apply, h1]
    have hΨ : ∀ q : A5, Ψ (x₀ * q * x₀⁻¹, q) = (x₀ * q * x₀⁻¹, q) := by
      intro q
      obtain ⟨y, rfl⟩ := hρs q
      have h1 := hrel y
      rw [hf (incl y), hθY y] at h1
      rw [hΨapp]
      have h2 : p * (c (x₀ * ρ y * x₀⁻¹), χ (ρ y)) * p⁻¹ =
          θ g'L * (x₀ * ρ y * x₀⁻¹, ρ y) * (θ g'L)⁻¹ := h1.symm
      simp only
      rw [h2]
      group
    have key : ∀ u v : A5 × A5, (θ g'L)⁻¹ * (p * (c u.1, χ u.2) * p⁻¹) * θ g'L = v →
        (c u.1, χ u.2) = (p⁻¹ * θ g'L) * v * (p⁻¹ * θ g'L)⁻¹ := by
      intro u v h
      rw [← h]
      group
    rcases eq_id_or_eq_swapAut_of_fix x₀ Ψ hΨ with h | h
    · exact prod_ne_conj c χ hc (p⁻¹ * θ g'L) fun u => key u u (by rw [← hΨapp]; exact h u)
    · exact prod_ne_conj_swapAut c χ x₀ (p⁻¹ * θ g'L) fun u =>
        key u (swapAut x₀ u) (by rw [← hΨapp]; exact h u)

end CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz
