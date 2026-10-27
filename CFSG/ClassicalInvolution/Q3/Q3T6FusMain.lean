module

public import CFSG.ClassicalInvolution.Q3.Q3T6FusCore
public import CFSG.ClassicalInvolution.Q3.Q3T6FusM
public import CFSG.ClassicalInvolution.Q3.Q3T6FusM11
public import CFSG.ClassicalInvolution.AschTight.S1911P3i

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.Assembly.LowTwoRank
open CFSG.Blueprint

section Main



variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {C : Subgroup G}

@[expose] def FusResidualL3 (K : Subgroup G) (z : G) (C : Subgroup G) : Prop :=
  ∀ s : ↥C, (∃ g : G, (s : G) = g * z * g⁻¹) → (s : G) * z = z * (s : G) →
    ∃ y ∈ conjGen (secL K C), ∀ w ∈ conjGen (secL K C),
      (s * y⁻¹) * w * (s * y⁻¹)⁻¹ * w⁻¹ ∈ oddCoreOf (conjGen (secL K C))

namespace FusSec3

variable (h : FusSec3 K z C)

include h

theorem fusion_of_sectionLieType3 {t : StatedLieTag} {k : ℕ} (htag : S1911.IsT6Tag t k)
    (hsec : SectionLieTypeU 3 1 (conjFamily (secL K C)) (conjGen (secL K C)) t k)
    (hres : ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) → FusResidualL3 K z C)
    (s : ↥C) (hs : ∃ g : G, (s : G) = g * z * g⁻¹) :
    ∃ c : ↥C, s = c * (⟨z, h.zC⟩ : C) * c⁻¹ := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨D, e, he, hft, hadm, hc⟩ := hsec
  have hconj : ConjInvariant (fusΦ K C) := conjInvariant_oddQuotientFamily
    (hypOmegaModU_restrict h.hypC (conjGen (secL K C))).conjInvariant
  have hO := CFSG.ComponentClassification.OddCore.quotient_corefree ↥(conjGen (secL K C))
  have hΦne : (fusΦ K C).Nonempty := ⟨_, (mem_secFamily_iff _ _).mpr ⟨1, rfl⟩⟩
  have : Nontrivial (fusE K C) := ⟨⟨_, 1, (h.isUniqueInvolution_secImg 1).ne_one⟩⟩
  have M : Ih8Model 3 1 (fusΦ K C) t k e := ih8ModelOfSystemU D 0 hconj hft hadm he hc
  have hsimple := isSimpleGroup_of_ih8Model hp2 htag M hO
  refine h.fusion_of_inner hsimple (fun x hx hx1 => factM2Gen hp2 htag M hΦne hx hx1) ?_ s hs
  intro s₁ hs₁2 hs₁g hs₁z hs₁e
  have hφ2 : secAct (conjGen (secL K C)) s₁ * secAct (conjGen (secL K C)) s₁ = 1 := by
    rw [← map_mul, hs₁2, map_one]
  have hLY : secL K C ≤ conjGen (secL K C) := le_conjGen ⟨1, conjSub_one _⟩
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨y, hy, hyx⟩ := hres (Or.inl ⟨rfl, rfl⟩) s₁ hs₁g hs₁z
    exact ⟨_, secAct_eq_conj_of_residual hy hyx⟩
  · obtain ⟨y, hy, hyx⟩ := hres (Or.inr ⟨rfl, rfl⟩) s₁ hs₁g hs₁z
    exact ⟨_, secAct_eq_conj_of_residual hy hyx⟩
  all_goals
    have hLΦ := (mem_secFamily_iff (secL K C) _).mpr ⟨1, rfl⟩
    rw [conjSub_one] at hLΦ
    have hnorm : (secImg (conjGen (secL K C)) (secL K C)).map
        (secAct (conjGen (secL K C)) s₁).toMonoidHom = secImg (conjGen (secL K C)) (secL K C) := by
      rw [secAct_secImg _ s₁ hLY, conjSub_eq_of_mem_normalizer (h.mem_normalizer_sec hs₁z)]
    refine factM1Gen hp2 (by simp) M _ hφ2 hLΦ hnorm ?_
    intro P hP2 hPL hfix
    by_contra hne
    push Not at hne
    obtain ⟨x, hx, y, hy, hxy⟩ := hne
    exact h.false_of_fixes_nonabelian hs₁g hs₁z hs₁2 hs₁e hP2 hPL hfix ⟨x, hx, y, hy, hxy⟩

theorem fusion_of_sectionType3 (hM : Q3.M11Facts)
    (hOut : ∀ φ : MulAut ↥NativeSporadic.M11, ∃ g, φ = MulAut.conj g)
    (hsec : SectionLieTypeU 3 1 (conjFamily (secL K C)) (conjGen (secL K C)) .PSL 3 ∨
      SectionLieTypeU 3 1 (conjFamily (secL K C)) (conjGen (secL K C)) .PSU 3 ∨
      SectionLieTypeU 3 1 (conjFamily (secL K C)) (conjGen (secL K C)) .G2 0 ∨
      SectionLieTypeU 3 1 (conjFamily (secL K C)) (conjGen (secL K C)) .trialityD4 0 ∨
      SectionCompU 3 1 (conjFamily (secL K C)) (conjGen (secL K C)) Q3.CompData.m11)
    (hL3 : (SectionLieTypeU 3 1 (conjFamily (secL K C)) (conjGen (secL K C)) .PSL 3 ∨
      SectionLieTypeU 3 1 (conjFamily (secL K C)) (conjGen (secL K C)) .PSU 3) →
        FusResidualL3 K z C)
    (s : ↥C) (hs : ∃ g : G, (s : G) = g * z * g⁻¹) :
    ∃ c : ↥C, s = c * (⟨z, h.zC⟩ : C) * c⁻¹ := by
  rcases hsec with hsec | hsec | hsec | hsec | hsec
  · exact h.fusion_of_sectionLieType3 (Or.inl ⟨rfl, rfl⟩) hsec (fun _ => hL3 (Or.inl hsec)) s hs
  · exact h.fusion_of_sectionLieType3 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hsec
      (fun _ => hL3 (Or.inr hsec)) s hs
  · refine h.fusion_of_sectionLieType3 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hsec ?_ s hs
    rintro (⟨h', -⟩ | ⟨h', -⟩) <;> cases h'
  · refine h.fusion_of_sectionLieType3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hsec ?_ s hs
    rintro (⟨h', -⟩ | ⟨h', -⟩) <;> cases h'
  · obtain ⟨D, hc⟩ := hsec
    have hconj : ConjInvariant (fusΦ K C) := conjInvariant_oddQuotientFamily
      (hypOmegaModU_restrict h.hypC (conjGen (secL K C))).conjInvariant
    have : Nontrivial (fusE K C) := ⟨⟨_, 1, (h.isUniqueInvolution_secImg 1).ne_one⟩⟩
    have hsurj : Function.Surjective (castHom hc (D.hom 0)) := by
      have h0 := lieSystemDataU_surjective_hom D 0
      rw [← MonoidHom.range_eq_top] at h0 ⊢
      rw [range_castHom]
      exact h0
    have hψ1 : ∃ x, castHom hc (D.hom 0) x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨a, ha⟩ := exists_ne (1 : fusE K C)
      obtain ⟨x, rfl⟩ := hsurj a
      exact ha (hcon x)
    have hne : ∃ R ∈ Q3.M11ClassicalClass, R.map (castHom hc (D.hom 0)) ∈ fusΦ K C := by
      obtain ⟨R, hR, hmem⟩ := D.meets 0
      obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom 0) hR
      exact ⟨R', hR', by rw [hRR]; exact hmem⟩
    obtain ⟨hsimple, hinn, hM2⟩ := m11_facts hM hOut (castHom hc (D.hom 0)) hsurj hψ1 hconj hne
    exact h.fusion_of_inner hsimple hM2 (fun s₁ _ _ _ _ => hinn _) s hs

end FusSec3

end Main

end CFSG.ClassicalInvolution.Q3.Q3T6
