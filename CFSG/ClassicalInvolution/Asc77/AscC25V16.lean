module

public import CFSG.ClassicalInvolution.Asc77.AscC25V15
public import CFSG.ClassicalInvolution.Asc77.AscC25V10
public import CFSG.ClassicalInvolution.Asc77.AscIH8Small
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped MatrixGroups commutatorElement

section Mixed

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


omit [IsSimpleGroup G]
    in
theorem isUniqueInvolution_le_centralizer {K : Subgroup G} {z : G}
    (hI : IsUniqueInvolution K z) : K ≤ Subgroup.centralizer ({z} : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : k * z * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hI.mem) (K.inv_mem hk)
  have hsq : k * z * k⁻¹ * (k * z * k⁻¹) = 1 := by
    calc k * z * k⁻¹ * (k * z * k⁻¹) = k * (z * z) * k⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  rcases hI.unique _ hmem hsq with h | h
  · exfalso
    apply hI.ne_one
    calc z = k⁻¹ * (k * z * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  · calc k * z = k * z * k⁻¹ * k := by group
      _ = z * k := by rw [h]

theorem mixed_section_data (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f ≠ 9)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R' a) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧
      ∃ hzA : z ∈ Subgroup.centralizer ({a} : Set G),
        IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩ ∧
        Nat.card ↥(Subgroup.centralizer ({a} : Set G)) < Nat.card G ∧
        CITBelowU p e₀ (Nat.card G) := by
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  have hfix := fix_of_isFAut h haS hF
  have haK' : a ∈ Subgroup.normalizer (K' : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.2
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK'
  have hσ1 : fieldChar hp hq e ⟨a, haK'⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hR'syl.1 h.hqR' h.hzR' hF ha2 haK'
  have hb1 : a ≠ 1 := by
    intro h1
    apply hσ1
    have : (⟨a, haK'⟩ : Subgroup.normalizer (K' : Set G)) = 1 := Subtype.ext h1
    rw [this, map_one]
  have hzb : z ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.hyp.hzS a haS).symm
  have d' := twinCtx'_of_hyp25 h
  have hconj : ∀ y x : G, y ∈ Subgroup.centralizer ({z} : Set G) →
      x ∈ Subgroup.centralizer ({z} : Set G) → conjSub x K' = K' →
        conjSub (y * x * y⁻¹) K' = K' := fun y x hy hx hxK =>
    d'.conj_normalizer (Subgroup.mem_centralizer_singleton_iff.mp hy)
      (Subgroup.mem_centralizer_singleton_iff.mp hx) hxK
  obtain ⟨e₀, hfe, h5, hmem, hlt, hIH⟩ := fs_sectionData hp hq h9 haK' ha2 hb1 hσ1 h.hz'
    (isUniqueInvolution_le_centralizer h.hz') hconj (exists_noncomm_of_swap h) hzb
    h.hs.stand.below
  exact ⟨e₀, hfe, h5, hzb, hmem, hlt, hIH⟩

section Typed


theorem mixed_sectionLieType (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f ≠ 9)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R' a)
    (hnoswap : ¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K' = K) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧
      ∃ hzA : z ∈ Subgroup.centralizer ({a} : Set G),
        IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩ ∧
        (SectionLieType p e₀ (conjFamily (perfectCoreIn K' a))
            (omegaGen (conjFamily (perfectCoreIn K' a))) .PSL 2 ∨
          SectionLieType p e₀ (conjFamily (perfectCoreIn K' a))
            (omegaGen (conjFamily (perfectCoreIn K' a))) .PSL 3 ∨
          SectionLieType p e₀ (conjFamily (perfectCoreIn K' a))
            (omegaGen (conjFamily (perfectCoreIn K' a))) .PSU 3 ∨
          SectionLieType p e₀ (conjFamily (perfectCoreIn K' a))
            (omegaGen (conjFamily (perfectCoreIn K' a))) .G2 0 ∨
          SectionLieType p e₀ (conjFamily (perfectCoreIn K' a))
            (omegaGen (conjFamily (perfectCoreIn K' a))) .trialityD4 0) := by
  obtain ⟨e₀, hfe, h5, hzA, hmem, hlt, hIH⟩ := mixed_section_data h h9 haS ha2 hF
  have d' := twinCtx'_of_hyp25 h
  have hDE : Disconnected.DEdgeless (conjFamily (perfectCoreIn K' a)) :=
    (fs_dEdgeless_iff d' h5 hzA hmem).mpr hnoswap
  have hΩ₀ := fs_hypOmegaMod_conjFamily h.hΩ h.hK' h.hz' hzA hmem
  exact ⟨e₀, hfe, h5, hzA, hmem, sectionThm6_five h.hp h5 (ih8SmallEdge p) hIH hlt hΩ₀
    ⟨_, ⟨1, conjSub_one _⟩⟩ hDE⟩

end Typed

theorem eq_conj_z_of_commute_order_four (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    {c g y₀ : G} (hy₀ : y₀ ∈ conjSub c K') (hy4 : orderOf y₀ = 4)
    (hcomm : (g * z * g⁻¹) * y₀ = y₀ * (g * z * g⁻¹)) : g * z * g⁻¹ = c * z * c⁻¹ := by
  by_contra hne
  have hJ : conjSub c K' ∈ Ω := h.hΩ.conjInvariant c K' h.hK'
  have ha : IsUniqueInvolution (conjSub c K') (c * z * c⁻¹) := h.hz'.conj c
  exact T7ER.not_commute_of_conj h.hs h.hyp.hW h.hyp.hE4 hJ ha hne hy₀ hy4 hcomm

end Mixed

end CFSG.ClassicalInvolution.Asc77.C25V
