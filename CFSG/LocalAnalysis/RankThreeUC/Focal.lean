module

public import CFSG.LocalAnalysis.RankThreeUC.CoreWitness
import CFSG.GroupTheory.FusionFamilyControl
import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_eq_top_of_standing [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with
    h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

theorem inf_commutator_le_of_fusion_control {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    {T₀ : Subgroup G} (F : Set (Subgroup G)) (hFT : ∀ N ∈ F, (T : Subgroup G) ≤ N)
    (hF : ∀ N ∈ F, (T : Subgroup G) ⊓ ⁅N, N⁆ ≤ T₀)
    (hfusion : ∀ x ∈ (T : Subgroup G), ∀ g : G, g * x * g⁻¹ ∈ (T : Subgroup G) →
      Relation.ReflTransGen (fun y z => y ∈ (T : Subgroup G) ∧ z ∈ (T : Subgroup G) ∧
        ∃ N ∈ F, ∃ c ∈ N, z = c * y * c⁻¹) x (g * x * g⁻¹)) :
    (T : Subgroup G) ⊓ commutator G ≤ T₀ := by
  have hctrl : CFSG.GroupTheory.FamilyControlsFusion F (T : Subgroup G) := by
    intro x y hxT hyT hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hchain : Relation.ReflTransGen (CFSG.GroupTheory.FusionStep F (T : Subgroup G)) x
        (g * x * g⁻¹) := hfusion x hxT g (by rwa [hg])
    have hEqv := Relation.EqvGen.reflTransGen_le_eqvGen
      (CFSG.GroupTheory.FusionStep F (T : Subgroup G)) x (g * x * g⁻¹) hchain
    rwa [hg] at hEqv
  have hstep : ∀ x y : G, CFSG.GroupTheory.FusionStep F (T : Subgroup G) x y →
      x⁻¹ * y ∈ T₀ := by
    rintro x y ⟨hxT, hyT, N, hN, c, hc, rfl⟩
    refine hF N hN ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem hxT) hyT, ?_⟩
    have h := commutator_mem_commutator (H₁ := N) (H₂ := N)
      (N.inv_mem (hFT N hN hxT)) hc
    rw [commutatorElement_def] at h
    simpa [mul_assoc] using h
  exact CFSG.GroupTheory.inf_commutator_le_of_familyControlsFusion (P := T) hctrl hstep

theorem IsWitness.sylow_le_commutator (hS : Standing G) (hUC : rankThreeUC G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hw : IsWitness p P M) :
    (P : Subgroup G) ≤ ⁅M, M⁆ := by
  have := hS.simple
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  have hfoc := Subgroup.commutator_inf_eq_focalSubgroup P
  rw [commutator_eq_top_of_standing hS.nonab, top_inf_eq] at hfoc
  rw [hfoc, Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro _ ⟨hgP, x, hxP, u, rfl⟩
  have hux : u * x * u⁻¹ ∈ (P : Subgroup G) := by
    have h := (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hxP) hgP
    rw [commutatorElement_def] at h
    simpa [mul_assoc] using (P : Subgroup G).inv_mem h
  have hmap : (zpowers x).map (MulAut.conj u⁻¹⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    simpa [MulAut.conj_apply] using hux
  obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le (setting_of_rankThreeUC hS hUC)
    (fullCoreLocal_of_rankThreeUC hS hUC) hp hw.isCoreMaxLocal (zpowers_le.mpr hxP) hmap
  have hcx : c⁻¹ * x * c = u * x * u⁻¹ := by
    simpa using hc x (mem_zpowers x)
  have heq : ⁅x, u⁆ = ⁅x, c⁻¹⁆ := by
    rw [commutatorElement_def, commutatorElement_def, inv_inv]
    calc x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
      _ = x * (c⁻¹ * x * c)⁻¹ := by rw [hcx]
      _ = x * c⁻¹ * x⁻¹ * c := by group
  rw [heq]
  exact commutator_mem_commutator (hw.sylow_le hS hp hxP) (M.inv_mem hcM)

theorem IsWitness.not_dvd_relIndex_of_commutator_le (hS : Standing G) (hUC : rankThreeUC G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) {N : Subgroup G} (hNM : N ≤ M) (hcomm : ⁅M, M⁆ ≤ N) :
    ¬ p ∣ N.relIndex M := by
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  have hPN : (P : Subgroup G) ≤ N := (hw.sylow_le_commutator hS hUC hp).trans hcomm
  have hPM : (P : Subgroup G) ≤ M := hPN.trans hNM
  intro hdvd
  have h1 : N.relIndex M ∣ (P : Subgroup G).relIndex M := relIndex_dvd_of_le_left M hPN
  have h2 : (P : Subgroup G).relIndex M ∣ (P : Subgroup G).index := by
    rw [← relIndex_top_right, ← relIndex_mul_relIndex (P : Subgroup G) M ⊤ hPM le_top]
    exact dvd_mul_right _ _
  exact P.not_dvd_index (hdvd.trans (h1.trans h2))

end CFSG.LocalAnalysis.RankThreeUC
