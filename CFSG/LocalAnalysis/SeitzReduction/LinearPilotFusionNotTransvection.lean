module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvectionCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem conj_not_mem_perfect (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    (hZ : center L = ⊥) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G)
    {P : Subgroup G} (hP : ⁅P, P⁆ = P) (hPL : P ≤ L)
    (hPw : P ≤ centralizer ({g⁻¹ * t * g} : Set G)) : g⁻¹ * t * g ∉ P := by
  intro hwP
  have hPt : P ≤ centralizer ({t} : Set G) := hPL.trans (le_centralizer_of_mem_centralizer htC)
  obtain ⟨l, hl, hlw⟩ := (std_perfect_le_inf_conjugate hset hOut htC ht g hP hPt hPw hwP).2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hlw
  have htl : t = l := by
    have h : g * (g⁻¹ * l * g) * g⁻¹ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [hlw]
    simpa [mul_assoc] using h.symm
  refine not_mem_of_mem_centralizer hZ htC (fun h1 => ?_) (htl ▸ hl)
  rw [h1, orderOf_one] at ht
  exact absurd ht (by decide)

theorem not_isInvolutionClass_one_conj (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G) (hgL : g⁻¹ * t * g ∈ L) :
    ¬ IsInvolutionClass 1 (e ⟨g⁻¹ * t * g, hgL⟩) := by
  intro hz
  have := finite_of_card_eq_two_pow hK
  have := charP_two_of_card_eq_two_pow hK
  have hnK : ¬(n = 4 ∧ Nat.card K = 2) := by
    rintro ⟨rfl, h2⟩
    refine ne_four_one_of_mulEquiv hset e hK ?_
    have h2f : 2 ^ f = 2 ^ 1 := by rw [← hK, h2, pow_one]
    rw [Nat.pow_right_injective le_rfl h2f]
  set w : L := ⟨g⁻¹ * t * g, hgL⟩ with hw
  have hcore := mem_perfectCore_centralizer_transvection hn hnK hz
  set φ : projectiveSL n K →* G := L.subtype.comp e.symm.toMonoidHom with hφ
  have hφw : φ (e w) = g⁻¹ * t * g := by simp [hφ, hw]
  refine conj_not_mem_perfect hset.standardSetting (isSolvable_outer_of_mulEquiv (by omega) e)
    hset.center_eq_bot htC ht g
    (P := (perfectCore (centralizer ({e w} : Set (projectiveSL n K)))).map φ) ?_ ?_ ?_
    ⟨e w, hcore, hφw⟩
  · rw [← map_commutator, perfectCore_perfect]
  · rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  · rintro _ ⟨x, hx, rfl⟩
    have h := mem_centralizer_singleton_iff.1 (perfectCore_le _ hx)
    rw [mem_centralizer_singleton_iff, ← hφw, ← map_mul, ← map_mul, h]

theorem not_isInvolutionClass_one_conj_of_inf_eq_zpowers (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* projectiveSL n K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (g : G)
    (hgL : g⁻¹ * t * g ∈ L) : ¬ IsInvolutionClass 1 (e ⟨g⁻¹ * t * g, hgL⟩) :=
  not_isInvolutionClass_one_conj hset hn hK e (mem_centralizer_of_inf_eq_zpowers hKt) ht g hgL

theorem not_forall_commute_sylow_of_isInvolutionClass_one (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* projectiveSL n K)
    (hU : ∀ (U : Sylow 2 L) {z : L}, z ≠ 1 → (∀ u ∈ (U : Subgroup L), u * z = z * u) →
      IsInvolutionClass 1 (e z))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hgL hcomm
  refine not_isInvolutionClass_one_conj hset hn hK e htC ht g hgL
    (hU U (fun h => ?_) fun u hu => Subtype.ext (hcomm u hu))
  have h1 : g⁻¹ * t * g = 1 := congrArg Subtype.val h
  have ht1 : t = 1 := by
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [ht1, orderOf_one] at ht
  exact absurd ht (by decide)

end CFSG.SeitzReduction.LinearPilot
