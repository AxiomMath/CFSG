module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXCov
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Simp
import CFSG.LocalAnalysis.ComponentClassification.InvolutionFixedPoints
import CFSG.Walter.AStar.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXSet

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_x_simple_exists_fixed_involution {Y : Type} [Group Y] [Finite Y]
    (hY : SimpleFStarQuotient Y) (α : MulAut Y) (hα : α * α = 1) :
    ∃ e : Y, orderOf e = 2 ∧ α e = e ∧ e ∉ center Y := by
  obtain ⟨hS, hZ⟩ := l34g_simple_of_simpleFStar hY
  haveI := hS
  have hnab : ∃ a b : Y, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := exists_ne (1 : Y)
    have hgc : g ∈ center Y := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact hcon k g
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hg hgc
  have heven : 2 ∣ Nat.card Y :=
    even_iff_two_dvd.mp (CFSG.Walter.even_card_of_isSimpleGroup hnab)
  obtain ⟨e, he2, hαe⟩ :=
    CFSG.ComponentClassification.InvolutionFixedPoints.exists_fixed_involution heven α
      (fun y => aut_apply_apply hα y)
  refine ⟨e, he2, hαe, ?_⟩
  rw [hZ, Subgroup.mem_bot]
  intro he
  rw [he, orderOf_one] at he2
  exact absurd he2 (by decide)

theorem l34g_x_f0_of_quotient [Finite G] {I : Subgroup G} (hI : InFStar I) {x : G}
    (hx : x * x = 1) (hxN : x ∈ normalizer (I : Set G)) {α : MulAut (↥I ⧸ oddCore ↥I)}
    (hα : ∀ a : ↥I, (QuotientGroup.mk (conjAut I hx hxN a) : ↥I ⧸ oddCore ↥I) =
      α (QuotientGroup.mk a))
    {e : ↥I ⧸ oddCore ↥I} (he : orderOf e = 2) (hαe : α e = e)
    (hnc : e ∉ center (↥I ⧸ oddCore ↥I)) :
    ∃ e' ∈ I ⊓ centralizer ({x} : Set G), orderOf e' = 2 ∧ ¬ ∀ g ∈ I, e' * g = g * e' := by
  have he2 : e * e = 1 := by
    have h1 := pow_orderOf_eq_one e
    rwa [he, pow_two] at h1
  obtain ⟨a, haa, hσa, hρa⟩ := l34g_x_lift_fixed_involution (l34g_x_cover hI)
    (conjAut_mul_self I hx hxN) hα he2 hαe
  have haa' : (a : G) * a = 1 := congrArg Subtype.val haa
  refine ⟨(a : G), ⟨a.2, ?_⟩, ?_, ?_⟩
  · have hfix : a ∈ fixSub (conjAut I hx hxN) := hσa
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((mem_fixSub_conjAut_iff I hx hxN a).mp hfix).symm
  · have hne : (a : G) ≠ 1 := by
      intro h1
      have h2 : a = 1 := Subtype.ext h1
      rw [h2, map_one] at hρa
      rw [← hρa, orderOf_one] at he
      exact absurd he (by decide)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ hne
    rw [pow_two]
    exact haa'
  · intro hc
    apply hnc
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← hρa]
    change (QuotientGroup.mk g : ↥I ⧸ oddCore ↥I) * QuotientGroup.mk a =
      QuotientGroup.mk a * QuotientGroup.mk g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hc (g : G) g.2).symm

theorem asc82FactNoncentralFixed_of_core (h : Asc82CoreF0) : Asc82FactNoncentralFixed := by
  intro G _ _ I hI x hx hxN
  have hx2 : x * x = 1 := by
    have h1 := pow_orderOf_eq_one x
    rwa [hx, pow_two] at h1
  obtain ⟨α, hα2, hα⟩ := l34g_x_induced hx2 hxN
  obtain ⟨e, he, hαe, hnc⟩ : ∃ e : ↥I ⧸ oddCore ↥I, orderOf e = 2 ∧ α e = e ∧
      e ∉ center (↥I ⧸ oddCore ↥I) := by
    rcases l34g_x_starQuotient hI with hs | ⟨hq, hU⟩
    · exact l34g_x_simple_exists_fixed_involution hs α hα2
    · exact h _ hq hU α hα2
  exact l34g_x_f0_of_quotient hI hx2 hxN hα he hαe hnc

end CFSG.OddStandard.SmallF3.Omega
