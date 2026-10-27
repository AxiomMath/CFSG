module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Ident

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem inf_centralizer_mul_eq {L : Subgroup G} {t : G} (hcomm : ∀ l ∈ L, l * t = t * l)
    (w : G) :
    L ⊓ centralizer ({w * t} : Set G) = L ⊓ centralizer ({w} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxL, hx⟩
    refine ⟨hxL, ?_⟩
    have hxt := hcomm x hxL
    have h1 : x * w * t = w * x * t := by
      calc x * w * t = x * (w * t) := by rw [mul_assoc]
        _ = w * t * x := hx
        _ = w * (t * x) := by rw [mul_assoc]
        _ = w * (x * t) := by rw [← hxt]
        _ = w * x * t := by rw [mul_assoc]
    exact mul_right_cancel h1
  · rintro ⟨hxL, hx⟩
    refine ⟨hxL, ?_⟩
    have hxt := hcomm x hxL
    calc x * (w * t) = x * w * t := by rw [mul_assoc]
      _ = w * x * t := by rw [hx]
      _ = w * (x * t) := by rw [mul_assoc]
      _ = w * (t * x) := by rw [hxt]
      _ = w * t * x := by rw [mul_assoc]

theorem isConj_of_inner_partner [Finite G] (h36 : Asc82Lemma36) (hInner : Asc82OmegaPlusInner)
    (hPC : Asc82OmegaPlusPocketedConj) (hPL : Asc82OmegaPlusPocketLift) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hΩ : LieModel (↥L ⧸ oddCore ↥L) .POmegaPlus 4 3 1) {z : G}
    (hz : IsI4PlusIn L z) {w : G} (hw2 : orderOf w = 2) (hwL : w ∈ L) (g : G)
    (hg : g⁻¹ * t * g = w * t) : IsConj (t * z) t := by
  have hLt : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hcomm : ∀ l ∈ L, l * t = t * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLt hl)
  have hwt : w * t = t * w := hcomm w hwL
  have hΩL : IsOmegaPlusIn L := ⟨hS.inF, hΩ⟩
  have hts : IsConj t (g⁻¹ * t * g) := isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩
  by_cases hwp : IsI4PlusIn L w
  · obtain ⟨a, haL, ha⟩ := hPC G L hΩL z w hz hwp
    have h1 : a⁻¹ * (t * z) * a = g⁻¹ * t * g := by
      rw [hg, conj_mul_of_commute (hcomm a haL) z, ha, hwt]
    have h2 : IsConj (t * z) (g⁻¹ * t * g) := isConj_iff.2 ⟨a⁻¹, by rw [inv_inv]; exact h1⟩
    exact h2.trans hts.symm
  · obtain ⟨X, u, hXc, hwX, hX2, huX, a, haL, ha⟩ := hInner G L hΩL w hw2 hwL hwp
    have hXF : InFStar X := Or.inl ⟨hXc.isQuasisimple, Or.inr hX2⟩
    have hst : (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := by
      rw [hg, ← mul_assoc t w t, ← hwt]
    have hCs : IsComponentIn X (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)) := by
      rw [hg, inf_centralizer_mul_eq hcomm w]
      exact hXc
    have hXL' : X ≤ CFSG.conjugate L g := le_conjugate_of_isComponentIn h36 hS rfl hst hCs hXF
    have hS' := hS.conjugate g
    have hX1 : IsComponentIn X
        (centralizer ({t} : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G)) :=
      hCs.of_normal_inf_centralizer hLt (conjugate_eq_self_of_lemma36 h36 hS)
    have hL's : CFSG.conjugate L g ≤ centralizer ({g⁻¹ * t * g} : Set G) := hS'.component.le
    have hXLt : X ≤ centralizer ({t} : Set G) := (hCs.le.trans inf_le_left).trans hLt
    have hXt : IsComponentIn X (CFSG.conjugate L g ⊓ centralizer ({t} : Set G)) :=
      hX1.mono (le_inf hXL' hXLt) fun x hx => ⟨hx.2, hL's hx.1⟩
    have htc : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hst.symm
    have htn : t ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
      mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS' t htc)
    have hΩ' : IsOmegaPlusIn (CFSG.conjugate L g) := isOmegaPlusIn_conjugate hΩL g
    have hu' : IsI4PlusIn (CFSG.conjugate L g) u :=
      hPL G (CFSG.conjugate L g) hΩ' t hS.involution htn X hXt u huX
    obtain ⟨m, hmL', hm⟩ := hPC G (CFSG.conjugate L g) hΩ' (g⁻¹ * z * g) u (hz.conjugate g) hu'
    have hl : g * m * g⁻¹ ∈ L := (mem_conjugate_iff L g m).1 hmL'
    have hu_eq : u = g⁻¹ * ((g * m * g⁻¹)⁻¹ * z * (g * m * g⁻¹)) * g := by
      rw [← hm]
      group
    have hus : u * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u :=
      Subgroup.mem_centralizer_singleton_iff.mp ((hCs.le.trans inf_le_right) huX.mem)
    have hat := hcomm a haL
    have hau : a⁻¹ * (g⁻¹ * t * g) * a = u * (g⁻¹ * t * g) := by
      rw [hg]
      calc a⁻¹ * (w * t) * a = a⁻¹ * w * (t * a) := by group
        _ = a⁻¹ * w * (a * t) := by rw [hat]
        _ = a⁻¹ * w * a * t := (mul_assoc _ _ _).symm
        _ = u * w * t := by rw [ha]
        _ = u * (w * t) := by rw [mul_assoc]
    have hsu : (g⁻¹ * t * g) * u =
        g⁻¹ * ((g * m * g⁻¹)⁻¹ * (t * z) * (g * m * g⁻¹)) * g := by
      rw [hu_eq, conj_mul_of_commute (hcomm _ hl) z]
      group
    have hconj1 : IsConj (t * z) ((g⁻¹ * t * g) * u) := by
      refine isConj_iff.2 ⟨g⁻¹ * (g * m * g⁻¹)⁻¹, ?_⟩
      rw [hsu]
      group
    have hconj2 : IsConj (g⁻¹ * t * g) ((g⁻¹ * t * g) * u) := by
      refine isConj_iff.2 ⟨a⁻¹, ?_⟩
      rw [inv_inv, ← hus]
      exact hau
    exact (hconj1.trans hconj2.symm).trans hts.symm

end CFSG.OddStandard.SmallF3.Omega
