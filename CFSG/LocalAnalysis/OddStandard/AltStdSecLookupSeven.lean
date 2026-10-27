module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEight
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSevenLie
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineAltSeven

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

section Order

variable {X : Type} [Group X] {t : X} {A : Subgroup X} {m : ℕ}

theorem card_centralizer_dvd_of_exactShape (h : ExactShape t A m) (hm5 : 5 ≤ m) (hm6 : m ≠ 6) :
    Nat.card (centralizer ({t} : Set X)) ∣ 2 * m.factorial := by
  classical
  obtain ⟨eA⟩ := h.iso
  set A' : Subgroup (centralizer ({t} : Set X)) := A.subgroupOf (centralizer ({t} : Set X))
    with hA'
  have hA'N : A'.Normal := by
    constructor
    intro a ha c
    rw [hA', mem_subgroupOf] at ha ⊢
    have := (mem_normalizer_iff.1 (h.cent_le_norm c.2) a).1 ha
    simpa using this
  set φ : centralizer ({t} : Set X) →* MulAut A' := MulAut.conjNormal with hφ
  have hker : φ.ker.map (centralizer ({t} : Set X)).subtype = zpowers t := by
    rw [← h.cent_cent]
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hc
      refine Subgroup.mem_inf.2 ⟨?_, c.2⟩
      rw [mem_centralizer_iff]
      intro a ha
      have h1 := congrArg (fun ψ : MulAut A' => ((ψ ⟨⟨a, h.le_cent ha⟩, ha⟩ : A') : X)) hc
      simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply, coe_mul, coe_inv] at h1
      calc a * (c : X) = (c : X) * a * (c : X)⁻¹ * c := by rw [h1]
        _ = c * a := by group
    · intro hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.1 hx
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      ext a
      simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply, coe_mul, coe_inv]
      have h1 := mem_centralizer_iff.1 hxA (a : X) a.2
      calc x * (a : X) * x⁻¹ = (a : X) * x * x⁻¹ := by rw [h1]
        _ = a := by group
  have hkcard : Nat.card φ.ker = 2 := by
    rw [← Subgroup.card_map_of_injective (centralizer ({t} : Set X)).subtype_injective, hker,
      Nat.card_zpowers, h.order]
  have hrange : Nat.card φ.range ∣ m.factorial := by
    have h1 : Nat.card φ.range ∣ Nat.card (MulAut A') := Subgroup.card_subgroup_dvd_card _
    have eA' : A' ≃* alternatingGroup (Fin m) := (subgroupOfEquivOfLe h.le_cent).trans eA
    have h2 : Nat.card (MulAut A') = m.factorial := by
      rw [Nat.card_congr (MulAut.congr eA').toEquiv,
        ← Nat.card_congr (Equiv.ofBijective _
          (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm5 hm6)),
        Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rwa [h2] at h1
  have hC : Nat.card (centralizer ({t} : Set X)) = Nat.card φ.ker * Nat.card φ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  rw [hC, hkcard]
  exact Nat.mul_dvd_mul_left 2 hrange

theorem card_fixedSubgroup_dvd_of_exactShape {W : Subgroup X} [W.Normal] (h : ExactShape t A m)
    (hm5 : 5 ≤ m) (hm6 : m ≠ 6) :
    Nat.card (fixedSubgroup (MulAut.conjNormal t : MulAut W)) ∣ 2 * m.factorial := by
  refine dvd_trans ?_ (card_centralizer_dvd_of_exactShape h hm5 hm6)
  rw [← Subgroup.card_map_of_injective W.subtype_injective]
  apply Subgroup.card_dvd_of_le
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h1 : (MulAut.conjNormal t : MulAut W) w = w := hw
  have h2 := congrArg Subtype.val h1
  simp only [MulAut.conjNormal_apply] at h2
  calc (w : X) * t = t * w * t⁻¹ * t := by rw [h2]
    _ = t * w := by group

end Order


theorem exactShape_almostSimple_seven (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput) {X : Type} [Group X]
    [Finite X] {t : X} {A : Subgroup X} (hK : CFSG.SectionRank.IsKGroupCat X)
    (hOX : CFSG.oddCore X = ⊥) (h : ExactShape t A 7) (hF : AlmostSimple X) : SymOutcome t 7 := by
  obtain ⟨W, hWN, hWs, hWnab, hCW, hcat, hAW, hcomp⟩ := almostSimple_setup hK hOX h (by norm_num) hF
  have := hWN
  have := hWs
  obtain ⟨eA⟩ := h.iso
  set σ : MulAut W := MulAut.conjNormal t with hσ
  have hσ2 : σ * σ = 1 := conjNormal_mul_self h.order
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 : t ∈ centralizer (W : Set X) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h3 := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : X)) h1
      simp only [hσ, MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc w * t = t * w * t⁻¹ * t := by rw [h3]
        _ = t * w := by group
    rw [hCW, mem_bot] at h2
    have h4 := h.order
    rw [h2, orderOf_one] at h4
    omega
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  obtain ⟨hle, hD⟩ := le_fixedSubgroup_and_isComponent hAW hcomp
  set D := (A.subgroupOf W).subgroupOf (fixedSubgroup σ) with hDdef
  have eD : D ≃* alternatingGroup (Fin 7) :=
    ((subgroupOfEquivOfLe hle).trans (subgroupOfEquivOfLe hAW)).trans eA
  have hsmall : FixedCentralizerTwoSmall σ D := twoSmall_of_exactShape h hAW hle
  have hcard : Nat.card (fixedSubgroup σ) ∣ 10080 :=
    card_fixedSubgroup_dvd_of_exactShape (W := W) h (by norm_num) (by norm_num)
  rcases (Milestones.ct_catalog_nonabelian_type_partition W hWnab).mp hcat with
    ⟨n, -, ⟨eW⟩⟩ | hodd | heven | hsp
  · exact (symOutcome_of_alt h (by norm_num) hAW hCW hcomp eW).1
  · exact absurd ⟨eD⟩ (not_alt7_of_oddLieType hGLS hO hodd hσo hD)
  · exact (false_of_evenLie_alt7 hO hEO hWnab heven hσ2 hσ1 hD eD).elim
  · exact (SeitzReduction.SporadicRefine.false_of_sporadic_alt_seven hWs hWnab hsp hσo hD eD
      hcard hsmall).elim

theorem exactShape_trichotomy_seven (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput) {X : Type} [Group X]
    [Finite X] {t : X} {A : Subgroup X} (hK : CFSG.SectionRank.IsKGroupCat X)
    (hOX : CFSG.oddCore X = ⊥) (h : ExactShape t A 7) :
    t ∈ center X ∨ WreathOutcome t A 7 ∨ SymOutcome t 7 := by
  rcases section_dichotomy hOX h (by norm_num) with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (exactShape_almostSimple_seven hGLS hO hEO hK hOX h h3))

end CFSG.OddStandard.AltStdSec
