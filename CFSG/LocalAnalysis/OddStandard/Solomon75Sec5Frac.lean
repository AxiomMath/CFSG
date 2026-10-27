module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneZ

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem K0_K0_inf_ne_bot_of_mem_centralizerSection {s r : X} (hr2 : r ^ 2 = 1) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B)
    (hrB : r ∈ centralizerSection B (pPrimeCoreOf 2 B)) :
    K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) ≠ ⊥ := by
  obtain ⟨u₀, hu₀⟩ := hB.1
  obtain ⟨u, hu, huC⟩ := hu₀.exists_witness_centralizer_singleton hr2 hrB
  obtain ⟨hd1, hd2, -⟩ := hu.descend_singleton hB.2 hr2 hrB huC
  set E : Subgroup X := oTwoPrimeOf (B ⊓ centralizer ({r} : Set X)) with hE
  have hBK : B ≤ K0 X n (centralizer ({s} : Set X)) := le_sSup hB
  have hEB : E ≤ B := (oTwoPrimeOf_le _).trans inf_le_left
  have hle : E ≤ K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X) :=
    le_inf (hEB.trans hBK) ((oTwoPrimeOf_le _).trans inf_le_right)
  have hI : IsIntrinsicIn X (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) E u :=
    ⟨hd1.1, hd1.2.1, ⟨hle, isPComponent_subgroupOf_mono hle
      (inf_le_inf_right _ (K0_le n (centralizer ({s} : Set X)))) hd1.2.2.1.2⟩, hd1.2.2.2⟩
  intro hbot
  have hEK : E ≤ K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({r} : Set X)) :=
    le_sSup ⟨⟨u, hI⟩, hd2⟩
  rw [hbot] at hEK
  exact ne_bot_of_isDoubleCoverOfAlt hd2 (le_bot_iff.1 hEK)

theorem Sec5Data.mem_Z_of_comm_mem (h : Sec5Data X n z Z S) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {y : X} (hyA : y ∈ A) (hy2 : y * y = 1)
    (hcommA : ∀ a' ∈ A, ⁅a', y⁆ ∈ oddCoreOf A) : y ∈ Z := by
  classical
  set N : Subgroup X := normalizer (Z : Set X) with hN
  set D : Subgroup X := K0 X n N with hD
  have hDN : D ≤ N := K0_le n N
  have hND : N ≤ normalizer (D : Set X) := Sec5Data.le_normalizer_K0 X n N
  have hAD : A ≤ D := le_sSup hA
  have hyD : y ∈ D := hAD hyA
  have hOD : oddCoreOf D = D ⊓ oddCoreOf N := oddCoreOf_eq_inf hDN hND
  have hcommD : ∀ d ∈ D, ⁅d, y⁆ ∈ oddCoreOf D := by
    have hS' : ∀ A' ∈ {B : Subgroup X | Sec5Comp X n N B}, A' ≤ normalizer (oddCoreOf D : Set X) :=
      fun A' hA' => (le_sSup hA' : A' ≤ D).trans (le_normalizer_oddCoreOf D)
    have h' : ∀ A' ∈ {B : Subgroup X | Sec5Comp X n N B}, ∀ a' ∈ A',
        ⁅a', y⁆ ∈ oddCoreOf D := by
      intro A' hA' a' ha'
      have hA'D : A' ≤ D := le_sSup hA'
      have hmemD : ⁅a', y⁆ ∈ D := by
        simp only [commutatorElement_def]
        exact D.mul_mem (D.mul_mem (D.mul_mem (hA'D ha') hyD) (D.inv_mem (hA'D ha')))
          (D.inv_mem hyD)
      rw [hOD]
      refine ⟨hmemD, ?_⟩
      by_cases hAA : A' = A
      · subst hAA
        exact oddCoreOf_le_of_isPCompIn hA.isPCompIn (hcommA a' ha')
      · exact commutator_mem_oddCoreOf_of_ne hA'.isPCompIn hA.isPCompIn hAA ha' hyA
    have := forall_comm_mem_of_sSup (le_normalizer_oddCoreOf D hyD) hS' h'
    intro d hd
    exact this d (by rw [← K0_eq_sSup_sec5Comp]; exact hd)
  have hyW : y ∈ oddTwoCoreOf D := by
    let q : ↥D →* ↥D ⧸ pPrimeCore 2 ↥D := QuotientGroup.mk' (pPrimeCore 2 ↥D)
    let yD : ↥D := ⟨y, hyD⟩
    have hcen : ∀ g : ↥D, Commute (q g) (q yD) := by
      intro g
      have h1 : q ⁅g, yD⁆ = 1 := by
        refine (QuotientGroup.eq_one_iff _).2 ?_
        have := hcommD g g.2
        exact (mem_oddCoreOf_iff.1 this).2
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_commute.1 h1
    have hnorm : (Subgroup.zpowers (q yD)).Normal := by
      refine ⟨fun m hm g' => ?_⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
      have hc : Commute (q g) (q yD ^ k) := (hcen g).zpow_right k
      rw [show (QuotientGroup.mk g : ↥D ⧸ pPrimeCore 2 ↥D) = q g from rfl, hc.eq]
      simp
    have hsq : q yD * q yD = 1 := by
      rw [← map_mul]
      have : yD * yD = 1 := Subtype.ext hy2
      rw [this, map_one]
    have hle := CFSG.LocalAnalysis.ComponentInitial.le_pCore hnorm
      (isPGroup_zpowers_of_mul_self hsq)
    exact ⟨yD, Subgroup.mem_comap.2 (hle (Subgroup.mem_zpowers _)), rfl⟩
  have hyN : y ∈ normalizer (Z : Set X) := hDN hyD
  exact h.l52.a.2.mem_of_mem_normalizer hyW (isPGroup_zpowers_of_mul_self hy2) hyN

theorem Sec5Data.comm_of_mem_Z_of_normalizes (h : Sec5Data X n z Z S) {s : X}
    (hsN : s ∈ normalizer (Z : Set X)) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) (hsA : s ∈ normalizer (A : Set X)) {w : X}
    (hwZ : w ∈ Z) (hwA : w ∈ A) (hw1 : w ≠ 1) : w * s = s * w := by
  set N : Subgroup X := normalizer (Z : Set X) with hN
  have hAD : A ≤ K0 X n N := le_sSup hA
  let C := AhatData.CoverSetup.ofCover hA.2
  have hvZ : s * w * s⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hsN w).1 hwZ
  have hvA : s * w * s⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hsA w).1 hwA
  have hv1 : s * w * s⁻¹ ≠ 1 := by
    intro h1
    apply hw1
    have := congrArg (fun t => s⁻¹ * t * s) h1
    simpa [mul_assoc] using this
  have hcen : ∀ u : X, u ∈ Z → ∀ hu : u ∈ A,
      (QuotientGroup.mk (⟨u, hu⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) ∈
        Subgroup.center (↥A ⧸ pPrimeCore 2 ↥A) := fun u huZ hu =>
    mk_mem_center_of_comm hu fun a ha => (h.Z_le_center_K0 huZ (hAD ha)).symm
  have hne : ∀ u : X, u ∈ Z → ∀ hu : u ∈ A, u ≠ 1 →
      (QuotientGroup.mk (⟨u, hu⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) ≠ 1 := by
    intro u huZ hu hu1 h1
    have h2 : u ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨hu, (QuotientGroup.eq_one_iff _).1 h1⟩
    exact hu1 (eq_one_of_mem_of_mem_odd (oddCoreOf A) Z (odd_card_oddCoreOf A) h.isPGroup_Z huZ h2)
  have heq := C.center_eq_of_ne_one (hcen w hwZ hwA) (hcen _ hvZ hvA) (hne w hwZ hwA hw1)
    (hne _ hvZ hvA hv1)
  have h3 : (⟨w, hwA⟩ : ↥A)⁻¹ * ⟨s * w * s⁻¹, hvA⟩ ∈ pPrimeCore 2 ↥A := QuotientGroup.eq.1 heq
  have h4 : w⁻¹ * (s * w * s⁻¹) ∈ oddCoreOf A := ⟨_, h3, rfl⟩
  have h5 : w⁻¹ * (s * w * s⁻¹) ∈ Z := Z.mul_mem (Z.inv_mem hwZ) hvZ
  have h6 := eq_one_of_mem_of_mem_odd (oddCoreOf A) Z (odd_card_oddCoreOf A) h.isPGroup_Z h5 h4
  have h7 : s * w * s⁻¹ = w := by
    have := congrArg (fun t => w * t) h6
    simpa using this
  have : s * w = w * s := by
    have := congrArg (fun t => t * s) h7
    simpa [mul_assoc] using this
  exact this.symm

end CFSG.OddStandard.Solomon75
