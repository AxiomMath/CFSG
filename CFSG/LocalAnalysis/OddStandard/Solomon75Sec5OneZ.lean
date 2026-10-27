module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneSetup
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentMirror

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

omit [Finite X] in
theorem isPGroup_zpowers_of_mul_self {G : Type*} [Group G] {x : G} (hx : x * x = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers x) := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

omit [Finite X] in
theorem mk_mem_center_of_comm {A : Subgroup X} {u : X} (hu : u ∈ A)
    (h : ∀ a ∈ A, a * u = u * a) :
    (QuotientGroup.mk (⟨u, hu⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) ∈
      Subgroup.center (↥A ⧸ pPrimeCore 2 ↥A) := by
  rw [Subgroup.mem_center_iff]
  intro k
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective k
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (h b b.2)

theorem Sec5Data.exists_mem_Z_inf (h : Sec5Data X n z Z S) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) : ∃ w, w ∈ Z ∧ w ∈ A ∧ w ≠ 1 := by
  set N : Subgroup X := normalizer (Z : Set X) with hN
  set D : Subgroup X := K0 X n N with hD
  have hDN : D ≤ N := K0_le n N
  have hND : N ≤ normalizer (D : Set X) := Sec5Data.le_normalizer_K0 X n N
  have hAD : A ≤ D := le_sSup hA
  let C := AhatData.CoverSetup.ofCover hA.2
  have hnt : Nontrivial (Subgroup.center (↥A ⧸ pPrimeCore 2 ↥A)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [C.center_card]; norm_num)
  obtain ⟨c', hc'⟩ := exists_ne (1 : Subgroup.center (↥A ⧸ pPrimeCore 2 ↥A))
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (c' : ↥A ⧸ pPrimeCore 2 ↥A)
  have hc2 : (c' : ↥A ⧸ pPrimeCore 2 ↥A) * c' = 1 := C.sq_of_mem_center c'.2
  obtain ⟨y, hyy, hy⟩ := exists_involution_rep a (by rw [ha]; exact hc2)
  have hyc : (QuotientGroup.mk y : ↥A ⧸ pPrimeCore 2 ↥A) = c' := hy.trans ha
  have hy1 : (y : X) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext h1
    rw [this] at hyc
    apply hc'
    exact Subtype.ext (by simpa using hyc.symm)
  have hyD : (y : X) ∈ D := hAD y.2
  have hy2 : (y : X) * y = 1 := by simpa using congrArg Subtype.val hyy
  have hcommA : ∀ a' ∈ A, ⁅a', (y : X)⁆ ∈ oddCoreOf A := by
    intro a' ha'
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥A)) ⁅(⟨a', ha'⟩ : ↥A), y⁆ = 1 := by
      rw [map_commutatorElement]
      refine commutatorElement_eq_one_iff_mul_comm.2 ?_
      show QuotientGroup.mk (⟨a', ha'⟩ : ↥A) * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk (⟨a', ha'⟩ : ↥A)
      rw [hyc]
      exact Subgroup.mem_center_iff.1 c'.2 _
    exact mem_oddCoreOf_iff.2 ⟨by
      simp only [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha' y.2) (A.inv_mem ha')) (A.inv_mem y.2),
      (QuotientGroup.eq_one_iff _).1 h1⟩
  have hOD : oddCoreOf D = D ⊓ oddCoreOf N := oddCoreOf_eq_inf hDN hND
  have hcommD : ∀ d ∈ D, ⁅d, (y : X)⁆ ∈ oddCoreOf D := by
    have hS' : ∀ A' ∈ {B : Subgroup X | Sec5Comp X n N B}, A' ≤ normalizer (oddCoreOf D : Set X) :=
      fun A' hA' => (le_sSup hA' : A' ≤ D).trans (le_normalizer_oddCoreOf D)
    have h' : ∀ A' ∈ {B : Subgroup X | Sec5Comp X n N B}, ∀ a' ∈ A',
        ⁅a', (y : X)⁆ ∈ oddCoreOf D := by
      intro A' hA' a' ha'
      have hA'D : A' ≤ D := le_sSup hA'
      have hmemD : ⁅a', (y : X)⁆ ∈ D := by
        simp only [commutatorElement_def]
        exact D.mul_mem (D.mul_mem (D.mul_mem (hA'D ha') hyD) (D.inv_mem (hA'D ha')))
          (D.inv_mem hyD)
      rw [hOD]
      refine ⟨hmemD, ?_⟩
      by_cases hAA : A' = A
      · subst hAA
        exact oddCoreOf_le_of_isPCompIn hA.isPCompIn (hcommA a' ha')
      · exact commutator_mem_oddCoreOf_of_ne hA'.isPCompIn hA.isPCompIn hAA ha' y.2
    have := forall_comm_mem_of_sSup (le_normalizer_oddCoreOf D hyD) hS' h'
    intro d hd
    exact this d (by rw [← K0_eq_sSup_sec5Comp]; exact hd)
  have hyW : (y : X) ∈ oddTwoCoreOf D := by
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
  have hyN : (y : X) ∈ normalizer (Z : Set X) := hDN hyD
  exact ⟨y, h.l52.a.2.mem_of_mem_normalizer hyW (isPGroup_zpowers_of_mul_self hy2) hyN, y.2, hy1⟩

theorem Sec5S.comm_of_mem_Z (hS : Sec5S X n z Z S s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {w : X} (hwZ : w ∈ Z) (hwA : w ∈ A)
    (hw1 : w ≠ 1) : w * s = s * w := by
  have h := hS.data
  set N : Subgroup X := normalizer (Z : Set X) with hN
  have hAD : A ≤ K0 X n N := le_sSup hA
  let C := AhatData.CoverSetup.ofCover hA.2
  have hsA : s ∈ normalizer (A : Set X) := hS.norm A hA
  have hvZ : s * w * s⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hS.inv.mem w).1 hwZ
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
