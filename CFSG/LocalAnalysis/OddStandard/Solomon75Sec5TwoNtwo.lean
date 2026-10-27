module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoCover
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoCount

public section

namespace CFSG.OddStandard.Solomon75

namespace Sec5Two

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

theorem K0_le_normalizer_comp {H A : Subgroup X} (hA : Sec5Comp X n H A) :
    K0 X n H ≤ normalizer (A : Set X) := by
  rw [K0_eq_sSup_sec5Comp]
  refine sSup_le fun A' hA' => ?_
  by_cases heq : A' = A
  · rw [heq]; exact Subgroup.le_normalizer
  · intro a' ha'
    have hC : a' ∈ normalizer (H : Set X) := Subgroup.le_normalizer (comp_le hA' ha')
    refine (normalizes_of_comm hA hC ?_).1
    intro a ha
    exact comm_mem_of_ne hA hA' (Ne.symm heq) a ha a' ha'

@[expose] def NA (D A : Subgroup X) : Subgroup X :=
  centralizerSection A (pPrimeCoreOf 2 D) ⊓ D

omit [Finite X] in
theorem mem_NA {D A : Subgroup X} {c : X} :
    c ∈ NA D A ↔ (c ∈ normalizer (A : Set X) ∧ c ∈ normalizer (pPrimeCoreOf 2 D : Set X) ∧
      ∀ a ∈ A, ⁅a, c⁆ ∈ pPrimeCoreOf 2 D) ∧ c ∈ D := Iff.rfl

omit [Finite X] in
theorem NA_le {D A : Subgroup X} : NA D A ≤ D := inf_le_right

theorem NA_conj_mem {H A : Subgroup X} (hA : Sec5Comp X n H A) {d c : X}
    (hd : d ∈ K0 X n H) (hc : c ∈ NA (K0 X n H) A) : d * c * d⁻¹ ∈ NA (K0 X n H) A := by
  set D := K0 X n H with hD
  obtain ⟨⟨hcA, hcO, hcom⟩, hcD⟩ := mem_NA.1 hc
  have hdA : d ∈ normalizer (A : Set X) := K0_le_normalizer_comp hA hd
  have hdO : d ∈ normalizer (pPrimeCoreOf 2 D : Set X) := mem_normalizer_pPrimeCoreOf_of_mem hd
  refine mem_NA.2 ⟨⟨?_, ?_, ?_⟩, D.mul_mem (D.mul_mem hd hcD) (D.inv_mem hd)⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hdA hcA) (Subgroup.inv_mem _ hdA)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hdO hcO) (Subgroup.inv_mem _ hdO)
  · intro a ha
    have ha' : d⁻¹ * a * d ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hdA) a).1 ha
      simpa using this
    have e : ⁅a, d * c * d⁻¹⁆ = d * ⁅d⁻¹ * a * d, c⁆ * d⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hdO _).1 (hcom _ ha')

theorem core_le_NA {H A : Subgroup X} (hA : Sec5Comp X n H A) :
    pPrimeCoreOf 2 (K0 X n H) ≤ NA (K0 X n H) A := by
  set D := K0 X n H with hD
  intro o ho
  have hoD : o ∈ D := oddCoreOf_le D ho
  refine mem_NA.2 ⟨⟨core_le_normalizer_comp hA ho, Subgroup.le_normalizer ho, ?_⟩, hoD⟩
  intro a ha
  have hAD : a ∈ D := comp_le_K0 hA ha
  have e : ⁅a, o⁆ = (a * o * a⁻¹) * o⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact (pPrimeCoreOf 2 D).mul_mem
    ((Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem hAD) o).1 ho)
    ((pPrimeCoreOf 2 D).inv_mem ho)

theorem comp_le_NA {H A A' : Subgroup X} (hA : Sec5Comp X n H A) (hA' : Sec5Comp X n H A')
    (hne : A' ≠ A) : A' ≤ NA (K0 X n H) A := by
  set D := K0 X n H with hD
  intro a' ha'
  have hD' : a' ∈ D := comp_le_K0 hA' ha'
  have hC : a' ∈ normalizer (H : Set X) := Subgroup.le_normalizer (comp_le hA' ha')
  have hcomm : ∀ a ∈ A, ⁅a, a'⁆ ∈ pPrimeCoreOf 2 D := fun a ha =>
    comm_mem_of_ne hA hA' (Ne.symm hne) a ha a' ha'
  exact mem_NA.2 ⟨⟨(normalizes_of_comm hA hC hcomm).1, mem_normalizer_pPrimeCoreOf_of_mem hD',
    hcomm⟩, hD'⟩

theorem z_mem_NA (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) :
    z ∈ NA (K0 X n (centralizer ({z} : Set X))) A := by
  set D := K0 X n (centralizer ({z} : Set X)) with hD
  have hzD : z ∈ D := z_mem_K0 h hA
  refine mem_NA.2 ⟨⟨K0_le_normalizer_comp hA hzD, mem_normalizer_pPrimeCoreOf_of_mem hzD, ?_⟩,
    hzD⟩
  intro a ha
  have : ⁅a, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (comm_z_of_mem_comp hA ha)
  rw [this]
  exact one_mem _

theorem K0_eq_mul_NA {H A : Subgroup X} (hA : Sec5Comp X n H A) {d : X} (hd : d ∈ K0 X n H) :
    ∃ a ∈ A, ∃ c ∈ NA (K0 X n H) A, d = a * c := by
  set D := K0 X n H with hD
  have hAn : A ≤ normalizer (NA D A : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have haD : a ∈ D := comp_le_K0 hA ha
    constructor
    · intro hc
      exact NA_conj_mem hA haD hc
    · intro hc
      have := NA_conj_mem hA (D.inv_mem haD) hc
      simpa [mul_assoc] using this
  have hle : D ≤ A ⊔ NA D A := by
    rw [hD, K0_eq_sSup_sec5Comp]
    refine sSup_le fun A' hA' => ?_
    by_cases heq : A' = A
    · rw [heq]; exact le_sup_left
    · exact (comp_le_NA hA hA' heq).trans le_sup_right
  exact exists_mul_of_mem_sup hAn (hle hd)

theorem z_mem_zStar_K0_cen (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) {w : X} (hw2 : orderOf w = 2)
    (hwC : w ∈ centralizer ({z} : Set X)) (hcomm : ∀ a ∈ A, ⁅a, w⁆ ∈ oddCoreOf A) :
    z ∈ zStar (K0 X n (centralizer ({w} : Set X))) := by
  have hw_sq : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  have hAK : IsPCompIn 2 (K0 X n (centralizer ({z} : Set X))) A := comp_isPCompIn_K0 hA
  have hnorm : w ∈ normalizer (A : Set X) :=
    (normalizes_of_comm hA (Subgroup.le_normalizer hwC) fun a ha =>
      oddCoreOf_le_of_isPCompIn hAK (hcomm a ha)).1
  have hsc : w ∈ centralizerSection A (pPrimeCoreOf 2 A) :=
    ⟨hnorm, mem_normalizer_oddCoreOf_of_mem_normalizer hnorm, hcomm⟩
  have hus : z ∈ centralizer ({w} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hwC).symm
  obtain ⟨h1, h2, -⟩ := (isIntrinsicIn_z h hA).descend_singleton hA.2 hw_sq hsc hus
  obtain ⟨M, hM, hMn, -⟩ := exists_isIntrinsicIn_centralizer h.hypA h.maxdeg (s := w) hw2
    (inf_le_right : centralizer ({z} : Set X) ⊓ centralizer ({w} : Set X) ≤ _) h1 h2
  exact hM.mem_zStar_K0 hMn

theorem K0_cen_le_sup_inf (h : Sec5Data X n z (zpowers z) S) {w : X}
    (hzw : z ∈ centralizer ({w} : Set X))
    (hzK : z ∈ zStar (K0 X n (centralizer ({w} : Set X)))) :
    K0 X n (centralizer ({w} : Set X)) ≤ pPrimeCoreOf 2 (K0 X n (centralizer ({w} : Set X))) ⊔
      K0 X n (centralizer ({w} : Set X) ⊓ centralizer ({z} : Set X)) := by
  have hz_sq : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z] at this
  refine sSup_le fun M hM => ?_
  obtain ⟨⟨u₀, hu₀⟩, hMn⟩ := hM
  have hMK : M ≤ K0 X n (centralizer ({w} : Set X)) := le_sSup ⟨⟨u₀, hu₀⟩, hMn⟩
  have hzc : z ∈ centralizerSection M (pPrimeCoreOf 2 M) :=
    normalizes_isPCompIn_of_comm_mem hu₀.2.2.1 (Subgroup.le_normalizer hzw)
      (fun m hm => pPrimeCoreOf_K0_le n _ (hzK.2.2.2 m (hMK hm)))
  obtain ⟨u, hu, huz⟩ := hu₀.exists_witness_centralizer_singleton hz_sq hzc
  obtain ⟨h1, h2, h3⟩ := hu.descend_singleton hMn hz_sq hzc huz
  have hMO : pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 (K0 X n (centralizer ({w} : Set X))) :=
    pPrimeCoreOf_le_oddCoreOf hMK (isPComponent_two_iff.1 (hu₀.isPCompIn_K0 hMn).2).1
  have hE : oTwoPrimeOf (M ⊓ centralizer ({z} : Set X)) ≤
      K0 X n (centralizer ({w} : Set X) ⊓ centralizer ({z} : Set X)) :=
    le_sSup ⟨⟨u, h1⟩, h2⟩
  exact h3.trans (sup_le_sup hMO hE)


theorem eq_z_of_mem_zStar (h : Sec5Data X n z (zpowers z) S) {B : Subgroup X}
    (hBD : B ≤ K0 X n (centralizer ({z} : Set X)))
    (hB : IsDoubleCoverOfAlt (↥B ⧸ pPrimeCore 2 ↥B) n) {u : X} (hu : u ∈ zStar B)
    (hu2 : orderOf u = 2) (huC : u ∈ centralizer ({z} : Set X)) : u = z := by
  set C := centralizer ({z} : Set X) with hCdef
  set D := K0 X n C with hD
  set O := pPrimeCoreOf 2 D with hO
  have hn2 : 2 ≤ n := by have := h.maxdeg.1; omega
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu2, pow_two] at this
    exact this
  have hu1 : u ≠ 1 := fun e => by rw [e, orderOf_one] at hu2; omega
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [h.orderOf_z, pow_two] at this
    exact this
  have hz1 : z ≠ 1 := fun e => by
    have := h.orderOf_z
    rw [e, orderOf_one] at this
    omega
  have huD : u ∈ D := hBD hu.1
  have hcomm : ∀ A : Subgroup X, Sec5Comp X n C A → ∀ a ∈ A, ⁅a, u⁆ ∈ O := by
    intro A hA a ha
    have hAD : A ≤ D := comp_le_K0 hA
    have hON : pPrimeCoreOf 2 A ≤ NA D A :=
      (oddCoreOf_le_of_isPCompIn (comp_isPCompIn_K0 hA)).trans (core_le_NA hA)
    have hidx := relIndex_lt_factorial hn2 hAD NA_le (fun d hd c hc => NA_conj_mem hA hd hc)
      (fun d hd => K0_eq_mul_NA hA hd) hA.2 hON (z_mem_comp h hA) (z_mem_NA h hA) hz2 hz1
    have huN : u ∈ NA D A :=
      mem_of_central_mod_core hn2 hBD NA_le (fun d hd c hc => NA_conj_mem hA hd hc) hB hidx hu.1
        huu hu1 hu.2.2.2
    exact (mem_NA.1 huN).1.2.2 a ha
  have huO : u ∈ normalizer (O : Set X) := mem_normalizer_pPrimeCoreOf_of_mem huD
  have huZD : u ∈ zStar D := by
    refine ⟨huD, Subgroup.le_normalizer huD, huO, ?_⟩
    intro k hk
    have hS : ∀ A ∈ {A : Subgroup X | Sec5Comp X n C A}, A ≤ normalizer (O : Set X) :=
      fun A hA a ha => mem_normalizer_pPrimeCoreOf_of_mem (comp_le_K0 hA ha)
    refine forall_comm_mem_of_sSup huO hS hcomm k ?_
    rw [← K0_eq_sSup_sec5Comp]
    exact hk
  have hmem : u ∈ zpowers z ⊔ O := by
    have := zStar_le_pPrimeCoreOf_sup h.pair.sylow huZD
    rwa [sup_comm] at this
  have hzD : z ∈ D := by
    have := h.z_mem_K0
    rwa [normalizer_zpowers_eq_centralizer h.orderOf_z] at this
  have hzn : zpowers z ≤ normalizer (O : Set X) :=
    Subgroup.zpowers_le.2 (mem_normalizer_pPrimeCoreOf_of_mem hzD)
  obtain ⟨ζ, hζ, o, ho, hu_eq⟩ := exists_mul_of_mem_sup hzn hmem
  rcases zpowers_eq_of_orderOf_two h.orderOf_z ζ hζ with e | e
  · exfalso
    rw [e, one_mul] at hu_eq
    have huo : u ∈ oddCoreOf D := hu_eq ▸ ho
    exact hu1 (eq_one_of_mem_oddCoreOf_of_pow (k := 1) huo (by rw [pow_one, pow_two]; exact huu))
  · rw [e] at hu_eq
    have hinv : z⁻¹ * u ∈ oddCoreOf D := by
      have : z⁻¹ * u = o := by rw [hu_eq]; group
      rw [this]; exact ho
    exact (eq_of_inv_mul_mem_oddCoreOf (k := 1) (Subgroup.mem_centralizer_singleton_iff.1 huC).symm
      (by rw [pow_one, pow_two]; exact hz2) (by rw [pow_one, pow_two]; exact huu) hinv).symm


theorem isSylowTwoIn_zStar_K0_cen (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) {w : X} (hw2 : orderOf w = 2)
    (hwC : w ∈ centralizer ({z} : Set X)) (hcomm : ∀ a ∈ A, ⁅a, w⁆ ∈ oddCoreOf A) :
    IsSylowTwoIn (zStar (K0 X n (centralizer ({w} : Set X)))) (zpowers z) := by
  by_cases hwz : w = z
  · subst hwz
    exact h.pair.sylow
  set K := K0 X n (centralizer ({w} : Set X)) with hK
  set H : Subgroup X := centralizer ({w} : Set X) ⊓ centralizer ({z} : Set X) with hH
  set F := K0 X n H with hF
  have hww : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.1 hwC
  have hzw : z ∈ centralizer ({w} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 hww.symm
  have hzK : z ∈ zStar K := z_mem_zStar_K0_cen h hA hw2 hwC hcomm
  have hKF : K ≤ pPrimeCoreOf 2 K ⊔ F := K0_cen_le_sup_inf h hzw hzK
  have h51 := lemma51c_of_hypA h.hypA h.maxdeg w z hw2 h.orderOf_z hww hwz
  have hFK : F ≤ K := h51.trans inf_le_left
  have hFD : F ≤ K0 X n (centralizer ({z} : Set X)) := h51.trans inf_le_right
  have hcov : F ⊔ pPrimeCoreOf 2 K = K :=
    le_antisymm (sup_le hFK (oddCoreOf_le K)) (by rw [sup_comm]; exact hKF)
  have hZK := zStar_le_sup_of_covers hFK hcov
  have hW : ∀ L : Subgroup X, (∃ u, IsIntrinsicIn X H L u) →
      IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n → ∃ u ∈ ({z} : Set X), IsIntrinsicIn X H L u := by
    rintro L ⟨u₀, hu₀⟩ hLn
    have hLF : L ≤ F := comp_le_K0 (A := L) ⟨⟨u₀, hu₀⟩, hLn⟩
    have huL : u₀ ∈ L := hu₀.2.1
    have huC : u₀ ∈ centralizer ({z} : Set X) := (hu₀.2.2.1.1 huL).2
    have hu0z : u₀ = z := eq_z_of_mem_zStar h (hLF.trans hFD) hLn hu₀.mem_zStar hu₀.1 huC
    exact ⟨z, Set.mem_singleton z, hu0z ▸ hu₀⟩
  have hZF := zStar_K0_le_sup_witnesses n H {z} hW
  have hZF' : zStar F ≤ pPrimeCoreOf 2 F ⊔ zpowers z :=
    hZF.trans (sup_le_sup_left ((Subgroup.closure_le _).2 fun u hu =>
      (Set.mem_singleton_iff.1 hu.1) ▸ Subgroup.mem_zpowers z) _)
  have hOF : pPrimeCoreOf 2 F ≤ pPrimeCoreOf 2 K :=
    (pPrimeCoreOf_eq_inf_of_covers hFK hcov).le.trans inf_le_right
  have hZKfin : zStar K ≤ pPrimeCoreOf 2 K ⊔ zpowers z :=
    hZK.trans (sup_le le_sup_left (hZF'.trans (sup_le (hOF.trans le_sup_left) le_sup_right)))
  exact isSylowTwoIn_of_le_sup_odd (Subgroup.zpowers_le.2 hzK) h.isPGroup_Z
    (odd_card_oddCoreOf K) (Subgroup.zpowers_le.2 (mem_normalizer_pPrimeCoreOf_of_mem hzK.1))
    hZKfin

theorem cen_eq_oddCoreOf_sup_of_comm (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) {w : X} (hw2 : orderOf w = 2)
    (hwC : w ∈ centralizer ({z} : Set X)) (hcomm : ∀ a ∈ A, ⁅a, w⁆ ∈ oddCoreOf A) :
    centralizer ({w} : Set X) = oddCoreOf (centralizer ({w} : Set X)) ⊔
      (centralizer ({z} : Set X) ⊓ centralizer ({w} : Set X)) := by
  have := centralizer_eq_oddCoreOf_sup_of_isSylowTwoIn (n := n)
    (isSylowTwoIn_zStar_K0_cen h hA hw2 hwC hcomm)
  rwa [normalizer_zpowers_eq_centralizer h.orderOf_z] at this


end Sec5Two

end CFSG.OddStandard.Solomon75
