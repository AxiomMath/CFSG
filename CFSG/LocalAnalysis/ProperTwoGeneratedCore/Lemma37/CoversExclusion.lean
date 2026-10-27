module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversAbelian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverCentral
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversFacts

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover
open scoped commutatorElement

namespace CoverExclusion

variable {K : Type*} [Group K] {Q : Subgroup K}

@[expose] noncomputable def coverPairing (K : Type*) [Group K] (a b : K ⧸ Subgroup.center K) :
    ZMod 2 :=
  neOneIndicator ⁅Quotient.out a, Quotient.out b⁆

theorem coverPairing_eq {a b : K ⧸ Subgroup.center K} {x y : K}
    (hx : (x : K ⧸ Subgroup.center K) = a) (hy : (y : K ⧸ Subgroup.center K) = b) :
    coverPairing K a b = neOneIndicator ⁅x, y⁆ := by
  unfold coverPairing
  rw [commutatorElement_eq_of_mk_eq (a := x) (b := y) (by rw [hx, QuotientGroup.out_eq'])
    (by rw [hy, QuotientGroup.out_eq'])]

theorem commutatorElement_mul_right_eq {x y y' : K} (hc : ⁅x, y'⁆ ∈ Subgroup.center K) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have h1 : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h1, Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right]

theorem neOneIndicator_mul_of_mem_center (hZ2 : Nat.card (Subgroup.center K) = 2) {s t : K}
    (hs : s ∈ Subgroup.center K) (ht : t ∈ Subgroup.center K) :
    neOneIndicator (s * t) = neOneIndicator s + neOneIndicator t :=
  neOneIndicator_mul (eq_or_of_mem_center hZ2 hs ht) (mul_self_eq_one_of_mem_center hZ2 hs)

theorem commute_of_pairing (hZ2 : Nat.card (Subgroup.center K) = 2)
    (hab : ∀ x ∈ centerPreimage Q, ∀ y ∈ centerPreimage Q, x * y = y * x)
    (hPV : CoverPairingVanishes (K ⧸ Subgroup.center K) (centralImage Q)) {x : K}
    (hx : (x : K ⧸ Subgroup.center K) ∈ centralImage Q) {w : K} (hw : w ∈ centerPreimage Q) :
    x * w = w * x := by
  have hcZ : ∀ a b : K, (a : K ⧸ Subgroup.center K) ∈ centralImage Q →
      InCenterOf (centralImage Q) (b : K ⧸ Subgroup.center K) → ⁅a, b⁆ ∈ Subgroup.center K :=
    fun a b ha hb => commutatorElement_mem_center ha (mem_centerPreimage_iff.mpr hb)
  have hout : ∀ a : K ⧸ Subgroup.center K, ((Quotient.out a : K) : K ⧸ _) = a :=
    fun a => QuotientGroup.out_eq' a
  have key := hPV (coverPairing K)
    (by
      intro a ha a' ha' b hb
      rw [← hout a] at ha
      rw [← hout a'] at ha'
      rw [← hout b] at hb
      rw [coverPairing_eq (x := Quotient.out a * Quotient.out a') (y := Quotient.out b)
          (by rw [QuotientGroup.mk_mul, hout, hout]) (hout b),
        commutatorElement_mul_left_eq (hcZ _ _ ha' hb),
        neOneIndicator_mul_of_mem_center hZ2 (hcZ _ _ ha' hb) (hcZ _ _ ha hb), add_comm]
      rfl)
    (by
      intro a ha b b' hb hb'
      rw [← hout a] at ha
      rw [← hout b] at hb
      rw [← hout b'] at hb'
      rw [coverPairing_eq (x := Quotient.out a) (y := Quotient.out b * Quotient.out b')
          (hout a) (by rw [QuotientGroup.mk_mul, hout, hout]),
        commutatorElement_mul_right_eq (hcZ _ _ ha hb'),
        neOneIndicator_mul_of_mem_center hZ2 (hcZ _ _ ha hb) (hcZ _ _ ha hb')]
      rfl)
    (by
      intro a b ha hb
      rw [← hout a] at ha
      rw [← hout b] at hb
      unfold coverPairing
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hab _ (mem_centerPreimage_iff.mpr ha) _
        (mem_centerPreimage_iff.mpr hb)), neOneIndicator_one])
    (by
      intro g _ a ha b hb
      rw [← hout a] at ha
      rw [← hout b] at hb
      set g' := Quotient.out g
      rw [coverPairing_eq (x := g' * Quotient.out a * g'⁻¹) (y := g' * Quotient.out b * g'⁻¹)
          (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hout, hout])
          (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hout, hout]),
        show ⁅g' * Quotient.out a * g'⁻¹, g' * Quotient.out b * g'⁻¹⁆ =
          g' * ⁅Quotient.out a, Quotient.out b⁆ * g'⁻¹ by simp only [commutatorElement_def]; group,
        Subgroup.mem_center_iff.mp (hcZ _ _ ha hb) g', mul_inv_cancel_right]
      rfl)
  have h := key _ hx _ (mem_centerPreimage_iff.mp hw)
  rw [coverPairing_eq rfl rfl] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp (eq_one_of_neOneIndicator_eq_zero h)

theorem false_of_benderCoverFacts [Finite K] (hperf : commutator K = ⊤)
    (hZ2 : Nat.card (Subgroup.center K) = 2) (Q : Sylow 2 K)
    (hBF : BenderBorelFacts (K ⧸ Subgroup.center K) (centralImage (Q : Subgroup K)))
    (hCF : BenderCoverFacts (K ⧸ Subgroup.center K) (centralImage (Q : Subgroup K))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : IsPGroup 2 (Subgroup.center K) := IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])
  have hZQ : Subgroup.center K ≤ (Q : Subgroup K) := hZ.le_sylow_of_normal Q
  obtain ⟨D, -, -, -, htrans, -⟩ := hBF.torus
  have hQ2 : IsPGroup 2 (centralImage (Q : Subgroup K)) := Q.isPGroup'.map _
  have hab : ∀ x ∈ centerPreimage (Q : Subgroup K), ∀ y ∈ centerPreimage (Q : Subgroup K),
      x * y = y * x := by
    intro x hx y hy
    rcases hCF.center with hcard | hcomm
    · exact centerPreimage_comm_of_card hZ2 htrans
        (fun w hw => mul_self_eq_one_of_transitive hQ2 htrans hw) hcard hx hy
    · exact centerPreimage_comm_of_commutator hcomm hx hy
  have hcard := hBF.center_card
  have : Finite {w : K ⧸ Subgroup.center K // InCenterOf (centralImage (Q : Subgroup K)) w} :=
    Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨w, hw⟩ := exists_notMem_of_card_lt
    ({⟨1, inCenterOf_one _⟩} :
      Finset {w : K ⧸ Subgroup.center K // InCenterOf (centralImage (Q : Subgroup K)) w})
    (by rw [Finset.card_singleton]; omega)
  have hw1 : (w : K ⧸ Subgroup.center K) ≠ 1 := fun h =>
    hw (Finset.mem_singleton.mpr (Subtype.ext h))
  have hw₀W : Quotient.out (w : K ⧸ Subgroup.center K) ∈ centerPreimage (Q : Subgroup K) :=
    mem_centerPreimage_iff.mpr (by rw [QuotientGroup.out_eq']; exact w.2)
  have hw₀Q : Quotient.out (w : K ⧸ Subgroup.center K) ∈ (Q : Subgroup K) :=
    (mk_mem_centralImage_iff hZQ).mp (by rw [QuotientGroup.out_eq']; exact w.2.1)
  have hw₀Z : Quotient.out (w : K ⧸ Subgroup.center K) ∉ Subgroup.center K := fun h => hw1 (by
    rw [← QuotientGroup.out_eq' (w : K ⧸ Subgroup.center K)]
    exact (QuotientGroup.eq_one_iff _).mpr h)
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center K)).mp hZ2
  have hu' : ∀ s ∈ Subgroup.center K, s * s = 1 → s = 1 ∨ s = (u : K) := by
    intro s hs _
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · exact Or.inr (congrArg Subtype.val (hu ⟨s, hs⟩ fun h => hs1 (congrArg Subtype.val h)))
  have hbot := center_eq_bot_of_borelFacts hperf hZ hu' Q hBF hw₀Q
    (fun q hq => commute_of_pairing hZ2 hab hCF.pairing (Subgroup.mem_map_of_mem _ hq) hw₀W)
    hw₀Z
  rw [hbot, Subgroup.card_bot] at hZ2
  exact absurd hZ2 (by decide)

end CoverExclusion

end CFSG.ProperTwoGeneratedCore.Lemma37
