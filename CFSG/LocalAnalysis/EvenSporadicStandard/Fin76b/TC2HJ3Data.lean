module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Table
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3
public import Certificates.Certificate25890

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.J3

theorem involution_conj_t0_j3P
    {a : Equiv.Perm (Fin 6156)} (ha : a ∈ j3P) (ha2 : a * a = 1)
    (ha1 : a ≠ 1) : ∃ c ∈ j3P, a = c * tp 6156 t0 * c⁻¹ := by
  obtain ⟨-, -, -, -, hP1, -, -, hcls⟩ := class_data
  have ha2' : orderOf a = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  obtain ⟨g, hg, hv | hv⟩ := hcls a (mem_sup_left ha) ha2'
  · exact ⟨g, hg, hv⟩
  · exfalso
    apply hP1
    have : tp 6156 t1 = g⁻¹ * a * g := by rw [hv]; group
    rw [this]
    exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) ha) hg

theorem outerEData_j3P :
    OuterEData ↥j3P := by
  classical
  obtain ⟨-, -, -, -, -, -, hSR, -, -⟩ :=
    j3_centData
  have hSR' : CFSG.Sporadic.SmallOddCore.j3S ≤ j3R := hSR
  obtain ⟨e, he, -, -, hcardAut⟩ := ctuc_j3_full_automorphism_permutation_model
  have hfin : Finite (MulAut ↥j3P) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; norm_num)
  set t := tp 6156 t0 with htdef
  obtain ⟨hP0, h20, -, -, -, -, -, -⟩ := class_data
  have ht2 : t * t = 1 := by
    rw [← sq, htdef, ← h20]
    exact pow_orderOf_eq_one _
  have ht1' : t ≠ 1 := fun h => by
    rw [htdef] at h
    rw [h, orderOf_one] at h20
    exact absurd h20 (by norm_num)
  have htR : t ∈ j3R := (le_sup_left : j3P ≤ j3P ⊔ zpowers j3u) hP0
  have hinner : ∀ (x : Equiv.Perm (Fin 6156)) (hxR : x ∈ j3R) (hxP : x ∈ j3P),
      e ⟨x, hxR⟩ = MulAut.conj (⟨x, hxP⟩ : ↥j3P) := by
    intro x hxR hxP
    refine MulEquiv.ext fun p => Subtype.ext ?_
    rw [he]
    simp [MulAut.conj_apply]
  let φ : Equiv.Perm (Fin 6156) → MulAut ↥j3P := fun x => if h : x ∈ j3R then e ⟨x, h⟩ else 1
  have hφ : ∀ x (h : x ∈ j3R), φ x = e ⟨x, h⟩ := fun x h => dite_eq_left h
  obtain ⟨K, E, hf⟩ := Certificates.certificate25890 φ ⟨t, hP0⟩ (Subtype.ext ht2)
    (fun h => ht1' (congrArg Subtype.val h))
    (fun x hx y hy => by
      rw [hφ _ (hSR' (mul_mem hx hy)), hφ _ (hSR' hx), hφ _ (hSR' hy), ← map_mul]
      rfl)
    (fun x hx y hy h => by
      rw [hφ _ (hSR' hx), hφ _ (hSR' hy)] at h
      exact congrArg Subtype.val (e.injective h))
    (by rw [hφ t htR]; exact hinner t htR hP0)
    (fun x hx hxP => ⟨⟨x, hxP⟩, by rw [hφ _ (hSR' hx)]; exact hinner _ _ _⟩)
    (fun x hx hxP hsq hne => by
      obtain ⟨c, hc, hac⟩ := involution_conj_t0_j3P hxP hsq hne
      have hceq : (⟨x, hxP⟩ : ↥j3P) = ⟨c, hc⟩ * ⟨t, hP0⟩ * ⟨c, hc⟩⁻¹ := Subtype.ext hac
      refine ⟨⟨c, hc⟩, ?_⟩
      rw [hφ _ (hSR' hx), hinner _ _ hxP, hceq])
  exact OuterEData.of_card ⟨392445, by decide, by rw [hcardAut]⟩ hf

end CFSG.EvenSporadicStandard.Fin76b.J3
