module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModMap
public import Certificates.Certificate25141
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QT2LocProofBase

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open Subgroup CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem eta_mul (hM : MatFacts) {c d e : ℕ} (h : c ^^^ d = e) :
    eta uJ 11 c * eta uJ 11 d = eta uJ 11 e := by
  rw [← h, eta_xor (elem_uJ hM) le_rfl]

theorem eta_mem_hOrbit_of_word (hF : J4Facts) {W : List ℤ}
    (hW : ∀ ℓ ∈ W, ℓ ∈ letters) {c c' : ℕ} (h : W.foldr act c = c') :
    eta uJ 11 c' ∈ hOrbit (⊤ : Subgroup J) (Eg uJ 11) (eta uJ 11 c) :=
  (mem_hOrbit_top hF).2 (exists_Hconj_of_word hF.mat hW h)

theorem chkTriple_spec :
    (∀ c ∈ tMasks, c < 2048) ∧ 23 ∉ tMasks := by
  have h := Certificates.certificate25141
  unfold chkTriple at h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
  refine ⟨fun c hc => ?_, fun hc => ?_⟩
  · simpa using List.all_eq_true.1 h1 c hc
  · have h3 : tMasks.contains 23 = true := List.contains_iff_mem.2 hc
    rw [h3] at h2
    exact absurd h2 (by decide)

theorem not_mem_hOrbit_eta_one :
    eta uJ 11 23 ∉ hOrbit (⊤ : Subgroup J) (Eg uJ 11) (eta uJ 11 1) := by
  have hF := j4Facts
  have hM := hF.mat
  intro h
  obtain ⟨k, hk, hkx⟩ := (mem_hOrbit_top hF).1 h
  have h1 : eta uJ 11 1 ∈ tSet := ⟨1, one_mem_tMasks, rfl⟩
  have h2 : k * eta uJ 11 1 * k⁻¹ ∈ tSet := (tSet_conj hM k hk).1 _ h1
  rw [hkx] at h2
  obtain ⟨c, hc, hce⟩ := h2
  have h3 : 23 = c := eta_inj hM 23 (by norm_num) c (chkTriple_spec.1 c hc) hce
  exact chkTriple_spec.2 (by rw [h3]; exact hc)

theorem tripleData_J :
    TripleData (⊤ : Subgroup J) (Eg uJ 11) := by
  have hF := j4Facts
  have hM := hF.mat
  have hetaE : ∀ c : ℕ, eta uJ 11 c ∈ Eg uJ 11 := fun c => eta_mem_Eg 11 le_rfl c
  have hne : ∀ c : ℕ, c ≠ 0 → c < 2 ^ 11 → eta uJ 11 c ≠ 1 := fun c hc0 hc => eta_ne_one hM hc0 hc
  have e12 : eta uJ 11 1 * eta uJ 11 22 = eta uJ 11 23 := eta_mul hM (by decide)
  have e13 : eta uJ 11 1 * eta uJ 11 1745 = eta uJ 11 1744 := eta_mul hM (by decide)
  have e23 : eta uJ 11 22 * eta uJ 11 1745 = eta uJ 11 1735 := eta_mul hM (by decide)
  have e123 : eta uJ 11 23 * eta uJ 11 1745 = eta uJ 11 1734 := eta_mul hM (by decide)
  refine ⟨eta uJ 11 1, hetaE 1, eta uJ 11 22, hetaE 22, eta uJ 11 1745, hetaE 1745,
    hne 1 (by norm_num) (by norm_num), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e12]
    exact hne 23 (by norm_num) (by norm_num)
  · exact eta_mem_hOrbit_of_word hF (W := [3, 3]) (by decide) (by decide)
  · exact eta_mem_hOrbit_of_word hF (W := [-3]) (by decide) (by decide)
  · rw [e23]
    exact eta_mem_hOrbit_of_word hF (W := [-2, -3, -2, 1]) (by decide) (by decide)
  · rw [e12]
    exact not_mem_hOrbit_eta_one
  · rw [e12, e13]
    exact eta_mem_hOrbit_of_word hF (W := [-1, -1]) (by decide) (by decide)
  · rw [e12, e123]
    exact eta_mem_hOrbit_of_word hF (W := [-3, -2, 3]) (by decide) (by decide)

end CFSG.EvenSporadicStandard.J4Std.DataMod

namespace CFSG.EvenSporadicStandard.J4Std

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem tripleData_J4
    {G : Type} [Group G]
    (ι : J →* G) (hι : Function.Injective ι) : TripleData ι.range ((Eg uJ 11).map ι) :=
  DataMod.tripleData_map ι hι _ DataMod.tripleData_J

end CFSG.EvenSporadicStandard.J4Std
