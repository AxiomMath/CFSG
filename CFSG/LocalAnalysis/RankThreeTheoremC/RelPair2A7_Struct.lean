module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Lift
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

theorem rFour_conj_vOneF : ∀ m : Fin 4, ∃ n : Fin 4, rFour * vOneF m * rFour⁻¹ = vTwoF n := by
  decide +kernel

theorem rFour_conj_eNineF : ∀ i j : Fin 3, ∃ m n : Fin 3,
    rFour * eNineF i j * rFour⁻¹ = eNineF m n := by
  decide +kernel

theorem eNineF_conj_vOneF : ∀ (i j : Fin 3) (m : Fin 4), ∃ n : Fin 4,
    eNineF i j * vOneF m * (eNineF i j)⁻¹ = vOneF n := by
  decide +kernel

theorem eNineF_conj_vTwoF : ∀ (i j : Fin 3) (m : Fin 4), ∃ n : Fin 4,
    eNineF i j * vTwoF m * (eNineF i j)⁻¹ = vTwoF n := by
  decide +kernel

theorem eNine_le_normalizer_vOne : eNine ≤ normalizer (vOne : Set (Perm (Fin 7))) := by
  rintro _ ⟨i, j, rfl⟩
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨m, rfl⟩ := hy
  obtain ⟨n, hn⟩ := eNineF_conj_vOneF i j m
  exact ⟨n, hn⟩

theorem eNine_le_normalizer_vTwo : eNine ≤ normalizer (vTwo : Set (Perm (Fin 7))) := by
  rintro _ ⟨i, j, rfl⟩
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨m, rfl⟩ := hy
  obtain ⟨n, hn⟩ := eNineF_conj_vTwoF i j m
  exact ⟨n, hn⟩

theorem rFour_mem_normalizer_eNine : rFour ∈ normalizer (eNine : Set (Perm (Fin 7))) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨i, j, rfl⟩ := hy
  obtain ⟨m, n, h⟩ := rFour_conj_eNineF i j
  exact ⟨m, n, h⟩

theorem vOne_le_alternatingGroup : vOne ≤ alternatingGroup (Fin 7) :=
  vOne_le_centOne.trans inf_le_right

theorem vTwo_le_alternatingGroup : vTwo ≤ alternatingGroup (Fin 7) :=
  vTwo_le_centTwo.trans inf_le_right

theorem map_conj_rFour_vOne : vOne.map (MulAut.conj rFour).toMonoidHom = vTwo := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, ⟨m, rfl⟩, rfl⟩
    obtain ⟨n, hn⟩ := rFour_conj_vOneF m
    exact ⟨n, by simpa [MulAut.conj_apply] using hn⟩
  · rw [card_vTwo, Subgroup.card_map_of_injective (MulAut.conj rFour).injective, card_vOne]

theorem three_dvd_card_vOne_sup_vTwo : 3 ∣ Nat.card (vOne ⊔ vTwo : Subgroup (Perm (Fin 7))) := by
  obtain ⟨h6, h2⟩ := check_vOne_vTwo 1 1 (by decide) (by decide)
  have hmem : vOneF 1 * vTwoF 1 ∈ (vOne ⊔ vTwo : Subgroup (Perm (Fin 7))) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨1, rfl⟩) (Subgroup.mem_sup_right ⟨1, rfl⟩)
  have h3 : 3 ∣ orderOf (vOneF 1 * vTwoF 1) :=
    three_dvd_orderOf_of_pow (m := 2) (by simpa using h6) h2
  exact h3.trans (Subgroup.orderOf_dvd_natCard _ hmem)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem a7_structure_aux {ι : X →* Perm (Fin 7)} (hι : Function.Injective ι)
    (hA7 : alternatingGroup (Fin 7) ≤ ι.range) {D V : Subgroup X} (hDe : D.map ι = eNine)
    (hV : rankTwoMaximalInvariantTwoSubgroup D V) {A B : Subgroup (Perm (Fin 7))}
    (hAA : A ≤ alternatingGroup (Fin 7)) (hA4 : Nat.card A = 4)
    (hAn : eNine ≤ normalizer (A : Set (Perm (Fin 7)))) (hVA : V.map ι ≤ A) {r : Perm (Fin 7)}
    (hrA : r ∈ alternatingGroup (Fin 7)) (hrN : r ∈ normalizer (eNine : Set (Perm (Fin 7))))
    (hAB : A.map (MulAut.conj r).toMonoidHom = B)
    (h3 : 3 ∣ Nat.card (A ⊔ B : Subgroup (Perm (Fin 7)))) :
    Nat.card V = 4 ∧ ∃ n ∈ normalizer (D : Set X),
      3 ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup X) := by
  classical
  have hAr : A ≤ ι.range := hAA.trans hA7
  have hAU : (A.comap ι).map ι = A := Subgroup.map_comap_eq_self hAr
  have hUcard : Nat.card (A.comap ι) = 4 := by
    rw [← hA4, ← hAU, Subgroup.card_map_of_injective hι, hAU]
  have hU2 : IsPGroup 2 (A.comap ι) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
  have hDU : D ≤ normalizer ((A.comap ι : Subgroup X) : Set X) := by
    intro d hd
    rw [mem_normalizer_iff]
    intro y
    have hdn : ι d ∈ normalizer (A : Set (Perm (Fin 7))) :=
      hAn (hDe ▸ Subgroup.mem_map_of_mem ι hd)
    have := mem_normalizer_iff.mp hdn (ι y)
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this
  have hVU : V ≤ A.comap ι := fun x hx => hVA (Subgroup.mem_map_of_mem ι hx)
  have hUV : A.comap ι = V := hV.2.2 _ hU2 hDU hVU
  have hVcard : Nat.card V = 4 := hUV ▸ hUcard
  refine ⟨hVcard, ?_⟩
  have hVA' : V.map ι = A := by rw [← hUV]; exact hAU
  obtain ⟨n, hn⟩ : ∃ n : X, ι n = r := hA7 hrA
  refine ⟨n, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    have hyD : y ∈ D ↔ ι y ∈ eNine := by
      rw [← hDe]
      exact (Subgroup.mem_map_iff_mem hι).symm
    have hndy : n * y * n⁻¹ ∈ D ↔ ι (n * y * n⁻¹) ∈ eNine := by
      rw [← hDe]
      exact (Subgroup.mem_map_iff_mem hι).symm
    rw [hyD, hndy, map_mul, map_mul, map_inv, hn]
    exact mem_normalizer_iff.mp hrN (ι y)
  · have hVn : (V.map (MulAut.conj n).toMonoidHom).map ι = B := by
      rw [Subgroup.map_map]
      have : ι.comp (MulAut.conj n).toMonoidHom = (MulAut.conj (ι n)).toMonoidHom.comp ι := by
        ext x
        simp [MulAut.conj_apply]
      rw [this, ← Subgroup.map_map, hVA', hn]
      exact hAB
    have hmap : (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup X).map ι = A ⊔ B := by
      rw [Subgroup.map_sup, hVA', hVn]
    have hcard := Subgroup.card_map_of_injective hι
      (K := (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup X))
    rw [hmap] at hcard
    rwa [← hcard]

omit [Finite X] in
theorem a7_structure_of_embedding {ι : X →* Perm (Fin 7)} (hι : Function.Injective ι)
    (hA7 : alternatingGroup (Fin 7) ≤ ι.range) {D V : Subgroup X} (hD : Nat.card D = 9)
    (hV : rankTwoMaximalInvariantTwoSubgroup D V) :
    Nat.card V = 4 ∧ ∃ n ∈ normalizer (D : Set X),
      3 ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup X) := by
  classical
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS7 : (Nat.card (Perm (Fin 7))).factorization 3 = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide +kernel
  have hDι : Nat.card (D.map ι) = 9 := by rw [Subgroup.card_map_of_injective hι, hD]
  have hsylD : CFSG.ABGLocalTools.IsSylowOf 3 (D.map ι) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by rw [hDι, Subgroup.card_top, hS7]; norm_num)
  have hsylE : CFSG.ABGLocalTools.IsSylowOf 3 eNine ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top
      (by rw [card_eNine, Subgroup.card_top, hS7]; norm_num)
  obtain ⟨k, -, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hsylD hsylE
  set ι' : X →* Perm (Fin 7) := (MulAut.conj k).toMonoidHom.comp ι with hι'
  have hι'inj : Function.Injective ι' := (MulAut.conj k).injective.comp hι
  have hA7' : alternatingGroup (Fin 7) ≤ ι'.range := by
    intro a ha
    have hna : k⁻¹ * a * k ∈ alternatingGroup (Fin 7) := by
      change Perm.sign _ = 1
      have : Perm.sign a = 1 := ha
      simp [this]
    obtain ⟨x, hx⟩ := hA7 hna
    refine ⟨x, ?_⟩
    simp only [hι', MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulAut.conj_apply, hx]
    group
  have hDe : D.map ι' = eNine := by
    ext x
    rw [hι', ← Subgroup.map_map, mem_map_conj_iff_implicit]
    exact (hk x).symm
  have hW2 : IsPGroup 2 (V.map ι') := hV.1.map ι'
  have hEN : eNine ≤ normalizer ((V.map ι' : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
    rw [← hDe]
    exact (Subgroup.map_mono hV.2.1).trans (Subgroup.le_normalizer_map ι')
  have hW3 : ¬ 3 ∣ Nat.card (V.map ι') := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := hW2.exists_card_eq
    rw [hj]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hrA : rFour ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.mpr rFour_spec.1
  have hB : vTwo.map (MulAut.conj rFour⁻¹).toMonoidHom = vOne := by
    rw [← map_conj_rFour_vOne, Subgroup.map_map]
    have : (MulAut.conj rFour⁻¹).toMonoidHom.comp (MulAut.conj rFour).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply]
    rw [this, Subgroup.map_id]
  rcases le_vOne_or_le_vTwo hW3 (hEN cOne_mem_eNine) (hEN cTwo_mem_eNine) with h | h
  · exact a7_structure_aux hι'inj hA7' hDe hV vOne_le_alternatingGroup card_vOne
      eNine_le_normalizer_vOne h hrA rFour_mem_normalizer_eNine map_conj_rFour_vOne
      three_dvd_card_vOne_sup_vTwo
  · exact a7_structure_aux hι'inj hA7' hDe hV vTwo_le_alternatingGroup card_vTwo
      eNine_le_normalizer_vTwo h (inv_mem hrA) (inv_mem rFour_mem_normalizer_eNine) hB
      (by rw [sup_comm]; exact three_dvd_card_vOne_sup_vTwo)

end CFSG.LocalAnalysis.RankThreeTheoremC
