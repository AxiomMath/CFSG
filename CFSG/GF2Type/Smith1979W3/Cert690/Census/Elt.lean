module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Facts
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFE
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB7a

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

theorem grpFacts_of_groupOK {minus : Bool} {D : GrpData} (h : groupOK minus D = true) :
    GrpFacts minus D := by
  unfold groupOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hO, hOm⟩, hsizeO⟩, hsizeOm⟩, hidx⟩, hinv⟩ := h
  have hen : EnumCert (oGensC minus) D.O.toList := enumOK_sound hO
  have henm : EnumCert (omegaGensC minus) D.Om.toList := enumOK_sound hOm
  refine
    { enumO := hen
      enumOm := henm
      codeO := ?_
      codeOm := ?_
      zero := ?_
      idx := ?_
      invI_lt := ?_
      mul_invI := ?_ }
  · refine eq_of_le_of_natCard
      (codeSubgroup_map_wordC_le_O₀ (minus := minus) (oWords minus) (oWords_letters minus)) ?_
    rw [hen.natCard, Array.length_toList, hsizeO, natCard_O₀]
  · refine eq_of_le_of_natCard
      (codeSubgroup_map_wordC_le_omega (minus := minus) (omegaWords minus)
        (omegaWords_letters minus) (omegaWords_even minus)) ?_
    rw [henm.natCard, Array.length_toList, hsizeOm, natCard_Ω₀]
  · unfold enumOK at hO
    simp only [Bool.and_eq_true, beq_iff_eq] at hO
    exact hO.1.1.1.1.1.2
  · unfold idxOK at hidx
    simp only [List.all_eq_true, beq_iff_eq] at hidx
    intro i hi
    exact hidx i (List.mem_range.mpr hi)
  · unfold invArrOK at hinv
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, List.all_eq_true] at hinv
    obtain ⟨⟨hsize, hall⟩, _⟩ := hinv
    intro i hi
    have hi' : i < D.invI.size := by rw [hsize]; exact hi
    have hlt := hall i hi'
    rw [← array_getElem!_eq_getElem hi'] at hlt
    exact of_decide_eq_true hlt
  · unfold invArrOK at hinv
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, List.all_eq_true] at hinv
    obtain ⟨_, hmul⟩ := hinv
    intro i hi
    exact hmul i (List.mem_range.mpr hi)

namespace GrpFacts

variable {minus : Bool} {D : GrpData}

private theorem memO (hD : GrpFacts minus D) {i : ℕ} (hi : i < D.O.size) :
    D.O[i]! ∈ D.O.toList := by
  rw [array_getElem!_eq_getElem hi]
  exact array_getElem_mem_toList hi

theorem size_O (hD : GrpFacts minus D) : D.O.size = if minus then 51840 else 40320 := by
  have h := hD.enumO.natCard
  rw [hD.codeO, natCard_O₀, Array.length_toList] at h
  exact h.symm

theorem size_Om (hD : GrpFacts minus D) : D.Om.size = if minus then 25920 else 20160 := by
  have h := hD.enumOm.natCard
  rw [hD.codeOm, natCard_Ω₀, Array.length_toList] at h
  exact h.symm

theorem natCard_O₀_eq_size (hD : GrpFacts minus D) : Nat.card (O₀ minus) = D.O.size := by
  rw [natCard_O₀, hD.size_O]

theorem code_lt (hD : GrpFacts minus D) {i : ℕ} (hi : i < D.O.size) : D.O[i]! < 2 ^ 36 :=
  hD.enumO.lt _ (hD.memO hi)

theorem hasCode_elt (hD : GrpFacts minus D) {i : ℕ} (hi : i < D.O.size) :
    Code.HasCode (hD.elt i : V₀ →ₗ[ZMod 2] V₀) D.O[i]! :=
  hD.enumO.hasCode_elem (hD.memO hi)

theorem elt_mem_O₀ (hD : GrpFacts minus D) {i : ℕ} (hi : i < D.O.size) :
    hD.elt i ∈ O₀ minus :=
  hD.codeO ▸ hD.enumO.elem_mem (hD.memO hi)

theorem eq_elt_of_hasCode (hD : GrpFacts minus D) {i : ℕ} (hi : i < D.O.size)
    {x : V₀ ≃ₗ[ZMod 2] V₀} (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) D.O[i]!) :
    x = hD.elt i :=
  Code.HasCode.eq_of_equiv hx (hD.hasCode_elt hi)

theorem exists_elt_eq (hD : GrpFacts minus D) {x : V₀ ≃ₗ[ZMod 2] V₀} (hx : x ∈ O₀ minus) :
    ∃ i < D.O.size, hD.elt i = x := by
  have hx' : x ∈ codeSubgroup (oGensC minus) := hD.codeO ▸ hx
  obtain ⟨c, hcE, hcode⟩ := hD.enumO.exists_code_mem hx'
  have hcodex := hD.enumO.hasCode_code hx'
  have hceq : c = hD.enumO.code x :=
    Code.HasCode.code_eq hcode hcodex (hD.enumO.lt c hcE)
      (hD.enumO.lt _ (hD.enumO.code_mem hx'))
  obtain ⟨i, hi, hci⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hcE)
  refine ⟨i, hi, ?_⟩
  show hD.enumO.elem D.O[i]! = x
  have hOi : D.O[i]! = c := by
    rw [array_getElem!_eq_getElem hi]
    exact hci
  rw [hOi, hceq]
  exact hD.enumO.elem_code hx'

theorem elt_injOn (hD : GrpFacts minus D) {i j : ℕ} (hi : i < D.O.size) (hj : j < D.O.size)
    (h : hD.elt i = hD.elt j) : i = j := by
  have hcode := hD.enumO.elem_inj (hD.memO hi) (hD.memO hj) h
  rw [← hD.idx i hi, ← hD.idx j hj, hcode]

theorem elt_zero (hD : GrpFacts minus D) : hD.elt 0 = 1 := by
  show hD.enumO.elem D.O[0]! = 1
  rw [hD.zero]
  exact hD.enumO.elem_one

theorem elt_invI (hD : GrpFacts minus D) {i : ℕ} (hi : i < D.O.size) :
    hD.elt D.invI[i]! = (hD.elt i)⁻¹ :=
  hD.enumO.elem_inv (hD.memO hi) (hD.memO (hD.invI_lt i hi)) (hD.mul_invI i hi)

theorem idx_spec (hD : GrpFacts minus D) {x : V₀ ≃ₗ[ZMod 2] V₀} (hx : x ∈ O₀ minus) {p : ℕ}
    (hp : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) p) (hplt : p < 2 ^ 36) :
    D.idx.getD p D.O.size < D.O.size ∧ D.O[D.idx.getD p D.O.size]! = p ∧
      hD.elt (D.idx.getD p D.O.size) = x := by
  obtain ⟨i, hi, hix⟩ := hD.exists_elt_eq hx
  have hcodei : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) D.O[i]! := by
    rw [← hix]
    exact hD.hasCode_elt hi
  have hpeq : p = D.O[i]! := Code.HasCode.code_eq hp hcodei hplt (hD.code_lt hi)
  have hidx : D.idx.getD p D.O.size = i := by
    rw [hpeq]
    exact hD.idx i hi
  exact ⟨by rw [hidx]; exact hi, by rw [hidx]; exact hpeq.symm, by rw [hidx]; exact hix⟩

theorem hasCode_mul (hD : GrpFacts minus D) {i j : ℕ} (hi : i < D.O.size) (hj : j < D.O.size) :
    Code.HasCode ((hD.elt i * hD.elt j : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
      (Code.mul D.O[i]! D.O[j]!) :=
  Code.HasCode.mul (hD.hasCode_elt hi) (hD.hasCode_elt hj)

theorem hasCode_conj (hD : GrpFacts minus D) {a x : ℕ} (ha : a < D.O.size) (hx : x < D.O.size) :
    Code.HasCode ((hD.elt a * hD.elt x * (hD.elt a)⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) :
        V₀ →ₗ[ZMod 2] V₀)
      (Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!) :=
  Code.HasCode.mul (hD.hasCode_mul ha hx)
    (hD.elt_invI ha ▸ hD.hasCode_elt (hD.invI_lt a ha))

theorem elt_vec (hD : GrpFacts minus D) {i : ℕ} (hi : i < D.O.size) (n : ℕ) :
    hD.elt i (Code.vec n) = Code.vec (Code.act D.O[i]! n) :=
  apply_vec_of_hasCode (hD.hasCode_elt hi) n

theorem elt_vec_eq_iff (hD : GrpFacts minus D) {i : ℕ} (hi : i < D.O.size) {n : ℕ}
    (hn : n < 64) : hD.elt i (Code.vec n) = Code.vec n ↔ Code.act D.O[i]! n = n := by
  rw [hD.elt_vec hi n]
  constructor
  · intro h
    exact vec_injective_of_lt (Code.act_lt _ _) hn h
  · intro h
    rw [h]

theorem mul_comm_iff (hD : GrpFacts minus D) {i j : ℕ} (hi : i < D.O.size) (hj : j < D.O.size) :
    Code.mul D.O[i]! D.O[j]! = Code.mul D.O[j]! D.O[i]! ↔
      hD.elt i * hD.elt j = hD.elt j * hD.elt i := by
  have h1 := hD.hasCode_mul hi hj
  have h2 := hD.hasCode_mul hj hi
  constructor
  · intro hc
    rw [hc] at h1
    exact Code.HasCode.eq_of_equiv h1 h2
  · intro h
    rw [← h] at h2
    exact Code.HasCode.code_eq h1 h2 (Code.mul_lt _ _) (Code.mul_lt _ _)

theorem codePow_eq_one_iff (hD : GrpFacts minus D) {i : ℕ} (hi : i < D.O.size) (n : ℕ) :
    codePow D.O[i]! n = Code.one ↔ hD.elt i ^ n = 1 := by
  have hmem := hD.memO hi
  have hxmem : hD.elt i ∈ codeSubgroup (oGensC minus) := hD.enumO.elem_mem hmem
  have hpow : hD.enumO.code (hD.elt i ^ n) = codePow D.O[i]! n := by
    have h := hD.enumO.code_pow hxmem n
    rw [show hD.enumO.code (hD.elt i) = D.O[i]! from hD.enumO.code_elem hmem] at h
    exact h
  constructor
  · intro h
    refine hD.enumO.eq_of_code_eq (Subgroup.pow_mem _ hxmem n) (Subgroup.one_mem _) ?_
    rw [hpow, h, hD.enumO.code_one]
  · intro h
    rw [h, hD.enumO.code_one] at hpow
    exact hpow.symm

theorem inIdx_iff (hD : GrpFacts minus D) {A : Array ℕ} {x : V₀ ≃ₗ[ZMod 2] V₀} :
    InIdx D A x ↔ ∃ i ∈ A, i < D.O.size ∧ hD.elt i = x := by
  constructor
  · rintro ⟨i, hiA, hi, hcode⟩
    exact ⟨i, hiA, hi, (hD.eq_elt_of_hasCode hi hcode).symm⟩
  · rintro ⟨i, hiA, hi, hix⟩
    exact ⟨i, hiA, hi, hix ▸ hD.hasCode_elt hi⟩

end GrpFacts

end CFSG.GF2Type.Smith1979W3.Cert690

end
