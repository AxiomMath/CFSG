module

public import CFSG.ClassicalInvolution.Phan.Phan3B3SpRel
public import CFSG.ClassicalInvolution.Phan.Phan3KerA3
public import CFSG.ClassicalInvolution.Phan.PhanB2Family
public import CFSG.ClassicalInvolution.Phan.Phan3B3Check

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg
open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.ClassicalInvolution.PhanB3 (PhanFamilyB3)

@[expose] noncomputable def x3sw : Fin 4 → Su K9 3 1 3 :=
  ![embSUid (unitaryInvolution K9 3 1) 0 A2, embSUid (unitaryInvolution K9 3 1) 0 B2,
    embSUid (unitaryInvolution K9 3 1) 2 A2, embSUid (unitaryInvolution K9 3 1) 2 B2]

@[expose] def mat3sw : Fin 4 → Matrix (Fin 3) (Fin 3) F9 :=
  ![embPair 0 mA, embPair 0 mB, embPair 2 mA, embPair 2 mB]

theorem hg3sw (i : Fin 4) :
    (((x3sw i : Su K9 3 1 3) : GL (Fin 3) K9) : Matrix (Fin 3) (Fin 3) K9) =
      (mat3sw i).map phi9r := by
  fin_cases i
  · exact embPair_map phi9r 0 mA
  · exact embPair_map phi9r 0 mB
  · exact embPair_map phi9r 2 mA
  · exact embPair_map phi9r 2 mB

theorem hU3sw : ∀ i, ct9 (mat3sw i) * mat3sw i = 1 := by decide +kernel

theorem wordVal_x3sw_su3Rels : ∀ r ∈ su3Rels, wordVal x3sw r = 1 := by
  have h : ∀ r ∈ su3Rels, wordMat mat3sw r = 1 := by decide +kernel
  exact fun r hr => wordVal_eq_one x3sw mat3sw hg3sw hU3sw (h r hr)

@[expose] def suIdx : Fin 4 → Fin 8 := Fin.castLE (by decide)

@[expose] def spIdx : Fin 4 → Fin 8 := ![2, 3, 4, 5]

theorem decodeWord_eight_su3 : ∀ c ∈ su3Codes,
    decodeWord 8 c = (decodeWord 4 c).map fun l => (suIdx l.1, l.2) := by
  decide +kernel

theorem decodeWord_eight_sp : ∀ c ∈ b3SpCodes,
    decodeWord 8 c = (decodeWord 4 (c.map (· - 4))).map fun l => (spIdx l.1, l.2) := by
  decide +kernel

variable {G : Type} [Group G] (E : PhanFamilyB3 b2Coord3 G)

@[expose] noncomputable def b3W : G := (E.ι 2 B2)⁻¹ * (E.ι 2 A2)⁻¹ * E.ι 2 B2

@[expose] noncomputable def b3Gens : Fin 8 → G :=
  ![E.ι 0 A2, E.ι 0 B2, E.ι 1 A2, E.ι 1 B2, E.ι 2 A2, E.ι 2 B2, b3W E * E.ι 1 A2 * (b3W E)⁻¹,
    b3W E * E.ι 1 B2 * (b3W E)⁻¹]

theorem b3Gens_0 : b3Gens E 0 = E.ι 0 A2 := rfl
theorem b3Gens_1 : b3Gens E 1 = E.ι 0 B2 := rfl
theorem b3Gens_2 : b3Gens E 2 = E.ι 1 A2 := rfl
theorem b3Gens_3 : b3Gens E 3 = E.ι 1 B2 := rfl
theorem b3Gens_4 : b3Gens E 4 = E.ι 2 A2 := rfl
theorem b3Gens_5 : b3Gens E 5 = E.ι 2 B2 := rfl
theorem b3Gens_6 : b3Gens E 6 = b3W E * E.ι 1 A2 * (b3W E)⁻¹ := rfl
theorem b3Gens_7 : b3Gens E 7 = b3W E * E.ι 1 B2 * (b3W E)⁻¹ := rfl

theorem b3Gens_suIdx (i : Fin 4) : b3Gens E (suIdx i) = E.θ (x3 i) := by
  fin_cases i
  · exact (DFunLike.congr_fun E.left A2).symm
  · exact (DFunLike.congr_fun E.left B2).symm
  · exact (DFunLike.congr_fun E.right A2).symm
  · exact (DFunLike.congr_fun E.right B2).symm

theorem b3Gens_spIdx (i : Fin 4) : b3Gens E (spIdx i) = E.ϑ (spGens i) := by
  fin_cases i
  · exact (DFunLike.congr_fun E.ℓ_eq A2).symm
  · exact (DFunLike.congr_fun E.ℓ_eq B2).symm
  · exact (DFunLike.congr_fun E.s_eq A2).symm
  · exact (DFunLike.congr_fun E.s_eq B2).symm

theorem wordVal_b3_su3 : ∀ r ∈ su3Codes.map (decodeWord 8), wordVal (b3Gens E) r = 1 := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  rw [decodeWord_eight_su3 c hc, wordVal_reindex]
  have h : (fun i : Fin 4 => b3Gens E (suIdx i)) = fun i => E.θ (x3 i) :=
    funext (b3Gens_suIdx E)
  rw [h, wordVal_map E.θ x3, wordVal_x3_su3Rels _ (List.mem_map.2 ⟨c, hc, rfl⟩), map_one]

theorem wordVal_b3_sp : ∀ r ∈ b3SpCodes.map (decodeWord 8), wordVal (b3Gens E) r = 1 := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  rw [decodeWord_eight_sp c hc, wordVal_reindex]
  have h : (fun i : Fin 4 => b3Gens E (spIdx i)) = fun i => E.ϑ (spGens i) :=
    funext (b3Gens_spIdx E)
  rw [h, wordVal_map E.ϑ spGens, wordVal_spGens_b3Sp4Rels _ (List.mem_map.2 ⟨c, hc, rfl⟩), map_one]

theorem wordVal_b3_comm : ∀ r ∈ b3CommCodes.map (decodeWord 8), wordVal (b3Gens E) r = 1 := by
  intro r hr
  simp only [b3CommCodes, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (wordVal_comm_iff (b3Gens E) [(0, true)] [(4, true)]).2
      (by simpa [wordVal, letterVal, b3Gens_0, b3Gens_4] using E.comm A2 A2)
  · exact (wordVal_comm_iff (b3Gens E) [(0, true)] [(5, true)]).2
      (by simpa [wordVal, letterVal, b3Gens_0, b3Gens_5] using E.comm A2 B2)
  · exact (wordVal_comm_iff (b3Gens E) [(1, true)] [(4, true)]).2
      (by simpa [wordVal, letterVal, b3Gens_1, b3Gens_4] using E.comm B2 A2)
  · exact (wordVal_comm_iff (b3Gens E) [(1, true)] [(5, true)]).2
      (by simpa [wordVal, letterVal, b3Gens_1, b3Gens_5] using E.comm B2 B2)

theorem wordVal_b3_def : ∀ r ∈ b3DefCodes.map (decodeWord 8), wordVal (b3Gens E) r = 1 := by
  intro r hr
  simp only [b3DefCodes, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show wordVal (b3Gens E) [(6, false), (5, false), (4, false), (5, true), (2, true), (5, false),
      (4, true), (5, true)] = 1
    simp only [wordVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal,
      Bool.cond_true, Bool.cond_false, mul_one, b3Gens_6, b3Gens_5, b3Gens_4, b3Gens_2, b3W]
    group
  · show wordVal (b3Gens E) [(7, false), (5, false), (4, false), (5, true), (3, true), (5, false),
      (4, true), (5, true)] = 1
    simp only [wordVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal,
      Bool.cond_true, Bool.cond_false, mul_one, b3Gens_7, b3Gens_5, b3Gens_4, b3Gens_3, b3W]
    group

theorem ϑ_wSp : E.ϑ (wordVal spGens wSp) = b3W E := by
  have h4 : E.ϑ (spGens 3) = E.ι 2 B2 := DFunLike.congr_fun E.s_eq B2
  have h3 : E.ϑ (spGens 2) = E.ι 2 A2 := DFunLike.congr_fun E.s_eq A2
  simp only [wSp, wordVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal,
    Bool.cond_true, Bool.cond_false, mul_one, map_mul, map_inv, h4, h3, b3W, mul_assoc]

theorem ϑ_conjSp (j : Fin 4) :
    E.ϑ (wordVal spGens (conjSp [(j, true)])) = b3W E * E.ϑ (spGens j) * (b3W E)⁻¹ := by
  simp only [conjSp, wordVal_append, wordVal_invWord, map_mul, map_inv, ϑ_wSp]
  simp [wordVal, letterVal]

theorem b3_x1p : E.ϑ (wordVal spGens (conjSp [(0, true)])) = b3Gens E 6 := by
  rw [ϑ_conjSp, b3Gens_6]
  exact congrArg (fun x => b3W E * x * (b3W E)⁻¹) (DFunLike.congr_fun E.ℓ_eq A2)

theorem b3_y1p : E.ϑ (wordVal spGens (conjSp [(1, true)])) = b3Gens E 7 := by
  rw [ϑ_conjSp, b3Gens_7]
  exact congrArg (fun x => b3W E * x * (b3W E)⁻¹) (DFunLike.congr_fun E.ℓ_eq B2)

theorem b3_comm_2_6 : b3Gens E 2 * b3Gens E 6 = b3Gens E 6 * b3Gens E 2 := by
  have h := congrArg E.ϑ (spGens_comm11 (0, 0) (by simp))
  rw [map_mul, map_mul, b3_x1p] at h
  have e : E.ϑ (spGens 0) = b3Gens E 2 := (b3Gens_spIdx E 0).symm
  simpa [e] using h

theorem b3_comm_2_7 : b3Gens E 2 * b3Gens E 7 = b3Gens E 7 * b3Gens E 2 := by
  have h := congrArg E.ϑ (spGens_comm11 (0, 1) (by simp))
  rw [map_mul, map_mul, b3_y1p] at h
  have e : E.ϑ (spGens 0) = b3Gens E 2 := (b3Gens_spIdx E 0).symm
  simpa [e] using h

theorem b3_comm_3_6 : b3Gens E 3 * b3Gens E 6 = b3Gens E 6 * b3Gens E 3 := by
  have h := congrArg E.ϑ (spGens_comm11 (1, 0) (by simp))
  rw [map_mul, map_mul, b3_x1p] at h
  have e : E.ϑ (spGens 1) = b3Gens E 3 := (b3Gens_spIdx E 1).symm
  simpa [e] using h

theorem b3_comm_3_7 : b3Gens E 3 * b3Gens E 7 = b3Gens E 7 * b3Gens E 3 := by
  have h := congrArg E.ϑ (spGens_comm11 (1, 1) (by simp))
  rw [map_mul, map_mul, b3_y1p] at h
  have e : E.ϑ (spGens 1) = b3Gens E 3 := (b3Gens_spIdx E 1).symm
  simpa [e] using h

theorem wordVal_b3_comm11 : ∀ r ∈ b3Comm11Codes.map (decodeWord 8),
    wordVal (b3Gens E) r = 1 := by
  intro r hr
  simp only [b3Comm11Codes, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (wordVal_comm_iff (b3Gens E) [(2, true)] [(6, true)]).2
      (by simpa [wordVal, letterVal] using b3_comm_2_6 E)
  · exact (wordVal_comm_iff (b3Gens E) [(2, true)] [(7, true)]).2
      (by simpa [wordVal, letterVal] using b3_comm_2_7 E)
  · exact (wordVal_comm_iff (b3Gens E) [(3, true)] [(6, true)]).2
      (by simpa [wordVal, letterVal] using b3_comm_3_6 E)
  · exact (wordVal_comm_iff (b3Gens E) [(3, true)] [(7, true)]).2
      (by simpa [wordVal, letterVal] using b3_comm_3_7 E)

theorem wordVal_b3RankTwoRels : ∀ w ∈ b3RankTwoRels, wordVal (b3Gens E) w = 1 := by
  intro w hw
  simp only [b3RankTwoRels, List.map_append, List.mem_append] at hw
  rcases hw with (((hw | hw) | hw) | hw) | hw
  · exact wordVal_b3_su3 E w hw
  · exact wordVal_b3_sp E w hw
  · exact wordVal_b3_comm E w hw
  · exact wordVal_b3_def E w hw
  · exact wordVal_b3_comm11 E w hw

@[expose] noncomputable def b3Gens6 : Fin 6 → G := fun i => b3Gens E (b3KerMap i)

theorem ι0_comm_b3W (a : Su K9 3 1 2) : E.ι 0 a * b3W E = b3W E * E.ι 0 a := by
  have h1 : Commute (E.ι 0 a) (E.ι 2 A2) := E.comm a A2
  have h2 : Commute (E.ι 0 a) (E.ι 2 B2) := E.comm a B2
  exact (h2.inv_right.mul_right h1.inv_right).mul_right h2

theorem wordVal_b3_A3 : ∀ w ∈ phanA3Rels, wordVal (b3Gens6 E) w = 1 := by
  intro w hw
  simp only [phanA3Rels, List.mem_append, List.mem_map] at hw
  rcases hw with (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | hw
  ·
    rw [wordVal_map_shiftLetter]
    have h : (fun i => b3Gens6 E (shiftIdx 0 (by decide) i)) = fun i => E.θ (x3sw i) := by
      funext i
      fin_cases i
      · exact (DFunLike.congr_fun E.right A2).symm
      · exact (DFunLike.congr_fun E.right B2).symm
      · exact (DFunLike.congr_fun E.left A2).symm
      · exact (DFunLike.congr_fun E.left B2).symm
    rw [h, wordVal_map E.θ x3sw, wordVal_x3sw_su3Rels r hr, map_one]
  ·
    rw [wordVal_map_shiftLetter]
    have h : (fun i => b3Gens6 E (shiftIdx 2 (by decide) i)) =
        fun i => ((MulAut.conj (b3W E)).toMonoidHom.comp E.θ) (x3 i) := by
      funext i
      fin_cases i
      · have h1 := ι0_comm_b3W E A2
        show E.ι 0 A2 = b3W E * E.θ (embSUid (unitaryInvolution K9 3 1) 2 A2) * (b3W E)⁻¹
        rw [show E.θ (embSUid (unitaryInvolution K9 3 1) 2 A2) = E.ι 0 A2 from
          DFunLike.congr_fun E.left A2, ← h1]
        group
      · have h1 := ι0_comm_b3W E B2
        show E.ι 0 B2 = b3W E * E.θ (embSUid (unitaryInvolution K9 3 1) 2 B2) * (b3W E)⁻¹
        rw [show E.θ (embSUid (unitaryInvolution K9 3 1) 2 B2) = E.ι 0 B2 from
          DFunLike.congr_fun E.left B2, ← h1]
        group
      · show b3W E * E.ι 1 A2 * (b3W E)⁻¹ =
          b3W E * E.θ (embSUid (unitaryInvolution K9 3 1) 0 A2) * (b3W E)⁻¹
        rw [show E.θ (embSUid (unitaryInvolution K9 3 1) 0 A2) = E.ι 1 A2 from
          DFunLike.congr_fun E.right A2]
      · show b3W E * E.ι 1 B2 * (b3W E)⁻¹ =
          b3W E * E.θ (embSUid (unitaryInvolution K9 3 1) 0 B2) * (b3W E)⁻¹
        rw [show E.θ (embSUid (unitaryInvolution K9 3 1) 0 B2) = E.ι 1 B2 from
          DFunLike.congr_fun E.right B2]
    rw [h, wordVal_map ((MulAut.conj (b3W E)).toMonoidHom.comp E.θ) x3,
      wordVal_x3_su3Rels r hr, map_one]
  ·
    simp only [phanA3CommRels, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact (wordVal_comm_iff (b3Gens6 E) [(0, true)] [(4, true)]).2
        (by simpa [wordVal, letterVal, b3Gens6, b3KerMap] using b3_comm_2_6 E)
    · exact (wordVal_comm_iff (b3Gens6 E) [(0, true)] [(5, true)]).2
        (by simpa [wordVal, letterVal, b3Gens6, b3KerMap] using b3_comm_2_7 E)
    · exact (wordVal_comm_iff (b3Gens6 E) [(1, true)] [(4, true)]).2
        (by simpa [wordVal, letterVal, b3Gens6, b3KerMap] using b3_comm_3_6 E)
    · exact (wordVal_comm_iff (b3Gens6 E) [(1, true)] [(5, true)]).2
        (by simpa [wordVal, letterVal, b3Gens6, b3KerMap] using b3_comm_3_7 E)

theorem wordVal_phanB3Rels
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range (b3Gens6 E))))) :
    ∀ w ∈ phanB3Rels, wordVal (b3Gens E) w = 1 := by
  obtain ⟨hu1, hu2⟩ := phanA3_kernel_vanish (b3Gens6 E) (wordVal_b3_A3 E) h3
  intro w hw
  simp only [phanB3Rels, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | rfl | rfl
  · exact wordVal_b3RankTwoRels E w hw
  · rw [b3KerWord, wordVal_reindex]
    exact hu1
  · rw [b3KerWord, wordVal_reindex]
    exact hu2

@[expose] noncomputable def b3Hom
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range (b3Gens6 E))))) :
    PhanB3Group →* G :=
  PresentedGroup.toGroup (f := b3Gens E) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact wordVal_phanB3Rels E h3 w hw)

theorem range_b3Hom
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range (b3Gens6 E))))) :
    (b3Hom E h3).range = Subgroup.closure (Set.range (b3Gens E)) := by
  have hcomp : (b3Hom E h3) ∘ (PresentedGroup.of : Fin 8 → PhanB3Group) = b3Gens E :=
    funext fun i => PresentedGroup.toGroup.of _
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp, hcomp]

end CFSG.ClassicalInvolution.Phan.Q3G
