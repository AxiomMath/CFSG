module

public import CFSG.LieType.Multipliers.U43Field
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.ClassicalInvolution.Phan.Phan3AData

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg
open CFSG.LieType.Multipliers.U43 (F9)
open scoped Matrix

abbrev K9 : Type := GaloisField 3 2

theorem card_K9 : Nat.card K9 = (3 ^ 1) ^ 2 := by
  rw [GaloisField.card 3 2 (by norm_num)]
  norm_num

noncomputable def phi9 : F9 ≃+* K9 := by
  classical
  haveI : Fintype K9 := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [F9.card_eq, ← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
    rfl)

noncomputable abbrev phi9r : F9 →+* K9 := phi9.toRingHom

@[expose] def cj9 (x : F9) : F9 := x * x * x

@[expose] def ct9 {d : Nat} (A : Matrix (Fin d) (Fin d) F9) : Matrix (Fin d) (Fin d) F9 :=
  (A.map cj9).transpose

theorem phi9_cj (x : F9) : unitaryInvolution K9 3 1 (phi9r x) = phi9r (cj9 x) := by
  rw [unitaryInvolution_apply, cj9, map_mul, map_mul]
  ring

theorem conjTr_map_phi9 {d : Nat} (M : Matrix (Fin d) (Fin d) F9) :
    conjTr (unitaryInvolution K9 3 1) (M.map phi9r) = (ct9 M).map phi9r := by
  ext i j
  simp only [conjTr, ct9, Matrix.transpose_apply, Matrix.map_apply, phi9_cj]

@[expose] def IsMU {d : Nat} (M : Matrix (Fin d) (Fin d) F9) : Prop :=
  ct9 M * M = 1 ∧ M.det = 1

instance {d : Nat} (M : Matrix (Fin d) (Fin d) F9) : Decidable (IsMU M) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[expose] noncomputable def toSu {d : Nat} (M : Matrix (Fin d) (Fin d) F9) (h : IsMU M) :
    Su K9 3 1 d :=
  ⟨⟨M.map phi9r, (ct9 M).map phi9r,
      by rw [← Matrix.map_mul, mul_eq_one_comm.mp h.1, Matrix.map_one _ (map_zero _) (map_one _)],
      by rw [← Matrix.map_mul, h.1, Matrix.map_one _ (map_zero _) (map_one _)]⟩,
    by
      show (M.map phi9r).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h.2, map_one],
    by
      show conjTr _ (M.map phi9r) * M.map phi9r = 1
      rw [conjTr_map_phi9, ← Matrix.map_mul, h.1, Matrix.map_one _ (map_zero _) (map_one _)]⟩

@[expose] def letterVal {n : Nat} {G : Type*} [Group G] (g : Fin n → G) (l : Fin n × Bool) : G :=
  cond l.2 (g l.1) (g l.1)⁻¹

@[expose] def wordVal {n : Nat} {G : Type*} [Group G] (g : Fin n → G) (w : List (Fin n × Bool)) :
    G :=
  (w.map (letterVal g)).prod

@[expose] def letterMat {n d : Nat} (M : Fin n → Matrix (Fin d) (Fin d) F9)
    (l : Fin n × Bool) : Matrix (Fin d) (Fin d) F9 :=
  cond l.2 (M l.1) (ct9 (M l.1))

@[expose] def wordMat {n d : Nat} (M : Fin n → Matrix (Fin d) (Fin d) F9)
    (w : List (Fin n × Bool)) : Matrix (Fin d) (Fin d) F9 :=
  (w.map (letterMat M)).prod

section Transport

variable {n d : Nat} (g : Fin n → Su K9 3 1 d) (M : Fin n → Matrix (Fin d) (Fin d) F9)

theorem val_letterVal
    (hg : ∀ i, (((g i : Su K9 3 1 d) : GL (Fin d) K9) : Matrix (Fin d) (Fin d) K9) =
      (M i).map phi9r)
    (hU : ∀ i, ct9 (M i) * M i = 1) (l : Fin n × Bool) :
    (((letterVal g l : Su K9 3 1 d) : GL (Fin d) K9) : Matrix (Fin d) (Fin d) K9) =
      (letterMat M l).map phi9r := by
  obtain ⟨i, b⟩ := l
  cases b
  · have h1 : (M i).map phi9r * (ct9 (M i)).map phi9r = 1 := by
      rw [← Matrix.map_mul, mul_eq_one_comm.mp (hU i), Matrix.map_one _ (map_zero _) (map_one _)]
    have hu : ((g i : GL (Fin d) K9)).inv = (ct9 (M i)).map phi9r := by
      calc (g i : GL (Fin d) K9).inv
          = (g i : GL (Fin d) K9).inv * ((M i).map phi9r * (ct9 (M i)).map phi9r) := by
            rw [h1, Matrix.mul_one]
        _ = ((g i : GL (Fin d) K9).inv * (g i : GL (Fin d) K9).val) *
              (ct9 (M i)).map phi9r := by
            rw [← hg i, Matrix.mul_assoc]
        _ = (ct9 (M i)).map phi9r := by rw [(g i : GL (Fin d) K9).inv_val, Matrix.one_mul]
    exact hu
  · exact hg i

theorem val_wordVal
    (hg : ∀ i, (((g i : Su K9 3 1 d) : GL (Fin d) K9) : Matrix (Fin d) (Fin d) K9) =
      (M i).map phi9r)
    (hU : ∀ i, ct9 (M i) * M i = 1) (w : List (Fin n × Bool)) :
    (((wordVal g w : Su K9 3 1 d) : GL (Fin d) K9) : Matrix (Fin d) (Fin d) K9) =
      (wordMat M w).map phi9r := by
  induction w with
  | nil =>
    simp only [wordVal, wordMat, List.map_nil, List.prod_nil]
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  | cons l w ih =>
    simp only [wordVal, wordMat, List.map_cons, List.prod_cons] at ih ⊢
    rw [Subgroup.coe_mul, Units.val_mul, val_letterVal g M hg hU l, ih, Matrix.map_mul]

theorem wordVal_eq_one
    (hg : ∀ i, (((g i : Su K9 3 1 d) : GL (Fin d) K9) : Matrix (Fin d) (Fin d) K9) =
      (M i).map phi9r)
    (hU : ∀ i, ct9 (M i) * M i = 1) {w : List (Fin n × Bool)} (h : wordMat M w = 1) :
    wordVal g w = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [val_wordVal g M hg hU w, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem wordMat_eq_of_wordVal_eq
    (hg : ∀ i, (((g i : Su K9 3 1 d) : GL (Fin d) K9) : Matrix (Fin d) (Fin d) K9) =
      (M i).map phi9r)
    (hU : ∀ i, ct9 (M i) * M i = 1) {w w' : List (Fin n × Bool)}
    (h : wordVal g w = wordVal g w') : wordMat M w = wordMat M w' := by
  have := congrArg (fun x : Su K9 3 1 d => ((x : GL (Fin d) K9) : Matrix (Fin d) (Fin d) K9)) h
  simp only [val_wordVal g M hg hU] at this
  exact Matrix.map_injective phi9r.injective this

end Transport

theorem embPair_map {F F' : Type*} [Field F] [Field F'] (f : F →+* F') (c : Fin 3)
    (A : Matrix (Fin 2) (Fin 2) F) : embPair c (A.map f) = (embPair c A).map f := by
  fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [embPair]

theorem blockMat_map {F F' : Type*} [Field F] [Field F'] (f : F →+* F') {m k i : Nat}
    (A : Matrix (Fin k) (Fin k) F) : (blockMat m i A).map f = blockMat m i (A.map f) := by
  have hL : (blockSel F m k i).map f = blockSel F' m k i := by
    ext a j
    simp only [Matrix.map_apply, blockSel_apply]
    split_ifs <;> simp
  have hLt : ((blockSel F m k i)ᵀ).map f = (blockSel F' m k i)ᵀ := by
    rw [Matrix.transpose_map, hL]
  have hN : (A - 1).map f = A.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]
  unfold blockMat
  rw [Matrix.map_add _ (map_add f), Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_mul,
    Matrix.map_mul, hL, hLt, hN]

@[expose] def i9 : F9 := ⟨0, 1⟩

@[expose] def mA : Matrix (Fin 2) (Fin 2) F9 := !![i9, 0; 0, -i9]

@[expose] def mB : Matrix (Fin 2) (Fin 2) F9 := !![⟨1, 1⟩, ⟨1, 1⟩; ⟨2, 1⟩, ⟨1, 2⟩]

theorem mA_mu : IsMU mA := by decide +kernel

theorem mB_mu : IsMU mB := by decide +kernel

@[expose] noncomputable def A2 : Su K9 3 1 2 := toSu mA mA_mu

@[expose] noncomputable def B2 : Su K9 3 1 2 := toSu mB mB_mu

@[expose] noncomputable def gen2 : Fin 2 → Su K9 3 1 2 := ![A2, B2]

@[expose] def mat2 : Fin 2 → Matrix (Fin 2) (Fin 2) F9 := ![mA, mB]

theorem hg2 (i : Fin 2) : (((gen2 i : Su K9 3 1 2) : GL (Fin 2) K9) : Matrix (Fin 2) (Fin 2) K9) =
    (mat2 i).map phi9r := by
  fin_cases i <;> rfl

theorem hU2 : ∀ i, ct9 (mat2 i) * mat2 i = 1 := by decide +kernel

@[expose] def su2Words : List (List (Fin 2 × Bool)) :=
  ([[], [0], [1], [2], [3], [0, 0], [0, 2], [0, 3], [1, 2], [1, 3], [2, 0], [2, 1], [3, 0], [3, 1],
    [0, 0, 2], [0, 0, 3], [0, 2, 0], [0, 2, 1], [0, 3, 0], [0, 3, 1], [2, 0, 3], [2, 1, 3],
    [3, 0, 2], [3, 1, 2]] : List (List Nat)).map (decodeWord 2)

theorem su2Words_inj : ∀ k k' : Fin 24, wordMat mat2 (su2Words.getD k []) =
    wordMat mat2 (su2Words.getD k' []) → k = k' := by decide +kernel

theorem card_su2 : Nat.card (Su K9 3 1 2) = 24 := by
  obtain ⟨P, hP⟩ := exists_wittMatrix card_K9 2
  rw [← Nat.card_congr (conjEquiv P hP).toEquiv, card_SU_two card_K9]
  norm_num

theorem wordVal_mem_closure (w : List (Fin 2 × Bool)) :
    wordVal gen2 w ∈ Subgroup.closure (Set.range gen2) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
    simp only [wordVal, List.map_cons, List.prod_cons] at ih ⊢
    refine Subgroup.mul_mem _ ?_ ih
    obtain ⟨i, b⟩ := l
    cases b
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)
    · exact Subgroup.subset_closure ⟨i, rfl⟩

theorem closure_gen2 : Subgroup.closure (Set.range gen2) = ⊤ := by
  set H := Subgroup.closure (Set.range gen2)
  have hmem : ∀ k : Fin 24, wordVal gen2 (su2Words.getD k []) ∈ H := fun k =>
    wordVal_mem_closure _
  let f : Fin 24 → H := fun k => ⟨wordVal gen2 (su2Words.getD k []), hmem k⟩
  have hinj : Function.Injective f := by
    intro k k' h
    exact su2Words_inj k k' (wordMat_eq_of_wordVal_eq gen2 mat2 hg2 hU2 (congrArg Subtype.val h))
  have h24 : 24 ≤ Nat.card H := by
    simpa using Nat.card_le_card_of_injective f hinj
  exact Subgroup.eq_top_of_card_eq H
    (le_antisymm (card_su2 ▸ Subgroup.card_le_card_group H) (card_su2 ▸ h24))

@[expose] noncomputable def x3 : Fin 4 → Su K9 3 1 3 :=
  ![embSUid (unitaryInvolution K9 3 1) 2 A2, embSUid (unitaryInvolution K9 3 1) 2 B2,
    embSUid (unitaryInvolution K9 3 1) 0 A2, embSUid (unitaryInvolution K9 3 1) 0 B2]

@[expose] def mat3 : Fin 4 → Matrix (Fin 3) (Fin 3) F9 :=
  ![embPair 2 mA, embPair 2 mB, embPair 0 mA, embPair 0 mB]

theorem hg3 (i : Fin 4) : (((x3 i : Su K9 3 1 3) : GL (Fin 3) K9) : Matrix (Fin 3) (Fin 3) K9) =
    (mat3 i).map phi9r := by
  fin_cases i
  · exact embPair_map phi9r 2 mA
  · exact embPair_map phi9r 2 mB
  · exact embPair_map phi9r 0 mA
  · exact embPair_map phi9r 0 mB

theorem hU3 : ∀ i, ct9 (mat3 i) * mat3 i = 1 := by decide +kernel

theorem wordVal_x3_su3Rels : ∀ r ∈ su3Rels, wordVal x3 r = 1 := by
  have h : ∀ r ∈ su3Rels, wordMat mat3 r = 1 := by decide +kernel
  exact fun r hr => wordVal_eq_one x3 mat3 hg3 hU3 (h r hr)

@[expose] def genIdx : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

@[expose] noncomputable def genElt : Fin 6 → Su K9 3 1 2 := ![A2, B2, A2, B2, A2, B2]

@[expose] def genMat : Fin 6 → Matrix (Fin 2) (Fin 2) F9 := ![mA, mB, mA, mB, mA, mB]

@[expose] noncomputable def x4 : Fin 6 → Su K9 3 1 4 := fun i =>
  blockEmb2 K9 3 1 3 (genIdx i) (genElt i)

@[expose] def mat4 : Fin 6 → Matrix (Fin 4) (Fin 4) F9 := fun i =>
  blockMat 4 (genIdx i).val (genMat i)

theorem hg4 (i : Fin 6) : (((x4 i : Su K9 3 1 4) : GL (Fin 4) K9) : Matrix (Fin 4) (Fin 4) K9) =
    (mat4 i).map phi9r := by
  have h2 : (((genElt i : Su K9 3 1 2) : GL (Fin 2) K9) : Matrix (Fin 2) (Fin 2) K9) =
      (genMat i).map phi9r := by
    fin_cases i <;> rfl
  show blockMat 4 (genIdx i).val
    (((genElt i : Su K9 3 1 2) : GL (Fin 2) K9) : Matrix (Fin 2) (Fin 2) K9) = _
  rw [h2, mat4, blockMat_map]

theorem hU4 : ∀ i, ct9 (mat4 i) * mat4 i = 1 := by decide +kernel

theorem wordVal_x4_phanA3U1 : wordVal x4 phanA3U1 = 1 := by
  have h : wordMat mat4 phanA3U1 = 1 := by decide +kernel
  exact wordVal_eq_one x4 mat4 hg4 hU4 h

theorem wordVal_x4_phanA3U2 : wordVal x4 phanA3U2 = 1 := by
  have h : wordMat mat4 phanA3U2 = 1 := by decide +kernel
  exact wordVal_eq_one x4 mat4 hg4 hU4 h

end CFSG.ClassicalInvolution.Phan.Q3G
