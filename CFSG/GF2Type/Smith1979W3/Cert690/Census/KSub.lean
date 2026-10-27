module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Elt

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

variable {minus : Bool} {D : GrpData} {gens elems : Array ℕ} {par : Array (ℕ × ℕ)}

private theorem certOK_basic {D : GrpData} {gens elems : Array ℕ} {par : Array (ℕ × ℕ)}
    (h : certOK D gens elems par = true) :
    elems.size ≠ 0 ∧ elems[0]! = 0 ∧
      (hashSetOfArray elems).size = elems.size ∧
      (∀ x ∈ elems, x < D.O.size) ∧
      (∀ g ∈ gens, g < D.O.size ∧ g ∈ elems.toList) := by
  unfold certOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true', decide_eq_true_eq,
    beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, hashSetOfArray_contains] at h
  obtain ⟨⟨⟨⟨⟨⟨hne, hone⟩, _⟩, hset⟩, helems⟩, hgens⟩, _⟩ := h
  exact ⟨hne, hone, hset, helems, fun g hg =>
    ⟨(hgens g hg).1, Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp (hgens g hg).2)⟩⟩

private theorem certOK_closed {D : GrpData} {gens elems : Array ℕ} {par : Array (ℕ × ℕ)}
    (h : certOK D gens elems par = true) :
    ∀ i, i < elems.size → ∀ g ∈ gens,
      D.idx.getD (Code.mul D.O[elems[i]!]! D.O[g]!) D.O.size < D.O.size ∧
      D.O[D.idx.getD (Code.mul D.O[elems[i]!]! D.O[g]!) D.O.size]! =
        Code.mul D.O[elems[i]!]! D.O[g]! ∧
      D.idx.getD (Code.mul D.O[elems[i]!]! D.O[g]!) D.O.size ∈ elems.toList := by
  unfold certOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true', decide_eq_true_eq,
    beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, hashSetOfArray_contains] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _, hclosed⟩ := h
  intro i hi g hg
  obtain ⟨⟨hylt, hyeq⟩, hymem⟩ := hclosed i (List.mem_range.mpr hi) g hg
  exact ⟨hylt, hyeq, hymem⟩

private theorem certOK_pos {D : GrpData} {gens elems : Array ℕ} {par : Array (ℕ × ℕ)}
    (h : certOK D gens elems par = true) : 0 < elems.size :=
  Nat.pos_of_ne_zero (certOK_basic h).1

private theorem certOK_head {D : GrpData} {gens elems : Array ℕ} {par : Array (ℕ × ℕ)}
    (h : certOK D gens elems par = true) (h0 : 0 < elems.size) : elems[0] = 0 := by
  have h' := (certOK_basic h).2.1
  rwa [array_getElem!_eq_getElem_of_lt h0] at h'

private theorem certOK_one_mem {D : GrpData} {gens elems : Array ℕ} {par : Array (ℕ × ℕ)}
    (hzero : D.O[0]! = Code.one) (h : certOK D gens elems par = true) :
    Code.one ∈ elems.toList.map fun i => D.O[i]! := by
  have h0pos : 0 < elems.size := certOK_pos h
  have h0 : elems[0] = 0 := certOK_head h h0pos
  refine List.mem_map.mpr ⟨elems[0], array_getElem_mem_toList h0pos, ?_⟩
  show D.O[elems[0]]! = Code.one
  rw [h0]
  exact hzero

private theorem certOK_mul_mem {D : GrpData} {gens elems : Array ℕ} {par : Array (ℕ × ℕ)}
    (h : certOK D gens elems par = true) :
    ∀ c ∈ elems.toList.map (fun i => D.O[i]!),
      ∀ g ∈ gens.toList.map (fun i => D.O[i]!),
        Code.mul c g ∈ elems.toList.map fun i => D.O[i]! := by
  intro c hc g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  obtain ⟨p, hp, hpi⟩ := List.mem_iff_getElem.mp hi
  have hp' : p < elems.size := by simpa [Array.length_toList] using hp
  have hpi' : elems[p]! = i := by
    rw [array_getElem!_eq_getElem_of_lt hp', ← Array.getElem_toList hp]
    exact hpi
  obtain ⟨-, hyeq, hymem⟩ := certOK_closed h p hp' q (Array.mem_toList_iff.mp hq)
  rw [← hpi', ← hyeq]
  exact List.mem_map.mpr ⟨_, hymem, rfl⟩

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
private theorem certOK_gen_inv {D : GrpData} {gens elems : Array ℕ} {par : Array (ℕ × ℕ)}
    (hD : GrpFacts minus D) (h : certOK D gens elems par = true) :
    ∀ g ∈ gens.toList.map (fun i => D.O[i]!),
      ∃ h' ∈ elems.toList.map (fun i => D.O[i]!), Code.mul g h' = Code.one := by
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  obtain ⟨-, -, -, -, hgens⟩ := certOK_basic h
  have hone_mem := certOK_one_mem hD.zero h
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  have hqO : q < D.O.size := (hgens q (Array.mem_toList_iff.mp hq)).1
  have hg_gen : D.O[q]! ∈ gens.toList.map fun i => D.O[i]! :=
    List.mem_map.mpr ⟨q, hq, rfl⟩
  have hg_lt : D.O[q]! < 2 ^ 36 := hD.code_lt hqO
  have hpow_mem : ∀ k, codePow (D.O[q]!) k ∈ elems.toList.map fun i => D.O[i]! := by
    intro k
    induction k with
    | zero =>
      rw [codePow_eq_go, codePow.go_zero]
      exact hone_mem
    | succ k ih =>
      rw [codePow_succ hg_lt k]
      exact certOK_mul_mem h _ ih _ hg_gen
  let x := hD.elt q
  have hpow_one : codePow (D.O[q]!) (orderOf x) = Code.one :=
    (hD.codePow_eq_one_iff hqO (orderOf x)).mpr (pow_orderOf_eq_one x)
  have hn : 0 < orderOf x := orderOf_pos x
  have hmul : Code.mul (codePow (D.O[q]!) (orderOf x - 1)) (D.O[q]!) = Code.one := by
    rw [← codePow_succ hg_lt (orderOf x - 1), Nat.sub_add_cancel hn]
    exact hpow_one
  exact ⟨codePow (D.O[q]!) (orderOf x - 1), hpow_mem _,
    EnumCert.code_mul_comm_one hmul⟩

end CFSG.GF2Type.Smith1979W3.Cert690

end
