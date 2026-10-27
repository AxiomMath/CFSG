module

public import CFSG.Sporadic.Co1Block.Perm
public import CFSG.Sporadic.Co1Block.Tools
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public import Certificates.Certificate2043
public import Certificates.Certificate3024
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.Sporadic.Co1.Module.InvPermChar

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F

open CFSG.Open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.InvNative Timmesfeld.Co1Five Matrix

local notation "Rows" => CFSG.Sporadic.Co1Schreier.Native.Rows

theorem xorMaskV_lt {v : ℕ × ℕ → ℕ} (hv : ∀ s, v s < 2 ^ 24) (slots : List (ℕ × ℕ))
    (mask : List ℕ) : xorMaskV v slots mask < 2 ^ 24 := by
  unfold xorMaskV
  have : ∀ (a : ℕ), a < 2 ^ 24 →
      mask.foldl (fun acc m => acc ^^^ v (slots.getD m (0, 0))) a < 2 ^ 24 := by
    induction mask with
    | nil => exact fun a ha => ha
    | cons m mask ih =>
      intro a ha
      rw [List.foldl_cons]
      exact ih _ (Nat.xor_lt_two_pow ha (hv _))
  exact this 0 (by norm_num)

theorem toVecD_xorMaskV {cM : Matrix (Fin 24) (Fin 24) (ZMod 2)} {v w : ℕ × ℕ → ℕ}
    (hvw : ∀ s, toVecD 24 (w s) = cM *ᵥ toVecD 24 (v s)) (slots : List (ℕ × ℕ))
    (mask : List ℕ) :
    toVecD 24 (xorMaskV w slots mask) = cM *ᵥ toVecD 24 (xorMaskV v slots mask) := by
  unfold xorMaskV
  have : ∀ (a b : ℕ), toVecD 24 b = cM *ᵥ toVecD 24 a →
      toVecD 24 (mask.foldl (fun acc m => acc ^^^ w (slots.getD m (0, 0))) b) =
        cM *ᵥ toVecD 24 (mask.foldl (fun acc m => acc ^^^ v (slots.getD m (0, 0))) a) := by
    induction mask with
    | nil => exact fun a b h => h
    | cons m mask ih =>
      intro a b h
      rw [List.foldl_cons, List.foldl_cons]
      refine ih _ _ ?_
      rw [toVecD_xor, toVecD_xor, h, hvw, Matrix.mulVec_add]
  exact this 0 0 (by rw [toVecD_zero, Matrix.mulVec_zero])

theorem planOKv_map {xs : Std.HashSet ℕ} {X : List ℕ} (hxs : ∀ x, xs.contains x = true ↔ x ∈ X)
    {cM : Matrix (Fin 24) (Fin 24) (ZMod 2)}
    (hX : ∀ x ∈ X, x < 2 ^ 24 ∧ ∃ y ∈ X, toVecD 24 y = cM *ᵥ toVecD 24 x)
    {v w : ℕ × ℕ → ℕ} (hw : ∀ s, w s < 2 ^ 24)
    (hvw : ∀ s, toVecD 24 (w s) = cM *ᵥ toVecD 24 (v s)) {P : Plan}
    (h : planOKv xs v P = true) : planOKv xs w P = true := by
  unfold planOKv at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h ⊢
  refine ⟨fun r hr => ?_, fun m hm => ?_⟩
  · have h1 := h.1 r hr
    apply toVecD_injective (hw _) (xorMaskV_lt hw _ _)
    rw [hvw, toVecD_xorMaskV hvw, h1]
  · obtain ⟨hlt, y, hy, hyv⟩ := hX _ ((hxs _).1 (h.2 m hm))
    rw [hxs]
    have : y = xorMaskV w P.slots m :=
      toVecD_injective (hX y hy).1 (xorMaskV_lt hw _ _) (by rw [hyv, toVecD_xorMaskV hvw])
    rwa [← this]

@[expose] noncomputable def μG : ↥GA →* Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))).comp GA.subtype

theorem μG_apply (x : ↥GA) : μG x = ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := rfl

theorem μG_injective : Function.Injective μG := fun _ _ h => Subtype.ext (Units.ext h)

unseal CFSG.Sporadic.Co1Block.certVecs in
theorem certVecs_size : certVecs.size = 98280 := by
  unfold certVecs CFSG.Monster.B.Co2.Native.hexTable
  rw [Array.size_ofFn]

theorem mem_certVecs_iff {x : ℕ} : x ∈ certVecs.toList ↔ ∃ i < 98280, certVecs[i]! = x := by
  constructor
  · intro h
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
    have hi' : i < certVecs.size := by rwa [Array.length_toList] at hi
    refine ⟨i, by rw [← certVecs_size]; exact hi', ?_⟩
    rw [getElem!_pos certVecs i hi', ← e]
    exact (Array.getElem_toList hi').symm
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < certVecs.size := by rw [certVecs_size]; exact hi
    rw [getElem!_pos certVecs i hi', ← Array.getElem_toList hi']
    exact List.getElem_mem _

theorem toVecD_mem_certX {x : ℕ} (hx : x ∈ certVecs.toList) : toVecD 24 x ∈ certX := by
  obtain ⟨i, hi, e⟩ := mem_certVecs_iff.1 hx
  exact ⟨i, hi, by rw [← e]; rfl⟩

theorem exists_mem_of_certX {v : Vec24} (hv : v ∈ certX) :
    ∃ y ∈ certVecs.toList, toVecD 24 y = v := by
  obtain ⟨i, hi, rfl⟩ := hv
  exact ⟨certVecs[i]!, mem_certVecs_iff.2 ⟨i, hi, rfl⟩, rfl⟩

theorem contains_xs {x : ℕ} :
    (Std.HashSet.ofList certVecs.toList).contains x = true ↔ x ∈ certVecs.toList := by
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem]

section WithCerts

theorem hX_GA (c : ↥GA) : ∀ x ∈ certVecs.toList, x < 2 ^ 24 ∧
    ∃ y ∈ certVecs.toList, toVecD 24 y = μG c *ᵥ toVecD 24 x := by
  intro x hx
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := mem_certVecs_iff.1 hx
    exact certVecs_lt hi
  · obtain ⟨y, hy, hyv⟩ := exists_mem_of_certX
      (mulVec_mem_certX c.2 (toVecD_mem_certX hx))
    exact ⟨y, hy, by rw [hyv]; rfl⟩

end WithCerts

theorem mem_stageStep {xs : Std.HashSet ℕ} {P : Plan} {cands : List (Array ℕ)}
    {pres : List (List (Array ℕ))} {pre : List (Array ℕ)} {a : Array ℕ} (hpre : pre ∈ pres)
    (ha : a ∈ cands) (h : planOK xs (tupImgs (pre ++ [a])) P = true) :
    pre ++ [a] ∈ stageStep xs P cands pres := by
  unfold stageStep
  rw [List.mem_flatMap]
  refine ⟨pre, hpre, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨a, ha, by simp [h]⟩

theorem stagesAux_mem {xs : Std.HashSet ℕ} (tw : ℕ → Array ℕ) :
    ∀ (Ps : List Plan) (cs : List (List (Array ℕ))) (j0 : ℕ)
      (pres : List (List (Array ℕ))) (hlen : Ps.length = cs.length),
      (List.range j0).map tw ∈ pres →
      (∀ i (hi : i < Ps.length), tw (j0 + i) ∈ cs[i]'(by omega) ∧
        planOK xs (tupImgs ((List.range (j0 + i + 1)).map tw)) Ps[i] = true) →
      (List.range (j0 + Ps.length)).map tw ∈ stagesAux xs Ps cs pres := by
  intro Ps
  induction Ps with
  | nil =>
    intro cs j0 pres hlen hmem _
    cases cs with
    | nil => simpa [stagesAux] using hmem
    | cons c cs => simp at hlen
  | cons P Ps ih =>
    intro cs j0 pres hlen hmem hall
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have hlen' : Ps.length = cs.length := by simpa using hlen
      have h0 := hall 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      have hstep : (List.range (j0 + 1)).map tw ∈ stageStep xs P c pres := by
        rw [List.range_succ, List.map_append, List.map_singleton]
        exact mem_stageStep hmem h0.1 (by
          have := h0.2
          rwa [List.range_succ, List.map_append, List.map_singleton] at this)
      have := ih cs (j0 + 1) (stageStep xs P c pres) hlen' hstep (fun i hi => by
        have h1 := hall (i + 1) (by simpa using hi)
        have e : j0 + 1 + i = j0 + (i + 1) := by omega
        rw [e]
        simpa using h1)
      have e2 : j0 + 1 + Ps.length = j0 + (P :: Ps).length := by simp; omega
      rw [e2] at this
      simpa [stagesAux] using this

@[expose] def colsMat (cols : List ℕ) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  Matrix.of fun r m => toVecD 24 (cols.getD m 0) r

theorem rowsMatrix_colsToRows (cols : List ℕ) : rowsMatrix 24 (colsToRows cols) = colsMat cols := by
  ext r m
  rw [rowsMatrix_apply, colsMat, Matrix.of_apply]
  unfold colsToRows
  simp only [Array.getElem?_ofFn, r.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_ofBits, toVecD_apply]

theorem mul_colsMat {cM : Matrix (Fin 24) (Fin 24) (ZMod 2)} {c₁ c₂ : List ℕ}
    (h : ∀ m, toVecD 24 (c₂.getD m 0) = cM *ᵥ toVecD 24 (c₁.getD m 0)) :
    cM * colsMat c₁ = colsMat c₂ := by
  ext r m
  have := congrFun (h m) r
  show (cM * Matrix.of fun r m => toVecD 24 (c₁.getD m 0) r) r m = toVecD 24 (c₂.getD m 0) r
  rw [this, Matrix.mul_apply]
  rfl

theorem take_map_orbImg (omT : Array Rows) (us : List ℕ) (n : ℕ) (hn : n ≤ us.length) :
    (us.map (orbImg omT)).take n = (List.range n).map fun i => orbImg omT (us.getD i 0) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    have hi' : i < us.length := by omega
    simp [List.getD_eq_getElem?_getD, hi']

theorem commGL_pow {a b : GL24} (e : a * b = b * a) (n : ℕ) : a * b ^ n = b ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, mul_assoc, ← e]

theorem commGL_mul {a b c : GL24} (e1 : a * b = b * a) (e2 : a * c = c * a) :
    a * (b * c) = (b * c) * a := by
  rw [← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]

theorem validRows_mul' {X Y : Rows} (hX : validRows X = true) (hY : validRows Y = true) :
    validRows (Native.mul X Y) = true := by
  have hXs := CFSG.Sporadic.Co1.Module.validRows_size hX
  unfold Native.mul mulRows validRows
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by rw [Array.size_map, hXs], fun i hi => ?_⟩
  rw [Array.getElem_map]
  exact CFSG.Sporadic.Co1.Module.vecMulN_lt _ (fun j => by
    by_cases hj : j < Y.size
    · simp only [Array.getElem?_eq_getElem hj, Option.getD_some]
      exact CFSG.Sporadic.Co1.Module.validRows_lt hY (by simp)
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hj)]; norm_num) _

theorem validRows_one : validRows (Native.one ()) = true := by
  unfold Native.one validRows idRows
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by rw [Array.size_ofFn], fun i hi => ?_⟩
  rw [Array.getElem_ofFn]
  have : i < 24 := by simpa using hi
  rw [Nat.shiftLeft_eq, one_mul]
  exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) this) (by norm_num)

theorem validRows_pow {X : Rows} (hX : validRows X = true) (e : ℕ) :
    validRows (Native.pow X e) = true := by
  induction e with
  | zero => exact validRows_one
  | succ e ih => exact validRows_mul' ih hX

theorem validRows_colsToRows (cols : List ℕ) : validRows (colsToRows cols) = true := by
  unfold colsToRows validRows
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by rw [Array.size_ofFn], fun i hi => ?_⟩
  rw [Array.getElem_ofFn]
  exact ofBits_lt 24 _

@[expose] noncomputable def Cen (g1 g2 : ↥GA) : Subgroup ↥GA :=
  Subgroup.centralizer ({g1, g2} : Set ↥GA)

theorem mem_Cen {g1 g2 c : ↥GA} : c ∈ Cen g1 g2 ↔ c * g1 = g1 * c ∧ c * g2 = g2 * c := by
  unfold Cen
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => ⟨(h.1).symm, (h.2).symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

section Counting

variable
  {b1 b2 : Rows} {gens : List Rows} {L : Leaf} {r : ℕ} {g1 g2 : ↥GA}

theorem rows_eq_of_mrep {X Y : Rows} (hX : validRows X = true) (hY : validRows Y = true)
    {g : GL24} (h1 : MRep X g) (h2 : MRep Y g) : X = Y :=
  CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hX hY (h1.trans h2.symm)

end Counting

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F
