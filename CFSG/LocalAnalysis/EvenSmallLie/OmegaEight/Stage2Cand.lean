module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Native
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Lin

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def candFilter (E₂ : Enum) (samples : List ℕ) (m : ℕ) : Bool :=
  memK E₂.keys (mulK m m) && fpowK m 256 == idK &&
    samples.all fun c => memK E₂.keys (mulK (mulK m c) (fpowK m 255))

@[expose] def repOK (EC : Enum) (reps : List (ℕ × ℕ)) (m : ℕ) : Bool :=
  reps.any fun r => memK EC.keys (mulK r.2 m)

@[expose] def candCons (zs ys : List ℕ) (cc : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.zipWith (fun z y => (z, y)) zs ys ++ cc

@[expose] def candCheck (EC E₂ : Enum) (samples : List ℕ) (reps : List (ℕ × ℕ)) (ys : List ℕ)
    (tuples : List (List ℕ)) (cases : List (List (ℕ × ℕ))) : Bool :=
  cases.all fun cc => tuples.all fun zs =>
    linCheck (candCons zs ys cc) &&
      spanAll (linBasis (candCons zs ys cc)) (linFree (candCons zs ys cc)).length
        fun m => !(candFilter E₂ samples m) || repOK EC reps m

theorem repOK_of_candCheck {EC E₂ : Enum} {samples : List ℕ} {reps : List (ℕ × ℕ)}
    {ys : List ℕ} {tuples : List (List ℕ)} {cases : List (List (ℕ × ℕ))}
    (h : candCheck EC E₂ samples reps ys tuples cases = true) {cc : List (ℕ × ℕ)}
    (hcc : cc ∈ cases) {zs : List ℕ} (hzs : zs ∈ tuples) {m : ℕ} (hm : m < 2 ^ 144)
    (hsol : ∀ c ∈ candCons zs ys cc, mulK c.1 m = mulK m c.2)
    (hf : candFilter E₂ samples m = true) : repOK EC reps m = true := by
  simp only [candCheck, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h cc hcc zs hzs
  have := forall_of_linCheck h1 h2 hm hsol
  rw [hf] at this
  simpa using this

theorem exists_rep_of_candCheck {cs c₂s : Array (ℕ × ℕ)} {EC E₂ : Enum} {samples : List ℕ}
    {reps : List (ℕ × ℕ)} {ys : List ℕ} {tuples : List (List ℕ)} {cases : List (List (ℕ × ℕ))}
    (hEC : enumOK cs EC = true) (hE₂ : enumOK c₂s E₂ = true) (hsz : E₂.keys.size < 2 ^ 64)
    (h : candCheck EC E₂ samples reps ys tuples cases = true)
    (hreps : reps.all (fun r => invPair r.1 r.2) = true)
    (hsamp : samples.all (memK E₂.keys) = true) {x : GL12} {cc : List (ℕ × ℕ)}
    (hcc : cc ∈ cases) {zs : List ℕ} (hzs : zs ∈ tuples)
    (hsol : ∀ c ∈ candCons zs ys cc, mulK c.1 (keyOfMat x) = mulK (keyOfMat x) c.2)
    (hx2 : x * x ∈ grpOf c₂s) (hx256 : x ^ 256 = 1)
    (hxn : ∀ c ∈ grpOf c₂s, x * c * x⁻¹ ∈ grpOf c₂s) :
    ∃ r ∈ reps, (glOf r.1 r.2)⁻¹ * x ∈ grpOf cs := by
  set k := keyOfMat x with hk
  have hr : Rep k x := rep_keyOfMat x
  have hinv : x ^ 255 = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hx256]
  have hf : candFilter E₂ samples k = true := by
    simp only [candFilter, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨Enum.memK_of_mem' hE₂ hsz hx2 (hr.mul hr) (mulK_lt _ _), ?_⟩, fun c hc => ?_⟩
    · exact (hr.fpow (by norm_num)).key_unique (by rw [hx256]; exact rep_one) (fpowK_lt _ _)
        idK_lt
    · simp only [List.all_eq_true] at hsamp
      obtain ⟨y, hy, hry⟩ := Enum.rep_of_memK hE₂ (hsamp c hc)
      have h1 : Rep (mulK (mulK k c) (fpowK k 255)) (x * y * x⁻¹) := by
        rw [← hinv]
        exact (hr.mul hry).mul (hr.fpow (by norm_num))
      exact Enum.memK_of_mem' hE₂ hsz (hxn y hy) h1 (mulK_lt _ _)
  have hok := repOK_of_candCheck h hcc hzs (keyOfMat_lt _) hsol hf
  simp only [repOK, List.any_eq_true] at hok
  obtain ⟨r, hrm, hmem⟩ := hok
  refine ⟨r, hrm, ?_⟩
  simp only [List.all_eq_true] at hreps
  have h2 : Rep (mulK r.2 k) ((glOf r.1 r.2)⁻¹ * x) := (rep_glOf_inv (hreps r hrm)).mul hr
  exact Enum.mem_of_memK hEC hmem h2

end CFSG.EvenSmallLie.OmegaEight.Stage2
