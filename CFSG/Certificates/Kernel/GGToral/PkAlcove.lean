module

public import CFSG.Certificates.Kernel.GGToral.PkLetter
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertAlcove

public section

namespace CFSG.KC.GGToral

@[expose] def packFrom : ℕ → List ℕ → ℕ
  | _, [] => 0
  | j, v :: l => v * 2 ^ (16 * j) + packFrom (j + 1) l

@[expose] noncomputable def alcLoop (p n t : ℕ) (ts : List ℕ) (b j x : ℕ) (m : ℕ) :
    List ℕ → List ℕ :=
  Nat.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
    (fun i ihi => fun acc => ihi (alcB p n ts (Nat.sub b (Nat.mul t i)) (Nat.add j 1)
      (Nat.add x (Nat.shiftLeft i (Nat.mul 16 j))) acc)) m

theorem alcB_nil (p n b j x : ℕ) (acc : List ℕ) :
    alcB p n [] b j x acc =
      Bool.rec (motive := fun _ => List ℕ) (modL p n x :: acc) acc (Nat.beq (modL p n x) 0) := rfl

theorem alcB_cons (p n t : ℕ) (ts : List ℕ) (b j x : ℕ) (acc : List ℕ) :
    alcB p n (t :: ts) b j x acc = alcLoop p n t ts b j x (Nat.add (Nat.div b t) 1) acc := rfl

theorem alcB_mono (p n : ℕ) (ts : List ℕ) :
    ∀ (b j x : ℕ) (acc : List ℕ), ∀ y ∈ acc, y ∈ alcB p n ts b j x acc := by
  induction ts with
  | nil =>
    intro b j x acc y hy
    rw [alcB_nil]
    cases Nat.beq (modL p n x) 0
    · exact List.mem_cons_of_mem _ hy
    · exact hy
  | cons t ts ih =>
    intro b j x acc y hy
    rw [alcB_cons]
    generalize Nat.add (Nat.div b t) 1 = m
    induction m generalizing acc with
    | zero => exact hy
    | succ m ihm => exact ihm _ (ih _ _ _ _ y hy)

theorem alcLoop_mono (p n t : ℕ) (ts : List ℕ) (b j x : ℕ) :
    ∀ (m : ℕ) (L : List ℕ), ∀ y ∈ L, y ∈ alcLoop p n t ts b j x m L := by
  intro m
  induction m with
  | zero => exact fun L y hy => hy
  | succ m ihm => exact fun L y hy => ihm _ y (alcB_mono p n ts _ _ _ L y hy)

theorem alcB_complete (p n : ℕ) (ts : List ℕ) (hts : ∀ t ∈ ts, 0 < t) :
    ∀ (b j x : ℕ) (acc μ : List ℕ), μ.length = ts.length →
      (List.zipWith (· * ·) ts μ).sum ≤ b → modL p n (x + packFrom j μ) ≠ 0 →
      modL p n (x + packFrom j μ) ∈ alcB p n ts b j x acc := by
  induction ts with
  | nil =>
    intro b j x acc μ hlen _ hy
    cases μ with
    | cons _ _ => simp at hlen
    | nil =>
      simp only [packFrom, add_zero] at hy ⊢
      rw [alcB_nil]
      have hb : Nat.beq (modL p n x) 0 = false := Bool.eq_false_iff.mpr fun h => hy (Nat.eq_of_beq_eq_true h)
      rw [hb]
      exact List.mem_cons_self
  | cons t ts ih =>
    intro b j x acc μ hlen hsum hy
    cases μ with
    | nil => simp at hlen
    | cons v μ' =>
      have ht : 0 < t := hts t List.mem_cons_self
      have hts' : ∀ s ∈ ts, 0 < s := fun s hs => hts s (List.mem_cons_of_mem _ hs)
      simp only [List.zipWith_cons_cons, List.sum_cons] at hsum
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hv : v < b / t + 1 := by
        rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le ht, Nat.mul_comm]
        omega
      have hx : x + packFrom j (v :: μ') = (x + v <<< (16 * j)) + packFrom (j + 1) μ' := by
        simp only [packFrom, Nat.shiftLeft_eq]
        ring
      rw [hx] at hy ⊢
      have hin := fun acc' => ih hts' (b - t * v) (j + 1) (x + v <<< (16 * j)) acc' μ' hlen
        (by omega) hy
      rw [alcB_cons]
      change _ ∈ alcLoop p n t ts b j x (b / t + 1) acc
      generalize b / t + 1 = m at hv
      induction m generalizing acc with
      | zero => omega
      | succ m ihm =>
        change _ ∈ alcLoop p n t ts b j x m (alcB p n ts (b - t * m) (j + 1)
          (x + m <<< (16 * j)) acc)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
        · exact ihm _ hv
        · exact alcLoop_mono p n t ts b j x v _ _ (hin acc)

theorem packN_succ' (m : ℕ) (f : ℕ → ℕ) :
    packN (m + 1) f = f 0 + 2 ^ 16 * packN m (fun i => f (i + 1)) := by
  rw [packN_eq_sum, packN_eq_sum, Finset.sum_range_succ', Finset.mul_sum, mul_zero, pow_zero,
    one_mul, add_comm]
  refine congrArg (f 0 + ·) (Finset.sum_congr rfl fun i _ => ?_)
  rw [show 16 * (i + 1) = 16 + 16 * i by ring, pow_add, mul_assoc]

theorem packFrom_eq (l : List ℕ) : ∀ j, packFrom j l = 2 ^ (16 * j) * packN l.length (fun i => l.getD i 0) := by
  induction l with
  | nil => intro j; simp [packFrom, packN]
  | cons v l ih =>
    intro j
    rw [packFrom, ih, List.length_cons, packN_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [show 16 * (j + 1) = 16 * j + 16 by ring, pow_add]
    ring

theorem packFrom_ofFn {n : ℕ} (f : Fin n → ℕ) :
    packFrom 0 (List.ofFn f) = packN n (fun i => if h : i < n then f ⟨i, h⟩ else 0) := by
  rw [packFrom_eq, List.length_ofFn, mul_zero, pow_zero, one_mul]
  refine packN_congr fun i hi => ?_
  rw [dif_pos hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.StepTwoToralCert

@[expose] noncomputable def packPt {N : ℕ} (μ : Fin N → ℤ) : ℕ :=
  packN N (fun i => if h : i < N then (μ ⟨i, h⟩).toNat else 0)

theorem alcNZ_complete {τ : Tag} (hτ : tgOK τ = true) {p : ℕ}
    {μ : Fin τ.rank → ℤ} (hμ : (kacOf τ).IsNormal p μ) (h0 : modL p τ.rank (packPt μ) ≠ 0) :
    modL p τ.rank (packPt μ) ∈ alcNZ p τ.rank (pkTheta τ) := by
  have hθpos : ∀ t ∈ pkTheta τ, 0 < t := by
    cases τ <;> simp [tgOK] at hτ <;> decide
  have hθ := pkTheta_eq hτ
  have hlen : (List.ofFn fun i => (μ i).toNat).length = (pkTheta τ).length := by
    rw [hθ, List.length_ofFn, List.length_ofFn]
  have hsum : (List.zipWith (· * ·) (pkTheta τ) (List.ofFn fun i => (μ i).toNat)).sum ≤ p := by
    rw [hθ, tcA_zipWith_ofFn_sum]
    obtain ⟨hnn, hdot⟩ := hμ
    have hθnn : ∀ i, 0 ≤ (kacOf τ).θ i := (kacOf τ).θ_nonneg
    have : ((∑ i, ((kacOf τ).θ i).toNat * (μ i).toNat : ℕ) : ℤ) = (kacOf τ).θ ⬝ᵥ μ := by
      push_cast
      simp only [dotProduct]
      exact Finset.sum_congr rfl fun i _ => by rw [Int.toNat_of_nonneg (hθnn i),
        Int.toNat_of_nonneg (hnn i)]
    omega
  have hpk : packFrom 0 (List.ofFn fun i => (μ i).toNat) = packPt μ := by
    rw [packFrom_ofFn]
    rfl
  have := alcB_complete p τ.rank (pkTheta τ) hθpos p 0 0 [] _ hlen hsum
    (by rw [zero_add, hpk]; exact h0)
  rw [zero_add, hpk] at this
  exact this

theorem vecZ_modL_packPt {τ : Tag} {p : ℕ} {μ : Fin τ.rank → ℤ} (hμ : ∀ i, 0 ≤ μ i)
    (hb : ∀ i, μ i < 65536) : vecZ p τ.rank (modL p τ.rank (packPt μ)) = modP p μ := by
  funext j
  unfold packPt
  rw [vecZ_modL_packN (fun k hk => by rw [dif_pos hk]; have := hb ⟨k, hk⟩; omega) j,
    dif_pos j.2]
  simp only [modP]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (hμ j)]

end CFSG.KC.GGToral
