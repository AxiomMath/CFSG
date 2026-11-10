
module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29E8FiveFourData
public import CFSG.Assembly.LowTwoRankDefs

@[expose] public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.E8FiveFour

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg

def cinvInt (j k : Fin 8) : ℤ := cinvNat j k

theorem cartan_mul_cinv :
    ∀ i k : Fin Tag.E8.rank, ∑ j, Tag.E8.cartan i j * cinvInt j k = if i = k then 1 else 0 := by
  decide

theorem cinv_symm : ∀ j k : Fin 8, cinvInt j k = cinvInt k j := by decide

def normZ (b : Fin Tag.E8.rank → ZMod 5) : ZMod 5 :=
  ∑ j, ∑ k, (cinvInt j k : ZMod 5) * b j * b k

theorem cartan_mul_cinv_cast (i k : Fin Tag.E8.rank) :
    ∑ j, (Tag.E8.cartan i j : ZMod 5) * (cinvInt j k : ZMod 5) = if i = k then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ZMod 5)) (cartan_mul_cinv i k)
  simp only [Int.cast_sum, Int.cast_mul] at h
  rw [h]
  split_ifs <;> simp

theorem normZ_pReflect (i : Fin Tag.E8.rank) (b : Fin Tag.E8.rank → ZMod 5) :
    normZ (pReflect i b) = normZ b := by
  set c : Fin Tag.E8.rank → ZMod 5 := fun j => (Tag.E8.cartan i j : ZMod 5) with hc
  set G : Fin Tag.E8.rank → Fin Tag.E8.rank → ZMod 5 := fun j k => (cinvInt j k : ZMod 5) with hG
  set t := b i with ht
  have hS : ∀ k, ∑ j, c j * G j k = if i = k then 1 else 0 := cartan_mul_cinv_cast i
  have hGs : ∀ j k, G j k = G k j := fun j k => by simp only [hG, cinv_symm j k]
  have hcb : ∑ j, ∑ k, c j * G j k * b k = t := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hS, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact ht.symm
  have hbc : ∑ j, ∑ k, G j k * c k * b j = t := by
    have : ∀ j, ∑ k, G j k * c k * b j = (∑ k, c k * G k j) * b j := fun j => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by rw [hGs j k]; ring
    simp only [this, hS, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact ht.symm
  have hcc : ∑ j, ∑ k, c j * G j k * c k = 2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hS, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    simp only [hc, Tag.cartan_self]
    norm_num
  have hexp : ∀ j k, G j k * pReflect i b j * pReflect i b k =
      G j k * b j * b k - t * (c j * G j k * b k) - t * (G j k * c k * b j) +
        t ^ 2 * (c j * G j k * c k) := fun j k => by
    simp only [pReflect, hc, ht]
    ring
  unfold normZ
  change ∑ j, ∑ k, G j k * pReflect i b j * pReflect i b k = ∑ j, ∑ k, G j k * b j * b k
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcb, hbc,
    hcc]
  ring

theorem normZ_pAct (ω : List (Fin Tag.E8.rank)) (b : Fin Tag.E8.rank → ZMod 5) :
    normZ (pAct ω b) = normZ b := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change normZ (pReflect i (pAct ω b)) = normZ b
    rw [normZ_pReflect, ih]

theorem normZ_smul (c : ZMod 5) (b : Fin Tag.E8.rank → ZMod 5) :
    normZ (c • b) = c ^ 2 * normZ b := by
  simp only [normZ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    change _ * (c * b _) * (c * b _) = _
    ring

theorem normZ_eq_zero_of_pAct {lam : ZMod 5} (hlam : lam = 2 ∨ lam = 3)
    {ω : List (Fin Tag.E8.rank)} {b : Fin Tag.E8.rank → ZMod 5} (h : pAct ω b = lam • b) :
    normZ b = 0 := by
  have h1 := normZ_pAct ω b
  rw [h, normZ_smul] at h1
  have h4 : lam ^ 2 = 4 := by rcases hlam with rfl | rfl <;> decide
  rw [h4] at h1
  have h3 : (3 : ZMod 5) * normZ b = 0 := by linear_combination h1
  have h5 : (5 : ZMod 5) = 0 := by decide
  linear_combination 2 * h3 - normZ b * h5

variable {τ : Tag} {p : ℕ}

theorem pReflect_add (i : Fin τ.rank) (b b' : Fin τ.rank → ZMod p) :
    pReflect i (b + b') = pReflect i b + pReflect i b' := by
  funext j
  simp only [pReflect, Pi.add_apply]
  ring

theorem pReflect_smul (i : Fin τ.rank) (c : ZMod p) (b : Fin τ.rank → ZMod p) :
    pReflect i (c • b) = c • pReflect i b := by
  funext j
  simp only [pReflect, Pi.smul_apply, smul_eq_mul]
  ring

theorem pReflect_pReflect (i : Fin τ.rank) (b : Fin τ.rank → ZMod p) :
    pReflect i (pReflect i b) = b := by
  funext j
  simp only [pReflect, Tag.cartan_self]
  push_cast
  ring

theorem pAct_append (ω ω' : List (Fin τ.rank)) (b : Fin τ.rank → ZMod p) :
    pAct (ω ++ ω') b = pAct ω (pAct ω' b) := by
  simp only [pAct, List.foldr_append]

theorem pAct_add (ω : List (Fin τ.rank)) (b b' : Fin τ.rank → ZMod p) :
    pAct ω (b + b') = pAct ω b + pAct ω b' := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change pReflect i (pAct ω (b + b')) = pReflect i (pAct ω b) + pReflect i (pAct ω b')
    rw [ih, pReflect_add]

theorem pAct_smul (ω : List (Fin τ.rank)) (c : ZMod p) (b : Fin τ.rank → ZMod p) :
    pAct ω (c • b) = c • pAct ω b := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change pReflect i (pAct ω (c • b)) = c • pReflect i (pAct ω b)
    rw [ih, pReflect_smul]

theorem pAct_reverse_pAct (ω : List (Fin τ.rank)) (b : Fin τ.rank → ZMod p) :
    pAct ω.reverse (pAct ω b) = b := by
  induction ω generalizing b with
  | nil => rfl
  | cons i ω ih =>
    rw [List.reverse_cons, pAct_append]
    change pAct ω.reverse (pReflect i (pReflect i (pAct ω b))) = b
    rw [pReflect_pReflect, ih]

theorem pAct_injective (ω : List (Fin τ.rank)) :
    Function.Injective (pAct (p := p) ω) := fun b b' h => by
  rw [← pAct_reverse_pAct ω b, h, pAct_reverse_pAct]

def pActHom (ω : List (Fin τ.rank)) : (Fin τ.rank → ZMod p) →+ (Fin τ.rank → ZMod p) where
  toFun := pAct ω
  map_zero' := by
    have h := pAct_smul ω (0 : ZMod p) 0
    rwa [zero_smul, zero_smul] at h
  map_add' := pAct_add ω

theorem vecP_scaleL (lam : ℕ) (l : List ℕ) :
    vecP (τ := τ) 5 (scaleL lam l) = (lam : ZMod 5) • vecP (τ := τ) 5 l := by
  have key : ∀ (l : List ℕ) (j : ℕ),
      (l.map fun x => lam * x % 5).getD j 0 = lam * l.getD j 0 % 5 := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro j
      cases j with
      | zero => rfl
      | succ j => exact ih j
  funext j
  simp only [vecP, scaleL, Pi.smul_apply, smul_eq_mul, key, ZMod.natCast_mod, Nat.cast_mul]

theorem normL_cast (l : List ℕ) : (normL l : ZMod 5) = normZ (vecP (τ := .E8) 5 l) := by
  simp only [normL, normZ, vecP, cinvInt, ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul,
    Int.cast_natCast]

theorem normL_lt (l : List ℕ) : normL l < 5 := Nat.mod_lt _ (by norm_num)

theorem entryOK_spec {e : Entry} (h : entryOK e = true) :
    (e.lam = 2 ∨ e.lam = 3) ∧
      pAct (toFinWord3 (τ := .E8) e.word) (vecP (τ := .E8) 5 e.rep) =
        (e.lam : ZMod 5) • vecP (τ := .E8) 5 e.rep ∧
      ∀ i : Fin 3,
        pAct (toFinWord3 (τ := .E8) e.word) (vecP (τ := .E8) 5 (e.basis.getD i [])) =
          (e.lam : ZMod 5) • vecP (τ := .E8) 5 (e.basis.getD i []) ∧
        ∀ j : Fin 3, ∃ hj : e.piv.getD j 0 < Tag.E8.rank,
          vecP (τ := .E8) 5 (e.basis.getD i []) ⟨e.piv.getD j 0, hj⟩ = if i = j then 1 else 0 := by
  simp only [entryOK, rows, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hlam, hw⟩, hlen⟩, hrep⟩, -⟩, -⟩, hB⟩ := h
  have hw' : ∀ i ∈ e.word, i < Tag.E8.rank := hw
  refine ⟨hlam, ?_, fun i => ?_⟩
  · rw [← vecP_actL hw' hlen, hrep, vecP_scaleL]
  · obtain ⟨⟨hbl, hbact⟩, hpiv⟩ := hB i i.2
    refine ⟨by rw [← vecP_actL hw' hbl, hbact, vecP_scaleL], fun j => ?_⟩
    obtain ⟨hj8, hjv⟩ := hpiv j j.2
    refine ⟨hj8, ?_⟩
    simp only [vecP]
    rw [hjv]
    by_cases hij : i = j
    · simp [hij]
    · have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, this]

theorem e8FiveFourCheck_spec (h : e8FiveFourCheck () = true) :
    (∀ e ∈ entries, entryOK e = true) ∧ ∀ r ∈ kacRepsN, repCovered r = true := by
  simpa only [e8FiveFourCheck, entriesOK, Bool.and_eq_true, List.all_eq_true] using h

theorem exists_datum_of_check (hchk : e8FiveFourCheck () = true)
    (hcover : ∀ b : Fin Tag.E8.rank → ZMod 5, ∃ r ∈ kacRepsN, ∃ σ : List (Fin Tag.E8.rank),
      pAct σ (vecP (τ := .E8) 5 r) = b)
    {lam : ZMod 5} (hlam : lam = 2 ∨ lam = 3) {b : Fin Tag.E8.rank → ZMod 5}
    {ω : List (Fin Tag.E8.rank)} (hω : pAct ω b = lam • b) :
    ∃ (ω₀ : List (Fin Tag.E8.rank)) (Θ : (Fin 3 → ZMod 5) →+ (Fin Tag.E8.rank → ZMod 5)),
      Function.Injective Θ ∧ pAct ω₀ b = lam • b ∧ ∀ c, pAct ω₀ (Θ c) = lam • Θ c := by
  have hN := normZ_eq_zero_of_pAct hlam hω
  obtain ⟨r, hrmem, σ, hk⟩ := hcover b
  have hNr : normZ (vecP (τ := .E8) 5 r) = 0 := by rw [← normZ_pAct σ, hk, hN]
  have hcov := (e8FiveFourCheck_spec hchk).2 r hrmem
  simp only [repCovered, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, List.any_eq_true,
    beq_iff_eq] at hcov
  obtain ⟨e, he, her, helam⟩ : ∃ e ∈ entries, e.rep = r ∧ (e.lam : ZMod 5) = lam := by
    rcases hcov with hc | ⟨⟨e2, he2, hr2, hl2⟩, ⟨e3, he3, hr3, hl3⟩⟩
    · exfalso
      refine hc ?_
      have h1 : (normL r : ZMod 5) = 0 := by rw [normL_cast, hNr]
      rw [ZMod.natCast_eq_zero_iff] at h1
      exact Nat.eq_zero_of_dvd_of_lt h1 (normL_lt r)
    · rcases hlam with rfl | rfl
      · exact ⟨e2, he2, hr2, by rw [hl2]; rfl⟩
      · exact ⟨e3, he3, hr3, by rw [hl3]; rfl⟩
  obtain ⟨-, hrep, hbasis⟩ := entryOK_spec ((e8FiveFourCheck_spec hchk).1 e he)
  rw [her, helam] at hrep
  set ωr : List (Fin Tag.E8.rank) := toFinWord3 e.word with hωr
  set E : Fin 3 → Fin Tag.E8.rank → ZMod 5 := fun i => vecP (τ := .E8) 5 (e.basis.getD i [])
    with hE
  have hEact : ∀ i, pAct ωr (E i) = lam • E i := fun i => by
    rw [← helam]
    exact (hbasis i).1
  let comb : (Fin 3 → ZMod 5) →+ (Fin Tag.E8.rank → ZMod 5) :=
    { toFun := fun c => ∑ i, c i • E i
      map_zero' := by simp
      map_add' := fun c c' => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] }
  refine ⟨σ ++ ωr ++ σ.reverse, (pActHom σ).comp comb, ?_, ?_, fun c => ?_⟩
  · intro c c' hcc
    have h1 : comb c = comb c' := pAct_injective σ hcc
    funext j
    obtain ⟨hj, hjv⟩ := (hbasis j).2 j
    have key : ∀ d : Fin 3 → ZMod 5, comb d ⟨e.piv.getD j 0, hj⟩ = d j := by
      intro d
      change (∑ i, d i • E i) ⟨e.piv.getD j 0, hj⟩ = d j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp only [Pi.smul_apply, smul_eq_mul, hE, hjv, if_true, mul_one]
      · intro i _ hij
        obtain ⟨hj', hjv'⟩ := (hbasis i).2 j
        simp only [Pi.smul_apply, smul_eq_mul, hE, hjv', if_neg hij, mul_zero]
      · simp
    rw [← key c, ← key c', h1]
  · rw [pAct_append, pAct_append, ← hk, pAct_reverse_pAct, hrep, pAct_smul]
  · change pAct (σ ++ ωr ++ σ.reverse) (pAct σ (comb c)) = lam • pAct σ (comb c)
    rw [pAct_append, pAct_append, pAct_reverse_pAct, ← pAct_smul]
    refine congrArg (pAct σ) ?_
    change pActHom ωr (∑ i, c i • E i) = lam • ∑ i, c i • E i
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change pAct ωr (c i • E i) = _
    rw [pAct_smul, hEact, smul_comm]

end CFSG.LocalAnalysis.RankFourTheoremC.E8FiveFour
