module

public import CFSG.RankThree.PartOne.KGD.D4Weyl
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (charVal charVal_single)
open scoped Matrix

theorem exists_charColumn {τ : Tag} {L : Type} [Field L] {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    ∃ (ζ : Lˣ) (e : Fin τ.rank → ℕ), orderOf ζ = p ∧ (∀ i, a i = ζ ^ e i) ∧
      (fun i => (e i : ZMod p)) ≠ 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    exact ha1 (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  have hord0 : orderOf (a i0) = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hap i0)) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hi0
    · exact h
  have hprim : IsPrimitiveRoot ((a i0 : Lˣ) : L) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hord0)
  have hexp : ∀ i, ∃ n : ℕ, a i = (a i0) ^ n := fun i => by
    have hi : ((a i : Lˣ) : L) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hap i, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
    exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩
  choose e he using hexp
  refine ⟨a i0, e, hord0, he, ?_⟩
  intro hz
  apply ha1
  funext i
  have h1 : (e i : ZMod p) = 0 := congrFun hz i
  rw [he i]
  have : p ∣ e i := (ZMod.natCast_eq_zero_iff _ _).1 h1
  obtain ⟨m, hm⟩ := this
  rw [hm, pow_mul, ← hord0, pow_orderOf_eq_one, one_pow]
  rfl

theorem rootCharStabilizer_subset_closure_of_dual {τ : Tag} {L : Type} [Field L] {p : ℕ}
    {ζ : Lˣ} (hζ : orderOf ζ = p) {a : Fin τ.rank → Lˣ} {e : Fin τ.rank → ℕ}
    (he : ∀ i, a i = ζ ^ e i)
    (hdual : dualWeylStabilizer (fun i => (e i : ZMod p)) ≤ Subgroup.closure
      {s | ∃ α ∈ rootKernel (fun i => (e i : ZMod p)), s = rootReflection α}) :
    rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)) := by
  intro w hw
  have hmem : w ∈ dualWeylStabilizer (fun i => (e i : ZMod p)) := fun y =>
    (rootChar_eq_rootChar_iff hζ e a he (w • y) y).1 (hw y)
  have hmem' := hdual hmem
  have hker' : rootKernel (fun i => (e i : ZMod p)) = rootCharKernel a := by
    ext α
    have h := rootChar_eq_rootChar_iff hζ e a he α 0
    rw [rootChar_zero] at h
    have h0 : charVal (fun i => (e i : ZMod p)) (0 : Fin τ.rank → ℤ) = 0 := by simp [charVal]
    rw [h0] at h
    exact and_congr_right fun _ => h.symm
  rw [hker'] at hmem'
  exact hmem'

def d4MnRootL : List (List ℤ) :=
  [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [1, 0, 1, 0],
    [0, -1, 0, 0], [0, 1, 1, 0], [0, 0, -1, 0], [0, 0, 1, 1], [0, 0, 0, -1], [-1, 0, -1, 0],
    [1, 1, 1, 0], [1, 0, 1, 1], [0, -1, -1, 0], [0, 1, 1, 1], [0, 0, -1, -1], [-1, -1, -1, 0],
    [-1, 0, -1, -1], [1, 1, 1, 1], [0, -1, -1, -1], [-1, -1, -1, -1], [1, 1, 2, 1],
    [-1, -1, -2, -1]]

def d4MnVec (k : Fin 24) : Fin 4 → ℤ := fun i => (d4MnRootL.getD k []).getD i 0

def d4MnRootVec (k : Fin 24) : Fin 4 → ℤ := d4RootVec k

theorem d4MnVec_apply : ∀ (k : Fin 24) (i : Fin 4), d4MnVec k i = d4MnRootVec k i := by
  decide +kernel

theorem d4MnVec_eq (k : Fin 24) : d4MnVec k = d4RootVec k :=
  funext (d4MnVec_apply k)

def d4MnMat (e : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => d4MnVec (d4Dig j (d4TupCode e)) i

theorem d4MnMat_eq (e : ℕ) : d4MnMat e = d4Mat e :=
  funext fun _ => funext fun _ => d4MnVec_apply _ _

def d4MnGram : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 0, -1, 0; 0, 2, -1, 0; -1, -1, 2, -1; 0, 0, -1, 2]

def d4MnRefl (α : Fin 4 → ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => (if i = j then 1 else 0) -
    α i * (α 0 * d4MnGram 0 j + α 1 * d4MnGram 1 j + α 2 * d4MnGram 2 j + α 3 * d4MnGram 3 j)

def d4MnMul (A B : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j

theorem d4MnMul_eq (A B : Matrix (Fin 4) (Fin 4) ℤ) : d4MnMul A B = A * B := by
  ext i j
  simp [d4MnMul, Matrix.mul_apply, Fin.sum_univ_four]

def d4MnWordMat : List (Fin 24) → Matrix (Fin 4) (Fin 4) ℤ
  | [] => 1
  | k :: l => d4MnMul (d4MnRefl (d4MnVec k)) (d4MnWordMat l)

def d4MnWords : ℕ → List (Fin 24) → List (List (Fin 24))
  | 0, _ => [[]]
  | n + 1, K => [] :: K.flatMap fun k => (d4MnWords n K).map (k :: ·)

def d4MnDot (x z : Fin 4 → ℤ) : ℤ := x 0 * z 0 + x 1 * z 1 + x 2 * z 2 + x 3 * z 3

def d4MnColZ (ε δ : ZMod 3) : Fin 4 → ℤ := ![(ε.val : ℤ), ε.val, δ.val, ε.val]

def d4MnKerIdx (z : Fin 4 → ℤ) : List (Fin 24) :=
  (List.finRange 24).filter fun k =>
    d4MnDot (d4MnVec k) z % 3 = 0 ∧ 0 < d4MnDot (d4MnVec k) (fun _ => 1)

theorem d4Mn_stab_check :
    ∀ ε δ : ZMod 3, (ε ≠ 0 ∨ δ ≠ 0) →
    ∀ e ∈ d4WeylTab, (∀ j : Fin 4,
        (d4MnDot (fun i => d4MnMat e i j) (d4MnColZ ε δ) - d4MnColZ ε δ j) % 3 = 0) →
      ∃ l ∈ d4MnWords 3 (d4MnKerIdx (d4MnColZ ε δ)), d4MnWordMat l = d4MnMat e := by
  decide +kernel

theorem d4MnGram_apply (k j : Fin 4) : Tag.D4.symmetrizedCartan k j = d4MnGram k j := by
  fin_cases k <;> fin_cases j <;> decide

theorem d4MnRefl_mulVec (α v : Fin 4 → ℤ) :
    d4MnRefl α *ᵥ v = v - iform (τ := Tag.D4) α v • α := by
  funext i
  have h1 : iform (τ := Tag.D4) α v = ∑ k : Fin 4, ∑ j : Fin 4, α k * d4MnGram k j * v j := by
    unfold iform
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (fun t => α k * t * v j) (d4MnGram_apply k j)
  rw [h1]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, d4MnRefl, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> simp [d4MnGram] <;> ring

theorem symmetrizer_D4_diag (j : Fin Tag.D4.rank) : Tag.D4.symmetrizer j j = 1 := by
  fin_cases j <;> simp [Tag.symmetrizer]

theorem corootPair_D4
    {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) (v : Fin Tag.D4.rank → ℤ) :
    corootPair α v = iform α v := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  rw [corootPair, hj, symmetrizer_D4_diag]
  simp

theorem rootReflection_smul_D4
    {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) (v : Fin Tag.D4.rank → ℤ) :
    rootReflection α • v = d4MnRefl α *ᵥ v := by
  rw [rootReflection_smul hα, corootPair_D4 hα]
  exact (d4MnRefl_mulVec α v).symm

theorem mem_of_mem_d4MnWords {K : List (Fin 24)} {n : ℕ} {l : List (Fin 24)}
    (hl : l ∈ d4MnWords n K) {k : Fin 24} (hk : k ∈ l) : k ∈ K := by
  induction n generalizing l with
  | zero =>
    simp only [d4MnWords, List.mem_singleton] at hl
    subst hl
    simp at hk
  | succ n ih =>
    simp only [d4MnWords, List.mem_cons, List.mem_flatMap, List.mem_map] at hl
    rcases hl with rfl | ⟨k', hk', l', hl', rfl⟩
    · simp at hk
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact hk'
      · exact ih hl' hk

theorem prod_rootReflection_smul_D4
    (l : List (Fin 24)) (v : Fin Tag.D4.rank → ℤ) :
    ((l.map fun k => rootReflection (d4RootVec k)).prod : WeylGroup Tag.D4) • v =
      d4MnWordMat l *ᵥ v := by
  induction l generalizing v with
  | nil => exact (Matrix.one_mulVec v).symm
  | cons k l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih v]
    refine (rootReflection_smul_D4 (isRoot_d4RootVec k) _).trans ?_
    have e1 : d4MnWordMat (k :: l) = d4MnRefl (d4RootVec k) * d4MnWordMat l := by
      rw [d4MnWordMat, d4MnMul_eq, d4MnVec_eq]
    rw [e1]
    exact Matrix.mulVec_mulVec (m := Fin 4) (n := Fin 4) (o := Fin 4) v
      (d4MnRefl (d4RootVec k)) (d4MnWordMat l)

@[expose] def d4MnCol (ε δ : ZMod 3) : Fin Tag.D4.rank → ZMod 3 := ![ε, ε, δ, ε]

theorem d4MnCol_eq (ε δ : ZMod 3) (i : Fin 4) :
    (![ε, ε, δ, ε] : Fin 4 → ZMod 3) i = ((d4MnColZ ε δ i : ℤ) : ZMod 3) := by
  fin_cases i <;> simp [d4MnColZ]

theorem charVal_d4MnCol (ε δ : ZMod 3) (x : Fin Tag.D4.rank → ℤ) :
    charVal (d4MnCol ε δ) x = ((d4MnDot x (d4MnColZ ε δ) : ℤ) : ZMod 3) := by
  show ∑ i : Fin 4, ((x i : ℤ) : ZMod 3) * (![ε, ε, δ, ε] : Fin 4 → ZMod 3) i = _
  simp [Fin.sum_univ_four, d4MnDot, d4MnColZ]

theorem intCast_zmod3_eq_zero_iff (n : ℤ) : ((n : ℤ) : ZMod 3) = 0 ↔ n % 3 = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast h)
  · intro h
    exact_mod_cast Int.dvd_of_emod_eq_zero h

theorem d4_dualWeylStabilizer_three
    (ε δ : ZMod 3) (h : ε ≠ 0 ∨ δ ≠ 0) :
    dualWeylStabilizer (τ := Tag.D4) (d4MnCol ε δ) ≤ Subgroup.closure
      {s | ∃ α ∈ rootKernel (τ := Tag.D4) (d4MnCol ε δ), s = rootReflection α} := by
  intro w hw
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab w
  have hM := smul_eq_d4Mat_mulVec w hwe
  have hcol : ∀ j : Fin Tag.D4.rank,
      (d4MnDot (fun i => d4MnMat e i j) (d4MnColZ ε δ) - d4MnColZ ε δ j) % 3 = 0 := fun j => by
    have h1 := hw (Pi.single j 1)
    rw [hM, charVal_single] at h1
    have h2 : charVal (d4MnCol ε δ) (fun i => d4Mat e i j) = d4MnCol ε δ j := by
      rw [← h1]
      congr 1
      funext i
      simp
    rw [charVal_d4MnCol, show d4MnCol ε δ j = _ from d4MnCol_eq ε δ j] at h2
    refine (intCast_zmod3_eq_zero_iff _).1 ?_
    rw [Int.cast_sub, sub_eq_zero, d4MnMat_eq]
    exact h2
  obtain ⟨l, hl, hlM⟩ := d4Mn_stab_check ε δ h e he hcol
  have hw' : w = (l.map fun k => rootReflection (d4RootVec k)).prod := by
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.D4.rank → ℤ) fun v => ?_
    rw [hM, prod_rootReflection_smul_D4, hlM, d4MnMat_eq]
    rfl
  rw [hw']
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  have hk' := mem_of_mem_d4MnWords hl hk
  refine Subgroup.subset_closure ⟨d4RootVec k, ⟨isRoot_d4RootVec k, ?_⟩, rfl⟩
  have hk2 : d4MnDot (d4MnVec k) (d4MnColZ ε δ) % 3 = 0 := by
    have := (List.mem_filter.1 hk').2
    simp only [decide_eq_true_eq] at this
    exact this.1
  rw [charVal_d4MnCol, ← d4MnVec_eq k]
  exact (intCast_zmod3_eq_zero_iff _).2 hk2

theorem d4MnCol_zero : d4MnCol 0 0 = 0 := by
  funext i
  fin_cases i <;> rfl

theorem d4MnCol_eq_of_perm {e : Fin 4 → ℕ} (h1 : (e 1 : ZMod 3) = e 0)
    (h3 : (e 3 : ZMod 3) = e 0) :
    (fun i : Fin 4 => (e i : ZMod 3)) = ![(e 0 : ZMod 3), e 0, e 2, e 0] := by
  funext i
  fin_cases i <;> simp [h1, h3]

theorem d4_stab_three {L : Type}
    [Field L] {a : Fin TwistTag.D4.tag.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1) (ha1 : a ≠ 1)
    (hρ : ∀ i, a (TwistTag.D4.perm i) = a i) :
    rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup TwistTag.D4.tag)) := by
  obtain ⟨ζ, e, hζ, he, hz0⟩ := exists_charColumn Nat.prime_three hap ha1
  have hmod : ∀ i, ((e (TwistTag.D4.perm i) : ℕ) : ZMod 3) = (e i : ZMod 3) := fun i => by
    have h1 : ζ ^ e (TwistTag.D4.perm i) = ζ ^ e i := by rw [← he, ← he, hρ]
    rw [pow_eq_pow_iff_modEq, hζ] at h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
  have h1 : ((e (1 : Fin 4) : ℕ) : ZMod 3) = e (0 : Fin 4) := hmod (0 : Fin 4)
  have h3 : ((e (3 : Fin 4) : ℕ) : ZMod 3) = e (0 : Fin 4) := (hmod (1 : Fin 4)).trans h1
  have hz : (fun i => (e i : ZMod 3)) = d4MnCol (e (0 : Fin 4)) (e (2 : Fin 4)) :=
    d4MnCol_eq_of_perm (e := e) h1 h3
  have hεδ : ((e (0 : Fin 4) : ℕ) : ZMod 3) ≠ 0 ∨ ((e (2 : Fin 4) : ℕ) : ZMod 3) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply hz0
    rw [hz, hcon.1, hcon.2, d4MnCol_zero]
    rfl
  refine rootCharStabilizer_subset_closure_of_dual hζ he ?_
  rw [hz]
  exact d4_dualWeylStabilizer_three _ _ hεδ

theorem d4_stab_three_shape
    {L : Type} [Field L] {A b : Lˣ} (hA3 : A ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : A ≠ 1 ∨ b ≠ 1) :
    rootCharStabilizer (τ := TwistTag.D4.tag) ![A, A, b, A] ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel (τ := TwistTag.D4.tag) ![A, A, b, A],
        s = rootReflection α} : Set (WeylGroup TwistTag.D4.tag)) := by
  have hap : ∀ i : Fin 4, (![A, A, b, A] : Fin 4 → Lˣ) i ^ 3 = 1 := fun i => by
    fin_cases i <;> simp [hA3, hb3]
  have hρ : ∀ i : Fin 4, (![A, A, b, A] : Fin 4 → Lˣ) (TwistTag.D4.perm i) =
      (![A, A, b, A] : Fin 4 → Lˣ) i := fun i => by
    fin_cases i <;> rfl
  have ha1 : (![A, A, b, A] : Fin 4 → Lˣ) ≠ 1 := fun h =>
    hab.elim (fun hA => hA (by simpa using congrFun h 0))
      (fun hb => hb (by simpa using congrFun h 2))
  exact d4_stab_three (a := ![A, A, b, A]) hap ha1 hρ

theorem d4_stab_three_A2 {L : Type}
    [Field L] {A : Lˣ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    rootCharStabilizer (τ := TwistTag.D4.tag) ![A, A, 1, A] ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel (τ := TwistTag.D4.tag) ![A, A, 1, A],
        s = rootReflection α} : Set (WeylGroup TwistTag.D4.tag)) :=
  d4_stab_three_shape hA3 (one_pow 3) (Or.inl hA1)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
