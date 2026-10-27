module

public import Certificates.Data.Kernel.MathieuAut.InAutK

public section

namespace CFSG.KS.MathieuAut

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

theorem testBit_orMask (v : ℕ) : ∀ l : List ℕ, (orMask l).testBit v = decide (v ∈ l)
  | [] => by simp [orMask]
  | x :: xs => by
    rw [orMask, Nat.testBit_or, Nat.testBit_two_pow, testBit_orMask v xs]
    by_cases h : v = x
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem orMask_eq_iff (l : List ℕ) : orMask l = 2 ^ 24 - 1 ↔ ∀ v, v ∈ l ↔ v < 24 := by
  constructor
  · intro h v
    have := testBit_orMask v l
    rw [h, Nat.testBit_two_pow_sub_one] at this
    exact (decide_eq_decide.1 this).symm
  · intro h
    apply Nat.eq_of_testBit_eq
    intro v
    rw [testBit_orMask, Nat.testBit_two_pow_sub_one]
    exact decide_eq_decide.2 (h v)

theorem mem_toList_iff {a : Array ℕ} (ha : a.size = 24) (v : ℕ) :
    v ∈ a.toList ↔ ∃ i < 24, a[i]! = v := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Array.length_toList] at hi
    exact ⟨i, by omega, by rw [getElem!_pos a i hi, Array.getElem_toList]⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < a.size := by omega
    exact ⟨i, by rwa [Array.length_toList], by rw [getElem!_pos a i hi', Array.getElem_toList]⟩

theorem permCols_eq {a : Array ℕ} (ha : a.size = 24) : permCols a = a.toList.map (2 ^ ·) := by
  apply List.ext_getElem
  · simp [permCols, ha]
  · intro i h1 _
    have hi : i < a.size := by
      simp only [permCols, List.length_map, List.length_range] at h1
      omega
    simp only [permCols, List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [getElem!_pos a i hi]

theorem autFwd_iff {a : Array ℕ} (ha : a.size = 24) :
    autFwd (a.toList.map (2 ^ ·)) = true ↔ ∀ i < 12, syndM (permM a (Bmask i)) = 0 := by
  simp only [autFwd, permM, ← permCols_eq ha, List.all_eq_true, List.mem_range, beq_iff_eq]

theorem autArrOK_iff {a b : Array ℕ} : autArrOK a b = true ↔
    (∀ i < 12, syndM (permM a (Bmask i)) = 0) ∧ ∀ i < 12, syndM (permM b (Bmask i)) = 0 := by
  simp only [autArrOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun h => ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩,
    fun h i hi => ⟨h.1 i hi, h.2 i hi⟩⟩

theorem getElem!_set!_ne (b : Array ℕ) {i k : ℕ} (v : ℕ) (h : i ≠ k) :
    (b.set! i v)[k]! = b[k]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hk : k < b.size
  · rw [getElem!_pos _ k (by simpa using hk), getElem!_pos b k hk,
      Array.getElem_setIfInBounds hk, if_neg h]
  · rw [getElem!_neg _ k (by simpa using hk), getElem!_neg b k hk]

theorem getElem!_set!_self (b : Array ℕ) {i : ℕ} (v : ℕ) (h : i < b.size) :
    (b.set! i v)[i]! = v := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ i (by simpa using h),
    Array.getElem_setIfInBounds h, if_pos rfl]

theorem size_foldl_set (f : ℕ → ℕ) : ∀ (L : List ℕ) (b : Array ℕ),
    (L.foldl (fun b i => b.set! (f i) i) b).size = b.size
  | [], _ => rfl
  | x :: xs, b => by
    rw [List.foldl_cons, size_foldl_set f xs, Array.size_set!]

theorem foldl_set_of_forall_ne (f : ℕ → ℕ) (k : ℕ) : ∀ (L : List ℕ) (b : Array ℕ),
    (∀ j ∈ L, f j ≠ k) → (L.foldl (fun b i => b.set! (f i) i) b)[k]! = b[k]!
  | [], _, _ => rfl
  | x :: xs, b, h => by
    rw [List.foldl_cons,
      foldl_set_of_forall_ne f k xs _ fun j hj => h j (List.mem_cons_of_mem x hj)]
    exact getElem!_set!_ne b x (h x List.mem_cons_self)

theorem foldl_set_self (f : ℕ → ℕ) : ∀ (L : List ℕ) (b : Array ℕ),
    (∀ i ∈ L, f i < b.size) → (∀ i ∈ L, ∀ j ∈ L, f i = f j → i = j) →
    ∀ i ∈ L, (L.foldl (fun b i => b.set! (f i) i) b)[f i]! = i
  | [], _, _, _, i, hi => by simp at hi
  | x :: xs, b, hlt, hinj, i, hi => by
    rw [List.foldl_cons]
    by_cases hxs : i ∈ xs
    · refine foldl_set_self f xs _ (fun j hj => ?_)
        (fun j hj k hk => hinj j (List.mem_cons_of_mem x hj) k (List.mem_cons_of_mem x hk)) i hxs
      rw [Array.size_set!]
      exact hlt j (List.mem_cons_of_mem x hj)
    · have hix : i = x := by simpa [hxs] using hi
      subst hix
      rw [foldl_set_of_forall_ne f (f i) xs _ fun j hj e =>
        hxs (by rwa [← hinj j (List.mem_cons_of_mem i hj) i List.mem_cons_self e])]
      exact getElem!_set!_self b i (hlt i List.mem_cons_self)

theorem invArr_getElem {a : Array ℕ} (hlt : ∀ i < 24, a[i]! < 24)
    (hinj : ∀ i < 24, ∀ j < 24, a[i]! = a[j]! → i = j) (i : ℕ) (hi : i < 24) :
    (invArr a)[a[i]!]! = i :=
  foldl_set_self (fun i => a[i]!) (List.range 24) _
    (fun j hj => by simpa using hlt j (List.mem_range.1 hj))
    (fun j hj k hk e => hinj j (List.mem_range.1 hj) k (List.mem_range.1 hk) e) i
    (List.mem_range.2 hi)

theorem invPairOK_invArr_iff {a : Array ℕ} :
    InvPairOK 24 a (invArr a) = true ↔
      (∀ i < 24, a[i]! < 24) ∧ ∀ v < 24, ∃ i < 24, a[i]! = v := by
  constructor
  · intro h
    exact ⟨fun i hi => (invPairOK_spec h i hi).1,
      fun v hv => ⟨(invArr a)[v]!, (invPairOK_spec h v hv).2.1, (invPairOK_spec h v hv).2.2.1⟩⟩
  · rintro ⟨hlt, hsurj⟩
    let g : Fin 24 → Fin 24 := fun i => ⟨a[(i : ℕ)]!, hlt i i.2⟩
    have hg : Function.Surjective g := fun v => by
      obtain ⟨i, hi, e⟩ := hsurj v v.2
      exact ⟨⟨i, hi⟩, Fin.ext e⟩
    have hgi := Finite.injective_iff_surjective.2 hg
    have hinj : ∀ i < 24, ∀ j < 24, a[i]! = a[j]! → i = j := fun i hi j hj e =>
      congrArg Fin.val (@hgi ⟨i, hi⟩ ⟨j, hj⟩ (Fin.ext e))
    unfold InvPairOK
    rw [List.all_eq_true]
    intro v hv
    have hv' := List.mem_range.1 hv
    obtain ⟨i, hi, hiv⟩ := hsurj v hv'
    have hbv : (invArr a)[v]! = i := by
      rw [← hiv]
      exact invArr_getElem hlt hinj i hi
    simp [hbv, invArr_getElem hlt hinj v hv', hiv, hlt v hv', hi]

theorem bwd_of_fwd {a b : Array ℕ} (h : InvPairOK 24 a b = true)
    (hf : ∀ i < 12, syndM (permM a (Bmask i)) = 0) :
    ∀ i < 12, syndM (permM b (Bmask i)) = 0 := by
  set σ := permOfArr 24 a b h
  have hB : ∀ i : Fin 12, B i ∘ ⇑σ⁻¹ ∈ C := fun i => by
    have e : B i ∘ ⇑σ⁻¹ = permWord σ (B i) := rfl
    rw [e, B_eq_bvec, permWord_bvec (hasArr_permOfArr h), bvec_mem_C_iff]
    exact hf i i.2
  have hC : ∀ x ∈ C, x ∘ ⇑σ⁻¹ ∈ C := fun x hx => by
    rw [eq_comb_of_mem_C hx]
    have e : (∑ i, ψ x i • B i) ∘ ⇑σ⁻¹ = ∑ i, ψ x i • (B i ∘ ⇑σ⁻¹) := by
      funext j
      simp [Finset.sum_apply]
    rw [e]
    exact C.sum_mem fun i _ => C.smul_mem _ (hB i)
  let f : C → C := fun x => ⟨x.1 ∘ ⇑σ⁻¹, hC x.1 x.2⟩
  have hfi : Function.Injective f := fun x y e => by
    apply Subtype.ext
    funext k
    have := congrFun (congrArg Subtype.val e) (σ k)
    simpa [f] using this
  have hfs := Finite.injective_iff_surjective.1 hfi
  have hC' : ∀ x ∈ C, x ∘ ⇑σ ∈ C := fun x hx => by
    obtain ⟨y, hy⟩ := hfs ⟨x, hx⟩
    have e : x ∘ ⇑σ = y.1 := by
      have hy' : y.1 ∘ ⇑σ⁻¹ = x := congrArg Subtype.val hy
      rw [← hy']
      funext k
      simp
    rw [e]
    exact y.2
  intro i hi
  have e : B ⟨i, hi⟩ ∘ ⇑σ = permWord σ⁻¹ (B ⟨i, hi⟩) := by
    funext k
    simp [permWord]
  have h2 := hC' _ (B_mem_C ⟨i, hi⟩)
  rw [e, B_eq_bvec, permWord_bvec (hasArr_permOfArr_inv h), bvec_mem_C_iff] at h2
  exact h2

theorem inAutKL_iff {a : Array ℕ} (ha : a.size = 24) :
    inAutKL a.toList = true ↔
      ((∀ i < 24, a[i]! < 24) ∧ ∀ v < 24, ∃ i < 24, a[i]! = v) ∧
        ∀ i < 12, syndM (permM a (Bmask i)) = 0 := by
  have hlen : a.toList.length = 24 := by rw [Array.length_toList, ha]
  have hall : (a.toList.all fun x => decide (x < 24)) = true ↔ ∀ i < 24, a[i]! < 24 := by
    rw [List.all_eq_true]
    constructor
    · intro h i hi
      exact of_decide_eq_true (h _ ((mem_toList_iff ha _).2 ⟨i, hi, rfl⟩))
    · intro h x hx
      obtain ⟨i, hi, rfl⟩ := (mem_toList_iff ha x).1 hx
      exact decide_eq_true (h i hi)
  simp only [inAutKL, Bool.and_eq_true, beq_iff_eq]
  rw [hall, orMask_eq_iff, autFwd_iff ha]
  constructor
  · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
    exact ⟨⟨h1, fun v hv => (mem_toList_iff ha v).1 ((h2 v).2 hv)⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨⟨hlen, h1⟩, fun v => ⟨fun hv => ?_, fun hv => (mem_toList_iff ha v).2 (h2 v hv)⟩⟩,
      h3⟩
    obtain ⟨i, hi, rfl⟩ := (mem_toList_iff ha v).1 hv
    exact h1 i hi

theorem inAutOK_eq_K (a : Array ℕ) : inAutOK a = inAutK a := by
  rw [inAutK]
  split_ifs with ha
  · rw [Bool.eq_iff_iff, inAutKL_iff ha, inAutOK, Bool.and_eq_true, invPairOK_invArr_iff,
      autArrOK_iff]
    constructor
    · rintro ⟨hp, hf, -⟩
      exact ⟨hp, hf⟩
    · rintro ⟨hp, hf⟩
      exact ⟨hp, hf, bwd_of_fwd (invPairOK_invArr_iff.2 hp) hf⟩
  · rfl

end CFSG.KS.MathieuAut

end
