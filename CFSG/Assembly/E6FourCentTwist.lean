module

public import CFSG.Assembly.E6FourCentRoots

public section

namespace CFSG.Assembly

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.E6FourCentChk
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Matrix


private theorem testBit_lt_of_lt {c : ℕ} (hc : c < 2 ^ 72) {k : ℕ} (h : c.testBit k = true) :
    k < 72 := by
  have hge : 2 ^ k ≤ c := Nat.ge_two_pow_of_testBit h
  have hlt : 2 ^ k < 2 ^ 72 := lt_of_le_of_lt hge hc
  exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hlt

private theorem mem_rootsOf {c : ℕ} {g : List ℤ} :
    g ∈ rootsOf c ↔ ∃ k, k < 72 ∧ c.testBit k = true ∧ rt k = g := by
  rw [rootsOf, List.mem_map]
  constructor
  · rintro ⟨k, hk, hkg⟩
    rw [List.mem_filter, List.mem_range] at hk
    exact ⟨k, hk.1, hk.2, hkg⟩
  · rintro ⟨k, hk, hbit, hkg⟩
    exact ⟨k, by rw [List.mem_filter, List.mem_range]; exact ⟨hk, hbit⟩, hkg⟩

private theorem zipWith_sub_ofFn {n : ℕ} (x y : Fin n → ℤ) :
    List.zipWith (· - ·) (List.ofFn x) (List.ofFn y) = List.ofFn (x - y) := by
  apply List.ext_getElem
  · simp [List.length_zipWith]
  · intro i hi _
    rw [List.getElem_zipWith, List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
    simp [Pi.sub_apply]

private theorem zipWith_add_ofFn {n : ℕ} (x y : Fin n → ℤ) :
    List.zipWith (· + ·) (List.ofFn x) (List.ofFn y) = List.ofFn (x + y) := by
  apply List.ext_getElem
  · simp [List.length_zipWith]
  · intro i hi _
    rw [List.getElem_zipWith, List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
    simp [Pi.add_apply]

private theorem ofFn_sub_smul (c : ℤ) (β v : Fin Tag.E6.rank → ℤ) :
    vsub (List.ofFn v) ((List.ofFn β).map (fun t => c * t)) = List.ofFn (v - c • β) := by
  rw [vsub, List.map_ofFn, zipWith_sub_ofFn, List.ofFn_injective.eq_iff]
  funext i
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

private theorem rootReflection_smul_E6 {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (v : Fin Tag.E6.rank → ℤ) :
    rootReflection β • v = v - iform v β • β := by
  rw [rootReflection_smul hβ, corootPair]
  have h2 : iform β β = 2 := by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hβ
    simpa [Tag.symmetrizer] using hj
  rw [h2, Int.mul_ediv_cancel_left _ two_ne_zero, iform_comm β v]

private theorem weyl_smul_zsmul (w : WeylGroup Tag.E6) (c : ℤ) (z : Fin Tag.E6.rank → ℤ) :
    w • (c • z) = c • (w • z) := by
  rw [smul_def, smul_def, map_smul]

private theorem wAct_cons (b : List ℤ) (bs : List (List ℤ)) (x : List ℤ) :
    wAct (b :: bs) x = wAct bs (vsub x (b.map fun t => iformI x b * t)) := rfl

private theorem wAct_ofFn (l : List (Fin Tag.E6.rank → ℤ))
    (hl : ∀ β ∈ l, IsRoot Tag.E6 β) (v : Fin Tag.E6.rank → ℤ) :
    wAct (l.map List.ofFn) (List.ofFn v) =
      List.ofFn (List.foldl (fun y β => rootReflection β • y) v l) := by
  induction l generalizing v with
  | nil => rfl
  | cons β l ih =>
    have hβ : IsRoot Tag.E6 β := hl β (by simp)
    rw [List.map_cons, wAct_cons, ofFn_sub_smul (iformI (List.ofFn v) (List.ofFn β)) β v,
      iformI_ofFn v β, ← rootReflection_smul_E6 hβ v, List.foldl_cons]
    exact ih (fun γ hγ => hl γ (List.mem_cons_of_mem β hγ)) (rootReflection β • v)

private theorem a5Valid_conj {e : A5Cert} (h : a5Valid e = true) :
    (Nat.testBit e.c e.b1 = true ∧ Nat.testBit e.c e.b2 = true ∧
      Nat.testBit e.c e.b3 = true) ∧
    (rootsOf e.c).all (fun g => mulVecI matLit g == wAct [rt e.b1, rt e.b2, rt e.b3] g) =
      true := by
  have h' := h
  simp only [a5Valid, Bool.and_eq_true_iff] at h'
  tauto

private theorem a5Valid_bits {e : A5Cert} (h : a5Valid e = true) :
    Nat.testBit e.c e.b1 = true ∧ Nat.testBit e.c e.b2 = true ∧ Nat.testBit e.c e.b3 = true :=
  (a5Valid_conj h).1

private theorem a5Valid_all {e : A5Cert} (h : a5Valid e = true) :
    ∀ g ∈ rootsOf e.c, mulVecI matLit g = wAct [rt e.b1, rt e.b2, rt e.b3] g := by
  intro g hg
  have hall := (a5Valid_conj h).2
  have := List.all_eq_true.mp hall g hg
  simpa using this

private theorem a5Valid_action {e : A5Cert} (h : a5Valid e = true)
    (hb1 : e.b1 < 72) (hb2 : e.b2 < 72) (hb3 : e.b3 < 72)
    {k : ℕ} (hk : k < 72) (hbit : e.c.testBit k = true) :
    (wordMat Tag.E6 e6TwoWord) *ᵥ e6RootVec k =
      (rootReflection (e6RootVec e.b3) * rootReflection (e6RootVec e.b2) *
        rootReflection (e6RootVec e.b1)) • e6RootVec k := by
  have hfall := a5Valid_all h
  have hg : rt k ∈ rootsOf e.c := mem_rootsOf.mpr ⟨k, hk, hbit, rfl⟩
  have hkfall := hfall (rt k) hg
  rw [rt_eq_ofFn hk, mulVecI_matLit_ofFn, rt_eq_ofFn hb1, rt_eq_ofFn hb2,
    rt_eq_ofFn hb3] at hkfall
  have hl : ∀ β ∈ [e6RootVec e.b1, e6RootVec e.b2, e6RootVec e.b3], IsRoot Tag.E6 β := by
    intro β hβ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
    rcases hβ with rfl | rfl | rfl
    · exact isRoot_e6RootVec hb1
    · exact isRoot_e6RootVec hb2
    · exact isRoot_e6RootVec hb3
  rw [show ([List.ofFn (e6RootVec e.b1), List.ofFn (e6RootVec e.b2),
        List.ofFn (e6RootVec e.b3)] : List (List ℤ))
      = List.map List.ofFn [e6RootVec e.b1, e6RootVec e.b2, e6RootVec e.b3] from rfl] at hkfall
  rw [wAct_ofFn _ hl (e6RootVec k), List.ofFn_injective.eq_iff] at hkfall
  rw [show List.foldl (fun y β => rootReflection β • y) (e6RootVec k)
        [e6RootVec e.b1, e6RootVec e.b2, e6RootVec e.b3]
      = (rootReflection (e6RootVec e.b3) * rootReflection (e6RootVec e.b2) *
          rootReflection (e6RootVec e.b1)) • e6RootVec k from by
    simp only [List.foldl_cons, List.foldl_nil, mul_smul]] at hkfall
  exact hkfall

private theorem typedOK_a5 {c : ℕ} (h : typedOK c c = true) (hp : popc c = 30) :
    ∃ e ∈ a5Tab, e.c = c ∧ a5Valid e = true := by
  have h' := h
  rw [typedOK, Nat.beq_refl c, Bool.true_and] at h'
  rcases Bool.or_eq_true_iff.mp h' with hl | hr
  · rcases Bool.and_eq_true_iff.mp hl with ⟨h30, hany⟩
    rcases List.any_eq_true.mp hany with ⟨e, he, hev⟩
    have hev' : (Nat.beq e.c c && a5Valid e) = true := by simpa using hev
    rcases Bool.and_eq_true_iff.mp hev' with ⟨hec, hval⟩
    exact ⟨e, he, Nat.eq_of_beq_eq_true hec, hval⟩
  · rcases Bool.and_eq_true_iff.mp hr with ⟨h24, _⟩
    have : popc c = 24 := Nat.eq_of_beq_eq_true h24
    omega

private theorem d4Valid_conj {e : D4Cert} (h : d4Valid e = true) :
    (Nat.testBit e.c e.b1 = true ∧ Nat.testBit e.c e.b2 = true) ∧
    (rootsOf e.c).all (fun g =>
        iformI (List.zipWith (· + ·) (rt e.b1) (rt e.b2)) g % 2 == 0) = true ∧
    (vsub (mulVecI matLit (List.zipWith (· + ·) (rt e.b1) (rt e.b2)))
        (List.zipWith (· + ·) (rt e.b1) (rt e.b2))).any (fun z => z % 2 != 0) = true := by
  have h' := h
  simp only [d4Valid, Bool.and_eq_true_iff] at h'
  tauto

private theorem d4Valid_bits {e : D4Cert} (h : d4Valid e = true) :
    Nat.testBit e.c e.b1 = true ∧ Nat.testBit e.c e.b2 = true := (d4Valid_conj h).1

private theorem d4Valid_even {e : D4Cert} (h : d4Valid e = true) :
    ∀ g ∈ rootsOf e.c, iformI (List.zipWith (· + ·) (rt e.b1) (rt e.b2)) g % 2 = 0 := by
  intro g hg
  have hall := (d4Valid_conj h).2.1
  have := List.all_eq_true.mp hall g hg
  simpa using this

private theorem d4Valid_odd {e : D4Cert} (h : d4Valid e = true) :
    (vsub (mulVecI matLit (List.zipWith (· + ·) (rt e.b1) (rt e.b2)))
        (List.zipWith (· + ·) (rt e.b1) (rt e.b2))).any (fun z => z % 2 != 0) = true :=
  (d4Valid_conj h).2.2

private theorem typedOK_d4 {c : ℕ} (h : typedOK c c = true) (hp : popc c = 24) :
    ∃ e ∈ d4Tab, e.c = c ∧ d4Valid e = true := by
  have h' := h
  rw [typedOK, Nat.beq_refl c, Bool.true_and] at h'
  rcases Bool.or_eq_true_iff.mp h' with hl | hr
  · rcases Bool.and_eq_true_iff.mp hl with ⟨h30, _⟩
    have : popc c = 30 := Nat.eq_of_beq_eq_true h30
    omega
  · rcases Bool.and_eq_true_iff.mp hr with ⟨h24, hany⟩
    rcases List.any_eq_true.mp hany with ⟨e, he, hev⟩
    have hev' : (Nat.beq e.c c && d4Valid e) = true := by simpa using hev
    rcases Bool.and_eq_true_iff.mp hev' with ⟨hec, hval⟩
    exact ⟨e, he, Nat.eq_of_beq_eq_true hec, hval⟩

theorem e6Four_a5_twist {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    {c : ℕ} (hc : c < 2 ^ 72) (hp : popc c = 30) (h : typedOK c c = true) :
    twistInner (e6MaskRoots c) (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
  obtain ⟨e, _he, hec, hevalid⟩ := typedOK_a5 h hp
  rw [← hec] at hc ⊢
  have hbits := a5Valid_bits hevalid
  obtain ⟨hb1, hb2, hb3⟩ := hbits
  have hb1lt : e.b1 < 72 := testBit_lt_of_lt hc hb1
  have hb2lt : e.b2 < 72 := testBit_lt_of_lt hc hb2
  have hb3lt : e.b3 < 72 := testBit_lt_of_lt hc hb3
  refine ⟨rootReflection (e6RootVec e.b3) * rootReflection (e6RootVec e.b2) *
      rootReflection (e6RootVec e.b1), ?_, ?_⟩
  · apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact Subgroup.subset_closure ⟨e6RootVec e.b3, ⟨e.b3, hb3lt, hb3, rfl⟩, rfl⟩
      · exact Subgroup.subset_closure ⟨e6RootVec e.b2, ⟨e.b2, hb2lt, hb2, rfl⟩, rfl⟩
    · exact Subgroup.subset_closure ⟨e6RootVec e.b1, ⟨e.b1, hb1lt, hb1, rfl⟩, rfl⟩
  · intro γ hγ
    obtain ⟨k, hk, hbit, hvec⟩ := hγ
    have hk_act : ρ (e6RootVec k) =
        (rootReflection (e6RootVec e.b3) * rootReflection (e6RootVec e.b2) *
          rootReflection (e6RootVec e.b1)) • e6RootVec k :=
      (hρ (e6RootVec k) (isRoot_e6RootVec hk)).trans
        (a5Valid_action hevalid hb1lt hb2lt hb3lt hk hbit)
    rw [← hvec]
    exact hk_act

theorem e6Four_d4_twist {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    {c : ℕ} (hc : c < 2 ^ 72) (hp : popc c = 24) (h : typedOK c c = true) :
    ¬ twistInner (e6MaskRoots c) (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
  obtain ⟨e, _he, hec, hevalid⟩ := typedOK_d4 h hp
  rw [← hec] at hc ⊢
  intro ht
  obtain ⟨w, hw_mem, hw_act⟩ := ht
  have hbits := d4Valid_bits hevalid
  obtain ⟨hb1, hb2⟩ := hbits
  have hb1lt : e.b1 < 72 := testBit_lt_of_lt hc hb1
  have hb2lt : e.b2 < 72 := testBit_lt_of_lt hc hb2
  let Uv : Fin Tag.E6.rank → ℤ := e6RootVec e.b1 + e6RootVec e.b2
  have hUeq : List.zipWith (· + ·) (rt e.b1) (rt e.b2) = List.ofFn Uv := by
    rw [rt_eq_ofFn hb1lt, rt_eq_ofFn hb2lt, zipWith_add_ofFn]
  have heven : ∀ γ ∈ e6MaskRoots e.c, iform Uv γ % 2 = 0 := by
    intro γ hγ
    obtain ⟨k, hk, hbit, hvec⟩ := hγ
    have hg : rt k ∈ rootsOf e.c := mem_rootsOf.mpr ⟨k, hk, hbit, rfl⟩
    have hk' := d4Valid_even hevalid (rt k) hg
    rw [hUeq, rt_eq_ofFn hk, iformI_ofFn] at hk'
    rw [← hvec]
    exact hk'
  let P : WeylGroup Tag.E6 → Prop :=
    fun w => ∃ z : Fin Tag.E6.rank → ℤ, w • Uv = Uv + (2 : ℤ) • z
  have hPw : P w := by
    refine Subgroup.closure_induction (p := fun w _ => P w) ?_ ?_ ?_ ?_ hw_mem
    · rintro s ⟨γ, hγ, rfl⟩
      have hγroot : IsRoot Tag.E6 γ := by
        obtain ⟨k, hk, hbit, hvec⟩ := hγ
        rw [← hvec]
        exact isRoot_e6RootVec hk
      have hpar := heven γ hγ
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero hpar
      refine ⟨-(m • γ), ?_⟩
      rw [rootReflection_smul_E6 hγroot, hm, mul_smul, sub_eq_add_neg, smul_neg]
    · exact ⟨0, by simp⟩
    · rintro x y _ _ ⟨zx, hzx⟩ ⟨zy, hzy⟩
      refine ⟨zx + x • zy, ?_⟩
      rw [mul_smul, hzy, smul_add, weyl_smul_zsmul, hzx, smul_add]
      abel
    · rintro x _ ⟨zx, hzx⟩
      refine ⟨-(x⁻¹ • zx), ?_⟩
      have hh := congrArg (fun t => x⁻¹ • t) hzx
      rw [← mul_smul, inv_mul_cancel, one_smul, smul_add, weyl_smul_zsmul] at hh
      have hA : x⁻¹ • Uv = Uv - (2 : ℤ) • (x⁻¹ • zx) := (eq_sub_iff_add_eq).mpr hh.symm
      rw [hA, sub_eq_add_neg, smul_neg]
  obtain ⟨z, hz⟩ := hPw
  have hb1mem : e6RootVec e.b1 ∈ e6MaskRoots e.c := ⟨e.b1, hb1lt, hb1, rfl⟩
  have hb2mem : e6RootVec e.b2 ∈ e6MaskRoots e.c := ⟨e.b2, hb2lt, hb2, rfl⟩
  have hw1 : w • e6RootVec e.b1 = (wordMat Tag.E6 e6TwoWord) *ᵥ e6RootVec e.b1 :=
    (hw_act _ hb1mem).symm.trans (hρ _ (isRoot_e6RootVec hb1lt))
  have hw2 : w • e6RootVec e.b2 = (wordMat Tag.E6 e6TwoWord) *ᵥ e6RootVec e.b2 :=
    (hw_act _ hb2mem).symm.trans (hρ _ (isRoot_e6RootVec hb2lt))
  have hwU : w • Uv = (wordMat Tag.E6 e6TwoWord) *ᵥ Uv := by
    change w • (e6RootVec e.b1 + e6RootVec e.b2) =
      (wordMat Tag.E6 e6TwoWord) *ᵥ (e6RootVec e.b1 + e6RootVec e.b2)
    rw [smul_add, Matrix.mulVec_add, hw1, hw2]
  have hMU : (wordMat Tag.E6 e6TwoWord) *ᵥ Uv = Uv + (2 : ℤ) • z := by
    rw [← hwU]
    exact hz
  have hdiff : vsub (mulVecI matLit (List.zipWith (· + ·) (rt e.b1) (rt e.b2)))
      (List.zipWith (· + ·) (rt e.b1) (rt e.b2)) =
      List.ofFn ((wordMat Tag.E6 e6TwoWord) *ᵥ Uv - Uv) := by
    rw [hUeq, mulVecI_matLit_ofFn, vsub, zipWith_sub_ofFn]
  obtain ⟨a, ha_mem, ha_odd⟩ := List.any_eq_true.mp (d4Valid_odd hevalid)
  rw [hdiff] at ha_mem
  rw [List.mem_ofFn] at ha_mem
  obtain ⟨i, hi⟩ := ha_mem
  have hzero : a % 2 = 0 := by
    rw [← hi]
    have hcoord : ((wordMat Tag.E6 e6TwoWord) *ᵥ Uv - Uv) i = 2 * z i := by
      rw [hMU]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hcoord]
    exact Int.emod_eq_zero_of_dvd ⟨z i, by ring⟩
  exact (by simpa [hzero] using ha_odd)

end CFSG.Assembly

end
