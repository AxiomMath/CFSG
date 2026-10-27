module

public import CFSG.RankThree.PartOne.KF4.LongA2Frame
public import CFSG.RankThree.PartOne.KF4.ShortA2Frame
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompTree
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false

@[expose] def f4ExtVec : Option (Fin 4) → Fin Tag.F4.rank → ℤ
  | none => -![2, 3, 4, 2]
  | some j => Pi.single j 1

@[expose] def f4Anc : ℕ → List ℕ
  | 0 => [0, 1, 2]
  | 1 => [1, 2]
  | 2 => [2]
  | 3 => [3, 2]
  | 4 => [4, 3, 2]
  | _ => []

@[expose] def f4EdgeIdx : List (ℕ × ℕ) := [(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 4),
  (4, 3)]

@[expose] def f4Conn : List (List ℕ) :=
  [[0], [1], [2], [3], [4], [0, 1], [1, 2], [2, 3], [3, 4], [0, 1, 2], [1, 2, 3], [2, 3, 4],
   [0, 1, 2, 3], [1, 2, 3, 4], [0, 1, 2, 3, 4]]

@[expose] def f4WordLong : List (Fin Tag.F4.rank) := [1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0]

@[expose] def f4Sigma01 (a b : Fin 3) : Fin Tag.F4.rank → ℤ :=
  wordMat Tag.F4 f4WordLong *ᵥ CFSG.RankThree.E6.chainRoot f4chainLong a b

theorem kacF4_extRoot : kacF4.extRoot = f4ExtVec := by
  funext x
  cases x <;> rfl

set_option maxRecDepth 100000

theorem f4_tree : IsTreePaths (Tag.F4.rank + 1) f4EdgeIdx (treePath f4Anc) where
  self := by decide +kernel
  lt := by decide +kernel
  head := by decide +kernel
  last := by decide +kernel
  chain := by decide +kernel
  step := by decide +kernel

theorem f4_adj_raw : ∀ x y : Option (Fin 4),
    (x ≠ y ∧ iform (f4ExtVec x) (f4ExtVec y) ≠ 0) ↔ (nodeIdx x, nodeIdx y) ∈ f4EdgeIdx := by
  decide +kernel

theorem f4_adj :
    ∀ x y : Option (Fin Tag.F4.rank), kacF4.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ f4EdgeIdx := by
  intro x y
  unfold CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.Adj
  rw [kacF4_extRoot]
  exact f4_adj_raw x y

theorem f4_check : ((List.range (Tag.F4.rank + 1)).sublists.all fun zl =>
    !(fun _ : List ℕ => true) zl ||
      zl.all fun x => f4Conn.any (sameSet (compIdx (Tag.F4.rank + 1) (treePath f4Anc) zl x))) =
        true := by
  decide +kernel

theorem f4_lt : ∀ c ∈ f4Conn, ∀ w ∈ c, w < Tag.F4.rank + 1 := by
  decide +kernel

theorem f4_card : ∀ c ∈ f4Conn, (c.map (idxNode (r := Tag.F4.rank))).toFinset.card = c.length := by
  decide +kernel

theorem f4_count_raw : ∀ c ∈ f4Conn, 2 ≤ c.length →
    kacCount Tag.F4 ![2, 3, 4, 2] (c.map (idxNode (r := Tag.F4.rank))).toFinset =
      c.length * (c.length + 1) → c = [0, 1] ∨ c = [1, 2] ∨ c = [3, 4] ∨ c = [0, 1, 2] := by
  decide +kernel

@[expose] def f4θ : Fin Tag.F4.rank → ℤ := ![2, 3, 4, 2]

theorem f4_long01_roots : ∀ r ∈ Tag.F4.artifactRoots,
    kacTest f4θ {none, some 0} (toVec Tag.F4.rank r) →
      ∃ a b : Fin 3, a ≠ b ∧ r = List.ofFn (f4Sigma01 a b) := by
  decide +kernel

theorem f4_long12_roots : ∀ r ∈ Tag.F4.artifactRoots,
    kacTest f4θ {some 0, some 1} (toVec Tag.F4.rank r) →
      ∃ a b : Fin 3, a ≠ b ∧ r = List.ofFn (CFSG.RankThree.E6.chainRoot f4chainLong a b) := by
  decide +kernel

theorem f4_short_roots : ∀ r ∈ Tag.F4.artifactRoots,
    kacTest f4θ {some 2, some 3} (toVec Tag.F4.rank r) →
      ∃ a b : Fin 3, a ≠ b ∧ r = List.ofFn (f4ShortSigma a b) := by
  decide +kernel

theorem f4_long01_isRoot : ∀ a b : Fin 3, a ≠ b →
    List.ofFn (f4Sigma01 a b) ∈ Tag.F4.artifactRoots ∧
      kacTest f4θ {none, some 0} (f4Sigma01 a b) ∧
        iform (f4Sigma01 a b) (f4Sigma01 a b) = 2 * 2 := by
  decide +kernel

theorem f4_long12_isRoot : ∀ a b : Fin 3, a ≠ b →
    List.ofFn (CFSG.RankThree.E6.chainRoot f4chainLong a b) ∈ Tag.F4.artifactRoots ∧
      kacTest f4θ {some 0, some 1} (CFSG.RankThree.E6.chainRoot f4chainLong a b) ∧
        iform (CFSG.RankThree.E6.chainRoot f4chainLong a b)
          (CFSG.RankThree.E6.chainRoot f4chainLong a b) = 2 * 2 := by
  decide +kernel

theorem f4_short_isRoot : ∀ a b : Fin 3, a ≠ b →
    List.ofFn (f4ShortSigma a b) ∈ Tag.F4.artifactRoots ∧
      kacTest f4θ {some 2, some 3} (f4ShortSigma a b) ∧
        iform (f4ShortSigma a b) (f4ShortSigma a b) = 2 * 1 := by
  decide +kernel

theorem toVec_ofFn_F4 (v : Fin Tag.F4.rank → ℤ) : toVec Tag.F4.rank (List.ofFn v) = v := by
  funext i
  fin_cases i <;> rfl

theorem f4_rootsOf_eq
    {C : Finset (Option (Fin Tag.F4.rank))} (hC : ∃ x, x ∉ C)
    {σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (h1 : ∀ r ∈ Tag.F4.artifactRoots, kacTest f4θ C (toVec Tag.F4.rank r) →
      ∃ a b : Fin 3, a ≠ b ∧ r = List.ofFn (σ a b))
    (h2 : ∀ a b : Fin 3, a ≠ b →
      List.ofFn (σ a b) ∈ Tag.F4.artifactRoots ∧ kacTest f4θ C (σ a b)) :
    kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) = frameRoots σ := by
  ext γ
  rw [mem_rootsOf_iff kacF4 facts_F4 hC]
  constructor
  · rintro ⟨hγ, hk⟩
    have hmem := isRoot_iff_mem_artifactRoots.1 hγ
    obtain ⟨a, b, hab, e⟩ := h1 _ hmem (by rw [toVec_ofFn_F4]; exact hk)
    refine ⟨a, b, hab, ?_⟩
    rw [← toVec_ofFn_F4 γ, e, toVec_ofFn_F4]
  · rintro ⟨a, b, hab, rfl⟩
    obtain ⟨hr, hk⟩ := h2 a b hab
    exact ⟨isRoot_iff_mem_artifactRoots.2 hr, hk⟩

theorem not_comp_eq_longA3_F4
    {p : ℕ} (hp : p.Prime) {μ : Fin Tag.F4.rank → ℤ} (hμ : kacF4.IsNormal p μ)
    {x : Option (Fin Tag.F4.rank)}
    (hc : kacF4.comp p μ x = {y | nodeIdx y ∈ ([0, 1, 2] : List ℕ)}) : False := by
  have hmem : ∀ y : Option (Fin Tag.F4.rank), nodeIdx y ∈ ([0, 1, 2] : List ℕ) →
      kacF4.IsZ p μ y := fun y hy => by
    have : y ∈ kacF4.comp p μ x := by rw [hc]; exact hy
    exact this.1
  have hz0 : kacF4.IsZ p μ none := hmem none (by decide)
  have hz1 : kacF4.IsZ p μ (some 0) := hmem (some 0) (by decide)
  have hz2 : kacF4.IsZ p μ (some 1) := hmem (some 1) (by decide)
  have h3 : ¬ kacF4.IsZ p μ (some 2) := by
    intro h
    have hin : some 1 ∈ kacF4.comp p μ x := by rw [hc]; decide
    have hadj : kacF4.Adj (some 1) (some 2) := (f4_adj _ _).2 (by decide)
    have : some 2 ∈ kacF4.comp p μ x :=
      ⟨h, hin.2.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨hz2, h, hadj⟩)⟩
    rw [hc] at this
    exact absurd this (by decide)
  change kacF4.θ ⬝ᵥ μ = p at hz0
  change μ 0 = 0 at hz1
  change μ 1 = 0 at hz2
  change ¬ μ 2 = 0 at h3
  have hθ : kacF4.θ ⬝ᵥ μ = 2 * μ 0 + 3 * μ 1 + 4 * μ 2 + 2 * μ 3 := by
    rw [show kacF4.θ = ![2, 3, 4, 2] from rfl]
    show ∑ j : Fin 4, (![2, 3, 4, 2] : Fin 4 → ℤ) j * μ j = _
    rw [Fin.sum_univ_four]
    rfl
  have h2pos : 1 ≤ μ 2 := by
    have := hμ.1 2
    omega
  have h3nn := hμ.1 3
  rw [hθ, hz1, hz2] at hz0
  have hp2 : (2 : ℤ) ∣ p := ⟨2 * μ 2 + μ 3, by linarith⟩
  have hp2' : 2 ∣ p := by exact_mod_cast hp2
  have hp : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hp2').symm
  subst hp
  push_cast at hz0
  omega

section Frames

theorem f4_long01_frame {L : Type} [Field L] :
    IsA2Frame ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L
      ((coxeterSystem Tag.F4).wordProd f4WordLong))).toMonoidHom.comp (f4rhoLong L)) f4Sigma01 := by
  have h := (f4Long_frame (L := L)).transport ((coxeterSystem Tag.F4).wordProd f4WordLong)
  have e : (fun i j => (coxeterSystem Tag.F4).wordProd f4WordLong •
      CFSG.RankThree.E6.chainRoot f4chainLong i j) = f4Sigma01 := by
    funext i j
    rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
    rfl
  rw [e] at h
  exact h

theorem exists_frame_of_typeA_F4_T_of_prime {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.F4 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTp : rootDiagUnit Tag.F4 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL Tag.F4 L) (σ : Fin ν → Fin ν → Fin Tag.F4.rank → ℤ) (κ : ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ κ ≠ 0 ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) ∧
        componentRoots (rootCharHom a) i = frameRoots σ := by
  classical
  obtain ⟨v, μ, hμ, hall⟩ := S.exists_kacT_of_prime hp hpL facts_F4 hTp
  obtain ⟨x, hx, hi⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := kacF4.exists_comp_eq_of_check f4_tree f4_adj (adm := fun _ => true)
    f4_check rfl hx
  set C : Finset (Option (Fin Tag.F4.rank)) := (c.map (idxNode (r := Tag.F4.rank))).toFinset
    with hCdef
  have hCset : kacF4.comp p μ x = (C : Set (Option (Fin Tag.F4.rank))) := by
    rw [hcomp]
    ext y
    simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (f4_lt c hc w hw)]
      exact hw
  have hCp : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacF4 hp.pos μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hi' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) := by
    rw [hi, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hi', compRank_image, compRank_rootsOf kacF4 facts_F4 hCp, f4_card c hc]
  have hncard : (componentRoots (rootCharHom a) i).ncard =
      kacCount Tag.F4 kacF4.θ (c.map (idxNode (r := Tag.F4.rank))).toFinset := by
    rw [hi', ncard_image_smul, ncard_rootsOf kacF4 facts_F4 hCp]
  rw [hrank] at h2 hn
  rw [hncard] at hn
  rcases f4_count_raw c hc h2 hn with rfl | rfl | rfl | rfl
  ·
    have hC : C = {none, some 0} := by rw [hCdef]; decide
    have hroots := f4_rootsOf_eq (C := C) hCp (σ := f4Sigma01)
      (by rw [hC]; exact f4_long01_roots) (fun a b hab => by
        rw [hC]
        exact ⟨(f4_long01_isRoot a b hab).1, (f4_long01_isRoot a b hab).2.1⟩)
    refine ⟨3, _, fun a b => v • f4Sigma01 a b, 2, le_rfl,
      (IsSLFrame.of_isA2Frame f4_long01_frame).transport v, by decide, fun a b hab => ?_, ?_⟩
    · rw [iform_smul]
      exact (f4_long01_isRoot a b hab).2.2
    · rw [hi', hroots, IsSLFrame.frameRoots_smul]
  ·
    have hC : C = {some 0, some 1} := by rw [hCdef]; decide
    have hroots := f4_rootsOf_eq (C := C) hCp
      (σ := fun a b => CFSG.RankThree.E6.chainRoot f4chainLong a b)
      (by rw [hC]; exact f4_long12_roots) (fun a b hab => by
        rw [hC]
        exact ⟨(f4_long12_isRoot a b hab).1, (f4_long12_isRoot a b hab).2.1⟩)
    refine ⟨3, _, fun a b => v • CFSG.RankThree.E6.chainRoot f4chainLong a b, 2, le_rfl,
      (IsSLFrame.of_isA2Frame f4Long_frame).transport v, by decide, fun a b hab => ?_, ?_⟩
    · rw [iform_smul]
      exact (f4_long12_isRoot a b hab).2.2
    · rw [hi', hroots, IsSLFrame.frameRoots_smul]
  ·
    have hC : C = {some 2, some 3} := by rw [hCdef]; decide
    have hroots := f4_rootsOf_eq (C := C) hCp (σ := f4ShortSigma)
      (by rw [hC]; exact f4_short_roots) (fun a b hab => by
        rw [hC]
        exact ⟨(f4_short_isRoot a b hab).1, (f4_short_isRoot a b hab).2.1⟩)
    refine ⟨3, _, fun a b => v • f4ShortSigma a b, 1, le_rfl,
      (IsSLFrame.of_isA2Frame f4Short_frame).transport v, by decide, fun a b hab => ?_, ?_⟩
    · rw [iform_smul]
      exact (f4_short_isRoot a b hab).2.2
    · rw [hi', hroots, IsSLFrame.frameRoots_smul]
  ·
    exact absurd (not_comp_eq_longA3_F4 hp hμ hcomp) id

end Frames

end CFSG.HardMathSupport.Timmesfeld.CrossChar
