module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompGen
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem card_le_nine_of_ne_top {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 27)
    {A : Subgroup H} (hA : A ≠ ⊤) : Nat.card A ≤ 9 := by
  have hdvd : Nat.card A ∣ 3 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card A
    rwa [hH, show (27 : ℕ) = 3 ^ 3 by norm_num] at this
  obtain ⟨k, hk, hkA⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk3 : k ≠ 3 := by
    rintro rfl
    apply hA
    apply Subgroup.eq_top_of_card_eq
    rw [hkA, hH]
    norm_num
  have hk2 : k ≤ 2 := by omega
  rw [hkA]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem exists_notMem_three {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 27)
    {A B C : Subgroup H} (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤) :
    ∃ h : H, h ∉ A ∧ h ∉ B ∧ h ∉ C := by
  by_contra hno
  push Not at hno
  have cA : (A : Set H).ncard ≤ 9 := by
    rw [← Nat.card_coe_set_eq]
    exact card_le_nine_of_ne_top hH hA
  have cB : (B : Set H).ncard ≤ 9 := by
    rw [← Nat.card_coe_set_eq]
    exact card_le_nine_of_ne_top hH hB
  have cC : (C : Set H).ncard ≤ 9 := by
    rw [← Nat.card_coe_set_eq]
    exact card_le_nine_of_ne_top hH hC
  have hcov : ((A : Set H) ∪ B) ∪ C = Set.univ := by
    ext h
    simp only [Set.mem_union, SetLike.mem_coe, Set.mem_univ, iff_true]
    by_cases hA' : h ∈ A
    · exact Or.inl (Or.inl hA')
    · by_cases hB' : h ∈ B
      · exact Or.inl (Or.inr hB')
      · exact Or.inr (hno h hA' hB')
  have h1 := Set.ncard_union_add_ncard_inter (A : Set H) B (Set.toFinite _) (Set.toFinite _)
  have h2 := Set.ncard_union_add_ncard_inter ((A : Set H) ∪ B) C (Set.toFinite _)
    (Set.toFinite _)
  have hp1 : 0 < ((A : Set H) ∩ B).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨1, A.one_mem, B.one_mem⟩
  have hp2 : 0 < (((A : Set H) ∪ B) ∩ C).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨1, Or.inl A.one_mem, C.one_mem⟩
  have hun : (Set.univ : Set H).ncard = 27 := by rw [Set.ncard_univ, hH]
  rw [hcov] at h2
  omega

section Fixer


def factorFixer (K : Type) [Field K] (i : Fin 3) : Subgroup (MulAut (adjointGroup Tag.E6 K)) where
  carrier := {f | ∀ x : adjointGroup Tag.E6 K, (x : ModGL Tag.E6 K) ∈ e6LineFactor K i → f x = x}
  mul_mem' {f g} hf hg x hx := by
    rw [MulAut.mul_apply, hg x hx, hf x hx]
  one_mem' x _ := rfl
  inv_mem' {f} hf x hx := f.injective (by rw [MulAut.apply_inv_self, hf x hx])

theorem mem_factorFixer {K : Type} [Field K] {i : Fin 3} {f : MulAut (adjointGroup Tag.E6 K)} :
    f ∈ factorFixer K i ↔ ∀ x : adjointGroup Tag.E6 K,
      (x : ModGL Tag.E6 K) ∈ e6LineFactor K i → f x = x :=
  Iff.rfl

theorem e6NormalizesR_of_le_factorFixer {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {i : Fin 3} (h : E ≤ factorFixer K i) :
    E6NormalizesR K E := by
  obtain ⟨α, hα⟩ : (e6LineRoots i).Nonempty :=
    Finset.card_pos.1 (by rw [card_e6LineRoots]; norm_num)
  refine ⟨(rootSubgroup .E6 K α).subgroupOf (adjointGroup Tag.E6 K), ?_, ?_, fun ε hε => ?_⟩
  · intro hbot
    have hmem : (⟨pinnedX Tag.E6 K α 1, pinnedX_mem_adjointGroup α 1⟩ : adjointGroup Tag.E6 K) ∈
        (rootSubgroup .E6 K α).subgroupOf (adjointGroup Tag.E6 K) :=
      mem_rootSubgroup.2 ⟨1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : pinnedX Tag.E6 K α 1 = pinnedX Tag.E6 K α 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val hmem
    exact one_ne_zero (pinnedX_injective Tag.E6 K α h1)
  · have hmult : IsPGroup (ringChar K) (Multiplicative K) := fun x => ⟨1, by
      rw [pow_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]
      rfl⟩
    exact (hmult.of_equiv (rootSubgroupEquiv Tag.E6 K α)).comap_of_injective
      (adjointGroup Tag.E6 K).subtype Subtype.val_injective
  · have hfix : ∀ x ∈ (rootSubgroup .E6 K α).subgroupOf (adjointGroup Tag.E6 K), ε x = x :=
      fun x hx => h hε x (rootSubgroup_le_e6LineFactor K hα hx)
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hfix x hx]
      exact hx
    · intro hy
      exact ⟨y, hy, hfix y hy⟩

end Fixer

section Gen

variable
  {K : Type} [Field K]

theorem not_smul_one_of_noncentral {v : adjointGroup Tag.E6 K}
    {ρ : SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K} {i : Fin 3}
    (hrange : ρ.range = e6LineFactor K i) {A : GL (Fin 3) K}
    (hA : ∀ s, (v : ModGL Tag.E6 K) * ρ s * (v : ModGL Tag.E6 K)⁻¹ = ρ (conjSL A s))
    (hmove : ∃ x : adjointGroup Tag.E6 K, (x : ModGL Tag.E6 K) ∈ e6LineFactor K i ∧
      MulAut.conj v x ≠ x) (κ : K) :
    (A : Matrix (Fin 3) (Fin 3) K) ≠ κ • 1 := by
  intro hκ
  have h1 : conjSL A = 1 := conjSL_eq_one_of_eq_smul_one hκ
  obtain ⟨x, hxF, hx⟩ := hmove
  rw [← hrange] at hxF
  obtain ⟨s, hs⟩ := hxF
  apply hx
  apply Subtype.ext
  rw [MulAut.conj_apply]
  have h := hA s
  rw [h1, MulAut.one_apply, hs] at h
  exact h

theorem canonicalRep_mem_of_fix_inner [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ}
    (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) (hEd : E ≤ e6Inndiag K)
    (hER : ¬ E6NormalizesR K E)
    (hsig : MulAut.conj (e6LineElt ω) ∈ E) {v : adjointGroup Tag.E6 K}
    (hv : MulAut.conj v ∈ E)
    (hvσ : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)))
    (hvM : (v : ModGL .E6 K) ∈ toralRootGroup .E6 K (e6LineChar ω))
    (hvmoves : ∀ i : Fin 3, ∃ x : adjointGroup Tag.E6 K,
      (x : ModGL Tag.E6 K) ∈ e6LineFactor K i ∧ MulAut.conj v x ≠ x)
    (hfix : ∀ f ∈ E, ∀ i : Fin 3,
      ((e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)).map f.toMonoidHom =
        (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
        toralRootGroup .E6 K (e6LineChar ω) := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  have hroots : ∀ α ∈ ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)), IsRoot .E6 α :=
    fun α hα => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hα
      exact isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hi)
  have hTN : torusGroup .E6 K ≤ Subgroup.normalizer
      (rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) :
        Set (ModGL Tag.E6 K)) :=
    torusGroup_le_normalizer_rootSpan_e6 hroots
  have hLM : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
      toralRootGroup .E6 K (e6LineChar ω) := by
    show _ ≤ torusGroup .E6 K ⊔ rootSpan .E6 K (rootCharKernel (e6LineChar ω))
    rw [e6Line_kernel hw3 hw1]
    exact le_sup_right
  have hnX : canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      toralCentralizer .E6 K (e6LineChar ω) :=
    canonicalRep_mem_toralCentralizer (e6LineWeyl_mem_stabilizer hw3 hw1)
  have hnL := canonicalRep_e6LineWeyl_mem_normalizer (K := K)
  have hcomm : ∀ d ∈ torusGroup .E6 K, canonicalRep (coxeterSystem .E6) K e6LineWeyl * d *
      (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹ * d⁻¹ ∈
        rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) :=
    fun d hd => canonicalRep_e6LineWeyl_commutator_mem hd
  obtain ⟨ρ, D, hinj, hrange, htor, hsh⟩ := exists_e6LineFrames_shift h3 hw3 hw1
  generalize canonicalRep (coxeterSystem .E6) K e6LineWeyl = n at hnX hnL hcomm hsh ⊢
  obtain ⟨π, -, hπL, hπonto, hconjd, -, hπconj, hMdec⟩ :=
    exists_commProd_of_frames hw3 hw1 hrange htor
  have hFC : ∀ i, e6LineFactor K i ≤ adjointGroup Tag.E6 K := fun i =>
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hρC : ∀ i s, ρ i s ∈ adjointGroup Tag.E6 K := fun i s =>
    hFC i ((hrange i) ▸ ⟨s, rfl⟩)
  have hd : ∀ i b, rootDiagUnit Tag.E6 b ∈ frameActSub (ρ i) := fun i b => ⟨D i b, htor i b⟩
  have hact : ∀ c x i s, (rootDiagUnit Tag.E6 c * π x) * ρ i s *
      (rootDiagUnit Tag.E6 c * π x)⁻¹ = ρ i (conjSL (D i c * SpecialLinearGroup.toGL (x i)) s) :=
    fun c x i s => by
      rw [map_mul, MulAut.mul_apply, conjSL_toGL, MulAut.conj_apply,
        ← htor i c (x i * s * (x i)⁻¹), ← hπconj x i s]
      group
  obtain ⟨c, x, hcT, hvcx⟩ := hMdec _ hvM
  have hvA : ∀ i s, (v : ModGL Tag.E6 K) * ρ i s * (v : ModGL Tag.E6 K)⁻¹ =
      ρ i (conjSL (D i c * SpecialLinearGroup.toGL (x i)) s) := fun i s => by
    rw [hvcx]
    exact hact c x i s
  have hv3 : (v : ModGL Tag.E6 K) ^ 3 = 1 := by
    have h : v ^ 3 = 1 := CFSG.Fischer.mulAutConj_injective center_adjointGroup_eq_bot
      (by rw [map_pow, map_one]; exact hE.2 _ hv)
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  have hα : ∀ i, ∃ α : K, ((D i c * SpecialLinearGroup.toGL (x i) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := fun i =>
    exists_pow_three_smul_one (ρ := ρ i) (hinj i) (ε := MulAut.conj (v : ModGL Tag.E6 K))
      (by rw [← map_pow, hv3, map_one]) fun s => by rw [MulAut.conj_apply]; exact hvA i s
  choose α hα using hα
  have hcyc : ∀ i, HasCyclicVec3 ((D i c * SpecialLinearGroup.toGL (x i) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) := fun i =>
    hasCyclicVec3_of_acts h3 hw3 hw1 hE hEd hER hsig hρC hinj hrange hd hfix hv
      (fun s => Subtype.ext (hvA i s)) (hα i)
      (not_smul_one_of_noncentral (hrange i) (hvA i) (hvmoves i))
  obtain ⟨x'', hnv⟩ : ∃ x'' : Fin 3 → SpecialLinearGroup (Fin 3) K,
      n * (v : ModGL Tag.E6 K) * n⁻¹ = rootDiagUnit Tag.E6 c * π x'' := by
    have hl₁ := (Subgroup.mem_normalizer_iff.1 (hTN (inv_mem hcT)) _).1 (hcomm _ hcT)
    have hl₂ := (Subgroup.mem_normalizer_iff.1 hnL _).1 (hπL x)
    obtain ⟨x'', hx''⟩ := hπonto _ (mul_mem hl₁ hl₂)
    refine ⟨x'', ?_⟩
    rw [hx'', hvcx]
    group
  have hnvB : ∀ i s, (n * (v : ModGL Tag.E6 K) * n⁻¹) * ρ i s *
      (n * (v : ModGL Tag.E6 K) * n⁻¹)⁻¹ =
        ρ i (conjSL (D i c * SpecialLinearGroup.toGL (x'' i)) s) := fun i s => by
    rw [hnv]
    exact hact c x'' i s
  have hβ : ∀ i, ∃ β : K, ((D i c * SpecialLinearGroup.toGL (x'' i) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = β • 1 := fun i =>
    exists_pow_three_smul_one (ρ := ρ i) (hinj i)
      (ε := MulAut.conj (n * (v : ModGL Tag.E6 K) * n⁻¹))
      (by rw [← map_pow, conj_pow, hv3, mul_one, mul_inv_cancel, map_one])
      fun s => by rw [MulAut.conj_apply]; exact hnvB i s
  choose β hβ using hβ
  have hBA : ∀ i, ∃ (μ : GL (Fin 3) K) (κ : K), κ ≠ 0 ∧
      ((D (i + 1) c * SpecialLinearGroup.toGL (x'' (i + 1)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = κ • ((μ : Matrix (Fin 3) (Fin 3) K) *
          ((D i c * SpecialLinearGroup.toGL (x i) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((μ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    intro i
    obtain ⟨μ, hμ⟩ := hsh i
    have heq : conjSL ((D (i + 1) c * SpecialLinearGroup.toGL (x'' (i + 1))) * μ) =
        conjSL (μ * (D i c * SpecialLinearGroup.toGL (x i))) := by
      refine MulEquiv.ext fun s => hinj (i + 1) ?_
      rw [map_mul conjSL (D (i + 1) c * SpecialLinearGroup.toGL (x'' (i + 1))) μ,
        map_mul conjSL μ (D i c * SpecialLinearGroup.toGL (x i)), MulAut.mul_apply,
        MulAut.mul_apply, ← hnvB (i + 1) (conjSL μ s), ← hμ s,
        ← hμ (conjSL (D i c * SpecialLinearGroup.toGL (x i)) s), ← hvA i s]
      group
    obtain ⟨κ, hκ0, hκ⟩ := exists_smul_of_conjSL_eq heq
    refine ⟨μ, κ, hκ0, ?_⟩
    calc ((D (i + 1) c * SpecialLinearGroup.toGL (x'' (i + 1)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)
        = (((D (i + 1) c * SpecialLinearGroup.toGL (x'' (i + 1))) * μ : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) * ((μ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [Units.val_mul _ μ, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [hκ, Units.val_mul μ, Matrix.smul_mul]
  have hcycB : ∀ j, HasCyclicVec3 ((D j c * SpecialLinearGroup.toGL (x'' j) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) := by
    intro j
    obtain ⟨μ, κ, hκ0, hBe⟩ := hBA (j - 1)
    rw [sub_add_cancel] at hBe
    rw [hBe]
    exact (hcyc (j - 1)).smul_conj μ hκ0
  have hdet : ∀ i, ((D i c * SpecialLinearGroup.toGL (x i) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = ((D i c * SpecialLinearGroup.toGL (x'' i) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := fun i => by
    have h1 : ∀ s : SpecialLinearGroup (Fin 3) K,
        ((SpecialLinearGroup.toGL s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      fun s => s.2
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h1, h1]
  have hy : ∀ i, ∃ y : SpecialLinearGroup (Fin 3) K,
      SpecialLinearGroup.toGL y * (D i c * SpecialLinearGroup.toGL (x i)) =
        (D i c * SpecialLinearGroup.toGL (x'' i)) * SpecialLinearGroup.toGL y := fun i =>
    exists_SL_conj_of_hasCyclicVec3 h3 (hα i) (hβ i) (hdet i) (hcyc i) (hcycB i)
  choose y hy using hy
  have hfac : ∀ i, conjSL (D i c)⁻¹ (y i) * x i * (y i)⁻¹ = x'' i := fun i => by
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv SpecialLinearGroup.toGL (y i), toGL_conjSL_eq_mul, inv_inv]
    calc (D i c)⁻¹ * SpecialLinearGroup.toGL (y i) * D i c * SpecialLinearGroup.toGL (x i) *
          (SpecialLinearGroup.toGL (y i))⁻¹
        = (D i c)⁻¹ * (SpecialLinearGroup.toGL (y i) *
            (D i c * SpecialLinearGroup.toGL (x i))) * (SpecialLinearGroup.toGL (y i))⁻¹ := by
          group
      _ = (D i c)⁻¹ * ((D i c * SpecialLinearGroup.toGL (x'' i)) *
            SpecialLinearGroup.toGL (y i)) * (SpecialLinearGroup.toGL (y i))⁻¹ := by
          rw [hy i]
      _ = SpecialLinearGroup.toGL (x'' i) := by group
  have hkey : π y * (v : ModGL Tag.E6 K) * (π y)⁻¹ = n * (v : ModGL Tag.E6 K) * n⁻¹ := by
    rw [hnv, hvcx]
    have h1 : π y * (rootDiagUnit Tag.E6 c * π x) * (π y)⁻¹ = rootDiagUnit Tag.E6 c *
        ((rootDiagUnit Tag.E6 c)⁻¹ * π y * rootDiagUnit Tag.E6 c * π x * (π y)⁻¹) := by group
    rw [h1, hconjd c y, ← map_inv π y, ← map_mul π, ← map_mul π]
    congr 2
    funext i
    exact hfac i
  have hgX : n⁻¹ * π y ∈ toralCentralizer .E6 K (e6LineChar ω) :=
    mul_mem (inv_mem hnX) (toralRootGroup_le _ (hLM (hπL y)))
  obtain ⟨hgC, hgχ⟩ := mem_toralCentralizer.1 hgX
  have hgv : (n⁻¹ * π y) * (v : ModGL Tag.E6 K) * (n⁻¹ * π y)⁻¹ = v := by
    calc (n⁻¹ * π y) * (v : ModGL Tag.E6 K) * (n⁻¹ * π y)⁻¹
        = n⁻¹ * (π y * (v : ModGL Tag.E6 K) * (π y)⁻¹) * n := by group
      _ = n⁻¹ * (n * (v : ModGL Tag.E6 K) * n⁻¹) * n := by rw [hkey]
      _ = v := by group
  have hσg : MulAut.conj (e6LineElt ω) (⟨_, hgC⟩ : adjointGroup Tag.E6 K) = ⟨_, hgC⟩ := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    exact hgχ
  have hvg : MulAut.conj v (⟨_, hgC⟩ : adjointGroup Tag.E6 K) = ⟨_, hgC⟩ := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    show (v : ModGL Tag.E6 K) * (n⁻¹ * π y) * (v : ModGL Tag.E6 K)⁻¹ = n⁻¹ * π y
    have hc : (n⁻¹ * π y) * (v : ModGL Tag.E6 K) = (v : ModGL Tag.E6 K) * (n⁻¹ * π y) := by
      calc (n⁻¹ * π y) * (v : ModGL Tag.E6 K)
          = ((n⁻¹ * π y) * (v : ModGL Tag.E6 K) * (n⁻¹ * π y)⁻¹) * (n⁻¹ * π y) := by group
        _ = _ := by rw [hgv]
    rw [← hc, mul_inv_cancel_right]
  have hgΓ := mem_seitzHyperGamma_of_fixed hE hcard27 hsig hv (conj_e6LineElt_ne_one hw1) hvσ
    hσg hvg
  have e : n = π y * (n⁻¹ * π y)⁻¹ := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_right (hLM (hπL y)))
    (Subgroup.mem_sup_left (inv_mem ⟨⟨_, hgC⟩, hgΓ, rfl⟩))

theorem exists_inner_moving_all_factors [Finite K]
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hcard : Nat.card E = 3 ^ 3)
    (hEi : E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) (hER : ¬ E6NormalizesR K E) :
    ∃ v : adjointGroup Tag.E6 K, MulAut.conj v ∈ E ∧ ∀ i : Fin 3,
      MulAut.conj v ∉ factorFixer K i := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard27]; norm_num)
  have hne : ∀ i, (factorFixer K i).subgroupOf E ≠ ⊤ := fun i hi =>
    hER (e6NormalizesR_of_le_factorFixer fun ε hε => by
      have h : (⟨ε, hε⟩ : E) ∈ (factorFixer K i).subgroupOf E := by
        rw [hi]
        exact Subgroup.mem_top _
      exact h)
  obtain ⟨ε, h0, h1, h2⟩ := exists_notMem_three hcard27 (hne 0) (hne 1) (hne 2)
  obtain ⟨v, hv⟩ := CFSG.Fischer.mem_innerAut.1 (hEi ε.2)
  refine ⟨v, hv ▸ ε.2, fun i => ?_⟩
  rw [hv]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem e6ThreeCompGenInner_holds :
    ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
      ∀ ω : Kˣ, ω ^ 3 = 1 → ω ≠ 1 →
      ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
        E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) → ¬ E6NormalizesR K E →
        MulAut.conj (e6LineElt ω) ∈ E →
        canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
          (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
            toralRootGroup .E6 K (e6LineChar ω) := by
  intro K _ _ _ h3 _ ω hw3 hw1 E hE hcard hEi hER hsig
  have hEd : E ≤ e6Inndiag K := hEi.trans (innerAut_le_e6Inndiag K)
  obtain ⟨v, hv, hvall⟩ := exists_inner_moving_all_factors hcard hEi hER
  have hσ0 : (MulAut.conj (e6LineElt ω) : MulAut (adjointGroup Tag.E6 K)) ∈ factorFixer K 0 :=
    fun x hx => conj_e6LineElt_apply_of_mem hw3 hw1 0 hx
  have hvσ : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)) := fun hmem =>
    hvall 0 ((Subgroup.zpowers_le.2 hσ0) hmem)
  have hvmoves : ∀ i : Fin 3, ∃ x : adjointGroup Tag.E6 K,
      (x : ModGL Tag.E6 K) ∈ e6LineFactor K i ∧ MulAut.conj v x ≠ x := fun i => by
    have h := hvall i
    rw [mem_factorFixer] at h
    push Not at h
    exact h
  by_cases hvM : (v : ModGL .E6 K) ∈ toralRootGroup .E6 K (e6LineChar ω)
  · by_cases hmove : ∃ f ∈ E, ∃ i : Fin 3,
        ((e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)).map f.toMonoidHom ≠
          (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)
    · obtain ⟨f, hf, i, hfi⟩ := hmove
      exact canonicalRep_mem_of_moves h3 hw3 hw1 hE hcard hEd hsig hv hvσ hvM hf hfi
    · push Not at hmove
      exact canonicalRep_mem_of_fix_inner h3 hw3 hw1 hE hcard hEd hER hsig hv hvσ hvM hvmoves
        hmove
  · exact canonicalRep_mem_of_notMem h3 hw3 hw1 hE hcard hsig hv hvσ hvM

end Gen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
