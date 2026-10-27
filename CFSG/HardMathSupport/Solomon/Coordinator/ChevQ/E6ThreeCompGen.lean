module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompFix
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompRegular
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompTorusComm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeSL3UnipStab

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcWideThree
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem exists_smul_of_conjSL_eq {K : Type*} [Field K] {g h : GL (Fin 3) K}
    (heq : conjSL g = conjSL h) :
    ∃ κ : K, κ ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) = κ • (h : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : conjSL (g * h⁻¹) = 1 := by
    rw [map_mul, heq, ← map_mul, mul_inv_cancel, map_one]
  obtain ⟨κ, hκ⟩ := exists_smul_one_of_conjSL_eq_one h1
  have e : (g : Matrix (Fin 3) (Fin 3) K) = κ • (h : Matrix (Fin 3) (Fin 3) K) := by
    calc (g : Matrix (Fin 3) (Fin 3) K)
        = ((g * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * h := by
          rw [Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      _ = κ • (h : Matrix (Fin 3) (Fin 3) K) := by
          rw [hκ, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨κ, fun hκ0 => g.ne_zero ?_, e⟩
  rw [e, hκ0, zero_smul]

section Gen

variable
  {K : Type} [Field K]

theorem e6LineFactor_conj_pow_mem (i : Fin 3) {g : ModGL Tag.E6 K}
    (hg : g ∈ e6LineFactor K 0) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ (i : ℕ) * g *
        (canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ (i : ℕ))⁻¹ ∈ e6LineFactor K i := by
  have h1 : ∀ (j : Fin 3), ∀ h ∈ e6LineFactor K j,
      canonicalRep (coxeterSystem .E6) K e6LineWeyl * h *
        (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹ ∈ e6LineFactor K (j + 1) :=
    fun j h hh => by
      rw [← e6LineFactor_conj]
      exact ⟨h, hh, rfl⟩
  generalize canonicalRep (coxeterSystem .E6) K e6LineWeyl = n at h1 ⊢
  fin_cases i
  · show n ^ 0 * g * (n ^ 0)⁻¹ ∈ e6LineFactor K 0
    simpa using hg
  · show n ^ 1 * g * (n ^ 1)⁻¹ ∈ e6LineFactor K 1
    rw [pow_one]
    exact h1 0 g hg
  · show n ^ 2 * g * (n ^ 2)⁻¹ ∈ e6LineFactor K 2
    rw [show n ^ 2 * g * (n ^ 2)⁻¹ = n * (n * g * n⁻¹) * n⁻¹ by
      rw [pow_two, _root_.mul_inv_rev]; simp only [mul_assoc]]
    exact h1 1 _ (h1 0 g hg)

theorem exists_e6LineFrames_shift [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ}
    (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) :
    ∃ (ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K)
      (D : Fin 3 → (Fin Tag.E6.rank → Kˣ) → GL (Fin 3) K),
      (∀ i, Function.Injective (ρ i)) ∧ (∀ i, (ρ i).range = e6LineFactor K i) ∧
      (∀ i b s, rootDiagUnit Tag.E6 b * ρ i s * (rootDiagUnit Tag.E6 b)⁻¹ =
        ρ i (conjSL (D i b) s)) ∧
      ∀ i, ∃ μ : GL (Fin 3) K, ∀ s,
        canonicalRep (coxeterSystem .E6) K e6LineWeyl * ρ i s *
          (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹ = ρ (i + 1) (conjSL μ s) := by
  obtain ⟨ρ₀, σ₀, hfr₀, hr₀⟩ := exists_frame_e6Line K 0
  have hfr₁ := hfr₀.transport e6LineWeyl
  have hfr₂ := hfr₁.transport e6LineWeyl
  have hr₁ : ((MulAut.conj (canonicalRep (coxeterSystem .E6) K e6LineWeyl)).toMonoidHom.comp
      ρ₀).range = e6LineFactor K 1 := by
    rw [MonoidHom.range_comp, hr₀]
    exact e6LineFactor_conj 0
  have hr₂ : ((MulAut.conj (canonicalRep (coxeterSystem .E6) K e6LineWeyl)).toMonoidHom.comp
      ((MulAut.conj (canonicalRep (coxeterSystem .E6) K e6LineWeyl)).toMonoidHom.comp
        ρ₀)).range = e6LineFactor K 2 := by
    rw [MonoidHom.range_comp, hr₁]
    exact e6LineFactor_conj 1
  have hn3 := canonicalRep_e6LineWeyl_pow_three_mem h3 hw3 hw1
  generalize canonicalRep (coxeterSystem .E6) K e6LineWeyl = n at hfr₁ hfr₂ hr₁ hr₂ hn3 ⊢
  let ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K :=
    ![ρ₀, (MulAut.conj n).toMonoidHom.comp ρ₀,
      (MulAut.conj n).toMonoidHom.comp ((MulAut.conj n).toMonoidHom.comp ρ₀)]
  let σ : Fin 3 → Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ :=
    ![σ₀, fun a b => e6LineWeyl • σ₀ a b, fun a b => e6LineWeyl • (e6LineWeyl • σ₀ a b)]
  have hfr : ∀ i, IsA2Frame (ρ i) (σ i) := by
    intro i
    fin_cases i
    · exact hfr₀
    · exact hfr₁
    · exact hfr₂
  have hrange : ∀ i, (ρ i).range = e6LineFactor K i := by
    intro i
    fin_cases i
    · exact hr₀
    · exact hr₁
    · exact hr₂
  have hd : ∀ i b, rootDiagUnit Tag.E6 b ∈ frameActSub (ρ i) := fun i b =>
    rootDiagUnit_mem_frameActSub (hfr i) b
  refine ⟨ρ, fun i b => diagGL3 fun j => rootChar b (σ i j 0), fun i => (hfr i).injective,
    hrange, fun i b s => ?_, fun i => ?_⟩
  · rw [conjSL_diagGL3]
    exact (hfr i).torus b s
  · fin_cases i
    · exact ⟨1, fun s => by rw [map_one, MulAut.one_apply]; rfl⟩
    · exact ⟨1, fun s => by rw [map_one, MulAut.one_apply]; rfl⟩
    · obtain ⟨μ, hμ⟩ := toralRootGroup_le_frameActSub hw3 hw1 hrange hd 0 hn3
      refine ⟨μ, fun s => Eq.trans ?_ (hμ s)⟩
      show n * (n * (n * ρ₀ s * n⁻¹) * n⁻¹) * n⁻¹ = n ^ 3 * ρ₀ s * (n ^ 3)⁻¹
      rw [pow_three, _root_.mul_inv_rev, _root_.mul_inv_rev]
      simp only [mul_assoc]

theorem hasCyclicVec3_of_acts [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ} (hw3 : ω ^ 3 = 1)
    (hw1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hEd : E ≤ e6Inndiag K) (hER : ¬ E6NormalizesR K E)
    (hsig : MulAut.conj (e6LineElt ω) ∈ E)
    {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    (hρC : ∀ i s, ρ i s ∈ adjointGroup Tag.E6 K) (hinj : ∀ i, Function.Injective (ρ i))
    (hrange : ∀ i, (ρ i).range = e6LineFactor K i)
    (hd : ∀ i b, rootDiagUnit Tag.E6 b ∈ frameActSub (ρ i))
    (hfix : ∀ f ∈ E, ∀ i : Fin 3,
      ((e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)).map f.toMonoidHom =
        (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K))
    {ε : MulAut (adjointGroup Tag.E6 K)} (hε : ε ∈ E) {i : Fin 3} {A : GL (Fin 3) K} {α : K}
    (hA : ∀ s, ε ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) s) =
      (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) (conjSL A s))
    (hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hAs : ∀ κ : K, (A : Matrix (Fin 3) (Fin 3) K) ≠ κ • 1) :
    HasCyclicVec3 (A : Matrix (Fin 3) (Fin 3) K) := by
  have hK4 : 4 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hω3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hw3, Units.val_one]
  have hω1 : (ω : K) ≠ 1 := fun h => hw1 (Units.val_eq_one.1 h)
  have hle : ∀ j, e6LineFactor K j ≤ adjointGroup Tag.E6 K := fun j =>
    iSup₂_le fun β _ => rootSubgroup_le_adjointGroup β
  have hCinj : Function.Injective ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i)) :=
    fun s t hst => hinj i (congrArg Subtype.val hst)
  have hinvSL : ∀ (g : GL (Fin 3) K) (s : SpecialLinearGroup (Fin 3) K),
      conjSL g (conjSL g⁻¹ s) = s := fun g s => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hact : ∀ f ∈ E, ∃ γ : GL (Fin 3) K, ∀ s,
      f ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) s) =
        (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) (conjSL γ s) := by
    intro f hf
    obtain ⟨k, hk, hk0⟩ := exists_hdec hw3 hw1 hK4 hE hEd hsig hρC hrange hd hf
    have hk' : k = 0 := by
      have h1 := hk 0
      rw [range_codRestrict_eq, range_codRestrict_eq, hrange, hrange, hfix f hf 0,
        Subgroup.subgroupOf_inj, inf_of_le_left (hle 0), inf_of_le_left (hle _)] at h1
      have h2 := e6LineFactor_injective h3 h1
      rw [zero_add] at h2
      exact h2.symm
    exact hk0 hk' i
  let S : Set (GL (Fin 3) K) := {γ | ∃ f ∈ E, ∀ s,
    f ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) s) =
      (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) (conjSL γ s)}
  have hSinv : ∀ γ ∈ S, γ⁻¹ ∈ S := by
    rintro γ ⟨f, hf, hγ⟩
    refine ⟨f⁻¹, inv_mem hf, fun s => f.injective ?_⟩
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply, hγ, hinvSL]
  have hSc : ∀ B ∈ S, ∃ κ : K, (B : Matrix (Fin 3) (Fin 3) K) * A =
      κ • ((A : Matrix (Fin 3) (Fin 3) K) * B) := by
    rintro B ⟨f, hf, hB⟩
    have hcomm : f * ε = ε * f :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hf⟩ : E) ⟨_, hε⟩)
    have heq : conjSL (B * A) = conjSL (A * B) := by
      refine MulEquiv.ext fun s => hCinj ?_
      have h := congrArg (fun φ : MulAut (adjointGroup Tag.E6 K) =>
        φ ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) s)) hcomm
      simp only [MulAut.mul_apply] at h
      rw [hA s, hB (conjSL A s), hB s, hA (conjSL B s)] at h
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
      exact h
    obtain ⟨κ, -, hκ⟩ := exists_smul_of_conjSL_eq heq
    exact ⟨κ, by rw [← Units.val_mul, ← Units.val_mul]; exact hκ⟩
  have hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ B ∈ S, ∀ w ∈ W, (B : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_contra hne
    push Not at hne
    refine hER ⟨(sl3UnipStab W).map ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i)), ?_,
      (isPGroup_sl3UnipStab W).map _, fun f hf => ?_⟩
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hCinj]
      exact sl3UnipStab_ne_bot hne.1 hne.2
    · obtain ⟨γ, hγ⟩ := hact f hf
      have hγS : γ ∈ S := ⟨f, hf, hγ⟩
      have hW₁ := hW γ hγS
      have hW₂ := hW γ⁻¹ (hSinv γ hγS)
      ext y
      constructor
      · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨conjSL γ s, conjSL_mem_sl3UnipStab hW₁ hW₂ hs, (hγ s).symm⟩
      · rintro ⟨s, hs, rfl⟩
        refine ⟨(ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) (conjSL γ⁻¹ s),
          ⟨conjSL γ⁻¹ s, conjSL_mem_sl3UnipStab hW₂ (by rwa [inv_inv]) hs, rfl⟩, ?_⟩
        show f _ = _
        rw [hγ, hinvSL]
  exact hasCyclicVec3_of_irreducible hω3 hω1 hA3 hAs S hSc hirr

theorem not_smul_one_of_inner [Finite K] (hK3 : (3 : K) ≠ 0) {ω : Kˣ} (hw3 : ω ^ 3 = 1)
    (hw1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hall : E6InnerAll24 K E) (hsig : MulAut.conj (e6LineElt ω) ∈ E)
    {v : adjointGroup Tag.E6 K} (hv : MulAut.conj v ∈ E)
    (hvσ : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)))
    (hvM : (v : ModGL .E6 K) ∈ toralRootGroup .E6 K (e6LineChar ω))
    {ρ : SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K} {i : Fin 3}
    (hrange : ρ.range = e6LineFactor K i) {A : GL (Fin 3) K}
    (hA : ∀ s, (v : ModGL Tag.E6 K) * ρ s * (v : ModGL Tag.E6 K)⁻¹ = ρ (conjSL A s)) (κ : K) :
    (A : Matrix (Fin 3) (Fin 3) K) ≠ κ • 1 := by
  intro hκ
  have h1 : conjSL A = 1 := conjSL_eq_one_of_eq_smul_one hκ
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hvσ (by rw [map_one]; exact one_mem _)
  have hv2 : e6LineElt ω * v ≠ 1 := by
    intro h
    apply hvσ
    rw [eq_inv_of_mul_eq_one_right h, map_inv]
    exact inv_mem (Subgroup.mem_zpowers _)
  have hv4 : e6LineElt ω ^ 2 * v ≠ 1 := by
    intro h
    apply hvσ
    rw [eq_inv_of_mul_eq_one_right h, map_inv, map_pow]
    exact inv_mem (pow_mem (Subgroup.mem_zpowers _) 2)
  have hd1 := hall v hv hv1
  have hd2 := hall (e6LineElt ω * v) (by rw [map_mul]; exact mul_mem hsig hv) hv2
  have hd4 := hall (e6LineElt ω ^ 2 * v)
    (by rw [map_mul, map_pow]; exact mul_mem (pow_mem hsig 2) hv) hv4
  rw [Subgroup.coe_mul, coe_e6LineElt] at hd2
  rw [Subgroup.coe_mul, Subgroup.coe_pow, coe_e6LineElt] at hd4
  have hv3 : (v : ModGL .E6 K) ^ 3 = 1 := by
    have h : v ^ 3 = 1 := CFSG.Fischer.mulAutConj_injective center_adjointGroup_eq_bot
      (by rw [map_pow, map_one]; exact hE.2 _ hv)
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  have hnX : canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      toralCentralizer .E6 K (e6LineChar ω) :=
    canonicalRep_mem_toralCentralizer (e6LineWeyl_mem_stabilizer hw3 hw1)
  have hnN : canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      Subgroup.normalizer (toralRootGroup .E6 K (e6LineChar ω) : Set (ModGL .E6 K)) :=
    canonicalRep_mem_normalizer_toralRootGroup (e6LineWeyl_mem_stabilizer hw3 hw1)
  have hconj : ∀ g ∈ e6LineFactor K 0,
      canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ (i : ℕ) * g *
        (canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ (i : ℕ))⁻¹ ∈ e6LineFactor K i :=
    fun g hg => e6LineFactor_conj_pow_mem i hg
  generalize canonicalRep (coxeterSystem .E6) K e6LineWeyl = n at hnX hnN hconj
  have hth : n ^ (i : ℕ) * rootDiagUnit .E6 (e6LineChar ω) =
      rootDiagUnit .E6 (e6LineChar ω) * n ^ (i : ℕ) :=
    (mul_inv_eq_iff_eq_mul.1 (mem_toralCentralizer.1 (pow_mem hnX _)).2).symm
  refine false_of_commute_conj_e6LineFactor_zero hw3 hw1 hK3 hvM (pow_mem hnN _) hth
    (fun g hg => ?_) hv3 hd1 hd2 hd4
  have hmem := hconj g hg
  rw [← hrange] at hmem
  obtain ⟨s, hs⟩ := hmem
  rw [← hs]
  have h := hA s
  rw [h1, MulAut.one_apply] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem canonicalRep_mem_of_fix [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ}
    (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) (hEd : E ≤ e6Inndiag K)
    (hER : ¬ E6NormalizesR K E) (hall : E6InnerAll24 K E)
    (hsig : MulAut.conj (e6LineElt ω) ∈ E) {v : adjointGroup Tag.E6 K}
    (hv : MulAut.conj v ∈ E)
    (hvσ : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)))
    (hvM : (v : ModGL .E6 K) ∈ toralRootGroup .E6 K (e6LineChar ω))
    (hfix : ∀ f ∈ E, ∀ i : Fin 3,
      ((e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)).map f.toMonoidHom =
        (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
        toralRootGroup .E6 K (e6LineChar ω) := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  have hK3 : (3 : K) ≠ 0 := by
    intro h
    have hω3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hw3, Units.val_one]
    have e : ((ω : K) - 1) ^ 3 = 0 := by
      linear_combination hω3 - ((ω : K) ^ 2 - (ω : K)) * h
    exact hw1 (Units.val_eq_one.1 (sub_eq_zero.1 ((pow_eq_zero_iff three_ne_zero).1 e)))
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
      (not_smul_one_of_inner hK3 hw3 hw1 hE hall hsig hv hvσ hvM (hrange i) (hvA i))
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

theorem e6ThreeCompGen_holds : E6ThreeCompGen := by
  intro K _ _ _ h3 _ ω hw3 hw1 E hE hcard hEd hEi hER hall hsig
  obtain ⟨v, hv, hvσ⟩ := exists_inner_notMem_zpowers hE hcard hEd hEi hsig
  by_cases hvM : (v : ModGL .E6 K) ∈ toralRootGroup .E6 K (e6LineChar ω)
  · by_cases hmove : ∃ f ∈ E, ∃ i : Fin 3,
        ((e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)).map f.toMonoidHom ≠
          (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)
    · obtain ⟨f, hf, i, hfi⟩ := hmove
      exact canonicalRep_mem_of_moves h3 hw3 hw1 hE hcard hEd hsig hv hvσ hvM hf hfi
    · push Not at hmove
      exact canonicalRep_mem_of_fix h3 hw3 hw1 hE hcard hEd hER hall hsig hv hvσ hvM hmove
  · exact canonicalRep_mem_of_notMem h3 hw3 hw1 hE hcard hsig hv hvσ hvM

end Gen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
