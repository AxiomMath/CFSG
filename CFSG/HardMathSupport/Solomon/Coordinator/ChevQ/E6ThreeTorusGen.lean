module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTorusDet

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Prod

variable {H G : Type*} [Group H] [Group G]

@[expose] def commProd3 (ρ : Fin 3 → H →* G)
    (hc : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s) : (Fin 3 → H) →* G where
  toFun x := ρ 0 (x 0) * ρ 1 (x 1) * ρ 2 (x 2)
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, map_mul]
    have c10 : Commute (ρ 0 (y 0)) (ρ 1 (x 1)) := (hc 1 0 (by decide) (x 1) (y 0)).symm
    have c20 : Commute (ρ 0 (y 0)) (ρ 2 (x 2)) := (hc 2 0 (by decide) (x 2) (y 0)).symm
    have c21 : Commute (ρ 1 (y 1)) (ρ 2 (x 2)) := (hc 2 1 (by decide) (x 2) (y 1)).symm
    rw [c10.mul_mul_mul_comm, (c20.mul_left c21).mul_mul_mul_comm]

theorem commProd3_apply (ρ : Fin 3 → H →* G)
    (hc : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s) (x : Fin 3 → H) :
    commProd3 ρ hc x = ρ 0 (x 0) * ρ 1 (x 1) * ρ 2 (x 2) :=
  rfl

theorem commProd3_mulSingle (ρ : Fin 3 → H →* G)
    (hc : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s) (i : Fin 3) (s : H) :
    commProd3 ρ hc (Pi.mulSingle i s) = ρ i s := by
  rw [commProd3_apply]
  fin_cases i <;> simp

theorem conj_commProd3 (ρ : Fin 3 → H →* G)
    (hc : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s) {g : G} {φ : Fin 3 → H → H}
    (hg : ∀ i w, g⁻¹ * ρ i w * g = ρ i (φ i w)) (x : Fin 3 → H) :
    g⁻¹ * commProd3 ρ hc x * g = commProd3 ρ hc (fun i => φ i (x i)) := by
  simp only [commProd3_apply, ← hg]
  group

theorem commProd3_conj_apply (ρ : Fin 3 → H →* G)
    (hc : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s) (x : Fin 3 → H) (i : Fin 3)
    (w : H) :
    commProd3 ρ hc x * ρ i w * (commProd3 ρ hc x)⁻¹ = ρ i (x i * w * (x i)⁻¹) := by
  have h : x * Pi.mulSingle i w * x⁻¹ = Pi.mulSingle i (x i * w * (x i)⁻¹) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [← commProd3_mulSingle ρ hc i w, ← commProd3_mulSingle ρ hc i (x i * w * (x i)⁻¹), ← h,
    map_mul, map_mul, map_inv]

end Prod

section Shift

variable {G : Type*} [Group G]

theorem exists_notMem_zpowers_map_eq {E : Subgroup (MulAut G)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) {σ : MulAut G} (hσ : σ ∈ E) {R : Fin 3 → Subgroup G}
    (hsh : ∀ ε ∈ E, ∃ k : Fin 3, ∀ i, (R i).map ε.toMonoidHom = R (i + k)) :
    ∃ f ∈ E, f ∉ Subgroup.zpowers σ ∧ ∀ i, (R i).map f.toMonoidHom = R i := by
  have hSh_mul : ∀ {ε₁ ε₂ : MulAut G} {k₁ k₂ : Fin 3},
      (∀ i, (R i).map ε₁.toMonoidHom = R (i + k₁)) →
      (∀ i, (R i).map ε₂.toMonoidHom = R (i + k₂)) →
        ∀ i, (R i).map (ε₁ * ε₂).toMonoidHom = R (i + (k₁ + k₂)) := by
    intro ε₁ ε₂ k₁ k₂ h₁ h₂ i
    have e : (ε₁ * ε₂).toMonoidHom = ε₁.toMonoidHom.comp ε₂.toMonoidHom := rfl
    rw [e, ← Subgroup.map_map, h₂, h₁, add_assoc, add_comm k₂ k₁]
  have hσ3 : σ ^ 3 = 1 := hE.2 σ hσ
  obtain ⟨ε₁, hε₁, hε₁σ⟩ := exists_notMem_zpowers hE hcard hσ
  obtain ⟨ε₂, hε₂, hε₂c⟩ := exists_notMem_closure_pair hE hcard hσ hε₁
  have hε₁3 : ε₁ ^ 3 = 1 := hE.2 ε₁ hε₁
  have hε₂3 : ε₂ ^ 3 = 1 := hE.2 ε₂ hε₂
  obtain ⟨s₁, hs₁⟩ := hsh ε₁ hε₁
  obtain ⟨s₂, hs₂⟩ := hsh ε₂ hε₂
  have hε₂σ : ε₂ ∉ Subgroup.zpowers σ := fun h =>
    hε₂c ((Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))) h)
  suffices h : ∃ f ∈ E, f ∉ Subgroup.zpowers σ ∧ ∀ i, (R i).map f.toMonoidHom = R (i + 0) by
    obtain ⟨f, hf, hfσ, hf0⟩ := h
    exact ⟨f, hf, hfσ, fun i => by rw [hf0, add_zero]⟩
  by_cases h₁ : s₁ = 0
  · subst h₁
    exact ⟨ε₁, hε₁, hε₁σ, hs₁⟩
  by_cases h₂ : s₂ = 0
  · subst h₂
    exact ⟨ε₂, hε₂, hε₂σ, hs₂⟩
  by_cases h12 : s₁ = s₂
  · refine ⟨ε₁ * ε₂ ^ 2, E.mul_mem hε₁ (E.pow_mem hε₂ 2), ?_, ?_⟩
    · intro hmem
      have := pow_mul_pow_mem_zpowers (a := 1) (b := 2) hε₁σ hε₂c hσ3 hε₁3 hε₂3
        (by rwa [pow_one])
      exact absurd this.1 (by norm_num)
    · have h := hSh_mul hs₁ (hSh_mul hs₂ hs₂)
      have e : s₁ + (s₂ + s₂) = 0 := by
        rw [← h12]
        exact (by decide : ∀ s : Fin 3, s + (s + s) = 0) s₁
      rw [e] at h
      rwa [pow_two]
  · refine ⟨ε₁ * ε₂, E.mul_mem hε₁ hε₂, ?_, ?_⟩
    · intro hmem
      have := pow_mul_pow_mem_zpowers (a := 1) (b := 1) hε₁σ hε₂c hσ3 hε₁3 hε₂3
        (by rwa [pow_one, pow_one])
      exact absurd this.1 (by norm_num)
    · have h := hSh_mul hs₁ hs₂
      have e : s₁ + s₂ = 0 :=
        (by decide : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → a ≠ b → a + b = 0) s₁ s₂ h₁ h₂ h12
      rwa [e] at h

end Shift

section Torus

variable
  {K : Type} [Field K]

theorem exists_dec_shift [Finite K] {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (hK : 4 ≤ Nat.card K) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hEd : E ≤ e6Inndiag K) (hsig : MulAut.conj (e6LineElt ω) ∈ E)
    {ε : MulAut (adjointGroup Tag.E6 K)} (hε : ε ∈ E) :
    ∃ (m : ModGL Tag.E6 K) (j : ℕ) (b : Fin Tag.E6.rank → Kˣ) (k : Fin 3),
      m ∈ toralRootGroup Tag.E6 K (e6LineChar ω) ∧ (k = 0 ↔ j = 0) ∧
      (∀ i, ((e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)).map ε.toMonoidHom =
        (e6LineFactor K (i + k)).subgroupOf (adjointGroup Tag.E6 K)) ∧
      ∀ h : adjointGroup Tag.E6 K, ((ε h : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        (m * canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j * rootDiagUnit Tag.E6 b) * h *
          (m * canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j * rootDiagUnit Tag.E6 b)⁻¹ := by
  obtain ⟨m, j, b, hm, hj, hform⟩ := exists_dec_of_mem h3 h1 hK hE hEd hsig hε
  obtain ⟨k, hk0, hk⟩ := exists_shift_pow (K := K) j hj
  have hle : ∀ i, e6LineFactor K i ≤ adjointGroup Tag.E6 K := fun i =>
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  exact ⟨m, j, b, k, hm, hk0,
    fun i => map_subgroupOf_eq hform (hle i) (map_conj_dec h3 h1 hm hk b i), hform⟩

theorem torusGroup_le_seitzHyperGamma_sup [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ}
    (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) (hEd : E ≤ e6Inndiag K)
    (hsig : MulAut.conj (e6LineElt ω) ∈ E) :
    torusGroup .E6 K ≤ (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
      rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  have hK4 : 4 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨L, hL⟩ : ∃ L : Subgroup (ModGL Tag.E6 K),
      L = rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := ⟨_, rfl⟩
  rw [← hL]
  have hroots : ∀ α ∈ ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)), IsRoot .E6 α :=
    fun α hα => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hα
      exact isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hi)
  have hLsup : L = ⨆ i : Fin 3, e6LineFactor K i := by rw [hL, rootSpan_eq_iSup_e6LineFactor]
  have hLker : L ≤ rootSpan .E6 K (rootCharKernel (e6LineChar ω)) :=
    le_of_eq (by rw [hL, e6Line_kernel hw3 hw1])
  have hTN : torusGroup .E6 K ≤ Subgroup.normalizer (L : Set (ModGL Tag.E6 K)) := by
    rw [hL]
    exact torusGroup_le_normalizer_rootSpan_e6 hroots
  have hM : toralRootGroup .E6 K (e6LineChar ω) = torusGroup .E6 K ⊔ L := by
    show torusGroup .E6 K ⊔ rootSpan .E6 K (rootCharKernel (e6LineChar ω)) = _
    rw [e6Line_kernel hw3 hw1, hL]
  choose ρ σf hfr hrange using exists_frame_e6Line K
  have hmemF : ∀ i s, ρ i s ∈ e6LineFactor K i := fun i s => (hrange i) ▸ ⟨s, rfl⟩
  have hFC : ∀ i, e6LineFactor K i ≤ adjointGroup Tag.E6 K := fun i =>
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hρC : ∀ i s, ρ i s ∈ adjointGroup Tag.E6 K := fun i s => hFC i (hmemF i s)
  have hcomm : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s := fun i j hij s t =>
    e6LineFactor_commute hij (hmemF i s) (hmemF j t)
  have hdiag : ∀ d d' : Fin 3 → Kˣ, Commute (diagGL3 d) (diagGL3 d') := fun d d' => by
    show diagGL3 d * diagGL3 d' = diagGL3 d' * diagGL3 d
    apply Units.ext
    show Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    exact mul_comm _ _
  obtain ⟨D, htor, hDc⟩ : ∃ D : Fin 3 → (Fin Tag.E6.rank → Kˣ) → GL (Fin 3) K,
      (∀ i b s, rootDiagUnit Tag.E6 b * ρ i s * (rootDiagUnit Tag.E6 b)⁻¹ =
        ρ i (conjSL (D i b) s)) ∧ ∀ i b c, Commute (D i b) (D i c) :=
    ⟨fun i b => diagGL3 fun j => rootChar b (σf i j 0), fun i b s => by
      rw [conjSL_diagGL3]
      exact (hfr i).torus b s, fun i b c => hdiag _ _⟩
  have hinvSL : ∀ (g : GL (Fin 3) K) (s : SpecialLinearGroup (Fin 3) K),
      conjSL g (conjSL g⁻¹ s) = s := fun g s => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have htor' : ∀ i b s, (rootDiagUnit Tag.E6 b)⁻¹ * ρ i s * rootDiagUnit Tag.E6 b =
      ρ i (conjSL (D i b)⁻¹ s) := fun i b s => by
    have h := htor i b (conjSL (D i b)⁻¹ s)
    rw [hinvSL] at h
    rw [← h]
    group
  have hFL : ∀ i, e6LineFactor K i ≤ L := fun i => by
    rw [hLsup]
    exact le_iSup (fun i => e6LineFactor K i) i
  obtain ⟨π, hπL, hLπ, hconjd, hπconj⟩ : ∃ π : (Fin 3 → SpecialLinearGroup (Fin 3) K) →*
      ModGL Tag.E6 K, (∀ x, π x ∈ L) ∧ (∀ g ∈ L, ∃ x, π x = g) ∧
      (∀ b x, (rootDiagUnit Tag.E6 b)⁻¹ * π x * rootDiagUnit Tag.E6 b =
        π (fun i => conjSL (D i b)⁻¹ (x i))) ∧
      ∀ x i w, π x * ρ i w * (π x)⁻¹ = ρ i (x i * w * (x i)⁻¹) := by
    refine ⟨commProd3 ρ hcomm, fun x => ?_, fun g hg => ?_, fun b x =>
      conj_commProd3 ρ hcomm (φ := fun i w => conjSL (D i b)⁻¹ w) (fun i w => htor' i b w) x,
      commProd3_conj_apply ρ hcomm⟩
    · rw [commProd3_apply]
      exact mul_mem (mul_mem (hFL 0 (hmemF 0 (x 0))) (hFL 1 (hmemF 1 (x 1))))
        (hFL 2 (hmemF 2 (x 2)))
    · rw [hLsup] at hg
      have hle : (⨆ i : Fin 3, e6LineFactor K i) ≤ (commProd3 ρ hcomm).range :=
        iSup_le fun i => by
          rw [← hrange i]
          rintro _ ⟨s, rfl⟩
          exact ⟨Pi.mulSingle i s, commProd3_mulSingle ρ hcomm i s⟩
      exact hle hg
  have hMdec : ∀ m ∈ toralRootGroup Tag.E6 K (e6LineChar ω), ∃ (c : Fin Tag.E6.rank → Kˣ)
      (x₀ : Fin 3 → SpecialLinearGroup (Fin 3) K), m = rootDiagUnit Tag.E6 c * π x₀ := by
    intro m hm
    rw [hM, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hm
    obtain ⟨t, ht, l, hl, rfl⟩ := Set.mem_mul.1 hm
    obtain ⟨c, rfl⟩ := torusGroup_le_range_rootDiagUnitHom_E6 ht
    obtain ⟨x₀, rfl⟩ := hLπ l hl
    exact ⟨c, x₀, rfl⟩
  have hRne : ∀ i j : Fin 3, (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K) =
      (e6LineFactor K j).subgroupOf (adjointGroup Tag.E6 K) → i = j := by
    intro i j hij
    by_contra hne
    obtain ⟨u, v, huv⟩ := exists_not_commute_SL3 (K := K) h3
    apply huv
    apply (hfr i).injective
    have hv : ρ i v ∈ e6LineFactor K j := by
      have h1 : (⟨ρ i v, hρC i v⟩ : adjointGroup Tag.E6 K) ∈
          (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K) := hmemF i v
      rw [hij] at h1
      exact h1
    rw [map_mul, map_mul]
    exact e6LineFactor_commute hne (hmemF i u) hv
  obtain ⟨f, hf, hfσ, hf0⟩ : ∃ f ∈ E, f ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)) ∧
      ∀ i, ((e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)).map f.toMonoidHom =
        (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K) :=
    exists_notMem_zpowers_map_eq hE hcard27 hsig
      (R := fun i => (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)) fun ε hε => by
        obtain ⟨_, _, _, k, _, _, hk, _⟩ := exists_dec_shift hw3 hw1 hK4 hE hEd hsig hε
        exact ⟨k, hk⟩
  obtain ⟨m, j, b, k, hm, hk0, hk, hform⟩ := exists_dec_shift hw3 hw1 hK4 hE hEd hsig hf
  have hk' : k = 0 := by
    have h := hRne _ _ ((hk 0).symm.trans (hf0 0))
    simpa using h
  obtain rfl : j = 0 := hk0.1 hk'
  simp only [pow_zero, mul_one] at hform
  obtain ⟨c, x₀, rfl⟩ := hMdec m hm
  have hft : rootDiagUnit Tag.E6 c * π x₀ * rootDiagUnit Tag.E6 b =
      rootDiagUnit Tag.E6 (c * b) * π (fun i => conjSL (D i b)⁻¹ (x₀ i)) := by
    rw [← hconjd b x₀, rootDiagUnit_mul]
    group
  obtain ⟨e, x, hfe⟩ : ∃ (e : Fin Tag.E6.rank → Kˣ) (x : Fin 3 → SpecialLinearGroup (Fin 3) K),
      ∀ h : adjointGroup Tag.E6 K, ((f h : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        rootDiagUnit Tag.E6 e * π x * h * (rootDiagUnit Tag.E6 e * π x)⁻¹ :=
    ⟨c * b, fun i => conjSL (D i b)⁻¹ (x₀ i), fun h => by rw [hform h, hft]⟩
  have hγ : ∀ i s, f ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) s) =
      (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i)
        (conjSL (D i e * SpecialLinearGroup.toGL (x i)) s) := by
    intro i s
    apply Subtype.ext
    rw [hfe]
    show rootDiagUnit Tag.E6 e * π x * ρ i s * (rootDiagUnit Tag.E6 e * π x)⁻¹ =
      ρ i (conjSL (D i e * SpecialLinearGroup.toGL (x i)) s)
    rw [map_mul, MulAut.mul_apply, conjSL_toGL, MulAut.conj_apply,
      ← htor i e (x i * s * (x i)⁻¹), ← hπconj x i s]
    group
  have hα : ∀ i, ∃ α : K, ((D i e * SpecialLinearGroup.toGL (x i) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := fun i =>
    exists_pow_three_smul_one (ρ := (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i))
      (fun s t hst => (hfr i).injective (congrArg Subtype.val hst)) (hE.2 f hf) (hγ i)
  intro t ht
  obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom_E6 ht
  have ht' : rootDiagUnit Tag.E6 a ∈ torusGroup Tag.E6 K := ht
  have hy : ∀ i, ∃ y : SpecialLinearGroup (Fin 3) K,
      conjSL (D i a)⁻¹ (x i) * y = conjSL (D i e)⁻¹ y * x i := fun i => by
    obtain ⟨α, hαi⟩ := hα i
    exact exists_conjSL_mul_eq h3 (hDc i a e) (x i) hαi
  choose y hy using hy
  have hxy : π (fun i => conjSL (D i a)⁻¹ (x i)) * π y =
      π (fun i => conjSL (D i e)⁻¹ (y i)) * π x := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (funext hy)
  have key : rootDiagUnit Tag.E6 e * π x * (rootDiagUnit Tag.E6 a * π y) =
      rootDiagUnit Tag.E6 a * π y * (rootDiagUnit Tag.E6 e * π x) := by
    have h1 : rootDiagUnit Tag.E6 e * π x * (rootDiagUnit Tag.E6 a * π y) =
        rootDiagUnit Tag.E6 e * rootDiagUnit Tag.E6 a *
          ((rootDiagUnit Tag.E6 a)⁻¹ * π x * rootDiagUnit Tag.E6 a * π y) := by group
    have h2 : rootDiagUnit Tag.E6 a * π y * (rootDiagUnit Tag.E6 e * π x) =
        rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 e *
          ((rootDiagUnit Tag.E6 e)⁻¹ * π y * rootDiagUnit Tag.E6 e * π x) := by group
    rw [h1, h2, hconjd, hconjd, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm e a, hxy]
  have hsM : rootDiagUnit Tag.E6 a * π y ∈
      torusGroup Tag.E6 K ⊔ rootSpan Tag.E6 K (rootCharKernel (e6LineChar ω)) :=
    mul_mem (Subgroup.mem_sup_left ht') (Subgroup.mem_sup_right (hLker (hπL y)))
  obtain ⟨hsC, hsχ⟩ := mem_toralCentralizer.1 (toralRootGroup_le (e6LineChar ω) hsM)
  have hσs : MulAut.conj (e6LineElt ω) (⟨_, hsC⟩ : adjointGroup Tag.E6 K) = ⟨_, hsC⟩ := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    exact hsχ
  have hfs : f (⟨_, hsC⟩ : adjointGroup Tag.E6 K) = ⟨_, hsC⟩ := by
    apply Subtype.ext
    rw [hfe]
    show rootDiagUnit Tag.E6 e * π x * (rootDiagUnit Tag.E6 a * π y) *
      (rootDiagUnit Tag.E6 e * π x)⁻¹ = rootDiagUnit Tag.E6 a * π y
    rw [key, mul_inv_cancel_right]
  have hsΓ := mem_seitzHyperGamma_of_fixed hE hcard27 hsig hf (conj_e6LineElt_ne_one hw1) hfσ
    hσs hfs
  have hmem : rootDiagUnit Tag.E6 a * π y * (π y)⁻¹ ∈
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔ L :=
    Subgroup.mul_mem_sup ⟨⟨_, hsC⟩, hsΓ, rfl⟩ (inv_mem (hπL y))
  rw [mul_inv_cancel_right] at hmem
  exact hmem

theorem e6ThreeTorusGen_holds : E6ThreeTorusGen :=
  fun _ _ _ _ h3 _ _ hw3 hw1 _ hE hcard hEd _ _ hsig =>
    torusGroup_le_seitzHyperGamma_sup h3 hw3 hw1 hE hcard hEd hsig

end Torus

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
