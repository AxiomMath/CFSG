module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTorusGen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.Fischer.Aut.Complete

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem mem_of_pow_mem_of_cube_mem {G : Type*} [Group G] {X : Subgroup G} {n : G} {j : ℕ}
    (hj : j < 3) (hj0 : j ≠ 0) (hn : n ^ j ∈ X) (h3 : n ^ 3 ∈ X) : n ∈ X := by
  interval_cases j
  · exact absurd rfl hj0
  · simpa using hn
  · have e : n = n ^ 3 * (n ^ 2)⁻¹ := by group
    rw [e]
    exact mul_mem h3 (inv_mem hn)

section Comp

variable
  {K : Type} [Field K]

theorem e6LineFactor_injective [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Function.Injective (e6LineFactor K) := by
  intro i j hij
  by_contra hne
  obtain ⟨u, v, huv⟩ := exists_not_commute_SL3 (K := K) h3
  obtain ⟨ρ, σ, hfr, hrange⟩ := exists_frame_e6Line K i
  apply huv
  apply hfr.injective
  have hu : ρ u ∈ e6LineFactor K i := hrange ▸ ⟨u, rfl⟩
  have hv : ρ v ∈ e6LineFactor K j := hij ▸ hrange ▸ ⟨v, rfl⟩
  rw [map_mul, map_mul]
  exact e6LineFactor_commute hne hu hv

theorem canonicalRep_e6LineWeyl_pow_three_mem [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ}
    (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ 3 ∈ toralRootGroup .E6 K (e6LineChar ω) := by
  have hnX : canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      toralCentralizer .E6 K (e6LineChar ω) :=
    canonicalRep_mem_toralCentralizer (e6LineWeyl_mem_stabilizer hw3 hw1)
  obtain ⟨m, hm, j, hj, he⟩ := e6Line_centralizer_mul hw3 hw1 (pow_mem hnX 3)
  obtain ⟨k, hk0, hk⟩ := exists_shift_pow (K := K) j hj
  have h3map : (e6LineFactor K 0).map
      (MulAut.conj (canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ 3)).toMonoidHom =
        e6LineFactor K 0 := by
    rw [pow_three, map_conj_mul_aux, map_conj_mul_aux, e6LineFactor_conj, e6LineFactor_conj,
      e6LineFactor_conj]
    rfl
  have hmk : (e6LineFactor K 0).map
      (MulAut.conj (canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ 3)).toMonoidHom =
        e6LineFactor K (0 + k) := by
    rw [he, map_conj_mul_aux, hk,
      map_conj_eq_of_mem_normalizer_aux (e6LineFactor_normalizer hw3 hw1 _ hm)]
  have hk' : k = 0 := by
    have h := e6LineFactor_injective h3 (h3map.symm.trans hmk)
    rw [zero_add] at h
    exact h.symm
  obtain rfl : j = 0 := hk0.1 hk'
  rw [he, pow_zero, mul_one]
  exact hm

theorem mem_toralCentralizer_of_conj_commute [Finite K] {ω : Kˣ} {v : adjointGroup Tag.E6 K}
    (h : MulAut.conj v * MulAut.conj (e6LineElt ω) =
      MulAut.conj (e6LineElt ω) * MulAut.conj v) :
    (v : ModGL .E6 K) ∈ toralCentralizer .E6 K (e6LineChar ω) := by
  rw [← map_mul, ← map_mul] at h
  have hc := congrArg Subtype.val (CFSG.Fischer.mulAutConj_injective center_adjointGroup_eq_bot h)
  simp only [Subgroup.coe_mul, coe_e6LineElt] at hc
  refine mem_toralCentralizer.2 ⟨v.2, ?_⟩
  rw [← hc, mul_inv_cancel_right]

theorem exists_inner_notMem_zpowers [Finite K] {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) (hEd : E ≤ e6Inndiag K)
    (hEi : ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K))
    {σ : MulAut (adjointGroup Tag.E6 K)} (hσ : σ ∈ E) :
    ∃ v : adjointGroup Tag.E6 K, MulAut.conj v ∈ E ∧ MulAut.conj v ∉ Subgroup.zpowers σ := by
  by_contra hno
  push Not at hno
  have h9 : Nat.card ↥(E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) = 3 ^ 2 :=
    card_inf_innerAut_of_le_e6Inndiag K hcard hEd hEi
  have hle : E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) ≤ Subgroup.zpowers σ := by
    intro ε hε
    obtain ⟨hεE, hεI⟩ := Subgroup.mem_inf.1 hε
    obtain ⟨v, rfl⟩ := CFSG.Fischer.mem_innerAut.1 hεI
    exact hno v hεE
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [h9, Nat.card_zpowers] at hdvd
  have h33 := Nat.dvd_trans hdvd (orderOf_dvd_of_pow_eq_one (hE.2 σ hσ))
  norm_num at h33

theorem canonicalRep_mem_of_notMem [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ}
    (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hsig : MulAut.conj (e6LineElt ω) ∈ E) {v : adjointGroup Tag.E6 K}
    (hv : MulAut.conj v ∈ E)
    (hvσ : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)))
    (hvM : (v : ModGL .E6 K) ∉ toralRootGroup .E6 K (e6LineChar ω)) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
        toralRootGroup .E6 K (e6LineChar ω) := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  have hcomm : MulAut.conj v * MulAut.conj (e6LineElt ω) =
      MulAut.conj (e6LineElt ω) * MulAut.conj v :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hv⟩ : E) ⟨_, hsig⟩)
  have hvX := mem_toralCentralizer_of_conj_commute hcomm
  obtain ⟨m, hm, j, hj, he⟩ := e6Line_centralizer_mul hw3 hw1 hvX
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at he
    exact hvM (he ▸ hm)
  have hσv : MulAut.conj (e6LineElt ω) v = v := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    exact (mem_toralCentralizer.1 hvX).2
  have hvv : MulAut.conj v v = v := by
    rw [MulAut.conj_apply, mul_inv_cancel_right]
  have hvΓ := mem_seitzHyperGamma_of_fixed hE hcard27 hsig hv (conj_e6LineElt_ne_one hw1) hvσ
    hσv hvv
  have hnj : canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j ∈
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
        toralRootGroup .E6 K (e6LineChar ω) := by
    have e : canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j = m⁻¹ * (v : ModGL .E6 K) := by
      rw [he, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right (inv_mem hm)) (Subgroup.mem_sup_left ⟨v, hvΓ, rfl⟩)
  exact mem_of_pow_mem_of_cube_mem hj hj0 hnj
    (Subgroup.mem_sup_right (canonicalRep_e6LineWeyl_pow_three_mem h3 hw3 hw1))

theorem exists_e6LineFrames (K : Type) [Field K] :
    ∃ (ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K)
      (D : Fin 3 → (Fin Tag.E6.rank → Kˣ) → GL (Fin 3) K),
      (∀ i, Function.Injective (ρ i)) ∧ (∀ i, (ρ i).range = e6LineFactor K i) ∧
      (∀ i b s, rootDiagUnit Tag.E6 b * ρ i s * (rootDiagUnit Tag.E6 b)⁻¹ =
        ρ i (conjSL (D i b) s)) ∧ ∀ i b c, Commute (D i b) (D i c) := by
  choose ρ σf hfr hrange using exists_frame_e6Line K
  have hdiag : ∀ d d' : Fin 3 → Kˣ, Commute (diagGL3 d) (diagGL3 d') := fun d d' => by
    show diagGL3 d * diagGL3 d' = diagGL3 d' * diagGL3 d
    apply Units.ext
    show Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    exact mul_comm _ _
  refine ⟨ρ, fun i b => diagGL3 fun j => rootChar b (σf i j 0), fun i => (hfr i).injective,
    hrange, fun i b s => ?_, fun i b c => hdiag _ _⟩
  rw [conjSL_diagGL3]
  exact (hfr i).torus b s

theorem exists_commProd_of_frames {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    {D : Fin 3 → (Fin Tag.E6.rank → Kˣ) → GL (Fin 3) K}
    (hrange : ∀ i, (ρ i).range = e6LineFactor K i)
    (htor : ∀ i b s, rootDiagUnit Tag.E6 b * ρ i s * (rootDiagUnit Tag.E6 b)⁻¹ =
      ρ i (conjSL (D i b) s)) :
    ∃ π : (Fin 3 → SpecialLinearGroup (Fin 3) K) →* ModGL Tag.E6 K,
      (∀ x, π x = ρ 0 (x 0) * ρ 1 (x 1) * ρ 2 (x 2)) ∧
      (∀ x, π x ∈ rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)))) ∧
      (∀ g ∈ rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))), ∃ x, π x = g) ∧
      (∀ b x, (rootDiagUnit Tag.E6 b)⁻¹ * π x * rootDiagUnit Tag.E6 b =
        π (fun i => conjSL (D i b)⁻¹ (x i))) ∧
      (∀ b x, rootDiagUnit Tag.E6 b * π x * (rootDiagUnit Tag.E6 b)⁻¹ =
        π (fun i => conjSL (D i b) (x i))) ∧
      (∀ x i w, π x * ρ i w * (π x)⁻¹ = ρ i (x i * w * (x i)⁻¹)) ∧
      ∀ m ∈ toralRootGroup Tag.E6 K (e6LineChar ω), ∃ (c : Fin Tag.E6.rank → Kˣ)
        (x : Fin 3 → SpecialLinearGroup (Fin 3) K),
        rootDiagUnit Tag.E6 c ∈ torusGroup Tag.E6 K ∧ m = rootDiagUnit Tag.E6 c * π x := by
  have hroots : ∀ α ∈ ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)), IsRoot .E6 α :=
    fun α hα => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hα
      exact isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hi)
  have hTN : torusGroup .E6 K ≤ Subgroup.normalizer
      (rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) :
        Set (ModGL Tag.E6 K)) :=
    torusGroup_le_normalizer_rootSpan_e6 hroots
  have hM : toralRootGroup .E6 K (e6LineChar ω) = torusGroup .E6 K ⊔
      rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := by
    show torusGroup .E6 K ⊔ rootSpan .E6 K (rootCharKernel (e6LineChar ω)) = _
    rw [e6Line_kernel hw3 hw1]
  have hmemF : ∀ i s, ρ i s ∈ e6LineFactor K i := fun i s => (hrange i) ▸ ⟨s, rfl⟩
  have hcomm : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s := fun i j hij s t =>
    e6LineFactor_commute hij (hmemF i s) (hmemF j t)
  have hinvSL : ∀ (g : GL (Fin 3) K) (s : SpecialLinearGroup (Fin 3) K),
      conjSL g (conjSL g⁻¹ s) = s := fun g s => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have htor' : ∀ i b s, (rootDiagUnit Tag.E6 b)⁻¹ * ρ i s * rootDiagUnit Tag.E6 b =
      ρ i (conjSL (D i b)⁻¹ s) := fun i b s => by
    have h := htor i b (conjSL (D i b)⁻¹ s)
    rw [hinvSL] at h
    rw [← h]
    group
  have hFL : ∀ i, e6LineFactor K i ≤
      rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := fun i => by
    rw [rootSpan_eq_iSup_e6LineFactor]
    exact le_iSup (fun i => e6LineFactor K i) i
  have hle : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
      (commProd3 ρ hcomm).range := by
    rw [rootSpan_eq_iSup_e6LineFactor]
    refine iSup_le fun i => ?_
    rw [← hrange i]
    rintro _ ⟨s, rfl⟩
    exact ⟨Pi.mulSingle i s, commProd3_mulSingle ρ hcomm i s⟩
  refine ⟨commProd3 ρ hcomm, fun x => commProd3_apply ρ hcomm x, fun x => ?_, fun g hg => hle hg,
    fun b x => conj_commProd3 ρ hcomm (φ := fun i w => conjSL (D i b)⁻¹ w)
      (fun i w => htor' i b w) x,
    fun b x => ?_, commProd3_conj_apply ρ hcomm, fun m hm => ?_⟩
  · rw [commProd3_apply]
    exact mul_mem (mul_mem (hFL 0 (hmemF 0 (x 0))) (hFL 1 (hmemF 1 (x 1))))
      (hFL 2 (hmemF 2 (x 2)))
  · have h := conj_commProd3 ρ hcomm (g := (rootDiagUnit Tag.E6 b)⁻¹)
      (φ := fun i w => conjSL (D i b) w) (fun i w => by rw [inv_inv]; exact htor i b w) x
    rwa [inv_inv] at h
  · rw [hM, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hm
    obtain ⟨t, ht, l, hl, rfl⟩ := Set.mem_mul.1 hm
    obtain ⟨c, rfl⟩ := torusGroup_le_range_rootDiagUnitHom_E6 ht
    obtain ⟨x₀, rfl⟩ := hle hl
    exact ⟨c, x₀, ht, rfl⟩

theorem canonicalRep_mem_of_shift [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ}
    (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hsig : MulAut.conj (e6LineElt ω) ∈ E) {v : adjointGroup Tag.E6 K}
    (hv : MulAut.conj v ∈ E)
    (hvσ : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)))
    (hvM : (v : ModGL .E6 K) ∈ toralRootGroup .E6 K (e6LineChar ω))
    {f : MulAut (adjointGroup Tag.E6 K)} (hf : f ∈ E) {m₀ : ModGL Tag.E6 K} {j : ℕ}
    {b : Fin Tag.E6.rank → Kˣ} (hm₀ : m₀ ∈ toralRootGroup Tag.E6 K (e6LineChar ω)) (hj : j < 3)
    (hj0 : j ≠ 0)
    (hform : ∀ h : adjointGroup Tag.E6 K, ((f h : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      (m₀ * canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j * rootDiagUnit Tag.E6 b) * h *
        (m₀ * canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j * rootDiagUnit Tag.E6 b)⁻¹) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
        toralRootGroup .E6 K (e6LineChar ω) := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  have hnX : canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      toralCentralizer .E6 K (e6LineChar ω) :=
    canonicalRep_mem_toralCentralizer (e6LineWeyl_mem_stabilizer hw3 hw1)
  have hn3 := canonicalRep_e6LineWeyl_pow_three_mem h3 hw3 hw1
  generalize canonicalRep (coxeterSystem .E6) K e6LineWeyl = n at hform hnX hn3 ⊢
  obtain ⟨ρ, D, hinj, hrange, htor, hDc⟩ := exists_e6LineFrames K
  obtain ⟨π, -, hπL, -, hconjd, hconjd', hπconj, hMdec⟩ := exists_commProd_of_frames hw3 hw1
    hrange htor
  have hFC : ∀ i, e6LineFactor K i ≤ adjointGroup Tag.E6 K := fun i =>
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hρC : ∀ i s, ρ i s ∈ adjointGroup Tag.E6 K := fun i s =>
    hFC i ((hrange i) ▸ ⟨s, rfl⟩)
  have hπM : ∀ x, π x ∈ toralRootGroup .E6 K (e6LineChar ω) := fun x => by
    have hle : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
        toralRootGroup .E6 K (e6LineChar ω) := by
      show _ ≤ torusGroup .E6 K ⊔ rootSpan .E6 K (rootCharKernel (e6LineChar ω))
      rw [e6Line_kernel hw3 hw1]
      exact le_sup_right
    exact hle (hπL x)
  have hfv : f v = v := by
    have hcomm : f * MulAut.conj v = MulAut.conj v * f :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hf⟩ : E) ⟨_, hv⟩)
    apply CFSG.Fischer.mulAutConj_injective center_adjointGroup_eq_bot
    refine MulEquiv.ext fun y => ?_
    have h := congrArg (fun φ : MulAut (adjointGroup Tag.E6 K) => φ (f.symm y)) hcomm
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h
    simp only [MulAut.conj_apply]
    exact h
  have hftv : (m₀ * n ^ j * rootDiagUnit Tag.E6 b) * (v : ModGL Tag.E6 K) *
      (m₀ * n ^ j * rootDiagUnit Tag.E6 b)⁻¹ = v := by
    rw [← hform v, hfv]
  obtain ⟨c, x, -, hvcx⟩ := hMdec _ hvM
  have hγ : ∀ i s, MulAut.conj v ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) s) =
      (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i)
        (conjSL (D i c * SpecialLinearGroup.toGL (x i)) s) := by
    intro i s
    apply Subtype.ext
    show (v : ModGL Tag.E6 K) * ρ i s * (v : ModGL Tag.E6 K)⁻¹ =
      ρ i (conjSL (D i c * SpecialLinearGroup.toGL (x i)) s)
    rw [hvcx, map_mul, MulAut.mul_apply, conjSL_toGL, MulAut.conj_apply,
      ← htor i c (x i * s * (x i)⁻¹), ← hπconj x i s]
    group
  have hα : ∀ i, ∃ α : K, ((D i c * SpecialLinearGroup.toGL (x i) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := fun i =>
    exists_pow_three_smul_one (ρ := (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i))
      (fun s t hst => hinj i (congrArg Subtype.val hst)) (hE.2 _ hv) (hγ i)
  have hz : ∀ i, ∃ z : GL (Fin 3) K, z * (D i c * SpecialLinearGroup.toGL (x i)) =
      (D i c * SpecialLinearGroup.toGL (x i)) * z ∧
        GeneralLinearGroup.det z = (GeneralLinearGroup.det (D i b))⁻¹ := fun i => by
    obtain ⟨α, hαi⟩ := hα i
    exact exists_commute_det_eq_of_pow_three h3 hαi _
  choose z hzc hzd using hz
  have hy1 : ∀ i, ((D i b * z i : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := fun i => by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, hzd, mul_inv_cancel, Units.val_one]
  obtain ⟨y, hyGL⟩ : ∃ y : Fin 3 → SpecialLinearGroup (Fin 3) K,
      ∀ i, SpecialLinearGroup.toGL (y i) = D i b * z i :=
    ⟨fun i => ⟨_, hy1 i⟩, fun i => Units.ext rfl⟩
  have hfac : ∀ i, conjSL (D i c)⁻¹ (y i) * x i * (y i)⁻¹ = conjSL (D i b) (x i) := fun i => by
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv SpecialLinearGroup.toGL (y i), toGL_conjSL_eq_mul,
      toGL_conjSL_eq_mul, hyGL, inv_inv]
    have hAB : D i b * D i c = D i c * D i b := hDc i b c
    have hZ : z i * (D i c * SpecialLinearGroup.toGL (x i)) * (z i)⁻¹ =
        D i c * SpecialLinearGroup.toGL (x i) := by
      rw [hzc i, mul_inv_cancel_right]
    calc (D i c)⁻¹ * (D i b * z i) * D i c * SpecialLinearGroup.toGL (x i) * (D i b * z i)⁻¹
        = (D i c)⁻¹ * D i b * (z i * (D i c * SpecialLinearGroup.toGL (x i)) * (z i)⁻¹) *
            (D i b)⁻¹ := by group
      _ = (D i c)⁻¹ * (D i b * D i c) * SpecialLinearGroup.toGL (x i) * (D i b)⁻¹ := by
          rw [hZ]; group
      _ = D i b * SpecialLinearGroup.toGL (x i) * (D i b)⁻¹ := by rw [hAB]; group
  have hkey : π y * (v : ModGL Tag.E6 K) * (π y)⁻¹ =
      rootDiagUnit Tag.E6 b * (v : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b)⁻¹ := by
    rw [hvcx]
    have hbc : rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 c =
        rootDiagUnit Tag.E6 c * rootDiagUnit Tag.E6 b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have h1 : π y * (rootDiagUnit Tag.E6 c * π x) * (π y)⁻¹ = rootDiagUnit Tag.E6 c *
        ((rootDiagUnit Tag.E6 c)⁻¹ * π y * rootDiagUnit Tag.E6 c * π x * (π y)⁻¹) := by group
    have h2 : rootDiagUnit Tag.E6 b * (rootDiagUnit Tag.E6 c * π x) *
        (rootDiagUnit Tag.E6 b)⁻¹ = rootDiagUnit Tag.E6 c *
          (rootDiagUnit Tag.E6 b * π x * (rootDiagUnit Tag.E6 b)⁻¹) := by
      calc rootDiagUnit Tag.E6 b * (rootDiagUnit Tag.E6 c * π x) * (rootDiagUnit Tag.E6 b)⁻¹
          = rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 c * π x *
              (rootDiagUnit Tag.E6 b)⁻¹ := by group
        _ = _ := by rw [hbc]; group
    rw [h1, h2, hconjd c y, hconjd' b x, ← map_inv π y, ← map_mul π, ← map_mul π]
    congr 2
    funext i
    exact hfac i
  have hgX : m₀ * n ^ j * π y ∈ toralCentralizer .E6 K (e6LineChar ω) :=
    mul_mem (mul_mem (toralRootGroup_le _ hm₀) (pow_mem hnX j)) (toralRootGroup_le _ (hπM y))
  obtain ⟨hgC, hgχ⟩ := mem_toralCentralizer.1 hgX
  have hgv : (m₀ * n ^ j * π y) * (v : ModGL Tag.E6 K) * (m₀ * n ^ j * π y)⁻¹ = v := by
    calc (m₀ * n ^ j * π y) * (v : ModGL Tag.E6 K) * (m₀ * n ^ j * π y)⁻¹
        = (m₀ * n ^ j) * (π y * (v : ModGL Tag.E6 K) * (π y)⁻¹) * (m₀ * n ^ j)⁻¹ := by group
      _ = (m₀ * n ^ j) * (rootDiagUnit Tag.E6 b * (v : ModGL Tag.E6 K) *
            (rootDiagUnit Tag.E6 b)⁻¹) * (m₀ * n ^ j)⁻¹ := by rw [hkey]
      _ = (m₀ * n ^ j * rootDiagUnit Tag.E6 b) * (v : ModGL Tag.E6 K) *
            (m₀ * n ^ j * rootDiagUnit Tag.E6 b)⁻¹ := by group
      _ = v := hftv
  have hσg : MulAut.conj (e6LineElt ω) (⟨_, hgC⟩ : adjointGroup Tag.E6 K) = ⟨_, hgC⟩ := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    exact hgχ
  have hvg : MulAut.conj v (⟨_, hgC⟩ : adjointGroup Tag.E6 K) = ⟨_, hgC⟩ := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    show (v : ModGL Tag.E6 K) * (m₀ * n ^ j * π y) * (v : ModGL Tag.E6 K)⁻¹ = m₀ * n ^ j * π y
    have hc : (m₀ * n ^ j * π y) * (v : ModGL Tag.E6 K) =
        (v : ModGL Tag.E6 K) * (m₀ * n ^ j * π y) := by
      calc (m₀ * n ^ j * π y) * (v : ModGL Tag.E6 K)
          = ((m₀ * n ^ j * π y) * (v : ModGL Tag.E6 K) * (m₀ * n ^ j * π y)⁻¹) *
              (m₀ * n ^ j * π y) := by group
        _ = _ := by rw [hgv]
    rw [← hc, mul_inv_cancel_right]
  have hgΓ := mem_seitzHyperGamma_of_fixed hE hcard27 hsig hv (conj_e6LineElt_ne_one hw1) hvσ
    hσg hvg
  have hnj : n ^ j ∈ (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
      toralRootGroup .E6 K (e6LineChar ω) := by
    have e : n ^ j = m₀⁻¹ * (m₀ * n ^ j * π y) * (π y)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_right (inv_mem hm₀))
      (Subgroup.mem_sup_left ⟨⟨_, hgC⟩, hgΓ, rfl⟩)) (Subgroup.mem_sup_right (inv_mem (hπM y)))
  exact mem_of_pow_mem_of_cube_mem hj hj0 hnj (Subgroup.mem_sup_right hn3)

theorem canonicalRep_mem_of_moves [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ}
    (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) (hEd : E ≤ e6Inndiag K)
    (hsig : MulAut.conj (e6LineElt ω) ∈ E) {v : adjointGroup Tag.E6 K}
    (hv : MulAut.conj v ∈ E)
    (hvσ : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj (e6LineElt ω)))
    (hvM : (v : ModGL .E6 K) ∈ toralRootGroup .E6 K (e6LineChar ω))
    {f : MulAut (adjointGroup Tag.E6 K)} (hf : f ∈ E) {i : Fin 3}
    (hfi : ((e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)).map f.toMonoidHom ≠
      (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K)) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl ∈
      (seitzHyperGamma 3 E).map (adjointGroup Tag.E6 K).subtype ⊔
        toralRootGroup .E6 K (e6LineChar ω) := by
  have hK4 : 4 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨m₀, j, b, hm₀, hj, hform⟩ := exists_dec_of_mem hw3 hw1 hK4 hE hEd hsig hf
  obtain ⟨k, hk0, hk⟩ := exists_shift_pow (K := K) j hj
  have hle : e6LineFactor K i ≤ adjointGroup Tag.E6 K :=
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hmap := map_subgroupOf_eq hform hle (map_conj_dec hw3 hw1 hm₀ hk b i)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [hk0.2 rfl, add_zero] at hmap
    exact hfi hmap
  exact canonicalRep_mem_of_shift h3 hw3 hw1 hE hcard hsig hv hvσ hvM hf hm₀ hj hj0 hform

end Comp

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
