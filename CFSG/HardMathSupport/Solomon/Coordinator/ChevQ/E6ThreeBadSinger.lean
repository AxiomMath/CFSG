module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadSingerFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTorusGen

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4
open CFSG.RankThree.PartOne.KE (diagGL3)
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)
open scoped MatrixGroups

section Mat

variable {K : Type*} [Field K]

theorem exists_mul_eq_smul_mul_of_commute {G : Type*} [Group G]
    {ρ : SpecialLinearGroup (Fin 3) K →* G} (hρ : Function.Injective ρ) {ε δ : MulAut G}
    (hεδ : ε * δ = δ * ε) {γ Δ : GL (Fin 3) K} (hγ : ∀ s, ε (ρ s) = ρ (conjSL γ s))
    (hΔ : ∀ s, δ (ρ s) = ρ (conjSL Δ s)) :
    ∃ r : K, (γ : Matrix (Fin 3) (Fin 3) K) * Δ = r • ((Δ : Matrix (Fin 3) (Fin 3) K) * γ) := by
  have h2 : conjSL (γ * Δ) = conjSL (Δ * γ) := by
    refine MulEquiv.ext fun s => hρ ?_
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, ← hγ (conjSL Δ s), ← hΔ s,
      ← hΔ (conjSL γ s), ← hγ s]
    exact DFunLike.congr_fun hεδ (ρ s)
  have h1 : conjSL (γ * Δ * (Δ * γ)⁻¹) = 1 := by
    rw [map_mul, h2, map_inv, mul_inv_cancel]
  obtain ⟨r, hr⟩ := exists_smul_one_of_conjSL_eq_one h1
  refine ⟨r, ?_⟩
  have h3 : ((γ * Δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((γ * Δ * (Δ * γ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((Δ * γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  rw [← Units.val_mul, ← Units.val_mul, h3, hr, Matrix.smul_mul, Matrix.one_mul]

theorem coe_eq_diagonal_mul_of_toGL_eq {s : SpecialLinearGroup (Fin 3) K}
    {B M : GL (Fin 3) K} {b d : Fin 3 → K} {k : ℕ}
    (hB : ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal b)
    (hM : (M : Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ k)
    (hs : SpecialLinearGroup.toGL s = B⁻¹ * M) :
    (s : Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => b i * d i) * signedCycMat ^ k := by
  have h := congrArg Units.val hs
  rw [SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul, hB, hM, ← Matrix.mul_assoc,
    diagonal_mul_diagonal] at h
  exact h

end Mat

section Main

variable
  {K : Type} [Field K]

theorem exists_monomial_of_e6D0Char_mem [Finite K] (h3 : 3 ∣ Nat.card K - 1) {ω : Kˣ}
    (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hEd : E ≤ e6Inndiag K)
    (hEi : ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K))
    (hsig : MulAut.conj (e6LineElt ω) ∈ E) (hδ : rootDiagAutHom .E6 K (e6D0Char ω) ∈ E) :
    ∃ φ ∈ e6Inndiag K, ∃ (ν : List (Fin Tag.E6.rank)) (a : Fin Tag.E6.rank → Kˣ),
      MulAut.conj (e6LineElt ω) ∈ E.map (MulAut.congr φ).toMonoidHom ∧
      rootDiagAutHom .E6 K (e6D0Char ω) ∈ E.map (MulAut.congr φ).toMonoidHom ∧
      MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a ∈
        E.map (MulAut.congr φ).toMonoidHom ∧
      MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a ∉
        CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  have hK4 : 4 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨f, hf, hfi⟩ := SetLike.not_le_iff_exists.1 hEi
  obtain ⟨L, hL⟩ : ∃ L : Subgroup (ModGL Tag.E6 K),
      L = rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := ⟨_, rfl⟩
  have hroots : ∀ α ∈ ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)), IsRoot .E6 α :=
    fun α hα => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hα
      exact isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hi)
  have hLsup : L = ⨆ i : Fin 3, e6LineFactor K i := by rw [hL, rootSpan_eq_iSup_e6LineFactor]
  have hTN : torusGroup .E6 K ≤ Subgroup.normalizer (L : Set (ModGL Tag.E6 K)) := by
    rw [hL]
    exact torusGroup_le_normalizer_rootSpan_e6 hroots
  have hM : toralRootGroup .E6 K (e6LineChar ω) = torusGroup .E6 K ⊔ L := by
    show torusGroup .E6 K ⊔ rootSpan .E6 K (rootCharKernel (e6LineChar ω)) = _
    rw [e6Line_kernel hw3 hw1, hL]
  choose ρ σf hfr hrange h01 h12 hmono using exists_frame_e6Line_mono K
  have hmemF : ∀ i s, ρ i s ∈ e6LineFactor K i := fun i s => (hrange i) ▸ ⟨s, rfl⟩
  have hFC : ∀ i, e6LineFactor K i ≤ adjointGroup Tag.E6 K := fun i =>
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hρC : ∀ i s, ρ i s ∈ adjointGroup Tag.E6 K := fun i s => hFC i (hmemF i s)
  have hcomm : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s := fun i j hij s t =>
    e6LineFactor_commute hij (hmemF i s) (hmemF j t)
  obtain ⟨D, hDv⟩ : ∃ D : Fin 3 → (Fin Tag.E6.rank → Kˣ) → GL (Fin 3) K,
      ∀ i b, D i b = diagGL3 fun j => rootChar b (σf i j 0) := ⟨_, fun _ _ => rfl⟩
  have htor : ∀ i b s, rootDiagUnit Tag.E6 b * ρ i s * (rootDiagUnit Tag.E6 b)⁻¹ =
      ρ i (conjSL (D i b) s) := fun i b s => by
    rw [hDv, conjSL_diagGL3]
    exact (hfr i).torus b s
  have hinvSL : ∀ (g : GL (Fin 3) K) (s : SpecialLinearGroup (Fin 3) K),
      conjSL g (conjSL g⁻¹ s) = s := fun g s => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have htor' : ∀ i b s, (rootDiagUnit Tag.E6 b)⁻¹ * ρ i s * rootDiagUnit Tag.E6 b =
      ρ i (conjSL (D i b)⁻¹ s) := fun i b s => by
    have h := htor i b (conjSL (D i b)⁻¹ s)
    rw [hinvSL] at h
    rw [← h]
    group
  obtain ⟨π, hLπ, hconjd, hπconj, hπs, hπa⟩ : ∃ π : (Fin 3 → SpecialLinearGroup (Fin 3) K) →*
      ModGL Tag.E6 K, (∀ g ∈ L, ∃ x, π x = g) ∧
      (∀ b x, (rootDiagUnit Tag.E6 b)⁻¹ * π x * rootDiagUnit Tag.E6 b =
        π (fun i => conjSL (D i b)⁻¹ (x i))) ∧
      (∀ x i w, π x * ρ i w * (π x)⁻¹ = ρ i (x i * w * (x i)⁻¹)) ∧
      (∀ i s, π (Pi.mulSingle i s) = ρ i s) ∧
      ∀ x, π x = ρ 0 (x 0) * ρ 1 (x 1) * ρ 2 (x 2) := by
    refine ⟨commProd3 ρ hcomm, fun g hg => ?_, fun b x =>
      conj_commProd3 ρ hcomm (φ := fun i w => conjSL (D i b)⁻¹ w) (fun i w => htor' i b w) x,
      commProd3_conj_apply ρ hcomm, commProd3_mulSingle ρ hcomm, commProd3_apply ρ hcomm⟩
    rw [hLsup] at hg
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
  have hfδ : f * rootDiagAutHom .E6 K (e6D0Char ω) = rootDiagAutHom .E6 K (e6D0Char ω) * f :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨f, hf⟩ : E) ⟨_, hδ⟩)
  obtain ⟨m, j, b, k, hm, hk0, hk, hform⟩ := exists_dec_shift hw3 hw1 hK4 hE hEd hsig hf
  have hk' : k = 0 := by
    have h := hk 0
    rw [zero_add] at h
    exact shift_eq_zero_of_commute_e6D0Char hw1 hfδ h
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
  have hδρ : ∀ i s, rootDiagAutHom .E6 K (e6D0Char ω)
      ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) s) =
      (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) (conjSL (D i (e6D0Char ω)) s) :=
    fun i s => Subtype.ext (htor i _ s)
  have hinj : ∀ i, Function.Injective ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i)) :=
    fun i s t hst => (hfr i).injective (congrArg Subtype.val hst)
  have hα : ∀ i, ∃ α : K, ((D i e * SpecialLinearGroup.toGL (x i) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := fun i =>
    exists_pow_three_smul_one (hinj i) (hE.2 f hf) (hγ i)
  have hω3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hw3, Units.val_one]
  have hω1 : (ω : K) ≠ 1 := fun h => hw1 (Units.val_eq_one.1 h)
  have hmono12 : ∀ i : Fin 3, i ≠ 0 → ∃ (d : Fin 3 → K) (n : ℕ),
      ((D i e * SpecialLinearGroup.toGL (x i) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal d * signedCycMat ^ n := by
    intro i hi
    obtain ⟨r, hr⟩ := exists_mul_eq_smul_mul_of_commute (hinj i) hfδ (hγ i) (hδρ i)
    have hΔ : ((D i (e6D0Char ω) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal ![1, (ω : K) ^ 2, (ω : K)] := by
      rw [hDv]
      exact congrArg diagonal (rootChar_e6D0Char_frame hw3 (hfr i) hi (h01 i) (h12 i))
    rw [hΔ] at hr
    exact eq_diagonal_mul_signedCycMat_pow hω3 hω1 hr
  obtain ⟨α₀, hα₀⟩ := hα 0
  obtain ⟨z, d₀, n₀, hz⟩ :=
    exists_conj_eq_diagonal_mul_signedCycMat_pow (exists_isPrimitiveRoot_three h3) hα₀
  obtain ⟨x', hx'⟩ : ∃ x' : Fin 3 → SpecialLinearGroup (Fin 3) K,
      x' = Pi.mulSingle 0 (conjSL (D 0 e)⁻¹ z) * x * Pi.mulSingle 0 z⁻¹ := ⟨_, rfl⟩
  have hkey : ρ 0 z * (rootDiagUnit Tag.E6 e * π x) * (ρ 0 z)⁻¹ =
      rootDiagUnit Tag.E6 e * π x' := by
    rw [hx', map_mul, map_mul, hπs, hπs, ← htor' 0 e z, map_inv]
    group
  have hx'0 : x' 0 = conjSL (D 0 e)⁻¹ z * x 0 * z⁻¹ := by
    rw [hx', Pi.mul_apply, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  have hx'i : ∀ i : Fin 3, i ≠ 0 → x' i = x i := fun i hi => by
    rw [hx', Pi.mul_apply, Pi.mul_apply, Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi,
      one_mul, mul_one]
  have hdinv : ∀ i, (((D i e)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun j => (((rootChar e (σf i j 0))⁻¹ : Kˣ) : K) := fun i =>
    (congrArg (fun g : GL (Fin 3) K => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (hDv i e)).trans rfl
  have hmon : ∀ i, ρ i (x' i) ∈ monomialSubgroup Tag.E6 K := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have hs : SpecialLinearGroup.toGL (x' 0) = (D 0 e)⁻¹ *
          (SpecialLinearGroup.toGL z * (D 0 e * SpecialLinearGroup.toGL (x 0)) *
            (SpecialLinearGroup.toGL z)⁻¹) := by
        rw [hx'0, map_mul, map_mul, toGL_conjSL_eq_mul, map_inv, inv_inv]
        group
      exact frame_mem_monomialSubgroup (hfr 0) (hmono 0)
        (coe_eq_diagonal_mul_of_toGL_eq (hdinv 0) hz hs)
    · obtain ⟨d, n, hd⟩ := hmono12 i hi
      have hs : SpecialLinearGroup.toGL (x' i) =
          (D i e)⁻¹ * (D i e * SpecialLinearGroup.toGL (x i)) := by
        rw [hx'i i hi, inv_mul_cancel_left]
      exact frame_mem_monomialSubgroup (hfr i) (hmono i)
        (coe_eq_diagonal_mul_of_toGL_eq (hdinv i) hd hs)
  have hπmon : π x' ∈ monomialSubgroup Tag.E6 K := by
    rw [hπa]
    exact mul_mem (mul_mem (hmon 0) (hmon 1)) (hmon 2)
  obtain ⟨ν, a, hνa⟩ := exists_weylWordElt_of_mem_monomialSubgroup hπmon e
  obtain ⟨U, hU⟩ : ∃ U : adjointGroup Tag.E6 K, (U : ModGL Tag.E6 K) = ρ 0 z :=
    ⟨⟨ρ 0 z, hρC 0 z⟩, rfl⟩
  have hUh : (U : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 (e6LineChar ω) =
      rootDiagUnit Tag.E6 (e6LineChar ω) * U := by
    have hS : (e6LineRoots 0 : Set (Fin Tag.E6.rank → ℤ)) ⊆ rootCharKernel (e6LineChar ω) := by
      rw [e6Line_kernel hw3 hw1]
      exact Set.subset_iUnion (fun i => (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) 0
    rw [hU]
    exact Subgroup.mem_centralizer_singleton_iff.1 (rootSpan_le_centralizer _ hS (hmemF 0 z))
  have hUd : (U : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 (e6D0Char ω) =
      rootDiagUnit Tag.E6 (e6D0Char ω) * U := by
    rw [hU]
    exact (mul_inv_eq_iff_eq_mul.1 (rootDiagUnit_e6D0Char_conj_of_mem (hmemF 0 z))).symm
  have hh₀ : MulAut.conj U * MulAut.conj (e6LineElt ω) * (MulAut.conj U)⁻¹ =
      MulAut.conj (e6LineElt ω) :=
    conj_mul_mul_inv_eq_self U (ε := MulAut.conj (e6LineElt ω))
      (F := rootDiagUnit Tag.E6 (e6LineChar ω)) (fun _ => rfl) hUh
  have hd₀ : MulAut.conj U * rootDiagAutHom .E6 K (e6D0Char ω) * (MulAut.conj U)⁻¹ =
      rootDiagAutHom .E6 K (e6D0Char ω) :=
    conj_mul_mul_inv_eq_self U (ε := rootDiagAutHom .E6 K (e6D0Char ω))
      (F := rootDiagUnit Tag.E6 (e6D0Char ω)) (fun _ => rfl) hUd
  have hX : MulAut.conj U * f * (MulAut.conj U)⁻¹ =
      MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hνa h, coe_conj_mul_mul_inv_apply U hfe h, hU, hkey]
  refine ⟨MulAut.conj U, innerAut_le_e6Inndiag K ⟨U, rfl⟩, ν, a,
    Subgroup.mem_map.2 ⟨_, hsig, ?_⟩, Subgroup.mem_map.2 ⟨_, hδ, ?_⟩,
    Subgroup.mem_map.2 ⟨f, hf, ?_⟩, fun hXi => hfi ?_⟩
  · rw [congr_toMonoidHom_apply, hh₀]
  · rw [congr_toMonoidHom_apply, hd₀]
  · rw [congr_toMonoidHom_apply, hX]
  · have h := CFSG.Fischer.innerAut_normal.conj_mem _ hXi (MulAut.conj U)⁻¹
    rwa [← hX, inv_inv, show (MulAut.conj U)⁻¹ * (MulAut.conj U * f * (MulAut.conj U)⁻¹) *
      MulAut.conj U = f by group] at h

theorem e6ThreeNotAll24NFB1_holds : E6ThreeNotAll24NFB1 :=
  fun _ _ _ _ h3 _ _ hw3 hw1 _ hE _ hEd hEi _ hsig hδ =>
    exists_monomial_of_e6D0Char_mem h3 hw3 hw1 hE hEd hEi hsig hδ

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
