module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqKac
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open scoped MatrixGroups

set_option linter.unusedSectionVars false

private theorem a2idxR_kc18 : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    (Tag.E6.artifactRoots.filter fun l => decide ((3 : ℤ) ∣
      dotμ (CFSG.RankThree.Lattice.toVec Tag.E6.rank l) ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ)
        ((m2 : ℕ) : ℤ) ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ) ((m5 : ℕ) : ℤ))).length = 18 →
    m0 = 0 ∧ m1 = 0 ∧ m2 = 0 ∧ m3 = 1 ∧ m4 = 0 ∧ m5 = 0 := by
  decide +kernel

private def a2idxR_β : Fin 6 → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1], ![1, 2, 2, 3, 2, 1]]

private def a2idxR_M : Fin 6 → Fin Tag.E6.rank → ℤ :=
  ![![2, 0, -1, 0, 0, 0], ![0, 2, 0, -1, 0, 0], ![-1, 0, 2, -1, 0, 0], ![0, 0, 0, -1, 2, -1],
    ![0, 0, 0, 0, -1, 2], ![0, 1, 0, 0, 0, 0]]

private def a2idxR_N : Fin Tag.E6.rank → Fin 6 → ℤ :=
  ![![2, -1, 1, 0, 0, 2], ![0, 0, 0, 0, 0, 3], ![1, -2, 2, 0, 0, 4], ![0, -3, 0, 0, 0, 6],
    ![0, -2, 0, 2, 1, 4], ![0, -1, 0, 1, 2, 2]]

private theorem a2idxR_mem_artifactRoots :
    ∀ i : Fin 6, List.ofFn (a2idxR_β i) ∈ Tag.E6.artifactRoots := by
  decide +kernel

private theorem a2idxR_three_dvd : ∀ i : Fin 6, (3 : ℤ) ∣ a2idxR_β i 3 := by
  decide +kernel

private theorem a2idxR_iform_self : ∀ i : Fin 6, iform (a2idxR_β i) (a2idxR_β i) = 2 := by
  decide +kernel

private theorem a2idxR_iform_single : ∀ (i : Fin 6) (k : Fin Tag.E6.rank),
    iform (a2idxR_β i) (Pi.single k 1 : Fin Tag.E6.rank → ℤ) = a2idxR_M i k := by
  decide +kernel

private theorem a2idxR_NM : ∀ j k : Fin Tag.E6.rank,
    ∑ i, a2idxR_N j i * a2idxR_M i k = if j = k then 3 else 0 := by
  decide +kernel

section Index


theorem a2cube_exists_weyl_kernelRoots_eq {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {ta : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, ta j ^ 3 = 1)
    (h18 : (kernelRoots (rootCharHom ta)).ncard = 18) :
    ∃ w : WeylGroup Tag.E6, kernelRoots (rootCharHom ta) =
      (fun α => w⁻¹ • α) '' {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3} := by
  obtain ⟨ζ, w, μ, hζ, hμ, hw, -⟩ := kac_pinned_classes h3 hap
  have hζu : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hker : kernelRoots (rootCharHom ta) =
      (fun α => w⁻¹ • α) '' {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ ⬝ᵥ μ} := by
    ext β
    rw [kernelRoots_rootCharHom]
    constructor
    · rintro ⟨hβ, h1⟩
      rw [hw β, hζu.zpow_eq_one_iff_dvd] at h1
      exact ⟨w • β, ⟨IsRoot.smul hβ w, by exact_mod_cast h1⟩, inv_smul_smul w β⟩
    · rintro ⟨γ, ⟨hγ, hd⟩, rfl⟩
      refine ⟨IsRoot.smul hγ w⁻¹, ?_⟩
      change rootChar ta (w⁻¹ • γ) = 1
      rw [hw, smul_inv_smul, hζu.zpow_eq_one_iff_dvd]
      exact_mod_cast hd
  obtain ⟨m0, m1, m2, m3, m4, m5, hsum, e0, e1, e2, e3, e4, e5⟩ := exists_tuple_of_isNormal hμ
  have hcard : {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ ⬝ᵥ μ}.ncard = 18 := by
    rw [← h18, hker, Set.ncard_image_of_injective _ (MulAction.injective w⁻¹)]
  have hc := (CFSG.RankThree.Lattice.ncard_isRoot_and (τ := Tag.E6)
    (fun γ => (3 : ℤ) ∣ γ ⬝ᵥ μ)).symm.trans hcard
  simp only [dot_eq_dotμ, e0, e1, e2, e3, e4, e5] at hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := a2idxR_kc18 m0 m1 m2 m3 m4 m5 hsum hc
  refine ⟨w, ?_⟩
  rw [hker]
  congr 1
  ext γ
  simp only [Set.mem_setOf_eq, dot_eq_dotμ, e0, e1, e2, e3, e4, e5, dotμ]
  simp

private theorem a2idxR_rootTorusSL2_eq {τ : Tag} {L : Type} [Field L] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (c : Lˣ) :
    rootTorusSL2 τ L β c =
      rootDiagUnit τ (fun i => c ^ (2 * iform β (Pi.single i 1) / iform β β)) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ L hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single τ i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit τ a : ModGL τ L) : Module.End L (RootModule τ L))
      (rootVec τ L (Pi.single i 1))) = ((a i : Lˣ) : L) • rootVec τ L (Pi.single i 1) := by
    change rootDiag a (rootVec τ L (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin τ.rank → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single τ i), hs]
  rw [h2] at h1
  have hne : rootVec τ L (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single τ i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  exact Units.ext (smul_left_injective L hne h1)

private theorem a2idxR_rootTorusSL2_mem {L : Type} [Field L] {S : Set (Fin Tag.E6.rank → ℤ)}
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (h1 : β ∈ S) (h2 : -β ∈ S) (c : Lˣ) :
    rootTorusSL2 Tag.E6 L β c ∈ rootSpan Tag.E6 L S := by
  have hmem : rootTorusSL2 Tag.E6 L β c ∈ rootRankOneGroup Tag.E6 L β := ⟨HSL c, rfl⟩
  rw [(exceptional_Lang_root_rank_one_torus_transport Tag.E6 L hβ).1] at hmem
  have hle : rootSubgroup Tag.E6 L β ⊔ rootSubgroup Tag.E6 L (-β) ≤ rootSpan Tag.E6 L S :=
    sup_le (le_iSup₂ (f := fun α (_ : α ∈ S) => rootSubgroup Tag.E6 L α) β h1)
      (le_iSup₂ (f := fun α (_ : α ∈ S) => rootSubgroup Tag.E6 L α) (-β) h2)
  exact hle hmem

private theorem a2idxR_isRoot (i : Fin 6) : IsRoot Tag.E6 (a2idxR_β i) :=
  isRoot_iff_mem_artifactRoots.2 (a2idxR_mem_artifactRoots i)

private theorem a2idxR_torusGroup_le {L : Type} [Field L] [IsAlgClosed L] :
    torusGroup Tag.E6 L ≤ rootSpan Tag.E6 L {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3} := by
  intro t ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hs : ∀ k : Fin Tag.E6.rank, ∃ s : Lˣ, s ^ 3 = b k := by
    intro k
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (b k : L) (by norm_num : 0 < 3)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact (b k).ne_zero (by rw [← hz]; ring)
    exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩
  choose s hs using hs
  let c : Fin 6 → Lˣ := fun i => ∏ j : Fin Tag.E6.rank, s j ^ a2idxR_N j i
  let v : Fin 6 → Fin Tag.E6.rank → Lˣ := fun i k => c i ^ a2idxR_M i k
  have hv : ∀ i, rootDiagUnitHom Tag.E6 L (v i) ∈
      rootSpan Tag.E6 L {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3} := by
    intro i
    have hv' : rootDiagUnitHom Tag.E6 L (v i) = rootTorusSL2 Tag.E6 L (a2idxR_β i) (c i) := by
      rw [a2idxR_rootTorusSL2_eq (a2idxR_isRoot i) (c i)]
      show rootDiagUnit Tag.E6 _ = rootDiagUnit Tag.E6 _
      congr 1
      funext k
      show c i ^ a2idxR_M i k = _
      rw [a2idxR_iform_self, a2idxR_iform_single]
      congr 1
      omega
    rw [hv']
    exact a2idxR_rootTorusSL2_mem (S := {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3})
      (a2idxR_isRoot i) ⟨a2idxR_isRoot i, a2idxR_three_dvd i⟩
      ⟨IsRoot.neg (a2idxR_isRoot i), by rw [Pi.neg_apply]; exact dvd_neg.2 (a2idxR_three_dvd i)⟩
      (c i)
  have hb : b = ∏ i : Fin 6, v i := by
    funext k
    rw [Finset.prod_apply]
    have hexp : ∀ i : Fin 6,
        v i k = ∏ j : Fin Tag.E6.rank, s j ^ (a2idxR_N j i * a2idxR_M i k) := by
      intro i
      simp only [v, c, ← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_congr rfl fun i _ => hexp i, Finset.prod_comm]
    have hcol : ∀ j : Fin Tag.E6.rank, ∏ i : Fin 6, s j ^ (a2idxR_N j i * a2idxR_M i k) =
        s j ^ (if j = k then (3 : ℤ) else 0) := by
      intro j
      rw [← a2idxR_NM j k, Finset.prod_zpow_eq_zpow_sum]
    rw [Finset.prod_congr rfl fun j _ => hcol j]
    rw [Finset.prod_eq_single k (fun j _ hj => by rw [if_neg hj, zpow_zero])
      (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]
    rw [zpow_ofNat, hs k]
  have hmem : b ∈ (rootSpan Tag.E6 L {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3}).comap
      (rootDiagUnitHom Tag.E6 L) := by
    rw [hb]
    exact Subgroup.prod_mem _ fun i _ => hv i
  exact hmem

theorem a2cube_torusGroup_le_rootSpan {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {ta : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, ta j ^ 3 = 1)
    (h18 : (kernelRoots (rootCharHom ta)).ncard = 18) :
    torusGroup Tag.E6 L ≤ rootSpan Tag.E6 L (kernelRoots (rootCharHom ta)) := by
  obtain ⟨w, hw⟩ := a2cube_exists_weyl_kernelRoots_eq h3 hap h18
  obtain ⟨hS, -, hN⟩ := canonical_weyl_root_transport Tag.E6 L
  rw [hw, ← hS w⁻¹ {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3} fun α hα => hα.1]
  intro t ht
  have ht' := (Subgroup.mem_normalizer_iff''.1 (hN w⁻¹) t).1 ht
  refine ⟨_, a2idxR_torusGroup_le ht', ?_⟩
  simp [mul_assoc]

end Index

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
