module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3ASL2
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.RankThree.PartTwo.KFacts.K72L3Group
public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag

section Elem

variable {G H : Type*} [Group G] [Group H]

theorem isElemAbelian_map (f : G →* H) {E : Subgroup G}
    (h : CFSG.Open.IsElemAbelian 3 E) : CFSG.Open.IsElemAbelian 3 (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map h _

theorem isElemAbelian_comap {f : G →* H} (hf : Function.Injective f) {E : Subgroup H}
    (h : CFSG.Open.IsElemAbelian 3 E) : CFSG.Open.IsElemAbelian 3 (E.comap f) :=
  CFSG.Open.IsElemAbelian.comap h hf

theorem card_comap_of_le_range {f : G →* H} (hf : Function.Injective f) {E : Subgroup H}
    (hE : E ≤ f.range) : Nat.card (E.comap f) = Nat.card E := by
  have h := Subgroup.card_map_of_injective hf (K := E.comap f)
  rw [Subgroup.map_comap_eq, inf_eq_right.2 hE] at h
  exact h.symm

end Elem

section Solvable

variable {K : Type} [Field K] {n : ℕ}

theorem isSolvable_statedScalars : Group.IsSolvable ↥(StatedScalars (Fin n) K) :=
  Group.isSolvable_of_surjective (f := (Matrix.GeneralLinearGroup.scalar (Fin n) :
    Kˣ →* GL (Fin n) K).rangeRestrict) (MonoidHom.rangeRestrict_surjective _)

theorem isSolvable_centMod (L : Subgroup (GL (Fin n) K)) (y : GL (Fin n) K)
    (h : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer {y})) : Group.IsSolvable ↥(centMod L y) := by
  have : Group.IsSolvable ↥(StatedScalars (Fin n) K) := isSolvable_statedScalars
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (centralizer_le_centMod L y)) (commHom L y) ?_
  rw [ker_commHom, Subgroup.inclusion_range]

theorem commutator_centMod_le (L : Subgroup (GL (Fin n) K)) (y : GL (Fin n) K) :
    ⁅centMod L y, centMod L y⁆ ≤ Subgroup.centralizer {y} := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  let a' : ↥(centMod L y) := ⟨a, ha⟩
  let b' : ↥(centMod L y) := ⟨b, hb⟩
  have hcomm : commHom L y a' * commHom L y b' = commHom L y b' * commHom L y a' :=
    Subtype.ext (commute_of_mem_statedScalars (commHom L y a').2 _).symm
  have h1 : commHom L y (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have h2 : a' * b' * a'⁻¹ * b'⁻¹ ∈ (L ⊓ Subgroup.centralizer {y}).subgroupOf (centMod L y) := by
    rw [← ker_commHom]
    exact h1
  exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h2)).2

end Solvable

section Block

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem typeII_commutator (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {y g : GL (Fin 3) K}
    {e : Kˣ} (he : e ≠ 1) (hgl : g ∈ glPi π 3 (p ^ f) K) (hg : g⁻¹ * y * g = diagE e)
    {W : Subgroup (GL (Fin 3) K)} (hWL : W ≤ slPi π 3 (p ^ f) K)
    (hWy : W ≤ Subgroup.centralizer {y}) :
    (∀ ω : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ ⁅W, W⁆ → ω = 1) ∧
      ∀ E : Subgroup (GL (Fin 3) K), E ≤ ⁅W, W⁆ → CFSG.Open.IsElemAbelian 3 E →
        Nat.card E ≤ 3 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set cg : GL (Fin 3) K →* GL (Fin 3) K := (MulAut.conj g⁻¹).toMonoidHom with hcg
  have hcg_apply : ∀ x, cg x = g⁻¹ * x * g := fun x => by
    simp [hcg]
  have hcg_inj : Function.Injective cg := (MulAut.conj g⁻¹).injective
  set Wg := W.map cg with hWg_def
  have hWg : Wg ≤ (glPi π 2 (p ^ f) K).map blockHom := by
    rw [← centralizer_diagE_eq hK he]
    rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := conj_mem_slPi hπ (inv_mem hgl) (hWL hw)
      rwa [hcg_apply, show g⁻¹ * w * g = g⁻¹ * w * g⁻¹⁻¹ by rw [inv_inv]]
    · rw [Subgroup.mem_centralizer_singleton_iff, hcg_apply, ← hg]
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hWy hw)
      calc g⁻¹ * w * g * (g⁻¹ * y * g) = g⁻¹ * (w * y) * g := by group
        _ = g⁻¹ * (y * w) * g := by rw [h1]
        _ = g⁻¹ * y * g * (g⁻¹ * w * g) := by group
  set W2 := Wg.comap blockHom with hW2
  have hWg_eq : W2.map blockHom = Wg := by
    rw [hW2, Subgroup.map_comap_eq]
    exact inf_eq_right.2 (hWg.trans (Subgroup.map_le_range _ _))
  have hcomm : ⁅W, W⁆.map cg = ⁅W2, W2⁆.map blockHom := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hWg_eq]
  have hdet : ∀ B ∈ ⁅W2, W2⁆, Matrix.GeneralLinearGroup.det B = 1 := by
    have hle : ⁅W2, W2⁆ ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    exact fun B hB => hle hB
  refine ⟨fun ω hω => ?_, fun E hE hEa => ?_⟩
  · have hs : cg (Matrix.GeneralLinearGroup.scalar (Fin 3) ω) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ω := by
      rw [hcg_apply]
      have := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ω g⁻¹).eq
      rw [this, mul_assoc, inv_mul_cancel, mul_one]
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ ⁅W, W⁆.map cg :=
      ⟨_, hω, hs⟩
    rw [hcomm] at hmem
    obtain ⟨B, hB, hBω⟩ := hmem
    have h1 := congrArg (fun m : GL (Fin 3) K => (m : Matrix (Fin 3) (Fin 3) K) 0 0) hBω
    have hd1 : (B : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      have := congrArg Units.val (hdet B hB)
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    simp only [coe_blockHom, blockMat] at h1
    rw [coe_scalar_eq_smul] at h1
    exact Units.ext (by simpa [hd1] using h1.symm)
  · have hEg : E.map cg ≤ ⁅W2, W2⁆.map blockHom := by
      rw [← hcomm]
      exact Subgroup.map_mono hE
    set E2 := (E.map cg).comap blockHom with hE2
    have hE2le : E2 ≤ ⁅W2, W2⁆ := by
      intro B hB
      obtain ⟨B', hB', hBB'⟩ := hEg hB
      rwa [← blockHom_injective hBB']
    have hcard : Nat.card E2 = Nat.card E := by
      rw [hE2, card_comap_of_le_range blockHom_injective
        (hEg.trans (Subgroup.map_le_range _ _)), Subgroup.card_map_of_injective hcg_inj]
    have hea : CFSG.Open.IsElemAbelian 3 E2 :=
      isElemAbelian_comap blockHom_injective (isElemAbelian_map cg hEa)
    have := card_le_three_of_elemAbelian_sl2 (PiField.three_ne_zero hK hq) hea (fun B hB => by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet B (hE2le hB)]
      rfl)
    rwa [hcard] at this

end Block

end CFSG.HardMathSupport.Solomon.Coordinator
