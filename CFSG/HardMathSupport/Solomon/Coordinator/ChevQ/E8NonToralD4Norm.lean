module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Basic
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.AlgebraicGroups.CocharacterCurve
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
import CFSG.RankThree.PartOne.KE.Basic
import CFSG.RankThree.PartOne.KE.E6FourPlane
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E7FourPlane
import CFSG.RankThree.PartOne.KE.E8NineData
import CFSG.RankThree.PartOne.KE.NativeCyclicMain
import CFSG.RankThree.PartOne.KE.PlaneToral
import CFSG.RankThree.PartOne.KGD.D4QA1

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.SeitzGeneration.ExcHighThree

section Algebra

variable {G : Type*} [Group G]

theorem map_orbitNorm {H : Type*} [Group H] (f : G →* H) (z y : G) :
    f (orbitNorm z y) = orbitNorm (f z) (f y) := by
  simp only [orbitNorm, map_mul, map_inv, map_pow]

theorem orbitNorm_one (z : G) : orbitNorm z 1 = 1 := by
  simp [orbitNorm]

theorem orbitNorm_mul_of_commute {z y y' : G} (h₁ : Commute y' (z * y * z⁻¹))
    (h₂ : Commute y' (z ^ 2 * y * (z ^ 2)⁻¹))
    (h₃ : Commute (z * y' * z⁻¹) (z ^ 2 * y * (z ^ 2)⁻¹)) :
    orbitNorm z (y * y') = orbitNorm z y * orbitNorm z y' := by
  have e₂ : z * (y * y') * z⁻¹ = z * y * z⁻¹ * (z * y' * z⁻¹) := by group
  have e₃ : z ^ 2 * (y * y') * (z ^ 2)⁻¹ = z ^ 2 * y * (z ^ 2)⁻¹ * (z ^ 2 * y' * (z ^ 2)⁻¹) := by
    group
  simp only [orbitNorm]
  rw [e₂, e₃]
  generalize z * y * z⁻¹ = a₂ at h₁ ⊢
  generalize z * y' * z⁻¹ = b₂ at h₃ ⊢
  generalize z ^ 2 * y * (z ^ 2)⁻¹ = a₃ at h₂ h₃ ⊢
  generalize z ^ 2 * y' * (z ^ 2)⁻¹ = b₃
  calc y * y' * (a₂ * b₂) * (a₃ * b₃) = y * (y' * a₂) * (b₂ * a₃) * b₃ := by group
    _ = y * (a₂ * y') * (a₃ * b₂) * b₃ := by rw [h₁.eq, h₃.eq]
    _ = y * a₂ * (y' * a₃) * b₂ * b₃ := by group
    _ = y * a₂ * (a₃ * y') * b₂ * b₃ := by rw [h₂.eq]
    _ = y * a₂ * a₃ * (y' * b₂ * b₃) := by group

theorem conj_orbitNorm {g z : G} (hgz : Commute g z) (y : G) :
    g * orbitNorm z y * g⁻¹ = orbitNorm z (g * y * g⁻¹) := by
  have h := map_orbitNorm (MulAut.conj g).toMonoidHom z y
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rwa [show g * z * g⁻¹ = z by rw [hgz.eq, mul_inv_cancel_right]] at h

private theorem commute_conj_sq_of_commute {z y : G} (hz3 : z ^ 3 = 1)
    (h12 : Commute y (z * y * z⁻¹)) : Commute y (z ^ 2 * y * (z ^ 2)⁻¹) := by
  have h := h12.map (MulAut.conj (z ^ 2))
  simp only [MulAut.conj_apply] at h
  have e : z ^ 2 * (z * y * z⁻¹) * (z ^ 2)⁻¹ = y := by
    calc z ^ 2 * (z * y * z⁻¹) * (z ^ 2)⁻¹ = z ^ 3 * y * (z ^ 3)⁻¹ := by group
      _ = y := by rw [hz3]; group
  rw [e] at h
  exact h.symm

theorem orbitNorm_conj_self {z y : G} (hz3 : z ^ 3 = 1) (h12 : Commute y (z * y * z⁻¹)) :
    orbitNorm z (z * y * z⁻¹) = orbitNorm z y := by
  have h13 := commute_conj_sq_of_commute hz3 h12
  have e₂ : z * (z * y * z⁻¹) * z⁻¹ = z ^ 2 * y * (z ^ 2)⁻¹ := by rw [pow_two]; group
  have e₃ : z ^ 2 * (z * y * z⁻¹) * (z ^ 2)⁻¹ = y := by
    calc z ^ 2 * (z * y * z⁻¹) * (z ^ 2)⁻¹ = z ^ 3 * y * (z ^ 3)⁻¹ := by group
      _ = y := by rw [hz3]; group
  simp only [orbitNorm]
  rw [e₂, e₃]
  generalize z * y * z⁻¹ = u₂ at h12 ⊢
  generalize z ^ 2 * y * (z ^ 2)⁻¹ = u₃ at h13 ⊢
  rw [mul_assoc, ← h13.eq, ← mul_assoc, ← h12.eq]

theorem orbitNorm_conj_pow {z y : G} (hz3 : z ^ 3 = 1) (h12 : Commute y (z * y * z⁻¹)) (k : ℕ) :
    orbitNorm z (z ^ k * y * (z ^ k)⁻¹) = orbitNorm z y := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (k + 1) * y * (z ^ (k + 1))⁻¹ = z * (z ^ k * y * (z ^ k)⁻¹) * z⁻¹ := by group
    have h := h12.map (MulAut.conj (z ^ k))
    simp only [MulAut.conj_apply] at h
    have e' : z ^ k * (z * y * z⁻¹) * (z ^ k)⁻¹ = z * (z ^ k * y * (z ^ k)⁻¹) * z⁻¹ := by group
    rw [e'] at h
    rw [e, orbitNorm_conj_self hz3 h, ih]

theorem commute_orbitNorm_of_commute {z y : G} (hz3 : z ^ 3 = 1)
    (h12 : Commute y (z * y * z⁻¹)) : Commute z (orbitNorm z y) := by
  have h := conj_orbitNorm (Commute.refl z) y
  rw [orbitNorm_conj_self hz3 h12] at h
  exact mul_inv_eq_iff_eq_mul.1 h

end Algebra


section Monomial

variable {τ : Tag} {L : Type} [Field L]

private theorem exists_torus_canonicalRep_conj_pinnedX {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (w : WeylGroup τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ μ : Lˣ, ∀ c : L, t * canonicalRep (coxeterSystem τ) L w * pinnedX τ L γ c *
        (t * canonicalRep (coxeterSystem τ) L w)⁻¹ = pinnedX τ L (w • γ) (μ * c) := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨ε, hε, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hγ
  refine ⟨rootChar a (w • γ) * Units.mkOfMulEqOne ε ε hε, fun c => ?_⟩
  calc rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w * pinnedX τ L γ c *
        (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w)⁻¹ =
      rootDiagUnit τ a * (canonicalRep (coxeterSystem τ) L w * pinnedX τ L γ c *
        (canonicalRep (coxeterSystem τ) L w)⁻¹) * (rootDiagUnit τ a)⁻¹ := by group
    _ = pinnedX τ L (w • γ) ((rootChar a (w • γ) : L) * (ε * c)) := by
        rw [hX, rootDiagUnit_conj_pinnedX a (IsRoot.smul hγ w)]
    _ = _ := by rw [Units.val_mul, Units.val_mkOfMulEqOne, mul_assoc]

private theorem exists_torus_canonicalRep_pow_conj_pinnedX {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (w : WeylGroup τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (k : ℕ) :
    ∃ μ : Lˣ, ∀ c : L, (t * canonicalRep (coxeterSystem τ) L w) ^ k * pinnedX τ L γ c *
        ((t * canonicalRep (coxeterSystem τ) L w) ^ k)⁻¹ = pinnedX τ L (w ^ k • γ) (μ * c) := by
  induction k with
  | zero => exact ⟨1, fun c => by simp⟩
  | succ k ih =>
    obtain ⟨μ, hμ⟩ := ih
    obtain ⟨μ', hμ'⟩ := exists_torus_canonicalRep_conj_pinnedX ht w (IsRoot.smul hγ (w ^ k))
    refine ⟨μ' * μ, fun c => ?_⟩
    have e : ∀ z : ModGL τ L, z ^ (k + 1) * pinnedX τ L γ c * (z ^ (k + 1))⁻¹ =
        z * (z ^ k * pinnedX τ L γ c * (z ^ k)⁻¹) * z⁻¹ := fun z => by group
    rw [e, hμ, hμ', pow_succ', mul_smul, Units.val_mul, mul_assoc]

private theorem rootRankOneGroup_eq_closure {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootRankOneGroup τ L γ =
      Subgroup.closure (Set.range (pinnedX τ L γ) ∪ Set.range (pinnedX τ L (-γ))) := by
  rw [(exceptional_Lang_root_rank_one_torus_transport τ L hγ).1, rootSubgroup, rootSubgroup,
    Subgroup.closure_union]

private theorem torus_canonicalRep_conj_mem_rootRankOneGroup {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (w : WeylGroup τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {y : ModGL τ L} (hy : y ∈ rootRankOneGroup τ L γ) :
    t * canonicalRep (coxeterSystem τ) L w * y * (t * canonicalRep (coxeterSystem τ) L w)⁻¹ ∈
      rootRankOneGroup τ L (w • γ) := by
  rw [rootRankOneGroup_eq_closure hγ] at hy
  rw [rootRankOneGroup_eq_closure (IsRoot.smul hγ w)]
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · obtain ⟨μ, hμ⟩ := exists_torus_canonicalRep_conj_pinnedX ht w hγ
      rw [hμ c]
      exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · obtain ⟨μ, hμ⟩ := exists_torus_canonicalRep_conj_pinnedX ht w (IsRoot.neg hγ)
      rw [hμ c, smul_neg]
      exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  | one => simpa using one_mem _
  | mul x x' _ _ hx hx' =>
    have e : t * canonicalRep (coxeterSystem τ) L w * (x * x') *
        (t * canonicalRep (coxeterSystem τ) L w)⁻¹ =
        t * canonicalRep (coxeterSystem τ) L w * x * (t * canonicalRep (coxeterSystem τ) L w)⁻¹ *
          (t * canonicalRep (coxeterSystem τ) L w * x' *
            (t * canonicalRep (coxeterSystem τ) L w)⁻¹) := by group
    rw [e]
    exact mul_mem hx hx'
  | inv x _ hx =>
    have e : t * canonicalRep (coxeterSystem τ) L w * x⁻¹ *
        (t * canonicalRep (coxeterSystem τ) L w)⁻¹ =
        (t * canonicalRep (coxeterSystem τ) L w * x *
          (t * canonicalRep (coxeterSystem τ) L w)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

private theorem torus_canonicalRep_pow_conj_mem_rootRankOneGroup {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (w : WeylGroup τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {y : ModGL τ L} (hy : y ∈ rootRankOneGroup τ L γ) (k : ℕ) :
    (t * canonicalRep (coxeterSystem τ) L w) ^ k * y *
        ((t * canonicalRep (coxeterSystem τ) L w) ^ k)⁻¹ ∈ rootRankOneGroup τ L (w ^ k • γ) := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    have e : ∀ z : ModGL τ L,
        z ^ (k + 1) * y * (z ^ (k + 1))⁻¹ = z * (z ^ k * y * (z ^ k)⁻¹) * z⁻¹ :=
      fun z => by group
    rw [e, pow_succ', mul_smul]
    exact torus_canonicalRep_conj_mem_rootRankOneGroup ht w (IsRoot.smul hγ (w ^ k)) ih

private theorem rootRankOneGroup_le_familyGroup {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ familyKernel a) :
    rootRankOneGroup τ L γ ≤ familyGroup (K := L) a := by
  rw [(exceptional_Lang_root_rank_one_torus_transport τ L hγ.1).1]
  exact le_sup_of_le_right (sup_le (le_iSup₂_of_le γ hγ le_rfl)
    (le_iSup₂_of_le (-γ) (neg_mem_familyKernel a hγ) le_rfl))

private theorem exists_rootWeylSL2_eq_torus_mul {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ t ∈ torusGroup τ L,
      rootWeylSL2 τ L β 1 = t * canonicalRep (coxeterSystem τ) L (rootReflection β) := by
  obtain ⟨h, hπ⟩ := (exceptional_Lang_root_rank_one_torus_transport τ L hβ).2.2.1 1
  obtain ⟨w, k, hk, hkw⟩ := monomialSubgroup_le_torusWeylCosets h
  have hm : MapsRootLines (rootWeylSL2 τ L β 1) w := by
    rw [hkw]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  have hw : w = rootReflection β := (weylQuotientHom_eq (g := ⟨_, h⟩) hm).symm.trans hπ
  exact ⟨k, hk, by rw [hkw, hw]⟩

private theorem torus_mul_canonicalRep_mul {X X' : ModGL τ L} {w w' : WeylGroup τ}
    (h : ∃ t ∈ torusGroup τ L, X = t * canonicalRep (coxeterSystem τ) L w)
    (h' : ∃ t ∈ torusGroup τ L, X' = t * canonicalRep (coxeterSystem τ) L w') :
    ∃ t ∈ torusGroup τ L, X * X' = t * canonicalRep (coxeterSystem τ) L (w * w') := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨t', ht', rfl⟩ := h'
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) w w'
  have hc : canonicalRep (coxeterSystem τ) L w * t' * (canonicalRep (coxeterSystem τ) L w)⁻¹ ∈
      torusGroup τ L :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) w) t').1 ht'
  refine ⟨t * (canonicalRep (coxeterSystem τ) L w * t' * (canonicalRep (coxeterSystem τ) L w)⁻¹) *
    k, mul_mem (mul_mem ht hc) hk, ?_⟩
  calc t * canonicalRep (coxeterSystem τ) L w * (t' * canonicalRep (coxeterSystem τ) L w')
      = t * (canonicalRep (coxeterSystem τ) L w * t' * (canonicalRep (coxeterSystem τ) L w)⁻¹) *
          (canonicalRep (coxeterSystem τ) L w * canonicalRep (coxeterSystem τ) L w') := by group
    _ = _ := by rw [hkk]; group

private theorem torus_mul_canonicalRep_inv {X : ModGL τ L} {w : WeylGroup τ}
    (h : ∃ t ∈ torusGroup τ L, X = t * canonicalRep (coxeterSystem τ) L w) :
    ∃ t ∈ torusGroup τ L, X⁻¹ = t * canonicalRep (coxeterSystem τ) L w⁻¹ := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) w⁻¹ w
  rw [inv_mul_cancel, canonicalRep_one, mul_one] at hkk
  have hc : canonicalRep (coxeterSystem τ) L w⁻¹ * t⁻¹ * (canonicalRep (coxeterSystem τ) L w⁻¹)⁻¹ ∈
      torusGroup τ L :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) w⁻¹) t⁻¹).1 (inv_mem ht)
  refine ⟨k⁻¹ * (canonicalRep (coxeterSystem τ) L w⁻¹ * t⁻¹ *
    (canonicalRep (coxeterSystem τ) L w⁻¹)⁻¹), mul_mem (inv_mem hk) hc, ?_⟩
  have hn : (canonicalRep (coxeterSystem τ) L w)⁻¹ =
      k⁻¹ * canonicalRep (coxeterSystem τ) L w⁻¹ := by
    rw [← hkk]
    group
  rw [mul_inv_rev, hn]
  group

theorem isOrthTriple_smul {w σ : WeylGroup τ} (hσw : σ * w = w * σ) {d : Fin τ.rank → ℤ}
    (h : IsOrthTriple w d) : IsOrthTriple w (σ • d) := by
  have e1 : w • σ • d = σ • w • d := by rw [← mul_smul, ← mul_smul, hσw]
  have e2 : w ^ 2 • σ • d = σ • w ^ 2 • d := by
    rw [← mul_smul, ← mul_smul, ((Commute.pow_right hσw 2).eq : σ * w ^ 2 = w ^ 2 * σ)]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, iform_smul]; exact h1
  · rw [e2, iform_smul]; exact h2
  · rw [e1, e2, iform_smul]; exact h3

private theorem pinnedX_mem_rootRankOneGroup {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : L) :
    pinnedX τ L γ c ∈ rootRankOneGroup τ L γ := by
  rw [rootRankOneGroup_eq_closure hγ]
  exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

private theorem pinnedX_neg_mem_rootRankOneGroup {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : L) :
    pinnedX τ L (-γ) c ∈ rootRankOneGroup τ L γ := by
  rw [rootRankOneGroup_eq_closure hγ]
  exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

private theorem rootWeylSL2_mem_rootRankOneGroup (β : Fin τ.rank → ℤ) (c : Lˣ) :
    rootWeylSL2 τ L β c ∈ rootRankOneGroup τ L β :=
  show rootWeylSL2 τ L β c ∈ (rootSL2 τ L β).range from MonoidHom.mem_range.2 ⟨nSL c, rfl⟩

private theorem isPolynomialCurve_orbitNorm_pinnedX (z : ModGL τ L) (δ : Fin τ.rank → ℤ) :
    IsPolynomialCurve fun c : L => orbitNorm z (pinnedX τ L δ c) := by
  have hX : IsPolynomialCurve fun c : L => pinnedX τ L δ c := by
    simpa only [Polynomial.eval_X] using isPolynomialCurve_pinnedX (k := L) (τ := τ) δ Polynomial.X
  exact (hX.mul (hX.conj z)).mul (hX.conj (z ^ 2))

end Monomial

section E8

variable {L : Type} [Field L] {ι : Type} (a : ι → Fin Tag.E8.rank → Lˣ) {t₁ : ModGL Tag.E8 L}
  {w₁ : WeylGroup Tag.E8}

local notation "z₁" => t₁ * canonicalRep (coxeterSystem Tag.E8) L w₁

private theorem iform_self_E8 {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) :
    iform β β = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hβ
  have h : ∀ j : Fin Tag.E8.rank, 2 * Tag.E8.symmetrizer j j = 2 := by decide
  rw [hj, h j]

private theorem commute_rootRankOneGroup_E8 {β γ : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β)
    (hγ : IsRoot Tag.E8 γ) (h0 : iform β γ = 0) {x y : ModGL Tag.E8 L}
    (hx : x ∈ rootRankOneGroup Tag.E8 L β) (hy : y ∈ rootRankOneGroup Tag.E8 L γ) :
    Commute x y := by
  have h0' : iform γ β = 0 := by rw [iform_comm]; exact h0
  have hββ := iform_self_E8 hβ
  have hγγ := iform_self_E8 hγ
  refine exceptional_Lang_strongly_orthogonal_root_rank_one_commutation Tag.E8 L hβ hγ h0
    (fun h => ?_) (fun h => ?_) x hx y hy
  · have e := iform_self_E8 h
    rw [iform_add_left, iform_add_right, iform_add_right, hββ, hγγ, h0, h0'] at e
    omega
  · have e := iform_self_E8 h
    rw [sub_eq_add_neg, iform_add_left, iform_add_right, iform_add_right, iform_neg_right,
      iform_neg_left, iform_neg_left, iform_neg_right, hββ, hγγ, h0, h0'] at e
    omega

private theorem triple_commute (ht₁ : t₁ ∈ torusGroup Tag.E8 L) {d : Fin Tag.E8.rank → ℤ}
    (hd : IsRoot Tag.E8 d) (horth : IsOrthTriple w₁ d) {y y' : ModGL Tag.E8 L}
    (hy : y ∈ rootRankOneGroup Tag.E8 L d) (hy' : y' ∈ rootRankOneGroup Tag.E8 L d) :
    Commute y' (z₁ * y * z₁⁻¹) ∧ Commute y' (z₁ ^ 2 * y * (z₁ ^ 2)⁻¹) ∧
      Commute (z₁ * y' * z₁⁻¹) (z₁ ^ 2 * y * (z₁ ^ 2)⁻¹) := by
  obtain ⟨o1, o2, o3⟩ := horth
  have hd1 := IsRoot.smul hd w₁
  have hd2 := IsRoot.smul hd (w₁ ^ 2)
  have c2 := torus_canonicalRep_pow_conj_mem_rootRankOneGroup ht₁ w₁ hd hy 2
  exact ⟨commute_rootRankOneGroup_E8 hd hd1 o1 hy'
      (torus_canonicalRep_conj_mem_rootRankOneGroup ht₁ w₁ hd hy),
    commute_rootRankOneGroup_E8 hd hd2 o2 hy' c2,
    commute_rootRankOneGroup_E8 hd1 hd2 o3
      (torus_canonicalRep_conj_mem_rootRankOneGroup ht₁ w₁ hd hy') c2⟩

theorem orbitNorm_mul (ht₁ : t₁ ∈ torusGroup Tag.E8 L) {d : Fin Tag.E8.rank → ℤ}
    (hd : IsRoot Tag.E8 d) (horth : IsOrthTriple w₁ d) {y y' : ModGL Tag.E8 L}
    (hy : y ∈ rootRankOneGroup Tag.E8 L d) (hy' : y' ∈ rootRankOneGroup Tag.E8 L d) :
    orbitNorm z₁ (y * y') = orbitNorm z₁ y * orbitNorm z₁ y' := by
  obtain ⟨h₁, h₂, h₃⟩ := triple_commute ht₁ hd horth hy hy'
  exact orbitNorm_mul_of_commute h₁ h₂ h₃

theorem commute_orbitNorm (ht₁ : t₁ ∈ torusGroup Tag.E8 L) (hz3 : z₁ ^ 3 = 1)
    {d : Fin Tag.E8.rank → ℤ} (hd : IsRoot Tag.E8 d) (horth : IsOrthTriple w₁ d)
    {y : ModGL Tag.E8 L} (hy : y ∈ rootRankOneGroup Tag.E8 L d) : Commute z₁ (orbitNorm z₁ y) :=
  commute_orbitNorm_of_commute hz3 (triple_commute ht₁ hd horth hy hy).1

theorem orbitNorm_mem_closedIdentityComponent [IsAlgClosed L] (ht₁ : t₁ ∈ torusGroup Tag.E8 L)
    (hz3 : z₁ ^ 3 = 1) (hzK : ∀ γ ∈ familyKernel a, w₁ • γ ∈ familyKernel a)
    {d : Fin Tag.E8.rank → ℤ} (hdK : d ∈ familyKernel a) (horth : IsOrthTriple w₁ d)
    {y : ModGL Tag.E8 L} (hy : y ∈ rootRankOneGroup Tag.E8 L d) :
    orbitNorm z₁ y ∈
      closedIdentityComponent (familyGroup (K := L) a ⊓ Subgroup.centralizer {z₁}) := by
  have hd := hdK.1
  have hMC : ∀ x ∈ rootRankOneGroup Tag.E8 L d,
      orbitNorm z₁ x ∈ familyGroup (K := L) a ⊓ Subgroup.centralizer {z₁} := by
    intro x hx
    have h1 : w₁ • d ∈ familyKernel a := hzK d hdK
    have h2 : w₁ ^ 2 • d ∈ familyKernel a := by
      rw [pow_two, mul_smul]
      exact hzK _ h1
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show x * (z₁ * x * z₁⁻¹) * (z₁ ^ 2 * x * (z₁ ^ 2)⁻¹) ∈ familyGroup (K := L) a
      exact mul_mem (mul_mem (rootRankOneGroup_le_familyGroup a hdK hx)
        (rootRankOneGroup_le_familyGroup a h1
          (torus_canonicalRep_conj_mem_rootRankOneGroup ht₁ w₁ hd hx)))
        (rootRankOneGroup_le_familyGroup a h2
          (torus_canonicalRep_pow_conj_mem_rootRankOneGroup ht₁ w₁ hd hx 2))
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (commute_orbitNorm ht₁ hz3 hd horth hx).symm.eq
  have hgen : ∀ δ : Fin Tag.E8.rank → ℤ,
      (∀ c, pinnedX Tag.E8 L δ c ∈ rootRankOneGroup Tag.E8 L d) →
      ∀ c, orbitNorm z₁ (pinnedX Tag.E8 L δ c) ∈
        closedIdentityComponent (familyGroup (K := L) a ⊓ Subgroup.centralizer {z₁}) :=
    fun δ hδ c => mem_closedIdentityComponent_of_isPolynomialCurve
      (isPolynomialCurve_orbitNorm_pinnedX z₁ δ) (fun c => hMC _ (hδ c)) (t₀ := 0)
      (show orbitNorm z₁ (pinnedX Tag.E8 L δ 0) = 1 by rw [pinnedX_zero, orbitNorm_one]) c
  rw [rootRankOneGroup_eq_closure hd] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hgen d (pinnedX_mem_rootRankOneGroup hd) c
    · exact hgen (-d) (pinnedX_neg_mem_rootRankOneGroup hd) c
  | one => rw [orbitNorm_one]; exact one_mem _
  | mul x x' hx hx' ihx ihx' =>
    have hx₁ : x ∈ rootRankOneGroup Tag.E8 L d := by rwa [rootRankOneGroup_eq_closure hd]
    have hx₁' : x' ∈ rootRankOneGroup Tag.E8 L d := by rwa [rootRankOneGroup_eq_closure hd]
    rw [orbitNorm_mul ht₁ hd horth hx₁ hx₁']
    exact mul_mem ihx ihx'
  | inv x hx ih =>
    have hx₁ : x ∈ rootRankOneGroup Tag.E8 L d := by rwa [rootRankOneGroup_eq_closure hd]
    have e := orbitNorm_mul ht₁ hd horth hx₁ (inv_mem hx₁)
    rw [mul_inv_cancel, orbitNorm_one] at e
    rw [eq_inv_of_mul_eq_one_right e.symm]
    exact inv_mem ih

theorem orbitNorm_rootWeylSL2 (ht₁ : t₁ ∈ torusGroup Tag.E8 L) {d : Fin Tag.E8.rank → ℤ}
    (hd : IsRoot Tag.E8 d) (_horth : IsOrthTriple w₁ d) :
    ∃ t ∈ torusGroup Tag.E8 L, orbitNorm z₁ (rootWeylSL2 Tag.E8 L d 1) =
      t * canonicalRep (coxeterSystem Tag.E8) L (tripleRefl w₁ d) := by
  have hn := exists_rootWeylSL2_eq_torus_mul (L := L) hd
  have hz : ∃ t ∈ torusGroup Tag.E8 L, z₁ = t * canonicalRep (coxeterSystem Tag.E8) L w₁ :=
    ⟨t₁, ht₁, rfl⟩
  have hz2 : ∃ t ∈ torusGroup Tag.E8 L,
      z₁ ^ 2 = t * canonicalRep (coxeterSystem Tag.E8) L (w₁ ^ 2) := by
    rw [pow_two, pow_two]
    exact torus_mul_canonicalRep_mul hz hz
  obtain ⟨t, ht, e⟩ := torus_mul_canonicalRep_mul (torus_mul_canonicalRep_mul hn
    (torus_mul_canonicalRep_mul (torus_mul_canonicalRep_mul hz hn) (torus_mul_canonicalRep_inv hz)))
    (torus_mul_canonicalRep_mul (torus_mul_canonicalRep_mul hz2 hn)
      (torus_mul_canonicalRep_inv hz2))
  refine ⟨t, ht, ?_⟩
  rw [tripleRefl, rootReflection_smul_root w₁ hd, rootReflection_smul_root (w₁ ^ 2) hd]
  exact e

private theorem exists_list_prod_orbitNorm_rootWeylSL2 (ht₁ : t₁ ∈ torusGroup Tag.E8 L)
    (l : List (Fin Tag.E8.rank → ℤ)) (hl : ∀ δ ∈ l, IsRoot Tag.E8 δ ∧ IsOrthTriple w₁ δ) :
    ∃ t ∈ torusGroup Tag.E8 L, (l.map fun δ => orbitNorm z₁ (rootWeylSL2 Tag.E8 L δ 1)).prod =
      t * canonicalRep (coxeterSystem Tag.E8) L (l.map (tripleRefl w₁)).prod := by
  induction l with
  | nil => exact ⟨1, one_mem _, by
      rw [List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, canonicalRep_one, mul_one]⟩
  | cons δ l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    have hδ := hl δ (by simp)
    exact torus_mul_canonicalRep_mul (orbitNorm_rootWeylSL2 ht₁ hδ.1 hδ.2)
      (ih fun δ' h => hl δ' (List.mem_cons_of_mem _ h))

theorem exists_conj_frobTwist_orbitNorm [IsAlgClosed L] (p e : ℕ) [Fact p.Prime] [CharP L p]
    (ht₁ : t₁ ∈ torusGroup Tag.E8 L) (hz3 : z₁ ^ 3 = 1)
    (hzK : ∀ γ ∈ familyKernel a, w₁ • γ ∈ familyKernel a)
    {d : Fin Tag.E8.rank → ℤ} (hdK : d ∈ familyKernel a) (horth : IsOrthTriple w₁ d)
    {t' : ModGL Tag.E8 L} (ht' : t' ∈ torusGroup Tag.E8 L) {σ : WeylGroup Tag.E8}
    (hσK : ∀ γ ∈ familyKernel a, σ • γ ∈ familyKernel a) (hσw : σ * w₁ = w₁ * σ)
    (hfix : frobTwistGL Tag.E8 L p e (t' * canonicalRep (coxeterSystem Tag.E8) L σ) z₁ = z₁)
    (htrans : ∀ β ∈ familyKernel a, IsOrthTriple w₁ β → ∃ l : List (Fin Tag.E8.rank → ℤ),
      (∀ δ ∈ l, δ ∈ familyKernel a ∧ IsOrthTriple w₁ δ) ∧
        (l.map (tripleRefl w₁)).prod • β ∈ ({d, w₁ • d, w₁ ^ 2 • d} : Set (Fin Tag.E8.rank → ℤ))) :
    ∃ n₀ ∈ closedIdentityComponent (familyGroup (K := L) a ⊓ Subgroup.centralizer {z₁}),
      ∃ μ : Lˣ, ∀ c : L,
        n₀ * frobTwistGL Tag.E8 L p e (t' * canonicalRep (coxeterSystem Tag.E8) L σ)
            (orbitNorm z₁ (pinnedX Tag.E8 L d c)) * n₀⁻¹ =
          orbitNorm z₁ (pinnedX Tag.E8 L d ((μ : L) * iterateFrobenius L p e c)) := by
  have hd := hdK.1
  obtain ⟨μ₁, hμ₁⟩ := exists_torus_canonicalRep_conj_pinnedX ht' σ hd
  have hS : ∀ c, frobTwistGL Tag.E8 L p e (t' * canonicalRep (coxeterSystem Tag.E8) L σ)
      (pinnedX Tag.E8 L d c) = pinnedX Tag.E8 L (σ • d) (μ₁ * iterateFrobenius L p e c) :=
    fun c => by rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX, hμ₁]
  obtain ⟨l, hl, hW⟩ := htrans _ (hσK d hdK) (isOrthTriple_smul hσw horth)
  have hn₀Y : (l.map fun δ => orbitNorm z₁ (rootWeylSL2 Tag.E8 L δ 1)).prod ∈
      closedIdentityComponent (familyGroup (K := L) a ⊓ Subgroup.centralizer {z₁}) := by
    refine list_prod_mem fun x hx => ?_
    obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 hx
    exact orbitNorm_mem_closedIdentityComponent a ht₁ hz3 hzK (hl δ hδ).1 (hl δ hδ).2
      (rootWeylSL2_mem_rootRankOneGroup δ 1)
  obtain ⟨t₀, ht₀, hn₀⟩ := exists_list_prod_orbitNorm_rootWeylSL2 ht₁ l
    (fun δ hδ => ⟨(hl δ hδ).1.1, (hl δ hδ).2⟩)
  have hcomm : Commute (l.map fun δ => orbitNorm z₁ (rootWeylSL2 Tag.E8 L δ 1)).prod z₁ :=
    Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (closedIdentityComponent_le _ hn₀Y)).2
  obtain ⟨μ₂, hμ₂⟩ := exists_torus_canonicalRep_conj_pinnedX ht₀ (l.map (tripleRefl w₁)).prod
    (IsRoot.smul hd σ)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (l.map (tripleRefl w₁)).prod • σ • d = w₁ ^ j • d := by
    rcases hW with h | h | h
    · exact ⟨0, by rw [h, pow_zero, one_smul]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
    · exact ⟨2, h⟩
  obtain ⟨ν, hν⟩ := exists_torus_canonicalRep_pow_conj_pinnedX ht₁ w₁ hd j
  have hX : ∀ X : L, pinnedX Tag.E8 L (w₁ ^ j • d) X =
      z₁ ^ j * pinnedX Tag.E8 L d (((ν⁻¹ : Lˣ) : L) * X) * (z₁ ^ j)⁻¹ := fun X => by
    rw [hν, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have h12 : ∀ c' : L, Commute (pinnedX Tag.E8 L d c') (z₁ * pinnedX Tag.E8 L d c' * z₁⁻¹) :=
    fun c' => (triple_commute ht₁ hd horth (pinnedX_mem_rootRankOneGroup hd c')
      (pinnedX_mem_rootRankOneGroup hd c')).1
  refine ⟨_, hn₀Y, ν⁻¹ * μ₂ * μ₁, fun c => ?_⟩
  rw [map_orbitNorm, hfix, hS, conj_orbitNorm hcomm, hn₀, hμ₂, hj, hX,
    orbitNorm_conj_pow hz3 (h12 _) j]
  congr 2
  simp only [Units.val_mul]
  ring

end E8

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
