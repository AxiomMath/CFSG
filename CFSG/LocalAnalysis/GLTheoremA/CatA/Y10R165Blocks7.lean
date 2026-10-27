module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp2
public import CFSG.GroupTheory.PLayer.Bootstrap
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import Certificates.Certificate41501

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.Open

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

section Choice

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ}

theorem exists_blockRep (hp : p.Prime) : ∃ t : Hyperplane A p → ↥A, ∀ D, t D ∉ D.1 := by
  have hex : ∀ D : Hyperplane A p, ∃ a : ↥A, a ∉ D.1 := by
    intro D
    by_contra h
    push Not at h
    have htop : D.1 = ⊤ := le_antisymm le_top fun x _ => h x
    have h1 : D.1.index = 1 := by rw [htop]; exact Subgroup.index_top
    have hp2 : 2 ≤ p := hp.two_le
    omega
  exact ⟨fun D => Classical.choose (hex D), fun D => Classical.choose_spec (hex D)⟩

end Choice

section MaximalRank

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ}

theorem blockEnd_mem_of_pRank_le [Finite F] [FiniteDimensional F V]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {H : Subgroup (V ≃ₗ[F] V)} (hAH : A ≤ H)
    (hmax : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p A)
    (htH : ∀ D, blockEnd A hp hpF hA t ht D ∈ H) (D : Hyperplane A p) :
    blockEnd A hp hpF hA t ht D ∈ A := by
  have hk : Nat.card ↥A = p ^ CFSG.Open.pRank p A :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hA
  have hAeq := eq_closure_blockEnd_of_pRank_le A hp hpF hA t ht hk hAH hmax htH
  exact hAeq.ge (Subgroup.subset_closure ⟨D, rfl⟩)

end MaximalRank

section BlockElements

variable [FiniteDimensional F V] {p : ℕ} [Finite F]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]

private def linearPointwiseStab (U : Submodule F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ x ∈ U, g x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by
    intro g h hg hh x hx
    change (g * h) x = x
    rw [LinearEquiv.mul_apply, hh x hx, hg x hx]
  inv_mem' := by
    intro g hg x hx
    apply g.injective
    rw [hg x hx]
    exact g.apply_symm_apply x

theorem zpow_blockEnd_apply_of_mem_block (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane A p} (hDE : D ≠ E) {v : V} (hv : v ∈ blockSpace A E.1) (n : ℤ) :
    (blockEnd A hp hpF hA t ht D ^ n) v = v := by
  have hx : blockEnd A hp hpF hA t ht D ∈ linearPointwiseStab (blockSpace A E.1) :=
    fun w hw => blockEnd_apply_of_mem_block A hp hpF hA t ht (D := D) (E := E) hDE.symm hw
  exact Subgroup.zpow_mem _ hx n v hv

theorem blockEnd_not_mem_zpowers_of_ne (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane A p} (hDE : E ≠ D) (hD : blockSpace A D.1 ≠ ⊥) :
    blockEnd A hp hpF hA t ht D ∉
      Subgroup.zpowers (blockEnd A hp hpF hA t ht E) := by
  intro hmem
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h1 : blockEnd A hp hpF hA t ht D v = v := by
    rw [← hn]
    exact zpow_blockEnd_apply_of_mem_block A hp hpF hA t ht (D := E) (E := D) hDE hv n
  have h2 : (t D : V ≃ₗ[F] V) v = v := by
    rw [← blockEnd_apply_mem A hp hpF hA t ht D hv]
    exact h1
  exact hv0 (eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) hv h2)

theorem card_closure_pair_blockEnd (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D E : Hyperplane A p}
    (hDE : D ≠ E) (hD : blockSpace A D.1 ≠ ⊥) (hE : blockSpace A E.1 ≠ ⊥)
    (hxD : blockEnd A hp hpF hA t ht D ∈ A) (hxE : blockEnd A hp hpF hA t ht E ∈ A) :
    Nat.card (Subgroup.closure
      ({blockEnd A hp hpF hA t ht D, blockEnd A hp hpF hA t ht E} :
        Set (V ≃ₗ[F] V))) = p ^ 2 := by
  set x := blockEnd A hp hpF hA t ht D with hx
  set y := blockEnd A hp hpF hA t ht E with hy
  have hsup : Subgroup.closure ({x, y} : Set (V ≃ₗ[F] V)) =
      Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · refine (Subgroup.closure_le (K := Subgroup.zpowers x ⊔ Subgroup.zpowers y)).mpr ?_
      intro z hz
      rcases hz with rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  rw [hsup]
  have hcomm : x * y = y * x := by
    haveI : IsMulCommutative ↥A := hA.1
    have h := mul_comm' (⟨x, hxD⟩ : ↥A) ⟨y, hxE⟩
    simpa using congrArg Subtype.val h
  refine CFSG.card_zpowers_sup_zpowers_eq_prime_sq hp (blockEnd_pow A hp hpF hA t ht D)
    (blockEnd_pow A hp hpF hA t ht E) ?_ ?_ hcomm
  · intro h1
    have hxord : orderOf x = p := by
      rw [hx]
      exact orderOf_blockEnd A hp hpF hA t ht hD
    rw [h1, orderOf_one] at hxord
    exact hp.ne_one hxord.symm
  · exact blockEnd_not_mem_zpowers_of_ne A hp hpF hA t ht (D := E) (E := D) hDE hE

theorem pointwiseStab_normal {H : Subgroup (V ≃ₗ[F] V)} {K : Subgroup ↥H} {U : Submodule F V}
    (hpres : ∀ g ∈ K, ∀ x ∈ U, (((g : ↥H) : V ≃ₗ[F] V)) x ∈ U) :
    ((pointwiseStab H U).subgroupOf K).Normal := by
  refine ⟨fun n hn k => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  rw [mem_pointwiseStab] at hn ⊢
  intro x hx
  have hkx : (((k : ↥H) : V ≃ₗ[F] V))⁻¹ x ∈ U :=
    hpres ((k : ↥H)⁻¹) (Subgroup.inv_mem K k.2) x hx
  have hnx := hn ((((k : ↥H) : V ≃ₗ[F] V))⁻¹ x) hkx
  let kH : V ≃ₗ[F] V := (k : ↥H)
  let nH : V ≃ₗ[F] V := (n : ↥H)
  change kH (nH (kH⁻¹ x)) = x
  rw [show nH (kH⁻¹ x) = kH⁻¹ x from hnx]
  exact kH.apply_symm_apply x

end BlockElements

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
