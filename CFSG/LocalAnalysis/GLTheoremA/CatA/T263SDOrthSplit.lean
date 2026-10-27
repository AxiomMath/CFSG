module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXGlue
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.T263.DX
open scoped commutatorElement Pointwise

section Split

variable {G : Type*} [Group G]

theorem sdo_mem_iSup_split {ι : Type*} (F : ι → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j, u * v = v * u) (i : ι) {g : G}
    (hg : g ∈ ⨆ k, F k) :
    ∃ c ∈ F i, ∃ c' ∈ Subgroup.centralizer (F i : Set G), g = c * c' := by
  set T : Subgroup G := ⨆ k, ⨆ (_ : k ≠ i), F k with hTdef
  have hT : T ≤ Subgroup.centralizer (F i : Set G) := by
    refine iSup₂_le fun k hk => ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hcomm i k (Ne.symm hk) u hu v hv
  have hsup : (⨆ k, F k) ≤ F i ⊔ T := by
    refine iSup_le fun k => ?_
    by_cases hki : k = i
    · subst hki
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le k hki le_rfl)
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (F i) T
    (hT.trans (Subgroup.centralizer_le_normalizer _))
  have hg' : g ∈ (F i : Set G) * (T : Set G) := by
    rw [← hmul]
    exact hsup hg
  obtain ⟨c, hc, t, ht, rfl⟩ := hg'
  exact ⟨c, hc, t, hT ht, rfl⟩

end Split

section Transport

variable {G : Type*} [Group G]

theorem sdo_isSubnormal_subgroupOf (H : Subgroup G) {K X : Subgroup G} (h : IsSubnormal K X) :
    IsSubnormal (K.subgroupOf H) (X.subgroupOf H) := by
  induction h with
  | refl H' => exact IsSubnormal.refl _
  | step hKM hNorm hMX ih =>
      refine IsSubnormal.step (Subgroup.subgroupOf_mono H hKM) ?_ ih
      rw [Subgroup.normal_subgroupOf_iff hKM] at hNorm
      rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono H hKM)]
      intro a b ha hb
      rw [Subgroup.mem_subgroupOf] at ha hb ⊢
      exact hNorm a b ha hb

theorem sdo_isQuasisimple_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  open_of_native_dx (CFSG.LocalCores.isQuasisimple_of_mulEquiv e (native_of_open_dx h))

theorem sdo_card_quot_center_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) :=
  Nat.card_congr (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
    (Subgroup.map_center_eq e)).toEquiv

end Transport

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
