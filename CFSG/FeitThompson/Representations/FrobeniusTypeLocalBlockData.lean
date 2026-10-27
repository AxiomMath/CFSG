module

public import CFSG.FeitThompson.Representations.NormalInducedBlockPartition
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.MultiplicityFreeBlockAgreeOnCore
import CFSG.FeitThompson.Representations.AbelianPointStabilizersCharacterStabilizers
import CFSG.FeitThompson.Representations.AbelianInertiaInducedBlock

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped ComplexOrder

variable {L : Type*} [Group L]

def coreCentralizerSupport (H : Subgroup L) : Set L :=
  {x | x ≠ 1 ∧ H ⊓ Subgroup.centralizer {x} ≠ ⊥}

theorem mem_coreCentralizerSupport {H : Subgroup L} {x : L} :
    x ∈ coreCentralizerSupport H ↔ x ≠ 1 ∧ H ⊓ Subgroup.centralizer {x} ≠ ⊥ := Iff.rfl

theorem mem_coreCentralizerSupport_iff_exists {H : Subgroup L} {x : L} :
    x ∈ coreCentralizerSupport H ↔ x ≠ 1 ∧ ∃ h ∈ H, h ≠ 1 ∧ h * x = x * h := by
  rw [mem_coreCentralizerSupport]
  refine and_congr_right fun _ => ?_
  rw [Ne, inf_centralizer_eq_bot_iff]
  push Not
  simp only [and_comm]

theorem one_notMem_coreCentralizerSupport (H : Subgroup L) :
    (1 : L) ∉ coreCentralizerSupport H := fun h => h.1 rfl

theorem coreCentralizerSupport_bot : coreCentralizerSupport (⊥ : Subgroup L) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => h.2 (by simp)

theorem coreCentralizerSupport_mono {H H' : Subgroup L} (h : H ≤ H') :
    coreCentralizerSupport H ⊆ coreCentralizerSupport H' := fun _ hx =>
  ⟨hx.1, fun hbot => hx.2 (le_antisymm (le_trans (inf_le_inf_right _ h) hbot.le) bot_le)⟩

theorem inf_centralizer_eq_bot_of_notMem_insert_one {H : Subgroup L} {x : L}
    (hx : x ∉ insert (1 : L) (coreCentralizerSupport H)) :
    H ⊓ Subgroup.centralizer {x} = ⊥ := by
  rw [Set.mem_insert_iff, mem_coreCentralizerSupport] at hx
  push Not at hx
  exact hx.2 hx.1

structure IsFrobeniusTypeLocalData (H U U₁ : Subgroup L) [H.Normal] : Prop where
  core_ne_bot : H ≠ ⊥
  sup_eq_top : H ⊔ U = ⊤
  inf_eq_bot : H ⊓ U = ⊥
  coprime : (Nat.card H).Coprime (Nat.card U)
  le_complement : U₁ ≤ U
  isMulCommutative : IsMulCommutative (U₁ : Type _)
  centralizer_le : ∀ h ∈ H, h ≠ 1 → U ⊓ Subgroup.centralizer {h} ≤ U₁

variable {H U U₁ : Subgroup L} [H.Normal] {lam : H → ℂ}

theorem eq_zero_of_notMem_insert_one_coreCentralizerSupport [Finite L] {χ : L → ℂ}
    (hχ : χ ∈ irrDetect ℂ H) {x : L}
    (hx : x ∉ insert (1 : L) (coreCentralizerSupport H)) : χ x = 0 :=
  eq_zero_of_inf_centralizer_eq_bot (mem_irrDetect.1 hχ).1 (mem_irrDetect.1 hχ).2
    (inf_centralizer_eq_bot_of_notMem_insert_one hx)

theorem support_subset_insert_one_coreCentralizerSupport [Finite L] {χ : L → ℂ}
    (hχ : χ ∈ irrDetect ℂ H) :
    Function.support χ ⊆ insert (1 : L) (coreCentralizerSupport H) :=
  Function.support_subset_iff'.2 fun _ hx =>
    eq_zero_of_notMem_insert_one_coreCentralizerSupport hχ hx

theorem IsFrobeniusTypeLocalData.isMulCommutative_inf_inertiaGroup [Finite L]
    (hD : IsFrobeniusTypeLocalData H U U₁) (hlam : lam ∈ nonprincipalIrr H) :
    IsMulCommutative ((U ⊓ inertiaGroup H lam : Subgroup L) : Type _) :=
  haveI := hD.isMulCommutative
  _root_.CFSG.FeitThompson.isMulCommutative_inf_inertiaGroup hD.centralizer_le
    (mem_nonprincipalIrr.1 hlam).1 (mem_nonprincipalIrr.1 hlam).2

variable [Fintype L]

theorem exists_finset_coe_eq_irrConstituents
    (hD : IsFrobeniusTypeLocalData H U U₁) (hlam : lam ∈ nonprincipalIrr H) :
    ∃ S : Finset (L → ℂ), ↑S = irrConstituents (indClassFun H lam) ∧ ↑S ⊆ Irr L ∧
      S.card = Nat.card (U ⊓ inertiaGroup H lam : Subgroup L) ∧
      indClassFun H lam = ∑ χ ∈ S, χ ∧
      ∀ χ ∈ S, χ 1 = ((H ⊔ (U ⊓ inertiaGroup H lam) : Subgroup L).index : ℂ) * lam 1 := by
  classical
  obtain ⟨hlamIrr, hlamne⟩ := mem_nonprincipalIrr.1 hlam
  have := hD.isMulCommutative_inf_inertiaGroup hlam
  obtain ⟨S, hSIrr, hcard, hsum, hdeg⟩ :=
    AbelianInertiaBlock.exists_finset_Irr_indClassFun (U := U) hlamIrr hD.sup_eq_top
      hD.inf_eq_bot hD.coprime
  refine ⟨S, ?_, hSIrr, hcard, hsum, ?_⟩
  ·
    ext χ
    rw [Finset.mem_coe, mem_irrConstituents]
    constructor
    · intro hχ
      refine ⟨hSIrr hχ, ?_⟩
      rw [hsum, cfInner_sum_eq_ite hSIrr (hSIrr hχ), if_pos hχ]
      exact zero_lt_one
    · rintro ⟨hχ, hpos⟩
      by_contra hnot
      rw [hsum, cfInner_sum_eq_ite hSIrr hχ, if_neg hnot] at hpos
      exact absurd hpos (lt_irrefl 0)
  · intro χ hχ
    rw [hdeg χ hχ, ← AbelianInertiaBlock.inertiaGroup_eq_sup (U := U) hlamIrr hD.sup_eq_top]

theorem indClassFun_eq_sum_irrConstituents (hD : IsFrobeniusTypeLocalData H U U₁)
    (hlam : lam ∈ nonprincipalIrr H) :
    indClassFun H lam
      = ∑ χ ∈ (finite_irrConstituents (indClassFun H lam)).toFinset, χ := by
  obtain ⟨S, hSeq, -, -, hsum, -⟩ := exists_finset_coe_eq_irrConstituents hD hlam
  have hSF : (finite_irrConstituents (indClassFun H lam)).toFinset = S := by
    rw [← Finset.coe_inj, Set.Finite.coe_toFinset, hSeq]
  rw [hSF, hsum]

theorem ncard_irrConstituents_indClassFun (hD : IsFrobeniusTypeLocalData H U U₁)
    (hlam : lam ∈ nonprincipalIrr H) :
    (irrConstituents (indClassFun H lam)).ncard
      = Nat.card (U ⊓ inertiaGroup H lam : Subgroup L) := by
  obtain ⟨S, hSeq, -, hcard, -, -⟩ := exists_finset_coe_eq_irrConstituents hD hlam
  rw [← hSeq, Set.ncard_coe_finset, hcard]

theorem apply_one_of_mem_irrConstituents (hD : IsFrobeniusTypeLocalData H U U₁)
    (hlam : lam ∈ nonprincipalIrr H) {χ : L → ℂ}
    (hχ : χ ∈ irrConstituents (indClassFun H lam)) :
    χ 1 = ((H ⊔ (U ⊓ inertiaGroup H lam) : Subgroup L).index : ℂ) * lam 1 := by
  obtain ⟨S, hSeq, -, -, -, hdeg⟩ := exists_finset_coe_eq_irrConstituents hD hlam
  exact hdeg χ (by rw [← Finset.mem_coe, hSeq]; exact hχ)

theorem apply_one_of_mem_irrConstituents' (hD : IsFrobeniusTypeLocalData H U U₁)
    (hlam : lam ∈ nonprincipalIrr H) {χ : L → ℂ}
    (hχ : χ ∈ irrConstituents (indClassFun H lam)) :
    χ 1 = ((inertiaGroup H lam).index : ℂ) * lam 1 := by
  rw [apply_one_of_mem_irrConstituents hD hlam hχ,
    ← AbelianInertiaBlock.inertiaGroup_eq_sup (U := U) (mem_nonprincipalIrr.1 hlam).1
      hD.sup_eq_top]

theorem resClassFun_eq_of_mem_irrConstituents (hD : IsFrobeniusTypeLocalData H U U₁)
    (hlam : lam ∈ nonprincipalIrr H) {χ χ' : L → ℂ}
    (hχ : χ ∈ irrConstituents (indClassFun H lam))
    (hχ' : χ' ∈ irrConstituents (indClassFun H lam)) :
    resClassFun H χ = resClassFun H χ' := by
  obtain ⟨S, hSeq, hSIrr, -, hsum, -⟩ := exists_finset_coe_eq_irrConstituents hD hlam
  exact resClassFun_eq_resClassFun_of_mem (mem_nonprincipalIrr.1 hlam).1 hSIrr hsum
    (by rw [← Finset.mem_coe, hSeq]; exact hχ) (by rw [← Finset.mem_coe, hSeq]; exact hχ')

theorem isFrobeniusTypeLocalData_block_facts (hD : IsFrobeniusTypeLocalData H U U₁) :
    (∀ lam ∈ nonprincipalIrr H,
        indClassFun H lam
            = ∑ χ ∈ (finite_irrConstituents (indClassFun H lam)).toFinset, χ ∧
          (irrConstituents (indClassFun H lam)).ncard
            = Nat.card (U ⊓ inertiaGroup H lam : Subgroup L) ∧
          (∀ χ ∈ irrConstituents (indClassFun H lam),
            χ 1 = ((H ⊔ (U ⊓ inertiaGroup H lam) : Subgroup L).index : ℂ) * lam 1) ∧
          ∀ χ ∈ irrConstituents (indClassFun H lam),
            ∀ χ' ∈ irrConstituents (indClassFun H lam), resClassFun H χ = resClassFun H χ') ∧
      ∀ χ ∈ irrDetect ℂ H,
        Function.support χ ⊆ insert (1 : L) (coreCentralizerSupport H) :=
  ⟨fun _ hlam => ⟨indClassFun_eq_sum_irrConstituents hD hlam,
      ncard_irrConstituents_indClassFun hD hlam,
      fun _ hχ => apply_one_of_mem_irrConstituents hD hlam hχ,
      fun _ hχ _ hχ' => resClassFun_eq_of_mem_irrConstituents hD hlam hχ hχ'⟩,
    fun _ hχ => support_subset_insert_one_coreCentralizerSupport hχ⟩

end

end CFSG.FeitThompson
