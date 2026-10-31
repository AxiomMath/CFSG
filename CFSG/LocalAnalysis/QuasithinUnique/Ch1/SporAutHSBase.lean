
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutLocal
public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairHSFaithfulInputs
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHSInputs
public import Certificates.Data.CFSGNative.HS.Data
import CFSG.Sporadic.Schreier.Co3ChainUtil
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

@[expose] public noncomputable section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Blueprint

namespace SporAutHS

def CntPr (g : Equiv.Perm (Fin 3850)) : Prop :=
  g * hsLtr 0 = wordElt yWord * g ∧ orderOf g = 15 ∧ orderOf (wordElt l1Word * g) = 5 ∧
    orderOf (wordElt l2Word * g) = 12

theorem s0Strong_zero : s0Strong[0]! = hsStrongArrs[0]! := by
  rw [s0Strong, getElem!_pos _ 0 (by simp)]
  simp only [List.getElem_toArray, List.getElem_cons_zero]

theorem ltr_zero : hsLtr 0 = hsGen 0 := by
  rw [hsLtr, if_pos (by norm_num : (0 : ℕ) < 4), hsGen, hsStrongPerm, s0Strong_zero]

theorem ltr_lt {k : ℕ} (hk : k < 4) : hsLtr k = permOfArr 3850 s0Strong[k]! := by
  rw [hsLtr, if_pos hk]

theorem ltr_memS0 {k : ℕ} (hk : k < 4) : hsLtr k ∈ s0Chain.originalSubgroup := by
  rw [s0Chain, CFSG.Sporadic.Schreier.Co3.ofArrays_originalSubgroup]
  exact Subgroup.subset_closure ⟨⟨k, hk⟩, (ltr_lt hk).symm⟩

theorem hsGen_zero_memS0 : hsGen 0 ∈ s0Chain.originalSubgroup := by
  have h := ltr_memS0 (k := 0) (by norm_num)
  rwa [ltr_zero] at h

theorem wordElt_cons (k : ℕ) (w : List ℕ) : wordElt (k :: w) = hsLtr k * wordElt w := by
  simp only [wordElt, List.map_cons, List.prod_cons]

theorem wordElt_nil : wordElt [] = 1 := rfl

theorem wordElt_memS0 : ∀ {w : List ℕ}, (∀ k ∈ w, k < 4) →
    wordElt w ∈ s0Chain.originalSubgroup
  | [], _ => by rw [wordElt_nil]; exact Subgroup.one_mem _
  | k :: w, h => by
    rw [wordElt_cons]
    exact Subgroup.mul_mem _ (ltr_memS0 (h k List.mem_cons_self))
      (wordElt_memS0 fun j hj => h j (List.mem_cons_of_mem k hj))

def A0 : hsChain.originalSubgroup := ⟨hsGen 0, hsGen_mem 0 (by norm_num)⟩

def A1 : hsChain.originalSubgroup := ⟨hsGen 1, hsGen_mem 1 (by norm_num)⟩

theorem order_A1 : orderOf (A1 : Equiv.Perm (Fin 3850)) = 5 := hs_word_orders.2.1

theorem orderOf_conj' {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) x
  rwa [MulAut.conj_apply] at this

theorem A1_ne_conj : A1 ≠ A0 * A1 * A0⁻¹ := by
  intro h
  have h1 : (A0 : Equiv.Perm (Fin 3850)) * A1 * (A0 : Equiv.Perm (Fin 3850))⁻¹ = A1 :=
    congrArg Subtype.val h.symm
  have h2 : hsGen 0 * hsGen 1 * (hsGen 0)⁻¹ * (hsGen 1)⁻¹ = 1 := by
    have : (A0 : Equiv.Perm (Fin 3850)) * A1 * (A0 : Equiv.Perm (Fin 3850))⁻¹ *
        (A1 : Equiv.Perm (Fin 3850))⁻¹ = 1 := by
      rw [h1]
      exact mul_inv_cancel _
    exact this
  have h3 := hs_word_orders.2.2.2
  rw [h2, orderOf_one] at h3
  omega

theorem closure_A0_A1 :
    Subgroup.closure ({A0, A1} : Set hsChain.originalSubgroup) = ⊤ :=
  CFSG.Sporadic.Mathieu.closure_pair_eq_top hsP_eq_original.symm (hsGen_mem 0 (by norm_num))
    (hsGen_mem 1 (by norm_num))

end SporAutHS

end CFSG.QuasithinUnique.Ch1
