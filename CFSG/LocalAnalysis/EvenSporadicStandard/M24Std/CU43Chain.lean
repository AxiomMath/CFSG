module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
public import CFSG.LieType.Multipliers.U43Bridge
public import CFSG.Sporadic.Schreier.PairChain

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43

@[expose] noncomputable def Q : RawSchreierDatum 820 :=
  RawSchreierDatum.ofArrays 820 (by norm_num) chainS 2 (by decide) chainBase (by decide) chainW

@[expose] noncomputable def P : Subgroup (Equiv.Perm (Fin 820)) := Q.originalSubgroup

theorem chainArrays :
    ChainArrays Q (chainS.extract 0 2) chainS baseArr chainW :=
  chainArrays_ofArrays (chainCheckFacts chain_check).strong_inv

theorem inP_iff {g : Array ℕ} {G : Equiv.Perm (Fin 820)}
    (hG : Rep 820 g G) : inP g = true ↔ G ∈ P :=
  siftA_iff_mem_originalSubgroup chainArrays (by norm_num) chain_check hG

theorem groups_flatten : groups.flatten = List.range Q.baseCount := rfl

theorem card_eq_countW_P {f : List (Array ℕ) → Bool}
    {Pr : Equiv.Perm (Fin 820) → Prop} [DecidablePred Pr]
    (hfP : ∀ w g, RepW 820 w g → g ∈ P → (f w = true ↔ Pr g)) :
    Nat.card {x : P // Pr x} = countW f blocks [] :=
  card_eq_countW chainArrays (by norm_num) chain_check groups_flatten hfP

theorem P_eq_closure :
    P = Subgroup.closure {psi xElt, psi yElt} := by
  rw [P, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [Q, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  have h0 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 0 (by decide))).1
  have h1 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 1 (by decide))).1
  have e0 : permOfArr 820 chainS[0]! = psi xElt := h0.unique rep_tabA
  have e1 : permOfArr 820 chainS[1]! = psi yElt := h1.unique rep_tabB
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩

theorem P_eq_range : P = psi.range := by
  rw [P_eq_closure, MonoidHom.range_eq_map, ← closure_xy, MonoidHom.map_closure, Set.image_pair]

noncomputable def psiEquiv : X₀ ≃* P :=
  (MonoidHom.ofInjective psi_injective).trans (MulEquiv.subgroupCongr P_eq_range.symm)

end CFSG.EvenSporadicStandard.M24Std.CU43
