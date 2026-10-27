module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {n : ℕ} {t : G}

namespace Setup

variable {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
  (P : Setup T M H S L n t M₀ x q W)
include P

theorem c56_7Concl (hne : conjJoin S L ≠ L) : C56_7Concl S H L M₀ := by
  have hU0 : blockU0 S L = blockU L ⊔ conjSubgroup (blockU L) t := P.D.blockU0_eq
  refine ⟨P.pCoreOf_conjJoin_eq, isElemAbelian_two_iff.2 P.D_elemAb, P.blockD_eq.symm, ?_, ?_,
    P.thompsonJ_eq.symm, ?_⟩
  · rw [hU0]; exact P.O_eq_DU
  · rw [P.O_eq_DU]; exact P.isMax_DU
  · intro x' hx' hx'S
    have hs : x⁻¹ * x' ∈ S := inv_mul_mem_of_relIndex_two P.h2 P.hx P.hxS hx' hx'S
    have hs' : x' * x⁻¹ ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 P.hxN (x⁻¹ * x')).1 hs
      simpa [mul_assoc] using this
    have hconj : ∀ Z : Subgroup G, (∀ s ∈ S, conjSubgroup Z s = Z) →
        conjSubgroup Z x' = conjSubgroup Z x := by
      intro Z hZ
      have e : conjSubgroup Z x' = conjSubgroup (conjSubgroup Z (x' * x⁻¹)) x := by
        simp only [conjSubgroup_conjSubgroup, mul_assoc, inv_mul_cancel, mul_one]
      rw [e, hZ _ hs']
    have hD : conjSubgroup (baumD S L) x' = conjSubgroup (baumD S L) x :=
      hconj _ fun s hs => C5.conjSubgroup_eq_self (S_le_normalizer_baumD S L hs)
    have hU : conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x' =
        conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x :=
      hconj _ fun s hs => P.D.conj_U_sup hs
    refine ⟨?_, ?_, fun h => absurd h hne, fun h => absurd h hne, fun _ A hA => ?_⟩
    · rw [C56.conjR_eq, hD]
      exact P.D_inf_conj
    · rw [hU0, C56.conjR_eq, hU]
      exact P.B_eq_sup
    · simpa only [hU0, C56.conjR_eq, hU] using P.invariant_members_iff hA

end Setup

theorem c56DoubleLin2 (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G)
    (hcs : ConstrainedSetting G T M H S L) (hL : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)
    (hne : conjJoin S L ≠ L) {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T)
    (h2 : S.relIndex M₀ = 2) : C56_7Concl S H L M₀ := by
  obtain ⟨n, hn, hlin⟩ := hL
  obtain ⟨t, ⟨D⟩⟩ := exists_dbl hcs hn hlin hne
  obtain ⟨q, W, hloc⟩ := D.loc
  obtain ⟨x, hx, hxS, hgood⟩ := D.exists_good hSM hMT h2 hloc
  exact (Setup.mk D hSM hMT h2 hx hxS hloc hgood :
    Setup T M H S L n t M₀ x q W).c56_7Concl hne

@[expose] def C56DoubleA5Case : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 5 → conjJoin S L ≠ L →
    ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S.relIndex M₀ = 2 → C56_7Concl S H L M₀

theorem c56DoubleNonA3 (h5 : C56DoubleA5Case) : AppC.C56DoubleNonA3 := by
  intro G _ _ T M H S L hcs hA3 hne M₀ hSM hMT h2
  rcases hcs.block.2 with hl | h3 | h5'
  · exact c56DoubleLin2 G T M H S L hcs hl hne hSM hMT h2
  · exact absurd h3 hA3
  · exact h5 G T M H S L hcs h5' hne M₀ hSM hMT h2

end CFSG.QuasithinUnique.AppE
