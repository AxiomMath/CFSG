module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Reduce
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi22

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.AGLEmbedding CFSG.HardMathSupport.Timmesfeld.SporadicRank
open CFSG.Open (IsElemAbelian)

theorem i1021_hcen_of_datum {F : Type} [Group F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) (D : ModuleSpec F 3) (hA : D.NoAlt) (hF : D.NoFun)
    (L : Type) [Group L] [Finite L] (ψ : L →* F) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) :
    D.n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have hker' : ψ.ker = Subgroup.center L := by
    refine le_antisymm hker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have : ψ z ∈ Subgroup.center F := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hψ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz x]
    rw [i1021_center_eq_bot hnc] at this
    exact this
  exact i1021_le_pRank_of_datum Nat.prime_three (by norm_num) ψ hψ hker' D hA hF

theorem i1021_fi22_of_two_rank
    {F : Type} [Group F] [Finite F]
    (e : F ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group)
    {V : Subgroup F} (hV : IsElemAbelian 2 V) (hVc : Nat.card V = 2 ^ 5)
    (X : Type) [Group X] [Finite X] (φ : X →* F) (hφ : Function.Surjective φ) :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := b0
  have e1 : NativeSporadic.Carrier .Fi22 ≃* F := b.trans e.symm
  have : IsSimpleGroup (NativeSporadic.Carrier .Fi22) := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  have : IsSimpleGroup F := e1.symm.isSimpleGroup
  have hnc : ∃ a b : F, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have : IsMulCommutative F := ⟨⟨fun a b => h a b⟩⟩
    have hp := IsSimpleGroup.prime_card (α := F)
    rw [Nat.card_congr e1.symm.toEquiv] at hp
    change Nat.Prime (Nat.card NativeSporadic.Fi22) at hp
    rw [CFSG.Sporadic.Fi22.card_Fi22] at hp
    exact absurd hp (by norm_num)
  obtain ⟨D, P, hn, hA, hF, -⟩ := sylowData_Fi22
  let D' : ModuleSpec F 3 := D.map e1.toMonoidHom e1.injective
  have hcen : ∀ (X1 : Type) [Group X1] [Finite X1] (ψ : X1 →* F), Function.Surjective ψ →
      commutator X1 = ⊤ → ψ.ker ≤ Subgroup.center X1 → IsPGroup 3 ψ.ker →
        5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X1) := by
    intro X1 _ _ ψ hψ _ hker _
    have h := i1021_hcen_of_datum hnc D' hA hF X1 ψ hψ hker
    exact (show D'.n = 5 from hn) ▸ h
  exact i1021_main hnc Nat.prime_three (by norm_num) (by norm_num) hV hVc hcen _ X le_rfl φ hφ

end CFSG.HardMathSupport.Solomon.Coordinator
