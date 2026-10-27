module

public import CFSG.CGT.PushingUpLit.SolKR2.Partition
public import CFSG.CGT.PushingUpLit.SolKR2.Torus

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.PartTwo (omegaOneSub)

variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

section Cert

variable
  (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) (h : R2 M B)
include hCen hU h

theorem sigCover_of_witness
    (hγ : ∀ f e e' : G, conjSubgroup e (omegaOneSub B) ≤
        Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G) →
      conjSubgroup e' (omegaOneSub B) ≤
        Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G) →
      ∀ a ∈ conjSubgroup e (omegaOneSub B), ∀ b ∈ conjSubgroup e' (omegaOneSub B),
        a * b = b * a)
    {e e' w : G} (hne : conjSubgroup e (omegaOneSub B) ≠ conjSubgroup e' (omegaOneSub B))
    (hcomm1 : ∀ a ∈ conjSubgroup e (omegaTwoSub B), ∀ b ∈ conjSubgroup e' (omegaTwoSub B),
      a * b = b * a)
    (hw : conjSubgroup w (omegaTwoSub B) ≤
      Subgroup.centralizer (conjSubgroup e (omegaTwoSub B) : Set G))
    (hwnc : ¬ ∀ a ∈ conjSubgroup w (omegaTwoSub B), ∀ b ∈ conjSubgroup e' (omegaTwoSub B),
      a * b = b * a)
    {F'' : Subgroup G} (hF'' : IsSig B F'')
    (hle : F'' ≤ conjSubgroup e (omegaOneSub B) ⊔ conjSubgroup e' (omegaOneSub B))
    (h1 : F'' ≠ conjSubgroup e (omegaOneSub B)) (h2 : F'' ≠ conjSubgroup e' (omegaOneSub B)) :
    SigCover B (conjSubgroup e (omegaOneSub B) ⊔ conjSubgroup e' (omegaOneSub B)) :=
  sigCover_of_witness_of_lemma h (fun _ _ P h16 h4 => by
    obtain ⟨K, hKX, hK3, hKE, hKV, hfV, -⟩ := P.exists_torus hCen hU h16 h4
    unfold HasTorus
    exact ⟨K, hKX, hK3, hKE, hKV, hfV⟩) hγ hne hcomm1 hw hwnc hF'' hle h1 h2

end Cert

end CFSG.CGT.PushingUpLit.SolKR2
