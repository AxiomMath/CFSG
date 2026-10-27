module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21BranchZ
public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixTwoA

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_branch_Z_false (h : Sec622Bar G t u x) {L M : Subgroup G} (hLn : L.Normal)
    [IsSimpleGroup L] (hnonab : ∃ a b : L, a * b ≠ b * a)
    (hcent : centralizer (L : Set G) = ⊥) (htL : t ∉ L) (hM : fusionIsSylowIn 2 M L)
    (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M)
    (hMC : fusionIsSylowIn 2 (M ⊓ centralizer ({t} : Set G)) (L ⊓ centralizer ({t} : Set G)))
    {w : G} (hw : w = u ∨ w = t * u) (hZ : M ⊓ centralizer ({t} : Set G) = zpowers w)
    (hcard : Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 4 ∨
      Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 20)
    : False :=
  sec622_branch_Z_false_of h hLn hnonab hcent htL hM hMt hMC hw hZ hcard
    (sec622_six_two h.secTwo h.exp_two)

end CFSG.LocalAnalysis.EvenBN.Tits
