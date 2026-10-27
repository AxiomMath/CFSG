module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinStep7
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinClaim

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem part2_2519_of_inputs (hL2p : L2pFacts) (hGen : L2pGen) : Part2_2519 := by
  intro G _ _ T M hs N t zK h I i hi
  by_contra hne
  have hlt : 4 < Nat.card (Rgrp2519 N i) := by
    have h1 : Subgroup.closure ({t, i} : Set G) < Rgrp2519 N i :=
      lt_of_le_of_ne (N.closure_le_R h.facts2511 hi) fun e => hne e.symm
    have h2 := Subgroup.card_lt_of_lt h1
    rwa [hi.card_closure h] at h2
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image {j : G | Hyp2519 N j}
    (fun j : G => toLex (Nat.card (Rgrp2519 N j),
      Nat.card ↥(N.S ⊓ Subgroup.centralizer ({j} : Set G))))
    (Set.toFinite _) ⟨i, hi⟩
  have hmax' : ∀ j : G, Hyp2519 N j →
      Nat.card (Rgrp2519 N j) < Nat.card (Rgrp2519 N a) ∨
        (Nat.card (Rgrp2519 N j) = Nat.card (Rgrp2519 N a) ∧
          Nat.card ↥(N.S ⊓ Subgroup.centralizer ({j} : Set G)) ≤
            Nat.card ↥(N.S ⊓ Subgroup.centralizer ({a} : Set G))) := fun j hj => by
    have := hmax j hj
    rwa [Prod.Lex.le_iff] at this
  have M1 : ∀ j : G, Hyp2519 N j → Nat.card (Rgrp2519 N j) ≤ Nat.card (Rgrp2519 N a) := fun j hj =>
    (hmax' j hj).elim (fun h1 => h1.le) (fun h1 => h1.1.le)
  have M2 : ∀ j : G, Hyp2519 N j → Nat.card (Rgrp2519 N j) = Nat.card (Rgrp2519 N a) →
      Nat.card ↥(N.S ⊓ Subgroup.centralizer ({j} : Set G)) ≤
        Nat.card ↥(N.S ⊓ Subgroup.centralizer ({a} : Set G)) := fun j hj hj' =>
    (hmax' j hj).elim (fun h1 => absurd hj' h1.ne) (fun h1 => h1.2)
  have hbig : 4 < Nat.card (Rgrp2519 N a) := lt_of_lt_of_le hlt (M1 i hi)
  obtain ⟨Ki, KP, R2, hid⟩ := I a ha
  exact hid.false_of_claim hL2p hGen h ha (hid.claim h ha hbig M1 M2)

end CFSG.QuasithinUnique
