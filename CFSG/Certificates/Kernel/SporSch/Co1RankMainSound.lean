module

public import CFSG.Certificates.Kernel.SporSch.Co1RankClassSound

public section

namespace CFSG.KS.SporSch.Co1Rank

open CFSG.KC CFSG.KC.Loop CFSG.KC.Co1RankCoord CFSG.KC.Co1RankTab CFSG.KC.Co1B CFSG.KC.Co1Cl
  CFSG.KC.Co1RankRec CFSG.KC.Co1RankBnd CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

theorem card_le_of_tables
    (hA₁ : ((A₁ : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank ≠ 8)
    (hcG : ((cG : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank ≠ 8)
    {T : Co1RankTab.Dat} {R : List Reps} {Dr : Co1RankRec.Dat} {gens : ℕ → GL24}
    (hM : chkM T = true) (hT : chkT T = true) (htab : tabOK T = true)
    (hlen : T.BS.length = T.d) (hP : chkP T = true) (hR : chkR T R Dr = true)
    (hC : ∀ n < 4, ∀ p ∈ getD [] R n, ∃ C : Co1RankCand.Dat, Co1RankCand.chkC C = true ∧
      bndOK C = true ∧ sameTab C T = true ∧ p ∈ C.reps)
    (hG : ∀ g < T.nG, matK (getM T.G g) = (gens g : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    (hGA : ∀ g < T.nG, gens g ∈ GA) {c : GL24}
    (hc : matK T.cM = (c : Matrix (Fin 24) (Fin 24) (ZMod 2))) :
    Nat.card (Subgroup.closure (gens '' {g | g < T.nG})) = 2 ^ (T.d + 7) ∧
      ∀ B : Subgroup GL24, B ≤ Subgroup.closure (gens '' {g | g < T.nG}) →
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → c ∈ B →
        (∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) → Nat.card B ≤ 16 := by
  obtain ⟨hMod, h0, hcl, hcard, hinj⟩ := closure_eq_of_checks hM hT htab hlen hG
  obtain ⟨-, -, hrel⟩ := model_of_checks hM hT htab hG
  obtain ⟨hn1, hn5, hU0, hUinj⟩ := repN_of_checks hR
  refine ⟨hcard, fun B hBS hcomm hsq hcB hnonA => ?_⟩
  have hSGA : elSub hMod h0 ≤ GA := by
    rw [← hcl, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hGA g hg
  have hc0 : el T.d (bU T) (wU T gens) (uC T 0) = c := by
    obtain ⟨-, -, -, -, -, -, hcM, -⟩ := chkM_sound hM
    refine Units.ext ?_
    rw [matK_eltM hM htab hG (uC_lt T 0), ← hc, ← hcM]
    rfl
  have hA : ∀ s ∈ elSub hMod h0, ∀ x, s * x * s⁻¹ ∈ {x : GL24 | (xFix x).ncard = 2280} ↔
      x ∈ {x : GL24 | (xFix x).ncard = 2280} := by
    intro s hs x
    simp only [Set.mem_setOf_eq]
    rw [ncard_fix_conj (hSGA hs)]
  have hA2 : ∀ z < 2 ^ ((Co1RankTab.toC T).d + 7), Co1RankCand.in2A (candT T) z = true →
      el (Co1RankTab.toC T).d (bU T) (wU T gens) z * el (Co1RankTab.toC T).d (bU T) (wU T gens) z
        = 1 → el (Co1RankTab.toC T).d (bU T) (wU T gens) z ≠ 1 →
      el (Co1RankTab.toC T).d (bU T) (wU T gens) z ∈ {x : GL24 | (xFix x).ncard = 2280} :=
    fun z hz htA hzz hz1 =>
      twoA_of_checks hA₁ hcG hM htab hG hz htA (hSGA ⟨z, hz, rfl⟩) hzz hz1
  have hgg : ∀ g < T.nG, gens g ∈ elSub hMod h0 := fun g hg => by
    rw [← hcl]
    exact Subgroup.subset_closure ⟨g, hg, rfl⟩
  have hE : Good (elSub hMod h0) {x : GL24 | (xFix x).ncard = 2280} B := by
    unfold Good
    exact ⟨hcl ▸ hBS, hsq, hcomm, fun x hx hx1 => hnonA x hx hx1⟩
  have hcB' : el (Co1RankTab.toC T).d (bU T) (wU T gens) (uC T 0) ∈ B := by
    change el T.d (bU T) (wU T gens) (uC T 0) ∈ B
    rw [hc0]
    exact hcB
  exact card_le_of_coords hMod h0 hinj (U := uC T) (fun u _ => uC_lt T u) hU0 hUinj hA hA2 hgg
    (P_conj_of_checks hMod h0 hrel hP) hn1 hn5 (repOK_of_checks (bU T) (wU T gens) hR hC) hE hcB'

end CFSG.KS.SporSch.Co1Rank

end
