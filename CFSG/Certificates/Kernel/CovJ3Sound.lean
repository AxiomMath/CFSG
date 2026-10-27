module

public import Certificates.Data.Kernel.CovJ3
public import CFSG.Certificates.Kernel.OpsLayGKFSound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.CovJ3

open CFSG.SectionRank.Native CFSG.GH74.KGroups.J3 CFSG.KC.OpsK CFSG.KC.OpsV4

theorem wordT_eq {V : Type} (O : Ops Nat V) (A B : Nat) (w : List ℤ) :
    wordT O A B (O.mul B B) w = wordMat O A B w := rfl

theorem xT_eq {V : Type} (O : Ops Nat V) (A B : Nat) (ws : List (List ℤ)) (i : Nat) :
    xT O A B (O.mul B B) ws i = xOf O A B ws i := rfl

theorem conjT_eq {V : Type} (O : Ops Nat V) (A B : Nat) (ws : List (List ℤ)) (tests : List ℕ) :
    conjT O A B ws tests = conjCheckAux O A B ws tests := by
  unfold conjT bodyT
  simp only [forceB_eq, wordT_eq, xT_eq]
  rfl

section Sim

variable {M V₀ V : Type} {O₀ : Ops M V₀} {O : Ops Nat V} (S : Sim O₀ O) {A B : M} {a b : Nat}

theorem letterMat_of (hA : S.R A a) (hB : S.R B b) (z : ℤ) :
    S.R (letterMat O₀ A B z) (letterMat O a b z) := by
  unfold letterMat
  split_ifs
  · exact hA
  · exact hB
  · exact S.mul hB hB
  · exact S.one

theorem wordMat_of (hA : S.R A a) (hB : S.R B b) :
    ∀ w : List ℤ, S.R (wordMat O₀ A B w) (wordMat O a b w)
  | [] => S.one
  | z :: w => S.mul (letterMat_of S hA hB z) (wordMat_of hA hB w)

theorem xOf_of (hA : S.R A a) (hB : S.R B b) (ws : List (List ℤ)) (i : Nat) :
    S.R (xOf O₀ A B ws i) (xOf O a b ws i) :=
  S.mul (S.mul (wordMat_of S hA hB _) hA) (wordMat_of S hA hB _)

theorem xsOf_of (hA : S.R A a) (hB : S.R B b) (ws : List (List ℤ)) :
    List.Forall₂ S.R (xsOf O₀ A B ws) (xsOf O a b ws) :=
  .cons (xOf_of S hA hB ws 0) (.cons (xOf_of S hA hB ws 1) (.cons (xOf_of S hA hB ws 2)
    (.cons (xOf_of S hA hB ws 3) .nil)))

theorem conjCheckAux_of_sim (hA : S.R A a) (hB : S.R B b) {ws : List (List ℤ)}
    {tests : List ℕ} (hT : ∀ k ∈ tests, S.T k) (h : conjCheckAux O a b ws tests = true) :
    conjCheckAux O₀ A B ws tests = true := by
  have hxs := xsOf_of S hA hB ws
  unfold conjCheckAux at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨hAA, hBB⟩, hlen⟩, hk⟩, hsq⟩, hc⟩, hker⟩ := h
  refine ⟨⟨⟨⟨⟨⟨S.eq (S.mul hA hA) S.one hAA, S.eq (S.mul hB (S.mul hB hB)) S.one hBB⟩, hlen⟩,
    ?_⟩, all_of_forall₂ (p := fun X => O₀.eq (O₀.mul X X) O₀.one)
      (q := fun x => O.eq (O.mul x x) O.one) (fun _ _ hX hx => S.eq (S.mul hX hX) S.one hx) hxs
      hsq⟩, S.commsOK hxs hc⟩, CFSG.KC.OpsLayGKF.kerModOK_of S S.one hxs hT hker⟩
  refine List.all_eq_true.2 fun k hkm => ?_
  have hk' := List.all_eq_true.1 hk k hkm
  simp only [Bool.and_eq_true] at hk' ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hk'
  have g := wordMat_of S hA hB (ws.getD k [])
  have gi := wordMat_of S hA hB (invWord (ws.getD k []))
  exact ⟨⟨S.eq (S.mul g gi) S.one h1, S.eq (S.mul gi g) S.one h2⟩,
    S.eq (S.mul g (xOf_of S hA hB ws 0)) (S.mul (CFSG.KC.OpsLayGKF.prodBase2_of S hxs (k + 1)) g)
      h3⟩

end Sim

end CFSG.KC.CovJ3

end
