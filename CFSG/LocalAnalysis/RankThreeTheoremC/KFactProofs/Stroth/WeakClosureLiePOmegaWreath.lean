module

public import CFSG.GroupTheory.WeirSylow.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.GroupTheory.WeirSylow

theorem isPGroup_sigmaModel (p : ℕ) [hp : Fact p.Prime] (e a N : ℕ) :
    IsPGroup p (sigmaModel p e a N) :=
  IsPGroup.of_card (card_sigmaModel p e a N)

private theorem regularWreath_exists_ne_one (D Q : Type*) [Group D] [Group Q] [Nontrivial Q] :
    ∃ g : D ≀ᵣ Q, g ≠ 1 := by
  obtain ⟨t, ht⟩ := exists_ne (1 : Q)
  refine ⟨⟨1, t⟩, fun h => ht ?_⟩
  simpa using congrArg RegularWreathProduct.right h

private theorem regularWreath_exists_noncomm (D Q : Type*) [Group D] [Group Q] {g : D}
    (hg : g ≠ 1) {t : Q} (ht : t ≠ 1) : ∃ w₁ w₂ : D ≀ᵣ Q, w₁ * w₂ ≠ w₂ * w₁ := by
  classical
  refine ⟨⟨fun x => if x = 1 then g else 1, 1⟩, ⟨1, t⟩, fun h => ?_⟩
  have h1 := congrArg (fun w : D ≀ᵣ Q => w.left 1) h
  simp [RegularWreathProduct.mul_left, hg, ht, inv_eq_one] at h1

private theorem wreathTower_exists_ne_one (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (i : ℕ) : ∃ g : wreathTower p (Multiplicative (ZMod (p ^ a))) i, g ≠ 1 := by
  cases i with
  | zero =>
    haveI : Fact (1 < p ^ a) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
    exact exists_ne (1 : Multiplicative (ZMod (p ^ a)))
  | succ i =>
    exact regularWreath_exists_ne_one (wreathTower p (Multiplicative (ZMod (p ^ a))) i)
      (Multiplicative (ZMod p))

private theorem wreathTower_exists_noncomm (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (i : ℕ) : ∃ w₁ w₂ : wreathTower p (Multiplicative (ZMod (p ^ a))) (i + 1),
      w₁ * w₂ ≠ w₂ * w₁ := by
  obtain ⟨g, hg⟩ := wreathTower_exists_ne_one p a ha i
  obtain ⟨t, ht⟩ := exists_ne (1 : Multiplicative (ZMod p))
  exact regularWreath_exists_noncomm (wreathTower p (Multiplicative (ZMod (p ^ a))) i)
    (Multiplicative (ZMod p)) hg ht

private theorem wreathTower_exists_noncomm' (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (hn : 1 ≤ n) : ∃ w₁ w₂ : wreathTower p (Multiplicative (ZMod (p ^ a))) n,
      w₁ * w₂ ≠ w₂ * w₁ := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  exact wreathTower_exists_noncomm p a ha i

private theorem mulSingle_comm_of {ι : Type*} [DecidableEq ι] {F : ι → Type*}
    [∀ i, Group (F i)] (i : ι) {a b : F i}
    (h : (Pi.mulSingle i a : ∀ j, F j) * Pi.mulSingle i b = Pi.mulSingle i b * Pi.mulSingle i a) :
    a * b = b * a := by
  simpa using congrFun h i

theorem exists_noncomm_sigmaModel (p : ℕ) [hp : Fact p.Prime] {e a N : ℕ} (ha : 1 ≤ a)
    (hN : p ≤ N / e) : ∃ x y : sigmaModel p e a N, x * y ≠ y * x := by
  have hm0 : N / e ≠ 0 := by have := hp.out.two_le; omega
  have hL : 2 ≤ (Nat.digits p (N / e)).length := by
    rw [Nat.digits_def' hp.out.one_lt (Nat.pos_of_ne_zero hm0), List.length_cons]
    have hq : N / e / p ≠ 0 := (Nat.div_pos_iff.mpr ⟨hp.out.pos, hN⟩).ne'
    have hne : Nat.digits p (N / e / p) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hq
    have := List.length_pos_iff.mpr hne
    omega
  have hlast : (Nat.digits p (N / e))[(Nat.digits p (N / e)).length - 1]'(by omega) ≠ 0 := by
    have h := Nat.getLast_digit_ne_zero p hm0
    rwa [List.getLast_eq_getElem] at h
  let i₀ : Fin (Nat.digits p (N / e)).length := ⟨(Nat.digits p (N / e)).length - 1, by omega⟩
  let j₀ : Fin (Nat.digits p (N / e))[i₀] := ⟨0, Nat.pos_of_ne_zero hlast⟩
  obtain ⟨w₁, w₂, hw⟩ :=
    wreathTower_exists_noncomm' p a ha ((Nat.digits p (N / e)).length - 1) (by omega)
  refine ⟨Pi.mulSingle i₀ (Pi.mulSingle j₀ w₁), Pi.mulSingle i₀ (Pi.mulSingle j₀ w₂),
    fun h => ?_⟩
  apply hw
  have h1 := mulSingle_comm_of
    (F := fun i : Fin (Nat.digits p (N / e)).length =>
      Fin (Nat.digits p (N / e))[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) i) i₀ h
  exact mulSingle_comm_of j₀ h1

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
