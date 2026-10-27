module

public import CFSG.LocalAnalysis.RankThreeUC.U4McQuad
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFPartBN
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.U4Mc

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Quasithin CFSG.Open
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LocalAnalysis.RankThreeUC (partBAdd partBSub partBAdd_toAdd partBAdd_mul partBSub_card
  partB_fix_iff partB_add_self partB_quad partB_statedSU bnqIsLin bnqLinSub mem_bnqLinSub
  bnqLinMat mem_bnqLinMat bnqGlAct bnqGlAct_injective bnqGlAct_mul bnqGlAct_one
  bnq_exists_statedSU bnq_exists_semilinear bnq_linear_part bnq_card_le_two bnq_nonlin_fix_sq
  bnq_card_linMat bnq_quad_matrix bnq_invol_apply qdImage)

variable {S : Type} [CommGroup S] {F : Type} [Field F]

structure NatSU4 (n : ℕ) (L : Subgroup (MulAut S)) (F : Type) [Field F] where
  ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F)
  ψ : S ≃* Multiplicative (Fin 4 → F)
  equiv : ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
    (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (Multiplicative.toAdd (ψ s)))

namespace NatSU4

variable {n : ℕ} {L : Subgroup (MulAut S)} (N : NatSU4 n L F)

@[expose] def vec (s : S) : Fin 4 → F := Multiplicative.toAdd (N.ψ s)

@[expose] def mat (l : ↥L) : Matrix (Fin 4) (Fin 4) F := ((N.ε l : GL (Fin 4) F) : Matrix _ _ F)

theorem vec_mul (s t : S) : N.vec (s * t) = N.vec s + N.vec t := by
  simp [vec]

theorem vec_one : N.vec 1 = 0 := by
  simp [vec]

theorem vec_inv (s : S) : N.vec s⁻¹ = -N.vec s := by
  simp [vec]

theorem vec_injective : Function.Injective N.vec :=
  fun _ _ h => N.ψ.injective (Multiplicative.toAdd.injective h)

theorem exists_vec (x : Fin 4 → F) : ∃ s, N.vec s = x :=
  ⟨N.ψ.symm (Multiplicative.ofAdd x), by simp [vec]⟩

theorem vec_apply (l : ↥L) (s : S) : N.vec ((l : MulAut S) s) = N.mat l *ᵥ N.vec s := by
  rw [vec, N.equiv]
  rfl

theorem partBAdd_vec (g : MulAut S) (s : S) : partBAdd N.ψ g (N.vec s) = N.vec (g s) :=
  partBAdd_toAdd N.ψ g s

theorem mat_mem (hF : Nat.card F = (2 ^ n) ^ 2) [Finite F] [CharP F 2] (l : ↥L) :
    (N.ε l : GL (Fin 4) F) ∈ SUid (unitaryInvolution F 2 n) 4 := by
  rw [SUid_eq_statedSU hF 4]
  exact (N.ε l).2

theorem herm_mat (hF : Nat.card F = (2 ^ n) ^ 2) [Finite F] [CharP F 2] (l : ↥L)
    (x y : Fin 4 → F) :
    herm (unitaryInvolution F 2 n) (N.mat l *ᵥ x) (N.mat l *ᵥ y) =
      herm (unitaryInvolution F 2 n) x y :=
  ((mem_SUid_iff _).mp (N.mat_mem hF l)).2 x y

include N in
theorem card_eq [Finite F] : Nat.card S = Nat.card F ^ 4 := by
  rw [Nat.card_congr (N.ψ.toEquiv.trans Multiplicative.toAdd), Nat.card_fun]
  simp

end NatSU4

theorem arith_nonlin_lt {b c l q r : ℕ} (hq : 4 ≤ q) (hr : r ≤ 2) (hb : b ≤ 2 * l)
    (hl : l ^ 2 ≤ q ^ (r ^ 2)) (hc : c ^ 2 ≤ q ^ (4 - r)) : b * c < q ^ 4 := by
  have hexp : r ^ 2 + (4 - r) ≤ 6 := by
    interval_cases r <;> norm_num
  have h6 : q ^ (r ^ 2) * q ^ (4 - r) ≤ q ^ 6 := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) hexp
  have hq2 : 4 < q ^ 2 := by nlinarith
  have h1 : (b * c) ^ 2 < (q ^ 4) ^ 2 := by
    calc (b * c) ^ 2 = b ^ 2 * c ^ 2 := mul_pow b c 2
      _ ≤ (2 * l) ^ 2 * c ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hb 2)
      _ = 4 * (l ^ 2 * c ^ 2) := by ring
      _ ≤ 4 * (q ^ (r ^ 2) * q ^ (4 - r)) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul hl hc)
      _ ≤ 4 * q ^ 6 := Nat.mul_le_mul_left 4 h6
      _ < q ^ 2 * q ^ 6 := Nat.mul_lt_mul_of_pos_right hq2 (by positivity)
      _ = (q ^ 4) ^ 2 := by ring
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h1

theorem exact_offender [Finite S] (hS : ∀ s : S, s ^ 2 = 1) [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) {L : Subgroup (MulAut S)} (N : NatSU4 n L F)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian2 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S))) (hA1 : A ≠ ⊥)
    (hoff : Nat.card S ≤ Nat.card A * Nat.card (fixV A)) :
    A ≤ L ∧ Nat.card F ^ 2 ≤ Nat.card A ∧
      ∃ W : Submodule F (Fin 4 → F), IsTI (unitaryInvolution F 2 n) W ∧
        Module.finrank F W = 2 ∧ (∀ a ∈ A, ∀ s : S, N.vec (a s) - N.vec s ∈ W) ∧
        ∀ s : S, s ∈ fixV A ↔ N.vec s ∈ W := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have hSU : SUid σ 4 = StatedSU 4 (2 ^ n) F := SUid_eq_statedSU hF 4
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hq4 : 4 ≤ Nat.card F := by
    have h2n : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2n 2
  obtain ⟨B₀, hB₀A, hB₀, hB₀c⟩ := B1.exists_offender_below (X := A) (A := A)
    ⟨le_rfl, hA1, hA⟩ 0 (by simpa using hoff)
  obtain ⟨Q, hQB, hQ, hQq, hQc, -, -⟩ := exists_quadratic_offender_le hS hB₀
  have hQA : Q ≤ A := hQB.trans hB₀A
  have hQel : IsElemAbelian2 Q := hQ.2.2.1
  have hQ1 : Q ≠ ⊥ := hQ.2.1
  have hQoff : Nat.card S ≤ Nat.card Q * Nat.card (fixV Q) := by
    rw [hQc]
    simpa using hB₀c
  set BQ := partBSub N.ψ Q with hBQ
  have h2 := partB_add_self N.ψ hQel
  have hquad := partB_quad N.ψ hQq
  have hN := partB_statedSU N.ε N.ψ N.equiv hAN hQA
  let e : (Fin 4 → F) ≃ S :=
    (Multiplicative.ofAdd : (Fin 4 → F) ≃ Multiplicative (Fin 4 → F)).trans N.ψ.symm.toEquiv
  have hfixeq : Nat.card {x : Fin 4 → F // ∀ a ∈ BQ, a x = x} = Nat.card (fixV Q) :=
    Nat.card_congr (Equiv.subtypeEquiv e fun x => partB_fix_iff N.ψ Q x)
  have hineq : Nat.card F ^ 4 ≤ Nat.card BQ * Nat.card {x : Fin 4 → F // ∀ a ∈ BQ, a x = x} := by
    rw [partBSub_card, hfixeq, ← N.card_eq]
    exact hQoff
  have hlin : ∀ a ∈ BQ, bnqIsLin a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hsB, hsnl⟩ := hcon
    obtain ⟨r, hr, hLF, hL⟩ := bnq_linear_part hF BQ h2 hquad hN
    have hb := bnq_card_le_two hF BQ h2 hN hsB hsnl
    have hc := bnq_nonlin_fix_sq hF BQ h2 hquad hN hsB hsnl
    rw [hLF] at hc
    have := arith_nonlin_lt hq4 hr hb hL hc
    omega
  set Bm := bnqLinMat BQ with hBm
  have hmemB : ∀ g ∈ Bm, bnqGlAct g ∈ BQ := fun g hg => (mem_bnqLinSub.mp (mem_bnqLinMat.mp hg)).1
  have hBmU : Bm ≤ SUid σ 4 := by
    rw [hSU]
    intro g hg
    obtain ⟨g₀, hg₀, h₀⟩ := bnq_exists_statedSU hF BQ h2 hN (mem_bnqLinMat.mp hg)
    rw [← bnqGlAct_injective h₀]
    exact hg₀
  have hquadM : ∀ b ∈ Bm, ∀ b' ∈ Bm,
      ((b : Matrix (Fin 4) (Fin 4) F) - 1) * ((b' : Matrix (Fin 4) (Fin 4) F) - 1) = 0 :=
    fun b hb b' hb' => bnq_quad_matrix (g := b) (g' := b')
      (fun x => hquad (bnqGlAct b) (hmemB b hb) (bnqGlAct b') (hmemB b' hb') x)
  have hinv : ∀ b ∈ Bm, b * b = 1 := fun b hb =>
    bnqGlAct_injective (by
      rw [bnqGlAct_mul, bnqGlAct_one]
      exact h2 _ (hmemB b hb))
  have hsurj : ∀ a ∈ BQ, ∃ g ∈ Bm, bnqGlAct g = a := by
    intro a ha
    obtain ⟨g, -, hga⟩ := bnq_exists_statedSU hF BQ h2 hN ⟨ha, hlin a ha⟩
    exact ⟨g, mem_bnqLinMat.mpr (by rw [hga]; exact ⟨ha, hlin a ha⟩), hga⟩
  have hBmcard : Nat.card Bm = Nat.card BQ := by
    rw [bnq_card_linMat hF BQ h2 hN]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a =>
      ⟨fun h => h.1, fun h => ⟨h, hlin a h⟩⟩)
  have hBmfix : Nat.card {x : Fin 4 → F // ∀ b ∈ Bm, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x} =
      Nat.card {x : Fin 4 → F // ∀ a ∈ BQ, a x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun hx a ha => ?_, fun hx b hb => hx _ (hmemB b hb)⟩)
    obtain ⟨g, hg, rfl⟩ := hsurj a ha
    exact hx g hg
  have hBQQ : Nat.card BQ = Nat.card Q := partBSub_card N.ψ Q
  have hBm1 : Bm ≠ ⊥ := by
    intro h
    apply hQ1
    rw [← Subgroup.card_eq_one, ← hBQQ, ← hBmcard, h, Subgroup.card_bot]
  obtain ⟨hcardBm, hWti, hW2, hWfix, htv⟩ := su4_quadratic_structure hσ Bm hBmU hinv hquadM hBm1
    (by rw [hBmcard, hBmfix]; exact hineq)
  have hcommA : ∀ a ∈ A, (∀ w ∈ qdImage Bm, partBAdd N.ψ a w = w) ∧
      (∀ x, partBAdd N.ψ a x - x ∈ qdImage Bm) ∧ bnqIsLin (partBAdd N.ψ a) := by
    intro a ha
    have ha2 : partBAdd N.ψ a + partBAdd N.ψ a = 0 := partB_add_self N.ψ hA _ ⟨a, ha, rfl⟩
    have hNa := partB_statedSU N.ε N.ψ N.equiv hAN le_rfl _ ⟨a, ha, rfl⟩
    obtain ⟨θ, hθ⟩ := bnq_exists_semilinear hF ha2 hNa
    have hcomm : ∀ u ∈ qdImage Bm, ∀ x, partBAdd N.ψ a (x + herm σ u x • u) =
        partBAdd N.ψ a x + herm σ u (partBAdd N.ψ a x) • u := by
      intro u hu x
      obtain ⟨g, hg, hgx⟩ := htv u hu
      obtain ⟨q, hq, hqg⟩ := hmemB g hg
      have hsum : partBAdd N.ψ a + bnqGlAct g = bnqGlAct g + partBAdd N.ψ a := by
        rw [← hqg, ← partBAdd_mul, ← partBAdd_mul, hA.1 a ha q (hQA hq)]
      have h' : partBAdd N.ψ a ((g : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
          (g : Matrix (Fin 4) (Fin 4) F) *ᵥ (partBAdd N.ψ a x) :=
        congrArg (fun e : AddAut (Fin 4 → F) => e x) hsum
      rw [hgx, hgx] at h'
      exact h'
    obtain ⟨hθid, hWa, hquot⟩ := commutant_transvections h2F hWti hW2 (bnq_invol_apply ha2) hθ
      hcomm
    exact ⟨hWa, hquot, fun c x => by rw [hθ, hθid]⟩
  refine ⟨fun a ha => ?_, ?_, qdImage Bm, hWti, hW2, fun a ha s => ?_, fun s => ⟨fun hs => ?_,
    fun hs => ?_⟩⟩
  ·
    obtain ⟨g, hg, hga⟩ := bnq_exists_statedSU hF (partBSub N.ψ A) (partB_add_self N.ψ hA)
      (partB_statedSU N.ε N.ψ N.equiv hAN le_rfl) ⟨⟨a, ha, rfl⟩, (hcommA a ha).2.2⟩
    have hl : ((N.ε.symm ⟨g, hg⟩ : ↥L) : MulAut S) = a := by
      refine MulEquiv.ext fun s => N.vec_injective ?_
      rw [N.vec_apply, NatSU4.mat, MulEquiv.apply_symm_apply, ← N.partBAdd_vec, ← hga]
      rfl
    rw [← hl]
    exact (N.ε.symm ⟨g, hg⟩).2
  · calc Nat.card F ^ 2 = Nat.card Q := by rw [← hcardBm, hBmcard, hBQQ]
      _ ≤ Nat.card A := Subgroup.card_le_of_le hQA
  · rw [← N.partBAdd_vec]
    exact (hcommA a ha).2.1 _
  · rw [hWfix]
    intro b hb
    obtain ⟨q, hq, hqb⟩ := hmemB b hb
    have h1 : bnqGlAct b (N.vec s) = N.vec s := by
      rw [← hqb, N.partBAdd_vec, hs q (hQA hq)]
    exact h1
  · intro a ha
    apply N.vec_injective
    rw [← N.partBAdd_vec]
    exact (hcommA a ha).1 _ hs

end CFSG.LocalAnalysis.RankThreeUC.U4Mc
