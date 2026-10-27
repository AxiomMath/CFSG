module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks4
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Unit
import CFSG.RankThree.PartOne.LIT.RankAbstract
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Quad

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks (fixedByEnd mem_fixedByEnd)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux (card_two_charP)

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem exists_pow_mul_fixedSpace_eq_two (hF : Nat.card F = 2) (hV : finrank F V = 10)
    {d e : V ≃ₗ[F] V} (he3 : e ^ 3 = 1) (hde : d * e = e * d) (hd : fixedByEnd d = ⊥)
    (he : finrank F ↥(fixedByEnd e) = 8) :
    ∃ k : ℕ, finrank F ↥(fixedSpace (d * e ^ k)) = 2 ∧
      ∀ v ∈ primaryComponent (d * e ^ k : V ≃ₗ[F] V).toLinearMap (cyc3 F), e v = v := by
  classical
  haveI := card_two_charP hF
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hww : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul F x, h2, zero_smul]
  have hc := LIT.isCompl_fixedSpace_commSpace (cast_three_ne_zero_of_card_two hF) he3
  set C := LIT.fixedSpace e
  set M := LIT.commSpace e
  have hCmem : ∀ v, v ∈ C ↔ e v = v := fun v => LIT.mem_fixedSpace
  have hMmem : ∀ w, w ∈ M ↔ ∃ y, e y - y = w := fun w => LIT.mem_commSpace
  have hCeq : C = fixedByEnd e := by
    ext v
    rw [hCmem, mem_fixedByEnd]
  have hM2 : finrank F M = 2 := by
    have h := Submodule.finrank_add_eq_of_isCompl hc
    rw [hCeq, he, hV] at h
    omega
  have hdc : ∀ x, d (e x) = e (d x) := fun x => LinearEquiv.congr_fun hde x
  have hdC : ∀ c ∈ C, d c ∈ C := fun c hc' =>
    (hCmem _).2 (by rw [← hdc, (hCmem c).1 hc'])
  have hdM : ∀ m ∈ M, d m ∈ M := fun m hm => by
    obtain ⟨y, rfl⟩ := (hMmem m).1 hm
    exact (hMmem _).2 ⟨d y, by rw [map_sub, hdc]⟩
  have heM : ∀ m ∈ M, e m ∈ M := fun m hm => by
    obtain ⟨y, rfl⟩ := (hMmem m).1 hm
    exact (hMmem _).2 ⟨e y, (map_sub e _ _).symm⟩
  have hCM : ∀ m, m ∈ C → m ∈ M → m = 0 := fun m hmC hmM =>
    Submodule.disjoint_def.1 hc.1 m hmC hmM
  have he3' : ∀ y, e (e (e y)) = y := fun y => by
    have h := LinearEquiv.congr_fun he3 y
    simpa [pow_succ] using h
  have hMsum : ∀ m ∈ M, e (e m) + e m + m = 0 := fun m hm => by
    obtain ⟨y, rfl⟩ := (hMmem m).1 hm
    simp only [map_sub, he3']
    abel
  have hdfix : ∀ x, d x = x → x = 0 := fun x hx => by
    have h : x ∈ fixedByEnd d := mem_fixedByEnd.2 hx
    rw [hd] at h
    exact (Submodule.mem_bot F).1 h
  obtain ⟨⟨w, hw⟩, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < finrank F M)
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hew : e w ∈ M := heM w hw
  have hew0 : e w ≠ 0 := fun h => hw0' (by simpa using h)
  have hewne : w ≠ e w := fun h => hw0' (hCM w ((hCmem w).2 h.symm) hw)
  have hspan : ∀ v ∈ M, v = 0 ∨ v = w ∨ v = e w ∨ v = w + e w := fun v hv =>
    eq_zero_or_eq_or_eq_add_of_finrank_two hF hM2 hw hew hw0' hew0 hewne hv
  have hee : e (e w) + e w = w := add_right_cancel ((hMsum w hw).trans (hww w).symm)
  obtain ⟨k, hkw⟩ : ∃ k : ℕ, (d * e ^ k) w = w := by
    have hdw0 : d w ≠ 0 := fun h => hw0' (by simpa using h)
    rcases hspan (d w) (hdM w hw) with h | h | h | h
    · exact absurd h hdw0
    · exact absurd (hdfix w h) hw0'
    · refine ⟨2, ?_⟩
      rw [LinearEquiv.mul_apply, pow_two, LinearEquiv.mul_apply, hdc, hdc, h, he3']
    · refine ⟨1, ?_⟩
      rw [LinearEquiv.mul_apply, pow_one, hdc, h, map_add, add_comm, hee]
  have hae : ∀ x, (d * e ^ k) (e x) = e ((d * e ^ k) x) := fun x =>
    LinearEquiv.congr_fun (Commute.mul_right (show Commute d e from hde).symm
      (Commute.pow_right (Commute.refl e) k)).eq.symm x
  have hfixpow : ∀ (n : ℕ) (c : V), e c = c → (e ^ n) c = c := fun n c hc' => by
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hc', ih]
  have hac : ∀ c, e c = c → (d * e ^ k) c = d c := fun c hc' => by
    rw [LinearEquiv.mul_apply, hfixpow k c hc']
  have hamM : ∀ m ∈ M, (d * e ^ k) m = m := by
    intro m hm
    rcases hspan m hm with h | h | h | h
    · rw [h, map_zero]
    · rw [h]; exact hkw
    · rw [h, hae, hkw]
    · rw [h, map_add, hae, hkw]
  have hsplit : ∀ v : V, ∃ c ∈ C, ∃ m ∈ M, c + m = v := fun v => by
    have hv : v ∈ C ⊔ M := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.1 hv
  refine ⟨k, ?_, ?_⟩
  · have hfs : fixedSpace (d * e ^ k) = M := by
      refine le_antisymm (fun v hv => ?_) (fun m hm => mem_fixedSpace.2 (hamM m hm))
      obtain ⟨c, hcC, m, hmM, rfl⟩ := hsplit v
      have h1 := mem_fixedSpace.1 hv
      rw [map_add, hac c ((hCmem c).1 hcC), hamM m hmM] at h1
      rw [hdfix c (add_right_cancel h1), zero_add]
      exact hmM
    rw [hfs, hM2]
  · intro v hv
    have h := mem_primaryComponent.1 hv
    rw [aeval_cyc3] at h
    have h' : (d * e ^ k) ((d * e ^ k) v) + (d * e ^ k) v + v = 0 := by
      simpa [pow_two] using h
    obtain ⟨c, hcC, m, hmM, rfl⟩ := hsplit v
    have hc1 := (hCmem c).1 hcC
    have hdcC := hdC c hcC
    rw [map_add, hac c hc1, hamM m hmM, map_add, hac _ ((hCmem _).1 hdcC), hamM m hmM] at h'
    have hX : (d (d c) + d c + c) + m = 0 := by
      have : (d (d c) + d c + c) + m = (d (d c) + m + (d c + m) + (c + m)) - (m + m) := by abel
      rw [this, h', hww m, sub_zero]
    have hXC : d (d c) + d c + c ∈ C := C.add_mem (C.add_mem (hdC _ hdcC) hdcC) hcC
    have hmC : m ∈ C := by
      rw [eq_neg_of_add_eq_zero_right hX]
      exact C.neg_mem hXC
    rw [hCM m hmC hmM, add_zero]
    exact hc1

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
