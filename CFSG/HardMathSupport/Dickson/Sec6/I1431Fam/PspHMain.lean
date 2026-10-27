module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHData
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShell

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Dickson.Sec6.I923

theorem t6psph_conj_injective_of_center {T : Type} [Group T] (hZ : Subgroup.center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [← hZ, Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun α : MulAut T => α g) (MonoidHom.mem_ker.1 hs)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * s = s * g * s⁻¹ * s := by rw [h]
    _ = s * g := by group

theorem t6psph_center_statedProj_statedSp {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 3 ≤ r) :
    Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
  have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
      (Nat.card K = 2 ∧ 3 ≤ r) := by
    by_cases h4 : 4 ≤ Nat.card K
    · exact Or.inl (Or.inr h4)
    · rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with h | h
      · exact Or.inr (Or.inr ⟨h, hr⟩)
      · exact Or.inr (Or.inl ⟨h, by omega⟩)
  obtain ⟨-, hsimple, hnab⟩ := CFSG.LieType.Universal.Symplectic.isQuasisimple r K (by omega) hq
  haveI := hsimple
  have hc := center_eq_bot_of_simple hnab
  rw [← Subgroup.map_center_eq (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv r K), hc,
    Subgroup.map_bot]

theorem t6psph_ker_cube {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 1 ≤ r) :
    ∀ z ∈ (SymplecticFlag.proj r K).ker, z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  rw [SymplecticHigher.ker_proj] at hz
  have h1 : orderOf z ∣ Nat.card (SymplecticHigher.spScalars r K) :=
    Subgroup.orderOf_dvd_natCard _ hz
  rw [card_spScalars_eq_gcd K hr] at h1
  have h2 : orderOf z ∣ 2 := h1.trans (Nat.gcd_dvd_left 2 _)
  have h3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  have h4 : orderOf z ∣ Nat.gcd 2 3 := Nat.dvd_gcd h2 h3
  have h5 : orderOf z = 1 := Nat.dvd_one.mp (by simpa using h4)
  exact orderOf_eq_one_iff.mp h5

theorem s1431_false_psp {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 3 ≤ r) (hpK : (3 : K) ≠ 0)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {A : Subgroup (MulAut (StatedProj (StatedSp r K)))} {ψ : MulAut (StatedProj (StatedSp r K))}
    {J : Subgroup (StatedProj (StatedSp r K))} {q : ℕ}
    (c : S1431Cfg (StatedProj (StatedSp r K)) A ψ J q) (hq : 10 ≤ q)
    (hA : ∀ a ∈ A, IsInnerAut a) : False := by
  have hker : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  exact s1431_false_of_lift_blocks (SymplecticFlag.proj r K) SymplecticHigher.proj_surjective hker
    (t6psph_ker_cube (by omega))
    (t6psph_conj_injective_of_center (t6psph_center_statedProj_statedSp hr)) c hA
    fun a ha3 hπa => t6psph_data_psp hO (by omega) hpK hq a ha3 hπa

end CFSG.HardMathSupport.Dickson.Sec6.I1431
