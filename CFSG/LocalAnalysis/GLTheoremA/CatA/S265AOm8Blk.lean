module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AOm8Comp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ABlk
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om7
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open Module QuadraticMap CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem exists_glaPLayer_ne_bot_om8 (hF : Nat.card F = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank F V = 8) {A : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian 3 A)
    (h27 : 27 ≤ Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧ GLAPLayer 3 (Subgroup.centralizer ({a} : Set ↥(orthDerived Q))) ≠ ⊥ := by
  haveI := CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.charP_two hF
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hpF : ((3 : ℕ) : F) ≠ 0 := cast_prime_ne_zero Nat.prime_three (by decide)
  by_contra hcon'
  have hcon : ∀ a ∈ A, a ≠ 1 →
      GLAPLayer 3 (Subgroup.centralizer ({a} : Set ↥(orthDerived Q))) = ⊥ :=
    fun a ha ha1 => by_contra fun hL => hcon' ⟨a, ha, ha1, hL⟩
  obtain ⟨A₀, hA₀A, hA₀c⟩ : ∃ A₀ ≤ A, Nat.card A₀ = 27 := by
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 3) Nat.prime_three
      hA.isPGroup (by norm_num; exact h27)
    refine ⟨K.map A.subtype, Subgroup.map_subtype_le K, ?_⟩
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective K _ A.subtype_injective).toEquiv, hK]
    norm_num
  have hA₀ : IsElemAbelian 3 A₀ := hA.mono hA₀A
  letI : Fintype ↥(orthImage A₀) := Fintype.ofFinite _
  have hAe : IsElemAbelian 3 (orthImage A₀) := isElemAbelian_orthImage hA₀
  have hB : ∀ a : ↥(orthImage A₀), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v :=
    fun a => polar_orthImage (Ã := A₀) a
  have hcard : Fintype.card ↥(orthImage A₀) = 27 := by
    rw [Fintype.card_eq_nat_card, ← hA₀c]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective A₀ _ (orthDerived Q).subtype_injective).toEquiv).symm
  have hev : ∀ D : Hyperplane (orthImage A₀) 3, Even (finrank F ↥(blockSpace (orthImage A₀) D.1)) :=
    fun D => even_finrank_blockSpace (orthImage A₀) h2 hQ Nat.prime_three hpF hAe hB D
  have hsplit : ∀ a, nOut (fun D : Hyperplane (orthImage A₀) 3 => D.1)
      (fun D => finrank F ↥(blockSpace (orthImage A₀) D.1)) a =
      2 * nOut (fun D : Hyperplane (orthImage A₀) 3 => D.1)
        (fun D => finrank F ↥(blockSpace (orthImage A₀) D.1) / 2) a := by
    intro a
    unfold nOut
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun D _ => ?_
    split_ifs
    · rfl
    · obtain ⟨k, hk⟩ := hev D
      dsimp only
      omega
  have hM : ∑ D : Hyperplane (orthImage A₀) 3,
      finrank F ↥(blockSpace (orthImage A₀) D.1) / 2 ≤ 4 := by
    have h1 := sum_finrank_blockSpace_le_finrank (orthImage A₀) Nat.prime_three hpF hAe
    have h2' : ∑ D : Hyperplane (orthImage A₀) 3, finrank F ↥(blockSpace (orthImage A₀) D.1) =
        2 * ∑ D : Hyperplane (orthImage A₀) 3,
          finrank F ↥(blockSpace (orthImage A₀) D.1) / 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun D _ => ?_
      obtain ⟨k, hk⟩ := hev D
      omega
    omega
  refine false_of_nOut_two_three (fun D : Hyperplane (orthImage A₀) 3 => D.1)
    (fun D => finrank F ↥(blockSpace (orthImage A₀) D.1) / 2) (fun D => D.2)
    (fun D => ⟨fun n hn g => ?_⟩) Subtype.val_injective (fun a ha1 => ?_) hM (Or.inl hcard)
  · have := hAe.1
    rwa [mul_comm' g n, mul_inv_cancel_right]
  · obtain ⟨a', ha'A₀, ha'⟩ := Subgroup.mem_map.mp a.2
    have ha'1 : a' ≠ 1 := fun h1 => ha1 (Subtype.ext (by rw [← ha', h1]; rfl))
    have ha'3 : a' ^ 3 = 1 := hA₀.2 a' ha'A₀
    have hfs : fixedByEnd (a : V ≃ₗ[F] V) = fixedSpace (a' : V ≃ₗ[F] V) := by
      ext v
      rw [mem_fixedByEnd, CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace, ← ha']
      rfl
    have hbr := finrank_eq_fixedByEnd_add_nOut (orthImage A₀) Nat.prime_three hpF hAe a
    rw [hsplit, hdim] at hbr
    generalize nOut (fun D : Hyperplane (orthImage A₀) 3 => D.1)
      (fun D => finrank F ↥(blockSpace (orthImage A₀) D.1) / 2) a = N at hbr ⊢
    have hlay := hcon a' (hA₀A ha'A₀) ha'1
    by_contra hN
    rcases (by omega : N = 0 ∨ N = 1 ∨ N = 4) with h0 | h1 | h4
    · have htop : fixedByEnd (a : V ≃ₗ[F] V) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by omega)
      refine ha1 (Subtype.ext (LinearEquiv.ext fun v => ?_))
      have hv : v ∈ fixedByEnd (a : V ≃ₗ[F] V) := by
        rw [htop]
        exact Submodule.mem_top
      rw [mem_fixedByEnd] at hv
      simpa using hv
    · rw [hfs] at hbr
      exact glaPLayer_ne_bot_of_orth_three hF hQ ha'3 (Or.inl (by omega)) hlay
    · rw [hfs] at hbr
      exact glaPLayer_ne_bot_of_orth_three hF hQ ha'3 (Or.inr (by omega)) hlay

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
