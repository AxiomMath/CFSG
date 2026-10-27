module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (SLComponentsTrivial)

theorem two_eq_zero_of_natCard_pow {K : Type} [Field K] [Finite K] {m : ℕ} (hm : Nat.card K = 2 ^ m) :
    (2 : K) = 0 := by
  haveI := Fintype.ofFinite K
  obtain ⟨q, _, n, hqp, hqcard⟩ := FiniteField.card' K
  rw [Nat.card_eq_fintype_card, hqcard] at hm
  have hdvd : q ∣ 2 ^ m := by
    rw [← hm]
    exact dvd_pow_self q (PNat.ne_zero n)
  have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
  subst hq2
  exact_mod_cast CharP.cast_eq_zero K 2

theorem u64_no_three_component {d : ℕ} {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : Nat.card K = 2 ^ m) (H : Subgroup (GL (Fin d) K)) (hH : H = StatedSL d K)
    (hSL : SLComponentsTrivial) (hP1 : LinPCompIsComp) (hP2 : LinLabelDict) (hd : 1 ≤ d)
    (β : MulAut (LargeEvenProj H)) (hβ : β ^ 3 = 1)
    (hdec : ∃ u f : MulAut (LargeEvenProj H), β = u * f ∧
      u ∈ LargeEvenMatConjImage (LargeEvenProjMk H) Set.univ ∧
        f ∈ LargeEvenMatFieldImage (LargeEvenProjMk H) ∧ f ^ 3 = 1)
    (hfld : ∀ u f : MulAut (LargeEvenProj H), u ∈ LargeEvenMatConjImage (LargeEvenProjMk H) Set.univ →
      f ∈ LargeEvenMatFieldImage (LargeEvenProjMk H) → f ^ 3 = 1 → (u * f) ^ 3 = 1 → f ≠ 1 →
        ∀ J : Subgroup (LargeEvenProj H), GLAPComponent 3 (fixSubgroup (u * f)) J →
          ∃ (a m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ m ∧
            Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL a E)))
    (J : Subgroup (LargeEvenProj H)) (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hlab : HasLabel ↥J (fun l : GLALabel => l = ⟨.twA, 4, 2⟩)) : False := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_natCard_pow hm
  subst hH
  obtain ⟨u, f, hβuf, hu, hf, hf3⟩ := hdec
  subst hβuf
  by_cases hf1 : f = 1
  ·
    subst hf1
    simp only [mul_one] at hJ hβ
    obtain ⟨A, -, hA⟩ := hu
    obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨φ⟩⟩ :=
      pComponent_psl_fixed hSL hP1 h2 hd A Nat.prime_three (by norm_num) u hA hβ J hJ
    have hEcard : Nat.card E = 2 ^ (m * Module.finrank K E) := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hm, ← pow_mul]
    have hcanon := hP2 J ⟨.twA, 4, 2⟩ a _ E ha hEcard hlab ⟨φ⟩
    simp [canonLabel] at hcanon
  ·
    obtain ⟨a, m', E, hEf, hEfin, ha, hEcard, ⟨φ⟩⟩ := hfld u f hu hf hf3 hβ hf1 J hJ
    have hcanon := hP2 J ⟨.twA, 4, 2⟩ a m' E ha hEcard hlab ⟨φ⟩
    simp [canonLabel] at hcanon

theorem U64LinearPiece_of_pieces (hSL : SLComponentsTrivial) (hP1 : LinPCompIsComp) (hP2 : LinLabelDict)
    (hDec : LinAutDecomp3) (hFld : FieldLinComp3) : U64LinearPiece := by
  intro d n K hK hKf hcard _ h5 _ β hβ J hJ hlab
  exact u64_no_three_component hcard (LargeEvenSLGroup (Fin d) K)
    (largeEvenSLGroup_eq_statedSL (K := K) d) hSL hP1 hP2 (by omega) β hβ
    (hDec d K (two_eq_zero_of_natCard_pow hcard) (by omega) β hβ)
    (fun u f hu hf hf3 huf hne J' hJ' =>
      hFld d K (two_eq_zero_of_natCard_pow hcard) (by omega) u f hu hf hf3 huf hne J' hJ')
    J hJ hlab

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
