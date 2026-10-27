module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUni

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniSig

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniTw
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU mem_heldGU)

theorem conj_transport_matrix {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (σ : K ≃+* K) (R : Matrix (Fin d) ι K) (T : Matrix ι (Fin d) K) (A A' : Matrix (Fin d) (Fin d) K)
    (g : Matrix ι ι K) :
    T * (A * (R * g * T).map σ * A') * R = (T * A * R.map σ) * g.map σ * (T.map σ * A' * R) := by
  simp only [Matrix.map_mul, Matrix.mul_assoc]

theorem uniSigmaPowOne_holds : UniSigmaPowOne := by
  unfold UniSigmaPowOne
  intro K _ _ n d τ hτ hτq hcard hd _hdQ A hA σ p _hp _hp2 u hβ hpow
  obtain ⟨r, ε, rfl, hε, hr⟩ : ∃ r ε : ℕ, d = 2 * r + ε ∧ ε ≤ 1 ∧ 1 ≤ r :=
    ⟨d / 2, d % 2, by omega, by omega, by omega⟩
  have hn : 1 ≤ 2 * r + ε := by omega
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      have h1 : Nat.card K = 1 := by rw [hcard, h0]; simp
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have hK : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn1, by rw [hcard, ← pow_mul, mul_comm]⟩
  have hτh : ∀ c : K, hK.bar c = τ c := fun c => by rw [UnitaryFieldData.bar_apply, hτq]
  have hτbar : (⇑hK.bar : K → K) = ⇑τ := funext hτh
  have hAmem : A ∈ primeFormUnitary hK (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) := by
    rw [mem_primeFormUnitary, Matrix.mul_one, hτbar]
    exact mem_heldGU.1 hA
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) hK
  have hW : IsGramHypTransport hK (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) R := by
    unfold IsGramHypTransport
    rw [Matrix.mul_one]
    exact hR
  have hCφ : ∀ φ : K ≃+* K, (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).map φ = 1 :=
    fun φ => Matrix.map_one _ (map_zero φ) (map_one φ)
  have hYmem : (⟨gramToHypSemiGL hW A σ, σ⟩ : SemiGL (HypIndex r ε) K) ∈
      semilinearSimilitudes hK r ε := by
    rw [mem_semilinearSimilitudes]
    refine ⟨1, one_ne_zero, map_one _, ?_⟩
    rw [one_smul]
    exact mem_hypUnitary.1 (gramToHypSemiGL_mem hCφ hW hAmem σ)
  set xS : semilinearSimilitudes hK r ε := ⟨⟨gramToHypSemiGL hW A σ, σ⟩, hYmem⟩ with hxS
  set e := hypPSUEquivStatedProj hK hR hn with he
  set v : MulAut (hypPSU hK r ε) := MulEquiv.trans e (MulEquiv.trans u e.symm) with hv_def
  have hvm : ∀ m, e (v m) = u (e m) := fun m => e.apply_symm_apply (u (e m))
  have hvpow : ∀ (k : ℕ) (m : hypPSU hK r ε), (v ^ k) m = e.symm ((u ^ k) (e m)) := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [pow_succ, MulAut.mul_apply, ih, hvm, pow_succ, MulAut.mul_apply]
  have hvp : v ^ p = 1 := by
    refine MulEquiv.ext fun m => ?_
    rw [hvpow p m, hpow]
    simp
  have hv : v = semilinearAutHom hK hr hε xS := by
    refine MulEquiv.ext fun m => ?_
    obtain ⟨g, rfl⟩ := hypProj_surjective hK r ε m
    obtain ⟨g0, hg0⟩ : ∃ g0 : ↥(StatedSU (2 * r + ε) (2 ^ n) K), g0 = hypTransport hK hR g := ⟨_, rfl⟩
    have hg0val : ((g0 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
        R * ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          transportInv hK R := by
      rw [hg0]
      exact coe_hypTransport hR g
    have hE1 : e (hypProj hK r ε g) = LargeEvenProjMk (StatedSU (2 * r + ε) (2 ^ n) K) g0 := by
      rw [hg0]
      exact hypPSUEquivStatedProj_hypProj hR hn g
    obtain ⟨g', hg'⟩ : ∃ g' : ↥(StatedSU (2 * r + ε) (2 ^ n) K),
        g' = ⟨A * glMap σ (g0 : GL (Fin (2 * r + ε)) K) * A⁻¹,
          conj_mem_statedSU hτ hτq hA (glMap_mem_statedSU hτ hτq σ g0.2)⟩ := ⟨_, rfl⟩
    have hu : u (LargeEvenProjMk (StatedSU (2 * r + ε) (2 ^ n) K) g0) =
        LargeEvenProjMk (StatedSU (2 * r + ε) (2 ^ n) K) g' :=
      hβ g0 g' (by rw [hg'])
    have hg'val : ((g' : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
        (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *
          ((g0 : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).map σ *
            ((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) := by
      rw [hg', Units.val_mul, Units.val_mul, coe_glMap]
    obtain ⟨gg, hgg⟩ : ∃ gg : ↥(hypSU hK r ε), gg = (hypTransport hK hR).symm g' := ⟨_, rfl⟩
    have hE2 : e (hypProj hK r ε gg) = LargeEvenProjMk (StatedSU (2 * r + ε) (2 ^ n) K) g' := by
      rw [hgg]
      refine (hypPSUEquivStatedProj_hypProj hR hn _).trans ?_
      rw [MulEquiv.apply_symm_apply]
      rfl
    have hLHS : v (hypProj hK r ε g) = hypProj hK r ε gg := by
      change e.symm (u (e (hypProj hK r ε g))) = hypProj hK r ε gg
      rw [hE1, hu, ← hE2, MulEquiv.symm_apply_apply]
    have hYinv : (((gramToHypSemiGL hW A σ)⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        (gramHypInv hK (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) R).map σ *
          ((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * R := rfl
    have hT1 : gramHypInv hK (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) R =
        transportInv hK R := by
      unfold gramHypInv transportInv
      rw [Matrix.mul_one]
    have hmat : ((gg : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        (((gramToHypSemiGL hW A σ : GL (HypIndex r ε) K) * glAut σ g *
          (gramToHypSemiGL hW A σ)⁻¹ : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) := by
      rw [hgg, coe_hypTransport_symm hR g', hg'val, hg0val, Units.val_mul, Units.val_mul, coe_glAut,
        coe_gramToHypSemiGL, hYinv, hT1]
      exact conj_transport_matrix σ R (transportInv hK R) (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
        ((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
    rw [hLHS, semilinearAutHom_apply hK hr hε xS g]
    congr 1
    exact Subtype.ext (Units.ext hmat)
  have hΦp : semilinearAutHom hK hr hε (xS ^ p) = 1 := by
    rw [map_pow, ← hv, hvp]
  have hker := ((semilinearAutHom_eq_one_iff hK hr hε hd (xS ^ p)).1 hΦp).1
  have hright : (((xS ^ p : ↥(semilinearSimilitudes hK r ε)) : SemiGL (HypIndex r ε) K)).right = σ ^ p := by
    rw [Subgroup.coe_pow]
    exact map_pow SemidirectProduct.rightHom (xS : SemiGL (HypIndex r ε) K) p
  rw [← hright]
  exact hker

section Certificates


theorem fldUni_holds : CFSG.LocalAnalysis.GLTheoremA.Y10GField.FldUni :=
  CFSG.LocalAnalysis.GLTheoremA.Y10GFldUni.fldUni_of_sigmaPow uniSigmaPowOne_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniSig

end
