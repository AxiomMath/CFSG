module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRankOne
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddShape
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofNorm

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19
open scoped MatrixGroups

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem triOdd_fieldActor_fix_A {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (u : C0 σ) (δ : X ≃+* X) (hδ : δ ^ 3 = 1)
    (hfix : ∀ a ∈ Asub σ, (MulAut.conj u * fieldActor (t := TwistTag.D4) σ δ) a = a) :
    δ = 1 := by
  classical
  obtain ⟨-, -, ⟨Θ, hΘ, hker⟩, -⟩ := KS11Lie5Proof.triality_normal_form hℓ hf X hX σ hσ
  haveI : Finite (C0 σ) := by
    have : Finite (ModGL TwistTag.D4.tag X) := finite_modGL
    exact Finite.of_injective (fun x : C0 σ => (x : ModGL TwistTag.D4.tag X)) Subtype.val_injective
  haveI : Finite (MulAut (C0 σ)) := inferInstance
  set ζ : MulAut (C0 σ) := MulAut.conj u * fieldActor (t := TwistTag.D4) σ δ with hζ
  have hΘζ : Θ ζ = δ := hΘ ζ u δ rfl
  have hpos : 0 < orderOf ζ := orderOf_pos ζ
  obtain ⟨s, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' 3 (by norm_num)
  have hfixm : ∀ n : ℕ, ∀ a ∈ Asub σ, (ζ ^ n) a = a := by
    intro n
    induction n with
    | zero => intro a _; simp
    | succ n ih =>
      intro a ha
      rw [pow_succ, MulAut.mul_apply, hfix a ha]
      exact ih a ha
  have h3pow : (ζ ^ m) ^ 3 ^ s = 1 := by
    rw [← pow_mul, mul_comm, ← hord]
    exact pow_orderOf_eq_one ζ
  have h3q : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)).symm)
  have hinn := KS11Lie5Proof.d4ShortOut_holds X (ℓ ^ f) σ hX hσ h3q (ζ ^ m) ⟨s, h3pow⟩
    (hfixm m)
  have hker1 : Θ (ζ ^ m) = 1 := by
    have : ζ ^ m ∈ Θ.ker := by rw [hker]; exact hinn
    exact MonoidHom.mem_ker.1 this
  have hδm : δ ^ m = 1 := by rw [← hΘζ, ← map_pow]; exact hker1
  have hg : δ ^ Nat.gcd m 3 = 1 := pow_gcd_eq_one.2 ⟨hδm, hδ⟩
  have hcop : Nat.gcd m 3 = 1 := by
    have : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3
    rw [Nat.gcd_comm]; exact this
  rwa [hcop, pow_one] at hg

theorem triOdd_asub_chart {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) :
    ∃ ι : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ, Function.Injective ι ∧
      (∀ x : C0 σ, x ∈ Asub σ ↔ ∃ M, ι M = x) ∧
      ∀ M, tauAut σ (ι M) = ι (Matrix.SpecialLinearGroup.map σ.toRingHom M) := by
  classical
  have hσ3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hX hσ
  have h3 : ∀ c : X, σ (σ (σ c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card (σ := σ.toRingHom) hX hσ
  set a₁ : Fin TwistTag.D4.foldedTag.rank := KS11Lie4Proof.d4Outer with ha₁
  have hL₁ : ∀ c : X, c ∈ orbitField TwistTag.D4 X σ.toRingHom a₁ := fun c => by
    rw [orbitField_D4_zero_eq_top σ h3]
    exact Subfield.mem_top c
  let f₁ : X →+* orbitField TwistTag.D4 X σ.toRingHom a₁ := (RingHom.id X).codRestrict _ hL₁
  let R := orbitRankOneHom TwistTag.D4 X σ.toRingHom a₁
  have hRC : ∀ N, R N ∈ graphFixedRootGroup TwistTag.D4 X σ.toRingHom := fun N =>
    CFSG.RankThree.Chevalley.orbitRankOneHom_mem_graphFixedRootGroup a₁ N
  have hRinj : Function.Injective R := orbitRankOneHom_injective_D4 hσ3 a₁
  let ι : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ :=
    (R.comp (Matrix.SpecialLinearGroup.map f₁)).codRestrict _ fun M => hRC _
  have hcoe : ∀ M, ((ι M : C0 σ) : ModGL TwistTag.D4.tag X) =
      R (Matrix.SpecialLinearGroup.map f₁ M) := fun M => rfl
  refine ⟨ι, ?_, ?_, ?_⟩
  · intro M N h
    have h1 : R (Matrix.SpecialLinearGroup.map f₁ M) = R (Matrix.SpecialLinearGroup.map f₁ N) := by
      rw [← hcoe, ← hcoe, h]
    exact KS11Lie6Proof.map_SL2_injective f₁ (hRinj h1)
  · intro x
    constructor
    · intro hx
      obtain ⟨N, hN⟩ := hx
      refine ⟨Matrix.SpecialLinearGroup.map (orbitField TwistTag.D4 X σ.toRingHom a₁).subtype N,
        Subtype.ext ?_⟩
      rw [hcoe]
      have : Matrix.SpecialLinearGroup.map f₁
          (Matrix.SpecialLinearGroup.map (orbitField TwistTag.D4 X σ.toRingHom a₁).subtype N) = N := by
        refine Subtype.ext ?_
        ext i j
        simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
        rfl
      rw [this]
      exact hN
    · rintro ⟨M, rfl⟩
      exact ⟨Matrix.SpecialLinearGroup.map f₁ M, hcoe M⟩
  · intro M
    have hι_up : ∀ c : X, ι (uSL c) = fixedOrbitX TwistTag.D4 X σ.toRingHom a₁ (f₁ c) := by
      intro c
      apply Subtype.ext
      rw [hcoe, map_uSL, orbitRankOneHom_uSL]
      rfl
    have hι_lo : ∀ c : X, ι (vSL c) = fixedOrbitY TwistTag.D4 X σ.toRingHom a₁ (f₁ c) := by
      intro c
      apply Subtype.ext
      rw [hcoe, map_vSL, orbitRankOneHom_vSL]
      rfl
    have key : (tauAut σ).toMonoidHom.comp ι =
        ι.comp (Matrix.SpecialLinearGroup.map σ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := X)) ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show tauAut σ (ι (uSL c)) = ι (Matrix.SpecialLinearGroup.map σ.toRingHom (uSL c))
        rw [map_uSL, hι_up, hι_up]
        show fieldActor σ σ (fixedOrbitX TwistTag.D4 X σ.toRingHom a₁ (f₁ c)) = _
        rw [fieldActor_fixedOrbitX]
        rfl
      · show tauAut σ (ι (vSL c)) = ι (Matrix.SpecialLinearGroup.map σ.toRingHom (vSL c))
        rw [map_vSL, hι_lo, hι_lo]
        show fieldActor σ σ (fixedOrbitY TwistTag.D4 X σ.toRingHom a₁ (f₁ c)) = _
        rw [fieldActor_fixedOrbitY]
        rfl
    exact DFunLike.congr_fun key M

end Model

end CFSG.LieType.SeitzGeneration.ExcWideThree
