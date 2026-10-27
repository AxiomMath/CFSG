module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeP
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOddTwo

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

section Support

@[expose] def D4ToralClass (p f : ℕ) (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Prop :=
  s = 1 ∨
    ((p ^ f) % 3 = 1 ∧ ∃ d : Kˣ, Units.map σ.toRingHom.toMonoidHom d = d ∧ d ^ 3 = 1 ∧ d ≠ 1 ∧
      (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) ∨
    ((p ^ f) % 3 = 2 ∧ D4MinusToral p f hp K σ s)

theorem conj_conj_eq {Y : Type*} [Group Y] (y₀ y : Y) (φ ψ χ : MulAut Y)
    (h1 : MulAut.conj y * φ * (MulAut.conj y)⁻¹ = ψ)
    (h2 : MulAut.conj y₀ * ψ * (MulAut.conj y₀)⁻¹ = χ) :
    MulAut.conj (y₀ * y) * φ * (MulAut.conj (y₀ * y))⁻¹ = χ := by
  rw [← h2, ← h1, map_mul]
  group

theorem d4_plusToral_fixed {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (d : Kˣ)
    (hd : Units.map σ.toRingHom.toMonoidHom d = d) (hd3 : d ^ 3 = 1)
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : Fin TwistTag.D4.tag.rank → Kˣ, a = ![1, 1, d, 1] := ⟨_, rfl⟩
  have hs' : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag a := by
    rw [ha]
    exact hs
  have hmap : ∀ i : Fin 4, Units.map σ.toRingHom.toMonoidHom ((![1, 1, d, 1] : Fin 4 → Kˣ) i) =
      (![1, 1, d, 1] : Fin 4 → Kˣ) i := by
    intro i
    fin_cases i <;> first | exact hd | simp
  have hcube : ∀ i : Fin 4, ((![1, 1, d, 1] : Fin 4 → Kˣ) i) ^ 3 = 1 := by
    intro i
    fin_cases i <;> simp [hd3]
  constructor
  · apply Subtype.ext
    rw [coe_fieldActor, hs', units_map_entrywiseHom_rootDiagUnit]
    refine congrArg _ (funext fun i => ?_)
    rw [ha]
    exact hmap i
  · apply Subtype.ext
    show (s : ModGL TwistTag.D4.tag K) ^ 3 = 1
    rw [hs', rootDiagUnit_pow, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
    refine congrArg _ (funext fun i => ?_)
    rw [ha]
    exact hcube i

theorem d4MinusToral_fixed {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : D4MinusToral p f hp K σ s) :
    fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hL, hKL, -, hCh, g₀, b, ⟨-, hP, -⟩, hb3, -, hsb⟩ := hs
  obtain ⟨a, ha⟩ : ∃ a : Fin TwistTag.D4.tag.rank → Lˣ, a = ![1, 1, b, 1] := ⟨_, rfl⟩
  have hsb' : CFSG.RankThree.PartOne.KGD.triEmb K σ L s =
      g₀ * rootDiagUnit TwistTag.D4.tag a * g₀⁻¹ := by
    rw [ha]
    exact hsb
  have hP3 : diagramMap TwistTag.D4 L ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  have hD : (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag a *
      diagramMap TwistTag.D4 L = rootDiagUnit TwistTag.D4.tag a := by
    have h := diagramMap_pow_conj_rootDiagUnit (L := L) a 2
    have hvec : (fun i => a (((TwistTag.D4.perm.symm) ^ 2) i)) = a := by
      funext i
      rw [ha]
      fin_cases i <;> rfl
    have hP2 : diagramMap TwistTag.D4 L ^ 2 = (diagramMap TwistTag.D4 L)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hP3]
    rw [hvec, hP2, inv_inv] at h
    exact h
  have hPg : (diagramMap TwistTag.D4 L)⁻¹ * g₀ = g₀ * (diagramMap TwistTag.D4 L)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hP, mul_inv_cancel_right]
  have hgP : g₀⁻¹ * diagramMap TwistTag.D4 L = diagramMap TwistTag.D4 L * g₀⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hP, mul_inv_cancel_right]
  have hcomm : (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L p f).comp (algebraMap K L) :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def]
      change algebraMap K L (σ c) = _
      rw [hσ, map_pow]
  have hfix := triEmb_fieldActor (iterateFrobenius L p f) hcomm s
  have hinj := CFSG.RankThree.PartOne.KGD.triEmb_injective (K := K) (σ := σ) (L := L)
  refine ⟨hinj ?_, hinj ?_⟩
  · rw [hfix, hsb']
    calc (diagramMap TwistTag.D4 L)⁻¹ * (g₀ * rootDiagUnit TwistTag.D4.tag a * g₀⁻¹) *
          diagramMap TwistTag.D4 L =
        ((diagramMap TwistTag.D4 L)⁻¹ * g₀) * rootDiagUnit TwistTag.D4.tag a *
          (g₀⁻¹ * diagramMap TwistTag.D4 L) := by group
      _ = g₀ * ((diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag a *
          diagramMap TwistTag.D4 L) * g₀⁻¹ := by rw [hPg, hgP]; group
      _ = g₀ * rootDiagUnit TwistTag.D4.tag a * g₀⁻¹ := by rw [hD]
  · have hD3 : rootDiagUnit TwistTag.D4.tag a ^ 3 = 1 := by
      rw [rootDiagUnit_pow, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)]
      congr 1
      funext i
      rw [ha]
      fin_cases i
      · exact one_pow 3
      · exact one_pow 3
      · exact hb3
      · exact one_pow 3
    rw [map_pow, hsb', map_one, conj_pow, hD3, mul_one, mul_inv_cancel]


end Support

section Classification


theorem d4_cocycle_toralClass {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
    ∃ y s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y)⁻¹ = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ ∧
        fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 ∧ D4ToralClass p f hp K σ s := by
  classical
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hq3 : ¬ 3 ∣ p ^ f := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h)) (by omega)
  rcases (show (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 by omega) with hq | hq
  · obtain ⟨y, n, hn, hyn⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
    have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
      rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
      exact mul_inv_cancel _
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
    by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
    · obtain ⟨y', s, hfix, hs3, hconj, d, hd, hd3, hsd⟩ :=
        d4_toral_conj hp hp2 hf K hK σ hσ n hnT hN
      refine ⟨y' * y, s, conj_conj_eq y' y _ _ _ hyn hconj, hfix, hs3, ?_⟩
      by_cases hd1 : d = 1
      · left
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      · exact Or.inr (Or.inl ⟨hq, d, hd, hd3, hd1, hsd⟩)
    · obtain ⟨y₀, s, d, hconj, hd, hd3, hd1, hsd⟩ := ellQ1_conj_toral
        CFSG.HardMathSupport.Lang.E6Descent.rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hnT hN
      obtain ⟨hfix, hs3⟩ := d4_plusToral_fixed σ d hd hd3 s hsd
      exact ⟨y₀ * y, s, conj_conj_eq y₀ y _ _ _ hyn hconj, hfix, hs3,
        Or.inr (Or.inl ⟨hq, d, hd, hd3, hd1, hsd⟩)⟩
  · rcases d4MinusNF p f hp hp2 hp3 hf hq K hK σ hσ g hg with ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ |
        ⟨y, n, hn, hyn⟩
    · refine ⟨y, 1, by rw [hy, map_one, one_mul], ?_, one_pow 3, Or.inl rfl⟩
      exact map_one _
    · obtain ⟨hfix, hs3⟩ := d4MinusToral_fixed hp hσ hs
      exact ⟨y, s, hys, hfix, hs3, Or.inr (Or.inr ⟨hq, hs⟩)⟩
    · have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
        rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
        exact mul_inv_cancel _
      have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
      obtain ⟨y₀, s, hsT, hconj⟩ := minusEll_conj_toral
        CFSG.HardMathSupport.Lang.E6Descent.rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hN
      obtain ⟨hfix, hs3⟩ := d4MinusToral_fixed hp hσ hsT
      exact ⟨y₀ * y, s, conj_conj_eq y₀ y _ _ _ hyn hconj, hfix, hs3, Or.inr (Or.inr ⟨hq, hsT⟩)⟩

end Classification

theorem d4CocycleNF_holds :
    D4CocycleNF := by
  intro p f hp hp2 hp3 hf K _ _ hK σ hσ g hg
  obtain ⟨y, s, hconj, hfix, hs3, -⟩ := d4_cocycle_toralClass hp hp2 hp3 hf hK σ hσ g hg
  exact ⟨y, s, hfix, hs3, hconj⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
