module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123b
public import CFSG.LieType.SeitzGeneration.CubeCoverField
public import CFSG.LieType.SeitzGeneration.CubeCoverPar
public import CFSG.LieType.SeitzGeneration.QuasiHigh6Rest

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs123b
open CFSG.LieType.Chevalley CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration.QuasiHigh

theorem coverImage_le_range_conj_iff {K C : Type*} [Group K] [Group C]
    (hperf : commutator K = ⊤) (e : K ⧸ Subgroup.center K ≃* C) {E : Subgroup (MulAut K)} :
    coverImage e E ≤ (MulAut.conj : C →* MulAut C).range ↔
      E ≤ (MulAut.conj : K →* MulAut K).range := by
  refine ⟨fun h x hx => ?_, coverImage_le_range_conj e⟩
  have hx' : (MulAut.congr e) (quotientCenterAut' K x) ∈
      (MulAut.conj : C →* MulAut C).range :=
    h (Subgroup.mem_map_of_mem _ hx)
  rw [← map_range_conj_congr e] at hx'
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
  have hq : quotientCenterAut' K x = y := (MulAut.congr e).injective hyx.symm
  exact mem_innerAut_of_quotientCenterAut' hperf (hq ▸ hy)

theorem normalizesRSub_innerImage {K C : Type*} [Group K] [Group C]
    {d : TauCeti.ValidLieTypeIndex} (e : K ⧸ Subgroup.center K ≃* Cat d) (φ : Cat d ≃* C)
    {E : Subgroup (MulAut K)} {R : Subgroup C} (hR : R ≠ ⊥)
    (hRp : IsPGroup d.1.characteristic R)
    (hRE : ∀ ε ∈ coverImage (e.trans φ) E, R.map ε.toMonoidHom = R) :
    NormalizesRSub d ((innerImage E).map e.toMonoidHom) := by
  refine ⟨R.map φ.symm.toMonoidHom, ?_, IsPGroup.map hRp _, ?_⟩
  · intro hbot
    exact hR ((Subgroup.map_eq_bot_iff_of_injective R φ.symm.injective).1 hbot)
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [innerImage] at hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
    have hg' : MulAut.conj g ∈ E := Subgroup.mem_comap.1 hg
    have himg : MulAut.conj (φ (e.toMonoidHom (QuotientGroup.mk' (Subgroup.center K) g))) ∈
        coverImage (e.trans φ) E := by
      have h := Subgroup.mem_map_of_mem
        ((MulAut.congr (e.trans φ)).toMonoidHom.comp (quotientCenterAut' K)) hg'
      simp only [MonoidHom.comp_apply, QuasiHigh.quotientCenterAut'_conj,
        mulAut_congr_conj] at h
      simpa [coverImage, MulEquiv.trans_apply] using h
    have h2 : R.map
        (MulAut.conj (φ (e.toMonoidHom
          (QuotientGroup.mk' (Subgroup.center K) g)))).toMonoidHom = R :=
      hRE _ himg
    have hcomp : (MulAut.conj (e.toMonoidHom
          (QuotientGroup.mk' (Subgroup.center K) g))).toMonoidHom.comp φ.symm.toMonoidHom =
        φ.symm.toMonoidHom.comp
          (MulAut.conj (φ (e.toMonoidHom
            (QuotientGroup.mk' (Subgroup.center K) g)))).toMonoidHom := by
      ext r
      simp [MulAut.conj_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, h2]

end CFSG.LieType.SeitzGeneration

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.QuasiHigh2
  CFSG.LieType.SeitzGeneration.QuasiHigh4 CFSG.LieType.SeitzGeneration.CubeCoverPar
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc


@[expose] def CoverE6DiagNotAll24 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    ∀ (k : Type) [Field k] [Finite k], ringChar k ≠ 3 → 3 ∣ Nat.card k - 1 → Nat.card k ≠ 4 →
    ∀ (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k) (E : Subgroup (MulAut K)),
      IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → coverImage θ E ≤ e6Inndiag k →
      ¬ coverImage θ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k) →
      ¬ E6NormalizesR k (coverImage θ E) → ¬ E6InnerAll24 k (coverImage θ E) →
      seitzHyperGamma 3 E = ⊤

@[expose] def CoverTwE6Cubes : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K],
    CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    (∃ q, d.1 = TauCeti.LieTypeIndex.twistedE6 q) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 3 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E → ¬ ExcIsotropic d E → ¬ LinearDiag p E → ¬ InvP'Pair p E →
      ¬ UDiagGU p E → ¬ UFieldSplit p E → ¬ UFieldStd p E → seitzHyperGamma p E = ⊤

theorem excIsotropic_e6 {K : Type} [Group K] (hperf : commutator K = ⊤) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.E6 q).Valid}
    (e : K ⧸ Subgroup.center K ≃* Cat ⟨.E6 q, hv⟩) {k : Type} [Field k] [Finite k]
    (hk : ringChar k = q.p) (φ : Cat ⟨.E6 q, hv⟩ ≃* adjointGroup Tag.E6 k)
    {E : Subgroup (MulAut K)}
    (hin : coverImage (e.trans φ) E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k))
    (hn : E6NormalizesR k (coverImage (e.trans φ) E)) : ExcIsotropic ⟨.E6 q, hv⟩ E := by
  rw [E6NormalizesR] at hn
  obtain ⟨R, hR, hRp, hRE⟩ := hn
  have hchar : (⟨.E6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = ringChar k := by
    rw [TauCeti.LieTypeIndex.characteristic_E6, ← hk]
  have hRp' : IsPGroup (⟨.E6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic R := by
    rw [hchar]
    exact hRp
  exact ⟨isChevalleyExcIndex_E6 q,
    (coverImage_le_range_conj_iff hperf (e.trans φ)).1 hin,
    ⟨e, normalizesRSub_innerImage e φ hR hRp' hRE⟩⟩

theorem seitzHyperGamma_eq_top_e6_cube (hD : CoverE6DiagNotAll24)
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) {k : Type} [Field k] [Finite k]
    (hk3 : ringChar k ≠ 3) (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hiso : coverImage θ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k) →
      ¬ E6NormalizesR k (coverImage θ E))
    (hpair : ¬ QuasiHigh2.InvP'Pair 3 E) : seitzHyperGamma 3 E = ⊤ := by
  by_cases hd : coverImage θ E ≤ e6Inndiag k
  · by_cases hi : coverImage θ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k)
    · exact seitzHyperGamma_eq_top_e6_inner_cube hperf hk3 h3 h4 θ hE hcard
        ((coverImage_le_range_conj_iff hperf θ).1 hi) (hiso hi)
    · by_cases hn : E6NormalizesR k (coverImage θ E)
      · exact absurd (invP'Pair_of_e6Inndiag hk3 θ hE hd hn) hpair
      · by_cases hA : E6InnerAll24 k (coverImage θ E)
        · exact seitzHyperGamma_eq_top_e6_diag_all24 hperf hk3 h3 h4 θ hE hcard hd hi hA
        · exact hD K hperf k hk3 h3 h4 θ E hE hcard hd hi hn hA
  · exact CubeCoverField.seitzHyperGamma_eq_top_e6_field_cube hperf hk3 h3 θ hE hcard hd

theorem seitzCoverCubeRest5_E6 (hD : CoverE6DiagNotAll24) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K],
      CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    (∃ q, d.1 = TauCeti.LieTypeIndex.E6 q) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 3 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E → ¬ ExcIsotropic d E → ¬ LinearDiag p E → ¬ InvP'Pair p E →
      ¬ UDiagGU p E → ¬ UFieldSplit p E → ¬ UFieldStd p E → seitzHyperGamma p E = ⊤ := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci hE6 E hE hcard hex hCS hX hLD hP hU hS hStd
  obtain ⟨q, hdq⟩ := hE6
  obtain ⟨dd, hv⟩ := d
  have hdd : dd = TauCeti.LieTypeIndex.E6 q := hdq
  subst hdd
  obtain ⟨e⟩ := hd
  obtain ⟨hp3, h3⟩ := hci
  subst hp3
  obtain ⟨k, _, _, hK, _, ⟨φ⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hk : ringChar k = q.p := ringChar.eq k q.p
  have hpd' : 3 ≠ q.p := by
    simpa only [TauCeti.LieTypeIndex.characteristic_E6] using hpd
  have hk3 : ringChar k ≠ 3 := by
    rw [hk]
    exact fun h => hpd' h.symm
  have h3' : 3 ∣ Nat.card k - 1 := by rw [hK]; exact h3
  have hnotsix : ¬ IsSixIndex (.E6 q) := by
    simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex]
  have hXe : ¬ ExcIndex 3 (.E6 q) := by
    rcases hex with h | h
    · exact h
    · exact absurd h.1 hnotsix
  have h4' : Nat.card k ≠ 4 := by
    intro h4k
    have hq4 : q.p ^ q.exponent = 2 ^ 2 := by
      rw [← TauCeti.PrimePower.card_def, ← hK, h4k]
      norm_num
    have hp2 : q.p = 2 := by
      have hdvd : q.p ∣ 2 ^ 2 := hq4 ▸ dvd_pow_self q.p q.exponent_pos.ne'
      exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
        (q.prime_p.dvd_of_dvd_pow hdvd)
    have hexp2 : q.exponent = 2 := by
      apply Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2)
      simpa [hp2] using hq4
    have hgen : Gen2318Index (.E6 q) := by
      show IsTwoPow q 1 ∨ IsTwoPow q 2 ∨ IsTwoPow q 3
      exact Or.inr (Or.inl ⟨hp2, hexp2⟩)
    exact hXe (Or.inr ⟨rfl, Or.inr (Or.inl hgen)⟩)
  have hiso : coverImage (e.trans φ) E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k) →
      ¬ E6NormalizesR k (coverImage (e.trans φ) E) := by
    intro hin hn
    exact hX (excIsotropic_e6 hq.1 e hk φ hin hn)
  exact seitzHyperGamma_eq_top_e6_cube hD hq.1 hk3 h3' h4' (e.trans φ) hE hcard hiso hP

theorem seitzCoverCubeRest5_of (hD : CoverE6DiagNotAll24) (hT : CoverTwE6Cubes) :
    CFSG.LieType.SeitzGeneration.QuasiHigh6.SeitzCoverCubeRest5 := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci h6 E hE hcard hex hCS hX hLD hP hU hS hStd
  rcases h6 with ⟨q, hdq⟩ | ⟨q, hdq⟩
  · exact seitzCoverCubeRest5_E6 hD p hp hp2 K hq d hd hpd hL34 hz hci ⟨q, hdq⟩ E hE
      hcard hex hCS hX hLD hP hU hS hStd
  · exact hT p hp hp2 K hq d hd hpd hL34 hz hci ⟨q, hdq⟩ E hE hcard hex hCS hX hLD hP hU
      hS hStd

end CFSG.LieType.SeitzGeneration.CubeCoverE6

end
