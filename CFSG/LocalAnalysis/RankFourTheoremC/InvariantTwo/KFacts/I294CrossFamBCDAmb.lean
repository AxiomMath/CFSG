module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDFam

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

@[expose] def AmbSmallAt (N Q p : ℕ) : Prop :=
  ∃ e : ℕ, 0 < e ∧ (∀ j : ℕ, p ∣ Q ^ j - 1 ↔ e ∣ j) ∧ N / e < p

section Ambient

theorem isMulCommutative_of_isPGroup_GL_index {K : Type} [Field K] [Finite K] {ι : Type}
    [Fintype ι] [DecidableEq ι] {p : ℕ} [hp : Fact p.Prime] (hp2 : Odd p)
    (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : 0 < e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    (hne : Fintype.card ι / e < p) {P : Subgroup (GL ι K)} (hP : IsPGroup p P) :
    IsMulCommutative P := by
  let ψ : GL ι K ≃* (Module.End K (ι → K))ˣ := Matrix.GeneralLinearGroup.toLin
  have h1 : IsPGroup p (P.map ψ.toMonoidHom) := hP.map ψ.toMonoidHom
  have hfr : Module.finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  exact isMulCommutative_of_map_injective ψ.toMonoidHom ψ.injective
    (isMulCommutative_of_isPGroup_GL (V := ι → K) hp2 hpK he hpe (by rw [hfr]; exact hne) h1)

theorem crossAtOn_of_ambient {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hchar : d.1.characteristic = q.p) {N : ℕ}
    (hmodel : ∀ (L : Type) [Group L], Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
        (H : Subgroup (GL ι K)), Fintype.card ι ≤ N ∧ Nat.card K = q.p ^ q.exponent ∧
          Nonempty (L ≃* StatedProj H)) :
    CrossAtOn d (AmbSmallAt N (q.p ^ q.exponent)) := by
  have core : ∀ (L : Type) [Group L] [Finite L] (p : ℕ), p.Prime → 5 ≤ p →
      AmbSmallAt N (q.p ^ q.exponent) p → d.1.characteristic ≠ p →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ P : Sylow p L,
        IsMulCommutative (P : Subgroup L) := by
    intro L _ _ p hp hp5 hS hdp hiso P
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨K, _, _, ι, _, _, H, hN, hK, ⟨e'⟩⟩ := hmodel L hiso
    have hdp' : q.p ≠ p := by rwa [hchar] at hdp
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hK]
      intro h
      exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
    obtain ⟨e, he, hpe, hne⟩ := hS
    rw [← hK] at hpe
    have hp2 : Odd p := hp.odd_of_ne_two (by omega)
    have hne' : Fintype.card ι / e < p := lt_of_le_of_lt (Nat.div_le_div_right hN) hne
    have hGL : ∀ P : Subgroup (GL ι K), IsPGroup p P → IsMulCommutative P := fun P hP =>
      isMulCommutative_of_isPGroup_GL_index hp2 hpK he hpe hne' hP
    exact isMulCommutative_sylow_of_mulEquiv e'
      (fun R => isMulCommutative_sylow_quotient _
        (fun P hP => isMulCommutative_of_map_injective H.subtype H.subtype_injective
          (hGL _ (hP.map _))) R) P
  refine ⟨fun p hp hp5 hS hdp L _ _ hs hiso hn h2 P => core L p hp hp5 hS hdp hiso P,
    fun p hp hp5 hS hdp L _ _ hs hiso hn h3 y hy => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact three_le_pRank_centralizer_of_sylow_abelian (core L p hp hp5 hS hdp hiso) h3
    (hy ▸ pow_orderOf_eq_one y)

end Ambient

section Families

theorem crossAtOn_C_amb {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) :
    CrossAtOn ⟨.C r q, hv⟩ (AmbSmallAt (2 * r) (q.p ^ q.exponent)) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine crossAtOn_of_ambient (TauCeti.LieTypeIndex.characteristic_C r q) fun L _ ⟨e⟩ => ?_
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := statedClassicalModel_of_lieModel_of_ne_zero (by omega)
    (CFSG.Models.lieModel_C r q hv e)
  exact ⟨K, inferInstance, inferInstance, Fin r ⊕ Fin r, inferInstance, inferInstance, _,
    by simp; omega, hK, ⟨e'⟩⟩

theorem crossAtOn_B_sp_amb {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hb : r = 2 ∨ q.p = 2) :
    CrossAtOn ⟨.B r q, hv⟩ (AmbSmallAt (2 * r) (q.p ^ q.exponent)) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine crossAtOn_of_ambient (TauCeti.LieTypeIndex.characteristic_B r q) fun L _ ⟨e⟩ => ?_
  have hm : CFSG.Models.LieModel L .PSp r q.p q.exponent := by
    refine (CFSG.Models.lieModel_B r q hv e).resolve_right fun h => ?_
    obtain ⟨-, -, h3, h2⟩ := h.1
    rcases hb with hb | hb
    · omega
    · exact h2 hb
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := statedClassicalModel_of_lieModel_of_ne_zero (by omega) hm
  exact ⟨K, inferInstance, inferInstance, Fin r ⊕ Fin r, inferInstance, inferInstance, _,
    by simp; omega, hK, ⟨e'⟩⟩

theorem crossAtOn_B_amb {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) :
    CrossAtOn ⟨.B r q, hv⟩ (AmbSmallAt (2 * r + 1) (q.p ^ q.exponent)) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine crossAtOn_of_ambient (TauCeti.LieTypeIndex.characteristic_B r q) fun L _ ⟨e⟩ => ?_
  rcases CFSG.Models.lieModel_B r q hv e with h | h
  · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := statedClassicalModel_of_lieModel_of_ne_zero (by omega) h
    exact ⟨K, inferInstance, inferInstance, Fin r ⊕ Fin r, inferInstance, inferInstance, _,
      by simp; omega, hK, ⟨e'⟩⟩
  · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := statedClassicalModel_of_lieModel_of_ne_zero (by omega) h
    exact ⟨K, inferInstance, inferInstance, Fin r ⊕ Fin r ⊕ Unit, inferInstance, inferInstance, _,
      by simp; omega, hK, ⟨e'⟩⟩

theorem crossAtOn_D_amb {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) :
    CrossAtOn ⟨.D r q, hv⟩ (AmbSmallAt (2 * r) (q.p ^ q.exponent)) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine crossAtOn_of_ambient (TauCeti.LieTypeIndex.characteristic_D r q) fun L _ ⟨e⟩ => ?_
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := statedClassicalModel_of_lieModel_of_ne_zero (by omega)
    (CFSG.Models.lieModel_D r q hv e)
  exact ⟨K, inferInstance, inferInstance, Fin r ⊕ Fin r, inferInstance, inferInstance, _,
    by simp; omega, hK, ⟨e'⟩⟩

theorem crossAtOn_twistedD_amb {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) :
    CrossAtOn ⟨.twistedD r q, hv⟩ (AmbSmallAt (2 * r) (q.p ^ q.exponent)) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine crossAtOn_of_ambient (TauCeti.LieTypeIndex.characteristic_twistedD r q)
    fun L _ ⟨e⟩ => ?_
  obtain ⟨-, K, _, _, hK, b, c, -, ⟨e'⟩⟩ := statedClassicalModel_of_lieModel_of_ne_zero
    (by omega) (CFSG.Models.lieModel_twistedD r q hv e)
  exact ⟨K, inferInstance, inferInstance, Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2, inferInstance,
    inferInstance, _, by simp; omega, hK, ⟨e'⟩⟩

end Families

end CFSG.LocalAnalysis.RankFourTheoremC
