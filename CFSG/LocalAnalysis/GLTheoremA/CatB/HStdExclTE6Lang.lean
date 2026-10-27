module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclTE6RatDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterIn
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem smallOrd_of_mulEquiv {G G' : Type} [Group G] [Group G'] {I : Subgroup G}
    {R : Subgroup G'} (e : ↥I ≃* ↥R) (h : SmallOrd I) : SmallOrd R := by
  unfold SmallOrd at h ⊢
  have hcard : Nat.card (↥I ⧸ Subgroup.center ↥I) =
      Nat.card (↥R ⧸ Subgroup.center ↥R) :=
    Nat.card_congr
      (QuotientGroup.congr (Subgroup.center ↥I) (Subgroup.center ↥R) e
        (Subgroup.map_center_eq e)).toEquiv
  rw [← hcard]
  exact h

theorem exclTE6_of_rat
    (h : E6TwoRatNotSmall) : ExclTE6 := by
  classical
  intro K _ _ σ hK hσ α hα3 hα1 I hI hIsmall
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  have hmem : α ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact Bal209TwoOuterInAux.mem_inn_sup_diag_of_pow_three hK σ hσ hα3
  obtain ⟨g, rfl⟩ := hmem
  have hg3 : g ^ 3 = 1 :=
    twistedE6InndiagConj_injective Nat.prime_two le_rfl hK2 σ hσ2
      (by rw [map_pow, hα3, map_one])
  have hg1 : g ≠ 1 := fun h' => hα1 (by rw [h', map_one])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    exists_setup_prime Nat.prime_two le_rfl Nat.prime_three (by decide) (by decide)
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp)
      Nat.prime_three (by decide)
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two le_rfl hK2 σ hσ2 Nat.prime_three
      (by decide) hp₀ hp₀ℓ hq₀ hmon (twistedE6InndiagConj K σ g)
      (g : ModGL TwistTag.E6.tag K) g.2 (twistedE6InndiagConj_apply g)
      (by rw [← Subgroup.coe_pow, hg3]; rfl) (fun h' => hg1 (Subtype.ext h'))
  have hq2 : S.D.q = 2 := by rw [hSq]; norm_num
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne Nat.prime_two Nat.prime_three hK2 (by decide)
  have hTame :=
    langSetup_hTame_of_prime S Nat.prime_three hpL (fun h' => absurd h' (by decide)) hT hap h1
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨i, hqi, hJR⟩ :=
    components_of_langSetup S Nat.prime_three ι hinj hrange (twistedE6InndiagConj K σ g)
      hconj hT hap h1 hTame hI
  have hnot := h (AlgebraicClosure K) p₀ S hq2 a hT hap h1 i hqi
  let eJ : ↥I ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (I.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  exact hnot (smallOrd_of_mulEquiv eJ hIsmall)

end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
