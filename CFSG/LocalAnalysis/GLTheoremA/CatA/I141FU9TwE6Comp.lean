module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9TwE6Disp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9TwE6Abs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HTE6Model
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterIn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section Centre


theorem twE6_centre_of_rat (h : E6TwoRatU38Centre) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2)
    (α : MulAut ↥(twistedE6RootGroup K σ)) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (I : Subgroup ↥(twistedE6RootGroup K σ)) (hI : IsComponentOf I (fixSubgroup α))
    (hcard : Nat.card (↥I ⧸ Subgroup.center ↥I) = 5515776) : Subgroup.center ↥I = ⊥ := by
  classical
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
  let eJ : ↥I ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (I.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hcardR : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776 :=
    (Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥I)
      (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) eJ
      (Subgroup.map_center_eq eJ)).toEquiv).symm.trans hcard
  have hZR := h (AlgebraicClosure K) p₀ S hq2 a hT hap h1 i hqi hcardR
  have hmap := Subgroup.map_center_eq eJ
  rw [hZR] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ eJ.injective).1 hmap

end Centre

section Holds


theorem twE6U38Centre_of_rat (h : E6TwoRatU38Centre) : TwE6U38Centre := by
  intro S _ hS α hα3 hα1 I hI hcard
  obtain ⟨K, hfield, hfin, σ, hK, hσ, ⟨e⟩⟩ :=
    CatB.I2610.exists_twistedE6RootGroup_of_catalogIs_isTE6two hS
  letI : Field K := hfield
  letI : Finite K := hfin
  have hα3' : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hα1' : MulAut.congr e α ≠ 1 := fun h' =>
    hα1 ((MulAut.congr e).injective (by rw [map_one]; exact h'))
  have hI' : IsComponentOf (I.map e.toMonoidHom) (fixSubgroup (MulAut.congr e α)) := by
    rw [fixSubgroup_congr e α]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hI
  let eI : ↥I ≃* ↥(I.map e.toMonoidHom) := I.equivMapOfInjective e.toMonoidHom e.injective
  have hcard' : Nat.card (↥(I.map e.toMonoidHom) ⧸ Subgroup.center ↥(I.map e.toMonoidHom)) =
      5515776 :=
    (Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥I)
      (Subgroup.center ↥(I.map e.toMonoidHom)) eI (Subgroup.map_center_eq eI)).toEquiv).symm.trans
      hcard
  have hZ' := twE6_centre_of_rat h σ hK hσ _ hα3' hα1' _ hI' hcard'
  have hmap := Subgroup.map_center_eq eI
  rw [hZ'] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ eI.injective).1 hmap

end Holds

section Final


theorem twE6U38Centre_holds : TwE6U38Centre :=
  twE6U38Centre_of_rat e6TwoRatU38Centre_holds

end Final

end CFSG.LocalAnalysis.GLTheoremA.I141F
