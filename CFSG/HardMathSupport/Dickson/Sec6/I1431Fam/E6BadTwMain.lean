module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadLift
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwWitness
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Mult
public import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Simplicity
  CFSG.LieType.Steinberg.CentralExt CFSG.RankThree.PerfectCover
  CFSG.HardMathSupport.Dickson.Sec6.I923

section


theorem rkY_false_twE6 {Y : Type} [Group Y] [Finite Y] (hrk : RkY Y) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f)
    (hE : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .twistedE6 p f)
    (hm : LieModel (Y ⧸ Subgroup.center Y) .twistedE6 0 p f) (h3 : 3 ∣ p ^ f + 1) : False := by
  classical
  obtain ⟨K, hKf, hKfin, hKcard, θ, hθq, ⟨e⟩⟩ := hE.2
  have hKq : Nat.card K = (p ^ f) ^ 2 := hKcard
  haveI : Fintype K := Fintype.ofFinite K
  have hθ : ∀ c, θ (θ c) = c := fun c => by
    rw [hθq, hθq, ← pow_mul, ← sq, ← hKq, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hq2le : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKq]
    nlinarith
  set H' := ⁅twistedFixedGroup TwistTag.E6 K θ, twistedFixedGroup TwistTag.E6 K θ⁆ with hH'
  have hZ : Subgroup.center ↥H' = ⊥ :=
    GriessExceptional.twistedE6_center_derived_eq_bot hθ hK4
  let ψ : ↥H' →* Y ⧸ Subgroup.center Y :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥H'))
  have hψinj : Function.Injective ψ := by
    refine e.symm.injective.comp ?_
    rw [injective_iff_map_eq_one]
    intro x hx
    have := (QuotientGroup.eq_one_iff x).1 hx
    rwa [hZ, Subgroup.mem_bot] at this
  have hψsurj : Function.Surjective ψ :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  set iso := twistedIsogeny θ hθ hK4 with hiso
  let θ' : ↥(fixedGroup K θ) →* Y ⧸ Subgroup.center Y := ψ.comp iso
  have hθ'surj : Function.Surjective θ' := hψsurj.comp (twistedIsogeny_surjective θ hθ hK4)
  have hθ'ker : θ'.ker = Subgroup.center ↥(fixedGroup K θ) := by
    have hker : (ψ.comp iso).ker = iso.ker := by
      ext g
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
      constructor
      · intro h
        exact (injective_iff_map_eq_one ψ).1 hψinj _ h
      · intro h
        rw [h, map_one]
    rw [show θ'.ker = (ψ.comp iso).ker from rfl, hker]
    exact TwistedE6Closed.ker_twistedIsogeny_eq_center hθ hK4
  haveI : Group.IsPerfect ↥(fixedGroup K θ) := fixedGroup_isPerfect_of_four_le_card θ hθ hK4
  have hcardker : Nat.card θ'.ker = Nat.gcd 3 (p ^ f + 1) := by
    rw [hθ'ker]
    exact (TwistedE6Closed.card_center_fixedGroup hKq hθq).1
  have hcardM : Nat.card (hopfMultiplier (Y ⧸ Subgroup.center Y)) =
      Nat.gcd 3 (p ^ f + 1) * (if p = 2 ∧ f = 1 then 4 else 1) :=
    card_hopfMultiplier_twistedE6 hm
  have hgcd : Nat.gcd 3 (p ^ f + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hM0 : Nat.card (hopfMultiplier (Y ⧸ Subgroup.center Y)) ≠ 0 := by
    rw [hcardM]
    split_ifs <;> omega
  let π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker = Subgroup.center Y := QuotientGroup.ker_mk' _
  obtain ⟨E, U, hEa, hcard, hU, hU2, hN⟩ :=
    tw_exists_torus_witness θ hθ hK4 hKq hθq (by simpa using h3)
  have hmap : E.map θ' = (E.map iso).map ψ := (Subgroup.map_map _ _ _).symm
  obtain ⟨R, hR, hRmap⟩ : ∃ R : Subgroup Y, IsElemAbelian 3 R ∧ R.map π = E.map θ' := by
    by_cases hq2 : p = 2 ∧ f = 1
    · refine exists_elemAbelian_lift_of_hopf_two_power θ' hθ'surj (hθ'ker ▸ le_rfl) hM0
        ⟨2, ?_⟩ π hπ hπker.le hEa
      rw [hcardM, hcardker, if_pos hq2]
      ring
    · obtain ⟨ρ, hρ⟩ := exists_hom_lift_of_hopf_card θ' hθ'surj (hθ'ker ▸ le_rfl)
        (by rw [hcardM, hcardker, if_neg hq2, mul_one]) hM0 π hπ hπker.le
      refine ⟨E.map ρ, IsElemAbelian.map hEa ρ, ?_⟩
      have hcomp : π.comp ρ = θ' := MonoidHom.ext hρ
      rw [Subgroup.map_map, hcomp]
  refine not_rkY_of_subgroup π hπ hπker hR ?_ (U := U.map ψ) ?_ (hU2.map ψ) ?_ hrk
  · rw [hRmap, hmap, Subgroup.card_map_of_injective hψinj]
    exact hcard
  · intro hbot
    exact hU ((Subgroup.map_eq_bot_iff_of_injective U hψinj).1 hbot)
  · rw [hRmap, hmap]
    exact map_le_normalizer_map ψ hN

theorem y1431_noCfg_twE6Bad : Y1431NoCfgAt FamTwE6Bad := by
  intro Y _ _ Â ξ J q hcfg t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨rfl, h3⟩ := hF
  have hn0 : n = 0 ∧ ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .twistedE6 p f := by
    rcases hm with ⟨ht', -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact ⟨hn, hE⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨rfl, hE⟩ := hn0
  exact rkY_false_twE6 hcfg.rank hadm.1 hadm.2.1 hE hm h3

end

end CFSG.HardMathSupport.Dickson.Sec6.I1431
