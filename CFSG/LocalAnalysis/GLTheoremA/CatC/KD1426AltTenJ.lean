module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltFix
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenJ

variable {Y : Type} [Group Y]

theorem J_pSimple {K : Subgroup Y} (π : ↥K ≃* alternatingGroup (Fin 10))
    {σ : alternatingGroup (Fin 10)}
    (hσc : ((σ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).support.card = 3)
    {J : Subgroup Y}
    (hJ : J = ((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom).map K.subtype) :
    GLAPPrimeCore 3 ↥J = ⊥ ∧ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥J = 2520 := by
  classical
  subst hJ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨RF⟩ := nonempty_altFix_equiv (σ : Equiv.Perm (Fin 10)) (m := 7) (by rw [hσc])
  have hFπ : ((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom).map π.toMonoidHom =
      altFix (σ : Equiv.Perm (Fin 10)) :=
    Subgroup.map_comap_eq_self_of_surjective π.surjective _
  let e1 : ↥((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom) ≃*
      ↥((((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom)).map K.subtype) :=
    Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective
  let e2 : ↥((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom) ≃*
      ↥(altFix (σ : Equiv.Perm (Fin 10))) :=
    (Subgroup.equivMapOfInjective _ π.toMonoidHom π.injective).trans
      (MulEquiv.subgroupCongr hFπ)
  let eJA7 : ↥((((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom)).map K.subtype) ≃*
      alternatingGroup (Fin 7) := (e1.symm.trans e2).trans RF
  haveI : Finite ↥((((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom)).map K.subtype) :=
    Finite.of_injective eJA7 eJA7.injective
  have hA7simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  haveI : IsSimpleGroup ↥((((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom)).map K.subtype) :=
    eJA7.isSimpleGroup
  have hJc : Nat.card ↥((((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom)).map K.subtype) =
      2520 := by
    rw [Nat.card_congr eJA7.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hcen : Subgroup.center ↥((((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom)).map
      K.subtype) = ⊥ := by
    have h1 := Subgroup.map_center_eq eJA7
    have h2 : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    rw [h2] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eJA7.injective).1 h1
  have hcore : GLAPPrimeCore 3 ↥((((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom)).map
      K.subtype) = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top
      (GLAPPrimeCore 3 ↥((((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom)).map K.subtype))
      with h | h
    · exact h
    · exfalso
      have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3
          ↥((((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom)).map K.subtype))) :=
        CFSG.pPrimeCore_coprime_card
      rw [h, Subgroup.card_top, hJc] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop (by norm_num)
  exact ⟨hcore, ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans
    eJA7⟩, hJc⟩

end CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenJ

end
