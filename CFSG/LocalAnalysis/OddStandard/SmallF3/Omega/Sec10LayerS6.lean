module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

namespace LayerS6

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem oddCore_eq_bot_of_simple {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Even (Nat.card X)) : CFSG.oddCore X = ⊥ := by
  rcases (CFSG.oddCore_normal (G := X)).eq_bot_or_eq_top with h | h
  · exact h
  · have hodd := odd_card_oddCore' X
    rw [h, Subgroup.card_top] at hodd
    exact absurd hX (Nat.not_even_iff_odd.2 hodd)

private theorem isQuasisimple_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hX
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have e : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨?_⟩, e.isSimpleGroup, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hX
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1)
    · exact h
  · obtain ⟨a, b, hab⟩ := hX
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h1 := congrArg e h
    simpa using h1

private theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem alt6_exists_not_comm : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  letI : CommGroup (alternatingGroup (Fin 6)) :=
    { (inferInstance : Group (alternatingGroup (Fin 6))) with mul_comm := hcon }
  have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 6))
  rw [card_alt6] at hp
  have h2 := hp.eq_one_or_self_of_dvd 2 ⟨180, rfl⟩
  omega

private theorem isQuasisimple_alt6 : CFSG.IsQuasisimple (alternatingGroup (Fin 6)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact isQuasisimple_of_simple alt6_exists_not_comm

theorem layer_eq_of_normal_quasisimple {Y : Type*} [Group Y] (E : Subgroup Y) [E.Normal]
    (hE : CFSG.IsQuasisimple ↥E) (hsolv : Group.IsSolvable (Y ⧸ E)) : CFSG.layer Y = E := by
  refine le_antisymm (sSup_le fun K hK => ?_)
    (le_sSup ⟨hE, Subgroup.Normal.isSubnormal inferInstance⟩)
  have : Group.IsPerfect ↥K := hK.1.1
  let f : ↥K →* Y ⧸ E := (QuotientGroup.mk' E).comp K.subtype
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have := hsolv
  intro x hx
  by_contra hxE
  have hnt : Nontrivial ↥f.range := by
    refine ⟨⟨⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, 1, fun h => hxE ?_⟩⟩
    have h1 : f ⟨x, hx⟩ = 1 := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff x).mp h1
  exact Group.IsPerfect.not_isSolvable ↥f.range inferInstance

theorem layer_equiv_alt6 {H : Type*} [Group H] (e : H ≃* Equiv.Perm (Fin 6)) :
    Nonempty (↥(CFSG.layer H) ≃* alternatingGroup (Fin 6)) := by
  let E : Subgroup H := (alternatingGroup (Fin 6)).map e.symm.toMonoidHom
  haveI : E.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
  let eE : ↥E ≃* alternatingGroup (Fin 6) :=
    ((alternatingGroup (Fin 6)).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  have hmem : ∀ x : H, x ∈ E ↔ e x ∈ alternatingGroup (Fin 6) := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hx
      exact ⟨e x, hx, by simp⟩
  have hsolv : Group.IsSolvable (H ⧸ E) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with | _ x => ?_
    induction b using QuotientGroup.induction_on with | _ y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hmem,
      Equiv.Perm.mem_alternatingGroup]
    simp [mul_comm]
  have hlayer : CFSG.layer H = E :=
    layer_eq_of_normal_quasisimple E (CFSG.IsQuasisimple.of_mulEquiv eE isQuasisimple_alt6) hsolv
  exact ⟨(MulEquiv.subgroupCongr hlayer).trans eE⟩

variable {G : Type} [Group G] {L : Subgroup G} {s : G}

theorem layerCent_equiv_alt6 (e : ↥(L ⊓ centralizer ({s} : Set G)) ≃* Equiv.Perm (Fin 6)) :
    Nonempty (↥(layerCent L s) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e'⟩ := layer_equiv_alt6 e
  exact ⟨(((CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))).equivMapOfInjective
    (L ⊓ centralizer ({s} : Set G)).subtype (Subgroup.subtype_injective _)).symm).trans e'⟩

theorem layerCent_ne_bot_of_equiv (e : ↥(L ⊓ centralizer ({s} : Set G)) ≃* Equiv.Perm (Fin 6)) :
    layerCent L s ≠ ⊥ := by
  obtain ⟨e1⟩ := layerCent_equiv_alt6 e
  intro hbot
  have hcard := Nat.card_congr e1.toEquiv
  rw [hbot, Subgroup.card_bot, card_alt6] at hcard
  omega

theorem isL29_layerCent_of_equiv (e : ↥(L ⊓ centralizer ({s} : Set G)) ≃* Equiv.Perm (Fin 6)) :
    IsL29 (layerCent L s) := by
  obtain ⟨e1⟩ := layerCent_equiv_alt6 e
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥(layerCent L s) := e1.isSimpleGroup
  haveI : Finite ↥(layerCent L s) := Finite.of_equiv _ e1.symm.toEquiv
  have hcard : Nat.card ↥(layerCent L s) = 360 := by
    rw [Nat.card_congr e1.toEquiv, card_alt6]
  have hodd : CFSG.oddCore ↥(layerCent L s) = ⊥ :=
    oddCore_eq_bot_of_simple (by rw [hcard]; decide)
  have e2 : (↥(layerCent L s) ⧸ CFSG.oddCore ↥(layerCent L s)) ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot).trans e1
  exact Or.inl ⟨by decide,
    CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _
      ⟨e2⟩⟩

theorem isComponentIn_layerCent_of_equiv [Finite G]
    (e : ↥(L ⊓ centralizer ({s} : Set G)) ≃* Equiv.Perm (Fin 6)) :
    IsComponentIn (layerCent L s) (L ⊓ centralizer ({s} : Set G)) :=
  isComponentIn_layerCent (Or.inr (Or.inl (isL29_layerCent_of_equiv e)))

end LayerS6

end CFSG.OddStandard.SmallF3.Omega
