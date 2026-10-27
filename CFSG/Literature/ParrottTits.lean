module

public import CFSG.Literature.ParrottTitsCheck
public import CFSG.Sporadic.Schreier.TitsOuter

public noncomputable section

namespace CFSG.Literature.ParrottTits

open CFSG.CosetTable CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem card_parrottGroup_le :
    Finite ParrottGroup ∧ Nat.card ParrottGroup ≤ 17971200 := by
  obtain ⟨hf, hc⟩ := card_PG_le
  exact ⟨Finite.of_equiv _ parrottEquivPG.symm.toEquiv,
    (Nat.card_congr parrottEquivPG.toEquiv).trans_le hc⟩

@[expose] noncomputable def parrottPerm (i : ℕ) :
    Equiv.Perm (Fin 1755) :=
  Classical.choose parrott_perms i

@[expose] noncomputable def parrottFam (i : Fin 10) :
    Equiv.Perm (Fin 1755) :=
  parrottPerm i

theorem lift_parrottRelators :
    ∀ r ∈ parrottRelators, FreeGroup.lift parrottFam r = 1 := by
  intro r hr
  rw [parrottRelators_eq] at hr
  simp only [Set.mem_ofPred_eq, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact (Classical.choose_spec parrott_perms).1 w hw

@[expose] def parrottHom : ParrottGroup →* Equiv.Perm (Fin 1755) :=
  PresentedGroup.toGroup lift_parrottRelators

theorem range_presentedGroup_toGroup {α X : Type*} [Group X] {rels : Set (FreeGroup α)}
    {f : α → X} (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    (PresentedGroup.toGroup h).range = Subgroup.closure (Set.range f) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, PresentedGroup.toGroup.of]

theorem titsDGen_eq_wordIn
    {j : ℕ} (hj : j < 2) :
    titsDGen j = wordIn 10 parrottPerm ([parrottD0Word, parrottD1Word].getD j []) := by
  rw [← titsDerived_perm hj]
  exact (Classical.choose_spec parrott_perms).2 j hj

theorem titsD_le_range :
    titsD ≤ parrottHom.range := by
  rw [parrottHom, range_presentedGroup_toGroup, titsD, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  change titsDGen (j : ℕ) ∈ Subgroup.closure (Set.range parrottFam)
  rw [titsDGen_eq_wordIn j.2]
  refine wordIn_mem ?_ _
  intro i hi
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem range_parrottHom :
    parrottHom.range = titsD := by
  obtain ⟨hfin, hle⟩ := card_parrottGroup_le
  have hc : Nat.card parrottHom.range ≤ Nat.card titsD := by
    rw [card_titsD]
    exact (Nat.card_le_card_of_surjective _ parrottHom.rangeRestrict_surjective).trans hle
  exact (Subgroup.eq_of_le_of_card_ge titsD_le_range hc).symm

theorem parrottHom_bijective :
    Function.Bijective parrottHom.rangeRestrict ∧ Nat.card ParrottGroup = 17971200 := by
  obtain ⟨hfin, hle⟩ := card_parrottGroup_le
  have hcard : Nat.card parrottHom.range = 17971200 := by rw [range_parrottHom, card_titsD]
  have hsurj := parrottHom.rangeRestrict_surjective
  have hge : Nat.card parrottHom.range ≤ Nat.card ParrottGroup :=
    Nat.card_le_card_of_surjective _ hsurj
  refine ⟨hsurj.bijective_of_nat_card_le (by omega), by omega⟩

@[expose] def parrottEquivD :
    ParrottGroup ≃* titsD :=
  (MulEquiv.ofBijective _ parrottHom_bijective.1).trans (MulEquiv.subgroupCongr range_parrottHom)

theorem reeTitsModel_of_lieModel {T : Type} [Group T]
    (h : CFSG.Blueprint.LieModel T .Tits 0 2 1) : CFSG.Blueprint.ReeTitsModel T .Tits 2 1 :=
  (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2

theorem CL_LIT_Parrott_Tits_group_presentation
    (T : Type) [Group T]
    (hT : CFSG.Blueprint.LieModel T .Tits 0 2 1) :
    Nonempty (ParrottGroup ≃* T) ∧ Nat.card ParrottGroup = 17971200 ∧
      (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 ∧
      ∀ (X : Type*) [Group X] (ρ : Fin 10 → X),
        (∀ p ∈ parrottRelations, FreeGroup.lift ρ p.1 = FreeGroup.lift ρ p.2) →
          ∃ f : T →* X, f.range = Subgroup.closure (Set.range ρ) ∧
            (Subgroup.closure (Set.range ρ) = ⊥ ∨
              Nonempty (Subgroup.closure (Set.range ρ) ≃* T)) := by
  have hree := reeTitsModel_of_lieModel hT
  obtain ⟨eT⟩ := titsModelEquiv T 2 1 hree
  have hsimple := (CFSG.LieType.Simplicity.fam_tits_simplicity T 2 1 hree).2
  set e : ParrottGroup ≃* T := parrottEquivD.trans eT.symm
  refine ⟨⟨e⟩, parrottHom_bijective.2, by norm_num, ?_⟩
  intro X _ ρ hρ
  have hrel := (lift_relators_iff ρ).1 hρ
  set ψ : ParrottGroup →* X := PresentedGroup.toGroup hrel
  set f : T →* X := ψ.comp e.symm.toMonoidHom
  have hrange : f.range = Subgroup.closure (Set.range ρ) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, ← MonoidHom.range_eq_map,
      range_presentedGroup_toGroup]
  refine ⟨f, hrange, ?_⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal f.ker with hker | hker
  · right
    rw [← hrange]
    exact ⟨(MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff f).1 hker)).symm⟩
  · left
    rw [← hrange, eq_bot_iff]
    rintro _ ⟨t, rfl⟩
    have ht : t ∈ f.ker := hker ▸ Subgroup.mem_top t
    exact Subgroup.mem_bot.2 ht

end CFSG.Literature.ParrottTits
