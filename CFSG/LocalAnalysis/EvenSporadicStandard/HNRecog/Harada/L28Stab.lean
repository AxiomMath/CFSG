module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

private theorem nontrivial_ker_of_perm_to_alt
    (g : Equiv.Perm (Fin 5) →* alternatingGroup (Fin 5)) : Nontrivial g.ker := by
  refine (Subgroup.nontrivial_iff_ne_bot _).mpr ?_
  intro hbot
  have hinj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hbot
  have hcard := Nat.card_le_card_of_injective
    (g : Equiv.Perm (Fin 5) → alternatingGroup (Fin 5)) hinj
  have hperm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have halt : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  omega

theorem L28_not_le_base_of_equiv_perm {S : Subgroup A5WrTwo} (e : ↥S ≃* Equiv.Perm (Fin 5)) :
    ¬ S ≤ commutator A5WrTwo := by
  intro hS
  let q : Equiv.Perm (Fin 5) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
    (MonoidHom.ofInjective A5WrTwo.baseEmb_injective).symm.toMonoidHom.comp
      (((MulEquiv.subgroupCongr A5WrTwo.range_baseEmb).symm.toMonoidHom).comp
        ((Subgroup.inclusion hS).comp e.symm.toMonoidHom))
  let q₁ : Equiv.Perm (Fin 5) →* alternatingGroup (Fin 5) :=
    (MonoidHom.fst (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).comp q
  let q₂ : Equiv.Perm (Fin 5) →* alternatingGroup (Fin 5) :=
    (MonoidHom.snd (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).comp q
  have hq_inj : Function.Injective q := by
    change Function.Injective (fun x : Equiv.Perm (Fin 5) =>
      (MonoidHom.ofInjective A5WrTwo.baseEmb_injective).symm
        ((MulEquiv.subgroupCongr A5WrTwo.range_baseEmb).symm
          (Subgroup.inclusion hS (e.symm x))))
    exact ((MonoidHom.ofInjective A5WrTwo.baseEmb_injective).symm.injective).comp
      (((MulEquiv.subgroupCongr A5WrTwo.range_baseEmb).symm.injective).comp
        ((Subgroup.inclusion_injective hS).comp e.symm.injective))
  have hker : q.ker = ⊥ := MonoidHom.ker_eq_bot q hq_inj
  have hprod : q₁.prod q₂ = q :=
    MonoidHom.ext fun _ => Prod.ext rfl rfl
  have hker12 : q₁.ker ⊓ q₂.ker = ⊥ := by
    rw [← MonoidHom.ker_prod q₁ q₂, hprod, hker]
  have hle1 : alternatingGroup (Fin 5) ≤ q₁.ker :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5)
      (by simp [Nat.card_eq_fintype_card]) (nontrivial_ker_of_perm_to_alt q₁)
  have hle2 : alternatingGroup (Fin 5) ≤ q₂.ker :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5)
      (by simp [Nat.card_eq_fintype_card]) (nontrivial_ker_of_perm_to_alt q₂)
  have hle : alternatingGroup (Fin 5) ≤ ⊥ := by
    rw [← hker12]
    exact le_inf hle1 hle2
  have hbot : alternatingGroup (Fin 5) = ⊥ := le_bot_iff.mp hle
  have halt : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [hbot, Subgroup.card_bot] at halt
  omega

theorem L28_nonempty_equiv_inf_base {S : Subgroup A5WrTwo} (e : ↥S ≃* Equiv.Perm (Fin 5)) :
    Nonempty (↥(S ⊓ commutator A5WrTwo) ≃* alternatingGroup (Fin 5)) := by
  let φ : ↥S →* Multiplicative (ZMod 2) :=
    (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).comp S.subtype
  have hker : φ.ker = (S ⊓ commutator A5WrTwo).subgroupOf S := by
    change ((RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).comp
      S.subtype).ker = (S ⊓ commutator A5WrTwo).subgroupOf S
    rw [← MonoidHom.comap_ker, ← A5WrTwo.commutator_eq_ker, Subgroup.comap_subtype,
      inf_comm S (commutator A5WrTwo), Subgroup.inf_subgroupOf_right]
  have hφ_ne_one : φ ≠ 1 := by
    intro hφ
    refine L28_not_le_base_of_equiv_perm e ?_
    intro x hx
    have hx1 : (RegularWreathProduct.rightHom (x : A5WrTwo)) = 1 := by
      have h := congrArg (fun f : ↥S →* Multiplicative (ZMod 2) => f ⟨x, hx⟩) hφ
      simpa [φ, MonoidHom.comp_apply] using h
    rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]
    exact hx1
  have hcardC2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hnt_range : Nontrivial φ.range := by
    refine (Subgroup.nontrivial_iff_ne_bot _).mpr ?_
    intro h
    exact hφ_ne_one ((MonoidHom.range_eq_bot_iff (f := φ)).mp h)
  have htop : φ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq φ.range ?_
    have hdvd : Nat.card φ.range ∣ 2 := by
      simpa [hcardC2] using Subgroup.card_subgroup_dvd_card φ.range
    have hle : Nat.card φ.range ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hlt : 1 < Nat.card φ.range :=
      (Subgroup.one_lt_card_iff_ne_bot φ.range).mpr
        ((Subgroup.nontrivial_iff_ne_bot _).mp hnt_range)
    omega
  have hindex : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, htop, Subgroup.card_top, hcardC2]
  let K : Subgroup (Equiv.Perm (Fin 5)) := φ.ker.map (e : ↥S →* Equiv.Perm (Fin 5))
  have hKindex : K.index = 2 := by
    change (φ.ker.map (e : ↥S →* Equiv.Perm (Fin 5))).index = 2
    rw [Subgroup.index_map_equiv φ.ker e, hindex]
  have hK : K = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hKindex
  exact ⟨((Subgroup.subgroupOfEquivOfLe inf_le_left).symm).trans
    (((MulEquiv.subgroupCongr hker).symm).trans
      ((Subgroup.equivMapOfInjective φ.ker (e : ↥S →* Equiv.Perm (Fin 5)) e.injective).trans
        (MulEquiv.subgroupCongr hK)))⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
