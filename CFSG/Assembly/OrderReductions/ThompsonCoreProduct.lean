module

public import CFSG.Assembly.OrderReductions.AbelianSylowCore

public section

namespace CFSG.OrderReductions.ThompsonCoreProduct

open CFSG.OrderReductions.PrimeComplementCore
open CFSG.OrderReductions.ThompsonCenter

@[expose] noncomputable def coreProduct {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group) : Subgroup group :=
  primeComplementCore prime group ⊔
    (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype

theorem coreProduct_nontrivial {group : Type*} [Group group] [Finite group] [Nontrivial group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group) :
    coreProduct prime sylow ≠ ⊥ := by
  classical
  intro trivial
  have core_bot : primeComplementCore prime group = ⊥ :=
    le_bot_iff.mp (trivial ▸ (show primeComplementCore prime group ≤ coreProduct prime sylow from le_sup_left))
  by_cases divides : prime ∣ Nat.card group
  · have : Nontrivial (sylow : Subgroup group) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr (sylow.ne_bot_of_dvd_card divides)
    have center_nontrivial := thompsonCenter_nontrivial_of_prime_group prime sylow.isPGroup'
    have image_bot : (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype = ⊥ :=
      le_bot_iff.mp (trivial ▸ (show
        (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype ≤ coreProduct prime sylow from le_sup_right))
    apply center_nontrivial
    apply Subgroup.map_injective (f := (sylow : Subgroup group).subtype) Subtype.val_injective
    rw [Subgroup.map_bot]
    exact image_bot
  · have top_coprime : ¬ prime ∣ Nat.card (⊤ : Subgroup group) := by
      rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup group) ≃* group).toEquiv]
      exact divides
    have top_le := normal_le_primeComplementCore prime (⊤ : Subgroup group) top_coprime
    rw [core_bot] at top_le
    exact bot_ne_top (le_bot_iff.mp top_le).symm

theorem coreProduct_map_le {source target : Type*} [Group source] [Finite source]
    [Group target] [Finite target] (prime : ℕ) [Fact (Nat.Prime prime)]
    (equivalence : source ≃* target) (sylow : Sylow prime source) :
    (coreProduct prime sylow).map equivalence.toMonoidHom ≤
      coreProduct prime (Sylow.mapSurjective (f := equivalence.toMonoidHom) equivalence.surjective sylow) := by
  have surjective : Function.Surjective equivalence.toMonoidHom := equivalence.surjective
  let image := Sylow.mapSurjective surjective sylow
  have image_eq : (image : Subgroup target) = (sylow : Subgroup source).map equivalence.toMonoidHom :=
    Sylow.coe_mapSurjective surjective sylow
  let internal : (sylow : Subgroup source) ≃* (image : Subgroup target) :=
    (equivalence.subgroupMap (sylow : Subgroup source)).trans (MulEquiv.subgroupCongr image_eq.symm)
  have intertwines : (image : Subgroup target).subtype.comp internal.toMonoidHom =
      equivalence.toMonoidHom.comp (sylow : Subgroup source).subtype := by
    ext element
    rfl
  have center_eq := congrArg (fun candidate : Subgroup (image : Subgroup target) =>
    candidate.map (image : Subgroup target).subtype) (thompsonCenter_map_eq internal)
  rw [Subgroup.map_map, intertwines, ← Subgroup.map_map] at center_eq
  unfold coreProduct
  rw [Subgroup.map_sup, map_core_eq_of_equiv prime equivalence, center_eq]

theorem coreProduct_characteristic_of_abelian {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (sylow : Sylow prime group) [IsMulCommutative (sylow : Subgroup group)] :
    (coreProduct prime sylow).Characteristic :=
  CFSG.OrderReductions.AbelianSylowCore.core_sup_thompsonCenter_characteristic_of_abelian prime sylow

theorem coreProduct_map_eq {source target : Type*} [Group source] [Finite source]
    [Group target] [Finite target] (prime : ℕ) [Fact (Nat.Prime prime)]
    (equivalence : source ≃* target) (sylow : Sylow prime source) :
    (coreProduct prime sylow).map equivalence.toMonoidHom =
      coreProduct prime (Sylow.mapSurjective (f := equivalence.toMonoidHom) equivalence.surjective sylow) := by
  have surjective : Function.Surjective equivalence.toMonoidHom := equivalence.surjective
  let image := Sylow.mapSurjective surjective sylow
  have image_eq : (image : Subgroup target) = (sylow : Subgroup source).map equivalence.toMonoidHom :=
    Sylow.coe_mapSurjective surjective sylow
  let internal : (sylow : Subgroup source) ≃* (image : Subgroup target) :=
    (equivalence.subgroupMap (sylow : Subgroup source)).trans (MulEquiv.subgroupCongr image_eq.symm)
  have intertwines : (image : Subgroup target).subtype.comp internal.toMonoidHom =
      equivalence.toMonoidHom.comp (sylow : Subgroup source).subtype := by
    ext element
    rfl
  have center_eq := congrArg (fun candidate : Subgroup (image : Subgroup target) =>
    candidate.map (image : Subgroup target).subtype) (thompsonCenter_map_eq internal)
  rw [Subgroup.map_map, intertwines, ← Subgroup.map_map] at center_eq
  unfold coreProduct
  rw [Subgroup.map_sup, map_core_eq_of_equiv prime equivalence, center_eq]

theorem coreProduct_characteristic_of_independent_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (independent : ∀ other : Sylow prime group, coreProduct prime other = coreProduct prime sylow) :
    (coreProduct prime sylow).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro automorphism
  rw [coreProduct_map_eq prime automorphism sylow]
  exact independent _

theorem independent_sylow_of_coreProduct_characteristic {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (characteristic : (coreProduct prime sylow).Characteristic) :
    ∀ other : Sylow prime group, coreProduct prime other = coreProduct prime sylow := by
  intro other
  obtain ⟨acting, conjugates⟩ := MulAction.exists_smul_eq group sylow other
  have surjective : Function.Surjective (MulAut.conj acting).toMonoidHom := (MulAut.conj acting).surjective
  have image_eq : Sylow.mapSurjective surjective sylow = other := by
    apply Sylow.ext
    rw [Sylow.coe_mapSurjective, ← CFSG.OrderReductions.FixedPairSylow.sylow_smul_subgroup_eq, conjugates]
  have mapped := coreProduct_map_eq prime (MulAut.conj acting) sylow
  rw [image_eq] at mapped
  exact mapped.symm.trans (Subgroup.characteristic_iff_map_eq.mp characteristic (MulAut.conj acting))

end CFSG.OrderReductions.ThompsonCoreProduct
