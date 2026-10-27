module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Cent

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section AltEmb

variable {n m : ℕ}

@[expose] def altEmb (e : Fin m ↪ Fin n) : Subgroup (Perm (Fin n)) where
  carrier := {g | (∀ x, x ∉ Set.range e → g x = x) ∧ sign g = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Perm.mul_apply, hb x hx, ha x hx]
    · rw [Perm.sign_mul, ha', hb', mul_one]
  one_mem' := ⟨fun x _ => rfl, Perm.sign_one⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · have := ha x hx
      rw [Perm.inv_eq_iff_eq]
      exact this.symm
    · rw [Perm.sign_inv, ha']

theorem mem_altEmb_iff {e : Fin m ↪ Fin n} {g : Perm (Fin n)} :
    g ∈ altEmb e ↔ (∀ x, x ∉ Set.range e → g x = x) ∧ sign g = 1 := Iff.rfl

theorem altEmb_le_alternatingGroup (e : Fin m ↪ Fin n) : altEmb e ≤ alternatingGroup (Fin n) :=
  fun _ hg => Perm.mem_alternatingGroup.mpr hg.2

theorem map_alternatingGroup_eq_altEmb (e : Fin m ↪ Fin n) :
    (alternatingGroup (Fin m)).map (Equiv.Perm.viaEmbeddingHom e) = altEmb e := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [Equiv.Perm.viaEmbeddingHom_apply]
    refine ⟨fun x hx => Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx, ?_⟩
    rw [Equiv.Perm.viaEmbedding, Perm.sign_extendDomain]
    exact Perm.mem_alternatingGroup.mp hτ
  · rintro ⟨hfix, hsign⟩
    have hmem : ∀ i, ∃ j, e j = g (e i) := by
      intro i
      by_cases hr : g (e i) ∈ Set.range e
      · exact hr
      · exfalso
        have h1 : g (e i) = e i := g.injective (hfix _ hr)
        exact hr ⟨i, h1.symm⟩
    choose f hf using hmem
    have hinj : Function.Injective f := by
      intro i i' hii
      apply e.injective
      apply g.injective
      rw [← hf i, ← hf i', hii]
    let τ : Perm (Fin m) := Equiv.ofBijective f hinj.bijective_of_finite
    have hτ : ∀ i, e (τ i) = g (e i) := hf
    have hgτ : Equiv.Perm.viaEmbedding τ e = g := by
      ext x
      by_cases hx : x ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hx
        rw [Equiv.Perm.viaEmbedding_apply, hτ]
      · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx, hfix _ hx]
    refine ⟨τ, ?_, hgτ⟩
    rw [Perm.mem_alternatingGroup]
    have := congrArg Perm.sign hgτ
    rw [Equiv.Perm.viaEmbedding, Perm.sign_extendDomain] at this
    rw [this, hsign]

end AltEmb

section Cover

variable {n m : ℕ} {K : Type} [Group K]

theorem exists_doubleCover_altEmb (hn : 8 ≤ n) (hm : 5 ≤ m) (C : CoverSetup n K)
    (e : Fin m ↪ Fin n) :
    ∃ L : Subgroup K, IsDoubleCoverOfAlt ↥L m ∧ L.map C.ρ = altEmb e ∧ center K ≤ L := by
  set E : Subgroup K := (altEmb e).comap C.ρ with hE
  have hEmap : E.map C.ρ = altEmb e := C.map_comap_eq_of_le (altEmb_le_alternatingGroup e)
  set L : Subgroup K := ⁅E, E⁆ with hL
  have haltPerf : ⁅altEmb e, altEmb e⁆ = altEmb e := by
    rw [← map_alternatingGroup_eq_altEmb, ← Subgroup.map_commutator]
    congr 1
    have : Group.IsPerfect (alternatingGroup (Fin m)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
    exact Subgroup.isPerfect_iff.1 this
  have hLmap : L.map C.ρ = altEmb e := by
    rw [hL, Subgroup.map_commutator, hEmap, haltPerf]
  have hcen : ∀ a ∈ E, ∃ l ∈ L, l⁻¹ * a ∈ center K := by
    intro a ha
    have : C.ρ a ∈ L.map C.ρ := by rw [hLmap]; exact ha
    obtain ⟨l, hl, hla⟩ := this
    exact ⟨l, hl, by rw [← C.ρ_eq_one_iff, map_mul, map_inv, hla, inv_mul_cancel]⟩
  have hLperf : ⁅L, L⁆ = L := by
    apply le_antisymm
    · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
    · rw [hL]
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      obtain ⟨l₁, hl₁, hc₁⟩ := hcen a ha
      obtain ⟨l₂, hl₂, hc₂⟩ := hcen b hb
      have e₁ : a = l₁ * (l₁⁻¹ * a) := by group
      have e₂ : b = l₂ * (l₂⁻¹ * b) := by group
      have : ⁅a, b⁆ = ⁅l₁, l₂⁆ := by
        rw [e₁, e₂]
        exact (CFSG.SectionRank.commutatorElement_mul_mem_center l₁ l₂ hc₁ hc₂).trans (by
          simp)
      rw [this]
      exact Subgroup.commutator_mem_commutator hl₁ hl₂
  have hm4 : 4 ≤ m := by omega
  set a := e ⟨0, by omega⟩ with ha
  set b := e ⟨1, by omega⟩ with hb
  set c := e ⟨2, by omega⟩ with hc
  set d := e ⟨3, by omega⟩ with hd
  have hinj := e.injective
  have hab : a ≠ b := fun h => by have := hinj h; simp at this
  have hac : a ≠ c := fun h => by have := hinj h; simp at this
  have had : a ≠ d := fun h => by have := hinj h; simp at this
  have hbc : b ≠ c := fun h => by have := hinj h; simp at this
  have hbd : b ≠ d := fun h => by have := hinj h; simp at this
  have hcd : c ≠ d := fun h => by have := hinj h; simp at this
  set u : Perm (Fin n) := swap a b * swap c d with hu
  have hu_mem : u ∈ altEmb e := by
    refine ⟨fun x hx => ?_, ?_⟩
    · have h1 : x ≠ a := fun h => hx ⟨_, h.symm⟩
      have h2 : x ≠ b := fun h => hx ⟨_, h.symm⟩
      have h3 : x ≠ c := fun h => hx ⟨_, h.symm⟩
      have h4 : x ≠ d := fun h => hx ⟨_, h.symm⟩
      rw [hu, Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]
    · rw [hu, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
      decide
  obtain ⟨x, hxL, hxρ⟩ : ∃ x ∈ L, C.ρ x = u := by
    have : u ∈ L.map C.ρ := by rw [hLmap]; exact hu_mem
    obtain ⟨x, hx, hxu⟩ := this
    exact ⟨x, hx, hxu⟩
  have hxx : x * x ≠ 1 := C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hxρ
  have hxxL : x * x ∈ L := L.mul_mem hxL hxL
  have hxxc : x * x ∈ center K := C.sq_mem_center (by
    rw [hxρ, hu]
    exact dbl_mul_self hab hac had hbc hbd hcd)
  have hZL : center K ≤ L := by
    intro c' hc'
    by_cases h1 : c' = 1
    · rw [h1]
      exact L.one_mem
    · rw [C.center_eq_of_ne_one hc' hxxc h1 hxx]
      exact hxxL
  let eAlt : alternatingGroup (Fin m) ≃* altEmb e :=
    (Subgroup.equivMapOfInjective _ _ (Equiv.Perm.viaEmbeddingHom_injective e)).trans
      (MulEquiv.subgroupCongr (map_alternatingGroup_eq_altEmb e))
  let ρL₀ : L →* altEmb e := (C.ρ.comp L.subtype).codRestrict (altEmb e) (fun x => by
    have : C.ρ x ∈ L.map C.ρ := ⟨x, x.2, rfl⟩
    rwa [hLmap] at this)
  let ρL : L →* alternatingGroup (Fin m) := eAlt.symm.toMonoidHom.comp ρL₀
  have hρL : ∀ x : L, ρL x = 1 ↔ (x : K) ∈ center K := fun x => by
    show eAlt.symm (ρL₀ x) = 1 ↔ _
    rw [map_eq_one_iff _ eAlt.symm.injective, ← C.ρ_eq_one_iff]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  have hsurj : Function.Surjective ρL := by
    intro a
    have : (eAlt a : Perm (Fin n)) ∈ L.map C.ρ := by rw [hLmap]; exact (eAlt a).2
    obtain ⟨l, hl, hla⟩ := this
    refine ⟨⟨l, hl⟩, ?_⟩
    show eAlt.symm (ρL₀ ⟨l, hl⟩) = a
    have : ρL₀ ⟨l, hl⟩ = eAlt a := Subtype.ext hla
    rw [this, MulEquiv.symm_apply_apply]
  have hkc : ρL.ker ≤ center ↥L := by
    intro x hx
    have hxc : (x : K) ∈ center K := (hρL x).1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.1 hxc g)
  have hkereq : ρL.ker = (center K).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, hρL, Subgroup.mem_subgroupOf]
  have hk2 : Nat.card ρL.ker = 2 := by
    rw [hkereq, ← C.center_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv
  exact ⟨L, isDoubleCoverOfAlt_of_ker hm (Subgroup.isPerfect_iff.2 hLperf) ρL hsurj hkc hk2,
    hLmap, hZL⟩

end Cover

end CFSG.OddStandard.Solomon75.AhatData
