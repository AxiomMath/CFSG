module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ChoiceExists
public import Certificates.Certificate2022
import CFSG.Models.PGLSimple
import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
import CFSG.Models.PGLOrders
import TauCeti.GroupTheory.Perm.Jordan
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup MulAction
open scoped Pointwise

universe u v

variable {S : Type v} [Group S] [IsSimpleGroup S]

private theorem subtypePerm_invariance {β : Type u} [Fintype β] [DecidableEq β]
    (Y : Subgroup (Perm β)) (O : Set β) (k : ↥(fixingSubgroup Y O)) :
    ∀ x : β, (((k : Y) : Perm β) x ∉ O) ↔ x ∉ O := by
  intro x
  have hk : ∀ y ∈ O, ((k : Y) : Perm β) y = y := (mem_fixingSubgroup_iff Y).mp k.2
  have hkinv : ∀ y ∈ O, (((k : Y) : Perm β)⁻¹) y = y := by
    intro y hy
    have h := (mem_fixingSubgroup_iff Y).mp ((fixingSubgroup Y O).inv_mem k.2) y hy
    change (((k : Y) : Perm β)⁻¹) y = y at h
    exact h
  constructor
  · intro hkx hx
    rw [hk x hx] at hkx
    exact hkx hx
  · intro hx hkx
    have h1 : (((k : Y) : Perm β)⁻¹) (((k : Y) : Perm β) x) = ((k : Y) : Perm β) x :=
      hkinv _ hkx
    have hsymm : (((k : Y) : Perm β)⁻¹) (((k : Y) : Perm β) x) = x := by
      simpa using Equiv.symm_apply_apply ((k : Y) : Perm β) x
    have h2 : x = ((k : Y) : Perm β) x := hsymm.symm.trans h1
    exact hx (h2 ▸ hkx)

private noncomputable def complementHom {β : Type u} [Fintype β] [DecidableEq β]
    (Y : Subgroup (Perm β)) (O : Set β) :
    ↥(fixingSubgroup Y O) →* Perm {x : β // x ∉ O} := by
  classical
  exact
  { toFun := fun k => (((k : Y) : Perm β).subtypePerm (subtypePerm_invariance Y O k))
    map_one' := by
      change Equiv.Perm.subtypePerm (1 : Perm β) (p := fun x : β => x ∉ O) _ = 1
      rw [Equiv.Perm.subtypePerm_one]
    map_mul' := fun k₁ k₂ => by
      apply Equiv.Perm.ext
      intro x
      change (Equiv.Perm.subtypePerm (((k₁ : Y) : Perm β) * ((k₂ : Y) : Perm β))
        (p := fun x : β => x ∉ O) _) x = _
      rw [Equiv.Perm.subtypePerm_mul] }

private theorem complementHom_injective {β : Type u} [Fintype β] [DecidableEq β]
    (Y : Subgroup (Perm β)) (O : Set β) :
    Function.Injective (complementHom Y O) := by
  classical
  intro k₁ k₂ h
  have h₁ : Equiv.Perm.ofSubtype (p := fun x : β => x ∉ O) (complementHom Y O k₁) =
      ((k₁ : Y) : Perm β) := by
    exact Equiv.Perm.ofSubtype_subtypePerm (subtypePerm_invariance Y O k₁)
      (fun x hx => by
        by_contra hxO
        exact hx ((mem_fixingSubgroup_iff Y).mp k₁.2 x hxO))
  have h₂ : Equiv.Perm.ofSubtype (p := fun x : β => x ∉ O) (complementHom Y O k₂) =
      ((k₂ : Y) : Perm β) := by
    exact Equiv.Perm.ofSubtype_subtypePerm (subtypePerm_invariance Y O k₂)
      (fun x hx => by
        by_contra hxO
        exact hx ((mem_fixingSubgroup_iff Y).mp k₂.2 x hxO))
  have hc := congrArg (Equiv.Perm.ofSubtype (p := fun x : β => x ∉ O)) h
  rw [h₁, h₂] at hc
  apply Subtype.ext
  apply Subtype.ext
  exact hc

private theorem toPermHom_ker_orbit {α : Type u} [Fintype α] [DecidableEq α]
    {G : Type u} [Group G] [MulAction G α] (a : α) :
    (MulAction.toPermHom G (orbit G a)).ker = fixingSubgroup G (orbit G a) := by
  ext y
  rw [MonoidHom.mem_ker]
  constructor
  · intro hy
    rw [mem_fixingSubgroup_iff]
    intro b hb
    have hb' := congrArg (fun f : Perm (orbit G a) => (f ⟨b, hb⟩ : orbit G a)) hy
    exact congrArg Subtype.val hb'
  · intro hy
    apply Equiv.ext
    intro b
    have hb : ((b : orbit G a) : α) ∈ orbit G a := b.2
    have := (mem_fixingSubgroup_iff G).mp hy ((b : orbit G a) : α) hb
    exact Subtype.ext (by simpa using this)

private theorem quotient_reduction {n : ℕ} (hn : n ≤ 11)
    (ih : ∀ m : ℕ, m < n → m ≤ 11 →
      ∀ (γ : Type u) [Fintype γ] [DecidableEq γ], Fintype.card γ = m →
        ∀ (Y : Subgroup (Equiv.Perm γ)) (ψ : Y →* S), ¬ Function.Surjective ψ)
    {G : Type u} [Group G]
    {β : Type u} [Fintype β] [DecidableEq β]
    (ψ : G →* S) (hψ : Function.Surjective ψ)
    (K : Subgroup G) (ρ : G →* Perm β) (hker : ρ.ker = K) (hKle : K ≤ ψ.ker)
    (hsmall : Fintype.card β < n) : False := by
  classical
  haveI : K.Normal := by rw [← hker]; exact MonoidHom.normal_ker ρ
  let ψq : G ⧸ K →* S := QuotientGroup.lift K ψ hKle
  have hψq : Function.Surjective ψq := by
    intro s
    obtain ⟨y, rfl⟩ := hψ s
    exact ⟨QuotientGroup.mk' K y, by simp [ψq, QuotientGroup.lift_mk]⟩
  let e : G ⧸ K ≃* ρ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientMulEquivOfEq (MonoidHom.ker_rangeRestrict ρ).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ρ.rangeRestrict
          (MonoidHom.rangeRestrict_surjective ρ)))
  let ψ' : ρ.range →* S := ψq.comp e.symm.toMonoidHom
  have hψ' : Function.Surjective ψ' := hψq.comp e.symm.surjective
  exact ih (Fintype.card β) hsmall (le_trans (le_of_lt hsmall) hn) β rfl
    ρ.range ψ' hψ'

private theorem complement_reduction {n : ℕ} (hn : n ≤ 11)
    (ih : ∀ m : ℕ, m < n → m ≤ 11 →
      ∀ (γ : Type u) [Fintype γ] [DecidableEq γ], Fintype.card γ = m →
        ∀ (Y : Subgroup (Equiv.Perm γ)) (ψ : Y →* S), ¬ Function.Surjective ψ)
    {β : Type u} [Fintype β] [DecidableEq β]
    (Y : Subgroup (Perm β)) (ψ : Y →* S) (O : Set β) (hO : O ≠ Set.univ)
    (hOpos : O.Nonempty) (hcardβ : Fintype.card β = n)
    (hKsurj : Function.Surjective
      (ψ.comp (fixingSubgroup Y O).subtype)) : False := by
  classical
  let K : Subgroup Y := fixingSubgroup Y O
  let ρ : K →* Perm {x : β // x ∉ O} := complementHom Y O
  have hρinj : Function.Injective ρ := complementHom_injective Y O
  let Yc : Subgroup (Perm {x : β // x ∉ O}) := ρ.range
  let eK : K ≃* Yc := MonoidHom.ofInjective hρinj
  let ψc : Yc →* S := (ψ.comp K.subtype).comp eK.symm.toMonoidHom
  have hψc : Function.Surjective ψc := by
    have h := hKsurj.comp eK.symm.surjective
    simpa [ψc] using h
  have hsmall : Fintype.card {x : β // x ∉ O} < n := by
    have hcardcomp : Nat.card {x : β // x ∉ O} = Oᶜ.ncard := by
      change Nat.card {x : β // x ∉ O} = Oᶜ.ncard
      letI : Fintype {x : β // x ∉ O} := Fintype.ofFinite _
      letI : Fintype ↥(Oᶜ) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      change Fintype.card ↥(Oᶜ) = Oᶜ.ncard
      exact Set.fintypeCard_eq_ncard (Oᶜ)
    have hβn : Nat.card β = n := by rw [Nat.card_eq_fintype_card, hcardβ]
    have hpos : 0 < O.ncard := (Set.ncard_pos (s := O)).mpr hOpos
    have hOlt : O.ncard < n := by
      rw [← hβn]
      exact Set.ncard_lt_card hO
    rw [← Nat.card_eq_fintype_card]
    calc Nat.card {x : β // x ∉ O} = Oᶜ.ncard := hcardcomp
      _ = Nat.card β - O.ncard := Set.ncard_compl O
      _ = n - O.ncard := by rw [hβn]
      _ < n := by omega
  exact ih (Fintype.card {x : β // x ∉ O}) hsmall (le_trans (le_of_lt hsmall) hn)
    {x : β // x ∉ O} rfl Yc ψc hψc

private theorem intransitive_reduction {n : ℕ} (hn : n ≤ 11)
    (ih : ∀ m : ℕ, m < n → m ≤ 11 →
      ∀ (γ : Type u) [Fintype γ] [DecidableEq γ], Fintype.card γ = m →
        ∀ (Y : Subgroup (Equiv.Perm γ)) (ψ : Y →* S), ¬ Function.Surjective ψ)
    {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β]
    (Y : Subgroup (Perm β)) (ψ : Y →* S) (hψ : Function.Surjective ψ)
    (hcardβ : Fintype.card β = n) (hntrans : ¬ IsPretransitive Y β) : False := by
  classical
  let a : β := Classical.choice ‹Nonempty β›
  let O : Set β := orbit Y a
  have hOne : O ≠ Set.univ := by
    intro h
    apply hntrans
    refine ⟨fun x y => ?_⟩
    have hx : x ∈ O := by rw [h]; exact Set.mem_univ x
    have hy : y ∈ O := by rw [h]; exact Set.mem_univ y
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    obtain ⟨g', hg'⟩ := MulAction.mem_orbit_iff.mp hx
    refine ⟨g * g'⁻¹, ?_⟩
    calc (g * g'⁻¹) • x = (g * g'⁻¹) • (g' • a) := by rw [← hg']
      _ = g • a := by simp [mul_smul]
      _ = y := hg
  have hOpos : O.Nonempty := ⟨a, MulAction.mem_orbit_self a⟩
  let K : Subgroup Y := fixingSubgroup Y O
  let ρ : Y →* Perm O := MulAction.toPermHom Y O
  have hker : ρ.ker = K := by
    change (MulAction.toPermHom Y (orbit Y a)).ker = fixingSubgroup Y (orbit Y a)
    exact toPermHom_ker_orbit a
  have hKnormal : K.Normal := by rw [← hker]; exact MonoidHom.normal_ker ρ
  haveI : K.Normal := hKnormal
  have hmapNormal : (Subgroup.map ψ K).Normal := hKnormal.map ψ hψ
  haveI : (Subgroup.map ψ K).Normal := hmapNormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.map ψ K) with hbot | htop
  · have hKle : K ≤ ψ.ker := (Subgroup.map_eq_bot_iff K).mp hbot
    have hsmall : Fintype.card O < n := by
      rw [← Nat.card_eq_fintype_card]
      change Nat.card ↥O < n
      rw [Nat.card_coe_set_eq]
      have hβn : Nat.card β = n := by rw [Nat.card_eq_fintype_card, hcardβ]
      rw [← hβn]
      exact Set.ncard_lt_card hOne
    exact quotient_reduction hn ih ψ hψ K ρ hker hKle hsmall
  · have hKsurj : Function.Surjective (ψ.comp K.subtype) := by
      intro s
      have hs : s ∈ Subgroup.map ψ K := by rw [htop]; exact Subgroup.mem_top s
      obtain ⟨k, hk, hkψ⟩ := Subgroup.mem_map.mp hs
      exact ⟨⟨k, hk⟩, by simpa using hkψ⟩
    exact complement_reduction hn ih Y ψ O hOne hOpos hcardβ hKsurj

private theorem not_isPretransitive_of_fixes_proper_set {β : Type u}
    [Fintype β] [DecidableEq β] (B : Set β) (hBne : B.Nonempty)
    (hBnotuniv : B ≠ Set.univ) (Lβ : Subgroup (Perm β))
    (hfix : ∀ lβ : Lβ, (lβ : Perm β) • B = B) :
    ¬ IsPretransitive Lβ β := by
  intro htr
  obtain ⟨b, hb⟩ := hBne
  obtain ⟨c, hc⟩ : ∃ c, c ∉ B := by
    by_contra h
    push Not at h
    exact hBnotuniv (Set.eq_univ_of_forall h)
  obtain ⟨y, hy⟩ := htr.exists_smul_eq b c
  have hyB : (y : Perm β) • B = B := hfix y
  have hcB : c ∈ B := by
    have hmem : (y : Perm β) • b ∈ (y : Perm β) • B := Set.smul_mem_smul_set hb
    rw [hyB] at hmem
    have hy' : (y : Perm β) • b = c := by
      simpa [Subgroup.smul_def] using hy
    rwa [hy'] at hmem
  exact hc hcB

private theorem block_kernel_top_reduction {n : ℕ} (hn : n ≤ 11)
    (ih : ∀ m : ℕ, m < n → m ≤ 11 →
      ∀ (γ : Type u) [Fintype γ] [DecidableEq γ], Fintype.card γ = m →
        ∀ (Y : Subgroup (Equiv.Perm γ)) (ψ : Y →* S), ¬ Function.Surjective ψ)
    {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β]
    (Y : Subgroup (Perm β)) (ψ : Y →* S) (hψ : Function.Surjective ψ)
    (B : Set β) (hBne : B.Nonempty) (hBnotuniv : B ≠ Set.univ)
    (O : Set (Set β)) (hO : O = orbit Y B)
    (L : Subgroup Y) (hL : L = fixingSubgroup Y O) (ρ : Y →* Perm O)
    (hker : ρ.ker = L) (htop : Subgroup.map ψ L = ⊤)
    (hcardβ : Fintype.card β = n) : False := by
  classical
  let Lβ : Subgroup (Perm β) := L.map Y.subtype
  let eL : L ≃* Lβ := Subgroup.equivMapOfInjective L Y.subtype Y.subtype_injective
  let ψL : L →* S := ψ.comp L.subtype
  have hψL : Function.Surjective ψL := by
    intro s
    have hs : s ∈ Subgroup.map ψ L := by rw [htop]; exact Subgroup.mem_top s
    obtain ⟨l, hl, hls⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨l, hl⟩, by simpa [ψL] using hls⟩
  let ψLβ : Lβ →* S := ψL.comp eL.symm.toMonoidHom
  have hψLβ : Function.Surjective ψLβ := hψL.comp eL.symm.surjective
  have hfixB : ∀ l : L, ((l : Y) : Perm β) • B = B := by
    intro l
    have hl : (l : Y) ∈ fixingSubgroup Y O := by
      rw [← hL]
      exact l.2
    have h := (mem_fixingSubgroup_iff Y).mp hl B (by rw [hO]; exact MulAction.mem_orbit_self B)
    simpa [Subgroup.smul_def] using h
  have hfixLβ : ∀ lβ : Lβ, (lβ : Perm β) • B = B := by
    intro lβ
    obtain ⟨l, rfl⟩ := eL.surjective lβ
    change ((l : Y) : Perm β) • B = B
    exact hfixB l
  have hLβntrans : ¬ IsPretransitive Lβ β :=
    not_isPretransitive_of_fixes_proper_set B hBne hBnotuniv Lβ hfixLβ
  exact intransitive_reduction hn ih Lβ ψLβ hψLβ hcardβ hLβntrans

private theorem block_reduction {n : ℕ} (hn : n ≤ 11)
    (ih : ∀ m : ℕ, m < n → m ≤ 11 →
      ∀ (γ : Type u) [Fintype γ] [DecidableEq γ], Fintype.card γ = m →
        ∀ (Y : Subgroup (Equiv.Perm γ)) (ψ : Y →* S), ¬ Function.Surjective ψ)
    {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β]
    (Y : Subgroup (Perm β)) (ψ : Y →* S) (hψ : Function.Surjective ψ)
    (hcardβ : Fintype.card β = n) (htrans : IsPretransitive Y β)
    (hnotprim : ¬ IsPreprimitive Y β) : False := by
  classical
  have hex : ∃ B : Set β, IsBlock Y B ∧ ¬ IsTrivialBlock B := by
    by_contra h
    push Not at h
    exact hnotprim (IsPreprimitive.mk (fun {B} hB => h B hB))
  obtain ⟨B, hB, hBnt⟩ := hex
  have hBne : B.Nonempty := by
    by_contra h
    exact hBnt (Or.inl (by
      rw [Set.not_nonempty_iff_eq_empty.mp h]
      exact Set.subsingleton_empty))
  have hBnotuniv : B ≠ Set.univ := fun h => hBnt (Or.inr h)
  have hBntsub : ¬ B.Subsingleton := fun h => hBnt (Or.inl h)
  have hBsize : 1 < B.ncard :=
    Set.one_lt_ncard_iff_nontrivial_and_finite.mpr
      ⟨Set.not_subsingleton_iff.mp hBntsub, Set.toFinite B⟩
  let O : Set (Set β) := orbit Y B
  let ρ : Y →* Perm O := MulAction.toPermHom Y O
  let L : Subgroup Y := fixingSubgroup Y O
  have hker : ρ.ker = L := by
    change (MulAction.toPermHom Y (orbit Y B)).ker = fixingSubgroup Y (orbit Y B)
    exact toPermHom_ker_orbit B
  have hblockmul := hB.ncard_block_mul_ncard_orbit_eq hBne
  have hβn : Nat.card β = n := by rw [Nat.card_eq_fintype_card, hcardβ]
  have hOncard_lt : O.ncard < n := by
    have hOpos : 0 < O.ncard :=
      (Set.ncard_pos (s := O)).mpr ⟨B, MulAction.mem_orbit_self B⟩
    by_contra h
    have hge : n ≤ O.ncard := Nat.le_of_not_lt h
    have hmul : 2 * n ≤ B.ncard * O.ncard :=
      Nat.mul_le_mul (by omega : 2 ≤ B.ncard) hge
    rw [hblockmul, hβn] at hmul
    have hnpos : 0 < n := by rw [← hβn]; exact Nat.card_pos
    omega
  have hLnormal : L.Normal := by rw [← hker]; exact MonoidHom.normal_ker ρ
  haveI : L.Normal := hLnormal
  have hmapNormal : (Subgroup.map ψ L).Normal := hLnormal.map ψ hψ
  haveI : (Subgroup.map ψ L).Normal := hmapNormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.map ψ L) with hbot | htop
  · have hLle : L ≤ ψ.ker := (Subgroup.map_eq_bot_iff L).mp hbot
    have hsmall : Fintype.card O < n := by
      rw [← Nat.card_eq_fintype_card]
      change Nat.card ↥O < n
      rw [Nat.card_coe_set_eq]
      exact hOncard_lt
    exact quotient_reduction hn ih ψ hψ L ρ hker hLle hsmall
  · exact block_kernel_top_reduction hn ih Y ψ hψ B hBne hBnotuniv O rfl L rfl ρ hker htop
      hcardβ

private theorem alternatingGroup_le_of_prime {n p : ℕ} (hp : Nat.Prime p) (hp3 : p + 3 ≤ n)
    (hpn : n < 2 * p) (hpdvd : p ∣ Nat.card S)
    {β : Type u} [Fintype β] [DecidableEq β] (hcard : Fintype.card β = n)
    (Y : Subgroup (Perm β)) (ψ : Y →* S) (hψ : Function.Surjective ψ)
    (hprim : IsPreprimitive Y β) : alternatingGroup β ≤ Y := by
  classical
  have hpdvdY : p ∣ Nat.card Y :=
    hpdvd.trans (Subgroup.card_dvd_of_surjective (f := ψ) hψ)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' p hpdvdY
  have hgperm : orderOf ((g : Y) : Perm β) = p := by
    rw [Subgroup.orderOf_coe, hgord]
  have hcyc : ((g : Y) : Perm β).IsCycle := by
    refine Equiv.Perm.isCycle_of_prime_order' ?_ ?_
    · rwa [hgperm]
    · rw [hcard, hgperm]
      omega
  have hsupp : ((g : Y) : Perm β).support.card = p := by
    rw [← hcyc.orderOf, hgperm]
  have hp3' : p + 3 ≤ Nat.card β := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact hp3
  exact TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hprim hp hp3' hcyc hsupp g.2

private theorem alternatingGroup_le_of_primitive
    (hS : Nat.card S = 20160)
    {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    {β : Type u} [Fintype β] [DecidableEq β] (hcard : Fintype.card β = n)
    (Y : Subgroup (Perm β)) (ψ : Y →* S) (hψ : Function.Surjective ψ)
    (hprim : IsPreprimitive Y β) : alternatingGroup β ≤ Y := by
  by_cases hn10 : 10 ≤ n
  · have hpdvd : 7 ∣ Nat.card S := by rw [hS]; norm_num
    exact alternatingGroup_le_of_prime (S := S) (p := 7) (by norm_num) (by omega)
      (by omega) hpdvd hcard Y ψ hψ hprim
  · have hpdvd : 5 ∣ Nat.card S := by rw [hS]; norm_num
    exact alternatingGroup_le_of_prime (S := S) (p := 5) (by norm_num) (by omega)
      (by omega) hpdvd hcard Y ψ hψ hprim

private theorem nonempty_equiv_alternatingGroup_eight_of_injective
    (hS : Nat.card S = 20160)
    {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    {β : Type u} [Fintype β] [DecidableEq β] [Nontrivial β]
    (hcard : Fintype.card β = n)
    (f : alternatingGroup β →* S) (hsurj : Function.Surjective f)
    (hinj : Function.Injective f) :
    Nonempty (S ≃* alternatingGroup (Fin 8)) := by
  classical
  have hcardn : Nat.card β = n := by rw [Nat.card_eq_fintype_card, hcard]
  let eAS : alternatingGroup β ≃* S := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hcardA : Nat.card (alternatingGroup β) = Nat.card S := Nat.card_congr eAS.toEquiv
  have hfac : Nat.factorial n = 40320 := by
    have h2 := two_mul_nat_card_alternatingGroup (α := β)
    rw [hcardA, hS, Nat.card_perm, hcardn] at h2
    omega
  have hn_eq : n = 8 := by
    by_contra h
    have h9 : 9 ≤ n := by omega
    have hle := Nat.factorial_le h9
    rw [hfac] at hle
    norm_num at hle
  have hcard8 : Fintype.card β = 8 := by rw [hcard, hn_eq]
  let efin : β ≃ Fin 8 := Fintype.equivFinOfCardEq hcard8
  exact ⟨eAS.symm.trans (Equiv.altCongrHom efin)⟩

private theorem false_of_alternatingGroup_le_bot
    (hS : Nat.card S = 20160)
    {β : Type u} [Fintype β] [DecidableEq β] [Nontrivial β]
    (Y : Subgroup (Perm β)) (ψ : Y →* S) (hψ : Function.Surjective ψ)
    (A : Subgroup (Perm β)) (N : Subgroup Y) (hA : A = alternatingGroup β)
    (hN : N = A.subgroupOf Y) (hNnormal : N.Normal) (halt : A ≤ Y)
    (hNle : N ≤ ψ.ker) : False := by
  classical
  haveI : N.Normal := hNnormal
  let ψq : Y ⧸ N →* S := QuotientGroup.lift N ψ hNle
  have hψq : Function.Surjective ψq := by
    intro s
    obtain ⟨y, rfl⟩ := hψ s
    exact ⟨QuotientGroup.mk' N y, by simp [ψq, QuotientGroup.lift_mk]⟩
  have hcardq : Nat.card (Y ⧸ N) ≤ 2 := by
    change N.index ≤ 2
    have hrel : A.relIndex Y ≤ 2 := by
      have hdvd : A.relIndex Y ∣ A.index := Subgroup.relIndex_dvd_index_of_le halt
      rw [hA] at hdvd ⊢
      rw [alternatingGroup.index_eq_two] at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd
    rw [hN]
    exact hrel
  have hle : Nat.card S ≤ Nat.card (Y ⧸ N) :=
    Nat.le_of_dvd (Nat.card_pos)
      (Subgroup.card_dvd_of_surjective (f := ψq) hψq)
  rw [hS] at hle
  omega

private theorem false_of_alternatingGroup_le
    (hS : Nat.card S = 20160)
    (hA8 : IsEmpty (S ≃* alternatingGroup (Fin 8)))
    {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    {β : Type u} [Fintype β] [DecidableEq β] (hcard : Fintype.card β = n)
    (Y : Subgroup (Perm β)) (ψ : Y →* S) (hψ : Function.Surjective ψ)
    (halt : alternatingGroup β ≤ Y) : False := by
  classical
  have hcardn : Nat.card β = n := by rw [Nat.card_eq_fintype_card, hcard]
  haveI : Nontrivial β := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hcard]; omega)
  let A : Subgroup (Perm β) := alternatingGroup β
  let N : Subgroup Y := A.subgroupOf Y
  have hNnormal : N.Normal := Subgroup.normal_subgroupOf (H := Y) (N := A)
  haveI : N.Normal := hNnormal
  have hmapNormal : (Subgroup.map ψ N).Normal := hNnormal.map ψ hψ
  haveI : (Subgroup.map ψ N).Normal := hmapNormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.map ψ N) with hbot | htop
  · have hNle : N ≤ ψ.ker := (Subgroup.map_eq_bot_iff N).mp hbot
    exact false_of_alternatingGroup_le_bot hS Y ψ hψ A N rfl rfl hNnormal halt hNle
  · have hNtop : Subgroup.map ψ N = ⊤ := htop
    let fA : A →* S := ψ.comp (Subgroup.inclusion halt)
    have hfAsurj : Function.Surjective fA := by
      intro s
      have hs : s ∈ Subgroup.map ψ N := by rw [hNtop]; exact Subgroup.mem_top s
      obtain ⟨y, hy, hyψ⟩ := Subgroup.mem_map.mp hs
      have hyA : ((y : Y) : Perm β) ∈ A := (Subgroup.mem_subgroupOf).mp hy
      refine ⟨⟨(y : Perm β), hyA⟩, ?_⟩
      have hinc : (Subgroup.inclusion halt) ⟨((y : Y) : Perm β), hyA⟩ = y :=
        Subtype.ext rfl
      simpa [fA, hinc] using hyψ
    let K : Subgroup A := fA.ker
    haveI : K.Normal := MonoidHom.normal_ker fA
    have hsimpleA : IsSimpleGroup A :=
      alternatingGroup.isSimpleGroup (by rw [hcardn]; omega)
    haveI : IsSimpleGroup A := hsimpleA
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hKbot | hKtop
    · have hinj : Function.Injective fA := (MonoidHom.ker_eq_bot_iff fA).mp hKbot
      obtain ⟨e8⟩ := nonempty_equiv_alternatingGroup_eight_of_injective hS hn8 hn11 hcard
        fA hfAsurj hinj
      exact hA8.false e8
    · have hfA1 : fA = 1 := by
        ext a
        have haK : a ∈ K := by rw [hKtop]; exact Subgroup.mem_top a
        have ha : a ∈ fA.ker := by simpa [K] using haK
        simpa using (MonoidHom.mem_ker.mp ha)
      obtain ⟨s, hs⟩ : ∃ s : S, s ≠ 1 := exists_ne 1
      obtain ⟨a, ha⟩ := hfAsurj s
      have h1 : fA a = 1 := by
        rw [hfA1]
        rfl
      rw [h1] at ha
      exact hs ha.symm

private theorem not_surjective_of_card_le_eleven_aux
    (hS : Nat.card S = 20160)
    (hA8 : IsEmpty (S ≃* alternatingGroup (Fin 8)))
    (n : ℕ) : n ≤ 11 →
    ∀ {β : Type u} [Fintype β] [DecidableEq β], Fintype.card β = n →
      ∀ (Y : Subgroup (Perm β)) (ψ : Y →* S), ¬ Function.Surjective ψ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn β _ _ hcard Y ψ hψ
    have hcardn : Nat.card β = n := by rw [Nat.card_eq_fintype_card, hcard]
    have hdvd : 20160 ∣ Nat.card Y := by
      rw [← hS]
      exact Subgroup.card_dvd_of_surjective (f := ψ) hψ
    have hYle : Nat.card Y ≤ n.factorial := by
      calc Nat.card Y ≤ Nat.card (Perm β) := Subgroup.card_le_card_group Y
        _ = (Nat.card β).factorial := Nat.card_perm
        _ = n.factorial := by rw [hcardn]
    have h2 : 20160 ≤ n.factorial :=
      (Nat.le_of_dvd (Nat.card_pos) hdvd).trans hYle
    have hn8 : 8 ≤ n := by
      by_contra h
      have hn7 : n ≤ 7 := by omega
      have hle := Nat.factorial_le hn7
      norm_num at hle
      omega
    haveI : Nonempty β := Fintype.card_pos_iff.mp (by rw [hcard]; omega)
    by_cases htrans : IsPretransitive Y β
    · by_cases hprim : IsPreprimitive Y β
      · exact false_of_alternatingGroup_le hS hA8 hn8 hn hcard Y ψ hψ
          (alternatingGroup_le_of_primitive hS hn8 hn hcard Y ψ hψ hprim)
      · exact block_reduction (n := n) hn ih Y ψ hψ hcard htrans hprim
    · exact intransitive_reduction (n := n) hn ih Y ψ hψ hcard htrans

theorem not_surjective_of_card_le_eleven {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : Nat.card S = 20160) (hA8 : IsEmpty (S ≃* alternatingGroup (Fin 8)))
    {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α ≤ 11)
    (X : Subgroup (Equiv.Perm α)) (φ : X →* S) : ¬ Function.Surjective φ :=
  not_surjective_of_card_le_eleven_aux (S := S) hS hA8 (Fintype.card α) hα rfl X φ

theorem kFactL34NotInvolvedA11_holds :
    KFactL34NotInvolvedA11 := by
  classical
  intro X φ hφ
  let A : Subgroup (Perm (Fin 11)) := alternatingGroup (Fin 11)
  have hsub : Function.Injective A.subtype := Subgroup.subtype_injective A
  let Y : Subgroup (Perm (Fin 11)) := X.map A.subtype
  let e : X ≃* Y := Subgroup.equivMapOfInjective X A.subtype hsub
  let ψ : Y →* _root_.CFSG.PGLModel.projSL 3 (GaloisField 2 2) :=
    φ.comp e.symm.toMonoidHom
  have hψ : Function.Surjective ψ := hφ.comp e.symm.surjective
  haveI : IsSimpleGroup (_root_.CFSG.PGLModel.projSL 3 (GaloisField 2 2)) :=
    _root_.CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 2 2)
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hS : Nat.card (_root_.CFSG.PGLModel.projSL 3 (GaloisField 2 2)) = 20160 :=
    _root_.CFSG.PGLModel.card_projSL_three_four
  have hA8 : IsEmpty (_root_.CFSG.PGLModel.projSL 3 (GaloisField 2 2) ≃*
      alternatingGroup (Fin 8)) := by
    have hX : _root_.CFSG.Open.StatedClassicalModel
        (_root_.CFSG.PGLModel.projSL 3 (GaloisField 2 2)) .PSL 3 2 2 :=
      _root_.CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL
        ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
        (MulEquiv.refl _)
    exact (_root_.CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated
      (_root_.CFSG.PGLModel.projSL 3 (GaloisField 2 2)) hX).2.2 (Fin 8) (by simp)
  exact not_surjective_of_card_le_eleven hS hA8 (by simp) Y ψ hψ

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
