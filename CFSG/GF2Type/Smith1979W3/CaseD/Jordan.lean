module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.GF2Type.Smith1979W3.CaseD

open Equiv Equiv.Perm Finset MulAction Subgroup

section Jordan

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem isMultiplyPretransitive_of_isCycle_five (G : Subgroup (Perm α))
    (hG : IsPreprimitive G α) {r : Perm α} (hr : r.IsCycle) (h5 : r.support.card = 5)
    (hrG : r ∈ G) (hα : 6 < Nat.card α) :
    IsMultiplyPretransitive G α (Nat.card α - 4) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' (le_of_lt hα)
  have hs : ((r.support : Set α)ᶜ).ncard = n + 1 := by
    apply Nat.add_left_cancel
    rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset, h5, add_comm, hn]
  have hs' : n + 2 < Nat.card α := by omega
  have hpre : IsMultiplyPreprimitive G α (n + 2) := by
    apply hG.isMultiplyPreprimitive hs hs'
    haveI := isPretransitive_of_isCycle_mem (G := G) hr hrG
    apply IsPreprimitive.of_prime_card
    have hcard : Nat.card ↥(SubMulAction.ofFixingSubgroup G ((r.support : Set α)ᶜ)) = 5 := by
      change (((r.support : Set α)ᶜ)ᶜ).ncard = 5
      rw [compl_compl, Set.ncard_coe_finset, h5]
    rw [hcard]
    exact Nat.prime_five
  rw [show Nat.card α - 4 = n + 2 by omega]
  exact hpre.isMultiplyPretransitive

theorem card_closure_threeCycles {c c' : Perm α} (hc : c.IsThreeCycle) (hc' : c'.IsThreeCycle)
    (hd : c.Disjoint c') : Nat.card (Subgroup.closure ({c, c'} : Set (Perm α))) = 9 := by
  classical
  let J := Subgroup.closure ({c, c'} : Set (Perm α))
  let cJ : J := ⟨c, Subgroup.subset_closure (by simp)⟩
  let c'J : J := ⟨c', Subgroup.subset_closure (by simp)⟩
  let H := Subgroup.zpowers cJ
  let K' := Subgroup.zpowers c'J
  have hcomm : Commute cJ c'J :=
    Subtype.ext (by simpa [cJ, c'J] using hd.commute.eq)
  have hdisj : H ⊓ K' = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxH, hxK⟩ := hx
    rw [Subgroup.mem_zpowers_iff] at hxH hxK
    obtain ⟨m, hm⟩ := hxH
    obtain ⟨n, hn⟩ := hxK
    rw [Subgroup.mem_bot]
    have hcoeq : c ^ m = c' ^ n := by
      have hh := congr_arg (Subtype.val) (hm.trans hn.symm)
      simpa [Subgroup.coe_zpow, cJ, c'J] using hh
    have hdisj2 : (c ^ m).Disjoint (c ^ m) := by
      have hh := hd.zpow_disjoint_zpow m n
      rwa [← hcoeq] at hh
    have hc1 : c ^ m = 1 := Equiv.Perm.disjoint_refl_iff.mp hdisj2
    rw [← hm]
    apply Subtype.ext
    simpa [Subgroup.coe_zpow, cJ, c'J, hc1]
  have hprod : ∀ g : J, ∃ m n : ℤ, cJ ^ m * c'J ^ n = g := by
    intro g
    refine Subgroup.closure_induction (k := ({c, c'} : Set (Perm α)))
      (p := fun z hz => ∃ m n : ℤ, cJ ^ m * c'J ^ n = (⟨z, hz⟩ : J)) ?_ ?_ ?_ ?_ g.property
    · intro z hzmem
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hzmem
      rcases hzmem with rfl | rfl
      · refine ⟨1, 0, ?_⟩
        apply Subtype.ext
        simp [cJ]
      · refine ⟨0, 1, ?_⟩
        apply Subtype.ext
        simp [c'J]
    · exact ⟨0, 0, by apply Subtype.ext; simp⟩
    · intro x y hx hy hpx hpy
      obtain ⟨m, n, hmn⟩ := hpx
      obtain ⟨p, q, hpq⟩ := hpy
      refine ⟨m + p, n + q, ?_⟩
      change cJ ^ (m + p) * c'J ^ (n + q) = (⟨x, hx⟩ : J) * ⟨y, hy⟩
      rw [zpow_add, zpow_add, ← hmn, ← hpq]
      exact (hcomm.zpow_zpow p n).mul_mul_mul_comm (cJ ^ m) (c'J ^ q)
    · intro x hx hpx
      obtain ⟨m, n, hmn⟩ := hpx
      refine ⟨-m, -n, ?_⟩
      change cJ ^ (-m) * c'J ^ (-n) = (⟨x, hx⟩ : J)⁻¹
      rw [← hmn, (hcomm.zpow_zpow m n).inv]
      group
  let f : H × K' → J := fun x => (x.1 : J) * x.2
  have hf_inj : Function.Injective f := by
    rintro ⟨h1, k1⟩ ⟨h2, k2⟩ heq
    change (h1 : J) * k1 = (h2 : J) * k2 at heq
    have hmem : (h2 : J)⁻¹ * h1 = k2 * (k1 : J)⁻¹ := by
      have hh := congr_arg (fun z => (h2 : J)⁻¹ * z * (k1 : J)⁻¹) heq
      simpa [mul_assoc] using hh
    have hH : (h2 : J)⁻¹ * h1 ∈ H := H.mul_mem (H.inv_mem h2.property) h1.property
    have hK : k2 * (k1 : J)⁻¹ ∈ K' := K'.mul_mem k2.property (K'.inv_mem k1.property)
    have h1eq : (h2 : J)⁻¹ * h1 = 1 := by
      have hmem' : (h2 : J)⁻¹ * h1 ∈ H ⊓ K' :=
        Subgroup.mem_inf.mpr ⟨hH, hmem.symm ▸ hK⟩
      rwa [hdisj, Subgroup.mem_bot] at hmem'
    have hh : h1 = h2 := by
      have hh' := congr_arg (fun z => (h2 : J) * z) h1eq
      simpa [mul_assoc] using hh'
    have hk : k1 = k2 := by
      apply Subtype.ext
      have hh' := heq
      rw [hh] at hh'
      exact mul_left_cancel hh'
    exact Prod.ext hh hk
  have hf_surj : Function.Surjective f := by
    intro g
    obtain ⟨m, n, hmn⟩ := hprod g
    refine ⟨⟨⟨cJ ^ m, Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩⟩,
      ⟨c'J ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩⟩⟩, hmn⟩
  have hcardH : Nat.card H = 3 := by
    rw [Nat.card_zpowers, ← orderOf_injective J.subtype Subtype.coe_injective cJ]
    simpa [cJ] using hc.orderOf
  have hcardK : Nat.card K' = 3 := by
    rw [Nat.card_zpowers, ← orderOf_injective J.subtype Subtype.coe_injective c'J]
    simpa [c'J] using hc'.orderOf
  have hbij : Nat.card (H × K') = Nat.card J :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hcardJ : Nat.card J = 9 := by
    rw [← hbij, Nat.card_prod, hcardH, hcardK]
  simpa [J] using hcardJ

end Jordan

section Restrict

variable {β : Type*} [Fintype β] [DecidableEq β]

@[expose] def resGroup (X : Subgroup (Perm β)) (Ω : Finset β) : Subgroup (Perm {x // x ∈ Ω}) :=
  X.comap (Perm.ofSubtype : Perm {x // x ∈ Ω} →* Perm β)

theorem mem_resGroup {X : Subgroup (Perm β)} {Ω : Finset β} {π : Perm {x // x ∈ Ω}} :
    π ∈ resGroup X Ω ↔ Perm.ofSubtype π ∈ X := Iff.rfl

theorem mem_iff_mem_of_fix {Ω : Finset β} {σ : Perm β} (h : ∀ x, x ∉ Ω → σ x = x) (x : β) :
    σ x ∈ Ω ↔ x ∈ Ω := by
  constructor
  · intro hx
    by_contra hx'
    rw [h x hx'] at hx
    exact hx' hx
  · intro hx
    by_contra hx'
    have hxx : σ x = x := σ.injective (h (σ x) hx')
    exact hx' (hxx.symm ▸ hx)

@[expose] def res {Ω : Finset β} (σ : Perm β) (h : ∀ x, x ∉ Ω → σ x = x) :
    Perm {x // x ∈ Ω} :=
  σ.subtypePerm (mem_iff_mem_of_fix h)

theorem ofSubtype_res {Ω : Finset β} (σ : Perm β) (h : ∀ x, x ∉ Ω → σ x = x) :
    Perm.ofSubtype (res σ h) = σ := by
  unfold res
  exact Perm.ofSubtype_subtypePerm (mem_iff_mem_of_fix h) fun x hx => by
    by_contra hx'
    exact hx (h x hx')

theorem res_apply {Ω : Finset β} (σ : Perm β) (h : ∀ x, x ∉ Ω → σ x = x) (x : {x // x ∈ Ω}) :
    ((res σ h x : {x // x ∈ Ω}) : β) = σ x := by
  unfold res
  rw [Perm.subtypePerm_apply]

theorem res_mem {X : Subgroup (Perm β)} {Ω : Finset β} {σ : Perm β} (hσ : σ ∈ X)
    (h : ∀ x, x ∉ Ω → σ x = x) : res σ h ∈ resGroup X Ω := by
  rw [mem_resGroup, ofSubtype_res]
  exact hσ

theorem card_support_res {Ω : Finset β} (σ : Perm β) (h : ∀ x, x ∉ Ω → σ x = x) :
    (res σ h).support.card = σ.support.card := by
  unfold res
  rw [Perm.support_subtypePerm]
  have hmap : (({x | σ x ≠ x} : Finset Ω)).map (Function.Embedding.subtype (· ∈ Ω)) =
      σ.support := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Perm.mem_support.mpr hy
    · intro hx
      refine ⟨⟨x, ?_⟩, Perm.mem_support.mp hx, rfl⟩
      by_contra hxΩ
      exact Perm.mem_support.mp hx (h x hxΩ)
  rw [← hmap, Finset.card_map]

theorem isThreeCycle_res {Ω : Finset β} {σ : Perm β} (h : ∀ x, x ∉ Ω → σ x = x)
    (hσ : σ.IsThreeCycle) : (res σ h).IsThreeCycle := by
  unfold Perm.IsThreeCycle at hσ ⊢
  rw [← Perm.cycleType_ofSubtype (g := res σ h), ofSubtype_res]
  exact hσ

theorem isCycle_res {Ω : Finset β} {σ : Perm β} (h : ∀ x, x ∉ Ω → σ x = x)
    (hσ : σ.IsCycle) : (res σ h).IsCycle := by
  rw [← Perm.card_cycleType_eq_one]
  rw [← Perm.cycleType_ofSubtype (g := res σ h), ofSubtype_res]
  exact Perm.card_cycleType_eq_one.mpr hσ

theorem fix_of_support_subset {Ω : Finset β} {σ : Perm β} (h : σ.support ⊆ Ω) :
    ∀ x, x ∉ Ω → σ x = x := by
  intro x hx
  by_contra hne
  exact hx (h (Perm.mem_support.mpr hne))

variable {X : Subgroup (Perm β)} {Ω : Finset β}

theorem isPretransitive_resGroup (hfix : ∀ σ ∈ X, ∀ x, x ∉ Ω → σ x = x)
    (htrans : ∀ x ∈ Ω, ∀ y ∈ Ω, ∃ σ ∈ X, σ x = y) :
    IsPretransitive (resGroup X Ω) {x // x ∈ Ω} := by
  rw [MulAction.isPretransitive_iff]
  intro x y
  obtain ⟨σ, hσ, hσxy⟩ := htrans x x.property y y.property
  refine ⟨⟨res σ (hfix σ hσ), res_mem hσ (hfix σ hσ)⟩, ?_⟩
  apply Subtype.ext
  simpa [Subgroup.smul_def, Perm.smul_def, res_apply] using hσxy

theorem isPreprimitive_resGroup_of_prime (hfix : ∀ σ ∈ X, ∀ x, x ∉ Ω → σ x = x)
    (htrans : ∀ x ∈ Ω, ∀ y ∈ Ω, ∃ σ ∈ X, σ x = y) (hp : Ω.card.Prime) :
    IsPreprimitive (resGroup X Ω) {x // x ∈ Ω} := by
  haveI := isPretransitive_resGroup hfix htrans
  apply IsPreprimitive.of_prime_card
  convert hp using 1
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem isPreprimitive_resGroup_of_blocks (hfix : ∀ σ ∈ X, ∀ x, x ∉ Ω → σ x = x)
    (htrans : ∀ x ∈ Ω, ∀ y ∈ Ω, ∃ σ ∈ X, σ x = y)
    (hblocks : ∀ B : Finset β, B ⊆ Ω → 2 ≤ B.card → B.card < Ω.card → B.card ∣ Ω.card →
      ∃ σ ∈ X, B.map σ.toEmbedding ≠ B ∧ ¬ Disjoint (B.map σ.toEmbedding) B) :
    IsPreprimitive (resGroup X Ω) {x // x ∈ Ω} := by
  classical
  haveI := isPretransitive_resGroup hfix htrans
  refine ⟨fun {B} hB => ?_⟩
  by_contra htriv
  rw [MulAction.IsTrivialBlock, not_or] at htriv
  obtain ⟨hBsub, hBtop⟩ := htriv
  have hBne : B.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    exact hBsub (hemp ▸ Set.subsingleton_empty)
  let Bf : Finset β := B.toFinset.map (Function.Embedding.subtype (· ∈ Ω))
  have hBf_sub : Bf ⊆ Ω := by
    intro x hx
    dsimp only [Bf] at hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.property
  have hBf_card : Bf.card = B.ncard := by
    dsimp only [Bf]
    rw [Finset.card_map, Set.ncard_eq_toFinset_card']
  have hBf_ge : 2 ≤ Bf.card := by
    rw [hBf_card]
    by_contra h
    rw [not_le] at h
    exact hBsub (Set.ncard_le_one_iff_subsingleton.mp (by omega))
  have hBf_lt : Bf.card < Ω.card := by
    rw [hBf_card]
    have hlt : B.ncard < (Set.univ : Set {x // x ∈ Ω}).ncard := by
      apply Set.ncard_lt_ncard
      · exact Set.ssubset_univ_iff.mpr hBtop
      · exact Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_coe] at hlt
  have hBf_dvd : Bf.card ∣ Ω.card := by
    rw [hBf_card]
    have hd := MulAction.IsBlock.ncard_dvd_card (G := resGroup X Ω) hB hBne
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at hd
  obtain ⟨σ, hσX, hσne, hσdisj⟩ := hblocks Bf hBf_sub hBf_ge hBf_lt hBf_dvd
  let τ : Perm {x // x ∈ Ω} := res σ (hfix σ hσX)
  have hτmem : τ ∈ resGroup X Ω := res_mem hσX (hfix σ hσX)
  have hcoe : (Bf : Set β) = Subtype.val '' B := by
    dsimp only [Bf]
    rw [Finset.coe_map, Set.coe_toFinset]
    rfl
  have hval_image : ∀ S : Set {x // x ∈ Ω},
      Subtype.val '' (τ '' S) = σ '' (Subtype.val '' S) := by
    intro S
    simp only [Set.image_image]
    congr 1
  have hblock := hB.smul_eq_or_disjoint (⟨τ, hτmem⟩ : resGroup X Ω)
  rw [← Set.image_smul] at hblock
  change τ '' B = B ∨ Disjoint (τ '' B) B at hblock
  rcases hblock with h | h
  · apply hσne
    have h1 : τ '' B = B := h
    have h2 : σ '' (Subtype.val '' B) = Subtype.val '' B := by
      rw [← hval_image B, h1]
    apply Finset.coe_inj.mp
    rw [Finset.coe_map, hcoe]
    exact h2
  · apply hσdisj
    have h1 : Disjoint (τ '' B) B := h
    have h2 : Disjoint (Subtype.val '' (τ '' B)) (Subtype.val '' B) :=
      (Set.disjoint_image_iff Subtype.coe_injective).mpr h1
    rw [hval_image B] at h2
    rw [← Finset.disjoint_coe, Finset.coe_map, hcoe]
    exact h2

theorem exists_map_eq_of_five_cycle (hfix : ∀ σ ∈ X, ∀ x, x ∉ Ω → σ x = x)
    (hprim : IsPreprimitive (resGroup X Ω) {x // x ∈ Ω}) {r : Perm β} (hrX : r ∈ X)
    (hr : r.IsCycle) (h5 : r.support.card = 5) (hΩ : 6 < Ω.card) {F F' : Finset β}
    (hF : F ⊆ Ω) (hF' : F' ⊆ Ω) (hcard : F.card = F'.card) (hk : F.card + 4 ≤ Ω.card) :
    ∃ σ ∈ X, F.map σ.toEmbedding = F' := by
  have hr' : (res r (hfix r hrX)).IsCycle := isCycle_res (hfix r hrX) hr
  have h5' : (res r (hfix r hrX)).support.card = 5 := by
    rw [card_support_res r (hfix r hrX), h5]
  have hr'G : res r (hfix r hrX) ∈ resGroup X Ω := res_mem hrX (hfix r hrX)
  have hN : 6 < Nat.card {x // x ∈ Ω} := by
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe]
  haveI : IsMultiplyPretransitive (resGroup X Ω) {x // x ∈ Ω}
      (Nat.card {x // x ∈ Ω} - 4) :=
    isMultiplyPretransitive_of_isCycle_five (resGroup X Ω) hprim hr' h5' hr'G hN
  have hk' : F.card ≤ Nat.card {x // x ∈ Ω} - 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    omega
  haveI : IsMultiplyPretransitive (resGroup X Ω) {x // x ∈ Ω} F.card :=
    MulAction.isMultiplyPretransitive_of_le hk' (Nat.sub_le _ _)
  let f : Fin F.card ↪ {x // x ∈ Ω} :=
    ⟨fun i => ⟨(F.equivFin.symm i : β), hF (F.equivFin.symm i).property⟩, by
      intro i j hij
      have hij' : (⟨(F.equivFin.symm i : β), hF (F.equivFin.symm i).property⟩ : {x // x ∈ Ω}) =
          ⟨(F.equivFin.symm j : β), hF (F.equivFin.symm j).property⟩ := hij
      exact F.equivFin.symm.injective
        (Subtype.ext (congr_arg (fun z : {x // x ∈ Ω} => (z : β)) hij'))⟩
  let e' : Fin F.card ≃ ↥F' := (finCongr hcard).trans F'.equivFin.symm
  let f' : Fin F.card ↪ {x // x ∈ Ω} :=
    ⟨fun i => ⟨(e' i : β), hF' (e' i).property⟩, by
      intro i j hij
      have hij' : (⟨(e' i : β), hF' (e' i).property⟩ : {x // x ∈ Ω}) =
          ⟨(e' j : β), hF' (e' j).property⟩ := hij
      exact e'.injective
        (Subtype.ext (congr_arg (fun z : {x // x ∈ Ω} => (z : β)) hij'))⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (resGroup X Ω) f f'
  have hg_apply : ∀ i, (g : Perm {x // x ∈ Ω}) (f i) = f' i := by
    intro i
    have h := (Function.Embedding.ext_iff.mp hg) i
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def, Perm.smul_def] using h
  have hrangeF : Subtype.val '' (Set.range f) = (F : Set β) := by
    have h : Set.range f = Subtype.val ⁻¹' (F : Set β) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (F.equivFin.symm i).property
      · intro hx
        refine ⟨F.equivFin ⟨x, hx⟩, ?_⟩
        apply Subtype.ext
        show ((F.equivFin.symm (F.equivFin ⟨x, hx⟩)) : β) = (x : β)
        simp
    rw [h, Set.image_preimage_eq_of_subset (f := Subtype.val) (by simpa using hF)]
  have hrangeF' : Subtype.val '' (Set.range f') = (F' : Set β) := by
    have h : Set.range f' = Subtype.val ⁻¹' (F' : Set β) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (e' i).property
      · intro hx
        refine ⟨e'.symm ⟨x, hx⟩, ?_⟩
        apply Subtype.ext
        show ((e' (e'.symm ⟨x, hx⟩)) : β) = (x : β)
        simp
    rw [h, Set.image_preimage_eq_of_subset (f := Subtype.val) (by simpa using hF')]
  have hrange_g : Set.range f' = (g : Perm {x // x ∈ Ω}) '' Set.range f := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, hg_apply i⟩
    · rintro ⟨x, ⟨i, rfl⟩, hy⟩
      exact ⟨i, (hg_apply i).symm.trans hy⟩
  let σ : Perm β := Perm.ofSubtype (g : Perm {x // x ∈ Ω})
  have hσF : σ '' (F : Set β) = (F' : Set β) := by
    rw [← hrangeF, ← hrangeF', hrange_g]
    simp only [Set.image_image]
    congr 1
    ext x
    exact ofSubtype_apply_of_mem (g : Perm {x // x ∈ Ω}) x.property
  refine ⟨σ, ?_, ?_⟩
  · exact mem_resGroup.mp g.property
  · apply Finset.coe_inj.mp
    rw [Finset.coe_map]
    exact hσF

theorem threeCycle_mem_of_primitive (hfix : ∀ σ ∈ X, ∀ x, x ∉ Ω → σ x = x)
    (hprim : IsPreprimitive (resGroup X Ω) {x // x ∈ Ω}) {c : Perm β} (hcX : c ∈ X)
    (hc : c.IsThreeCycle) {c' : Perm β} (hc' : c'.IsThreeCycle) (hsupp : c'.support ⊆ Ω) :
    c' ∈ X := by
  have hres : (res c (hfix c hcX)).IsThreeCycle := isThreeCycle_res (hfix c hcX) hc
  have hmem : res c (hfix c hcX) ∈ resGroup X Ω := res_mem hcX (hfix c hcX)
  have hle : alternatingGroup {x // x ∈ Ω} ≤ resGroup X Ω :=
    Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hres hmem
  have hres' : (res c' (fix_of_support_subset hsupp)).IsThreeCycle :=
    isThreeCycle_res (fix_of_support_subset hsupp) hc'
  have hmemAlt : res c' (fix_of_support_subset hsupp) ∈ alternatingGroup {x // x ∈ Ω} :=
    Equiv.Perm.mem_alternatingGroup.mpr hres'.sign
  have hX : res c' (fix_of_support_subset hsupp) ∈ resGroup X Ω := hle hmemAlt
  rw [mem_resGroup] at hX
  rwa [ofSubtype_res] at hX

end Restrict

end CFSG.GF2Type.Smith1979W3.CaseD
