module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.IsPerfect
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.ABGLocalTools CFSG.LocalCores
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro b hb
  have hb' : b ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h a ha b hb
  exact Subgroup.centralizer_le_normalizer _ hb'

theorem exists_mul_of_mem_sup {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have h1 := Subgroup.coe_mul_of_right_le_normalizer_left A B h
  have hx' : x ∈ (↑(A ⊔ B) : Set G) := hx
  rw [h1] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem relIndex_map_dvd {G' : Type*} [Group G'] (φ : G →* G') (H K : Subgroup G) :
    (H.map φ).relIndex (K.map φ) ∣ H.relIndex K := by
  have hK : K.map φ = (φ.comp K.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hK, ← Subgroup.index_comap]
  exact Subgroup.index_dvd_of_le fun k hk =>
    Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)

theorem isSylowOf_map {G' : Type*} [Group G'] [Finite G] [Finite G'] {p : ℕ} (hp : p.Prime)
    (f : G →* G') {P K : Subgroup G} (h : IsSylowOf p P K) :
    IsSylowOf p (P.map f) (K.map f) := by
  have := Fact.mk hp
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  exact ⟨Subgroup.map_mono hle, hP.map f, fun hd => hdvd (hd.trans (relIndex_map_dvd f P K))⟩

theorem relIndex_sup_dvd_of_commute {A B A' B' : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : A' ≤ A) (hB : B' ≤ B) :
    (A' ⊔ B').relIndex (A ⊔ B) ∣ A'.relIndex A * B'.relIndex B := by
  have hBn : B ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_commute hAB
  have hBn' : B' ≤ Subgroup.normalizer (A' : Set G) :=
    le_normalizer_of_commute fun a ha b hb => hAB a (hA ha) b (hB hb)
  let f : ↥A × ↥B →* ↥(A ⊔ B) :=
    MonoidHom.noncommCoprod (Subgroup.inclusion (le_sup_left : A ≤ A ⊔ B))
      (Subgroup.inclusion (le_sup_right : B ≤ A ⊔ B))
      (fun a b => Subtype.ext (hAB a a.2 b b.2))
  have hf : ∀ (a : ↥A) (b : ↥B), ((f (a, b) : ↥(A ⊔ B)) : G) = a * b := fun _ _ => rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hBn hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (hf ⟨a, ha⟩ ⟨b, hb⟩)⟩
  let W : Subgroup (↥A × ↥B) := (A'.subgroupOf A).prod (B'.subgroupOf B)
  have hW : W.map f = (A' ⊔ B').subgroupOf (A ⊔ B) := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨⟨a, b⟩, hab, hfab⟩
      have h1 : x = a * b := by
        have := congrArg Subtype.val hfab
        rw [hf] at this
        exact this.symm
      show x ∈ A' ⊔ B'
      rw [h1]
      exact Subgroup.mul_mem_sup (Subgroup.mem_prod.1 hab).1 (Subgroup.mem_prod.1 hab).2
    · intro hx'
      have hx'' : x ∈ A' ⊔ B' := hx'
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hBn' hx''
      refine ⟨(⟨a, hA ha⟩, ⟨b, hB hb⟩), Subgroup.mem_prod.2 ⟨ha, hb⟩, Subtype.ext ?_⟩
      rw [hf ⟨a, hA ha⟩ ⟨b, hB hb⟩]
      exact hab.symm
  have h1 : (W.map f).index ∣ W.index := Subgroup.index_map_dvd W hsurj
  rw [hW] at h1
  have h2 : W.index = A'.relIndex A * B'.relIndex B := Subgroup.index_prod _ _
  rw [h2] at h1
  exact h1

theorem relIndex_iSup_dvd_prod {ι : Type*} [Fintype ι] (L L' : ι → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ L i, ∀ b ∈ L j, a * b = b * a) (hle : ∀ i, L' i ≤ L i) :
    (⨆ i, L' i).relIndex (⨆ i, L i) ∣ ∏ i, (L' i).relIndex (L i) := by
  classical
  have key : ∀ s : Finset ι,
      (⨆ i ∈ s, L' i).relIndex (⨆ i ∈ s, L i) ∣ ∏ i ∈ s, (L' i).relIndex (L i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.iSup_insert, Finset.iSup_insert, Finset.prod_insert hj]
      have hcen : (⨆ i ∈ s, L i) ≤ Subgroup.centralizer (L j : Set G) := by
        refine iSup₂_le fun i hi => ?_
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        intro b hb a ha
        exact hcomm j i (Ne.symm hij) a ha b hb
      refine (relIndex_sup_dvd_of_commute (A := L j) (B := ⨆ i ∈ s, L i) ?_ (hle j)
        (iSup₂_mono fun i _ => hle i)).trans (mul_dvd_mul_left _ ih)
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.1 (hcen hb)) a ha
  have := key Finset.univ
  simpa using this

theorem eq_bot_of_perfect_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) {K : Subgroup G}
    (hK : ⁅K, K⁆ = K) (hpg : IsPGroup p ↥K) : K = ⊥ := by
  have := Fact.mk hp
  by_contra hne
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hne
  have : Group.IsNilpotent ↥K := hpg.isNilpotent
  have h1 : commutator ↥K = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hK)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K).ne h1

theorem eq_one_of_commute_inner {L : Type*} [Group L] (hL : Group.IsPerfect L) (β : MulAut L)
    (h : ∀ x : L, β * MulAut.conj x = MulAut.conj x * β) : β = 1 := by
  have hc : ∀ x y : L, (β x)⁻¹ * x * y = y * ((β x)⁻¹ * x) := by
    intro x y
    have h1 := congrArg (fun γ : MulAut L => γ (β.symm y)) (h x)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
      at h1
    calc (β x)⁻¹ * x * y = (β x)⁻¹ * (x * y * x⁻¹) * x := by group
      _ = (β x)⁻¹ * (β x * y * (β x)⁻¹) * x := by rw [h1]
      _ = y * ((β x)⁻¹ * x) := by group
  let f : L →* L := MonoidHom.mk' (fun x => (β x)⁻¹ * x) fun x y => by
    have h2 := hc x (β y)⁻¹
    show (β (x * y))⁻¹ * (x * y) = (β x)⁻¹ * x * ((β y)⁻¹ * y)
    rw [map_mul, mul_inv_rev]
    calc (β y)⁻¹ * (β x)⁻¹ * (x * y) = (β y)⁻¹ * ((β x)⁻¹ * x) * y := by group
      _ = ((β x)⁻¹ * x) * (β y)⁻¹ * y := by rw [← h2]
      _ = ((β x)⁻¹ * x) * ((β y)⁻¹ * y) := by group
  have hf : ∀ x, f x = (β x)⁻¹ * x := fun x => rfl
  have hker : commutator L ≤ f.ker := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hf a,
      hf b]
    exact hc a _
  have htop : commutator L = ⊤ := Group.isPerfect_def.1 hL
  ext x
  have : x ∈ f.ker := hker (by rw [htop]; exact Subgroup.mem_top x)
  rw [MonoidHom.mem_ker, hf] at this
  have h3 : β x = x := by
    exact inv_mul_eq_one.1 this
  simpa using h3

theorem conj_eq_one_iff {L : Type*} [Group L] (x : L) :
    MulAut.conj x = 1 ↔ x ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun γ : MulAut L => γ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = x * g * x⁻¹ * x := by rw [this]
      _ = x * g := by group
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g]
    group

end CFSG.QuasithinUnique.Setup.Layer
