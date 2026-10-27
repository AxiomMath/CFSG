module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

theorem card_closure_le_pow_two {G : Type*} [Group G] [Finite G] (s : Finset G)
    (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hsq : ∀ x ∈ s, x * x = 1) :
    Nat.card ↥(Subgroup.closure (s : Set G)) ≤ 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hc' : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := fun x hx y hy =>
      hc x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
    have hsq' : ∀ x ∈ s, x * x = 1 := fun x hx => hsq x (Finset.mem_insert_of_mem hx)
    have ih' := ih hc' hsq'
    have hcent : Subgroup.closure (s : Set G) ≤
        Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hay : Commute a y :=
        hc a (Finset.mem_insert_self a s) y (Finset.mem_insert_of_mem (Finset.mem_coe.mp hy))
      exact (hay.zpow_left n).eq
    have hle : Subgroup.closure (s : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
      hcent.trans (Subgroup.centralizer_le_normalizer _)
    have hins : Subgroup.closure ((insert a s : Finset G) : Set G) =
        Subgroup.closure (s : Set G) ⊔ Subgroup.zpowers a := by
      rw [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, sup_comm,
        ← Subgroup.zpowers_eq_closure]
    have hmul := Set.natCard_mul_le (s := (Subgroup.closure (s : Set G) : Set G))
      (t := (Subgroup.zpowers a : Set G))
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hmul
    have hB : Nat.card (Subgroup.zpowers a) ≤ 2 := by
      rw [Nat.card_zpowers]
      refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
      rw [pow_two]
      exact hsq a (Finset.mem_insert_self a s)
    rw [Finset.card_insert_of_notMem ha, pow_succ, hins]
    exact hmul.trans (Nat.mul_le_mul ih' hB)

theorem not_closure_of_card_gt {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) (k : ℕ)
    (hE : 2 ^ k < Nat.card E) :
    ¬ ∃ s : Finset G, s.card ≤ k ∧ Subgroup.closure (s : Set G) = E := by
  rintro ⟨s, hs, hsE⟩
  have hsub : ∀ x ∈ s, x ∈ E := fun x hx => by
    rw [← hsE]
    exact Subgroup.subset_closure (Finset.mem_coe.mpr hx)
  have h1 := card_closure_le_pow_two s
    (fun x hx y hy => hc x (hsub x hx) y (hsub y hy)) (fun x hx => hsq x (hsub x hx))
  rw [hsE] at h1
  have h2 : 2 ^ s.card ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hs
  omega

theorem conjNormal_injective_of_centralizer_eq_bot {N : Type} [Group N] {K : Subgroup N}
    [K.Normal] (hc : centralizer (K : Set N) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := K) : N →* MulAut ↥K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hg' : g ∈ centralizer (K : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have key := congrArg (fun φ : MulAut ↥K => ((φ ⟨h, hh⟩ : ↥K) : N)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at key
    calc h * g = g * h * g⁻¹ * g := by rw [key]
      _ = g * h := by group
  rw [hc] at hg'
  exact hg'

theorem card_dvd_mulAut {N : Type} [Group N] [Finite N] {K : Subgroup N} [K.Normal]
    (hc : centralizer (K : Set N) = ⊥) : Nat.card N ∣ Nat.card (MulAut ↥K) :=
  Subgroup.card_dvd_of_injective _ (conjNormal_injective_of_centralizer_eq_bot hc)

theorem le_of_card_aut {N : Type} [Group N] [Finite N] {K X : Subgroup N} [K.Normal]
    (hc : centralizer (K : Set N) = ⊥) (hXs : IsSimpleGroup ↥X) (hX60 : Nat.card X = 60)
    {m : ℕ} (hm : Nat.card (MulAut ↥K) = m * Nat.card K) (h60 : ¬ 60 ∣ m) : X ≤ K := by
  by_contra hXK
  have : (K.subgroupOf X).Normal := Subgroup.Normal.subgroupOf inferInstance X
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf X) with h | h
  · have hd : Disjoint K X := Subgroup.subgroupOf_eq_bot.1 h
    have hinf : K ⊓ X = ⊥ := disjoint_iff.1 hd
    have h1 : K.relIndex X * Nat.card (K ⊓ X :) = Nat.card X :=
      Subgroup.relIndex_mul_card K X
    rw [hinf, Subgroup.card_bot, mul_one, hX60] at h1
    have h2 : K.relIndex (X ⊔ K) * Nat.card (K ⊓ (X ⊔ K) :) = Nat.card (X ⊔ K :) :=
      Subgroup.relIndex_mul_card K (X ⊔ K)
    rw [inf_of_le_left le_sup_right, Subgroup.relIndex_sup_right, h1] at h2
    have h3 : Nat.card (X ⊔ K :) ∣ Nat.card N := Subgroup.card_subgroup_dvd_card _
    have h4 := card_dvd_mulAut hc
    rw [hm] at h4
    rw [← h2] at h3
    have h5 : 60 * Nat.card K ∣ m * Nat.card K := h3.trans h4
    have hKpos : 0 < Nat.card K := Nat.card_pos
    exact h60 (Nat.dvd_of_mul_dvd_mul_right hKpos h5)
  · exact hXK (Subgroup.subgroupOf_eq_top.1 h)

theorem exists_embedding_perm {N : Type} [Group N] [Finite N] {K : Subgroup N} [K.Normal]
    (hc : centralizer (K : Set N) = ⊥) (n : ℕ) (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : ↥K ≃* alternatingGroup (Fin n)) :
    ∃ ψ : N →* Equiv.Perm (Fin n), Function.Injective ψ ∧
      ∀ k : ↥K, ψ (k : N) = ((e k : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  let θ : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective _ hbij
  have hθ : ∀ (σ : Equiv.Perm (Fin n)) (x : alternatingGroup (Fin n)),
      ((θ σ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = σ * x * σ⁻¹ := fun σ x => rfl
  let ψ : N →* Equiv.Perm (Fin n) :=
    θ.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)
  have hinj : Function.Injective ψ :=
    θ.symm.injective.comp ((MulAut.congr e).injective.comp
      (conjNormal_injective_of_centralizer_eq_bot hc))
  refine ⟨ψ, hinj, ?_⟩
  intro k
  apply θ.injective
  have h1 : θ (ψ (k : N)) = MulAut.congr e (MulAut.conjNormal (k : N)) :=
    θ.apply_symm_apply _
  rw [h1, MulAut.conjNormal_val]
  refine MulEquiv.ext fun x => ?_
  have hL : (MulAut.congr e (MulAut.conj k)) x = e k * x * (e k)⁻¹ := by
    simp [MulAut.congr_apply]
  rw [hL]
  apply Subtype.ext
  rw [hθ]
  simp

end CFSG.OddStandard.Seitz77
