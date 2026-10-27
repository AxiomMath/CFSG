module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Sp43

open Subgroup

@[expose] def GenProp (X : Type*) [Group X] : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → q ≠ 3 → ∀ (D : Sylow q X) (P : Sylow 3 X),
    (D : Subgroup X) ≠ ⊥ → normalizer (D : Set X) ⊔ normalizer (P : Set X) = ⊤

theorem genProp_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite Y] (e : X ≃* Y)
    (h : GenProp X) : GenProp Y := by
  intro q _ hq2 hq3 D P hD
  let D' : Sylow q X := D.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let P' : Sylow 3 X := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcD : (D' : Subgroup X) = (D : Subgroup Y).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ D
  have hcP : (P' : Subgroup X) = (P : Subgroup Y).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ P
  have hD' : (D' : Subgroup X) ≠ ⊥ := by
    intro h0
    apply hD
    rw [hcD] at h0
    exact (map_eq_bot_iff_of_injective _ e.symm.injective).1 h0
  have key : normalizer (((D' : Subgroup X)) : Set X) ⊔
      normalizer (((P' : Subgroup X)) : Set X) = ⊤ := h q hq2 hq3 D' P' hD'
  rw [hcD, hcP] at key
  show normalizer (((D : Subgroup Y)) : Set Y) ⊔ normalizer (((P : Subgroup Y)) : Set Y) = ⊤
  have hN : ∀ H : Subgroup Y, normalizer (((H.map e.symm.toMonoidHom : Subgroup X)) : Set X) =
      (normalizer (H : Set Y)).map e.symm.toMonoidHom := fun H =>
    (map_equiv_normalizer_eq H e.symm).symm
  rw [hN, hN, ← Subgroup.map_sup] at key
  have := congrArg (fun K : Subgroup X => K.map e.toMonoidHom) key
  simp only [map_map] at this
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext; simp
  rw [hid, map_id, map_top_of_surjective _ e.surjective] at this
  exact this

private theorem card_sylow_eq_relIndex {W : Type*} [Group W] [Finite W] {p : ℕ} [Fact p.Prime]
    (S : Sylow p W) {M : Subgroup W} (hM : normalizer (S : Set W) ≤ M) :
    Nat.card (Sylow p M) = (normalizer (S : Set W)).relIndex M := by
  have hSM : (S : Subgroup W) ≤ M := le_normalizer.trans hM
  rw [Sylow.card_eq_index_normalizer (S.subtype hSM), Subgroup.relIndex]
  show (normalizer (((S.subtype hSM : Sylow p M) : Subgroup M) : Set M)).index = _
  rw [Sylow.coe_subtype, ← Subgroup.subgroupOf_normalizer_eq hSM]
  rfl

theorem index_mod_of_normalizer_le {W : Type*} [Group W] [Finite W] {p : ℕ} [Fact p.Prime]
    (S : Sylow p W) {M : Subgroup W} (hM : normalizer (S : Set W) ≤ M) :
    M.index ≡ 1 [MOD p] := by
  have h1 := card_sylow_modEq_one p W
  have h2 := card_sylow_modEq_one p M
  rw [card_sylow_eq_relIndex S hM] at h2
  rw [Sylow.card_eq_index_normalizer S, ← Subgroup.relIndex_mul_index hM] at h1
  have h3 := Nat.ModEq.mul_right M.index h2
  rw [one_mul] at h3
  exact h3.symm.trans h1

theorem index_sup_normalizer_eq {W : Type*} [Group W] [Finite W]
    (hW : Nat.card W ∣ 2 ^ 7 * 3 ^ 4 * 5) (D : Sylow 5 W) (P : Sylow 3 W) :
    (normalizer (D : Set W) ⊔ normalizer (P : Set W)).index = 1 ∨
      (normalizer (D : Set W) ⊔ normalizer (P : Set W)).index = 16 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := normalizer (D : Set W) ⊔ normalizer (P : Set W)
  have h5 := index_mod_of_normalizer_le D (le_sup_left : normalizer (D : Set W) ≤ M)
  have h3 := index_mod_of_normalizer_le P (le_sup_right : normalizer (P : Set W) ≤ M)
  have hk : M.index ∣ 2 ^ 7 * 3 ^ 4 * 5 := (Subgroup.index_dvd_card M).trans hW
  have hc5 : Nat.Coprime M.index 5 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    intro h
    have := (Nat.modEq_zero_iff_dvd.2 h).symm.trans h5
    simp [Nat.ModEq] at this
  have hc3 : Nat.Coprime M.index (3 ^ 4) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    have := (Nat.modEq_zero_iff_dvd.2 h).symm.trans h3
    simp [Nat.ModEq] at this
  have h2 : M.index ∣ 2 ^ 7 := hc3.dvd_of_dvd_mul_right (hc5.dvd_of_dvd_mul_right hk)
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have h15 : M.index % 15 = 1 := by
    have e5 : M.index % 5 = 1 := h5
    have e3 : M.index % 3 = 1 := h3
    omega
  rw [hjk] at h15 ⊢
  interval_cases j <;> simp_all

theorem genProp_of_index_ne {X : Type*} [Group X] [Finite X]
    (hX : Nat.card X ∣ 2 ^ 7 * 3 ^ 4 * 5)
    (h : ∀ (D : Sylow 5 X) (P : Sylow 3 X),
      (normalizer (D : Set X) ⊔ normalizer (P : Set X)).index ≠ 16) :
    GenProp X := by
  intro q hqp hq2 hq3 D P hD
  have hq : q.Prime := hqp.out
  have hdvd : q ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := (D.isPGroup').exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hD (Subgroup.card_eq_one.1 (by simpa using hk))
    exact (dvd_pow_self q hk0).trans (hk ▸ Subgroup.card_subgroup_dvd_card _)
  have hq5 : q = 5 := by
    have h' := hdvd.trans hX
    rcases (Nat.Prime.dvd_mul hq).1 h' with h' | h'
    · rcases (Nat.Prime.dvd_mul hq).1 h' with h' | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
          (hq.dvd_of_dvd_pow h')) hq2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
          (hq.dvd_of_dvd_pow h')) hq3
    · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1 h'
  subst hq5
  rcases index_sup_normalizer_eq hX D P with h1 | h16
  · exact Subgroup.index_eq_one.1 h1
  · exact absurd h16 (h D P)

theorem index_ne_of_not_dvd_card {X : Type*} [Group X] [Finite X]
    (h : ¬ 16 ∣ Nat.card X) (D : Sylow 5 X) (P : Sylow 3 X) :
    (normalizer (D : Set X) ⊔ normalizer (P : Set X)).index ≠ 16 := fun h16 =>
  h (h16 ▸ Subgroup.index_dvd_card _)

private theorem index_ne_of_index_normalizer {X : Type*} [Group X] [Finite X]
    (D : Sylow 5 X) (P : Sylow 3 X) (h : ¬ 16 ∣ (normalizer (P : Set X)).index) :
    (normalizer (D : Set X) ⊔ normalizer (P : Set X)).index ≠ 16 := fun h16 =>
  h (h16 ▸ Subgroup.index_dvd_of_le le_sup_right)

theorem index_ne_of_center {X : Type*} [Group X] [Finite X] {z : X}
    (hz : z ∈ center X) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (h : ¬ 32 ∣ Nat.card X)
    (D : Sylow 5 X) (P : Sylow 3 X) :
    (normalizer (D : Set X) ⊔ normalizer (P : Set X)).index ≠ 16 := by
  apply index_ne_of_index_normalizer D P
  intro h16
  have hzN : z ∈ normalizer (P : Set X) := center_le_normalizer (P : Set X) hz
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have h2 : 2 ∣ Nat.card (normalizer (P : Set X)) := by
    rw [← hord]
    have := Subgroup.orderOf_dvd_natCard (normalizer (P : Set X)) hzN
    exact this
  apply h
  rw [← Subgroup.card_mul_index (normalizer (P : Set X))]
  exact (show 32 = 2 * 16 by norm_num) ▸ Nat.mul_dvd_mul h2 h16

theorem index_ne_of_dvd_normalizer {X : Type*} [Group X] [Finite X]
    (hN : ∀ P : Sylow 3 X, 16 ∣ Nat.card (normalizer (P : Set X))) (h : ¬ 256 ∣ Nat.card X)
    (D : Sylow 5 X) (P : Sylow 3 X) :
    (normalizer (D : Set X) ⊔ normalizer (P : Set X)).index ≠ 16 := by
  apply index_ne_of_index_normalizer D P
  intro h16
  apply h
  rw [← Subgroup.card_mul_index (normalizer (P : Set X))]
  exact (show 256 = 16 * 16 by norm_num) ▸ Nat.mul_dvd_mul (hN P) h16

private theorem card_mul_le {X : Type*} [Group X] [Finite X] (H K : Subgroup X) :
    Nat.card H * Nat.card K ≤ Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) := by
  have hK : H.relIndex K * Nat.card ↥(H ⊓ K) = Nat.card K := Subgroup.relIndex_mul_card H K
  have hHK : H.relIndex (H ⊔ K) * Nat.card H = Nat.card ↥(H ⊔ K) := by
    have := Subgroup.relIndex_mul_card H (H ⊔ K)
    rwa [inf_of_le_left (le_sup_left : H ≤ H ⊔ K)] at this
  have hne : H.relIndex (H ⊔ K) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hHK
    exact Nat.card_pos.ne' hHK.symm
  have hle : H.relIndex K ≤ H.relIndex (H ⊔ K) :=
    Subgroup.relIndex_le_of_le_right le_sup_right hne
  rw [← hK, ← hHK]
  calc Nat.card H * (H.relIndex K * Nat.card ↥(H ⊓ K))
      = Nat.card ↥(H ⊓ K) * (Nat.card H * H.relIndex K) := by ring
    _ ≤ Nat.card ↥(H ⊓ K) * (Nat.card H * H.relIndex (H ⊔ K)) := by gcongr
    _ = H.relIndex (H ⊔ K) * Nat.card H * Nat.card ↥(H ⊓ K) := by ring

theorem index_ne_of_card_inf {X : Type*} [Group X] [Finite X] (D : Sylow 5 X) (P : Sylow 3 X)
    (h : Nat.card X * Nat.card ↥(normalizer (D : Set X) ⊓ normalizer (P : Set X)) <
      16 * (Nat.card (normalizer (D : Set X)) * Nat.card (normalizer (P : Set X)))) :
    (normalizer (D : Set X) ⊔ normalizer (P : Set X)).index ≠ 16 := by
  intro h16
  have hle := card_mul_le (normalizer (D : Set X)) (normalizer (P : Set X))
  have hX := Subgroup.card_mul_index (normalizer (D : Set X) ⊔ normalizer (P : Set X))
  rw [h16] at hX
  rw [← hX] at h
  nlinarith

private theorem sup_closure_insert' {G : Type*} [Group G] (K : Subgroup G) (a : G) (t : Set G) :
    K ⊔ Subgroup.closure (insert a t) = (K ⊔ Subgroup.closure t) ⊔ Subgroup.zpowers a := by
  rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure a,
    sup_comm (Subgroup.closure {a}) (Subgroup.closure t), ← sup_assoc]

theorem mem_of_join_closed_pElt {G : Type*} [Group G] [Finite G] {p : ℕ}
    (𝓜 : Set (Subgroup G))
    (hjoin : ∀ K ∈ 𝓜, ∀ σ : G, (∃ k, orderOf σ = p ^ k) → K ⊔ Subgroup.zpowers σ ∈ 𝓜)
    {W K₀ : Subgroup G} (hW : Subgroup.closure {x : G | x ∈ W ∧ ∃ k, orderOf x = p ^ k} = W)
    (hK₀ : K₀ ∈ 𝓜) (h0 : K₀ ≤ W) : W ∈ 𝓜 := by
  classical
  have := Fintype.ofFinite G
  set S : Set G := {x : G | x ∈ W ∧ ∃ k, orderOf x = p ^ k}
  have key : ∀ t : Finset G, ((t : Set G) ⊆ S) → K₀ ⊔ Subgroup.closure (t : Set G) ∈ 𝓜 := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      simpa using hK₀
    · intro a t _ ih hsub
      rw [Finset.coe_insert] at hsub
      have haS : a ∈ S := hsub (Set.mem_insert a (t : Set G))
      have htS : (t : Set G) ⊆ S := fun x hx => hsub (Set.mem_insert_of_mem a hx)
      rw [Finset.coe_insert, sup_closure_insert']
      exact hjoin _ (ih htS) a haS.2
  have hfin : ((Finset.univ.filter (· ∈ S) : Finset G) : Set G) = S := by
    ext x
    simp
  have hkey := key (Finset.univ.filter (· ∈ S)) (by rw [hfin])
  rw [hfin, hW, sup_eq_right.2 h0] at hkey
  exact hkey

end CFSG.Sp43
