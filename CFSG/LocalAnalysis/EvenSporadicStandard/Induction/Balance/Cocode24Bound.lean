module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Octad
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

structure PinStep where
  pt : Fin 24
  octs : List (List (Fin 24))

@[expose] def PinStep.target (Fx : Finset (Fin 24)) (st : PinStep) : Finset (Fin 24) :=
  Finset.univ.filter fun q => q ∉ Fx ∧ ∀ O ∈ st.octs, (q ∈ O ↔ st.pt ∈ O)

@[expose] def PinStep.ok (Fx : Finset (Fin 24)) (st : PinStep) : Prop :=
  st.pt ∉ Fx ∧ ∀ O ∈ st.octs, IsOctad O.toFinset ∧ 5 ≤ (O.toFinset ∩ Fx).card

instance (Fx : Finset (Fin 24)) (st : PinStep) : Decidable (st.ok Fx) := by
  unfold PinStep.ok
  infer_instance

@[expose] def chainOK : Finset (Fin 24) → List PinStep → Prop
  | Fx, [] => Fx = Finset.univ
  | Fx, st :: rest => st.ok Fx ∧ chainOK (insert st.pt Fx) rest

instance chainOK.decidable : ∀ (Fx : Finset (Fin 24)) (steps : List PinStep),
    Decidable (chainOK Fx steps)
  | Fx, [] => by
    unfold chainOK
    infer_instance
  | Fx, st :: rest => by
    unfold chainOK
    haveI := chainOK.decidable (insert st.pt Fx) rest
    infer_instance

@[expose] def chainBound : Finset (Fin 24) → List PinStep → ℕ
  | _, [] => 1
  | Fx, st :: rest => (st.target Fx).card * chainBound (insert st.pt Fx) rest

theorem card_le_mul_stabilizer (G : Subgroup (Perm (Fin 24))) (x : Fin 24) (D : Finset (Fin 24))
    (hD : ∀ σ ∈ G, σ x ∈ D) :
    Nat.card G ≤ D.card *
      Nat.card ↥(G ⊓ MulAction.stabilizer (Perm (Fin 24)) x : Subgroup (Perm (Fin 24))) := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (↥G) x)
  rw [Nat.card_prod] at h
  have hs : Nat.card ↥(MulAction.stabilizer ↥G x) =
      Nat.card ↥(G ⊓ MulAction.stabilizer (Perm (Fin 24)) x : Subgroup (Perm (Fin 24))) :=
    Nat.card_congr
      { toFun := fun σ => ⟨σ.1.1, σ.1.2, σ.2⟩
        invFun := fun σ => ⟨⟨σ.1, σ.2.1⟩, σ.2.2⟩
        left_inv := fun σ => rfl
        right_inv := fun σ => rfl }
  have ho : Nat.card ↥(MulAction.orbit ↥G x) ≤ D.card := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset D]
    refine Set.ncard_le_ncard (fun y hy => ?_) D.finite_toSet
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hy
    exact hD g.1 g.2
  rw [← h, hs]
  exact Nat.mul_le_mul_right _ ho

theorem pin {σ : Perm (Fin 24)} (hσ : σ ∈ aut) {Fx : Finset (Fin 24)}
    (hfix : ∀ x ∈ Fx, σ x = x) {st : PinStep} (hok : st.ok Fx) : σ st.pt ∈ st.target Fx := by
  obtain ⟨hpt, hocts⟩ := hok
  have hinv : ∀ O ∈ st.octs, O.toFinset.image σ = O.toFinset := by
    intro O hO
    obtain ⟨hOct, h5⟩ := hocts O hO
    exact image_eq_of_five hσ hOct (Finset.inter_subset_left) h5
      (fun x hx => hfix x (Finset.mem_inter.1 hx).2)
  have hnot : σ st.pt ∉ Fx := by
    intro h
    have h1 := hfix _ h
    exact hpt (by rwa [σ.injective h1] at h)
  rw [PinStep.target, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hnot, fun O hO => ?_⟩
  have h2 := hinv O hO
  have key : σ st.pt ∈ O.toFinset ↔ st.pt ∈ O.toFinset := by
    constructor
    · intro h
      rw [← h2, Finset.mem_image] at h
      obtain ⟨a, ha, hσa⟩ := h
      rwa [← σ.injective hσa]
    · intro h
      rw [← h2]
      exact Finset.mem_image_of_mem _ h
  simpa only [List.mem_toFinset] using key

theorem card_le_chainBound : ∀ (steps : List PinStep) (Fx : Finset (Fin 24)), chainOK Fx steps →
    Nat.card ↥(aut ⊓ fixingSubgroup (Perm (Fin 24)) (↑Fx : Set (Fin 24)) :
      Subgroup (Perm (Fin 24))) ≤ chainBound Fx steps := by
  intro steps
  induction steps with
  | nil =>
    intro Fx hFx
    rw [chainOK] at hFx
    subst hFx
    rw [chainBound]
    refine (Finite.card_le_one_iff_subsingleton).2 ⟨fun σ τ => ?_⟩
    apply Subtype.ext
    have h1 := (mem_fixingSubgroup_iff _).1 (Subgroup.mem_inf.1 σ.2).2
    have h2 := (mem_fixingSubgroup_iff _).1 (Subgroup.mem_inf.1 τ.2).2
    ext i
    have := h1 i (by simp)
    have := h2 i (by simp)
    simp_all
  | cons st rest ih =>
    intro Fx hFx
    rw [chainOK] at hFx
    obtain ⟨hok, hrest⟩ := hFx
    have hstep := card_le_mul_stabilizer
      (aut ⊓ fixingSubgroup (Perm (Fin 24)) (↑Fx : Set (Fin 24))) st.pt (st.target Fx)
      (fun σ hσ => by
        obtain ⟨hσ1, hσ2⟩ := Subgroup.mem_inf.1 hσ
        exact pin hσ1 (fun x hx => by simpa using (mem_fixingSubgroup_iff _).1 hσ2 x hx) hok)
    have heq : (aut ⊓ fixingSubgroup (Perm (Fin 24)) (↑Fx : Set (Fin 24))) ⊓
        MulAction.stabilizer (Perm (Fin 24)) st.pt =
        aut ⊓ fixingSubgroup (Perm (Fin 24)) (↑(insert st.pt Fx) : Set (Fin 24)) := by
      ext σ
      simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, mem_fixingSubgroup_iff,
        Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h3, h2⟩
      · rintro ⟨h1, h3, h2⟩
        exact ⟨⟨h1, h2⟩, h3⟩
    rw [heq] at hstep
    have := ih (insert st.pt Fx) hrest
    rw [chainBound]
    calc _ ≤ _ := hstep
      _ ≤ _ := Nat.mul_le_mul_left _ this

@[expose] def steps24 : List PinStep := [
  ⟨0, []⟩,
  ⟨1, []⟩,
  ⟨2, []⟩,
  ⟨3, []⟩,
  ⟨4, []⟩,
  ⟨5, [[0, 1, 2, 3, 4, 10, 16, 23]]⟩,
  ⟨11, [[0, 1, 2, 3, 5, 11, 17, 22]]⟩,
  ⟨6, [[0, 1, 3, 4, 6, 11, 12, 20],
    [2, 3, 4, 5, 10, 11, 20, 21],
    [1, 2, 4, 5, 11, 12, 15, 23]]⟩,
  ⟨7, [[2, 3, 4, 6, 7, 11, 17, 23],
    [0, 2, 3, 5, 6, 15, 20, 23],
    [0, 1, 4, 5, 6, 7, 22, 23]]⟩,
  ⟨8, [[0, 2, 5, 7, 9, 10, 11, 23],
    [0, 3, 4, 5, 11, 13, 14, 23],
    [1, 2, 4, 5, 11, 12, 15, 23],
    [0, 1, 2, 3, 4, 10, 16, 23],
    [2, 3, 4, 6, 7, 11, 17, 23],
    [0, 1, 3, 7, 11, 15, 18, 23],
    [0, 1, 2, 6, 11, 14, 19, 23],
    [0, 2, 3, 5, 6, 15, 20, 23],
    [1, 2, 3, 5, 7, 14, 21, 23],
    [0, 1, 4, 5, 6, 7, 22, 23]]⟩,
  ⟨9, [[2, 3, 4, 5, 8, 9, 22, 23],
    [1, 2, 7, 8, 11, 16, 22, 23]]⟩,
  ⟨10, [[1, 2, 5, 6, 9, 16, 17, 23],
    [1, 2, 3, 9, 11, 13, 20, 23],
    [1, 5, 7, 8, 9, 15, 20, 23],
    [4, 5, 6, 9, 11, 19, 20, 23],
    [1, 6, 7, 9, 11, 12, 21, 23],
    [0, 5, 6, 8, 9, 14, 21, 23],
    [4, 5, 7, 8, 11, 18, 21, 23],
    [0, 3, 6, 9, 11, 16, 22, 23]]⟩,
  ⟨12, [[1, 4, 5, 9, 10, 13, 21, 23],
    [0, 5, 6, 8, 9, 14, 21, 23],
    [0, 4, 6, 10, 11, 15, 21, 23],
    [4, 5, 7, 8, 11, 18, 21, 23],
    [2, 3, 6, 9, 10, 19, 21, 23],
    [0, 3, 4, 7, 9, 20, 21, 23],
    [0, 3, 6, 9, 11, 16, 22, 23],
    [1, 3, 7, 9, 10, 17, 22, 23]]⟩,
  ⟨13, [[0, 1, 10, 11, 12, 13, 22, 23],
    [2, 4, 7, 10, 12, 21, 22, 23]]⟩,
  ⟨14, [[4, 7, 9, 11, 13, 15, 22, 23],
    [0, 3, 6, 9, 11, 16, 22, 23],
    [1, 3, 7, 9, 10, 17, 22, 23],
    [0, 7, 8, 9, 12, 18, 22, 23],
    [1, 6, 8, 9, 13, 19, 22, 23],
    [3, 4, 6, 10, 13, 20, 22, 23],
    [2, 5, 6, 11, 13, 21, 22, 23]]⟩,
  ⟨15, [[0, 2, 5, 12, 14, 16, 22, 23],
    [1, 2, 4, 13, 14, 17, 22, 23],
    [1, 5, 9, 11, 14, 18, 22, 23],
    [0, 4, 9, 10, 14, 19, 22, 23],
    [2, 6, 7, 9, 14, 20, 22, 23],
    [3, 9, 12, 13, 14, 21, 22, 23]]⟩,
  ⟨16, [[0, 3, 4, 12, 15, 17, 22, 23],
    [0, 6, 13, 14, 15, 18, 22, 23],
    [1, 7, 12, 14, 15, 19, 22, 23],
    [2, 8, 12, 13, 15, 20, 22, 23],
    [0, 1, 2, 9, 15, 21, 22, 23]]⟩,
  ⟨17, [[3, 4, 7, 14, 16, 18, 22, 23],
    [2, 4, 6, 15, 16, 19, 22, 23],
    [0, 7, 10, 15, 16, 20, 22, 23],
    [1, 6, 10, 14, 16, 21, 22, 23]]⟩,
  ⟨18, [[3, 5, 6, 14, 17, 19, 22, 23],
    [1, 6, 11, 15, 17, 20, 22, 23],
    [0, 7, 11, 14, 17, 21, 22, 23]]⟩,
  ⟨19, [[10, 12, 14, 17, 18, 20, 22, 23],
    [4, 6, 9, 17, 18, 21, 22, 23]]⟩,
  ⟨20, [[2, 8, 14, 18, 19, 21, 22, 23]]⟩,
  ⟨21, [[3, 9, 15, 18, 19, 20, 22, 23]]⟩,
  ⟨22, [[4, 10, 16, 18, 19, 20, 21, 23]]⟩,
  ⟨23, []⟩]

theorem chainOK_steps24 : chainOK ∅ steps24 := by decide

theorem chainBound_steps24 : chainBound ∅ steps24 = 244823040 := by decide

theorem card_aut_le : Nat.card aut ≤ 244823040 := by
  have h := card_le_chainBound steps24 ∅ chainOK_steps24
  rw [chainBound_steps24] at h
  have heq : (aut ⊓ fixingSubgroup (Perm (Fin 24))
      (↑(∅ : Finset (Fin 24)) : Set (Fin 24)) : Subgroup (Perm (Fin 24))) = aut := by
    ext σ
    simp
  rwa [heq] at h

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
