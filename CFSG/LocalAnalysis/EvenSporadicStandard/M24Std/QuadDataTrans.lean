module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

@[expose] def qdFix (s : S24) : ℕ :=
  (Finset.univ.filter fun i : Fin 24 => (s : Equiv.Perm (Fin 24)) i = i).card

theorem qdFix_conj (g s : S24) : qdFix (g * s * g⁻¹) = qdFix s := by
  unfold qdFix
  refine Finset.card_equiv (((g : Equiv.Perm (Fin 24)))⁻¹) fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : ((g * s * g⁻¹ : S24) : Equiv.Perm (Fin 24)) i =
      (g : Equiv.Perm (Fin 24)) ((s : Equiv.Perm (Fin 24)) ((g : Equiv.Perm (Fin 24))⁻¹ i)) := rfl
  rw [h1]
  constructor
  · intro h
    simpa using congrArg (fun j => ((g : Equiv.Perm (Fin 24)))⁻¹ j) h
  · intro h
    rw [h]
    simp

@[expose] def QdNorm (g : S24) : Prop := ∀ s, s ∈ m24E1l ↔ g * s * g⁻¹ ∈ m24E1l

@[expose] def QdNormChk (g : S24) : Prop :=
  ∀ x ∈ m24E1l, g * x * g⁻¹ ∈ m24E1l ∧ g⁻¹ * x * g ∈ m24E1l

instance (g : S24) : Decidable (QdNormChk g) := by
  unfold QdNormChk
  infer_instance

theorem QdNormChk.norm {g : S24} (h : QdNormChk g) : QdNorm g := fun s =>
  ⟨fun hs => (h s hs).1, fun hs => by
    have h2 := (h _ hs).2
    have h3 : g⁻¹ * (g * s * g⁻¹) * g = s := by group
    rwa [h3] at h2⟩

theorem QdNorm.mul {g h : S24} (hg : QdNorm g) (hh : QdNorm h) : QdNorm (g * h) := fun s => by
  have h3 : g * h * s * (g * h)⁻¹ = g * (h * s * h⁻¹) * g⁻¹ := by group
  rw [hh s, hg (h * s * h⁻¹), ← h3]

@[expose] def qdStep (gs l : List S24) : List S24 :=
  (l ++ gs.flatMap fun g => l.map fun x => normH NativeSporadic.M24 (g * x * g⁻¹)).dedup

@[expose] def qdReach (gs : List S24) (a : S24) : ℕ → List S24
  | 0 => [a]
  | n + 1 => qdStep gs (qdReach gs a n)

theorem mem_qdReach {P : S24 → Prop} {gs : List S24} {a : S24} (ha : P a)
    (hg : ∀ g ∈ gs, ∀ x, P x → P (g * x * g⁻¹)) :
    ∀ (n : ℕ) {x : S24}, x ∈ qdReach gs a n → P x
  | 0, x, hx => by
    simp only [qdReach, List.mem_singleton] at hx
    rw [hx]
    exact ha
  | n + 1, x, hx => by
    simp only [qdReach, qdStep, List.mem_dedup, List.mem_append, List.mem_flatMap,
      List.mem_map] at hx
    rcases hx with hx | ⟨g, hg', y, hy, rfl⟩
    · exact mem_qdReach ha hg n hx
    · rw [normH_eq]
      exact hg g hg' y (mem_qdReach ha hg n hy)

theorem exists_norm_of_mem_qdReach {gs : List S24} (hgs : ∀ g ∈ gs, QdNorm g) {a x : S24} {n : ℕ}
    (hx : x ∈ qdReach gs a n) : ∃ m, QdNorm m ∧ m * a * m⁻¹ = x := by
  refine mem_qdReach (P := fun x => ∃ m, QdNorm m ∧ m * a * m⁻¹ = x) ⟨1, fun s => by simp, by simp⟩
    ?_ n hx
  rintro g hg x ⟨m, hm, rfl⟩
  exact ⟨g * m, (hgs g hg).mul hm, by group⟩

section Transport

variable {G : Type} [Group G] {L A : Subgroup G}

@[expose] def qdIota (e : L ≃* S24) : S24 →* G := L.subtype.comp e.symm.toMonoidHom

theorem qdIota_injective (e : L ≃* S24) : Function.Injective (qdIota e) :=
  Subtype.val_injective.comp e.symm.injective

theorem qdIota_mem (e : L ≃* S24) (s : S24) : qdIota e s ∈ L := (e.symm s).2

@[simp] theorem qdIota_apply (e : L ≃* S24) (x : L) : qdIota e (e x) = x := by
  simp [qdIota]

theorem qdIota_conj (e : L ≃* S24) (g t : S24) :
    qdIota e g * qdIota e t * (qdIota e g)⁻¹ = qdIota e (g * t * g⁻¹) := by
  simp [map_mul, map_inv]

section Pinned

variable (e : L ≃* S24) (hAL : A ≤ L) (hA : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l)
include hA

theorem qdIota_mem_A (s : S24) : qdIota e s ∈ A ↔ s ∈ m24E1l := by
  simpa [qdIota] using hA (e.symm s)

include hAL

theorem qdMem_A_iff (y : G) : y ∈ A ↔ ∃ s ∈ m24E1l, qdIota e s = y := by
  constructor
  · intro hy
    exact ⟨e ⟨y, hAL hy⟩, (hA ⟨y, hAL hy⟩).1 hy, by simp⟩
  · rintro ⟨s, hs, rfl⟩
    exact (qdIota_mem_A e hA s).2 hs

theorem qdIota_mem_egNL {g : S24} (hg : QdNorm g) : qdIota e g ∈ egNL L A := by
  refine mem_inf.2 ⟨?_, qdIota_mem e g⟩
  rw [mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ L
  · obtain ⟨s, rfl⟩ : ∃ s : S24, qdIota e s = y := ⟨e ⟨y, hy⟩, by simp⟩
    rw [qdIota_conj, qdIota_mem_A e hA, qdIota_mem_A e hA]
    exact hg s
  · have h1 : y ∉ A := fun h => hy (hAL h)
    have h2 : qdIota e g * y * (qdIota e g)⁻¹ ∉ A := by
      intro h
      apply hy
      have h3 := L.mul_mem (L.mul_mem (L.inv_mem (qdIota_mem e g)) (hAL h)) (qdIota_mem e g)
      have h4 : (qdIota e g)⁻¹ * (qdIota e g * y * (qdIota e g)⁻¹) * qdIota e g = y := by group
      rwa [h4] at h3
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

omit hAL in
theorem qdExists_norm_of_mem_egNL {n : G} (hn : n ∈ egNL L A) :
    ∃ g : S24, QdNorm g ∧ qdIota e g = n := by
  have hnL : n ∈ L := (mem_inf.1 hn).2
  have hnN : n ∈ normalizer (A : Set G) := (mem_inf.1 hn).1
  have hgn : qdIota e (e ⟨n, hnL⟩) = n := by simp
  refine ⟨e ⟨n, hnL⟩, fun s => ?_, hgn⟩
  have h1 := mem_normalizer_iff.1 hnN (qdIota e s)
  rw [← qdIota_mem_A e hA s, ← qdIota_mem_A e hA (e ⟨n, hnL⟩ * s * (e ⟨n, hnL⟩)⁻¹),
    ← qdIota_conj, hgn]
  exact h1

end Pinned

end Transport

end CFSG.EvenSporadicStandard.M24Std
