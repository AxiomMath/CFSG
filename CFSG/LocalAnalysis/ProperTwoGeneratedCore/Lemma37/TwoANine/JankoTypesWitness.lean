module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoLiftSubgroup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.Janko

open Equiv Subgroup

@[expose] def sbar₁ : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def ebar₂ : alternatingGroup (Fin 9) :=
  ⟨swap 3 4 * swap 4 5, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def ebar₃ : alternatingGroup (Fin 9) :=
  ⟨swap 6 7 * swap 7 8, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def sbar₂ : alternatingGroup (Fin 9) :=
  ⟨swap 3 4 * swap 4 5 * swap 6 7 * swap 7 8, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def sbar₃ : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 1 2 * swap 3 4 * swap 4 5 * swap 6 7 * swap 7 8,
    Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def tbar : alternatingGroup (Fin 9) :=
  ⟨swap 1 2 * swap 3 6 * swap 4 7 * swap 5 8, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def ℓbar : alternatingGroup (Fin 9) :=
  ⟨swap 3 6 * swap 4 8 * swap 8 5 * swap 5 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def ybar : alternatingGroup (Fin 9) :=
  ⟨swap 4 5 * swap 7 8, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def ρbar : alternatingGroup (Fin 9) :=
  ⟨swap 0 3 * swap 3 6 * swap 1 4 * swap 4 7 * swap 2 5 * swap 5 8,
    Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def bbar₁ : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 3 4 * swap 5 6 * swap 7 8, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def bbar₂ : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 3 6 * swap 4 8 * swap 5 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def bbar₃ : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 3 7 * swap 4 6 * swap 5 8, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def Ebar : Subgroup (alternatingGroup (Fin 9)) :=
  closure {sbar₁, ebar₂, ebar₃}

@[expose] def Pbar : Subgroup (alternatingGroup (Fin 9)) :=
  closure {sbar₁, ebar₂, ebar₃, ρbar}

@[expose] def Fbar : Subgroup (alternatingGroup (Fin 9)) :=
  fixingSubgroup (alternatingGroup (Fin 9)) ({0, 1, 2} : Set (Fin 9))

@[expose] def Kbar : Subgroup (alternatingGroup (Fin 9)) :=
  closure {tbar, ℓbar, ρbar}

theorem ℓbar_sq : ℓbar ^ 2 = ybar :=
  Subtype.ext (show (ℓbar : Perm (Fin 9)) ^ 2 = ybar by decide)

theorem mem_Fbar_iff {g : alternatingGroup (Fin 9)} :
    g ∈ Fbar ↔ (g : Perm (Fin 9)) 0 = 0 ∧ (g : Perm (Fin 9)) 1 = 1 ∧ (g : Perm (Fin 9)) 2 = 2 := by
  rw [Fbar, mem_fixingSubgroup_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rfl

section Lifts

variable {G : Type*} [Group G] {z : G}
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))

@[expose] noncomputable def s₁ : G :=
  (liftOdd e sbar₁ : centralizer ({z} : Set G))

@[expose] noncomputable def s₂ : G :=
  (liftOdd e sbar₂ : centralizer ({z} : Set G))

@[expose] noncomputable def s₃ : G :=
  (liftOdd e sbar₃ : centralizer ({z} : Set G))

@[expose] noncomputable def t : G :=
  (someLift e tbar : centralizer ({z} : Set G))

@[expose] noncomputable def ℓ : G :=
  (someLift e ℓbar : centralizer ({z} : Set G))

@[expose] noncomputable def E : Subgroup G :=
  (liftOddSubgroup e Ebar).map (centralizer ({z} : Set G)).subtype

@[expose] noncomputable def P : Subgroup G :=
  (liftOddSubgroup e Pbar).map (centralizer ({z} : Set G)).subtype

@[expose] noncomputable def F : Subgroup G :=
  (Fbar.comap (proj e)).map (centralizer ({z} : Set G)).subtype

@[expose] noncomputable def K : Subgroup G :=
  (Kbar.comap (proj e)).map (centralizer ({z} : Set G)).subtype

theorem s₁_mem : s₁ e ∈ centralizer ({z} : Set G) :=
  (liftOdd e sbar₁ : centralizer ({z} : Set G)).2

theorem t_mem : t e ∈ centralizer ({z} : Set G) :=
  (someLift e tbar : centralizer ({z} : Set G)).2

theorem E_le : E e ≤ centralizer ({z} : Set G) :=
  map_subtype_le _

theorem P_le : P e ≤ centralizer ({z} : Set G) :=
  map_subtype_le _

theorem F_le : F e ≤ centralizer ({z} : Set G) :=
  map_subtype_le _

theorem K_le : K e ≤ centralizer ({z} : Set G) :=
  map_subtype_le _

end Lifts

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.Janko
