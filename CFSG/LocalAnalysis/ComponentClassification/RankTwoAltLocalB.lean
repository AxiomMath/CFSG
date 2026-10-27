module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIILocal

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

@[expose] def beta6 : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5

abbrev betaClosure : Subgroup (Perm (Fin 6)) :=
  closure {g | ∃ h ∈ alternatingGroup (Fin 6), g = ⁅beta6, h⁆}

theorem commutator_beta6_mem {h : Perm (Fin 6)} (hh : sign h = 1) : ⁅beta6, h⁆ ∈ betaClosure :=
  subset_closure ⟨h, mem_alternatingGroup.2 hh, rfl⟩

theorem carmichael6_mem_2 : carmichaelPerm (⟨2, by decide⟩ : CarmichaelIndex 6) ∈ betaClosure := by
  rw [show carmichaelPerm (⟨2, by decide⟩ : CarmichaelIndex 6) =
      ⁅beta6, (swap 1 2 * swap 3 4 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 3 * swap 3 5 * swap 5 4 * swap 4 2 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 2 * swap 3 5 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 4 * swap 4 3 * swap 3 5 * swap 5 2 : Perm (Fin 6))⁆ by
    decide +kernel]
  exact mul_mem (mul_mem (mul_mem (commutator_beta6_mem (by decide +kernel))
      (commutator_beta6_mem (by decide +kernel)))
      (commutator_beta6_mem (by decide +kernel)))
      (commutator_beta6_mem (by decide +kernel))

theorem carmichael6_mem_3 : carmichaelPerm (⟨3, by decide⟩ : CarmichaelIndex 6) ∈ betaClosure := by
  rw [show carmichaelPerm (⟨3, by decide⟩ : CarmichaelIndex 6) =
      ⁅beta6, (swap 1 3 * swap 3 4 * swap 4 5 * swap 5 2 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 2 * swap 3 5 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 3 * swap 3 5 * swap 5 4 * swap 4 2 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 4 * swap 4 3 * swap 3 5 * swap 5 2 : Perm (Fin 6))⁆ by
    decide +kernel]
  exact mul_mem (mul_mem (mul_mem (commutator_beta6_mem (by decide +kernel))
      (commutator_beta6_mem (by decide +kernel)))
      (commutator_beta6_mem (by decide +kernel)))
      (commutator_beta6_mem (by decide +kernel))

theorem carmichael6_mem_4 : carmichaelPerm (⟨4, by decide⟩ : CarmichaelIndex 6) ∈ betaClosure := by
  rw [show carmichaelPerm (⟨4, by decide⟩ : CarmichaelIndex 6) =
      ⁅beta6, (swap 1 2 * swap 4 5 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 2 * swap 3 5 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 3 * swap 3 2 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 5 * swap 5 4 * swap 4 3 * swap 3 2 : Perm (Fin 6))⁆ by
    decide +kernel]
  exact mul_mem (mul_mem (mul_mem (commutator_beta6_mem (by decide +kernel))
      (commutator_beta6_mem (by decide +kernel)))
      (commutator_beta6_mem (by decide +kernel)))
      (commutator_beta6_mem (by decide +kernel))

theorem carmichael6_mem_5 : carmichaelPerm (⟨5, by decide⟩ : CarmichaelIndex 6) ∈ betaClosure := by
  rw [show carmichaelPerm (⟨5, by decide⟩ : CarmichaelIndex 6) =
      ⁅beta6, (swap 1 2 * swap 4 5 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 2 * swap 3 4 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 3 * swap 3 2 : Perm (Fin 6))⁆ * ⁅beta6, (swap 1 4 * swap 4 5 * swap 5 3 * swap 3 2 : Perm (Fin 6))⁆ by
    decide +kernel]
  exact mul_mem (mul_mem (mul_mem (commutator_beta6_mem (by decide +kernel))
      (commutator_beta6_mem (by decide +kernel)))
      (commutator_beta6_mem (by decide +kernel)))
      (commutator_beta6_mem (by decide +kernel))

theorem alternatingGroup_six_le_closure : alternatingGroup (Fin 6) ≤ betaClosure := by
  refine (closure_range_carmichaelPerm (by norm_num)).symm.le.trans ?_
  rw [closure_le]
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact carmichael6_mem_2
  · exact carmichael6_mem_3
  · exact carmichael6_mem_4
  · exact carmichael6_mem_5

@[expose] def dbl : Perm (Fin 6) →* Perm (Fin 6 × Fin 2) where
  toFun σ := prodCongrLeft fun _ => σ
  map_one' := by ext x <;> rfl
  map_mul' σ τ := by ext x <;> rfl

theorem dbl_apply (σ : Perm (Fin 6)) (x : Fin 6 × Fin 2) : dbl σ x = (σ x.1, x.2) := rfl

theorem dbl_injective : Function.Injective dbl := by
  intro σ τ h
  ext i
  have := congrArg (fun f : Perm (Fin 6 × Fin 2) => (f (i, 0)).1) h
  simpa [dbl_apply] using congrArg Fin.val this

theorem sign_dbl (σ : Perm (Fin 6)) : sign (dbl σ) = 1 := by
  show sign (prodCongrLeft fun _ : Fin 2 => σ) = 1
  rw [sign_prodCongrLeft, Fin.prod_univ_two, Int.units_mul_self]

@[expose] def a12 : Perm (Fin 6 × Fin 2) := prodCongr (Equiv.refl _) (swap 0 1)

@[expose] def b12 : Perm (Fin 6 × Fin 2) := dbl beta6

theorem dbl_mul_a12 (σ : Perm (Fin 6)) : dbl σ * a12 = a12 * dbl σ := by
  ext x <;> rfl

theorem a12_ne_one : a12 ≠ 1 := by decide

theorem dbl_alternatingGroup_le_nE :
    (alternatingGroup (Fin 6)).map dbl ≤
      nE (alternatingGroup (Fin 6 × Fin 2)) (closure {a12, b12}) := by
  set P := (alternatingGroup (Fin 6)).map dbl
  have ha : a12 ∈ closure ({a12, b12} : Set (Perm (Fin 6 × Fin 2))) :=
    subset_closure (Set.mem_insert _ _)
  have hb : b12 ∈ closure ({a12, b12} : Set (Perm (Fin 6 × Fin 2))) :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  have hPP : ⁅P, P⁆ = P := by
    rw [← Subgroup.map_commutator, commutator_alternatingGroup_eq_self (by simp)]
  have hPC : P ≤ alternatingGroup (Fin 6 × Fin 2) ⊓ centralizer ({a12} : Set _) := by
    rintro _ ⟨σ, -, rfl⟩
    refine ⟨mem_alternatingGroup.2 (sign_dbl σ), ?_⟩
    show dbl σ ∈ centralizer ({a12} : Set _)
    rw [mem_centralizer_singleton_iff]
    exact dbl_mul_a12 σ
  have hPΓ : P ≤ gammaE (alternatingGroup (Fin 6 × Fin 2)) (closure {a12, b12}) := by
    have hle : centDer (alternatingGroup (Fin 6 × Fin 2)) a12 ≤
        gammaE (alternatingGroup (Fin 6 × Fin 2)) (closure {a12, b12}) :=
      le_iSup₂_of_le a12 ha (le_iSup_of_le a12_ne_one le_rfl)
    calc P = ⁅P, P⁆ := hPP.symm
      _ ≤ centDer (alternatingGroup (Fin 6 × Fin 2)) a12 := commutator_mono hPC hPC
      _ ≤ _ := hle
  have hgen := Subgroup.map_mono (f := dbl) alternatingGroup_six_le_closure
  refine hgen.trans ?_
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
  rw [map_commutatorElement]
  exact commutator_mem_commutator hb (hPΓ ⟨h, hh, rfl⟩)

@[expose] def a8 : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def b8 : Perm (Fin 8) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7

@[expose] def c8 : Perm (Fin 8) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

theorem a8_mem : a8 ∈ closure ({a8, b8} : Set (Perm (Fin 8))) :=
  subset_closure (Set.mem_insert _ _)

theorem b8_mem : b8 ∈ closure ({a8, b8} : Set (Perm (Fin 8))) :=
  subset_closure (Set.mem_insert_of_mem _ rfl)

theorem a8_mem_nE : a8 ∈ nE (alternatingGroup (Fin 8)) (closure {a8, b8}) := by
  refine (congrArg (fun x => x ∈ nE (alternatingGroup (Fin 8)) (closure {a8, b8}))
    (show a8 = ⁅b8, ⁅(swap 4 5 * swap 6 7 : Perm (Fin 8)), (swap 2 4 * swap 3 5 : Perm (Fin 8))⁆⁆ by decide +kernel)).mpr ?_
  exact commutatorElement_mem_nE b8_mem
      (commutatorElement_mem_gammaE_perm a8_mem (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel) (by decide +kernel))

theorem b8_mem_nE : b8 ∈ nE (alternatingGroup (Fin 8)) (closure {a8, b8}) := by
  refine (congrArg (fun x => x ∈ nE (alternatingGroup (Fin 8)) (closure {a8, b8}))
    (show b8 = ⁅a8, ⁅(swap 4 6 * swap 5 7 : Perm (Fin 8)), (swap 1 4 * swap 3 6 : Perm (Fin 8))⁆⁆ by decide +kernel)).mpr ?_
  exact commutatorElement_mem_nE a8_mem
      (commutatorElement_mem_gammaE_perm b8_mem (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel) (by decide +kernel))

theorem c8_mem_nE : c8 ∈ nE (alternatingGroup (Fin 8)) (closure {a8, b8}) := by
  refine (congrArg (fun x => x ∈ nE (alternatingGroup (Fin 8)) (closure {a8, b8}))
    (show c8 = ⁅b8, ⁅(swap 4 6 * swap 5 7 : Perm (Fin 8)), (swap 2 6 * swap 6 4 * swap 3 7 * swap 7 5 : Perm (Fin 8))⁆⁆ by decide +kernel)).mpr ?_
  exact commutatorElement_mem_nE b8_mem
      (commutatorElement_mem_gammaE_perm a8_mem (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel) (by decide +kernel))

@[expose] def e8 : Subgroup (Perm (Fin 8)) := closure {a8, b8, c8}

theorem e8_le_nE : e8 ≤ nE (alternatingGroup (Fin 8)) (closure {a8, b8}) := by
  rw [e8, closure_le]
  rintro x (rfl | rfl | rfl)
  · exact a8_mem_nE
  · exact b8_mem_nE
  · exact c8_mem_nE

theorem a8_mem_e8 : a8 ∈ e8 := subset_closure (Set.mem_insert _ _)
theorem b8_mem_e8 : b8 ∈ e8 := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
theorem c8_mem_e8 : c8 ∈ e8 :=
  subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem e8_pairwise_commute : ({a8, b8, c8} : Set (Perm (Fin 8))).Pairwise Commute := by
  intro x hx y hy _
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    · unfold Commute SemiconjBy
      decide

theorem mul_self_of_mem_e8 {x : Perm (Fin 8)} (hx : x ∈ e8) : x * x = 1 := by
  have hc := Subgroup.isMulCommutative_closure e8_pairwise_commute
  induction hx using Subgroup.closure_induction with
  | mem x hx => rcases hx with rfl | rfl | rfl <;> decide
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * x * (y * y) := by rw [← hxy]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x _ ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem isPGroup_e8 : IsPGroup 2 e8 := fun g =>
  ⟨1, Subtype.ext (by rw [pow_one, sq, Subgroup.coe_mul, mul_self_of_mem_e8 g.2]; rfl)⟩

theorem five_le_card_e8 : 5 ≤ Nat.card e8 := by
  have hsub : (({1, a8, b8, c8, a8 * b8} : Finset (Perm (Fin 8))) : Set (Perm (Fin 8))) ⊆
      (e8 : Set (Perm (Fin 8))) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact a8_mem_e8
    · exact b8_mem_e8
    · exact c8_mem_e8
    · exact mul_mem a8_mem_e8 b8_mem_e8
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, show ({1, a8, b8, c8, a8 * b8} : Finset (Perm (Fin 8))).card = 5 by
    decide] at h
  calc 5 ≤ (e8 : Set (Perm (Fin 8))).ncard := h
    _ = Nat.card e8 := (Nat.card_coe_set_eq _).symm

@[expose] def a3 : Perm (Fin 8) := swap 5 6 * swap 6 7

theorem sign_a3 : sign a3 = 1 := by decide

theorem map_conj_e8 : e8.map (MulAut.conj (a3 * a8 * a3⁻¹)).toMonoidHom ≤ e8 := by
  rw [e8, MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with rfl | rfl | rfl
  · show a3 * a8 * a3⁻¹ * a8 * (a3 * a8 * a3⁻¹)⁻¹ ∈ e8
    rw [show a3 * a8 * a3⁻¹ * a8 * (a3 * a8 * a3⁻¹)⁻¹ = a8 by decide]
    exact a8_mem_e8
  · show a3 * a8 * a3⁻¹ * b8 * (a3 * a8 * a3⁻¹)⁻¹ ∈ e8
    rw [show a3 * a8 * a3⁻¹ * b8 * (a3 * a8 * a3⁻¹)⁻¹ = b8 by decide]
    exact b8_mem_e8
  · show a3 * a8 * a3⁻¹ * c8 * (a3 * a8 * a3⁻¹)⁻¹ ∈ e8
    rw [show a3 * a8 * a3⁻¹ * c8 * (a3 * a8 * a3⁻¹)⁻¹ = a8 * b8 * c8 by decide]
    exact mul_mem (mul_mem a8_mem_e8 b8_mem_e8) c8_mem_e8

theorem conj_a3a8_mem_e8 {m : Perm (Fin 8)} (hm : m ∈ e8) :
    a3 * a8 * a3⁻¹ * m * (a3 * a8 * a3⁻¹)⁻¹ ∈ e8 := by
  have h := map_conj_e8 (Subgroup.mem_map_of_mem (MulAut.conj (a3 * a8 * a3⁻¹)).toMonoidHom hm)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem a8_not_commute : a8 * (a3⁻¹ * c8 * a3) ≠ a3⁻¹ * c8 * a3 * a8 := by decide

end CFSG.ComponentClassification.RankTwoAlt
