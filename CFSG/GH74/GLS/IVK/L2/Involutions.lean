module

public import CFSG.GH74.GLS.IVK.L2.DihedralAux
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section PGL2

variable {F : Type} [Field F] [Finite F]

theorem torus_data (hodd : Odd (Nat.card F)) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    ∃ (U : Subgroup (PGL2 F)) (s w : PGL2 F), IsCyclic U ∧ (Nat.card U : ℤ) = Nat.card F - δ ∧
      s ∈ U ∧ s * s = 1 ∧ s ≠ 1 ∧ w ∉ U ∧ w * w = 1 ∧ (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
      centralizer ({s} : Set (PGL2 F)) = U ⊔ zpowers w ∧
      ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  have hpos : 0 < Nat.card F := Nat.card_pos
  rcases hδ with rfl | rfl
  · obtain ⟨U, s, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      pgl2_split_torus_centralizer_data F hodd
    exact ⟨U, s, w, h1, by omega, h3, h4, h5, h6, h7, h8, h9, h10 hodd⟩
  · obtain ⟨U, s, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      pgl2_nonsplit_torus_centralizer_data F hodd
    exact ⟨U, s, w, h1, by omega, h3, h4, h5, h6, h7, h8, h9, h10 hodd⟩

theorem odd_of_isOddPrimePower {n : ℕ} (hF : IsOddPrimePower n) : Odd n := by
  obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
  rw [hq]
  exact hpodd.pow

theorem pgl2_involution_centralizer_dihedral (hF : IsOddPrimePower (Nat.card F))
    (hq3 : 3 < Nat.card F) {ε : ℤ} (hε1 : ε = 1 ∨ ε = -1) (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4])
    {A : PGL2 F} (hA2 : orderOf A = 2) :
    (A ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range →
      ∃ m : ℕ, (m : ℤ) = Nat.card F - ε ∧ Nonempty (↥(centralizer ({A} : Set (PGL2 F))) ≃*
        DihedralGroup m)) ∧
    (A ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range →
      ∃ m : ℕ, (m : ℤ) = Nat.card F + ε ∧ Nonempty (↥(centralizer ({A} : Set (PGL2 F))) ≃*
        DihedralGroup m)) := by
  have hodd : Odd (Nat.card F) := odd_of_isOddPrimePower hF
  set K' := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hK'
  have hidx : K'.index = 2 := pgl2_psl2Range_index_eq_two F hF
  have hcomm : commutator (PGL2 F) = K' := pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hq3
  have hA1 : A ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hA2
    omega
  have hAI : BenderSuzuki.PFAppendixIII.IsInvolution A :=
    ⟨hA1, by have := pow_orderOf_eq_one A; rwa [hA2] at this⟩
  have hεmod := hε
  unfold Int.ModEq at hεmod
  constructor
  · intro hAK
    obtain ⟨U, s, w, hU, hcard, hsU, hs2, hs1, hwU, hw2, hinv, hC, hUK⟩ := torus_data hodd ε hε1
    have hUc : IsCyclic U := hU
    have h4 : 4 ∣ Nat.card U := by omega
    have hsK : s ∈ K' := (DihedralAux.involution_mem_iff K' hidx U hUK hsU hs2 hs1).mpr h4
    have hsI : BenderSuzuki.PFAppendixIII.IsInvolution s := ⟨hs1, by rw [pow_two]; exact hs2⟩
    obtain ⟨g, -, hg⟩ := pgl2_inner_involutions_conjugate hF hq3 (x := A) (y := s)
      (hcomm ▸ hAK) hAI (hcomm ▸ hsK) hsI
    obtain ⟨e1⟩ := DihedralAux.centralizer_equiv_of_conj hg
    obtain ⟨e2⟩ := CFSG.ABGDGroups.nonempty_mulEquiv_dihedral_of_reflected (T := U) hwU hw2 hinv
    exact ⟨Nat.card U, hcard, ⟨(e1.trans (MulEquiv.subgroupCongr hC)).trans e2⟩⟩
  · intro hAK
    obtain ⟨U, s, w, hU, hcard, hsU, hs2, hs1, hwU, hw2, hinv, hC, hUK⟩ :=
      torus_data hodd (-ε) (by rcases hε1 with rfl | rfl <;> simp)
    have hUc : IsCyclic U := hU
    have h4 : ¬ 4 ∣ Nat.card U := by omega
    have hsK : s ∉ K' := fun h => h4 ((DihedralAux.involution_mem_iff K' hidx U hUK hsU hs2 hs1).mp h)
    have hsI : BenderSuzuki.PFAppendixIII.IsInvolution s := ⟨hs1, by rw [pow_two]; exact hs2⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (pgl2_outer_involutions_conjugate F hF hq3 (a := A) (b := s) hAI hsI
        (by rw [hcomm]; exact hAK) (by rw [hcomm]; exact hsK))
    obtain ⟨e1⟩ := DihedralAux.centralizer_equiv_of_conj hg
    obtain ⟨e2⟩ := CFSG.ABGDGroups.nonempty_mulEquiv_dihedral_of_reflected (T := U) hwU hw2 hinv
    exact ⟨Nat.card U, by omega, ⟨(e1.trans (MulEquiv.subgroupCongr hC)).trans e2⟩⟩

end PGL2

end CFSG.GH74.GLS.IVK
