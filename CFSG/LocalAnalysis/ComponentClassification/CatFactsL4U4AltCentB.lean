module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentA

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace AltCent

open CFSG Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal] {m : ℕ}

@[expose] noncomputable def toPerm (eN : ↥N ≃* alternatingGroup (Fin m)) (hm5 : 5 ≤ m)
    (hm6 : m ≠ 6) : G →* Perm (Fin m) :=
  (MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm5
    hm6)).symm.toMonoidHom.comp ((MulAut.congr eN).toMonoidHom.comp MulAut.conjNormal)

variable (eN : ↥N ≃* alternatingGroup (Fin m)) (hm5 : 5 ≤ m) (hm6 : m ≠ 6)

theorem toPerm_of_mem {n : G} (hn : n ∈ N) :
    toPerm eN hm5 hm6 n = ((eN ⟨n, hn⟩ : alternatingGroup (Fin m)) : Perm (Fin m)) := by
  rw [toPerm, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq,
    MulEquiv.ofBijective_apply]
  refine MulEquiv.ext fun y => Subtype.ext ?_
  rw [MulAut.conjNormal_apply]
  show ((eN (MulAut.conjNormal n (eN.symm y)) : alternatingGroup (Fin m)) : Perm (Fin m)) = _
  have h1 : (MulAut.conjNormal n (eN.symm y) : ↥N) = ⟨n, hn⟩ * eN.symm y * (⟨n, hn⟩)⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp

theorem toPerm_injective (hC : centralizer (N : Set G) = ⊥) :
    Function.Injective (toPerm eN hm5 hm6) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : MulAut.conjNormal (H := N) g = 1 := by
    have h2 : (MulAut.congr eN) (MulAut.conjNormal (H := N) g) = 1 := by
      have := congrArg (MulEquiv.ofBijective _
        (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm5 hm6)) hg
      rw [map_one] at this
      rw [← this, toPerm, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
      rfl
    exact (MulEquiv.map_eq_one_iff _).mp h2
  have hgC : g ∈ centralizer (N : Set G) := by
    rw [mem_centralizer_iff]
    intro n hn
    have := congrArg (fun φ : MulAut ↥N => (φ ⟨n, hn⟩ : G)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc n * g = g * n * g⁻¹ * g := by rw [this]
      _ = g * n := by group
  rw [hC, mem_bot] at hgC
  exact hgC

theorem map_N : N.map (toPerm eN hm5 hm6) = alternatingGroup (Fin m) := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    rw [toPerm_of_mem eN hm5 hm6 hn]
    exact (eN ⟨n, hn⟩).2
  · intro x hx
    obtain ⟨n, hn⟩ := eN.surjective ⟨x, hx⟩
    refine ⟨n, n.2, ?_⟩
    rw [toPerm_of_mem eN hm5 hm6 n.2]
    simp [hn]

theorem exists_of_mem_alt {x : Perm (Fin m)} (hx : x ∈ alternatingGroup (Fin m)) :
    ∃ n ∈ N, toPerm eN hm5 hm6 n = x := by
  rw [← map_N eN hm5 hm6] at hx
  obtain ⟨n, hn, h⟩ := hx
  exact ⟨n, hn, h⟩

theorem mem_pair_iff_of_comm {i j : Fin m} (hij : i ≠ j) {c : Perm (Fin m)}
    (hc : swap i j * c = c * swap i j) (a : Fin m) :
    c a ∈ ({i, j} : Finset (Fin m)) ↔ a ∈ ({i, j} : Finset (Fin m)) := by
  have hc' : c * swap i j = swap i j * c := hc.symm
  have h1 := mem_support_iff_of_comm hc' a
  rw [support_swap hij] at h1
  exact h1

theorem card_dvd_of_quot {J : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (eJ : ↥J ⧸ center ↥J ≃* alternatingGroup (Fin n)) : n.factorial / 2 ∣ Nat.card J := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h1 : Nat.card (↥J ⧸ center ↥J) = n.factorial / 2 := by
    rw [Nat.card_congr eJ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  rw [← h1]
  exact Subgroup.card_quotient_dvd_card _

end AltCent

end CFSG.ComponentClassification.CatFactsL4U4
