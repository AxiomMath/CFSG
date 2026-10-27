module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSeed

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

@[expose] def fixedSub {U : Type*} [Group U] (σ : MulAut U) : Subgroup U where
  carrier := {u | σ u = u}
  one_mem' := map_one σ
  mul_mem' := fun {a b} ha hb =>
    show σ (a * b) = a * b by
      rw [map_mul, show σ a = a from ha, show σ b = b from hb]
  inv_mem' := fun {a} ha =>
    show σ a⁻¹ = a⁻¹ by
      rw [map_inv, show σ a = a from ha]

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

@[expose] def ell (t : ∀ i, MulAut ↥(planesIn W I i)) (i : Fin r) : Subgroup H :=
  (fixedSub (t i)).map (W.subtype.comp (planesIn W I i).subtype)

variable {t : ∀ i, MulAut ↥(planesIn W I i)}

omit [Finite H] in
theorem ell_le_I (i : Fin r) : ell t i ≤ I i := by
  rintro _ ⟨u, -, rfl⟩
  exact u.2

include h

omit [Finite H] in
theorem card_ell (ht : h.IsT0 t) (i : Fin r) : Nat.card ↥(ell t i) = 2 := by
  let _ := h.cg
  have := h.isKleinFour_planes i
  have hinj : Function.Injective (W.subtype.comp (planesIn W I i).subtype) :=
    W.subtype_injective.comp (planesIn W I i).subtype_injective
  unfold ell
  rw [Subgroup.card_map_of_injective hinj]
  have hinv := ht.invol i (Finset.mem_univ i)
  have h2 := card_fixed_of_invol hinv.1 hinv.2
  rw [← h2]
  exact Nat.card_congr (Equiv.refl _)

theorem rho_fixes_ell (ht : h.IsT0 t) {x : H} (hxJ : x ∈ thompsonJ R) (i : Fin r)
    {u : ↥(planesIn W I i)} (hu : t i u = u) : h.rho x (u : ↥W) = (u : ↥W) := by
  let _ := h.cg
  have hmem : h.rho x ∈ h.T0 := by
    rw [← h.rho_J_eq_T0 ht]
    exact ⟨x, hxJ, rfl⟩
  rcases (ht.mem_iff _).mp hmem i with hid | ⟨-, hgt⟩
  · exact hid u
  · rw [hgt u, hu]

theorem ell_le_E (ht : h.IsT0 t) (i : Fin r) : ell t i ≤ elemCenterIn 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro _ ⟨u, hu, rfl⟩
  refine mem_elemCenterIn_iff_centralizer.mpr ⟨?_, ?_, ?_⟩
  · exact h.V_le_R (h.W_le (u : ↥W).2)
  · exact h.W_elem.2 _ (u : ↥W).2
  · intro j hj
    rw [elemThompsonIn_two_eq] at hj
    have h1 := congrArg (fun a : ↥W => (a : H)) (h.rho_fixes_ell ht hj i hu)
    simp only [h.rho_apply] at h1
    show j * ((u : ↥W) : H) = ((u : ↥W) : H) * j
    calc j * ((u : ↥W) : H) = (j * ((u : ↥W) : H) * j⁻¹) * j := by group
      _ = ((u : ↥W) : H) * j := by rw [h1]

omit [Finite H] in
theorem ell_ne_bot (ht : h.IsT0 t) (i : Fin r) : ell t i ≠ ⊥ := fun hb => by
  have := h.card_ell ht i
  rw [hb, Subgroup.card_bot] at this
  omega

theorem piH_eq_one_of_mem_S (ht : h.IsT0 t) {s : H} (hs : s ∈ elemBaumannIn 2 R) :
    h.piH s = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsR, hsc⟩ := mem_elemBaumannIn_iff.mp hs
  refine Equiv.ext fun i => ?_
  by_contra hne
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h.ell_ne_bot ht i)
  have hxE : (x : H) ∈ elemCenterIn 2 R := h.ell_le_E ht i x.2
  have hcomm := hsc (x : H) hxE
  have hxI : (x : H) ∈ I i := ell_le_I i x.2
  have hxI' : (x : H) ∈ I (h.piH s i) := by
    rw [← h.map_conj_plane s i]
    refine ⟨x, hxI, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc s * (x : H) * s⁻¹ = (x : H) * s * s⁻¹ := by rw [hcomm]
      _ = x := by group
  have hne' : i ≠ h.piH s i := fun e => hne e.symm
  have hd : Disjoint (I i) (I (h.piH s i)) := h.I_indep.pairwiseDisjoint hne'
  exact hx1 (Subtype.ext (Subgroup.disjoint_def.mp hd hxI hxI'))

theorem rho_S_le_T0 (ht : h.IsT0 t) : (elemBaumannIn 2 R).map h.rho ≤ h.T0 := by
  rintro _ ⟨s, hs, rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsR : s ∈ R := (mem_elemBaumannIn_iff.mp hs).1
  exact ⟨⟨s, hsR, rfl⟩, (h.piH_eq_one_iff s).mp (h.piH_eq_one_of_mem_S ht hs)⟩

theorem rho_S_eq_T0 (ht : h.IsT0 t) : (elemBaumannIn 2 R).map h.rho = h.T0 := by
  apply le_antisymm (h.rho_S_le_T0 ht)
  rw [← h.rho_J_eq_T0 ht]
  refine Subgroup.map_mono ?_
  rw [← elemThompsonIn_two_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact elemThompsonIn_le_elemBaumannIn 2 R

theorem S_normalizes_planes (ht : h.IsT0 t) {s : H} (hs : s ∈ elemBaumannIn 2 R) (i : Fin r) :
    (I i).map (MulAut.conj s).toMonoidHom = I i := by
  rw [h.map_conj_plane, h.piH_eq_one_of_mem_S ht hs]
  rfl

end WreathHyp

theorem thompsonJ_le_baumann : thompsonJ R ≤ elemBaumannIn 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← elemThompsonIn_two_eq]
  exact elemThompsonIn_le_elemBaumannIn 2 R

theorem elemThompsonIn_baumann : elemThompsonIn 2 (elemBaumannIn 2 R) = thompsonJ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← elemThompsonIn_two_eq]
  exact elemThompsonIn_eq_of_le 2 (by rw [elemThompsonIn_two_eq]; exact thompsonJ_le_baumann)
    (elemBaumannIn_le 2 R)

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
