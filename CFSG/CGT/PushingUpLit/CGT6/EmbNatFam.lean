module

public import CFSG.CGT.PushingUpLit.CGT6.EmbNatBase

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

section Aux

variable {V : Type} [CommGroup V] {m : ℕ} {X : Subgroup (MulAut V)}

private def nrecPhi (vo : Fin m → V) (u : G6.PermMod m) : V :=
  ∏ i, vo i ^ (Multiplicative.toAdd u i).val

private theorem nrecPhi_mul {vo : Fin m → V} (h2 : ∀ i, vo i ^ 2 = 1) (u w : G6.PermMod m) :
    nrecPhi vo (u * w) = nrecPhi vo u * nrecPhi vo w := by
  unfold nrecPhi
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [toAdd_mul, Pi.add_apply]
  generalize Multiplicative.toAdd u i = a
  generalize Multiplicative.toAdd w i = b
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (h2 i)]

private def nrecHom (vo : Fin m → V) (h2 : ∀ i, vo i ^ 2 = 1) : G6.PermMod m →* V where
  toFun := nrecPhi vo
  map_one' := by simp [nrecPhi]
  map_mul' := nrecPhi_mul h2

private theorem nrecHom_apply (vo : Fin m → V) (h2 : ∀ i, vo i ^ 2 = 1) (u : G6.PermMod m) :
    nrecHom vo h2 u = nrecPhi vo u := rfl

private theorem nrecHom_single (vo : Fin m → V) (h2 : ∀ i, vo i ^ 2 = 1) (a : Fin m) :
    nrecHom vo h2 (Multiplicative.ofAdd (Pi.single a 1)) = vo a := by
  have h1 : (1 : ZMod 2).val = 1 := rfl
  rw [nrecHom_apply, nrecPhi, Finset.prod_eq_single a]
  · simp [h1]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private theorem nrec_exists_vo (θ : X ≃* alternatingGroup (Fin m)) (p : Fin m) (v : V)
    (htrans : ∀ i : Fin m, ∃ x : X, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = i)
    (hJ : ∀ x : X, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = p →
      (x : MulAut V) v = v) :
    ∃ vo : Fin m → V, ∀ x : X,
      vo (((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p) = (x : MulAut V) v := by
  choose xi hxi using htrans
  refine ⟨fun i => (xi i : MulAut V) v, fun x => ?_⟩
  have h1 := hJ (x⁻¹ * xi (((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p)) (by
    simp [hxi])
  have h3 : (x : MulAut V) ((x : MulAut V)⁻¹ ((xi (((θ x : alternatingGroup (Fin m)) :
      Equiv.Perm (Fin m)) p) : MulAut V) v)) = (x : MulAut V) v := by
    simpa using congrArg (x : MulAut V) h1
  rwa [MulAut.apply_inv_self] at h3

private theorem nrec_vo_equiv (θ : X ≃* alternatingGroup (Fin m)) (p : Fin m) (v : V)
    (vo : Fin m → V)
    (htrans : ∀ i : Fin m, ∃ x : X, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = i)
    (hvo : ∀ x : X, vo (((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p) =
      (x : MulAut V) v)
    (x : X) (i : Fin m) :
    (x : MulAut V) (vo i) = vo (((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) i) := by
  obtain ⟨y, rfl⟩ := htrans i
  rw [hvo y]
  simpa using (hvo (x * y)).symm

private theorem nrecHom_equiv (θ : X ≃* alternatingGroup (Fin m)) (vo : Fin m → V)
    (h2 : ∀ i, vo i ^ 2 = 1)
    (hvo : ∀ (x : X) (i : Fin m), (x : MulAut V) (vo i) =
      vo (((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) i))
    (x : X) (u : G6.PermMod m) :
    (x : MulAut V) (nrecHom vo h2 u) = nrecHom vo h2
      (G6.permAct m ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) u) := by
  simp only [nrecHom_apply, nrecPhi]
  rw [map_prod]
  simp only [map_pow, hvo, G6.permAct_apply]
  exact Fintype.prod_equiv ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) _ _
    fun i => by simp

private theorem nrecHom_range (θ : X ≃* alternatingGroup (Fin m)) (p : Fin m) (v : V)
    (vo : Fin m → V) (h2 : ∀ i, vo i ^ 2 = 1)
    (htrans : ∀ i : Fin m, ∃ x : X, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = i)
    (hvo : ∀ x : X, vo (((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p) =
      (x : MulAut V) v) :
    (nrecHom vo h2).range = orbitSpan X v := by
  have hmem : ∀ i, vo i ∈ orbitSpan X v := by
    intro i
    obtain ⟨x, rfl⟩ := htrans i
    rw [hvo x]
    exact Subgroup.subset_closure ⟨(x : MulAut V), x.2, rfl⟩
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    rw [nrecHom_apply, nrecPhi]
    exact Subgroup.prod_mem _ fun i _ => Subgroup.pow_mem _ (hmem i) _
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Multiplicative.ofAdd (Pi.single (((θ ⟨x, hx⟩ : alternatingGroup (Fin m)) :
      Equiv.Perm (Fin m)) p) 1), ?_⟩
    rw [nrecHom_single, hvo ⟨x, hx⟩]

end Aux

theorem exists_orbitFamHom {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 3 ≤ m) {X : Subgroup (MulAut V)} (θ : X ≃* alternatingGroup (Fin m)) (p : Fin m)
    {v : V}
    (hJ : ∀ x : X, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = p →
      (x : MulAut V) v = v) :
    ∃ Φ : G6.PermMod m →* V, Φ (Multiplicative.ofAdd (Pi.single p 1)) = v ∧
      Φ.range = orbitSpan X v ∧
      ∀ (x : X) (u : G6.PermMod m), (x : MulAut V) (Φ u) =
        Φ (G6.permAct m ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) u) := by
  have htrans : ∀ i : Fin m,
      ∃ x : X, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = i := by
    intro i
    have := alternatingGroup.isPretransitive_of_three_le_card (Fin m) (by simp; omega)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin m)) p i
    exact ⟨θ.symm g, by simpa using (show (g : Equiv.Perm (Fin m)) p = i from hg)⟩
  obtain ⟨vo, hvo⟩ := nrec_exists_vo θ p v htrans hJ
  have h2 : ∀ i, vo i ^ 2 = 1 := fun i => hV _
  refine ⟨nrecHom vo h2, ?_, nrecHom_range θ p v vo h2 htrans hvo,
    nrecHom_equiv θ vo h2 (nrec_vo_equiv θ p v vo htrans hvo)⟩
  have h1 := hvo 1
  simp only [map_one, Subgroup.coe_one, Equiv.Perm.coe_one, id_eq, MulAut.one_apply] at h1
  rw [nrecHom_single, h1]

end CFSG.CGT.PushingUpLit.CGT6
