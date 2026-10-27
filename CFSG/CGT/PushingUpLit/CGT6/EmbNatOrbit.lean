module

public import CFSG.CGT.PushingUpLit.CGT6.EmbNatFam
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltPerm

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

section Aux

variable {V : Type} [CommGroup V] {m : ℕ} {X : Subgroup (MulAut V)}

private theorem nrec_permAct_allOnes (σ : Equiv.Perm (Fin m)) :
    G6.permAct m σ (G6.allOnes m) = G6.allOnes m := rfl

private theorem nrec_permAct_single (σ : Equiv.Perm (Fin m)) (a : Fin m) :
    G6.permAct m σ (Multiplicative.ofAdd (Pi.single a 1)) =
      Multiplicative.ofAdd (Pi.single (σ a) 1) := by
  refine Multiplicative.toAdd.injective (funext fun i => ?_)
  rw [G6.permAct_apply]
  simp [Pi.single_apply, Equiv.symm_apply_eq]

private theorem nrec_ker_eq (hm : 4 ≤ m) (θ : X ≃* alternatingGroup (Fin m))
    (hV : ∀ v : V, v ^ 2 = 1)
    (hX : ∀ w : V, (∀ x : X, (x : MulAut V) w = w) → w = 1) (p : Fin m) {v : V} (hv : v ≠ 1)
    (Φ : G6.PermMod m →* V) (hΦp : Φ (Multiplicative.ofAdd (Pi.single p 1)) = v)
    (hequiv : ∀ (x : X) (u : G6.PermMod m), (x : MulAut V) (Φ u) =
      Φ (G6.permAct m ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) u)) :
    Φ.ker = Subgroup.zpowers (G6.allOnes m) := by
  have hinv : ∀ σ ∈ alternatingGroup (Fin m), ∀ u ∈ Φ.ker, G6.permAct m σ u ∈ Φ.ker := by
    intro σ hσ u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have := hequiv (θ.symm ⟨σ, hσ⟩) u
    simp only [MulEquiv.apply_symm_apply] at this
    rw [← this, hu, map_one]
  have hall : G6.allOnes m ∈ Φ.ker := by
    rw [MonoidHom.mem_ker]
    apply hX
    intro x
    rw [hequiv x, nrec_permAct_allOnes]
  apply le_antisymm
  · intro u hu
    by_contra hnot
    have hu1 : u ≠ 1 := fun h => hnot (h ▸ one_mem _)
    have hu2 : u ≠ G6.allOnes m := fun h => hnot (by rw [h]; exact Subgroup.mem_zpowers _)
    have hcore := coreMod_le_of_invariant hm hinv hu hu1 hu2
    have hconst : ∀ a b, Φ (Multiplicative.ofAdd (Pi.single a 1)) =
        Φ (Multiplicative.ofAdd (Pi.single b 1)) := by
      intro a b
      have hmem : Multiplicative.ofAdd (Pi.single a 1) * Multiplicative.ofAdd (Pi.single b 1) ∈
          G6.coreMod m := by
        rw [G6.mem_coreMod]
        simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply, Finset.sum_add_distrib,
          Finset.sum_pi_single', Finset.mem_univ, ite_true]
        decide
      have h := hcore hmem
      rw [MonoidHom.mem_ker, map_mul] at h
      have hb : Φ (Multiplicative.ofAdd (Pi.single b 1)) *
          Φ (Multiplicative.ofAdd (Pi.single b 1)) = 1 := by rw [← pow_two]; exact hV _
      exact mul_right_cancel (h.trans hb.symm)
    apply hv
    apply hX
    intro x
    have h := hequiv x (Multiplicative.ofAdd (Pi.single p 1))
    rw [hΦp, nrec_permAct_single] at h
    rw [h]
    exact (hconst _ _).trans hΦp
  · rwa [Subgroup.zpowers_le]

end Aux

theorem exists_orbitHom {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 4 ≤ m) {X : Subgroup (MulAut V)} (θ : X ≃* alternatingGroup (Fin m))
    (hX : ∀ w : V, (∀ x : X, (x : MulAut V) w = w) → w = 1) (p : Fin m) {v : V} (hv : v ≠ 1)
    (hJ : ∀ x : X, ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) p = p →
      (x : MulAut V) v = v) :
    ∃ Φ : G6.PermMod m →* V, Φ.range = orbitSpan X v ∧
      Φ.ker = Subgroup.zpowers (G6.allOnes m) ∧
      ∀ (x : X) (u : G6.PermMod m), (x : MulAut V) (Φ u) =
        Φ (G6.permAct m ((θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) u) := by
  obtain ⟨Φ, hΦp, hrange, hequiv⟩ := exists_orbitFamHom hV (by omega) θ p hJ
  exact ⟨Φ, hrange, nrec_ker_eq hm θ hV hX p hv Φ hΦp hequiv, hequiv⟩

end CFSG.CGT.PushingUpLit.CGT6
