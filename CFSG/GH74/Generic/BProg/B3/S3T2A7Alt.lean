module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Defs
public import CFSG.GH74.Generic.BProg.B3.S3T5AnCore
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG Equiv Equiv.Perm Subgroup CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance

theorem card_fix_ne_three {n : ℕ} (hn : n % 2 = 0) {f : Perm (Fin n)} (hf : f * f = 1) :
    (Finset.univ.filter fun p => f p = p).card ≠ 3 := by
  classical
  have h2 : 2 ∣ f.support.card := Equiv.Perm.two_dvd_card_support (by rw [sq]; exact hf)
  have hsupp : (Finset.univ.filter fun p => f p = p) = f.supportᶜ := by
    ext p
    simp [Equiv.Perm.mem_support]
  have hc : (Finset.univ.filter fun p => f p = p).card + f.support.card = n := by
    rw [hsupp, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ f.support
    rw [Fintype.card_fin] at this
    omega
  omega

theorem locBal1Two_alt {K : Type} [Group K] [Finite K] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (hev : n % 2 = 0) (e : K ≃* alternatingGroup (Fin n)) : LocBal1Two K := by
  intro H hInn t ht
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  let Φ : MulAut K ≃* Perm (Fin n) :=
    (MulAut.congr e).trans (MulEquiv.ofBijective MulAut.conjNormal hbij).symm
  have hΦconj : ∀ k : K, Φ (MulAut.conj k) = ((e k : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro k
    show (MulEquiv.ofBijective MulAut.conjNormal hbij).symm (MulAut.congr e (MulAut.conj k)) = _
    rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply]
    ext x
    simp [MulAut.congr_apply, MulAut.conjNormal_apply]
  set H' : Subgroup (Perm (Fin n)) := H.map Φ.toMonoidHom with hH'
  have hA : alternatingGroup (Fin n) ≤ H' := by
    intro σ hσ
    obtain ⟨k, hk⟩ := e.surjective ⟨σ, hσ⟩
    refine ⟨MulAut.conj k, hInn ⟨k, rfl⟩, ?_⟩
    show Φ (MulAut.conj k) = σ
    rw [hΦconj, hk]
  have : H'.Normal := S3T5An.normal_of_alternatingGroup_le hA
  let ψ : ↥H ≃* ↥H' := H.equivMapOfInjective Φ.toMonoidHom Φ.injective
  have h1 : (involutionOddCore t).map ψ.toMonoidHom = involutionOddCore (ψ t) :=
    involutionOddCore_map ψ t
  rw [← Subgroup.map_eq_bot_iff_of_injective (f := ψ.toMonoidHom) (involutionOddCore t)
    ψ.injective, h1, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hx1' : ((x : H') : Perm (Fin n)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have ht2 : (ψ t : Perm (Fin n)) * (ψ t) = 1 := by
    have h2 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht, sq] at this
    have := congrArg (fun s => ((ψ s : H') : Perm (Fin n))) h2
    simpa using this
  apply card_fix_ne_three hev ht2
  refine S3T5An.card_fix_eq_three (N := (involutionOddCore (ψ t)).map H'.subtype)
    (S3T5An.odd_card_map_involutionOddCore (ψ t)) ht2 ?_
    (fun g hg y hy => S3T5An.conj_mem_map_involutionOddCore hg hy) ⟨x, hx, rfl⟩ hx1'
  rintro _ ⟨y, hy, rfl⟩
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_singleton_iff.1 (involutionOddCore_le_centralizer (ψ t) hy))

theorem locBal1For_alt810 : LocBal1For Alt810 := by
  intro T _ _ hT
  rcases hT with h | h
  · obtain ⟨e⟩ := h
    exact locBal1Two_alt (n := 8) (by norm_num) (by norm_num) (by norm_num) e
  · obtain ⟨e⟩ := h
    exact locBal1Two_alt (n := 10) (by norm_num) (by norm_num) (by norm_num) e

end CFSG.GH74.Generic.BProg.B3.S3T2A7
