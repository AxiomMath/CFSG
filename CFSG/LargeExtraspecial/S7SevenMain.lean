module

public import CFSG.LargeExtraspecial.S7SevenB
public import CFSG.LargeExtraspecial.BridgeForms
public import CFSG.LargeExtraspecial.S7Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Equiv
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.Open

universe u

section Forms

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem timmesfeldIsometries_eq (Q : QuadraticForm (ZMod 2) V) :
    timmesfeldIsometries (Q : V → ZMod 2) = TauCeti.QuadraticMap.orthogonalGroup Q := by
  ext g
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  rfl

theorem timmesfeldOmega_eq [FiniteDimensional (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)
    (hQ : Q.polarBilin.Nondegenerate) :
    timmesfeldOmega (Q : V → ZMod 2) = omegaGroup Q hQ := by
  unfold timmesfeldOmega
  have : {g : V ≃ₗ[ZMod 2] V | g ∈ timmesfeldIsometries (Q : V → ZMod 2) ∧
      Even (finrank (ZMod 2) (LinearMap.range ((g : V →ₗ[ZMod 2] V) - LinearMap.id)))} =
      (omegaGroup Q hQ : Set (V ≃ₗ[ZMod 2] V)) := by
    ext g
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, mem_omegaGroup, timmesfeldIsometries_eq,
      ← Module.End.one_eq_id]
  rw [this, Subgroup.closure_eq]

end Forms

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Seven

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h8 : 8 ≤ finrank (ZMod 2) (Vt S g t))
include hCE H hNo C ht ht1 hVQ hΩ hN h8

theorem RmodN_le_range_resC (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t) :
    RmodN S g t ≤ (resC S g hV).range := by
  intro e he
  rw [← range_resV H.conj_mem t] at he
  obtain ⟨⟨r, hr⟩, rfl⟩ := he
  have htV : ∀ v ∈ Vt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv =>
    (self_mem_Nbar H ht).2 v hv
  rcases mem_Cbar_of_comm hCE H hNo C ht ht1 hVQ hΩ hN h8 (Rbar_le_Mbar hr)
    (commute_of_mem_Rbar H.conj_mem hr) with hc | hc
  · exact ⟨⟨r, hc⟩, LinearEquiv.ext fun v => Subtype.ext rfl⟩
  · refine ⟨⟨t * r, hc⟩, LinearEquiv.ext fun v => Subtype.ext ?_⟩
    change ((t * r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v
    rw [coe_mul_apply, htV _ (apply_mem_Vt_of_mem_Rbar H.conj_mem hr v.2)]

omit hCE hN h8 in
theorem range_resC_le_orthogonalGroup (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t)
    {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))) :
    (resC S g hV).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro _ ⟨c, rfl⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  have hD := dtEqConj_of_omegaCase H hNo C hΩ
  have key : ∀ x ∈ Cbar S t, ∀ v : S.Qt, v ∈ orbit S g t →
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ orbit S g t := fun x hx v hv =>
    apply_mem_orbit_of_comm H ht hD (Cbar_le_Mbar hx) (comm_of_mem_Cbar hx) hv
  intro v
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hcv0 : resC S g hV c v ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hv0
  have hiff : Q (resC S g hV c v) = 0 ↔ Q v = 0 := by
    rw [hsing _ hcv0, hsing _ hv0, mem_orbitOf_RmodN_iff H.conj_mem ht,
      mem_orbitOf_RmodN_iff H.conj_mem ht, coe_resC_apply]
    constructor
    · intro h
      have := key _ (inv_mem c.2) _ h
      rwa [inv_apply_apply_O] at this
    · exact key _ c.2 v
  rcases zmod2_eq_zero_or_eq_one (Q (resC S g hV c v)) with h1 | h1 <;>
    rcases zmod2_eq_zero_or_eq_one (Q v) with h2 | h2
  · rw [h1, h2]
  · exact absurd (hiff.mp h1) (by rw [h2]; decide)
  · exact absurd (hiff.mpr h2) (by rw [h1]; decide)
  · rw [h1, h2]

theorem range_resC_eq (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t)
    {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
    (hX : RmodN S g t = omegaGroup Q hQ)
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))) :
    (resC S g hV).range = omegaGroup Q hQ ∨
      (resC S g hV).range = TauCeti.QuadraticMap.orthogonalGroup Q := by
  have : Nontrivial (Vt S g t) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have h1 : omegaGroup Q hQ ≤ (resC S g hV).range :=
    hX ▸ RmodN_le_range_resC hCE H hNo C ht ht1 hVQ hΩ hN h8 hV
  have h2 := range_resC_le_orthogonalGroup H hNo C ht ht1 hVQ hΩ hV hsing
  have h3 := relIndex_omegaGroup Q hQ
  have h4 := Subgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [h3] at h4
  rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ h4) with h5 | h5
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h5) h1
  · right
    rw [h5] at h4
    exact le_antisymm h2 (Subgroup.relIndex_eq_one.mp (by omega))

theorem timmesfeld_7_7_of_omegaCase :
    ∃ q : QuadraticForm (ZMod 2) (Vt S g t), q.polarBilin.Nondegenerate ∧
      (Nonempty (S.Mbar ≃* Perm (Fin 3) × timmesfeldOmega (q : Vt S g t → ZMod 2)) ∨
        Nonempty (S.Mbar ≃* Perm (Fin 3) × timmesfeldIsometries (q : Vt S g t → ZMod 2))) := by
  obtain ⟨Q, hQ, -, hX, -, hsing⟩ := hΩ.exists_form
  have hV := (commSpace_t_eq H C ht ht1 hVQ).1
  obtain ⟨e₁⟩ := nonempty_mulEquiv_Mbar hCE H hNo C ht ht1 hVQ hΩ hN h8
  have hinj := resC_injective hCE H hNo C ht ht1 hVQ hΩ hN h8 hV
  let e₂ : Cbar S t ≃* (resC S g hV).range := MonoidHom.ofInjective hinj
  refine ⟨Q, hQ, ?_⟩
  rcases range_resC_eq hCE H hNo C ht ht1 hVQ hΩ hN h8 hV hX hsing with h | h
  · exact Or.inl ⟨e₁.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (e₂.trans (MulEquiv.subgroupCongr (h.trans (timmesfeldOmega_eq Q hQ).symm))))⟩
  · exact Or.inr ⟨e₁.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (e₂.trans (MulEquiv.subgroupCongr (h.trans (timmesfeldIsometries_eq Q).symm))))⟩

end Seven

theorem timmesfeld_7_7 (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hR : Rbar S g t ≠ S.Lbar g) (hN : Nbar S g t = zpowers t) (hn : 6 < S.width) :
    finrank (ZMod 2) (Vt S g t) = S.width ∧ Even S.width ∧
      ∃ q : QuadraticForm (ZMod 2) (Vt S g t), q.polarBilin.Nondegenerate ∧
        (Nonempty (S.Mbar ≃* Perm (Fin 3) × timmesfeldOmega (q : Vt S g t → ZMod 2)) ∨
          Nonempty (S.Mbar ≃* Perm (Fin 3) × timmesfeldIsometries (q : Vt S g t → ZMod 2))) := by
  obtain ⟨hVQ, hΩ, hw, h6 | ⟨h8, -, -, -⟩⟩ := timmesfeld_7_6 hCE H hNo C ht ht1 hR hN (by omega)
  · omega
  · obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
    exact ⟨hw.symm, ⟨m, by omega⟩,
      timmesfeld_7_7_of_omegaCase hCE H hNo C ht ht1 hVQ hΩ hN (by omega)⟩

theorem timmesfeldAlt3 (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hR : Rbar S g t ≠ S.Lbar g) (hN : Nbar S g t = zpowers t) (hn : 6 < S.width) :
    Bridge.TimmesfeldAlt3 S.width S.Mbar := by
  obtain ⟨hd, he, q, hq, h⟩ := timmesfeld_7_7 hCE H hNo C ht ht1 hR hN hn
  exact Bridge.TimmesfeldAlt3.of_space (by omega) he q hd
    ((Bridge.polarBilin_nondegenerate_iff q).mp hq) h

end CFSG.LargeExtraspecial.S7
