module

public import CFSG.GH74.GLS.C3.Layer1.P34RealAut

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

section Transport

variable {M M₂ : Type} [Group M] [Group M₂] (ψ : M ≃* M₂)

theorem mem_map_equiv_iff {S : Subgroup M} (x : M) : ψ x ∈ S.map ψ.toMonoidHom ↔ x ∈ S := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem map_inf_equiv (S T : Subgroup M) :
    (S ⊓ T).map ψ.toMonoidHom = S.map ψ.toMonoidHom ⊓ T.map ψ.toMonoidHom :=
  Subgroup.map_inf _ _ _ ψ.injective

theorem map_sup_zpowers_equiv (S : Subgroup M) (a : M) :
    (S ⊔ zpowers a).map ψ.toMonoidHom = S.map ψ.toMonoidHom ⊔ zpowers (ψ a) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  rfl

noncomputable def mapEquiv (S : Subgroup M) : ↥S ≃* ↥(S.map ψ.toMonoidHom) :=
  Subgroup.equivMapOfInjective S ψ.toMonoidHom ψ.injective

theorem isDihedralTwoGroup_of_equiv' {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {n : ℕ}
    (h : IsDihedralTwoGroup Y' n) : IsDihedralTwoGroup Y n := by
  obtain ⟨hn, k, hk, hk2, ⟨φ⟩⟩ := h
  exact ⟨hn, k, hk, hk2, ⟨e.trans φ⟩⟩

theorem AutP34G.of_equiv {I B : Subgroup M} {α z : M}
    (h : AutP34G (I.map ψ.toMonoidHom) (B.map ψ.toMonoidHom) (ψ α) (ψ z)) : AutP34G I B α z := by
  have hBI : ∀ x : M, ψ x ∈ B.map ψ.toMonoidHom ⊓ I.map ψ.toMonoidHom ↔ x ∈ B ⊓ I := by
    intro x
    rw [← map_inf_equiv]
    exact mem_map_equiv_iff ψ x
  have hB : ∀ x : M, ψ x ∈ B.map ψ.toMonoidHom ↔ x ∈ B := fun x => mem_map_equiv_iff ψ x
  have hI : ∀ x : M, ψ x ∈ I.map ψ.toMonoidHom ↔ x ∈ I := fun x => mem_map_equiv_iff ψ x
  have hsup : ∀ (a x : M), ψ x ∈ (B.map ψ.toMonoidHom ⊓ I.map ψ.toMonoidHom) ⊔ zpowers (ψ a) ↔
      x ∈ (B ⊓ I) ⊔ zpowers a := by
    intro a x
    rw [← map_inf_equiv, ← map_sup_zpowers_equiv]
    exact mem_map_equiv_iff ψ x
  have hsq : ∀ x : M, ψ x * ψ x = 1 ↔ x * x = 1 := by
    intro x
    rw [← map_mul, ← map_one ψ]
    exact ψ.injective.eq_iff
  have hord : ∀ x : M, orderOf (ψ x) = orderOf x := fun x => MulEquiv.orderOf_eq ψ x
  refine
    { dihedral := ?_
      z_mem := (hBI z).1 h.z_mem
      z_order := by rw [← hord]; exact h.z_order
      z_cent := ?_
      z_unique := ?_
      abelian := ?_
      invol_coset := ?_
      invol_dih := ?_
      cent_B := ?_
      conj_z := ?_
      fus_alpha := ?_
      shear := ?_ }
  · obtain ⟨n, hn, hd⟩ := h.dihedral
    refine ⟨n, hn, isDihedralTwoGroup_of_equiv' ((mapEquiv ψ (B ⊓ I)).trans
      (MulEquiv.subgroupCongr (map_inf_equiv ψ B I))) hd⟩
  · intro q hq
    apply ψ.injective
    rw [map_mul, map_mul]
    exact h.z_cent (ψ q) ((hBI q).2 hq)
  · intro w hw hwc
    have := h.z_unique (ψ w) ((hBI w).2 hw) (fun q hq => by
      obtain ⟨q', hq', rfl⟩ : ∃ q', q' ∈ B ⊓ I ∧ ψ q' = q := by
        refine ⟨ψ.symm q, (hBI _).1 (by simpa using hq), by simp⟩
      rw [← map_mul, ← map_mul, hwc q' hq'])
    rcases this with h1 | h1
    · left
      exact ψ.injective (by rw [h1, map_one])
    · right
      exact ψ.injective h1
  · intro a ha b hb
    have := h.abelian (ψ a) ((hB a).2 ha) (ψ b) ((hB b).2 hb)
    have e : ψ (a * b * a⁻¹ * b⁻¹) = ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ := by
      simp only [map_mul, map_inv]
    exact (hBI _).1 (by rw [e]; exact this)
  · intro u hu hu2 hunot u' hu' hu'2 hu'not
    have := h.invol_coset (ψ u) ((hB u).2 hu) ((hsq u).2 hu2) (fun hmem => hunot ((hsup α u).1 hmem))
      (ψ u') ((hB u').2 hu') ((hsq u').2 hu'2) (fun hmem => hu'not ((hsup α u').1 hmem))
    have e : ψ (u' * u⁻¹) = ψ u' * (ψ u)⁻¹ := by simp only [map_mul, map_inv]
    exact (hBI _).1 (by rw [e]; exact this)
  · intro u hu hu2 hunot
    obtain ⟨n, hn, ⟨e⟩⟩ := h.invol_dih (ψ u) ((hB u).2 hu) ((hsq u).2 hu2)
      (fun hmem => hunot ((hsup α u).1 hmem))
    refine ⟨n, hn, ⟨?_⟩⟩
    refine ((mapEquiv ψ ((B ⊓ I) ⊔ zpowers u)).trans (MulEquiv.subgroupCongr ?_)).trans e
    rw [map_sup_zpowers_equiv, map_inf_equiv]
  · intro w hw hwc
    have := h.cent_B (ψ w) ((hB w).2 hw) (fun q hq => by
      obtain ⟨q', hq', rfl⟩ : ∃ q', q' ∈ B ⊓ I ∧ ψ q' = q := by
        refine ⟨ψ.symm q, (hBI _).1 (by simpa using hq), by simp⟩
      rw [← map_mul, ← map_mul, hwc q' hq'])
    have hsupz : ∀ x : M, ψ x ∈ zpowers (ψ α) ⊔ zpowers (ψ z) ↔ x ∈ zpowers α ⊔ zpowers z := by
      intro x
      have := mem_map_equiv_iff ψ (S := zpowers α ⊔ zpowers z) x
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
      exact this
    exact (hsupz w).1 this
  · intro p hp hp2
    obtain ⟨g, hg, hgp⟩ := h.conj_z (ψ p) ((hBI p).2 hp) (by rw [hord]; exact hp2)
    refine ⟨ψ.symm g, (hI _).1 (by simpa using hg), ?_⟩
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hgp]
  · intro v hv hv2
    obtain ⟨g, hg, hgv⟩ := h.fus_alpha (ψ v) ((hBI v).2 hv) (by rw [hord]; exact hv2)
    refine ⟨ψ.symm g, (hI _).1 (by simpa using hg), ?_⟩
    rcases hgv with h1 | h1
    · left
      apply ψ.injective
      rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h1
    · right
      apply ψ.injective
      rw [map_mul, map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h1
  · intro σ' hσ' hσ'2 hσ'I hσ'c
    obtain ⟨p, hp, hp2, g, hg, hgσ⟩ := h.shear (ψ σ') ((hB σ').2 hσ') (by rw [hord]; exact hσ'2)
      (fun hmem => hσ'I ((hI σ').1 hmem)) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ : ∃ q', q' ∈ B ⊓ I ∧ ψ q' = q := by
          refine ⟨ψ.symm q, (hBI _).1 (by simpa using hq), by simp⟩
        rw [← map_mul, ← map_mul, hσ'c q' hq'])
    obtain ⟨p', hp', rfl⟩ : ∃ p', p' ∈ B ⊓ I ∧ ψ p' = p :=
      ⟨ψ.symm p, (hBI _).1 (by simpa using hp), by simp⟩
    refine ⟨p', hp', by rw [← hord]; exact hp2, ψ.symm g, (hI _).1 (by simpa using hg), ?_⟩
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_mul]
    exact hgσ

end Transport

end CFSG.GH74.GLS.C3.Layer1.P34Real
