module

public import CFSG.LargeExtraspecial.S14NQSixModB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.S2
open CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

namespace Plus6

variable {ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)} {p p₁ e₁ f₁ e₂ f₂ : V}
  (P : Plus6 ρ p p₁ e₁ f₁ e₂ f₂)
include P

omit [FiniteDimensional (ZMod 2) M] in
theorem exists_apply_eq : ∃ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) p = p₁ := by
  have hmem0 : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hF0 : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have h3 : 3 ≤ finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) := by
    rw [perp_bot, finrank_top, P.hV]; norm_num
  obtain ⟨g, hg, hgp⟩ := exists_mem_radGen_apply_eq hq hF0 h3 (hmem0 p) (hmem0 p₁) P.hp0
    P.p₁_ne_zero P.hp P.hp₁
  exact ⟨⟨g, (mem_omegaFix.mp (radGen_le_omegaFix hq ⊥ hg)).1⟩, hgp⟩

omit [FiniteDimensional (ZMod 2) M] in
theorem A0_inf_A0 : A0 ρ p ⊓ A0 ρ p₁ = ⊥ := by
  have h := P.hD.2
  rw [top_inf_eq, top_inf_eq] at h
  exact h

omit [FiniteDimensional (ZMod 2) M] in
theorem sup_map_inf_A0 {U : Submodule (ZMod 2) M} (hUA : U ≤ A0 ρ p) (g : omegaGroup q hq)
    (hgp : (g : V ≃ₗ[ZMod 2] V) p = p₁) :
    (U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M)) ⊓ A0 ρ p = U := by
  have hB : U.map (ρ g : M →ₗ[ZMod 2] M) ≤ A0 ρ p₁ := by
    rintro _ ⟨u, hu, rfl⟩
    have := mapsTo_fixOf_radFix ρ P.hp0 P.hp g (hUA hu)
    rw [hgp] at this
    exact this
  have h0 : U.map (ρ g : M →ₗ[ZMod 2] M) ⊓ A0 ρ p = ⊥ := by
    rw [eq_bot_iff, ← P.A0_inf_A0]
    exact fun v hv => ⟨hv.2, hB hv.1⟩
  rw [sup_inf_assoc_of_le _ hUA, h0, sup_bot_eq]

theorem eq_of_inf_A0_eq {N W : Submodule (ZMod 2) M}
    (hN : ∀ x : omegaGroup q hq, ∀ v ∈ N, ρ x v ∈ N)
    (hW : ∀ x : omegaGroup q hq, ∀ v ∈ W, ρ x v ∈ W)
    (h : N ⊓ A0 ρ p = W ⊓ A0 ρ p) : N = W := by
  have hNW : ∀ x : omegaGroup q hq, ∀ v ∈ N ⊓ W, ρ x v ∈ N ⊓ W := fun x v hv =>
    ⟨hN x v hv.1, hW x v hv.2⟩
  have hi : N ⊓ W ⊓ A0 ρ p = N ⊓ A0 ρ p := by
    refine le_antisymm (inf_le_inf_right _ inf_le_left) fun v hv => ?_
    have hv' : v ∈ W ⊓ A0 ρ p := h ▸ hv
    exact ⟨⟨hv.1, hv'.1⟩, hv.2⟩
  have d1 := (P.dims hNW).2
  have d2 := (P.dims hN).2
  have d3 := (P.dims hW).2
  rw [hi, h] at d1
  rw [h] at d2
  have e1 : N ⊓ W = N := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  have e2 : N ⊓ W = W := Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  rw [← e1, e2]

theorem eq_or_eq_of_finrank_eq_two {T : Submodule (ZMod 2) M} (hTA : T ≤ A0 ρ p)
    (hTz : ∀ v ∈ T, ρ (zElt hq e₁ f₁ e₂ f₂) v ∈ T) (hT : finrank (ZMod 2) T = 2) :
    T = Unorm ρ p e₁ f₁ e₂ f₂ ∨ T = Ufix ρ p e₁ f₁ e₂ f₂ := by
  have hsum := ord3_finrank P.z_cube hTz
  obtain ⟨k, hk⟩ := two_dvd_finrank_of_le_normKer (S := T ⊓ normKer (ρ (zElt hq e₁ f₁ e₂ f₂)))
    (fun v hv => ⟨hTz v hv.1, normKer_mapsTo hv.2⟩) inf_le_right
  have hk1 : k ≤ 1 := by omega
  interval_cases k
  · right
    have h1 : T ⊓ fixSpace (ρ (zElt hq e₁ f₁ e₂ f₂)) = T :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    have hle : T ≤ Ufix ρ p e₁ f₁ e₂ f₂ := fun v hv => ⟨hTA hv, (h1.ge hv).2⟩
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hT, P.finrank_fix_z])
  · left
    have h1 : T ⊓ normKer (ρ (zElt hq e₁ f₁ e₂ f₂)) = T :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    have hle : T ≤ Unorm ρ p e₁ f₁ e₂ f₂ := fun v hv => ⟨hTA hv, (h1.ge hv).2⟩
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hT, P.finrank_normKer_z])

theorem sup_map_props {U : Submodule (ZMod 2) M} (hUA : U ≤ A0 ρ p)
    (hU : ∀ y : omegaGroup q hq,
      (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) →
        ∀ v ∈ U, ρ y v ∈ U)
    (hU2 : finrank (ZMod 2) U = 2) (g : omegaGroup q hq) (hgp : (g : V ≃ₗ[ZMod 2] V) p = p₁) :
    (∀ x : omegaGroup q hq, ∀ v ∈ U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M),
      ρ x v ∈ U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M)) ∧
      (U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M)) ⊓ A0 ρ p = U ∧
      finrank (ZMod 2) (U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M) : Submodule (ZMod 2) M) = 4 := by
  have hinv := fun x => P.mapsTo_sup hUA hU g hgp x
  have hi := P.sup_map_inf_A0 hUA g hgp
  refine ⟨hinv, hi, ?_⟩
  rw [(P.dims hinv).2, hi, hU2]

theorem lattice : ∃ W₁ W₂ : Submodule (ZMod 2) M,
    (∀ x : omegaGroup q hq, ∀ v ∈ W₁, ρ x v ∈ W₁) ∧
      (∀ x : omegaGroup q hq, ∀ v ∈ W₂, ρ x v ∈ W₂) ∧
      finrank (ZMod 2) W₁ = 4 ∧ finrank (ZMod 2) W₂ = 4 ∧ W₁ ⊓ W₂ = ⊥ ∧
      ∀ N : Submodule (ZMod 2) M, (∀ x : omegaGroup q hq, ∀ v ∈ N, ρ x v ∈ N) →
        N = ⊥ ∨ N = W₁ ∨ N = W₂ ∨ N = ⊤ := by
  obtain ⟨g, hgp⟩ := P.exists_apply_eq
  obtain ⟨h1inv, h1A, h1d⟩ := P.sup_map_props (U := Unorm ρ p e₁ f₁ e₂ f₂) inf_le_left
    (fun y hy v hv => P.mapsTo_Unorm_of_fix hy hv) P.finrank_normKer_z g hgp
  obtain ⟨h2inv, h2A, h2d⟩ := P.sup_map_props (U := Ufix ρ p e₁ f₁ e₂ f₂) inf_le_left
    (fun y hy v hv => P.mapsTo_Ufix_of_fix hy hv) P.finrank_fix_z g hgp
  refine ⟨_, _, h1inv, h2inv, h1d, h2d, ?_, fun N hN => ?_⟩
  · have hinv : ∀ x : omegaGroup q hq, ∀ v ∈ (Unorm ρ p e₁ f₁ e₂ f₂ ⊔
        (Unorm ρ p e₁ f₁ e₂ f₂).map (ρ g : M →ₗ[ZMod 2] M)) ⊓ (Ufix ρ p e₁ f₁ e₂ f₂ ⊔
        (Ufix ρ p e₁ f₁ e₂ f₂).map (ρ g : M →ₗ[ZMod 2] M)), ρ x v ∈ (Unorm ρ p e₁ f₁ e₂ f₂ ⊔
        (Unorm ρ p e₁ f₁ e₂ f₂).map (ρ g : M →ₗ[ZMod 2] M)) ⊓ (Ufix ρ p e₁ f₁ e₂ f₂ ⊔
        (Ufix ρ p e₁ f₁ e₂ f₂).map (ρ g : M →ₗ[ZMod 2] M)) :=
      fun x v hv => ⟨h1inv x v hv.1, h2inv x v hv.2⟩
    have h := (P.dims hinv).2
    rw [inf_inf_distrib_right, h1A, h2A, ord3_inf_eq_bot, finrank_bot, mul_zero] at h
    exact Submodule.finrank_eq_zero.mp h
  · obtain ⟨⟨c, hc⟩, hdT⟩ := P.dims hN
    have hTle : finrank (ZMod 2) (N ⊓ A0 ρ p : Submodule (ZMod 2) M) ≤ 4 :=
      (Submodule.finrank_mono inf_le_right).trans P.finrank_A0.le
    have hTz : ∀ v ∈ N ⊓ A0 ρ p, ρ (zElt hq e₁ f₁ e₂ f₂) v ∈ N ⊓ A0 ρ p := fun v hv =>
      ⟨hN _ v hv.1, mapsTo_A0 ρ P.hp0 P.hp _ (apply_p_of_mem_fixGroup P.z_mem_fixGroup) hv.2⟩
    have hcases : finrank (ZMod 2) (N ⊓ A0 ρ p : Submodule (ZMod 2) M) = 0 ∨
        finrank (ZMod 2) (N ⊓ A0 ρ p : Submodule (ZMod 2) M) = 2 ∨
        finrank (ZMod 2) (N ⊓ A0 ρ p : Submodule (ZMod 2) M) = 4 := by omega
    rcases hcases with h0 | h2 | h4
    · left
      exact Submodule.finrank_eq_zero.mp (by omega)
    · rcases P.eq_or_eq_of_finrank_eq_two inf_le_right hTz h2 with hU | hU
      · exact Or.inr (Or.inl (P.eq_of_inf_A0_eq hN h1inv (by rw [h1A]; exact hU)))
      · exact Or.inr (Or.inr (Or.inl (P.eq_of_inf_A0_eq hN h2inv (by rw [h2A]; exact hU))))
    · right; right; right
      exact Submodule.eq_top_of_finrank_eq (by rw [P.hM]; omega)

end Plus6

end CFSG.LargeExtraspecial.S14
