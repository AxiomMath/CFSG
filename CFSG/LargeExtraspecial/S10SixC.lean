module

public import CFSG.LargeExtraspecial.S10SixB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem orthogonal_sup_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (A A' : Submodule K V) :
    B.orthogonal (A ⊔ A') = B.orthogonal A ⊓ B.orthogonal A' := by
  ext w
  simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
      fun u hu => h u (Submodule.mem_sup_right hu)⟩
  · rintro ⟨h, h'⟩ u hu
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add, LinearMap.add_apply, h a ha, h' a' ha', add_zero]

theorem finrank_map_le_add_of_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) {U P : Submodule K V} (hUP : U ≤ P) :
    finrank K (P.map f) ≤ finrank K (U.map f) + (finrank K P - finrank K U) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  have hP : P = U ⊔ (C ⊓ P) := by
    rw [← sup_inf_assoc_of_le C hUP, hC.sup_eq_top, top_inf_eq]
  have h1 : P.map f ≤ U.map f ⊔ (C ⊓ P).map f := by
    rw [← Submodule.map_sup, ← hP]
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (U.map f) ((C ⊓ P).map f)
  have h3 := Submodule.finrank_map_le f (C ⊓ P)
  have h4 : finrank K ↥(C ⊓ P) + finrank K U ≤ finrank K P := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U (C ⊓ P)
    have hd : U ⊓ (C ⊓ P) = ⊥ := by
      rw [← inf_assoc, hC.inf_eq_bot, bot_inf_eq]
    rw [← hP, hd, finrank_bot] at this
    omega
  have h5 := Submodule.finrank_mono h1
  omega

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Vt_le_Wt_of_mem_Nbar {τ : S.O} (Y : Hyp10 S g τ) (hτN : τ ∈ Nbar S g t) :
    Vt S g t ≤ Wt S g τ := by
  rw [← (commSpace_t_eq Y.H Y.C Y.ht Y.ht1 Y.hVQ).2]
  intro v hv
  exact mem_fixSpace.mpr ((mem_Nbar.mp hτN).2 v hv)

theorem eq_of_Vt_eq {τ : S.O} (X : Hyp10 S g t) (Y : Hyp10 S g τ)
    (hV : Vt S g t = Vt S g τ) : τ = t := by
  have hW : Wt S g t = Wt S g τ := by rw [Wt, Wt, hV]
  have hft := (commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ).2
  have hfτ := (commSpace_t_eq Y.H Y.C Y.ht Y.ht1 Y.hVQ).2
  have hagree : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g),
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) p := by
    intro p hp
    have h1 := Lbar_apply_sub_mem_span' X.haQ hp X.ht
    have h2 := Lbar_apply_sub_mem_span' X.haQ hp Y.ht
    have hiff : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p ↔ (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
      rw [← mem_fixSpace, ← mem_fixSpace, hft, hfτ, hW]
    rcases mem_span_cl_iff.mp h1 with h1 | h1 <;> rcases mem_span_cl_iff.mp h2 with h2 | h2
    · rw [sub_eq_zero.mp h1, sub_eq_zero.mp h2]
    · exact absurd (hiff.mp (sub_eq_zero.mp h1))
        (fun h => cl_conj_z_ne_zero S X.H.conj_mem X.H.conj_ne (by rw [← h2, h, sub_self]))
    · exact absurd (hiff.mpr (sub_eq_zero.mp h2))
        (fun h => cl_conj_z_ne_zero S X.H.conj_mem X.H.conj_ne (by rw [← h1, h, sub_self]))
    · rw [← sub_eq_zero, ← sub_sub_sub_cancel_right _ _ p, h1, h2, sub_self]
  have hone := X.C.faithful (t⁻¹ * τ) (mul_mem (inv_mem X.ht) Y.ht) fun p hp => by
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hagree p hp, inv_apply_apply_O]
  calc τ = t * (t⁻¹ * τ) := by group
    _ = t := by rw [hone, mul_one]

theorem le_span_of_invariant (X : Hyp10 S g t) {D : Submodule (ZMod 2) S.Qt}
    (hD : finrank (ZMod 2) D ≤ 1)
    (hinv : ∀ l ∈ S.Lbar g, ∀ v ∈ D, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ D) :
    D ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  intro v hv
  rw [← X.H.fixSub_eq]
  intro l hl
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hspan : (ZMod 2) ∙ v = D := by
    refine Submodule.eq_of_le_of_finrank_le
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hv) ?_
    rw [finrank_span_singleton hv0]
    exact hD
  have hlv := hinv l hl v hv
  rw [← hspan] at hlv
  rcases mem_span_cl_iff.mp hlv with h | h
  · exfalso
    apply hv0
    have := congrArg (((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h
    rwa [inv_apply_apply_O, map_zero] at this
  · exact h

theorem finrank_Vt_inf_Vt_le (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {τ : S.O}
    (Y : Hyp10 S g τ) (hτN : τ ∈ Nbar S g t) (hτt : τ ≠ t) :
    finrank (ZMod 2) ↥(Vt S g t ⊓ Vt S g τ) ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have hle4 : finrank (ZMod 2) ↥(Vt S g t ⊓ Vt S g τ) ≤ 4 := by
    rw [← X.h4]
    exact Submodule.finrank_mono inf_le_left
  have hfτ := (commSpace_t_eq Y.H Y.C Y.ht Y.ht1 Y.hVQ).2
  have hVne : Vt S g t ≠ Vt S g τ := fun h => hτt (eq_of_Vt_eq X Y h)
  have h3 : finrank (ZMod 2) ↥(Vt S g t ⊓ Vt S g τ) = 3 := by
    rcases (by omega : finrank (ZMod 2) ↥(Vt S g t ⊓ Vt S g τ) = 3 ∨
      finrank (ZMod 2) ↥(Vt S g t ⊓ Vt S g τ) = 4) with h | h
    · exact h
    · exfalso
      apply hVne
      have e1 : Vt S g t ⊓ Vt S g τ = Vt S g t :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [h, X.h4])
      have e2 : Vt S g t ⊓ Vt S g τ = Vt S g τ :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [h, Y.h4])
      rw [← e1, e2]
  have h5 : finrank (ZMod 2) ↥(Vt S g t ⊔ Vt S g τ) = 5 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t) (Vt S g τ)
    rw [X.h4, Y.h4, h3] at this
    omega
  have hn := S.finrank_Qt_eq_two_mul_width
  have hWW : Wt S g t ⊓ Wt S g τ =
      LinearMap.BilinForm.orthogonal S.q.polarBilin (Vt S g t ⊔ Vt S g τ) := by
    rw [orthogonal_sup_eq]
    rfl
  have hdimWW : finrank (ZMod 2) ↥(Wt S g t ⊓ Wt S g τ) + 5 = 2 * S.width := by
    rw [hWW, LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate, h5, hn]
    have := Submodule.finrank_le (Vt S g t ⊔ Vt S g τ)
    rw [hn, h5] at this
    omega
  have hW := finrank_Wt (S := S) (g := g) (t := t)
  have hWτ := finrank_Wt (S := S) (g := g) (t := τ)
  rw [X.h4, hn] at hW
  rw [Y.h4, hn] at hWτ
  have hD1 := finrank_map_le_add_of_le
    (((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)
    (inf_le_left : Wt S g t ⊓ Wt S g τ ≤ Wt S g t)
  have hzero : (Wt S g t ⊓ Wt S g τ).map
      (((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    have := mem_fixSpace.mp (hfτ ▸ hw.2 : w ∈ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    simp [this]
  rw [hzero, finrank_bot] at hD1
  have hDa : (Wt S g t).map (((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤
      (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    refine le_span_of_invariant X (by omega) ?_
    rintro l hl _ ⟨w, hw, rfl⟩
    refine ⟨(l : S.Qt ≃ₗ[ZMod 2] S.Qt) w, apply_mem_Wt X.H (Lbar_le_Rbar X.ht hl) hw, ?_⟩
    have hc : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
        (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, S4.Lbar_comm S X.haQ Y.ht hl]
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub, hc]
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  have hbV := cl_mem_Vt (mem_Lbar_mul_of_mem_Rbar X.H X.ht hk)
  have haPb := S.cl_not_mem_clSub_of_not_mem_Qa X.haQ X.H.conj_ne k.2 hb
  have hyP : ∀ q ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t,
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) q = q := by
    intro q hq
    have h1 : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) :=
      hDa ⟨q, hq.2, rfl⟩
    have h2 : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) :=
      sub_mem (Nbar_apply_mem_clSub (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne)
        hbV hτN hq.1) hq.1
    rcases mem_span_cl_iff.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (h ▸ h2) haPb
  have hfix := fix_Wt_of_fix hCE X hk hb (y := τ) (fun l hl => S4.Lbar_comm S X.haQ Y.ht hl)
    (fun v hv => (mem_Nbar.mp hτN).2 v hv) hyP
  have hWle : Wt S g t ≤ Wt S g τ := fun w hw => hfτ ▸ mem_fixSpace.mpr (hfix w hw)
  have hWeq : Wt S g t = Wt S g τ := Submodule.eq_of_le_of_finrank_le hWle (by omega)
  apply hVne
  rw [← orthogonal_Wt (g := g) t, ← orthogonal_Wt (g := g) τ, hWeq]

end CFSG.LargeExtraspecial.S10
