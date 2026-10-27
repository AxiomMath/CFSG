module

public import CFSG.LargeExtraspecial.S8Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {X : Type*} [Group X] {t x : X} (htt : t * t = 1)
    (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, ht2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · exact Or.inl (zpow_zero t)
  · exact Or.inr (zpow_one t)

variable (S) in
@[expose] noncomputable def CMt (t : S.O) : Subgroup S.O := S.Mbar ⊓ centralizer ({t} : Set S.O)

theorem mem_CMt {t x : S.O} : x ∈ CMt S t ↔ x ∈ S.Mbar ∧ x * t = t * x := by
  rw [CMt, mem_inf, mem_centralizer_singleton_iff]

theorem apply_mem_Vt_of_mem_CMt (haQ : g * S.z * g⁻¹ ∈ S.QG) {t x : S.O} (hx : x ∈ CMt S t)
    {v : S.Qt} (hv : v ∈ Vt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
  obtain ⟨hxM, hxt⟩ := mem_CMt.mp hx
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hxM
  exact apply_mem_Vt haQ hxt hv

variable (S g) in
@[expose] noncomputable def resCV (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    CMt S t →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  restrictHom (S.O.subtype.comp (CMt S t).subtype) (Vt S g t)
    (fun x _ hu => apply_mem_Vt_of_mem_CMt haQ x.2 hu)

theorem coe_resCV_apply (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (x : CMt S t) (v : Vt S g t) :
    ((resCV S g haQ t x v : Vt S g t) : S.Qt) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  rfl

theorem Rbar_le_CMt (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} : Rbar S g t ≤ CMt S t :=
  fun _ hx => mem_CMt.mpr ⟨Rbar_le_Mbar hx, commute_of_mem_Rbar haQ hx⟩

theorem apply_mem_orbit_of_mem_CMt (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (ht : t ∈ S.Lbar g) {x : S.O} (hx : x ∈ CMt S t) {v : S.Qt} (hv : v ∈ orbit S g t) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ orbit S g t := by
  obtain ⟨r, hr, rfl⟩ := hv
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (S.Mbar.mul_mem (mem_CMt.mp hx).1 (Rbar_le_Mbar hr))
  have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S k haQ, hk]
    rfl
  rw [e]
  refine hfus k ?_
  rw [← e]
  exact apply_mem_Vt_of_mem_CMt haQ hx (orbit_subset_Vt ht haQ ⟨r, hr, rfl⟩)

section Form

variable (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
  {Q : QuadraticForm (ZMod 2) (Vt S g t)}
  (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
  (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
    S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
include H hsing hfus

theorem Q_resCV_apply (x : CMt S t) (v : Vt S g t) : Q (resCV S g H.conj_mem t x v) = Q v := by
  have hsing' : ∀ w : Vt S g t, Q w = 0 ↔ w = 0 ∨ (w : S.Qt) ∈ orbit S g t := by
    intro w
    by_cases hw : w = 0
    · simp [hw]
    · rw [hsing w hw, mem_orbitOf_RmodN_iff H.conj_mem ht]
      simp [hw]
  have himp : ∀ (y : CMt S t) (w : Vt S g t), Q w = 0 → Q (resCV S g H.conj_mem t y w) = 0 := by
    intro y w hw
    rw [hsing'] at hw ⊢
    rcases hw with rfl | hw
    · exact Or.inl (map_zero _)
    · exact Or.inr (by
        rw [coe_resCV_apply]
        exact apply_mem_orbit_of_mem_CMt H.conj_mem hfus ht y.2 hw)
  have hinv : resCV S g H.conj_mem t x⁻¹ (resCV S g H.conj_mem t x v) = v := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rcases zmod2_eq_zero_or_eq_one (Q v) with h0 | h1
  · rw [h0]
    exact himp x v h0
  · rw [h1]
    rcases zmod2_eq_zero_or_eq_one (Q (resCV S g H.conj_mem t x v)) with h0' | h1'
    · have := himp x⁻¹ _ h0'
      rw [hinv, h1] at this
      exact absurd this one_ne_zero
    · exact h1'

theorem resCV_mem_orthogonalGroup (x : CMt S t) :
    resCV S g H.conj_mem t x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v =>
    Q_resCV_apply H ht hsing hfus x v

end Form

section Radical

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {Q : QuadraticForm (ZMod 2) (Vt S g t)}
  (hpol : Q.polarBilin = beta H C ht ht1 hVQ) (hE : LmodN S g t = pointRadical Q (aV ht))
  (hQa : Q (aV ht) = 0)
include H C ht ht1 hVQ hpol hE hQa

theorem exists_mem_Lbar_sub_sub_mem {u d : Vt S g t}
    (hu : (u : S.Qt) ∉ S.clSub (S.QG ⊓ S.Qa g)) (hd : (d : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    ∃ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u - d ∈
      (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  have hpolar : ∀ x y : Vt S g t, polar Q x y = beta H C ht ht1 hVQ x y := fun x y => by
    rw [← polarBilin_apply_apply, hpol]
  have had : polar Q (aV ht) d = 0 := by
    rw [hpolar]
    exact (beta_aV_eq_zero_iff H C ht ht1 hVQ d).mpr hd
  have hau : polar Q u (aV ht) = 1 := by
    rw [polar_comm, hpolar]
    exact zmod2_eq_one_of_ne_zero fun h0 => hu ((beta_aV_eq_zero_iff H C ht ht1 hVQ u).mp h0)
  have hEm : CFSG.ClassicalGroups.Orthogonal.eichler Q (aV ht) d ∈ LmodN S g t := by
    rw [hE]
    exact eichler_mem_pointRadical hQa had
  obtain ⟨l, hl, hlE⟩ := mem_LmodN.mp hEm
  refine ⟨l, hl, ?_⟩
  have h1 := hlE u
  rw [eichler_apply_zmod2 hQa had, hau, one_smul, mul_one] at h1
  rw [← h1]
  refine Submodule.mem_span_singleton.mpr ⟨polar Q u d + Q d, ?_⟩
  have e : ((aV ht : Vt S g t) : S.Qt) = S.cl (g * S.z * g⁻¹) := rfl
  rw [Submodule.coe_add, Submodule.coe_add, Submodule.coe_smul, e]
  abel

end Radical

theorem eq_t_of_commSpace_eq (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {τ : S.O} (hτL : τ ∈ S.Lbar g)
    (hτ : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t) : τ = t := by
  have hfix : fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = Wt S g t := by
    rw [fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate τ.2, hτ]
    rfl
  have hWt := (commSpace_t_eq H C ht ht1 hVQ).2
  have hmem : τ * t ∈ zpowers t := by
    refine mem_zpowers_of_fix_Wt H C ht ht1 hVQ (mul_mem hτL ht) fun w hw => ?_
    have h1 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := mem_fixSpace.mp (hWt ▸ hw)
    have h2 : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := mem_fixSpace.mp (hfix ▸ hw)
    change (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w
    rw [h1, h2]
  have hτt : τ ∈ zpowers t := by
    have := mul_mem hmem (inv_mem (mem_zpowers t))
    rwa [mul_inv_cancel_right] at this
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  rcases eq_one_or_eq_of_mem_zpowers htt hτt with rfl | h
  · exfalso
    have ha := cl_a_mem_Vt ht
    rw [← hτ] at ha
    have h0 : commSpace ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
      simp
    rw [h0, Submodule.mem_bot] at ha
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne ha
  · exact h

end CFSG.LargeExtraspecial.S8
