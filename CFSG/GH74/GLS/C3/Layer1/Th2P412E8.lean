module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412Ev
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt CFSG.GH74.GLS.Th2.P412

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

@[expose] def Esub (x z a s₁ : G) : Subgroup G := zpowers (tt a s₁ s₁) ⊔ (zpowers x ⊔ zpowers z)

theorem tt_one_one (a : G) : tt a (1 : G) 1 = 1 := by unfold tt; group

theorem tt_z_one (a z : G) : tt a z (1 : G) = z := by unfold tt; group

theorem tt_zs_s (a z s₁ : G) : tt a (z * s₁) s₁ = z * tt a s₁ s₁ := by
  unfold tt
  group

theorem x_mem_Esub (x z a s₁ : G) : x ∈ Esub x z a s₁ :=
  Subgroup.mem_sup_right (Subgroup.mem_sup_left (mem_zpowers x))

theorem z_mem_Esub (x z a s₁ : G) : z ∈ Esub x z a s₁ :=
  Subgroup.mem_sup_right (Subgroup.mem_sup_right (mem_zpowers z))

theorem y0_mem_Esub (x z a s₁ : G) : tt a s₁ s₁ ∈ Esub x z a s₁ :=
  Subgroup.mem_sup_left (mem_zpowers _)

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem T_comm_x [Finite G] {t : G} (ht : t ∈ T) : t * x = x * t :=
  Subgroup.mem_centralizer_singleton_iff.1 (F.T_le_C ht)

theorem T_comm_z [Finite G] {t : G} (ht : t ∈ T) : t * z = z * t := by
  have h := F.T_central_z t ht
  calc t * z = (t * z * t⁻¹) * t := by group
    _ = z * t := by rw [h]

theorem x_ne_z [Finite G] : x ≠ z := by
  intro h
  have : x ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨h ▸ F.z_mem, F.x_mem⟩
  rw [F.core.P_inf_conj, Subgroup.mem_bot] at this
  exact F.x_ne this

theorem tt_one_z : tt a (1 : G) z = x := by unfold tt; rw [F.a_z_a, one_mul]

theorem xz_comm [Finite G] : ∀ a' ∈ zpowers x, ∀ b ∈ zpowers z, a' * b = b * a' := by
  intro a' ha b hb
  rcases mem_zpowers_of_sq F.x_sq ha with rfl | rfl <;>
    rcases mem_zpowers_of_sq F.z_sq hb with rfl | rfl
  · simp
  · simp
  · simp
  · exact F.zx_comm.symm

theorem mem_V4 [Finite G] {e : G} (he : e ∈ zpowers x ⊔ zpowers z) :
    e = 1 ∨ e = x ∨ e = z ∨ e = x * z := by
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.xz_comm he
  rcases mem_zpowers_of_sq F.x_sq hf₁ with rfl | rfl <;>
    rcases mem_zpowers_of_sq F.z_sq hf₂ with rfl | rfl
  · left; simp
  · right; right; left; simp
  · right; left; simp
  · right; right; right; rfl

theorem V4_card [Finite G] : Nat.card ↥(zpowers x ⊔ zpowers z) = 4 := by
  have hd : zpowers x ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rcases mem_zpowers_of_sq F.x_sq hu.1 with rfl | rfl
    · exact one_mem _
    · rcases mem_zpowers_of_sq F.z_sq hu.2 with h | h
      · exact absurd h F.x_ne
      · exact absurd h F.x_ne_z
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact F.x_sq) F.x_ne
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact F.z_sq) F.z_ne
  rw [card_sup_of_commute_of_disjoint F.xz_comm hd, Nat.card_zpowers, Nat.card_zpowers, hxo, hzo]

theorem y0_not_mem_V4 [Finite G] {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁1 : s₁ ≠ 1) (hs₁z : s₁ ≠ z) :
    tt a s₁ s₁ ∉ zpowers x ⊔ zpowers z := by
  intro h
  have hP1 : (1 : G) ∈ T ⊓ K := one_mem _
  rcases F.mem_V4 h with h1 | h1 | h1 | h1
  · have := F.tt_inj hs₁ hP1 hs₁ hP1 (h1.trans (tt_one_one a).symm)
    exact hs₁1 this.1
  · have := F.tt_inj hs₁ hP1 hs₁ F.z_mem (h1.trans F.tt_one_z.symm)
    exact hs₁1 this.1
  · have := F.tt_inj hs₁ F.z_mem hs₁ hP1 (h1.trans (tt_z_one a z).symm)
    exact hs₁z this.1
  · have hxz : x * z = tt a z z := by rw [F.tt_zz, F.zx_comm]
    have := F.tt_inj hs₁ F.z_mem hs₁ F.z_mem (h1.trans hxz)
    exact hs₁z this.1

theorem y0_sq [Finite G] {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁2 : s₁ * s₁ = 1) :
    tt a s₁ s₁ * tt a s₁ s₁ = 1 := F.tt_sq hs₁ hs₁ hs₁2 hs₁2

theorem y0_comm_V4 [Finite G] {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁2 : s₁ * s₁ = 1) :
    ∀ a' ∈ zpowers (tt a s₁ s₁), ∀ b ∈ zpowers x ⊔ zpowers z, a' * b = b * a' := by
  have hy0T : tt a s₁ s₁ ∈ T := F.tt_mem_T hs₁ hs₁
  have hle : zpowers x ⊔ zpowers z ≤ centralizer ({tt a s₁ s₁} : Set G) := by
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (F.T_comm_x hy0T).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (F.T_comm_z hy0T).symm
  intro a' ha b hb
  rcases mem_zpowers_of_sq (F.y0_sq hs₁ hs₁2) ha with rfl | rfl
  · simp
  · exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hb)).symm

theorem Esub_card [Finite G] {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁2 : s₁ * s₁ = 1) (hs₁1 : s₁ ≠ 1)
    (hs₁z : s₁ ≠ z) : Nat.card ↥(Esub x z a s₁) = 8 := by
  have hy0V4 := F.y0_not_mem_V4 hs₁ hs₁1 hs₁z
  have hd : zpowers (tt a s₁ s₁) ⊓ (zpowers x ⊔ zpowers z) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rcases mem_zpowers_of_sq (F.y0_sq hs₁ hs₁2) hu.1 with rfl | rfl
    · exact one_mem _
    · exact absurd hu.2 hy0V4
  have hy0o : orderOf (tt a s₁ s₁) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact F.y0_sq hs₁ hs₁2) (fun h => hy0V4 (h ▸ one_mem _))
  unfold Esub
  rw [card_sup_of_commute_of_disjoint (F.y0_comm_V4 hs₁ hs₁2) hd, Nat.card_zpowers, hy0o,
    F.V4_card]

theorem Esub_el [Finite G] {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁2 : s₁ * s₁ = 1) :
    CFSG.IsElementaryAbelian 2 ↥(Esub x z a s₁) := by
  have hV4 : CFSG.IsElementaryAbelian 2 ↥(zpowers x ⊔ zpowers z) :=
    isElementaryAbelian_sup_of_commute (isElementaryAbelian_zpowers_of_sq F.x_sq)
      (isElementaryAbelian_zpowers_of_sq F.z_sq) F.xz_comm
  exact isElementaryAbelian_sup_of_commute (isElementaryAbelian_zpowers_of_sq (F.y0_sq hs₁ hs₁2))
    hV4 (F.y0_comm_V4 hs₁ hs₁2)

theorem Esub_le_T [Finite G] {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) : Esub x z a s₁ ≤ T :=
  sup_le (zpowers_le.2 (F.tt_mem_T hs₁ hs₁))
    (sup_le (zpowers_le.2 F.x_mem_T) (zpowers_le.2 F.z_mem.1))

theorem mem_Esub_cases [Finite G] {s₁ e : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁2 : s₁ * s₁ = 1)
    (he : e ∈ Esub x z a s₁) :
    e = 1 ∨ e = x ∨ e = z ∨ e = x * z ∨ e = tt a s₁ s₁ ∨ e = tt a s₁ s₁ * x ∨
      e = tt a s₁ s₁ * z ∨ e = tt a s₁ s₁ * (x * z) := by
  obtain ⟨g, hg, f, hf, rfl⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute (F.y0_comm_V4 hs₁ hs₁2) he
  rcases mem_zpowers_of_sq (F.y0_sq hs₁ hs₁2) hg with rfl | rfl <;>
    rcases F.mem_V4 hf with rfl | rfl | rfl | rfl <;> simp

theorem tt_s_zs [Finite G] {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) :
    tt a s₁ (z * s₁) = x * tt a s₁ s₁ := by
  unfold tt
  have hc : s₁ * x = x * s₁ := F.core.comm_P_conj s₁ hs₁ x F.x_mem
  have e : a⁻¹ * (z * s₁) * a = x * (a⁻¹ * s₁ * a) := by
    rw [← F.a_z_a]
    group
  rw [e]
  calc s₁ * (x * (a⁻¹ * s₁ * a)) = (s₁ * x) * (a⁻¹ * s₁ * a) := by group
    _ = (x * s₁) * (a⁻¹ * s₁ * a) := by rw [hc]
    _ = x * (s₁ * (a⁻¹ * s₁ * a)) := by group

theorem tt_zs_zs [Finite G] {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) :
    tt a (z * s₁) (z * s₁) = (z * x) * tt a s₁ s₁ := by
  unfold tt
  have hc : s₁ * x = x * s₁ := F.core.comm_P_conj s₁ hs₁ x F.x_mem
  have e : a⁻¹ * (z * s₁) * a = x * (a⁻¹ * s₁ * a) := by
    rw [← F.a_z_a]
    group
  rw [e]
  calc z * s₁ * (x * (a⁻¹ * s₁ * a)) = z * ((s₁ * x) * (a⁻¹ * s₁ * a)) := by group
    _ = z * ((x * s₁) * (a⁻¹ * s₁ * a)) := by rw [hc]
    _ = (z * x) * (s₁ * (a⁻¹ * s₁ * a)) := by group

theorem invol_mul_z [Finite G] {p : G} (hp : p ∈ T ⊓ K) (hp2 : p * p = 1) :
    p * z ∈ T ⊓ K ∧ (p * z) * (p * z) = 1 := by
  have hpzc : p * z = z * p := F.z_central p hp
  refine ⟨Subgroup.mul_mem _ hp F.z_mem, ?_⟩
  calc (p * z) * (p * z) = p * (z * p) * z := by group
    _ = p * (p * z) * z := by rw [← hpzc]
    _ = (p * p) * (z * z) := by group
    _ = 1 := by rw [hp2, F.z_sq, one_mul]

theorem not_mem_R_mul_z [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {p : G}
    (hpR : p ∉ conjugate (T ⊓ CxK x K) a⁻¹) : p * z ∉ conjugate (T ⊓ CxK x K) a⁻¹ := by
  have hR := F.R_four hG hs e7 hP2 hQ4
  have hzR : z ∈ conjugate (T ⊓ CxK x K) a⁻¹ := F.z_mem_four hR
  intro h
  apply hpR
  have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ hzR)
  rwa [mul_inv_cancel_right] at this

theorem Fv_inter [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁2 : s₁ * s₁ = 1)
    (hs₁R : s₁ ∉ conjugate (T ⊓ CxK x K) a⁻¹) :
    ∀ y' ∈ S, (y' ∈ Fv x (z * x) ↔ (y' ∈ Esub x z a s₁ ∧ y' ≠ 1 ∧ y' ≠ z * x)) := by
  intro y' hyS
  have hxv : ¬ IsConj x (z * x) :=
    F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
  have hs₁sR := F.not_mem_R_mul_z hG hs e7 hP2 hQ4 hs₁R
  obtain ⟨hs₁zP, hs₁z2⟩ := F.invol_mul_z hs₁ hs₁2
  constructor
  · rintro ⟨hyv, hy2, hxy, hxyv⟩
    have hyne1 : y' ≠ 1 := fun h => F.x_ne (isConj_one_left.1 (h ▸ hxy))
    have hynev : y' ≠ z * x := fun h => hxv (h ▸ hxy)
    refine ⟨?_, hyne1, hynev⟩
    have hyT : y' ∈ T := by
      by_contra hyT
      exact F.not_isConj_x_of_swap hG hs e7 hP2 hQ4 hyS hyT hy2 hxy
    rcases F.zs_T hG hs e7 hP2 hQ4 hyT hy2 hxy hxyv with h | h | ⟨p, hp, w, hw, hp2, hw2, hpR, hwR, h⟩
    · rw [h]; exact x_mem_Esub x z a s₁
    · rw [h]; exact z_mem_Esub x z a s₁
    · rw [h]
      have hy0 := y0_mem_Esub x z a s₁
      rcases F.invol_not_mem_R_eq hG hs e7 hP2 hQ4 hs₁ hs₁2 hs₁R hp hp2 hpR with hp' | hp' <;>
        rcases F.invol_not_mem_R_eq hG hs e7 hP2 hQ4 hs₁ hs₁2 hs₁R hw hw2 hwR with hw' | hw' <;>
        rw [hp', hw']
      · exact hy0
      · rw [F.tt_s_zs hs₁]
        exact Subgroup.mul_mem _ (x_mem_Esub x z a s₁) hy0
      · rw [tt_zs_s]
        exact Subgroup.mul_mem _ (z_mem_Esub x z a s₁) hy0
      · rw [F.tt_zs_zs hs₁]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (z_mem_Esub x z a s₁) (x_mem_Esub x z a s₁)) hy0
  · rintro ⟨hE, hne1, hnev⟩
    rcases F.mem_Esub_cases hs₁ hs₁2 hE with h | h | h | h | h | h | h | h
    · exact absurd h hne1
    · rw [h]; exact F.x_mem_Fv
    · rw [h]; exact F.z_mem_Fv
    · exact absurd (h.trans F.zx_comm.symm) hnev
    · rw [h]
      exact F.tt_mem_Fv hG hs e7 hP2 hQ4 hs₁ hs₁ hs₁2 hs₁2 hs₁R hs₁R
    · rw [h, F.tt_mul_x]
      exact F.tt_mem_Fv hG hs e7 hP2 hQ4 hs₁ hs₁zP hs₁2 hs₁z2 hs₁R hs₁sR
    · rw [h, F.tt_mul_z hs₁]
      exact F.tt_mem_Fv hG hs e7 hP2 hQ4 hs₁zP hs₁ hs₁z2 hs₁2 hs₁sR hs₁R
    · rw [h, ← F.zx_comm, F.tt_mul_v hs₁]
      exact F.tt_mem_Fv hG hs e7 hP2 hQ4 hs₁zP hs₁zP hs₁z2 hs₁z2 hs₁sR hs₁sR

theorem Ev_eq_Esub [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁2 : s₁ * s₁ = 1)
    (hs₁R : s₁ ∉ conjugate (T ⊓ CxK x K) a⁻¹) : Ev x (z * x) S = Esub x z a s₁ := by
  have hint := F.Fv_inter hG hs e7 hP2 hQ4 hs₁ hs₁2 hs₁R
  have hv : z * x ∈ Esub x z a s₁ :=
    Subgroup.mul_mem _ (z_mem_Esub x z a s₁) (x_mem_Esub x z a s₁)
  apply le_antisymm
  · unfold Ev
    rw [Subgroup.closure_le]
    rintro t (ht | ⟨htF, htS⟩)
    · rw [Set.mem_singleton_iff.1 ht]; exact hv
    · exact ((hint t htS).1 htF).1
  · have hS : ∀ t ∈ Fv x (z * x), t ∈ S → t ∈ Ev x (z * x) S := fun t htF htS =>
      Subgroup.subset_closure (Or.inr ⟨htF, htS⟩)
    have hy0S : tt a s₁ s₁ ∈ S := F.core.T_le_S (F.tt_mem_T hs₁ hs₁)
    have hy0F : tt a s₁ s₁ ∈ Fv x (z * x) :=
      F.tt_mem_Fv hG hs e7 hP2 hQ4 hs₁ hs₁ hs₁2 hs₁2 hs₁R hs₁R
    exact sup_le (zpowers_le.2 (hS _ hy0F hy0S))
      (sup_le (zpowers_le.2 (hS _ F.x_mem_Fv (F.core.T_le_S F.x_mem_T)))
        (zpowers_le.2 (hS _ F.z_mem_Fv (F.core.T_le_S F.z_mem.1))))

end Frame

end CFSG.GH74.GLS.Th2.P43f
