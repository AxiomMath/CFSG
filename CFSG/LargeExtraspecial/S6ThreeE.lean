module

public import CFSG.LargeExtraspecial.S6ThreeD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def Wone (t : S.O) (g₁ g₂ : G) : Submodule (ZMod 2) S.Qt :=
  LinearMap.BilinForm.orthogonal S.q.polarBilin (Vone S g t g₁ g₂)

theorem mem_Wone {t : S.O} {g₁ g₂ : G} {v : S.Qt} :
    v ∈ Wone S g t g₁ g₂ ↔ ∀ u ∈ Vone S g t g₁ g₂, polar S.q u v = 0 := by
  simp [Wone, LinearMap.BilinForm.mem_orthogonal_iff, polarBilin_apply_apply]

theorem finrank_Wone {t : S.O} (g₁ g₂ : G) :
    finrank (ZMod 2) (Wone S g t g₁ g₂) + finrank (ZMod 2) (Vone S g t g₁ g₂) =
      finrank (ZMod 2) S.Qt := by
  have := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (Vone S g t g₁ g₂)
  rw [Wone]
  have h2 := Submodule.finrank_le (Vone S g t g₁ g₂)
  omega

theorem Wone_le_Wt {t : S.O} (g₁ g₂ : G) : Wone S g t g₁ g₂ ≤ Wt S g t :=
  fun _ hv => mem_Wt.mpr fun u hu => mem_Wone.mp hv u (Vt_le_Vone _ _ hu)

section Pair

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include H C ht ht1 hVQ hh hb

theorem Vone_eq' :
    Vone S g t g ((h : G) * g) =
      (S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g))) ⊔ Vt S g t := by
  have h1 := pair_one (t := t) hb
  have := Vone_eq H C ht ht1 hVQ h1.1 hh h1.2
  simpa using this

theorem sup_clSub_inf_Vt :
    (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Vt S g t) =
      Vt S g t := by
  have h1 := pair_one (t := t) hb
  have hth := mem_Lbar_of_pair H ht hh
  refine le_antisymm (sup_le inf_le_right inf_le_right) fun u hu => ?_
  obtain ⟨ε, hε⟩ := exists_add_mem_clSub H C ht ht1 hVQ h1.1 hh h1.2 hu
  simp only [OneMemClass.coe_one, one_mul] at hε
  have hbV := cl_mem_Vt hth
  have hbP : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) :=
    cl_mem_clSub_self (H.mul h).conj_mem
  have e : u = (u + ε • S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) +
      ε • S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    rw [add_assoc, vec_add_self, add_zero]
  rw [e]
  exact Submodule.add_mem_sup ⟨hε, add_mem hu (Submodule.smul_mem _ _ hbV)⟩
    ⟨Submodule.smul_mem _ _ hbP, Submodule.smul_mem _ _ hbV⟩

theorem finrank_clSub_inf_clSub_inf_Vt :
    finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊓
      (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Vt S g t)) + 2 = finrank (ZMod 2) (Vt S g t) := by
  have hth := mem_Lbar_of_pair H ht hh
  have d1 := finrank_clSub_inf_Vt H C ht ht1 hVQ
  have d2 := finrank_clSub_inf_Vt (H.mul h) (C.mul h) hth ht1 (not_V_le_Qa_mul H hVQ hh)
  rw [Vt_mul] at d2
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t)
    (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Vt S g t)
  rw [sup_clSub_inf_Vt H C ht ht1 hVQ hh hb] at hs
  omega

theorem clSub_inf_clSub_le_Wt :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Wt S g t := by
  intro p hp
  rw [mem_Wt]
  intro u hu
  rw [← sup_clSub_inf_Vt H C ht ht1 hVQ hh hb] at hu
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
  rw [polar_add_left, polar_eq_zero_of_mem_clSub H.conj_ne hx.1 hp.1,
    polar_eq_zero_of_mem_clSub (H.mul h).conj_ne hy.1 hp.2, add_zero]

theorem Vone_le_Wt : Vone S g t g ((h : G) * g) ≤ Wt S g t := by
  rw [Vone_eq' H C ht ht1 hVQ hh hb]
  exact sup_le (clSub_inf_clSub_le_Wt H C ht ht1 hVQ hh hb) (Vt_le_Wt H ht1)

theorem q_eq_zero_of_mem_Vone {v : S.Qt} (hv : v ∈ Vone S g t g ((h : G) * g)) : S.q v = 0 := by
  rw [Vone_eq' H C ht ht1 hVQ hh hb] at hv
  obtain ⟨p, hp, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
  have hpu := mem_Wt.mp (clSub_inf_clSub_le_Wt H C ht ht1 hVQ hh hb hp) u hu
  rw [QuadraticMap.map_add S.q p u, S.q_eq_zero_of_mem_clSub_QG_inf_Qa H.conj_ne hp.1,
    q_eq_zero_of_mem_Vt H ht1 hu, polar_comm, hpu, add_zero, add_zero]

theorem Vone_le_Wone : Vone S g t g ((h : G) * g) ≤ Wone S g t g ((h : G) * g) := by
  intro v hv
  rw [mem_Wone]
  intro u hu
  rw [polar, q_eq_zero_of_mem_Vone H C ht ht1 hVQ hh hb (add_mem hu hv),
    q_eq_zero_of_mem_Vone H C ht ht1 hVQ hh hb hu, q_eq_zero_of_mem_Vone H C ht ht1 hVQ hh hb hv,
    sub_zero, sub_zero]

theorem clSub_inf_Wt_le_Wone :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ≤ Wone S g t g ((h : G) * g) := by
  intro w hw
  rw [mem_Wone]
  intro v hv
  rw [Vone_eq' H C ht ht1 hVQ hh hb] at hv
  obtain ⟨p, hp, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
  rw [polar_add_left, polar_eq_zero_of_mem_clSub H.conj_ne hp.1 hw.1, mem_Wt.mp hw.2 u hu,
    add_zero]

theorem clSub_inf_Wt_le_Wone' :
    S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t ≤ Wone S g t g ((h : G) * g) := by
  intro w hw
  rw [mem_Wone]
  intro v hv
  rw [Vone_eq' H C ht ht1 hVQ hh hb] at hv
  obtain ⟨p, hp, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
  rw [polar_add_left, polar_eq_zero_of_mem_clSub (H.mul h).conj_ne hp.2 hw.1,
    mem_Wt.mp hw.2 u hu, add_zero]

theorem finrank_clSub_inf_clSub :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g))) + 2 =
      finrank (ZMod 2) (Vone S g t g ((h : G) * g)) := by
  have d1 := finrank_clSub_inf_clSub_inf_Vt H C ht ht1 hVQ hh hb
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g))) (Vt S g t)
  rw [← Vone_eq' H C ht ht1 hVQ hh hb] at hs
  have e : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Vt S g t =
      (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊓ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Vt S g t) := by
    rw [inf_inf_distrib_right]
  rw [e] at hs
  omega

end Pair

section Sp

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem finrank_Vone_eq' :
    finrank (ZMod 2) (Vone S g t g ((h : G) * g)) = finrank (ZMod 2) (Vt S g t) + 1 := by
  have h1 := pair_one (t := t) hb
  have := finrank_Vone_eq hCE H hNo C ht ht1 hVQ hSp h1.1 hh h1.2
  rw [show ((1 : S.M) : G) * g = g by simp] at this
  exact this

theorem finrank_Wone_eq :
    finrank (ZMod 2) (Wone S g t g ((h : G) * g)) + 1 = finrank (ZMod 2) (Wt S g t) := by
  have h1 := finrank_Wone (S := S) (g := g) (t := t) g ((h : G) * g)
  have h2 := finrank_Wt (S := S) (g := g) (t := t)
  have h3 := finrank_Vone_eq' hCE H hNo C ht ht1 hVQ hSp hh hb
  omega

theorem Wone_eq_sup :
    (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) =
      Wone S g t g ((h : G) * g) := by
  have hth := mem_Lbar_of_pair H ht hh
  have dA := finrank_clSub_inf_Wt H C ht ht1 hVQ
  have dB := finrank_clSub_inf_Wt (H.mul h) (C.mul h) hth ht1 (not_V_le_Qa_mul H hVQ hh)
  rw [Wt_mul] at dB
  have dP := finrank_clSub_inf_clSub H C ht ht1 hVQ hh hb
  have dV := finrank_Vone_eq' hCE H hNo C ht ht1 hVQ hSp hh hb
  have dW := finrank_Wone (S := S) (g := g) (t := t) g ((h : G) * g)
  have dQ := S.finrank_Qt_eq_two_mul_width
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t)
    (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t)
  have e : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊓
      (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) =
      S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := by
    rw [← inf_inf_distrib_right, inf_eq_left.mpr (clSub_inf_clSub_le_Wt H C ht ht1 hVQ hh hb)]
  rw [e] at hs
  refine Submodule.eq_of_le_of_finrank_le (sup_le (clSub_inf_Wt_le_Wone H C ht ht1 hVQ hh hb)
    (clSub_inf_Wt_le_Wone' H C ht ht1 hVQ hh hb)) ?_
  omega

theorem Nbar_eq_sup_sp :
    Nbar S g t = (S.Lbar g ⊓ Nbar S g t) ⊔ (S.Lbar ((h : G) * g) ⊓ Nbar S g t) :=
  (timmesfeld_6_5_bar H C ht ht1 hVQ (pairGen_of_spCase H C ht ht1 hVQ hSp)
    (Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp) hh hb).1

theorem Nbar_fix_Vone' {x : S.O} (hx : x ∈ Nbar S g t) {v : S.Qt}
    (hv : v ∈ Vone S g t g ((h : G) * g)) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have h1 := pair_one (t := t) hb
  have hN := Nbar_eq_sup_sp hCE H hNo C ht ht1 hVQ hSp hh hb
  exact Nbar_fix_Vone H C ht ht1 hVQ h1.1 hh h1.2 (by simpa using hN) hx (by simpa using hv)

theorem Nbar_apply_sub_mem_Wone {x : S.O} (hx : x ∈ Nbar S g t) (v : S.Qt) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Wone S g t g ((h : G) * g) := by
  rw [mem_Wone]
  intro u hu
  have hxu := Nbar_fix_Vone' hCE H hNo C ht ht1 hVQ hSp hh hb hx hu
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2 u v
  rw [hxu] at h1
  rw [polar_sub_right, h1, sub_self]

theorem Nbar_apply_mem_Wone {x : S.O} (hx : x ∈ Nbar S g t) {w : S.Qt}
    (hw : w ∈ Wone S g t g ((h : G) * g)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wone S g t g ((h : G) * g) := by
  have := add_mem (Nbar_apply_sub_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hx w) hw
  rwa [sub_add_cancel] at this

omit hCE H hNo C ht ht1 hVQ hSp hh hb in
theorem apply_sub_mem_Vone_of_decomp {g₁ g₂ : G} (C₁ : Cons311 S g₁)
    (h1Q : g₁ * S.z * g₁⁻¹ ∈ S.QG) (h1V : S.cl (g₁ * S.z * g₁⁻¹) ∈ Vt S g t)
    (h2Q : g₂ * S.z * g₂⁻¹ ∈ S.QG) (h2z : g₂ * S.z * g₂⁻¹ ≠ S.z)
    (h2V : S.cl (g₂ * S.z * g₂⁻¹) ∈ Vt S g t) {X Y : Submodule (ZMod 2) S.Qt}
    (hVX : Vt S g t ≤ X) (hYW : Y ≤ Wt S g t)
    (hdec : (S.clSub (S.QG ⊓ S.Qa g₁) ⊓ Y) ⊔ (S.clSub (S.QG ⊓ S.Qa g₂) ⊓ Y) = Y)
    (hP : S.clSub (S.QG ⊓ S.Qa g₁) ⊓ S.clSub (S.QG ⊓ S.Qa g₂) ≤ X)
    {k : S.O} (hk : k ∈ S.Lbar g₁ ⊓ Nbar S g t) {w : S.Qt} (hw : w ∈ Y) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X := by
  rw [← hdec] at hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add, show (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x + (k : S.Qt ≃ₗ[ZMod 2] S.Qt) y - (x + y) =
    ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) + ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) by abel]
  refine add_mem ?_ (hP ⟨apply_sub_mem_clSub_of_mem_Wt C₁ h1V h1Q (hYW hy.2) hk.1,
    sub_mem (Nbar_apply_mem_clSub h2Q h2z h2V hk.2 hy.1) hy.1⟩)
  have h1 := Lbar_apply_sub_mem_span' h1Q hx.1 hk.1
  exact hVX ((Submodule.span_singleton_le_iff_mem _ _).mpr h1V h1)

theorem Nbar_apply_sub_mem_Vone {x : S.O} (hx : x ∈ Nbar S g t) {w : S.Qt}
    (hw : w ∈ Wone S g t g ((h : G) * g)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vone S g t g ((h : G) * g) := by
  have hth := mem_Lbar_of_pair H ht hh
  have hdec := Wone_eq_sup hCE H hNo C ht ht1 hVQ hSp hh hb
  set X := Vone S g t g ((h : G) * g) with hX
  set Y := Wone S g t g ((h : G) * g) with hY
  have hYW : Y ≤ Wt S g t := Wone_le_Wt _ _
  have hdecY : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Y) ⊔ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Y) = Y := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
    conv_lhs => rw [← hdec]
    exact sup_le_sup (le_inf inf_le_left (clSub_inf_Wt_le_Wone H C ht ht1 hVQ hh hb))
      (le_inf inf_le_left (clSub_inf_Wt_le_Wone' H C ht ht1 hVQ hh hb))
  have hP : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ X :=
    inf_le_Vone _ _
  have hA : ∀ k ∈ S.Lbar g ⊓ Nbar S g t, ∀ w ∈ Y, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X :=
    fun k hk w hw => apply_sub_mem_Vone_of_decomp C H.conj_mem
      (cl_a_mem_Vt ht) (conj_mem_QG' S h.2 H.conj_mem) (conj_ne_z' S h.2 H.conj_ne)
      (cl_mem_Vt hth) (Vt_le_Vone _ _) hYW hdecY hP hk hw
  have hB : ∀ k ∈ S.Lbar ((h : G) * g) ⊓ Nbar S g t, ∀ w ∈ Y,
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X :=
    fun k hk w hw => apply_sub_mem_Vone_of_decomp (C.mul h)
      (conj_mem_QG' S h.2 H.conj_mem) (cl_mem_Vt hth) H.conj_mem H.conj_ne (cl_a_mem_Vt ht)
      (Vt_le_Vone _ _) hYW (by rw [sup_comm]; exact hdecY) (by rw [inf_comm]; exact hP) hk hw
  let K : Subgroup S.O :=
    { carrier := {x | x ∈ Nbar S g t ∧ ∀ w ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X}
      mul_mem' := by
        rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
        refine ⟨mul_mem hxN hyN, fun w hw => ?_⟩
        rw [coe_mul_apply, show (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w =
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
            (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) by abel]
        exact add_mem (hx _ (Nbar_apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hyN hw))
          (hy w hw)
      one_mem' := ⟨one_mem _, fun w _ => by
        rw [show ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w from rfl, sub_self]
        exact Submodule.zero_mem _⟩
      inv_mem' := by
        rintro x ⟨hxN, hx⟩
        refine ⟨inv_mem hxN, fun w hw => ?_⟩
        have h1 := hx _ (Nbar_apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb (inv_mem hxN) hw)
        rw [apply_inv_apply_O] at h1
        have h2 := neg_mem h1
        rwa [neg_sub] at h2 }
  have hle : Nbar S g t ≤ K := by
    rw [Nbar_eq_sup_sp hCE H hNo C ht ht1 hVQ hSp hh hb]
    exact sup_le (fun k hk => ⟨hk.2, hA k hk⟩) (fun k hk => ⟨hk.2, hB k hk⟩)
  exact (hle hx).2 w hw

end Sp

theorem timmesfeld_6_3_five (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ) :
    (∀ v : S.Qt, ((chi H C ht ht1 hVQ (Submodule.Quotient.mk v) : Vt S g t) : S.Qt) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) ∧
    (∀ (x : Rbar S g t) (v : S.Qt),
      chi H C ht ht1 hVQ (Submodule.Quotient.mk (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) =
        resV H.conj_mem t x (chi H C ht ht1 hVQ (Submodule.Quotient.mk v))) ∧
    RmodN S g t = TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) ∧
    LmodN S g t = spPointRadical (beta H C ht ht1 hVQ) (aV ht) :=
  ⟨coe_chi_apply_mk H C ht ht1 hVQ, chi_equivariant H C ht ht1 hVQ, hSp.eq_sp, hSp.LmodN_eq⟩

end CFSG.LargeExtraspecial.S6
