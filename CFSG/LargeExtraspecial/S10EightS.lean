module

public import CFSG.LargeExtraspecial.S10EightR

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem finrank_map_sup_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) {C W : Submodule K V} (hCW : C ≤ W)
    (A : Submodule K V) :
    finrank K ↥(W.map f ⊔ A) + finrank K C ≤ finrank K ↥(C.map f ⊔ A) + finrank K W := by
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (C.comap W.subtype)
  have hWle : W ≤ C ⊔ D.map W.subtype := by
    intro w hw
    have hw' : (⟨w, hw⟩ : W) ∈ C.comap W.subtype ⊔ D := by
      rw [hD.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hw'
    have e : w = (c : V) + (d : V) := by
      rw [← Submodule.coe_add, hcd]
    rw [e]
    exact Submodule.add_mem_sup hc (Submodule.mem_map_of_mem hd)
  have h2 : W.map f ≤ C.map f ⊔ (D.map W.subtype).map f := by
    rw [← Submodule.map_sup]
    exact Submodule.map_mono hWle
  have h1 : W.map f ⊔ A ≤ (C.map f ⊔ A) ⊔ (D.map W.subtype).map f :=
    sup_le (h2.trans (sup_le_sup_right le_sup_left _)) (le_sup_right.trans le_sup_left)
  have h3 := Submodule.finrank_mono h1
  have h4 := Submodule.finrank_add_le_finrank_add_finrank (C.map f ⊔ A)
    ((D.map W.subtype).map f)
  have h5 := Submodule.finrank_map_le f (D.map W.subtype)
  have h6 : finrank K (D.map W.subtype) = finrank K D := Submodule.finrank_map_subtype_eq W D
  have h7 := Submodule.finrank_add_eq_of_isCompl hD
  have h8 : finrank K (C.comap W.subtype) = finrank K C :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hCW)
  omega

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem exists_comm_sing : ∀ γ : Gm, γ = τ₁ ∨ γ = τ₂ → ∃ m : M2, qf (act γ m - m) = 0 ∧
    pf E00 (act γ m - m) = 0 ∧ act γ m - m ≠ E00 ∧ act γ m - m ≠ 0 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem apply_sub_mem_clSub_of_commute {τ : S.M} {u : G} (hτu : (τ : G) = u * S.z * u⁻¹)
    {x : S.M} (hxu : (x : G) ∈ S.Qa u) {c : G} (hcQ : c ∈ S.QG) (hcτ : c * τ = τ * c) :
    ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c) - S.cl c ∈ S.clSub (S.QG ⊓ S.Qa u) := by
  have hmem : (x : G) * c * (x : G)⁻¹ * c⁻¹ ∈ S.QG ⊓ S.Qa u := by
    refine ⟨S.commutator_mem_QG x.2 hcQ, ?_⟩
    rw [show (x : G) * c * (x : G)⁻¹ * c⁻¹ = x * (c * (x : G)⁻¹ * c⁻¹) by group]
    exact mul_mem hxu (conj_mem_Qa_of_commute hτu (inv_mem hxu) hcτ)
  rw [← S.cl_commutator x.2 hcQ]
  exact S.cl_mem_clSub hmem hmem.1

theorem clSub_inf_fixSub_le (H : Hyp4 S g) (C : Cons311 S g) (hF : S6.FusionCtl S g)
    {s : S.O} (hs1 : s ≠ 1) {τ : S.M} (hτ : S.ρ τ = s) {u : G}
    (hτu : (τ : G) = u * S.z * u⁻¹) (haQt : g * S.z * g⁻¹ ∈ S.Qa u) :
    S.clSub (S.QG ⊓ S.Qa g) ⊓
        fixSub S ((((S.Qa g ⊓ S.Qa u) ⊓ S.M).subgroupOf S.M).map S.ρ) ≤
      S.clSub (S.QG ⊓ S.Qa u) := by
  set X := (S.Qa g ⊓ S.Qa u) ⊓ S.M with hX
  set Xbar := (X.subgroupOf S.M).map S.ρ with hXbar
  set Pa := S.clSub (S.QG ⊓ S.Qa g) with hPa
  set P3 := S.clSub (S.QG ⊓ (S.Qa g ⊓ S.Qa u)) with hP3
  have hXL : Xbar ≤ S.Lbar g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ρ_mem_Lbar S ⟨(mem_subgroupOf.mp hx).1.1, x.2⟩
  have hfixdim := card_mul_two_pow_finrank_fix H C hXL
  have hcomm : ∀ x ∈ S.Qa g ⊓ S.Qa u, ∀ y ∈ S.Qa g ⊓ S.Qa u, x * y = y * x := by
    intro x hx y hy
    have hTa : (S.conjBy u).Qa (g * u⁻¹) = S.Qa g := by
      rw [S.Qa_conjBy, inv_mul_cancel_right]
    have hne : (g * u⁻¹) * (S.conjBy u).z * (g * u⁻¹)⁻¹ ≠ (S.conjBy u).z := by
      rw [Setting.conjBy_z, show g * u⁻¹ * (u * S.z * u⁻¹) * (g * u⁻¹)⁻¹ = g * S.z * g⁻¹ by
        group, ← hτu]
      intro h
      exact tau_not_mem_QG hs1 hτ (h ▸ H.conj_mem)
    exact (S.conjBy u).QG_inf_Qa_comm hne ⟨hx.2, by rw [hTa]; exact hx.1⟩
      ⟨hy.2, by rw [hTa]; exact hy.1⟩
  have hP3le : P3 ≤ Pa ⊓ fixSub S Xbar := by
    intro v hv
    obtain ⟨q, hq, hqQ, rfl⟩ := S.mem_clSub_iff.mp hv
    refine ⟨S.cl_mem_clSub ⟨hqQ, hq.2.1⟩ hqQ, fun ξ hξ => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hξ
    obtain ⟨hxgu, -⟩ := mem_subgroupOf.mp hx
    rw [S.ρ_cl x hqQ, hcomm _ hxgu _ hq.2, mul_inv_cancel_right]
  have hzP : S.z ∉ S.QG ⊓ (S.Qa g ⊓ S.Qa u) := fun h => z_not_mem_Qa_of_tau hs1 hτ hτu h.2.2
  have hP3card : Nat.card (S.QG ⊓ (S.Qa g ⊓ S.Qa u) : Subgroup G) = 2 ^ finrank (ZMod 2) P3 := by
    rw [card_eq_card_clSub inf_le_left hzP, S.card_submodule]
  have hK : Nat.card (S.ρ.ker ⊓ X.subgroupOf S.M : Subgroup S.M) ≤
      Nat.card (S.QG ⊓ (S.Qa g ⊓ S.Qa u) : Subgroup G) := by
    have hle : (S.ρ.ker ⊓ X.subgroupOf S.M).map S.M.subtype ≤ S.QG ⊓ (S.Qa g ⊓ S.Qa u) := by
      rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨(S.ρ_eq_one_iff y).mp hy1, (mem_subgroupOf.mp hy2).1⟩
    rw [← Subgroup.card_map_of_injective S.M.subtype_injective]
    exact Subgroup.card_le_of_le hle
  have hX0 := card_Qa_inf_Qa H hs1 hτ hτu C hF haQt
  have hX01 : Nat.card (S.Qa g ⊓ S.Qa u : Subgroup G) ≤ 2 * Nat.card X := card_le_two_mul H u
  have hXc : Nat.card X = Nat.card Xbar * Nat.card (S.ρ.ker ⊓ X.subgroupOf S.M : Subgroup S.M) :=
    card_eq_card_map_mul (S := S) (X := X) inf_le_right
  have hle := Submodule.finrank_mono hP3le
  set d := finrank (ZMod 2) ↥(Pa ⊓ fixSub S Xbar) with hd
  set p := finrank (ZMod 2) P3 with hp
  have hBpos : 0 < Nat.card Xbar := Nat.card_pos
  have e1 : 2 ^ (S.width + 1) = 2 * 2 ^ S.width := pow_succ' 2 _
  have e2 : 2 ^ S.width ≤ Nat.card Xbar * 2 ^ p := by
    have := Nat.mul_le_mul_left (Nat.card Xbar) (hK.trans hP3card.le)
    rw [← hXc] at this
    omega
  have e3 : Nat.card Xbar * 2 ^ d ≤ Nat.card Xbar * 2 ^ p := by rw [hfixdim]; exact e2
  have hdp : d ≤ p :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_left e3 hBpos)
  have heq : P3 = Pa ⊓ fixSub S Xbar := Submodule.eq_of_le_of_finrank_le hP3le (by omega)
  rw [← heq]
  exact S.clSub_mono (inf_le_inf_left _ inf_le_right)

theorem exists_point_of_a2 {s : S.O} (Y : Hyp10 S g s) (F : Frame Y) {τ : S.M}
    (hτ : S.ρ τ = s) {u : G} (hτu : (τ : G) = u * S.z * u⁻¹) {x : S.M}
    (hxu : (x : G) ∈ S.Qa u) (hxR : S.ρ x ∈ Rbar S g s)
    (h12 : F.π ⟨S.ρ x, hxR⟩ = τ₁ ∨ F.π ⟨S.ρ x, hxR⟩ = τ₂) :
    ∃ kv : S.M, S.cl ((kv : G) * g * S.z * ((kv : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
      S.cl ((kv : G) * g * S.z * ((kv : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹) ∧
      S.cl ((kv : G) * g * S.z * ((kv : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa u) := by
  obtain ⟨hcomm, -⟩ := commSpace_t_eq Y.H Y.C Y.ht Y.ht1 Y.hVQ
  have hq : ∀ v ∈ commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt), S.q v = 0 := fun v hv =>
    q_eq_zero_of_mem_Vt Y.H Y.ht1 (hcomm ▸ hv)
  obtain ⟨m, hmq, hmpf, hmE, hm0⟩ := exists_comm_sing _ h12
  set w : Vt S g s := F.φ.symm m with hw
  set v : Vt S g s := resV Y.haQ s ⟨S.ρ x, hxR⟩ w - w with hv
  have hφv : F.φ v = act (F.π ⟨S.ρ x, hxR⟩) m - m := by
    rw [hv, map_sub, F.compat, hw, LinearEquiv.apply_symm_apply]
  have hv0 : v ≠ 0 := fun h => hm0 (by rw [← hφv, h, map_zero])
  obtain ⟨e, ⟨r, hrR, hre⟩, hea⟩ := (F.sing v hv0).mpr (by rw [hφv]; exact hmq)
  obtain ⟨kv, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hrR)
  have hvcl : (v : S.Qt) = S.cl ((kv : G) * g * S.z * ((kv : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S kv Y.haQ, ← hea]
    exact hre (aV Y.ht)
  refine ⟨kv, ?_, ?_, ?_⟩
  · rw [← hvcl, ← beta_aV_eq_zero_iff Y.H Y.C Y.ht Y.ht1 Y.hVQ, F.beta_eq, F.base, hφv]
    exact hmpf
  · rw [← hvcl]
    intro h
    apply hmE
    rw [← hφv, ← F.base]
    exact congrArg F.φ (Subtype.ext h)
  · rw [← hvcl]
    obtain ⟨c, hcQ, hcw⟩ := S.exists_cl (w : S.Qt)
    have hcU : S.cl c ∈ commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) := by rw [hcw, hcomm]; exact w.2
    have hcτ := commute_of_cl_mem_commSpace hτ hτu hq hcQ hcU
    have h1 := apply_sub_mem_clSub_of_commute hτu hxu hcQ hcτ
    rw [hcw] at h1
    rw [hv, Submodule.coe_sub, coe_resV_apply]
    exact h1

theorem false_of_c2 (hCE : CentralExtInput.{u}) (h7 : 7 ≤ S.width) {s : S.O}
    (Y : Hyp10 S g s) (F : Frame Y) {τ : S.M} (hτ : S.ρ τ = s) {u : G}
    (hτu : (τ : G) = u * S.z * u⁻¹) {x : S.M} (hxu : (x : G) ∈ S.Qa u)
    (hxL : S.ρ x ∈ S.Lbar g) (hc2 : F.π ⟨S.ρ x, Lbar_le_Rbar Y.ht hxL⟩ = τ₁ * τ₂) : False := by
  obtain ⟨hcomm, hfixW⟩ := commSpace_t_eq Y.H Y.C Y.ht Y.ht1 Y.hVQ
  have hW := width_le_finrank_Wstar hCE Y F hxL hc2
  set T : S.Qt →ₗ[ZMod 2] S.Qt :=
    ((((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) with hT
  set Cq := S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) with hCq
  have hCW : Cq ≤ Wt S g s := by
    rw [← hfixW]
    have hfixeq : fixSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) = S.fixQt (τ : G) := by
      rw [S.fixQt_of_mem τ.2, ← hτ]
    rw [hfixeq]
    exact S.clSub_centralizer_le_fixQt τ.2
  have hTC : Cq.map T ≤ S.clSub (S.QG ⊓ S.Qa u) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨c, ⟨hcQ, hcτ⟩, -, rfl⟩ := S.mem_clSub_iff.mp hv
    exact apply_sub_mem_clSub_of_commute hτu hxu hcQ (mem_centralizer_singleton_iff.mp hcτ)
  have h1 := finrank_map_sup_le T hCW (Vt S g s)
  have h2 : finrank (ZMod 2) (Wt S g s) ≤ finrank (ZMod 2) Cq + 1 := by
    rw [← hfixW]
    exact finrank_fixSpace_le hτ
  have h3 := finrank_clSub_le Y.H Y.ht Y.ht1 hτ hτu
  rw [hcomm] at h3
  have h4 := Submodule.finrank_mono (sup_le_sup_right hTC (Vt S g s))
  have h5 := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub (S.QG ⊓ S.Qa u)) (Vt S g s)
  rw [Y.h4] at h5
  omega

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem exists_point_hyp10 (hCE : CentralExtInput.{u}) (hF : S6.FusionCtl S g)
    (h7 : 7 ≤ S.width) {s : S.O} (hs : s ∈ S.Lbar g ⊓ Xb) (Y : Hyp10 S g s) {τ : S.M}
    (hτ : S.ρ τ = s) {u : G} (hτu : (τ : G) = u * S.z * u⁻¹)
    (haQt : g * S.z * g⁻¹ ∈ S.Qa u) :
    ∃ kv : S.M, S.cl ((kv : G) * g * S.z * ((kv : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
      S.cl ((kv : G) * g * S.z * ((kv : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹) ∧
      S.cl ((kv : G) * g * S.z * ((kv : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa u) := by
  set Xx := (S.Qa g ⊓ S.Qa u) ⊓ S.M with hXx
  set Xbar := (Xx.subgroupOf S.M).map S.ρ with hXbar
  have hK1 := clSub_inf_fixSub_le X.H X.C hF Y.ht1 hτ hτu haQt
  by_cases hXN : ∀ x ∈ Xbar, x ∈ Nbar S g s
  ·
    obtain ⟨kd, hkd, -, hne, hPa, -⟩ := D.exists_d hCE
    refine ⟨kd, hPa, hne, hK1 ⟨hPa, fun ξ hξ => ?_⟩⟩
    have hkdR := D.Yb_le_Rbar hs ((D.dec.mem_commutator_iff).mp hkd).1
    have hmem := apply_mem_Vt_of_mem_Rbar X.haQ hkdR (cl_a_mem_Vt hs.1)
    rw [ρ_cl_conj_z S kd X.haQ] at hmem
    exact (mem_Nbar.mp (hXN ξ hξ)).2 _ hmem
  push Not at hXN
  obtain ⟨_, ⟨x, hx, rfl⟩, hxN⟩ := hXN
  obtain ⟨⟨hxg, hxu⟩, -⟩ := mem_subgroupOf.mp hx
  have hxL : S.ρ x ∈ S.Lbar g := ρ_mem_Lbar S ⟨hxg, x.2⟩
  have hxR := Lbar_le_Rbar Y.ht hxL
  obtain ⟨F⟩ := Y.exists_frame
  have hst := F.π_mem_stabA hxL
  rw [mem_stabA, act_E00_iff] at hst
  rcases hst with h1 | h12 | h12 | hc2
  · exact absurd ((F.ker _).mp h1) hxN
  · exact exists_point_of_a2 Y F hτ hτu hxu hxR (Or.inl h12)
  · exact exists_point_of_a2 Y F hτ hτu hxu hxR (Or.inr h12)
  · exact (false_of_c2 hCE h7 Y F hτ hτu hxu hxL hc2).elim

theorem exists_point (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (hF : S6.FusionCtl S g)
    (h7 : 7 ≤ S.width) {s : S.O} (hs : s ∈ S.Lbar g ⊓ Xb) (hs1 : s ≠ 1) {τ : S.M}
    (hτ : S.ρ τ = s) {u : G} (hτu : (τ : G) = u * S.z * u⁻¹)
    (haQt : g * S.z * g⁻¹ ∈ S.Qa u) :
    ∃ c ∈ (S.QG ⊓ S.Qa g) ⊓ S.Qa u, (∃ w : G, c = w * S.z * w⁻¹) ∧
      S.cl c ≠ S.cl (g * S.z * g⁻¹) := by
  rcases D.Rbar_eq_or_hyp10 hCE hP hs hs1 with ⟨hL, -, -⟩ | Y
  · obtain ⟨kd, hkd, -, hne, hPa, -⟩ := D.exists_d hCE
    exact X.exists_point_of_mem_clSub hPa hne
      (D.mem_clSub_of_linCase hF hs hs1 hL hτ hτu haQt hkd)
  · obtain ⟨kv, hPa, hne, hv⟩ := D.exists_point_hyp10 hCE hF h7 hs Y hτ hτu haQt
    exact X.exists_point_of_mem_clSub hPa hne hv

end Dec108

end CFSG.LargeExtraspecial.S10
