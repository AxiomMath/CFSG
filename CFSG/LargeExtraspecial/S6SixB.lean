module

public import CFSG.LargeExtraspecial.S6Six
public import CFSG.LargeExtraspecial.S6ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_conj_eq_of_mem_V (H : Hyp4 S g) {t : S.O} {ht : t ∈ S.Lbar g}
    (hL : LinCase S g ht) {α : G} (hαV : α ∈ V S g t) (hα1 : α ≠ 1) :
    ∃ k : G, k * S.z * k⁻¹ = α := by
  by_cases hαz : α = S.z
  · exact ⟨1, by rw [hαz]; group⟩
  have hαQ : α ∈ S.QG := V_le_QG hαV
  have hv0 : S.cl α ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff hαQ).mp h with h | h
    exacts [hα1 h, hαz h]
  obtain ⟨k, -, hkα⟩ := exists_of_mem_orbit
    (hL.mem_orbit ⟨_, hαV.2⟩ fun h => hv0 (congrArg Subtype.val h)) H.conj_mem
  rcases (S.cl_eq_cl_iff (conj_mem_QG' S k.2 H.conj_mem) hαQ).mp hkα.symm with h | h
  · exact ⟨_, h.symm⟩
  · obtain ⟨q, -, hqb⟩ := S.exists_mul_conj_eq_mul_z (conj_mem_QG' S k.2 H.conj_mem)
      (conj_ne_z' S k.2 H.conj_ne)
    exact ⟨q * ((k : G) * g), by rw [hqb, h]⟩

theorem Tt_le_clSub (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} {ht : t ∈ S.Lbar g}
    (hL : LinCase S g ht) {k : G} (hkV : k * S.z * k⁻¹ ∈ V S g t) :
    Tt S g t ≤ S.clSub (S.QG ⊓ S.Qa k) := by
  by_cases hkz : k * S.z * k⁻¹ = S.z
  · rw [S.Qa_eq_QG_of_conj_eq hkz, inf_idem]
    intro v _
    obtain ⟨x, hx, rfl⟩ := S.exists_cl v
    exact S.cl_mem_clSub hx hx
  have hkQ : k * S.z * k⁻¹ ∈ S.QG := V_le_QG hkV
  have hv0 : S.cl (k * S.z * k⁻¹) ≠ 0 := cl_conj_z_ne_zero S hkQ hkz
  obtain ⟨k', hk', hkk'⟩ := exists_of_mem_orbit
    (hL.mem_orbit ⟨_, hkV.2⟩ fun h => hv0 (congrArg Subtype.val h)) H.conj_mem
  rw [clSub_eq_of_cl_eq hkQ hkz (conj_mem_QG' S k'.2 H.conj_mem) hkk']
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_Tt.mp hv
  have h1 := apply_mem_clSub_Qa_mul k' (inv_apply_t_sub_mem H C ht hw hk')
  rwa [apply_inv_apply_O] at h1

theorem polar_eq_zero_of_fixSpace_eq (H : Hyp4 S g) {t : S.O} {ht : t ∈ S.Lbar g}
    (hL : LinCase S g ht)
    (hfixW : fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Wt S g t)
    (hcomm : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t)
    (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t)) {c : S.Qt} (hc : c ∈ Vt S g t) (y : S.Qt) :
    polar S.q c y = 0 := by
  set tl := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with htl
  have hv : tl y - y ∈ Vt S g t := hcomm ▸ sub_mem_commSpace tl y
  set c' : Vt S g t := ⟨c, hc⟩ with hc'
  set v' : Vt S g t := ⟨tl y - y, hv⟩ with hv'
  have hspan : Submodule.span (ZMod 2) ({c', v'} : Set (Vt S g t)) ≠ ⊤ := by
    intro h
    have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({c', v'} : Set (Vt S g t))) ≤ 2 := by
      rw [Submodule.span_insert]
      refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
      have h2 := finrank_span_le_card (R := ZMod 2) ({c'} : Set (Vt S g t))
      have h3 := finrank_span_le_card (R := ZMod 2) ({v'} : Set (Vt S g t))
      simp only [Set.toFinset_singleton, Finset.card_singleton] at h2 h3
      omega
    rw [h, finrank_top] at h1
    omega
  obtain ⟨w', hw'⟩ : ∃ w' : Vt S g t,
      w' ∉ Submodule.span (ZMod 2) ({c', v'} : Set (Vt S g t)) := by
    by_contra hcon
    push Not at hcon
    exact hspan (eq_top_iff.mpr fun x _ => hcon x)
  obtain ⟨φ, hφw, hφspan⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw' inferInstance
  have hφ0 : ∀ x ∈ Submodule.span (ZMod 2) ({c', v'} : Set (Vt S g t)), φ x = 0 := by
    intro x hx
    have : φ x ∈ (Submodule.span (ZMod 2) ({c', v'} : Set (Vt S g t))).map φ := ⟨x, hx, rfl⟩
    rw [hφspan] at this
    exact this
  have hφc : φ c' = 0 := hφ0 _ (Submodule.subset_span (by simp))
  have hφv : φ v' = 0 := hφ0 _ (Submodule.subset_span (by simp))
  have hφw1 : φ w' = 1 := zmod2_eq_one_of_ne_zero hφw
  have hτ : LinearEquiv.transvection hφc ∈ RmodN S g t := by
    rw [hL.eq_top]
    exact Subgroup.mem_top _
  obtain ⟨r, hr, hrτ⟩ := mem_RmodN.mp hτ
  have hrv : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (tl y - y) = tl y - y := by
    have h1 := hrτ v'
    rw [LinearEquiv.transvection.apply, hφv, zero_smul, add_zero] at h1
    exact h1.symm
  have hrw : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (w' : S.Qt) = (w' : S.Qt) + c := by
    have h1 := hrτ w'
    rw [LinearEquiv.transvection.apply, hφw1, one_smul] at h1
    exact h1.symm
  have hrW : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ Wt S g t := by
    rw [← hfixW, mem_fixSpace, map_sub]
    have hcomm' : tl ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) y) = (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (tl y) := by
      rw [htl, ← coe_mul_apply, ← coe_mul_apply, commute_of_mem_Rbar H.conj_mem hr]
    have e1 : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (tl y) = tl y - y + (r : S.Qt ≃ₗ[ZMod 2] S.Qt) y := by
      rw [← hrv, map_sub]
      abel
    rw [hcomm', e1]
    abel
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup r.2 y (w' : S.Qt)
  rw [hrw] at h1
  have h2 : polar S.q ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) ((w' : S.Qt) + c) = 0 := by
    rw [polar_comm]
    exact mem_Wt.mp hrW _ (add_mem w'.2 hc)
  have e : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) y = y + ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) := by abel
  rw [e, polar_add_left, h2, add_zero, polar_add_right, add_eq_left] at h1
  rw [polar_comm]
  exact h1

theorem Vt_le_Tt (H : Hyp4 S g) (hNo : NoA2 S g) {t : S.O} {ht : t ∈ S.Lbar g} (ht1 : t ≠ 1)
    (hL : LinCase S g ht) : Vt S g t ≤ Tt S g t := by
  set tl := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with htl
  have htt := mul_self_of_mem_Lbar S H.conj_mem ht
  by_cases hT : Tt S g t = ⊥
  swap
  · exact Vt_le_of_invariant H hT fun x hx v hv => apply_mem_Tt H hx hv
  exfalso
  have hWfix : Wt S g t ≤ fixSpace tl := fun w hw => by
    have h1 := sub_mem_Tt (S := S) (g := g) (t := t) hw
    rw [hT, Submodule.mem_bot, sub_eq_zero] at h1
    exact mem_fixSpace.mpr h1
  have hfixW : fixSpace tl = Wt S g t := le_antisymm (fixSpace_le_Wt H ht ht1) hWfix
  have hcomm : commSpace tl = Vt S g t := by
    rw [← orthogonal_fixSpace htt, hfixW, Wt,
      LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl]
  by_cases h3 : 3 ≤ finrank (ZMod 2) (Vt S g t)
  · apply Vt_ne_bot H ht
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_bot]
    refine S.q_nondegenerate.1 c fun y => ?_
    rw [polarBilin_apply_apply]
    exact polar_eq_zero_of_fixSpace_eq H hL hfixW hcomm h3 hc y
  · have h2 : finrank (ZMod 2) (Vt S g t) = 2 := by
      have := hL.two_le_finrank
      omega
    obtain ⟨α, hαL, hαQ, hα⟩ := exists_of_mem_Lbar_ne_one ht ht1
    apply hNo α hαL hαQ
    unfold Setting.IsTypeAOn
    rw [hα]
    refine ⟨fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup t.2 v,
      fun h => ht1 (Subtype.ext h), coe_mul_self htt, by rw [hcomm, h2], fun v hv => ?_⟩
    rw [hcomm] at hv
    exact q_eq_zero_of_mem_Vt H ht1 hv

theorem isTypeA_of_linCase (H : Hyp4 S g) {t : S.O} {ht : t ∈ S.Lbar g} (ht1 : t ≠ 1)
    (hL : LinCase S g ht) : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))) := by
  set tl := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with htl
  have htt := coe_mul_self (mul_self_of_mem_Lbar S H.conj_mem ht)
  refine ⟨fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup t.2 v,
    fun h => ht1 (Subtype.ext h), htt, rfl, ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨u₀, hu₀, hqu₀⟩ := hne
  let lam : S.Qt →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun y => S.q (tl y - y)
      map_add' := fun y y' => by
        have e : tl (y + y') - (y + y') = (tl y - y) + (tl y' - y') := by
          rw [map_add]
          abel
        rw [e, map_add_eq, polar_commSpace_eq_zero t.2 htt (sub_mem_commSpace tl y)
          (sub_mem_commSpace tl y'), add_zero]
      map_smul' := fun c y => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [map_smul, ← smul_sub, map_smul_zmod2] }
  have hlam : ∀ y, lam y = S.q (tl y - y) := fun _ => rfl
  obtain ⟨y₀, hy₀⟩ := mem_commSpace.mp hu₀
  have hlam0 : lam y₀ = 1 := by
    rw [hlam, hy₀]
    exact zmod2_eq_one_of_ne_zero hqu₀
  have hrange : LinearMap.range lam = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • y₀, by rw [map_smul, hlam0, smul_eq_mul, mul_one]⟩
  have hdim := LinearMap.finrank_range_add_finrank_ker lam
  rw [hrange, finrank_top, finrank_self] at hdim
  set K := LinearMap.ker lam with hK
  have hKinv : ∀ x ∈ Rbar S g t, ∀ y ∈ K, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) y ∈ K := by
    intro x hx y hy
    rw [LinearMap.mem_ker, hlam] at hy ⊢
    have e : tl ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) y) - (x : S.Qt ≃ₗ[ZMod 2] S.Qt) y =
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (tl y - y) := by
      rw [map_sub, htl, ← coe_mul_apply, ← coe_mul_apply, commute_of_mem_Rbar H.conj_mem hx]
    rw [e, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2]
    exact hy
  set P := LinearMap.BilinForm.orthogonal S.q.polarBilin K with hP
  have hPdim : finrank (ZMod 2) P = 1 := by
    rw [hP, LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate]
    omega
  have hPne : P ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hPdim
    omega
  have hPinv : ∀ x ∈ Rbar S g t, ∀ u ∈ P, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ P := by
    intro x hx u hu
    rw [hP, LinearMap.BilinForm.mem_orthogonal_iff] at hu ⊢
    intro k hk
    have h1 := hu _ (hKinv _ (inv_mem hx) k hk)
    rw [polarBilin_apply_apply] at h1 ⊢
    rwa [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2,
      apply_inv_apply_O] at h1
  have hle := Submodule.finrank_mono (Vt_le_of_invariant H hPne hPinv)
  have := hL.two_le_finrank
  omega

end CFSG.LargeExtraspecial.S6
