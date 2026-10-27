module

public import CFSG.LargeExtraspecial.S11EightA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.clSub_inf_fixSub_eq {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) :
    S.clSub (S.QG ⊓ S.Qa k) ⊓ fixSub S (S.Lbar k ⊓ Nbar S g t) = Vt S g t := by
  obtain ⟨hkz, htk⟩ := K.base_of_mem hk
  have hyk := hy.of_conj hk.1 hkz
  set P := S.clSub (S.QG ⊓ S.Qa k) with hP
  set X := S.Lbar k ⊓ Nbar S g t with hX
  have h1 : Nat.card X * 2 ^ finrank (ZMod 2) ↥(P ⊓ fixSub S X) = 2 ^ S.width :=
    card_mul_two_pow_finrank_fix hyk.hyp4 hyk.cons inf_le_left
  have h2 := card_Lbar_inf_Nbar hyk.hyp4 hyk.cons (K.linCase_of hy hk htk)
  rw [hy.Nbar_eq hk.1 hkz t, hy.Vt_eq hk.1 hkz t] at h2
  have hVP : Vt S g t ≤ P ⊓ fixSub S X := fun v hv =>
    ⟨K.Vt_le_clSub hy hk hv, fun ℓ hℓ => (mem_Nbar.mp hℓ.2).2 v hv⟩
  have hm := K.lin.two_le_finrank
  have hw := hy.hyp4.two_lt_width
  have h3 := Submodule.finrank_mono hVP
  have hd : finrank (ZMod 2) ↥(P ⊓ fixSub S X) = finrank (ZMod 2) (Vt S g t) := by
    have h4 : Nat.card X * 2 ^ (finrank (ZMod 2) ↥(P ⊓ fixSub S X) + (S.width - 1)) =
        Nat.card X * 2 ^ (finrank (ZMod 2) (Vt S g t) - 1 + S.width) := by
      rw [pow_add, pow_add, ← mul_assoc, ← mul_assoc, h1, h2, ← pow_add, ← pow_add]
      congr 1
      omega
    have h5 := Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left Nat.card_pos h4)
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hVP hd.symm).symm

variable (hCE : CentralExtInput.{u_G}) (hn : 6 ≤ S.width)
include hCE hn

theorem Conf.apply_sub_mem_Vt_of_commute {y : G} (hyM : y ∈ S.M)
    (hyE : ∀ e ∈ S.QG ⊓ S.Qa u, y * e = e * y) (hyN : S.ρ ⟨y, hyM⟩ ∈ Nbar S g t)
    (hyc : ∀ ℓ ∈ Nbar S g t, ℓ * S.ρ ⟨y, hyM⟩ = S.ρ ⟨y, hyM⟩ * ℓ) {w : S.Qt}
    (hw : w ∈ Wt S g t) :
    (S.ρ ⟨y, hyM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  set x := S.ρ ⟨y, hyM⟩ with hx
  set W := (Vt S g t).comap (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)
    with hW
  have hmem : ∀ v, v ∈ W ↔ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t := fun v => by
    rw [hW, Submodule.mem_comap, LinearMap.sub_apply]
    rfl
  refine (hmem w).mp (K.Wt_le hy hCE (fun v hv => (hmem v).mpr ?_)
    (fun k hk v hv => (hmem v).mpr ?_) hw)
  · exact K.apply_sub_mem_Vt_of_mem_fixSpace hy hCE hn hyN hv
  · rw [← K.clSub_inf_fixSub_eq hy hk]
    refine ⟨sub_mem ?_ hv, fun ℓ hℓ => ?_⟩
    · obtain ⟨p, hp, hpQ, rfl⟩ := S.mem_clSub_iff.mp hv
      rw [hx, S.ρ_cl _ hpQ]
      exact S.cl_mem_clSub (mem_inf.mpr ⟨S.conj_mem_QG hyM hpQ,
        conj_mem_Qa_of_commute' (mem_inf.mp hp).2 (hyE _ hk)⟩) (S.conj_mem_QG hyM hpQ)
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
        (Lbar_apply_sub_mem_span' hk.1 hv (mem_inf.mp hℓ).1)
      have hkV : S.cl (k * S.z * k⁻¹) ∈ Vt S g t := by
        rw [← K.timmesfeld_11_3 hy]
        exact S.cl_mem_clSub hk hk.1
      have hxk : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) = S.cl (k * S.z * k⁻¹) :=
        (mem_Nbar.mp hyN).2 _ hkV
      have hcomm : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
        rw [← coe_mul_apply, ← coe_mul_apply, hyc ℓ (mem_inf.mp hℓ).2]
      have hℓv : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + c • S.cl (k * S.z * k⁻¹) := by
        rw [hc]
        abel
      rw [map_sub, hcomm, hℓv, map_add, map_smul, hxk]
      abel

theorem Conf.commutator_mem_Qa {w : G} (hwQ : w ∈ S.QG) (hwW : S.cl w ∈ Wt S g t) :
    w * τ * w⁻¹ * (τ : G)⁻¹ ∈ S.Qa u := by
  have hcV : ∀ x ∈ S.QG, S.cl x ∈ Wt S g t →
      S.cl (x * τ * x⁻¹ * (τ : G)⁻¹) ∈ Vt S g t := fun x hx hxW => by
    rw [(K.commutator_facts hy hx).2.1, ← K.timmesfeld_11_7 hy hCE]
    exact sub_mem_Tt hxW
  have hcomm : ∀ x ∈ S.QG, S.cl x ∈ Wt S g t → ∀ c ∈ S.QG, S.cl c ∈ Vt S g t →
      x * c = c * x := fun x hx hxW c hc hcv => by
    have := mem_Wt.mp hxW _ hcv
    rw [S.polar_cl_eq_zero_iff hc hx] at this
    exact this.symm
  let WE : Subgroup G :=
    { carrier := {x | x ∈ S.QG ∧ S.cl x ∈ Wt S g t ∧ x * τ * x⁻¹ * (τ : G)⁻¹ ∈ S.Qa u}
      mul_mem' := by
        rintro x x' ⟨hx, hxW, hxc⟩ ⟨hx', hx'W, hx'c⟩
        refine ⟨S.QG.mul_mem hx hx', by rw [S.cl_mul hx hx']; exact add_mem hxW hx'W, ?_⟩
        have h1 := hcomm x hx hxW _ (K.commutator_facts hy hx').1 (hcV x' hx' hx'W)
        have e : x * x' * τ * (x * x')⁻¹ * (τ : G)⁻¹ =
            (x' * τ * x'⁻¹ * (τ : G)⁻¹) * (x * τ * x⁻¹ * (τ : G)⁻¹) := by
          calc x * x' * τ * (x * x')⁻¹ * (τ : G)⁻¹ =
                (x * (x' * τ * x'⁻¹ * (τ : G)⁻¹)) * x⁻¹ * (x * τ * x⁻¹ * (τ : G)⁻¹) := by
                group
            _ = ((x' * τ * x'⁻¹ * (τ : G)⁻¹) * x) * x⁻¹ * (x * τ * x⁻¹ * (τ : G)⁻¹) := by
                rw [h1]
            _ = _ := by group
        rw [e]
        exact mul_mem hx'c hxc
      one_mem' := ⟨S.QG.one_mem, by rw [S.cl_one]; exact zero_mem _, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, hxW, hxc⟩
        refine ⟨S.QG.inv_mem hx, by rw [S.cl_inv hx]; exact hxW, ?_⟩
        have h1 : Commute x (x * τ * x⁻¹ * (τ : G)⁻¹) :=
          hcomm x hx hxW _ (K.commutator_facts hy hx).1 (hcV x hx hxW)
        have h2 := h1.inv_right.eq
        have e : x⁻¹ * τ * x⁻¹⁻¹ * (τ : G)⁻¹ = (x * τ * x⁻¹ * (τ : G)⁻¹)⁻¹ := by
          calc x⁻¹ * τ * x⁻¹⁻¹ * (τ : G)⁻¹ =
                x⁻¹ * ((x * τ * x⁻¹ * (τ : G)⁻¹)⁻¹ * x) := by group
            _ = x⁻¹ * (x * (x * τ * x⁻¹ * (τ : G)⁻¹)⁻¹) := by rw [h2]
            _ = _ := by group
        rw [e]
        exact inv_mem hxc }
  have hτQ : (τ : G) ∉ S.QG := K.not_mem_QG
  have hle : Wt S g t ≤ S.clSub WE := by
    refine K.Wt_le hy hCE (fun v hv => ?_) (fun k hk v hv => ?_)
    · have hvW := fixSpace_le_Wt hy.hyp4 K.mem_Lbar K.ne_one hv
      rw [K.fixSpace_eq hy hCE hn] at hv
      obtain ⟨c, hc, hcQ, rfl⟩ := S.mem_clSub_iff.mp hv
      have hcτ : c * τ = τ * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
      refine S.cl_mem_clSub ⟨hcQ, hvW, ?_⟩ hcQ
      rw [hcτ, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · obtain ⟨p, hp, hpQ, rfl⟩ := S.mem_clSub_iff.mp hv
      have hτk : (τ : G) ∈ S.Qa k := by
        have hne : k * S.z * k⁻¹ ≠ u * S.z * u⁻¹ := fun h =>
          hτQ (by rw [K.conj_eq, ← h]; exact hk.1)
        rw [K.conj_eq]
        exact S.mem_Qa_symm hne hk.2
      refine S.cl_mem_clSub ⟨hpQ, K.clSub_le_Wt hy hk (S.cl_mem_clSub hp hpQ), ?_⟩ hpQ
      rcases (S.conjBy k).commutator_eq_one_or_z (mem_inf.mp hp).2 hτk with h | h
      · rw [h]
        exact one_mem _
      · have h' : p * τ * p⁻¹ * (τ : G)⁻¹ = k * S.z * k⁻¹ := h
        rw [h']
        exact hk.2
  obtain ⟨x, hx, hxQ, hxw⟩ := S.mem_clSub_iff.mp (hle hwW)
  rcases (S.cl_eq_cl_iff hxQ hwQ).mp hxw with rfl | rfl
  · exact hx.2.2
  · have hzτ : S.z * τ * S.z⁻¹ = τ := by
      rw [← S.z_comm τ.2, mul_inv_cancel_right]
    have e : x * S.z * τ * (x * S.z)⁻¹ * (τ : G)⁻¹ = x * τ * x⁻¹ * (τ : G)⁻¹ := by
      calc x * S.z * τ * (x * S.z)⁻¹ * (τ : G)⁻¹ = x * (S.z * τ * S.z⁻¹) * x⁻¹ * (τ : G)⁻¹ := by
            group
        _ = _ := by rw [hzτ]
    rw [e]
    exact hx.2.2

end CFSG.LargeExtraspecial.S11
