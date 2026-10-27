module

public import CFSG.CGT.Stroth77.Stroth3VCase

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

theorem crdT_cocycle_mul {e f x : G} (hf : f ∈ Subgroup.normalizer (D : Set G))
    (hre : e⁻¹ * x * e * x⁻¹ ∈ D) (hrf : f⁻¹ * x * f * x⁻¹ ∈ D) :
    (e * f)⁻¹ * x * (e * f) * x⁻¹ ∈ D ∧
      crdT dD.e ((e * f)⁻¹ * x * (e * f) * x⁻¹) =
        dD.thetaT hf (crdT dD.e (e⁻¹ * x * e * x⁻¹)) + crdT dD.e (f⁻¹ * x * f * x⁻¹) := by
  have hc : f⁻¹ * (e⁻¹ * x * e * x⁻¹) * f ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp hf _).mp hre
  have key : (e * f)⁻¹ * x * (e * f) * x⁻¹ =
      (f⁻¹ * (e⁻¹ * x * e * x⁻¹) * f) * (f⁻¹ * x * f * x⁻¹) := by group
  rw [key]
  refine ⟨mul_mem hc hrf, ?_⟩
  rw [crdT_mul dD.e hc hrf, ← dD.thetaT_crdT hf hre]

theorem crdT_cocycle_uvt {e : G} (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D)
    (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) :
    e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹ ∈ D ∧
      crdT dD.e (e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹) =
        crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) +
          τ.action.φuv (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹)) := by
  have huvi : dD.uv⁻¹ = dD.uv := inv_eq_of_mul_eq_one_right dD.uv_sq
  have hrt' : dD.uv⁻¹ * (e⁻¹ * dD.t * e * dD.t⁻¹) * dD.uv ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp dD.uv_mem _).mp ht
  have huvt : e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹ =
      (e⁻¹ * dD.uv * e * dD.uv⁻¹) * (dD.uv⁻¹ * (e⁻¹ * dD.t * e * dD.t⁻¹) * dD.uv) := by
    rw [huvi]
    have hs : ∀ y, dD.uv * (dD.uv * y) = y := fun y => by rw [← mul_assoc, dD.uv_sq, one_mul]
    simp only [mul_inv_rev, mul_assoc, hs, inv_mul_cancel_left, mul_inv_cancel_left]
    rw [huvi]
  rw [huvt]
  exact ⟨mul_mem huv hrt', by
    rw [crdT_mul dD.e huv hrt', crdT_conj dD.e dD.uv_mem dD.uv_conj ht]⟩

theorem thetaT_cob {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    {φ : Torus τ.k →+ Torus τ.k} (hc : ∀ x, dD.thetaT hg (φ x) = φ (dD.thetaT hg x))
    (c₀ : Torus τ.k) :
    dD.thetaT hg (c₀ - φ c₀) = dD.thetaT hg c₀ - φ (dD.thetaT hg c₀) := by
  rw [map_sub, hc]

theorem crdT_cocycle_of_mem_uv {d : G} (hd : d ∈ D) :
    d⁻¹ * dD.uv * d * dD.uv⁻¹ ∈ D ∧
      crdT dD.e (d⁻¹ * dD.uv * d * dD.uv⁻¹) = τ.action.φuv (crdT dD.e d) - crdT dD.e d := by
  obtain ⟨hm, hc⟩ := crdT_conj_mul dD.e (e := 1) dD.uv_mem dD.uv_sq dD.uv_conj
    (by simp) hd
  simp only [one_mul] at hm hc
  refine ⟨hm, ?_⟩
  rw [hc, show (1 : G)⁻¹ * dD.uv * 1 * dD.uv⁻¹ = 1 by group, crdT_one]
  abel

theorem crdT_cocycle_of_mem_t {d : G} (hd : d ∈ D) :
    d⁻¹ * dD.t * d * dD.t⁻¹ ∈ D ∧
      crdT dD.e (d⁻¹ * dD.t * d * dD.t⁻¹) = τ.action.φt (crdT dD.e d) - crdT dD.e d := by
  obtain ⟨hm, hc⟩ := crdT_conj_mul dD.e (e := 1) dD.t_mem dD.t_sq dD.t_conj
    (by simp) hd
  simp only [one_mul] at hm hc
  refine ⟨hm, ?_⟩
  rw [hc, show (1 : G)⁻¹ * dD.t * 1 * dD.t⁻¹ = 1 by group, crdT_one]
  abel

theorem c_eq_ofT : (dD.c : G) = dD.ofT Torus.c := rfl

theorem crdT_sq_coset {e d x : G} (he : e ∈ Subgroup.normalizer (D : Set G))
    (hx : x ∈ Subgroup.normalizer (D : Set G)) (hx2 : x * x = 1)
    {φ : Torus τ.k →+ Torus τ.k} (hφ : ∀ y, dD.thetaT hx y = φ y)
    (hr : e⁻¹ * x * e * x⁻¹ ∈ D) (hsq : e * e ∈ D) (hd : d ∈ D) :
    (e * d * x) * (e * d * x) ∈ D ∧
      crdT dD.e ((e * d * x) * (e * d * x)) =
        crdT dD.e (e * e) + dD.thetaT he (crdT dD.e d) + crdT dD.e (e⁻¹ * x * e * x⁻¹) +
          φ (crdT dD.e d) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have h1 : e⁻¹ * d * e ∈ D := (Subgroup.mem_normalizer_iff''.mp he d).mp hd
  have h2 : x⁻¹ * d * x ∈ D := (Subgroup.mem_normalizer_iff''.mp hx d).mp hd
  have key : (e * d * x) * (e * d * x) =
      (e * e) * (e⁻¹ * d * e) * (e⁻¹ * x * e * x⁻¹) * (x⁻¹ * d * x) := by
    calc (e * d * x) * (e * d * x) = e * d * x * e * d * x := by group
      _ = (e * e) * (e⁻¹ * d * e) * (e⁻¹ * x * e * x⁻¹) * (x * d * x) := by group
      _ = _ := by rw [hxi]
  rw [key]
  refine ⟨mul_mem (mul_mem (mul_mem hsq h1) hr) h2, ?_⟩
  rw [crdT_mul dD.e (mul_mem (mul_mem hsq h1) hr) h2, crdT_mul dD.e (mul_mem hsq h1) hr,
    crdT_mul dD.e hsq h1, ← dD.thetaT_crdT he hd, ← dD.thetaT_crdT hx hd, hφ]

theorem false_of_twist_fix {f g x : G} (hf : f ∈ Subgroup.normalizer (D : Set G))
    (hx : x ∈ Subgroup.normalizer (D : Set G)) {φ : Torus τ.k →+ Torus τ.k}
    (hφ : ∀ y, dD.thetaT hx y = φ y) (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hxf : f⁻¹ * x * f = g * x) {y : ℤ} (hθg : ∀ v, dD.thetaT hg v = y • v) {k : ℕ}
    (hexp : ∀ w, φ w = w → (2 ^ k : ℤ) • w = 0) {v : Torus τ.k} (hv : y • φ v = v)
    (hv0 : (2 ^ k : ℤ) • v ≠ 0) : False := by
  have hfi := inv_mem hf
  have h1 : dD.thetaT (mul_mem (mul_mem (inv_mem hf) hx) hf) v = v := by
    rw [dD.thetaT_congr _ (mul_mem hg hx) hxf, dD.thetaT_mul hg hx, hθg, hφ, map_zsmul, hv]
  rw [dD.thetaT_conj hx hf, hφ] at h1
  have h2 : φ (dD.thetaT hfi v) = dD.thetaT hfi v := by
    have := congrArg (dD.thetaT hfi) h1
    rwa [dD.thetaT_inv_thetaT] at this
  have h3 := hexp _ h2
  rw [← map_zsmul] at h3
  apply hv0
  have := congrArg (dD.thetaT hf) h3
  rwa [dD.thetaT_thetaT_inv, map_zero] at this

end StrothWeakTypeData

namespace Torus

theorem zsmul_c_cases {k : Fin 3 → ℕ} (hk : 1 ≤ k 0) (l : ℤ)
    (h : l • (Torus.c : Torus k) + l • Torus.c = 0) :
    l • (Torus.c : Torus k) = 0 ∨ l • (Torus.c : Torus k) = (2 ^ (k 0 - 1) : ℕ) • Torus.c := by
  have h0 : (l : ZMod (2 ^ k 0)) + (l : ZMod (2 ^ k 0)) = 0 := by
    have := congrFun h 0
    simpa [Torus.c, gen] using this
  have hneg : -(l : ZMod (2 ^ k 0)) = (l : ZMod (2 ^ k 0)) := neg_eq_of_add_eq_zero_left h0
  rw [ZMod.neg_eq_self_iff] at hneg
  rcases hneg with hz | hv
  · left
    funext i
    fin_cases i <;> simp [Torus.c, gen, hz]
  · right
    have hval : (l : ZMod (2 ^ k 0)) = ((2 ^ (k 0 - 1) : ℕ) : ZMod (2 ^ k 0)) := by
      rw [← ZMod.natCast_zmod_val (l : ZMod (2 ^ k 0))]
      congr 1
      have h2 : 2 ^ k 0 = 2 * 2 ^ (k 0 - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    funext i
    fin_cases i <;> simp [Torus.c, gen, hval]

end Torus

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem mem_of_cocycle_cob (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R) (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D) (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D)
    (c₀ : Torus τ.k)
    (h1 : crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) = c₀ - τ.action.φuv c₀)
    (h2 : crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) = c₀ - τ.action.φt c₀) : e ∈ D := by
  have hd := dD.ofT_mem c₀
  obtain ⟨huv', cuv⟩ := crdT_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj huv hd
  obtain ⟨ht', ct⟩ := crdT_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj ht hd
  rw [dD.crdT_ofT, h1] at cuv
  rw [dD.crdT_ofT, h2] at ct
  have e1 : (e * dD.ofT c₀)⁻¹ * dD.uv * (e * dD.ofT c₀) * dD.uv⁻¹ = 1 :=
    crdT_inj dD.e huv' (one_mem D) (by rw [cuv, crdT_one]; abel)
  have e2 : (e * dD.ofT c₀)⁻¹ * dD.t * (e * dD.ofT c₀) * dD.t⁻¹ = 1 :=
    crdT_inj dD.e ht' (one_mem D) (by rw [ct, crdT_one]; abel)
  have hR : e * dD.ofT c₀ ∈ hS.R := mul_mem he (hS.D_le_R hd)
  have key : e * dD.ofT c₀ ∈ D := by
    refine h.mem_of_commute (hS.R_le_S hR) (hS.R_le_centralizer_omega hR) ?_ ?_
    · rw [← h.uv_eq]
      rw [mul_inv_eq_one, mul_assoc, inv_mul_eq_iff_eq_mul] at e1
      exact e1.symm
    · rw [← h.t_eq]
      rw [mul_inv_eq_one, mul_assoc, inv_mul_eq_iff_eq_mul] at e2
      exact e2.symm
  simpa using mul_mem key (inv_mem hd)

theorem mul_inv_mem_of_cocycle_cob (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    {e f : G} (he : e ∈ hS.R1 dD.uv dD.t) (hf : f ∈ hS.R1 dD.uv dD.t) (c₀ : Torus τ.k)
    (h1 : crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) =
      crdT dD.e (f⁻¹ * dD.uv * f * dD.uv⁻¹) + (c₀ - τ.action.φuv c₀))
    (h2 : crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) =
      crdT dD.e (f⁻¹ * dD.t * f * dD.t⁻¹) + (c₀ - τ.action.φt c₀)) : e * f⁻¹ ∈ D := by
  have hk : e * f⁻¹ ∈ hS.R1 dD.uv dD.t := mul_mem he (inv_mem hf)
  obtain ⟨hkR, hkuv, hkt⟩ := hk
  obtain ⟨hfR, hfuv, hft⟩ := hf
  have hfN := hS.R_le_normalizer hfR
  have hfiN := inv_mem hfN
  have euv := dD.crdT_cocycle_mul (e := e * f⁻¹) (x := dD.uv) hfN hkuv hfuv
  have et := dD.crdT_cocycle_mul (e := e * f⁻¹) (x := dD.t) hfN hkt hft
  rw [show e * f⁻¹ * f = e by group] at euv et
  rw [euv.2, add_comm, add_left_cancel_iff] at h1
  rw [et.2, add_comm, add_left_cancel_iff] at h2
  have hfi : f⁻¹ ∈ hS.R1 dD.uv dD.t := (hS.R1 dD.uv dD.t).inv_mem ⟨hfR, hfuv, hft⟩
  have cuv : ∀ x, dD.thetaT hfiN (τ.action.φuv x) = τ.action.φuv (dD.thetaT hfiN x) := fun x => by
    have := dD.thetaT_comm_of_conj_mem hfiN dD.uv_mem hfi.2.1 x
    rwa [dD.thetaT_uv, dD.thetaT_uv] at this
  have ct : ∀ x, dD.thetaT hfiN (τ.action.φt x) = τ.action.φt (dD.thetaT hfiN x) := fun x => by
    have := dD.thetaT_comm_of_conj_mem hfiN dD.t_mem hfi.2.2 x
    rwa [dD.thetaT_t, dD.thetaT_t] at this
  refine h.mem_of_cocycle_cob hS hkR hkuv hkt (dD.thetaT hfiN c₀) ?_ ?_
  · have := congrArg (dD.thetaT hfiN) h1
    rwa [dD.thetaT_inv_thetaT, dD.thetaT_cob hfiN cuv] at this
  · have := congrArg (dD.thetaT hfiN) h2
    rwa [dD.thetaT_inv_thetaT, dD.thetaT_cob hfiN ct] at this

theorem cocycle_proj_rho (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R) (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D)
    (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) :
    (hS.proj dD.ρ e)⁻¹ * dD.uv * hS.proj dD.ρ e * dD.uv⁻¹ ∈ D ∧
      (hS.proj dD.ρ e)⁻¹ * dD.t * hS.proj dD.ρ e * dD.t⁻¹ ∈ D ∧
      crdT dD.e ((hS.proj dD.ρ e)⁻¹ * dD.uv * hS.proj dD.ρ e * dD.uv⁻¹) =
        τ.action.φρ (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) +
          τ.action.φuv (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹))) ∧
      crdT dD.e ((hS.proj dD.ρ e)⁻¹ * dD.t * hS.proj dD.ρ e * dD.t⁻¹) =
        τ.action.φρ (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹)) := by
  have hp : hS.proj dD.ρ e = e * (e⁻¹ * hS.proj dD.ρ e) := by group
  obtain ⟨tw1, tw2⟩ := h.rho_twist hS he huv ht hp
  rw [← hp] at tw1 tw2
  have huvi : dD.uv⁻¹ = dD.uv := inv_eq_of_mul_eq_one_right dD.uv_sq
  have hrt' : dD.uv⁻¹ * (e⁻¹ * dD.t * e * dD.t⁻¹) * dD.uv ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp dD.uv_mem _).mp ht
  have huvt : e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹ =
      (e⁻¹ * dD.uv * e * dD.uv⁻¹) * (dD.uv⁻¹ * (e⁻¹ * dD.t * e * dD.t⁻¹) * dD.uv) := by
    rw [huvi]
    have hs : ∀ y, dD.uv * (dD.uv * y) = y := fun y => by rw [← mul_assoc, dD.uv_sq, one_mul]
    simp only [mul_inv_rev, mul_assoc, hs, inv_mul_cancel_left, mul_inv_cancel_left]
    rw [huvi]
  have hmem : e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹ ∈ D := by
    rw [huvt]; exact mul_mem huv hrt'
  have cρ := fun {g : G} (hg : g ∈ D) => crdT_conj dD.e dD.ρ_mem dD.ρ_conj hg
  have cuv := fun {g : G} (hg : g ∈ D) => crdT_conj dD.e dD.uv_mem dD.uv_conj hg
  have m1 : dD.ρ⁻¹ * (e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹) * dD.ρ ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp hmem
  have m2 : dD.ρ⁻¹ * (e⁻¹ * dD.uv * e * dD.uv⁻¹) * dD.ρ ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp huv
  refine ⟨tw1 ▸ m1, tw2 ▸ m2, ?_, ?_⟩
  · rw [tw1, cρ hmem, huvt, crdT_mul dD.e huv hrt', cuv ht]
  · rw [tw2, cρ huv]

theorem conj_u_mem_R (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R) : dD.u⁻¹ * e * dD.u ∈ hS.R := by
  have huS : dD.u ∈ (F.S : Subgroup G) := h.u_eq ▸ F.u_mem_S
  have := (Subgroup.mem_normalizer_iff''.mp
    (mem_normalizer_inf_centralizer_omegaIn huS dD.u_mem dD.u_sq) e).mp he
  exact this

theorem cocycle_conj_u (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D) (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) :
    (dD.u⁻¹ * e * dD.u)⁻¹ * dD.uv * (dD.u⁻¹ * e * dD.u) * dD.uv⁻¹ ∈ D ∧
      (dD.u⁻¹ * e * dD.u)⁻¹ * dD.t * (dD.u⁻¹ * e * dD.u) * dD.t⁻¹ ∈ D ∧
      crdT dD.e ((dD.u⁻¹ * e * dD.u)⁻¹ * dD.uv * (dD.u⁻¹ * e * dD.u) * dD.uv⁻¹) =
        τ.action.φu (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹)) ∧
      crdT dD.e ((dD.u⁻¹ * e * dD.u)⁻¹ * dD.t * (dD.u⁻¹ * e * dD.u) * dD.t⁻¹) =
        τ.action.φu (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) +
          τ.action.φuv (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹))) := by
  have hui : dD.u⁻¹ = dD.u := inv_eq_of_mul_eq_one_right dD.u_sq
  have huvi : dD.uv⁻¹ = dD.uv := inv_eq_of_mul_eq_one_right dD.uv_sq
  obtain ⟨hmem, hcrd⟩ := dD.crdT_cocycle_uvt huv ht
  have cu := fun {g : G} (hg : g ∈ D) => crdT_conj dD.e dD.u_mem dD.u_conj hg
  have nu := fun {g : G} (hg : g ∈ D) => (Subgroup.mem_normalizer_iff''.mp dD.u_mem g).mp hg
  have g1 : dD.u * dD.uv * dD.u⁻¹ = dD.uv := by rw [← dD.uv_comm_u]; group
  have hc' : dD.u * dD.uv⁻¹ = dD.uv⁻¹ * dD.u := by rw [huvi]; exact dD.uv_comm_u.symm
  have g2 : dD.u * dD.t * dD.u⁻¹ = dD.uv * dD.t := by
    calc dD.u * dD.t * dD.u⁻¹ = dD.u * (dD.t * dD.u) := by rw [hui, mul_assoc]
      _ = dD.u * (dD.u * dD.uv * dD.t) := by rw [dD.t_u]
      _ = (dD.u * dD.u) * dD.uv * dD.t := by group
      _ = dD.uv * dD.t := by rw [dD.u_sq, one_mul]
  have g3 : (dD.uv * dD.t)⁻¹ = dD.u * dD.t⁻¹ * dD.u⁻¹ := by rw [← g2]; group
  have k1 : (dD.u⁻¹ * e * dD.u)⁻¹ * dD.uv * (dD.u⁻¹ * e * dD.u) * dD.uv⁻¹ =
      dD.u⁻¹ * (e⁻¹ * dD.uv * e * dD.uv⁻¹) * dD.u := by
    calc (dD.u⁻¹ * e * dD.u)⁻¹ * dD.uv * (dD.u⁻¹ * e * dD.u) * dD.uv⁻¹
        = dD.u⁻¹ * e⁻¹ * (dD.u * dD.uv * dD.u⁻¹) * e * dD.u * dD.uv⁻¹ := by group
      _ = dD.u⁻¹ * e⁻¹ * dD.uv * e * (dD.u * dD.uv⁻¹) := by rw [g1]; group
      _ = dD.u⁻¹ * e⁻¹ * dD.uv * e * (dD.uv⁻¹ * dD.u) := by rw [hc']
      _ = dD.u⁻¹ * (e⁻¹ * dD.uv * e * dD.uv⁻¹) * dD.u := by group
  have k2 : (dD.u⁻¹ * e * dD.u)⁻¹ * dD.t * (dD.u⁻¹ * e * dD.u) * dD.t⁻¹ =
      dD.u⁻¹ * (e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹) * dD.u := by
    calc (dD.u⁻¹ * e * dD.u)⁻¹ * dD.t * (dD.u⁻¹ * e * dD.u) * dD.t⁻¹
        = dD.u⁻¹ * e⁻¹ * (dD.u * dD.t * dD.u⁻¹) * e * dD.u * dD.t⁻¹ := by group
      _ = dD.u⁻¹ * e⁻¹ * (dD.uv * dD.t) * e * dD.u * dD.t⁻¹ := by rw [g2]
      _ = dD.u⁻¹ * (e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹) * dD.u := by rw [g3]; group
  rw [k1, k2]
  exact ⟨nu huv, nu hmem, cu huv, by rw [cu hmem, hcrd]⟩

theorem proj_rho_mul_inv_mem (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hρH : ∀ ruv rt : Torus τ.k, ruv + τ.action.φuv ruv = 0 → rt + τ.action.φt rt = 0 →
      ruv + τ.action.φuv rt = rt + τ.action.φt ruv →
      ∃ d₀ : Torus τ.k, τ.action.φρ (ruv + τ.action.φuv rt) = ruv - d₀ + τ.action.φuv d₀ ∧
        τ.action.φρ ruv = rt - d₀ + τ.action.φt d₀)
    {e : G} (he : e ∈ hS.R1 dD.uv dD.t) : hS.proj dD.ρ e * e⁻¹ ∈ D := by
  obtain ⟨heR, huv, ht⟩ := he
  obtain ⟨puv, pt, p1, p2⟩ := h.cocycle_proj_rho hS heR huv ht
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj huv ht
  obtain ⟨d₀, s1, s2⟩ := hρH _ _ c1 c2 c3
  refine h.mul_inv_mem_of_cocycle_cob hS ⟨hS.proj_mem dD.ρ_mem heR, puv, pt⟩ ⟨heR, huv, ht⟩
    (-d₀) ?_ ?_
  · rw [p1, s1, map_neg]; abel
  · rw [p2, s2, map_neg]; abel

theorem conj_u_mul_inv_mem (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (huH : ∀ ruv rt : Torus τ.k, ruv + τ.action.φuv ruv = 0 → rt + τ.action.φt rt = 0 →
      ruv + τ.action.φuv rt = rt + τ.action.φt ruv →
      ∃ d : Torus τ.k, τ.action.φu ruv = ruv - d + τ.action.φuv d ∧
        τ.action.φu (ruv + τ.action.φuv rt) = rt - d + τ.action.φt d)
    {e : G} (he : e ∈ hS.R1 dD.uv dD.t) : (dD.u⁻¹ * e * dD.u) * e⁻¹ ∈ D := by
  obtain ⟨heR, huv, ht⟩ := he
  obtain ⟨puv, pt, p1, p2⟩ := cocycle_conj_u hS huv ht
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj huv ht
  obtain ⟨d, s1, s2⟩ := huH _ _ c1 c2 c3
  refine h.mul_inv_mem_of_cocycle_cob hS ⟨h.conj_u_mem_R hS heR, puv, pt⟩ ⟨heR, huv, ht⟩
    (-d) ?_ ?_
  · rw [p1, s1, map_neg]; abel
  · rw [p2, s2, map_neg]; abel

theorem thetaT_comm_rho (hS : Local.Setting (F.S : Subgroup G) D) {e : G} (he : e ∈ hS.R)
    (hpe : hS.proj dD.ρ e * e⁻¹ ∈ D) (y : Torus τ.k) :
    dD.thetaT (hS.R_le_normalizer he) (τ.action.φρ y) =
      τ.action.φρ (dD.thetaT (hS.R_le_normalizer he) y) := by
  have hp := hS.proj_mem dD.ρ_mem he
  have heN := hS.R_le_normalizer he
  have h1 : ∀ x, dD.thetaT (hS.R_le_normalizer hp) x = dD.thetaT heN x := fun x => by
    rw [dD.thetaT_congr _ (mul_mem (Subgroup.le_normalizer hpe) heN)
        (by group : hS.proj dD.ρ e = hS.proj dD.ρ e * e⁻¹ * e),
      dD.thetaT_mul (Subgroup.le_normalizer hpe) heN, dD.thetaT_of_mem _ hpe]
  have key := dD.thetaT_proj hS dD.ρ_mem he (τ.action.φρ y)
  rw [dD.thetaT_conj heN dD.ρ_mem, ← dD.thetaT_ρ y, dD.thetaT_inv_thetaT, dD.thetaT_ρ,
    dD.thetaT_ρ, h1] at key
  exact key

theorem thetaT_comm_u (hS : Local.Setting (F.S : Subgroup G) D) {e : G} (he : e ∈ hS.R)
    (hue : dD.u⁻¹ * e * dD.u * e⁻¹ ∈ D) (y : Torus τ.k) :
    dD.thetaT (hS.R_le_normalizer he) (τ.action.φu y) =
      τ.action.φu (dD.thetaT (hS.R_le_normalizer he) y) := by
  have heN := hS.R_le_normalizer he
  have hcN : dD.u⁻¹ * e * dD.u ∈ Subgroup.normalizer (D : Set G) :=
    mul_mem (mul_mem (inv_mem dD.u_mem) heN) dD.u_mem
  have h1 : ∀ x, dD.thetaT hcN x = dD.thetaT heN x := fun x => by
    rw [dD.thetaT_congr _ (mul_mem (Subgroup.le_normalizer hue) heN)
        (by group : dD.u⁻¹ * e * dD.u = dD.u⁻¹ * e * dD.u * e⁻¹ * e),
      dD.thetaT_mul (Subgroup.le_normalizer hue) heN, dD.thetaT_of_mem _ hue]
  have key := dD.thetaT_conj heN dD.u_mem (τ.action.φu y)
  rw [← dD.thetaT_u y, dD.thetaT_inv_thetaT, dD.thetaT_u, dD.thetaT_u, h1] at key
  exact key

theorem proj_rho_one (hS : Local.Setting (F.S : Subgroup G) D) : hS.proj dD.ρ 1 = 1 := by
  rw [hS.proj_eq_of_mem (by rw [mul_one, inv_mul_cancel]; exact one_mem _)]
  group

theorem proj_rho_inv (hS : Local.Setting (F.S : Subgroup G) D) {e : G} (he : e ∈ hS.R) :
    hS.proj dD.ρ e⁻¹ = (hS.proj dD.ρ e)⁻¹ := by
  have h0 := hS.proj_mul dD.ρ_mem he (inv_mem he)
  rw [mul_inv_cancel, proj_rho_one hS] at h0
  exact (eq_inv_of_mul_eq_one_right h0.symm)

theorem proj_rho_conj_u (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R) :
    hS.proj dD.ρ (dD.u⁻¹ * e * dD.u) = dD.u⁻¹ * hS.proj dD.ρ⁻¹ e * dD.u := by
  have hu1 : dD.u * dD.ρ = dD.ρ⁻¹ * dD.u := by
    have h0 := dD.u_rho
    have hui : dD.u⁻¹ = dD.u := inv_eq_of_mul_eq_one_right dD.u_sq
    calc dD.u * dD.ρ = (dD.u * dD.ρ * dD.u * dD.ρ) * dD.ρ⁻¹ * dD.u⁻¹ := by group
      _ = dD.ρ⁻¹ * dD.u := by rw [h0, hui]; group
  have hprojU : ∀ x ∈ hS.R, hS.proj dD.u x = dD.u⁻¹ * x * dD.u := fun x hx =>
    hS.proj_eq_of_mem (h.conj_u_mem_R hS hx)
  rw [← hprojU e he, ← hS.proj_mul_left dD.u_mem dD.ρ_mem he, hu1,
    hS.proj_mul_left (inv_mem dD.ρ_mem) dD.u_mem he,
    hprojU _ (hS.proj_mem (inv_mem dD.ρ_mem) he)]

theorem exists_normalized (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hfix : ∀ x : Torus τ.k, τ.action.φρ x = x → ∃ l : ℤ, x = l • Torus.c)
    (huc : τ.action.φu Torus.c = Torus.c) (hk0 : 1 ≤ τ.k 0)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (τ.k 0 - 1) * dD.u)
    {e : G} (heR : e ∈ hS.R) (hpe : hS.proj dD.ρ e * e⁻¹ ∈ D)
    (hue : dD.u⁻¹ * e * dD.u * e⁻¹ ∈ D) :
    ∃ d ∈ D, hS.proj dD.ρ (e * d) = e * d ∧ dD.u * (e * d) = e * d * dD.u := by
  have heN := hS.R_le_normalizer heR
  have hfix' : e⁻¹ * hS.proj dD.ρ e ∈ D := by
    have := (Subgroup.mem_normalizer_iff''.mp heN _).mp hpe
    convert this using 1; group
  obtain ⟨d₁, hd₁, hp₁⟩ := hS.exists_proj_fixed dD.ρ_mem dD.rho_odd heR hfix'
  refine ⟨d₁, hd₁, hp₁, ?_⟩
  set e₁ := e * d₁ with he₁
  have he₁R : e₁ ∈ hS.R := mul_mem heR (hS.D_le_R hd₁)
  have he₁N := hS.R_le_normalizer he₁R
  have hue₁ : dD.u⁻¹ * e₁ * dD.u * e₁⁻¹ ∈ D := by
    have hud : dD.u⁻¹ * d₁ * dD.u ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.u_mem _).mp hd₁
    have hd' : e * ((dD.u⁻¹ * d₁ * dD.u) * d₁⁻¹) * e⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp heN _).mp (mul_mem hud (inv_mem hd₁))
    have := mul_mem hue hd'
    convert this using 1
    rw [he₁]; group
  set s := e₁⁻¹ * (dD.u⁻¹ * e₁ * dD.u) with hs
  have hsD : s ∈ D := by
    have := (Subgroup.mem_normalizer_iff''.mp he₁N _).mp hue₁
    convert this using 1; rw [hs]; group
  have hρinv : hS.proj dD.ρ⁻¹ e₁ = e₁ := by
    conv_lhs => rw [← hp₁]
    rw [← hS.proj_mul_left dD.ρ_mem (inv_mem dD.ρ_mem) he₁R, mul_inv_cancel, hS.proj_one he₁R]
  have hps : hS.proj dD.ρ s = s := by
    rw [hs, hS.proj_mul dD.ρ_mem (inv_mem he₁R) (h.conj_u_mem_R hS he₁R),
      h.proj_rho_conj_u hS he₁R, hρinv, proj_rho_inv hS he₁R, hp₁]
  have hsρ : τ.action.φρ (crdT dD.e s) = crdT dD.e s := by
    have hρs : dD.ρ⁻¹ * s * dD.ρ ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp hsD
    have := hS.proj_eq_of_mem (hS.D_le_R hρs)
    rw [hps] at this
    rw [← crdT_conj dD.e dD.ρ_mem dD.ρ_conj hsD, ← this]
  obtain ⟨l, hl⟩ := hfix _ hsρ
  have hsu : s * (dD.u⁻¹ * s * dD.u) = 1 := by
    rw [hs]
    calc e₁⁻¹ * (dD.u⁻¹ * e₁ * dD.u) * (dD.u⁻¹ * (e₁⁻¹ * (dD.u⁻¹ * e₁ * dD.u)) * dD.u)
        = e₁⁻¹ * (dD.u * dD.u)⁻¹ * e₁ * (dD.u * dD.u) := by group
      _ = 1 := by rw [dD.u_sq]; group
  have hus' : dD.u⁻¹ * s * dD.u ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.u_mem _).mp hsD
  have hus : crdT dD.e (dD.u⁻¹ * s * dD.u) = crdT dD.e s := by
    rw [crdT_conj dD.e dD.u_mem dD.u_conj hsD, hl, map_zsmul, huc]
  have h2l : l • (Torus.c : Torus τ.k) + l • Torus.c = 0 := by
    have := congrArg (crdT dD.e) hsu
    rw [crdT_mul dD.e hsD hus', hus, crdT_one, hl] at this
    exact this
  have hsus : dD.u⁻¹ * s * dD.u = s := crdT_inj dD.e hus' hsD hus
  rcases Torus.zsmul_c_cases hk0 l h2l with h0 | h1
  · have hs1 : s = 1 := crdT_inj dD.e hsD (one_mem D) (by rw [hl, h0, crdT_one])
    have hc : dD.u⁻¹ * e₁ * dD.u = e₁ := by
      rw [hs] at hs1
      exact (inv_mul_eq_one.mp hs1).symm
    calc dD.u * e₁ = dD.u * (dD.u⁻¹ * e₁ * dD.u) := by rw [hc]
      _ = e₁ * dD.u := by group
  · exfalso
    have hsc : s = (dD.c : G) ^ 2 ^ (τ.k 0 - 1) := by
      rw [dD.c_eq_ofT, ← dD.ofT_crdT hsD, hl, h1]
      unfold StrothWeakTypeData.ofT
      rw [map_nsmul, toMul_nsmul, Subgroup.coe_pow]
    have hs2 : s * s = 1 := by
      have := hsu
      rwa [hsus] at this
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    apply hfus e₁
    have key : e₁⁻¹ * dD.u⁻¹ * e₁ = s * dD.u⁻¹ := by rw [hs]; group
    have key2 : e₁⁻¹ * dD.u * e₁ = dD.u * s⁻¹ := by
      have := congrArg (·⁻¹) key
      simpa [mul_assoc] using this
    rw [key2, hsi, ← hsc]
    calc dD.u * s = dD.u * (dD.u⁻¹ * s * dD.u) := by rw [hsus]
      _ = s * dD.u := by group

theorem cocycle_normalized (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) (hp : hS.proj dD.ρ e = e) (hu : dD.u * e = e * dD.u) :
    τ.action.φρ (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) +
        τ.action.φuv (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹))) =
          crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) ∧
      τ.action.φρ (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹)) =
        crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) ∧
      τ.action.φu (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹)) =
        crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) ∧
      τ.action.φu (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) +
        τ.action.φuv (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹))) =
          crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) := by
  obtain ⟨heR, huv, ht⟩ := he
  obtain ⟨-, -, p1, p2⟩ := h.cocycle_proj_rho hS heR huv ht
  obtain ⟨-, -, q1, q2⟩ := cocycle_conj_u hS huv ht
  have hue : dD.u⁻¹ * e * dD.u = e := by
    calc dD.u⁻¹ * e * dD.u = dD.u⁻¹ * (dD.u * e) := by rw [hu]; group
      _ = e := by group
  rw [hp] at p1 p2
  rw [hue] at q1 q2
  exact ⟨p1.symm, p2.symm, q1.symm, q2.symm⟩

theorem sq_normalized (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) (hp : hS.proj dD.ρ e = e) (hsq : e * e ∈ D) :
    τ.action.φρ (crdT dD.e (e * e)) = crdT dD.e (e * e) ∧
      τ.action.φuv (crdT dD.e (e * e)) - crdT dD.e (e * e) =
        dD.thetaT (hS.R_le_normalizer he.1) (crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹)) +
          crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) ∧
      τ.action.φt (crdT dD.e (e * e)) - crdT dD.e (e * e) =
        dD.thetaT (hS.R_le_normalizer he.1) (crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹)) +
          crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) := by
  obtain ⟨heR, huv, ht⟩ := he
  have heN := hS.R_le_normalizer heR
  refine ⟨?_, ?_, ?_⟩
  · have hpp : hS.proj dD.ρ (e * e) = e * e := by rw [hS.proj_mul dD.ρ_mem heR heR, hp]
    have hρs : dD.ρ⁻¹ * (e * e) * dD.ρ ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp hsq
    have := hS.proj_eq_of_mem (hS.D_le_R hρs)
    rw [hpp] at this
    rw [← crdT_conj dD.e dD.ρ_mem dD.ρ_conj hsq, ← this]
  · rw [← (dD.crdT_cocycle_of_mem_uv hsq).2, ← (dD.crdT_cocycle_mul heN huv huv).2]
  · rw [← (dD.crdT_cocycle_of_mem_t hsq).2, ← (dD.crdT_cocycle_mul heN ht ht).2]

theorem conj_mem_R1 (hS : Local.Setting (F.S : Subgroup G) D) {x : G}
    (hxR : x ∈ Subgroup.normalizer (hS.R : Set G)) (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (huvx : x * dD.uv = dD.uv * x) (htx : x * dD.t = dD.t * x) {e : G}
    (he : e ∈ hS.R1 dD.uv dD.t) : x⁻¹ * e * x ∈ hS.R1 dD.uv dD.t := by
  obtain ⟨heR, huv, ht⟩ := he
  have key : ∀ z : G, x * z = z * x → e⁻¹ * z * e * z⁻¹ ∈ D →
      (x⁻¹ * e * x)⁻¹ * z * (x⁻¹ * e * x) * z⁻¹ ∈ D := by
    intro z hc hr
    have hcomm : Commute x z := hc
    have := (Subgroup.mem_normalizer_iff''.mp hxN _).mp hr
    convert this using 1
    calc (x⁻¹ * e * x)⁻¹ * z * (x⁻¹ * e * x) * z⁻¹
        = x⁻¹ * e⁻¹ * (x * z) * x⁻¹ * e * x * z⁻¹ := by group
      _ = x⁻¹ * e⁻¹ * (z * x) * x⁻¹ * e * x * z⁻¹ := by rw [hc]
      _ = x⁻¹ * e⁻¹ * z * e * (x * z⁻¹) := by group
      _ = x⁻¹ * e⁻¹ * z * e * (z⁻¹ * x) := by rw [hcomm.inv_right.eq]
      _ = x⁻¹ * (e⁻¹ * z * e * z⁻¹) * x := by group
  exact ⟨(Subgroup.mem_normalizer_iff''.mp hxR e).mp heR, key _ huvx huv, key _ htx ht⟩

theorem exists_mem_R_conj_mem_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hnorm : hS.R ≤ Subgroup.normalizer ((hS.R1 dD.uv dD.t : Subgroup G) : Set G))
    (hlt : hS.R1 dD.uv dD.t < hS.R) :
    ∃ f ∈ hS.R, f ∉ hS.R1 dD.uv dD.t ∧ f⁻¹ * dD.uv * f * dD.uv⁻¹ ∈ hS.R1 dD.uv dD.t ∧
      f⁻¹ * dD.t * f * dD.t⁻¹ ∈ hS.R1 dD.uv dD.t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen : ∀ x ∈ ({dD.uv, dD.t} : Set G), x ∈ (F.S : Subgroup G) ∧
      x ∈ Subgroup.normalizer (D : Set G) ∧ x * x = 1 ∧ x * dD.uv = dD.uv * x ∧
      x * dD.t = dD.t * x := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨h.uv_mem_S, dD.uv_mem, dD.uv_sq, rfl, dD.uv_comm_t⟩
    · exact ⟨h.t_mem_S, dD.t_mem, dD.t_sq, dD.uv_comm_t.symm, rfl⟩
  have hPS : Subgroup.closure ({dD.uv, dD.t} : Set G) ≤ (F.S : Subgroup G) :=
    (Subgroup.closure_le _).mpr fun x hx => (hgen x hx).1
  have hPQ : Subgroup.closure ({dD.uv, dD.t} : Set G) ≤ Subgroup.normalizer (hS.R : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx =>
      mem_normalizer_inf_centralizer_omegaIn (hgen x hx).1 (hgen x hx).2.1 (hgen x hx).2.2.1
  have hPK : Subgroup.closure ({dD.uv, dD.t} : Set G) ≤
      Subgroup.normalizer ((hS.R1 dD.uv dD.t : Subgroup G) : Set G) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨-, hxN, hx2, huvx, htx⟩ := hgen x hx
    have hxR : x ∈ Subgroup.normalizer (hS.R : Set G) := hPQ (Subgroup.subset_closure hx)
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff'']
    intro e
    refine ⟨fun he => conj_mem_R1 hS hxR hxN huvx htx he, fun he => ?_⟩
    have := conj_mem_R1 hS hxR hxN huvx htx he
    rwa [show x⁻¹ * (x⁻¹ * e * x) * x = e by
      calc x⁻¹ * (x⁻¹ * e * x) * x = (x * x)⁻¹ * e * (x * x) := by group
        _ = e := by rw [hx2]; group] at this
  obtain ⟨f, hfR, hfR1, hf⟩ := CFSG.GroupTheory.exists_commutatorElement_mem_of_isPGroup
    (F.S.isPGroup'.to_le hPS) (F.S.isPGroup'.to_le hS.R_le_S) hlt hnorm hPQ hPK
  have hr : ∀ x ∈ ({dD.uv, dD.t} : Set G), f⁻¹ * x * f * x⁻¹ ∈ hS.R1 dD.uv dD.t := fun x hx => by
    have h' := (Subgroup.mem_normalizer_iff''.mp (hnorm hfR) _).mp
      (hf x (Subgroup.subset_closure hx))
    rw [commutatorElement_def] at h'
    convert h' using 1
    group
  exact ⟨f, hfR, hfR1, hr _ (by simp), hr _ (by simp)⟩

end StrothFrame.IsD

end CFSG.CGT.Stroth77
