module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Cls

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_cases4 : ∀ v : Fin 6 → ZMod 2, v 2 = v 3 → v 3 = v 4 → v 4 = v 5 →
    (v = 0 ∨ v = fun _ => 1) ∨ (v = Pi.single 0 1 ∨ v = Pi.single 0 1 + fun _ => 1) ∨
      (v = Pi.single 1 1 ∨ v = Pi.single 1 1 + fun _ => 1) ∨
      (v = Pi.single 0 1 + Pi.single 1 1 ∨ v = Pi.single 0 1 + Pi.single 1 1 + fun _ => 1) := by
  decide +kernel

theorem sec11_permVec_swap01 :
    ∀ v : Fin 6 → ZMod 2, v 0 = v 1 → permVec (Equiv.swap 0 1) v = v := by
  decide +kernel

namespace Sec11Perm

variable {A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem eq_or_eq_add_one (h : Sec11Perm A M Alt φ) {v w : Fin 6 → ZMod 2} (hvw : φ v = φ w) :
    v = w ∨ v = w + (fun _ => 1) := by
  rcases (h.eq_iff _ _).mp hvw with h1 | h1
  · exact Or.inl (sec11_vec_eq_of_add_eq_zero h1)
  · refine Or.inr (funext fun i => ?_)
    have key : ∀ a b : ZMod 2, a + b = 1 → a = b + 1 := by decide
    have := congrFun h1 i
    simp only [Pi.add_apply] at this ⊢
    exact key _ _ this

theorem rho_of_mem (h : Sec11Perm A M Alt φ) (hAM : A ≤ M) {a : G} (ha : a ∈ A) :
    h.rho a = 1 := by
  rw [h.rho_eq_one_iff (hAM ha)]
  intro b hb
  obtain ⟨v, rfl⟩ := h.surj a ha
  obtain ⟨w, rfl⟩ := h.surj b hb
  rw [h.comm v w]
  group

end Sec11Perm

namespace Sec11Model

variable {t z : G} {L S : Subgroup G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem t_sq (hm : Sec11Model t L S z K1 K2 T Alt φ) : t * t = 1 := by
  rw [hm.t_eq]
  exact hm.perm.sq _

theorem z_eq (hm : Sec11Model t L S z K1 K2 T Alt φ) :
    φ (Pi.single 0 1 + Pi.single 1 1) = z := by
  rw [hm.perm.mul, ← hm.t_eq, ← hm.tz_eq]
  calc t * (t * z) = (t * t) * z := by group
    _ = z := by rw [hm.t_sq, one_mul]

theorem cent_rho (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L) {c : G}
    (hc : c ∈ T) (hcQ : ∀ q ∈ secQ K1 K2, c * q = q * c) :
    hm.perm.rho c = 1 ∨ hm.perm.rho c = Equiv.swap 0 1 := by
  refine sec11_stab_pointwise _ fun v hv0 hv01 => ?_
  have h1 : c * φ v * c⁻¹ = φ v := by
    rw [hcQ _ ((hm.mem_Q v).mpr ⟨hv0, hv01⟩)]
    group
  exact hm.perm.eq_or_eq_add_one ((hm.perm.conj_apply (hTM hc) v).symm.trans h1)

theorem cent_ker (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L) {c : G}
    (hc : c ∈ T) (hcQ : ∀ q ∈ secQ K1 K2, c * q = q * c) (h1 : hm.perm.rho c = 1) :
    c = 1 ∨ c = t ∨ c = t * z ∨ c = z := by
  have hcA : c ∈ secA t S L := hm.cenTA c hc fun a ha =>
    mul_inv_eq_iff_eq_mul.mp (((hm.perm.rho_eq_one_iff (hTM hc)).mp h1) a ha)
  obtain ⟨v, rfl⟩ := hm.perm.surj c hcA
  have hfix : ∀ s ∈ sec11V4, permVec s v = v ∨ permVec s v = v + (fun _ => 1) := by
    intro s hs
    obtain ⟨q, hq, hqs⟩ := hm.Q_act_surj s hs
    have h2 : q * φ v * q⁻¹ = φ v := by
      rw [← hcQ q hq]
      group
    exact hm.perm.eq_or_eq_add_one ((hqs v).symm.trans h2)
  obtain ⟨h23, h34, h45⟩ := sec11_v4_fixed v hfix
  rcases sec11_cases4 v h23 h34 h45 with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl)
  · exact Or.inl hm.perm.map_zero
  · refine Or.inl ?_
    have := hm.perm.map_add_one 0
    rwa [zero_add, hm.perm.map_zero] at this
  · exact Or.inr (Or.inl hm.t_eq.symm)
  · rw [hm.perm.map_add_one]
    exact Or.inr (Or.inl hm.t_eq.symm)
  · exact Or.inr (Or.inr (Or.inl hm.tz_eq.symm))
  · rw [hm.perm.map_add_one]
    exact Or.inr (Or.inr (Or.inl hm.tz_eq.symm))
  · exact Or.inr (Or.inr (Or.inr hm.z_eq))
  · rw [hm.perm.map_add_one]
    exact Or.inr (Or.inr (Or.inr hm.z_eq))

theorem conj_t (hm : Sec11Model t L S z K1 K2 T Alt φ) {r : G}
    (hr : ∀ v, r * φ v * r⁻¹ = φ (permVec (Equiv.swap 0 1) v)) : r * t * r⁻¹ = t * z := by
  rw [hm.t_eq, hr, sec11_permVec_single]
  simp only [Equiv.swap_apply_left]
  rw [← hm.tz_eq, hm.t_eq]

theorem conj_z (hm : Sec11Model t L S z K1 K2 T Alt φ) {r : G}
    (hr : ∀ v, r * φ v * r⁻¹ = φ (permVec (Equiv.swap 0 1) v)) : r * z * r⁻¹ = z := by
  have h : permVec (Equiv.swap 0 1) (Pi.single 0 1 + Pi.single 1 1) =
      Pi.single 0 1 + Pi.single 1 1 :=
    sec11_permVec_swap01 _ (by simp [Pi.single_apply])
  conv_lhs => rw [← hm.z_eq, hr, h]
  exact hm.z_eq

end Sec11Model

end CFSG.OddStandard.SmallF3.Omega
