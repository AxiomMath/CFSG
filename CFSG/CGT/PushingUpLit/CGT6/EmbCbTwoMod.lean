module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoPair
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoFix

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)} {m : ℕ}

namespace CbtLift

variable {C : CbtY Y m} {t : MulAut V} {X : Subgroup (MulAut V)} (L : CbtLift C t X)

theorem t_wa : t (L.D.w L.D.a) = L.D.w L.D.b := by
  rw [L.D.htw, swap_apply_left]

theorem t_wb : t (L.D.w L.D.b) = L.D.w L.D.a := by
  rw [L.D.htw, swap_apply_right]

theorem vvec_mul_self [Finite V] (hV : ∀ v : V, v ^ 2 = 1) : L.vvec * L.vvec = 1 := by
  unfold vvec
  rw [mul_mul_mul_comm, L.D.w_sq hV, L.D.w_sq hV, mul_one]

theorem t_vvec : t L.vvec = L.vvec := by
  unfold vvec
  rw [map_mul, L.t_wa, L.t_wb, mul_comm]

theorem t_zvec [Finite V] (hV : ∀ v : V, v ^ 2 = 1) : t L.zvec = L.zvec * L.vvec := by
  unfold zvec vvec
  rw [L.t_wb, mul_left_comm, L.D.w_sq hV, mul_one]

theorem sElt_wa {x y : Fin m} (hxy : x ≠ y) : L.sElt t hxy (L.D.w L.D.a) = L.D.w L.D.a := by
  rw [L.sElt_w hxy, swap_apply_of_ne_of_ne (Ne.symm (L.hja x)) (Ne.symm (L.hja y))]

theorem sElt_wb {x y : Fin m} (hxy : x ≠ y) : L.sElt t hxy (L.D.w L.D.b) = L.D.w L.D.b := by
  rw [L.sElt_w hxy, swap_apply_of_ne_of_ne (Ne.symm (L.hjb x)) (Ne.symm (L.hjb y))]

theorem sElt_vvec {x y : Fin m} (hxy : x ≠ y) : L.sElt t hxy L.vvec = L.vvec := by
  unfold vvec
  rw [map_mul, L.sElt_wa hxy, L.sElt_wb hxy]

end CbtLift

namespace CbtCtx

variable [Finite V] {G T : Subgroup (MulAut V)} {t : MulAut V} {X₁ X₂ : Subgroup (MulAut V)}
  (K : CbtCtx G T Y t m X₁ X₂)

include K

theorem exists_pair : ∃ x y : Fin m, x ≠ y :=
  ⟨⟨0, by have := K.hm; omega⟩, ⟨1, by have := K.hm; omega⟩, by simp [Fin.ext_iff]⟩

theorem d0_eq_t {x y : Fin m} (hxy : x ≠ y) : K.d0 hxy = t := by
  by_contra hne
  refine K.h2 V K.hV G T Y K.h m K.hm K.hodd K.hY (K.d0 hxy) t (K.d0_mem hxy) K.htG ?_ ?_
    (by rw [sq]; exact K.d0_sq hxy) K.ht2 (K.d0_ne_one hxy) K.ht1 hne (K.d0_comm_t hxy).symm
  · exact Subgroup.mem_centralizer_iff.mpr fun z hz => K.d0_comm_Y hxy z hz
  · exact Subgroup.mem_centralizer_iff.mpr fun z hz => (K.t_comm_Y z hz).symm

theorem step2 {x y : Fin m} (hxy : x ≠ y) :
    K.L₂.vvec ∈ fixV X₁ ∧ ∃ n : ℕ, K.L₂.zvec * K.L₁.vvec ^ n ∈ fixV X₁ := by
  have hz : K.L₂.zvec ∈ commV X₁ ⊔ fixV X₁ := by
    rw [(K.L₁.D.split K.hm K.hodd).1]
    exact Subgroup.mem_top _
  obtain ⟨w', hw', f, hf, hzf⟩ := Subgroup.mem_sup.mp hz
  have hYw : ∀ z ∈ Y, z w' = w' := by
    intro z hz'
    have h1 : z (w' * f) = w' * f := by
      rw [hzf]
      exact K.L₂.y_wb z hz'
    have h2 : z f = f := mem_fixV.mp hf z (K.L₁.hYX hz')
    rw [map_mul, h2] at h1
    exact mul_right_cancel h1
  have hcases := cbtFixY_mem K.L₁.D K.hm K.hodd K.L₁.hYX hw' hYw
  have hs1w : K.L₁.sElt t hxy w' = w' := by
    rcases hcases with h | h | h | h
    · rw [h, map_one]
    · rw [h]
      exact K.L₁.sElt_wa hxy
    · rw [h]
      exact K.L₁.sElt_wb hxy
    · rw [h]
      exact K.L₁.sElt_vvec hxy
  have hs1 : K.L₁.sElt t hxy K.L₂.zvec = w' * t f := by
    rw [← hzf, map_mul, hs1w, K.L₁.sElt_fix hxy hf]
  have hs2 : K.L₂.sElt t hxy K.L₂.zvec = K.L₂.zvec := K.L₂.sElt_wb hxy
  have htz : t K.L₂.zvec = K.L₂.zvec * K.L₂.vvec := K.L₂.t_zvec K.hV
  have hts : t K.L₂.zvec = K.L₁.sElt t hxy K.L₂.zvec := by
    have h1 : (K.d0 hxy) K.L₂.zvec = t K.L₂.zvec := by rw [K.d0_eq_t hxy]
    rw [← h1]
    unfold d0
    rw [MulAut.mul_apply, hs2]
  have heq : w' * t f = w' * f * K.L₂.vvec :=
    calc w' * t f = K.L₁.sElt t hxy K.L₂.zvec := hs1.symm
      _ = t K.L₂.zvec := hts.symm
      _ = K.L₂.zvec * K.L₂.vvec := htz
      _ = w' * f * K.L₂.vvec := by rw [hzf]
  have htf : t f = f * K.L₂.vvec := mul_left_cancel (heq.trans (mul_assoc _ _ _))
  have hv2 : K.L₂.vvec ∈ fixV X₁ := by
    have h : K.L₂.vvec = f⁻¹ * t f := by rw [htf, inv_mul_cancel_left]
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hf) (CbData.fixV_invariant K.L₁.D.hn hf)
  have htw' : t w' = w' := by
    have h1 : t w' * (f * K.L₂.vvec) = w' * (f * K.L₂.vvec) :=
      calc t w' * (f * K.L₂.vvec) = t w' * t f := by rw [htf]
        _ = t (w' * f) := (map_mul t _ _).symm
        _ = t K.L₂.zvec := by rw [hzf]
        _ = K.L₂.zvec * K.L₂.vvec := htz
        _ = w' * (f * K.L₂.vvec) := by rw [← hzf, mul_assoc]
    exact mul_right_cancel h1
  refine ⟨hv2, ?_⟩
  rcases hcases with h | h | h | h
  · refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, ← hzf, h, one_mul]
    exact hf
  · exfalso
    rw [h, K.L₁.t_wa] at htw'
    exact K.L₁.D.hab (K.L₁.D.hwinj htw').symm
  · exfalso
    rw [h, K.L₁.t_wb] at htw'
    exact K.L₁.D.hab (K.L₁.D.hwinj htw')
  · refine ⟨1, ?_⟩
    have h' : w' = K.L₁.vvec := h
    rw [pow_one, ← hzf, h']
    have h2 : K.L₁.vvec * f * K.L₁.vvec = f := by
      rw [mul_comm K.L₁.vvec f, mul_assoc, K.L₁.vvec_mul_self K.hV, mul_one]
    rw [h2]
    exact hf

theorem step2_v : K.L₂.vvec ∈ fixV X₁ := by
  obtain ⟨x, y, hxy⟩ := K.exists_pair
  exact (K.step2 hxy).1

theorem step2_z : ∃ n : ℕ, K.L₂.zvec * K.L₁.vvec ^ n ∈ fixV X₁ := by
  obtain ⟨x, y, hxy⟩ := K.exists_pair
  exact (K.step2 hxy).2

theorem t_fix_R {r : V} (hr : r ∈ fixV X₁ ⊓ fixV X₂) : t r = r := by
  obtain ⟨-, -, -, hdisj⟩ := EndCfg4.card_commV_of_two_lifts K.h2 K.h K.hV K.hm K.hodd K.hY
    K.htG K.htT K.ht2 K.ht1 K.h₁ K.h₂ K.hne
  have h1 : cbtN t r ∈ (fixV X₁ ⊓ commV (Subgroup.zpowers t)) ⊓
      (fixV X₂ ⊓ commV (Subgroup.zpowers t)) := ⟨K.L₁.N_t_fix hr.1, K.L₂.N_t_fix hr.2⟩
  rw [hdisj, Subgroup.mem_bot] at h1
  unfold cbtN at h1
  exact mul_inv_eq_one.mp h1

end CbtCtx

end CFSG.CGT.PushingUpLit.CGT6
