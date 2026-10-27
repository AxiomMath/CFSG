module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L16aF4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L16aQ8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L16aU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartPhi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

private theorem l16a_isEvenVec_permVec (σ : Equiv.Perm (Fin 8)) {v : Fin 8 → ZMod 2}
    (hv : IsEvenVec v) : IsEvenVec (permVec σ v) := by
  unfold IsEvenVec at hv ⊢
  have h : ∑ i, permVec σ v i = ∑ i, v i := Equiv.sum_comp σ.symm v
  rw [h]
  exact hv

private theorem l16a_vec_add_self (v : Fin 8 → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private theorem l16a_vec_add_one_add_self (v : Fin 8 → ZMod 2) : (v + 1) + v = 1 := by
  funext i
  have h : ∀ a : ZMod 2, a + 1 + a = 1 := by decide
  exact h (v i)

private theorem l16a_zpowers_inf {G : Type} [Group G] {t z : G} (ht : t * t = 1) (hz : z * z = 1)
    (ht1 : t ≠ 1) (htz : t ≠ z) {y : G} (hyt : y ∈ zpowers t) (hyz : y ∈ zpowers z) : y = 1 := by
  rcases l16a_zpowers_eq_one_or_self ht hyt with h | h
  · exact h
  · rcases l16a_zpowers_eq_one_or_self hz hyz with h' | h'
    · exact absurd (h.symm.trans h') ht1
    · exact absurd (h.symm.trans h') htz

section Ctx

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem l16a_heart_false (h37 : Asc82Lemma37) (h514 : Asc82Lemma514) (hHeart : Asc82HeartDict)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {x : G} (hxD : x ∈ centralizer (L : Set G))
    (hxN : x ∈ normalizer (A : Set G))
    (hxcm : ∀ q ∈ Qsub K₁ K₂ h, x * q * x⁻¹ * q⁻¹ ∈ zpowers z)
    (hxA : ⁅A, zpowers x⁆ = zpowers t) : False := by
  obtain ⟨Alt, φ, -, hperm, -, h12, h34⟩ := hHeart G t L S z r B A K₁ K₂ h c
  have hd := sec5b_heartData hperm
  obtain ⟨σ, -, hact⟩ := hd.act x hxN
  have hq := sec5b517_quad h514 c
  have hφ0 : φ 0 = 1 := by
    have h0 := hd.add 0 0 sec5b_isEvenVec_zero sec5b_isEvenVec_zero
    rw [add_zero] at h0
    exact mul_left_cancel (a := φ 0) (by rw [mul_one]; exact h0.symm)
  have hcomm_iff : ∀ v, IsEvenVec v → x * φ v = φ v * x →
      permVec σ v + v = 0 ∨ permVec σ v + v = 1 := by
    intro v hv hxv
    have e2 : φ v = φ (permVec σ v) := by
      rw [← hact v hv]
      calc φ v = φ v * x * x⁻¹ := by group
        _ = x * φ v * x⁻¹ := by rw [← hxv]
    rcases hd.inj v (permVec σ v) hv (l16a_isEvenVec_permVec σ hv) e2 with h1 | h1
    · left
      rw [h1]
      exact l16a_vec_add_self v
    · right
      rw [h1]
      exact l16a_vec_add_one_add_self v
  have hfirst : ∀ w, IsFirstBlockVec w → permVec σ w + w = 0 ∨ permVec σ w + w = 1 := by
    intro w hw
    have hmem : φ w ∈ A ⊓ (K₁ ⊔ K₂) := (h12 (φ w)).mpr ⟨w, hw, rfl⟩
    have hL : φ w ∈ L := l16a_sup_le_L c hmem.2
    exact hcomm_iff w hw.1 (Subgroup.mem_centralizer_iff.mp hxD (φ w) hL).symm
  have hsecond : ∀ w, IsSecondBlockVec w → permVec σ w + w = 0 ∨ permVec σ w + w = 1 := by
    intro w hw
    have hmem : φ w ∈ A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :=
      (h34 (φ w)).mpr ⟨w, hw, rfl⟩
    have hsq : φ w * φ w = 1 := by
      rw [← hd.add w w hw.1 hw.1, l16a_vec_add_self, hφ0]
    have hQw : φ w ∈ Qsub K₁ K₂ h := by
      have hpair : φ w ∈ Sec5B517Q8.pair hq 2 3 :=
        Sec5B517Q8.mem_pair_of_sq (i := 2) (j := 3) hq (by simpa [Kfam5] using hmem.2) hsq
      rw [l16a_Qsub_eq h514 c]
      exact hpair.1
    have hz1 : x * φ w * x⁻¹ * (φ w)⁻¹ ∈ zpowers z := hxcm (φ w) hQw
    have ht1 : φ w * x * (φ w)⁻¹ * x⁻¹ ∈ zpowers t := by
      rw [← hxA]
      exact Subgroup.commutator_mem_commutator hmem.1 (Subgroup.mem_zpowers x)
    have hz2 : φ w * x * (φ w)⁻¹ * x⁻¹ ∈ zpowers z := by
      have hinv : φ w * x * (φ w)⁻¹ * x⁻¹ = (x * φ w * x⁻¹ * (φ w)⁻¹)⁻¹ := by group
      rw [hinv]
      exact (zpowers z).inv_mem hz1
    have hone : φ w * x * (φ w)⁻¹ * x⁻¹ = 1 :=
      l16a_zpowers_inf c.t_mul_self c.z_mul_self c.t_ne_one (c.t_ne_z h37) ht1 hz2
    have hcm : φ w * x = x * φ w := commutatorElement_eq_one_iff_mul_comm.mp hone
    exact hcomm_iff w hw.1 hcm.symm
  have hσ1 : σ = 1 := heartPerm_eq_one_of_blocks σ hfirst hsecond
  have hAx : ∀ a ∈ A, a * x = x * a := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := hd.surj a ha
    have h1 := hact v hv
    have h2 : permVec (1 : Equiv.Perm (Fin 8)) v = v := by
      funext i
      rfl
    rw [hσ1, h2] at h1
    calc φ v * x = (x * φ v * x⁻¹) * x := by rw [h1]
      _ = x * φ v := by group
  have hbot : ⁅A, zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := hy
    have hc : Commute a x := hAx a ha
    exact (hc.zpow_right k).eq.symm
  have htmem : t ∈ zpowers t := Subgroup.mem_zpowers t
  rw [← hxA, hbot, Subgroup.mem_bot] at htmem
  exact c.t_ne_one htmem

end Ctx

end CFSG.OddStandard.SmallF3.Omega
