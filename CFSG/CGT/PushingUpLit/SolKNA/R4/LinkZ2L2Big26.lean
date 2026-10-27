module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big21
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big14
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big19

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section Transport

theorem isSylow2In_map_of_injective {G K : Type} [Group G] [Group K] (φ : G →* K)
    (hφ : Function.Injective φ) {S : Subgroup G} (hS : IsSylow2In S ⊤) :
    IsSylow2In (S.map φ) φ.range := by
  refine ⟨Subgroup.map_le_range φ S, hS.2.1.map φ, ?_⟩
  intro V hV hV2 hSV
  have hV' : IsPGroup 2 ↥(V.comap φ) := hV2.comap_of_injective φ hφ
  have hSV' : S ≤ V.comap φ := Subgroup.map_le_iff_le_comap.mp hSV
  have hEq : V.comap φ = S := hS.2.2 (V.comap φ) le_top hV' hSV'
  calc V = (V.comap φ).map φ := (Subgroup.map_comap_eq_self hV).symm
    _ = S.map φ := by rw [hEq]

variable {X : Type} [Group X] [Finite X] {r : ℕ}

theorem exists_quat_le_sylow (Q : Subgroup X) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))
    {S : Subgroup X} (hS : IsSylow2In S ⊤) :
    ∃ (Q' : Subgroup X) (_ : ↥Q' ≃* QuaternionGroup (2 ^ (r - 2))), Q' ≤ S := by
  have hQ2 : IsPGroup 2 ↥Q := isPGroup_two_of_equiv_quaternion e
  obtain ⟨g, hg⟩ := exists_conj_ge_of_isSylow2In hS hQ2
  refine ⟨Q.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_⟩
  · exact (Subgroup.equivMapOfInjective Q (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.trans e
  · rintro y ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using mem_conjSub_iff.mp (hg hx)

end Transport

section Fix

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}
  {p f : ℕ}

theorem fix_quatInvolution [Fact p.Prime] (E : PGamEmb X F)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) (hf : Even f) (hidx : (genFittingFStar X).index ≤ 2) (hr : 4 ≤ r)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hq : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2))) {S : Subgroup X} (hS : IsSylow2In S ⊤)
    (hQS : Q ≤ S) {H : Subgroup (MulAut X)}
    (hSH : S.map (MulAut.conj : X →* MulAut X) ≤ H) (hH : IsPGroup 2 ↥H) :
    ∀ h ∈ H, h (quatInvolution r e) = quatInvolution r e := by
  let z := quatInvolution r e
  have hzS : z ∈ S := hQS (quatInvolution_mem hr e)
  have hzne : z ≠ 1 := quatInvolution_ne_one hr e
  let V : Subgroup X := H.comap (MulAut.conj : X →* MulAut X)
  have hV2 : IsPGroup 2 ↥V :=
    hH.comap_of_injective (MulAut.conj : X →* MulAut X) E.conjInj
  have hSV : S ≤ V := by
    intro s hs
    exact Subgroup.mem_comap.mpr (hSH (Subgroup.mem_map_of_mem (MulAut.conj : X →* MulAut X) hs))
  have hVS : V = S := hS.2.2 V le_top hV2 hSV
  have hVmem : ∀ x : X, MulAut.conj x ∈ H → x ∈ S := by
    intro x hx
    have hxV : x ∈ V := Subgroup.mem_comap.mpr hx
    rwa [hVS] at hxV
  have hSh : ∀ h ∈ H, ∀ s ∈ S, h s ∈ S := by
    intro h hh s hs
    apply hVmem (h s)
    have hconj : MulAut.conj s ∈ H :=
      hSH (Subgroup.mem_map_of_mem (MulAut.conj : X →* MulAut X) hs)
    have hmem : h * MulAut.conj s * h⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hh hconj) (H.inv_mem hh)
    rwa [mulAut_mul_conj_mul_inv] at hmem
  have hzcent : ∀ s ∈ S, z * s = s * z := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Nontrivial ↥S :=
      ⟨⟨⟨z, hzS⟩, ⟨1, S.one_mem⟩, fun h => hzne (Subtype.ext_iff.mp h)⟩⟩
    haveI : Nontrivial ↥(Subgroup.center ↥S) := IsPGroup.center_nontrivial hS.2.1
    obtain ⟨w, hwne⟩ := exists_ne (1 : ↥(Subgroup.center ↥S))
    have hw2 : ∃ k : ℕ, ((w : ↥S) : X) ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hS.2.1 (w : ↥S)
      exact ⟨k, by simpa [Subgroup.coe_pow] using congrArg (Subtype.val) hk⟩
    have hwQ : ∀ y ∈ Q, ((w : ↥S) : X) * y = y * ((w : ↥S) : X) := by
      intro y hy
      exact (congrArg (Subtype.val)
        (Subgroup.mem_center_iff.mp w.2 (⟨y, hQS hy⟩ : ↥S))).symm
    have hcent := cent_two_elements E e hF hp2 h4 hf hidx hr hz hσ₀1 hσ₀2 hq hwQ hw2
    have hwz : ((w : ↥S) : X) = z := by
      rcases hcent with h1 | h1
      · exact absurd (Subtype.ext (Subtype.ext h1)) hwne
      · exact h1
    intro s hs
    have hc : ((w : ↥S) : X) * s = s * ((w : ↥S) : X) :=
      (congrArg (Subtype.val) (Subgroup.mem_center_iff.mp w.2 (⟨s, hs⟩ : ↥S))).symm
    rw [hwz] at hc
    exact hc
  intro h hh
  have hcomm : ∀ s ∈ S, h z * s = s * h z := by
    intro s hs
    have hs' : h⁻¹ s ∈ S := hSh h⁻¹ (H.inv_mem hh) s hs
    calc h z * s = h (z * h⁻¹ s) := by rw [map_mul, MulAut.apply_inv_self]
      _ = h (h⁻¹ s * z) := by rw [hzcent (h⁻¹ s) hs']
      _ = s * h z := by rw [map_mul, MulAut.apply_inv_self]
  have hsq : h z * h z = 1 := by
    rw [← map_mul, quatInvolution_sq hr e, map_one]
  have hcent := cent_two_elements E e hF hp2 h4 hf hidx hr hz hσ₀1 hσ₀2 hq
    (x := h z) (fun y hy => hcomm y (hQS hy)) ⟨1, by rw [show 2 ^ 1 = 2 by norm_num, pow_two]; exact hsq⟩
  rcases hcent with h1 | h1
  · exact absurd (h.injective (by rw [h1, map_one])) hzne
  · exact h1

theorem isMon_rho_of_fix [Fact p.Prime] (E : PGamEmb X F)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {h : MulAut X} (hfix : h (quatInvolution r e) = quatInvolution r e) : IsMon (E.ρ h) := by
  have h2 : (2 : F) ≠ 0 := (field_facts (Fact.out) hp2 hF h4).2
  rw [isMon_iff_comm_ubar h2]
  have hub : ubar F = E.ρ (MulAut.conj (quatInvolution r e)) := by
    rw [ubar_eq, ← inl_pD_eq, ← hz]
  rw [hub]
  have hmul : h * MulAut.conj (quatInvolution r e) =
      MulAut.conj (h (quatInvolution r e)) * h := by
    rw [← mulAut_mul_conj_mul_inv h (quatInvolution r e)]
    group
  calc E.ρ h * E.ρ (MulAut.conj (quatInvolution r e))
      = E.ρ (h * MulAut.conj (quatInvolution r e)) := by rw [map_mul]
    _ = E.ρ (MulAut.conj (h (quatInvolution r e)) * h) := by rw [hmul]
    _ = E.ρ (MulAut.conj (quatInvolution r e) * h) := by rw [hfix]
    _ = E.ρ (MulAut.conj (quatInvolution r e)) * E.ρ h := by rw [map_mul]

end Fix

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
