module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big6
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big7

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section Gamma

variable {F : Type} [Field F] [Finite F]

theorem gD_one_pow (x : Fˣ) (n : ℕ) : (gD x (1 : F ≃+* F)) ^ n = gD (x ^ n) 1 := by
  rw [gD_pow]
  simp only [nrm, one_pow, autU_one_aut, Finset.prod_const, Finset.card_range, one_pow]

theorem pow_half_order_eq_ubar (h2 : (2 : F) ≠ 0) {g : PGammaL2 F} (hg : IsMon g) {e K : ℕ}
    (he : 1 ≤ e) (hσ : g.right ^ 2 ^ e = 1) (hK : e < K) (hord : orderOf g = 2 ^ K) :
    g ^ 2 ^ (K - 1) = ubar F := by
  have h2e : 2 * 2 ^ (e - 1) = 2 ^ e := by
    rw [mul_comm, ← pow_succ, show e - 1 + 1 = e by omega]
  obtain ⟨x, hx⟩ := exists_gD_pow_even hg (2 ^ (e - 1))
  rw [h2e] at hx
  rw [hσ] at hx
  have hexp : e + (K - 1 - e) = K - 1 := by omega
  have hpow : g ^ 2 ^ (K - 1) = (g ^ 2 ^ e) ^ 2 ^ (K - 1 - e) := by
    rw [← pow_mul, show 2 ^ e * 2 ^ (K - 1 - e) = 2 ^ (K - 1) by
      rw [← pow_add, show e + (K - 1 - e) = K - 1 by omega]]
  have hmain : g ^ 2 ^ (K - 1) = gD (x ^ 2 ^ (K - 1 - e)) 1 := by
    rw [hpow, hx, gD_one_pow]
  have hK1 : 1 ≤ K := by omega
  have h2K : 2 ^ (K - 1) * 2 = 2 ^ K := by
    rw [← pow_succ, show K - 1 + 1 = K by omega]
  have hsqg : (gD (x ^ 2 ^ (K - 1 - e)) 1) ^ 2 = 1 := by
    rw [← hmain, ← pow_mul, h2K, ← hord, pow_orderOf_eq_one]
  have hzsq : (x ^ 2 ^ (K - 1 - e)) ^ 2 = 1 := by
    have h1 : (gD (x ^ 2 ^ (K - 1 - e)) 1) ^ 2 =
        gD ((x ^ 2 ^ (K - 1 - e)) ^ 2) 1 := gD_one_pow _ _
    rw [h1, ← gD_one_one] at hsqg
    exact (gD_eq_iff.mp hsqg).1
  have hzne : x ^ 2 ^ (K - 1 - e) ≠ 1 := by
    intro h1
    apply pow_ne_one_of_lt_orderOf (n := 2 ^ (K - 1))
      (pow_ne_zero _ (by norm_num)) (by rw [hord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
    rw [hmain, h1, gD_one_one]
  rcases (unit_sq_eq_one_iff (x ^ 2 ^ (K - 1 - e))).mp hzsq with h | h
  · exact absurd h hzne
  · rw [hmain, h, ubar_eq]

theorem sq_pow_eq_ubar (h2 : (2 : F) ≠ 0) {g : PGammaL2 F} (hg : IsMon g)
    (hσ : g.right * g.right = 1) {m : ℕ} (hm : 1 ≤ m) (hord : orderOf g = 2 ^ (m + 1)) :
    g ^ 2 ^ m = ubar F := by
  obtain ⟨x, hx⟩ := exists_gD_sq hg
  rw [pow_two, pow_two] at hx
  rw [hσ] at hx
  rw [← pow_two] at hx
  have hpow : g ^ 2 ^ m = (g ^ 2) ^ 2 ^ (m - 1) := by
    rw [← pow_mul, show 2 * 2 ^ (m - 1) = 2 ^ m by
      rw [mul_comm, ← pow_succ, show m - 1 + 1 = m by omega]]
  have hmain : g ^ 2 ^ m = gD (x ^ 2 ^ (m - 1)) 1 := by
    rw [hpow, hx, gD_one_pow]
  have hsqg : (gD (x ^ 2 ^ (m - 1)) 1) ^ 2 = 1 := by
    rw [← hmain, ← pow_mul, show 2 ^ m * 2 = 2 ^ (m + 1) by
      rw [← pow_succ], ← hord, pow_orderOf_eq_one]
  have hzsq : (x ^ 2 ^ (m - 1)) ^ 2 = 1 := by
    have h1 : (gD (x ^ 2 ^ (m - 1)) 1) ^ 2 = gD ((x ^ 2 ^ (m - 1)) ^ 2) 1 :=
      gD_one_pow _ _
    rw [h1, ← gD_one_one] at hsqg
    exact (gD_eq_iff.mp hsqg).1
  have hzne : x ^ 2 ^ (m - 1) ≠ 1 := by
    intro h1
    apply pow_ne_one_of_lt_orderOf (n := 2 ^ m)
      (pow_ne_zero _ (by norm_num)) (by rw [hord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
    rw [hmain, h1, gD_one_one]
  rcases (unit_sq_eq_one_iff (x ^ 2 ^ (m - 1))).mp hzsq with h | h
  · exact absurd h hzne
  · rw [hmain, h, ubar_eq]

end Gamma

section Easy

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}

theorem mulAut_quatInvolution {r : ℕ} (hr : 4 ≤ r) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))
    {β : MulAut X} (hβ : ∀ x ∈ Q, β x ∈ Q) : β (quatInvolution r e) = quatInvolution r e := by
  have hzQ : quatInvolution r e ∈ Q := quatInvolution_mem hr e
  have hyQ : β (quatInvolution r e) ∈ Q := hβ _ hzQ
  have hy2 : β (quatInvolution r e) * β (quatInvolution r e) = 1 := by
    rw [← map_mul, quatInvolution_sq hr e, map_one]
  have hy1 : β (quatInvolution r e) ≠ 1 := by
    intro h
    apply quatInvolution_ne_one hr e
    apply β.injective
    rw [h, map_one]
  exact eq_quatInvolution_of_sq hr e hyQ hy2 hy1

theorem rho_comm_ubar (E : PGamEmb X F) (hr : 4 ≤ r) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {β : MulAut X} (hβ : ∀ x ∈ Q, β x ∈ Q) : E.ρ β * ubar F = ubar F * E.ρ β := by
  have huz : ubar F = E.ρ (MulAut.conj (quatInvolution r e)) := by
    rw [ubar_eq, ← inl_pD_eq, ← hz]
  have hconj : E.ρ β * E.ρ (MulAut.conj (quatInvolution r e)) * (E.ρ β)⁻¹ =
      E.ρ (MulAut.conj (quatInvolution r e)) := by
    rw [← map_inv, ← map_mul, ← map_mul, mulAut_mul_conj_mul_inv,
      mulAut_quatInvolution hr e hβ]
  calc E.ρ β * ubar F
      = E.ρ β * E.ρ (MulAut.conj (quatInvolution r e)) := by rw [huz]
    _ = (E.ρ β * E.ρ (MulAut.conj (quatInvolution r e)) * (E.ρ β)⁻¹) * E.ρ β := by group
    _ = E.ρ (MulAut.conj (quatInvolution r e)) * E.ρ β := by rw [hconj]
    _ = ubar F * E.ρ β := by rw [huz]

theorem z2BigModelPiCyc_holds (r : ℕ) : Z2BigModelPiCyc r := by
  intro hr X _ _ p f hL Q e H hH hHQ g hgH hge
  obtain ⟨F, _, _, hF, h4, hp, E, hz⟩ :=
    exists_normalized_emb hL.simple hL.odd hL.even hL.model
      (quatInvolution_sq hr e) (quatInvolution_ne_one hr e)
      (quatInvolution_mem_fstar hL.index hr e)
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : F) ≠ 0 := (field_facts hp hL.odd hF h4).2
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hF h4
    omega
  have he1 : 1 ≤ padicValNat 2 f :=
    one_le_padicValNat_of_dvd hf0 (even_iff_two_dvd.mp hL.even)
  obtain ⟨K, hKord⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨g, hgH⟩
  rw [Subgroup.orderOf_mk] at hKord
  have hordg : orderOf g = 2 ^ K := hKord
  have hlt : 2 ^ padicValNat 2 f < 2 ^ K := by
    simpa [hordg] using hge
  have heK : padicValNat 2 f < K := by
    by_contra hnot
    have hle : 2 ^ K ≤ 2 ^ padicValNat 2 f :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hordE : orderOf (E.ρ g) = 2 ^ K := by
    rw [orderOf_injective E.ρ E.inj, hordg]
  have hσK : (E.ρ g).right ^ 2 ^ K = 1 := by
    rw [← right_pow, ← map_pow, ← hordg, pow_orderOf_eq_one, map_one]
    rfl
  have hσ : (E.ρ g).right ^ 2 ^ padicValNat 2 f = 1 :=
    ringAut_pow_two_pow_eq_one hF hσK
  have hmon : IsMon (E.ρ g) :=
    (isMon_iff_comm_ubar h2).mpr (rho_comm_ubar E hr e hz (hHQ g hgH))
  have hpow := pow_half_order_eq_ubar h2 hmon he1 hσ heK hordE
  have hub : ubar F = E.ρ (MulAut.conj (quatInvolution r e)) := by
    rw [ubar_eq, ← inl_pD_eq, ← hz]
  have hpoweq : (E.ρ g) ^ 2 ^ (K - 1) = E.ρ (MulAut.conj (quatInvolution r e)) := by
    rw [hpow, hub]
  have hhalf : orderOf g / 2 = 2 ^ (K - 1) := by
    rw [hordg]
    have hK1 : K - 1 + 1 = K := by omega
    conv_lhs =>
      rw [← hK1, pow_succ]
    rw [Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  exact E.inj (by rw [map_pow, hhalf]; exact hpoweq)

theorem quaternion_xa_conj_a {N : ℕ} [NeZero N] :
    QuaternionGroup.xa (0 : ZMod (2 * N)) * QuaternionGroup.a (1 : ZMod (2 * N)) *
        (QuaternionGroup.xa (0 : ZMod (2 * N)))⁻¹ =
      (QuaternionGroup.a (1 : ZMod (2 * N)))⁻¹ := by
  have hN : (((N : ℕ) : ZMod (2 * N)) + ((N : ℕ) : ZMod (2 * N))) = 0 :=
    quaternion_a_add_self
  have hinv_a : (QuaternionGroup.a (1 : ZMod (2 * N)) : QuaternionGroup N)⁻¹ =
      QuaternionGroup.a (-1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [QuaternionGroup.a_mul_a, add_neg_cancel]
    rfl
  have hinv_xa : (QuaternionGroup.xa (0 : ZMod (2 * N)) : QuaternionGroup N)⁻¹ =
      QuaternionGroup.xa ((N : ℕ) : ZMod (2 * N)) := by
    apply inv_eq_of_mul_eq_one_right
    rw [QuaternionGroup.xa_mul_xa, sub_zero, hN]
    rfl
  rw [hinv_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa, hinv_a]
  congr 1
  rw [zero_add]
  linear_combination hN

theorem z2BigModelPiQuat_holds (r : ℕ) : Z2BigModelPiQuat r := by
  intro hr X _ _ p f hL Q e H hH hHQ m hm B hBH eB
  obtain ⟨F, _, _, hF, h4, hp, E, hz⟩ :=
    exists_normalized_emb hL.simple hL.odd hL.even hL.model
      (quatInvolution_sq hr e) (quatInvolution_ne_one hr e)
      (quatInvolution_mem_fstar hL.index hr e)
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : F) ≠ 0 := (field_facts hp hL.odd hF h4).2
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  set x : MulAut X :=
    ((eB.symm (QuaternionGroup.a (1 : ZMod (2 * 2 ^ m))) : ↥B) : MulAut X) with hxdef
  set y : MulAut X :=
    ((eB.symm (QuaternionGroup.xa (0 : ZMod (2 * 2 ^ m))) : ↥B) : MulAut X) with hydef
  have hxH : x ∈ H := hBH (eB.symm (QuaternionGroup.a (1 : ZMod (2 * 2 ^ m)))).2
  have hxord : orderOf x = 2 ^ (m + 1) := by
    rw [hxdef, Subgroup.orderOf_coe]
    change orderOf (eB.symm.toMonoidHom (QuaternionGroup.a (1 : ZMod (2 * 2 ^ m)))) = 2 ^ (m + 1)
    rw [orderOf_injective eB.symm.toMonoidHom eB.symm.injective, QuaternionGroup.orderOf_a_one]
    rw [show 2 * 2 ^ m = 2 ^ (m + 1) by rw [pow_succ]; ring]
  have hρxord : orderOf (E.ρ x) = 2 ^ (m + 1) := by
    rw [orderOf_injective E.ρ E.inj, hxord]
  have hqB : eB.symm (QuaternionGroup.xa (0 : ZMod (2 * 2 ^ m))) *
      eB.symm (QuaternionGroup.a (1 : ZMod (2 * 2 ^ m))) *
      (eB.symm (QuaternionGroup.xa (0 : ZMod (2 * 2 ^ m))))⁻¹ =
      (eB.symm (QuaternionGroup.a (1 : ZMod (2 * 2 ^ m))))⁻¹ := by
    have h := congrArg (fun z : QuaternionGroup (2 ^ m) => eB.symm z)
      (quaternion_xa_conj_a (N := 2 ^ m))
    simpa only [map_mul, map_inv] using h
  have hq : y * x * y⁻¹ = x⁻¹ := by
    rw [hxdef, hydef]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      congrArg (fun z : ↥B => (z : MulAut X)) hqB
  have hρrel : E.ρ y * E.ρ x * (E.ρ y)⁻¹ = (E.ρ x)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul, hq, map_inv]
  have hτrel : (E.ρ y).right * (E.ρ x).right * ((E.ρ y).right)⁻¹ =
      ((E.ρ x).right)⁻¹ := by
    have h := congrArg (fun t : PGammaL2 F => t.right) hρrel
    simpa using h
  have hcommτ : (E.ρ y).right * (E.ρ x).right = (E.ρ x).right * (E.ρ y).right :=
    ringAut_comm hF hL.odd h4 _ _
  have hτeq : (E.ρ x).right = ((E.ρ x).right)⁻¹ := by
    rw [hcommτ, mul_assoc, mul_inv_cancel, mul_one] at hτrel
    exact hτrel
  have hτx : (E.ρ x).right * (E.ρ x).right = 1 := by
    rw [mul_eq_one_iff_eq_inv]
    exact hτeq
  have hρxmon : IsMon (E.ρ x) :=
    (isMon_iff_comm_ubar h2).mpr (rho_comm_ubar E hr e hz (hHQ x hxH))
  have hsq : (E.ρ x) ^ 2 ^ m = ubar F :=
    sq_pow_eq_ubar h2 hρxmon hτx hm hρxord
  have hub : ubar F = E.ρ (MulAut.conj (quatInvolution r e)) := by
    rw [ubar_eq, ← inl_pD_eq, ← hz]
  have hxpow : x ^ 2 ^ m =
      ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : MulAut X) := by
    rw [hxdef, ← Subgroup.coe_pow, ← map_pow, QuaternionGroup.a_one_pow]
  have hfinal : E.ρ (((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) :
      MulAut X)) = E.ρ (MulAut.conj (quatInvolution r e)) := by
    rw [← hxpow, map_pow, hsq, hub]
  exact E.inj hfinal

end Easy

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
