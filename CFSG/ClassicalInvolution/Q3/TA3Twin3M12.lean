module

public import CFSG.ClassicalInvolution.Q3.TA3Twin3M12Lift
public import CFSG.ClassicalInvolution.Q3.TA3Twin3M12Tab
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinDefs
public import CFSG.GH74.KGroups.TwoM12Aut
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinReduce
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLift

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.ComponentClassification
open scoped commutatorElement

namespace Twin3

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_witness {L : Subgroup Y} (hH : TwinFr.TwinHyp L R S t)
    {π : L →* NativeSporadic.M12} (hπs : Function.Surjective π) (hπk : π.ker = Subgroup.center L)
    {c : L} (hcZ : c ∈ Subgroup.center L) (hc1 : c ≠ 1) (hcc : c * c = 1)
    (hsq : ∀ v : L, π v * π v = 1 → v * v = E c (M12Cover.fixedCount (π v) == 0))
    {sK : L} (hsR : (sK : Y) ∈ R) (hss : sK * sK = ⟨t, hH.mem⟩) (h' : L)
    {γ X U : NativeSporadic.M12} (hγ : π (h' * sK * h'⁻¹) = γ) (hXX : X * X = 1)
    (hXγ : X * γ = γ * X) (hXU : X * U = U * X) (hUU : U * U = 1) (hUγ : U * γ * (U * γ) = 1)
    (hf1 : (M12Cover.fixedCount X == 0) = (M12Cover.fixedCount (X * (γ * γ)) == 0))
    (hf2 : ((M12Cover.fixedCount U == 0) ^^ (M12Cover.fixedCount (X * U) == 0) ^^
      (M12Cover.fixedCount (U * γ) == 0) ^^ (M12Cover.fixedCount (X * (U * γ)) == 0)) = true) :
    False := by
  set tK : L := ⟨t, hH.mem⟩
  set s' := h' * sK * h'⁻¹ with hs'
  set t' := h' * tK * h'⁻¹ with ht'
  have hst : s' * s' = t' := by rw [hs', ht', ← hss]; group
  have htt : tK * tK = 1 := Subtype.ext (by
    have h := pow_orderOf_eq_one t
    rwa [hH.datum.order, sq] at h)
  have htt' : t' * t' = 1 := by
    calc t' * t' = h' * (tK * tK) * h'⁻¹ := by rw [ht']; group
      _ = 1 := by rw [htt]; group
  have hπt : π t' = γ * γ := by rw [← hst, map_mul, hγ]
  have hfT : (M12Cover.fixedCount (π t') == 0) = false := by
    have h := hsq t' (by rw [← map_mul, htt', map_one])
    rw [htt'] at h
    cases hb : (M12Cover.fixedCount (π t') == 0)
    · rfl
    · rw [hb] at h
      exact absurd h.symm hc1
  obtain ⟨x, rfl⟩ := hπs X
  obtain ⟨u, rfl⟩ := hπs U
  set w := u⁻¹ * s' with hw
  have hπw : π w = π u * γ := by rw [hw, map_mul, map_inv, hγ, inv_eq_of_mul_eq_one_right hUU]
  have hxt : ⁅x, t'⁆ = 1 := by
    have hxt2 : π x * π t' = π t' * π x := by
      rw [hπt, ← mul_assoc, hXγ, mul_assoc, hXγ, mul_assoc]
    rw [commutator_lift hπk hcc hsq hXX (by rw [← map_mul, htt', map_one]) hxt2, hfT, hπt, hf1]
    cases M12Cover.fixedCount (π x * (γ * γ)) == 0 <;> rfl
  have hxs : ⁅x, s'⁆ = c := by
    have hxw : π x * π w = π w * π x := by
      rw [hπw, ← mul_assoc, hXU, mul_assoc, hXγ, mul_assoc]
    have h1 := commutator_lift hπk hcc hsq hXX hUU hXU
    have h2 := commutator_lift hπk hcc hsq hXX (by rw [hπw]; exact hUγ) hxw
    rw [hπw] at h2
    have hsw : s' = u * w := by rw [hw, mul_inv_cancel_left]
    have hcomm : ⁅x, u * w⁆ = ⁅x, u⁆ * (u * ⁅x, w⁆ * u⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hsw, hcomm, h2, E_comm hcZ, mul_inv_cancel_right, h1, E_mul hcc]
    have key : ∀ a b c d e : Bool, ((a ^^ b ^^ c) ^^ (a ^^ d ^^ e)) = (b ^^ c ^^ d ^^ e) := by
      decide
    rw [key, hf2]
    rfl
  refine false_of_commutator_eq hH hcZ hc1 hcc hsR (x := h'⁻¹ * x * h') ?_ ?_
  · have h := commutatorElement_eq_one_iff_mul_comm.1 hxt
    calc h'⁻¹ * x * h' * tK = h'⁻¹ * (x * t') * h' := by rw [ht']; group
      _ = h'⁻¹ * (t' * x) * h' := by rw [h]
      _ = tK * (h'⁻¹ * x * h') := by rw [ht']; group
  · calc ⁅h'⁻¹ * x * h', sK⁆ = h'⁻¹ * ⁅x, s'⁆ * h' := by
          rw [hs']
          simp only [commutatorElement_def]
          group
      _ = c := by rw [hxs, Subgroup.mem_center_iff.1 hcZ h'⁻¹, inv_mul_cancel_right]

theorem false_of_m12
    (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hH : TwinFr.TwinHyp (genFittingFStar Y) R S t)
    (hS : GH74.E2.Shape2M12 ↥(genFittingFStar Y)) : False := by
  set L := genFittingFStar Y
  have : L.Normal := genFittingFStar_normal Y
  let e := GH74.KGroups.TwoM12.quotEquiv hS
  have hcardL : Nat.card L = 190080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L),
      Nat.card_congr e.toEquiv, Sporadic.Mathieu.card_M12, hS.2.1]
  obtain ⟨s, hsR, hsL, hst⟩ := exists_sq_eq_of_index_le_two hd hc (index_le_two hH.cent hS.2.1
    (hcardL ▸ Nat.le_of_dvd (by norm_num) (GH74.KGroups.TwoM12.card_mulAut_dvd hS)))
  let π : L →* NativeSporadic.M12 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = Subgroup.center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hZne : Subgroup.center L ≠ ⊥ := fun h => by
    have h2 := hS.2.1
    rw [h, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZne
  have hcc : (a : L) * a = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center L) (x := a)
    rw [hS.2.1, sq] at h
    exact congrArg Subtype.val h
  have hc1 : (a : L) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hc2 : orderOf (a : L) = 2 := orderOf_eq_prime (by rw [sq]; exact hcc) hc1
  have hZc : Subgroup.center L = Subgroup.zpowers (a : L) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 a.2)
      (by rw [Nat.card_zpowers, hc2, hS.2.1])).symm
  obtain ⟨h40, h4, h0⟩ := M12Cover.m12_double_cover_involution_lift_orders
    ⟨hS.1.1.commutator_eq_top, hS.1.2.1⟩ hc2 hZc π hπs (hπk.trans hZc)
  have hsq : ∀ v : L, π v * π v = 1 → v * v = E (a : L) (M12Cover.fixedCount (π v) == 0) :=
    fun v hv => sq_lift (hπk.trans hZc) hc2 h40 h4 h0 hv
  set sK : L := ⟨s, hsL⟩
  set tK : L := ⟨t, hH.mem⟩
  have hss : sK * sK = tK := Subtype.ext hst
  have htt : tK * tK = 1 := Subtype.ext (by
    have h := pow_orderOf_eq_one t
    rwa [hd.order, sq] at h)
  have hγ4 : π sK ^ 2 ^ 2 = 1 := by
    rw [← map_pow, show sK ^ 2 ^ 2 = (sK * sK) * (sK * sK) by simp [pow_succ, mul_assoc], hss, htt,
      map_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hγ4)
  obtain ⟨P, hP⟩ := (IsPGroup.of_card (p := 2) (n := k)
    (by rw [Nat.card_zpowers, hk]) : IsPGroup 2 (Subgroup.zpowers (π sK))).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq NativeSporadic.M12 P M12Cover.sylow
  obtain ⟨h', rfl⟩ := hπs h
  have hmem : π h' * π sK * (π h')⁻¹ ∈ (M12Cover.sylow : Subgroup NativeSporadic.M12) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr
      (by simpa [mul_assoc] using hP (Subgroup.mem_zpowers _))
  rw [M12Cover.coe_sylow, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨j, hj, hjσ⟩ := M12Cover.SylowTable.exists_elt hmem
  set γ := π h' * π sK * (π h')⁻¹ with hγdef
  have hγ : π (h' * sK * h'⁻¹) = γ := by rw [map_mul, map_mul, map_inv]
  have hγ2 : γ * γ = π (h' * tK * h'⁻¹) := by
    rw [← hγ, ← map_mul, ← hss]
    congr 1
    group
  have htt' : h' * tK * h'⁻¹ * (h' * tK * h'⁻¹) = 1 := by
    calc h' * tK * h'⁻¹ * (h' * tK * h'⁻¹) = h' * (tK * tK) * h'⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have h2 : (γ : Equiv.Perm (Fin 12)) * γ ≠ 1 := by
    intro h1
    have h1' : γ * γ = 1 := Subtype.ext h1
    rw [hγ2, ← MonoidHom.mem_ker, hπk] at h1'
    have htK : tK = h' * tK * h'⁻¹ := by
      calc tK = h'⁻¹ * (h' * tK * h'⁻¹) * h' := by group
        _ = h' * tK * h'⁻¹ * h'⁻¹ * h' := by rw [Subgroup.mem_center_iff.1 h1' h'⁻¹]
        _ = h' * tK * h'⁻¹ := by group
    rw [← htK] at h1'
    obtain ⟨l, hl, hlt⟩ := hH.not_central
    exact hlt (congrArg Subtype.val (Subgroup.mem_center_iff.1 h1' ⟨l, hl⟩))
  have h4' : (γ : Equiv.Perm (Fin 12)) * γ * (γ * γ) = 1 := by
    have : γ * γ * (γ * γ) = 1 := by rw [hγ2, ← map_mul, htt', map_one]
    exact congrArg Subtype.val this
  have hf : M12W.fp ((γ : Equiv.Perm (Fin 12)) * γ) ≠ 0 := by
    change M12Cover.fixedCount (γ * γ) ≠ 0
    intro h0
    have h := hsq _ (by rw [← map_mul, htt', map_one])
    rw [htt', ← hγ2, h0] at h
    exact hc1 h.symm
  obtain ⟨X, U, hXm, hUm, hXX, hXγ, hXU, hUU, hUγ, hf1, hf2⟩ := M12W.exists_witness hj hjσ h2 h4' hf
  exact false_of_witness hH hπs hπk a.2 hc1 hcc hsq hsR hss h' (X := ⟨X, hXm⟩) (U := ⟨U, hUm⟩) hγ
    (Subtype.ext hXX) (Subtype.ext hXγ) (Subtype.ext hXU) (Subtype.ext hUU) (Subtype.ext hUγ) hf1
    hf2

end Twin3

open Twin3 in
theorem twin2M12Leaf_holds : Twin2M12Leaf := by
  intro Y _ _ _ _ hsmall hS R S t hd hc hE2 _ _ _ _
  exact (false_of_m12 hd hc (TwinFr.twinHyp_fstar hd hc hE2 hsmall) hS).elim

end CFSG.ClassicalInvolution.Q3.TA3
