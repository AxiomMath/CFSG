module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3TwinBase
public import CFSG.ClassicalInvolution.Q3.TA3Twin3M12

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Q3.TA3.Twin3
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_m12_q8
    (hd : TightDatum R S t) (hq : Q8Emb R t)
    (hH : TwinFr.TwinHyp (genFittingFStar Y) R S t)
    (hS : GH74.E2.Shape2M12 ↥(genFittingFStar Y)) : False := by
  set L := genFittingFStar Y
  have : L.Normal := genFittingFStar_normal Y
  let e := GH74.KGroups.TwoM12.quotEquiv hS
  have hcardL : Nat.card L = 190080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L),
      Nat.card_congr e.toEquiv, Sporadic.Mathieu.card_M12, hS.2.1]
  obtain ⟨s, hsR, hsL, hst⟩ := exists_sq_eq_of_index_le_two_q8 hq (index_le_two hH.cent hS.2.1
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


end CFSG.CGT.PushingUpLit.SolKNA.R4
