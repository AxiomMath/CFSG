module

public import CFSG.ClassicalInvolution.Q3.Q3AMDB11
public import CFSG.ClassicalInvolution.Q3.Q3AMDB16
public import CFSG.ClassicalInvolution.Q3.Q3AMDB17

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP
open scoped commutatorElement

section Core


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem PspSetting.false_of_swap_partner (hset : PspSetting Ω K J S R T W z t K')
    {L : Subgroup G} (hL : L ∈ Ω) {e : G} (he : IsUniqueInvolution L e) (_hez : e ≠ z)
    (hcomm : e * z = z * e) (hsw : e * t * e⁻¹ = z * t)
    (hno : ¬ ∃ P : Subgroup G, IsSylow2In P L ∧ P ≤ Subgroup.centralizer ({z} : Set G)) :
    False := by
  have hbad := hset.bad
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hee : e * e = 1 := he.sq
  have hzz : z * z = 1 := hstd.hz.sq
  have htt : t * t = 1 := hstd.ht.sq
  have hu := hset.uniq_mul
  have hzt := hset.mul_comm_zt
  have hJΩ : J ∈ Ω := hstd.hJ.1
  have hK'Ω : K' ∈ Ω := hset.nbrK.1
  obtain ⟨t₁, t₂, t₃, R₁, R₂, R₃, hax⟩ := hbad.exists_axis_of_triangle hset.intrinsic
    hstd.stand.mem hstd.hJ hset.nbrK hset.nbrJ hstd.hz hstd.ht hu rfl
  obtain ⟨a, haR, b, hbR, ha2, hb2, hab⟩ := exists_quaternion_pair_of_isSylow2In
    (isClassicalMember3_of_uniqueInvolution hstd.stand.modU hJΩ hstd.ht) hax.syl₂ hax.z_mem₂
  have hJe : conjSub e J = K' := hset.conjSub_swap hsw
  have hK'e : conjSub e K' = J := by
    rw [← hJe, ← conjSub_mul, hee, conjSub_one]
  have hR₂Ω : R₂ ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hax.syl₂
  have hR₃Ω : R₃ ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hax.syl₃
  have hR₂K' : ∀ y ∈ R₂, conjSub y K' = K' :=
    normalizes_of_commutes_sylow hΩ hK'Ω hax.syl₃ hR₃Ω hax.comm₂₃
  have hnR₂ : ∀ x ∈ R₂,
      x ∈ Subgroup.normalizer ((oddCoreOf J ⊓ oddCoreOf K' : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreOf_inf (Or.inl ⟨conjSub_eq_self_of_mem (hax.syl₂.1 hx), hR₂K' x hx⟩)
  have hnz : z ∈ Subgroup.normalizer ((oddCoreOf J ⊓ oddCoreOf K' : Subgroup G) : Set G) :=
    mem_normalizer_oddCoreOf_inf (Or.inl
      ⟨normalizes_of_commutes_sylow hΩ hJΩ hax.syl₂ hR₂Ω hax.comm₁₂ z hax.z_mem₁,
        normalizes_of_commutes_sylow hΩ hK'Ω hax.syl₃ hR₃Ω hax.comm₁₃ z hax.z_mem₁⟩)
  have hne : e ∈ Subgroup.normalizer ((oddCoreOf J ⊓ oddCoreOf K' : Subgroup G) : Set G) :=
    mem_normalizer_oddCoreOf_inf (Or.inr ⟨hJe, hK'e⟩)
  have hcross := hset.cross_mem_oddCore hax hee hsw
  have hNodd : Odd (Nat.card ↥(oddCoreOf J ⊓ oddCoreOf K')) := odd_natCard_oddCoreOf_inf J K'
  set N : Subgroup G := oddCoreOf J ⊓ oddCoreOf K' with hN
  have hNΓ : Odd (Nat.card ↥(N.subgroupOf (Subgroup.normalizer (N : Set G)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.le_normalizer : N ≤ Subgroup.normalizer (N : Set G))).toEquiv]
    exact hNodd
  have htR : t ∈ R₂ := hax.z_mem₂
  obtain ⟨ha, hb, ηa, ηb, ηc, hea, hza, heb, hzb, hηa, hηb, hηc, hA, hB, hC⟩ :=
    exists_swap_lifts (N.subgroupOf (Subgroup.normalizer (N : Set G))) hNΓ
      (e := ⟨e, hne⟩) (z := ⟨z, hnz⟩) (t := ⟨t, hnR₂ t htR⟩) (a := ⟨a, hnR₂ a haR⟩)
      (b := ⟨b, hnR₂ b hbR⟩) (Subtype.ext hee) (Subtype.ext hzz) (Subtype.ext hcomm)
      (Subtype.ext hzt) (Subtype.ext htt) (Subtype.ext hsw) (Subtype.ext ha2) (Subtype.ext hb2)
      (Subtype.ext hab) (Subtype.ext (hax.comm₁₂ z hax.z_mem₁ a haR))
      (Subtype.ext (hax.comm₁₂ z hax.z_mem₁ b hbR))
      (Subgroup.mem_subgroupOf.mpr (hcross a haR a haR))
      (Subgroup.mem_subgroupOf.mpr (hcross a haR b hbR))
      (Subgroup.mem_subgroupOf.mpr (hcross b hbR a haR))
      (Subgroup.mem_subgroupOf.mpr (hcross b hbR b hbR))
  have hea' : e * (ha : G) = (ha : G) * e := congrArg Subtype.val hea
  have heb' : e * (hb : G) = (hb : G) * e := congrArg Subtype.val heb
  have hza' : z * (ha : G) = (ha : G) * z := congrArg Subtype.val hza
  have hzb' : z * (hb : G) = (hb : G) * z := congrArg Subtype.val hzb
  have hA' : (ha : G) * (ha : G) = z * (ηa : G) := congrArg Subtype.val hA
  have hB' : (hb : G) * (hb : G) = z * (ηb : G) := congrArg Subtype.val hB
  have hC' : (ha : G) * (hb : G) * (ha : G)⁻¹ * (hb : G)⁻¹ = z * (ηc : G) :=
    congrArg Subtype.val hC
  have hηaN : (ηa : G) ∈ N := Subgroup.mem_subgroupOf.mp hηa
  have hηbN : (ηb : G) ∈ N := Subgroup.mem_subgroupOf.mp hηb
  have hηcN : (ηc : G) ∈ N := Subgroup.mem_subgroupOf.mp hηc
  obtain ⟨eL⟩ := hset.exists_iso_of_mem hL
  have hCN := hset.centralizer_le_normalizer_of_mem hL he
  have hCe : ∀ g : G, g * e = e * g → g ∈ Subgroup.centralizer ({e} : Set G) := fun g h =>
    Subgroup.mem_centralizer_singleton_iff.mpr h
  have hzC : z ∈ Subgroup.centralizer ({e} : Set G) := hCe z hcomm.symm
  have hhaC : (ha : G) ∈ Subgroup.centralizer ({e} : Set G) := hCe _ hea'.symm
  have hhbC : (hb : G) ∈ Subgroup.centralizer ({e} : Set G) := hCe _ heb'.symm
  have hηaC : (ηa : G) ∈ Subgroup.centralizer ({e} : Set G) := by
    have : (ηa : G) = z⁻¹ * ((ha : G) * (ha : G)) := by rw [hA']; group
    rw [this]
    exact (Subgroup.centralizer ({e} : Set G)).mul_mem
      ((Subgroup.centralizer ({e} : Set G)).inv_mem hzC)
      ((Subgroup.centralizer ({e} : Set G)).mul_mem hhaC hhaC)
  have hηbC : (ηb : G) ∈ Subgroup.centralizer ({e} : Set G) := by
    have : (ηb : G) = z⁻¹ * ((hb : G) * (hb : G)) := by rw [hB']; group
    rw [this]
    exact (Subgroup.centralizer ({e} : Set G)).mul_mem
      ((Subgroup.centralizer ({e} : Set G)).inv_mem hzC)
      ((Subgroup.centralizer ({e} : Set G)).mul_mem hhbC hhbC)
  have hηcC : (ηc : G) ∈ Subgroup.centralizer ({e} : Set G) := by
    have : (ηc : G) = z⁻¹ * ((ha : G) * (hb : G) * (ha : G)⁻¹ * (hb : G)⁻¹) := by
      rw [hC']; group
    rw [this]
    exact (Subgroup.centralizer ({e} : Set G)).mul_mem
      ((Subgroup.centralizer ({e} : Set G)).inv_mem hzC)
      ((Subgroup.centralizer ({e} : Set G)).mul_mem
        ((Subgroup.centralizer ({e} : Set G)).mul_mem
          ((Subgroup.centralizer ({e} : Set G)).mul_mem hhaC hhbC)
          ((Subgroup.centralizer ({e} : Set G)).inv_mem hhaC))
        ((Subgroup.centralizer ({e} : Set G)).inv_mem hhbC))
  let xa : ↥(Subgroup.centralizer ({e} : Set G)) := ⟨(ha : G), hhaC⟩
  let xb : ↥(Subgroup.centralizer ({e} : Set G)) := ⟨(hb : G), hhbC⟩
  let xz : ↥(Subgroup.centralizer ({e} : Set G)) := ⟨z, hzC⟩
  let ya : ↥(Subgroup.centralizer ({e} : Set G)) := ⟨(ηa : G), hηaC⟩
  let yb : ↥(Subgroup.centralizer ({e} : Set G)) := ⟨(ηb : G), hηbC⟩
  let yc : ↥(Subgroup.centralizer ({e} : Set G)) := ⟨(ηc : G), hηcC⟩
  have hodd : ∀ y : G, y ∈ N → Odd (orderOf y) := fun y hy =>
    hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hy)
  have hζ : centAct eL hCN xz ≠ 1 := by
    intro h1
    obtain ⟨P, hP, hPz⟩ := exists_sylow_centralized_of_centAct_eq_one eL hCN xz hzz h1
    exact hno ⟨P, hP, hPz⟩
  have hζ2 : centAct eL hCN xz * centAct eL hCN xz = 1 := by
    rw [← map_mul, show xz * xz = 1 from Subtype.ext hzz, map_one]
  have hAζ : centAct eL hCN xa * centAct eL hCN xz = centAct eL hCN xz * centAct eL hCN xa := by
    rw [← map_mul, ← map_mul, show xa * xz = xz * xa from Subtype.ext hza'.symm]
  have hBζ : centAct eL hCN xb * centAct eL hCN xz = centAct eL hCN xz * centAct eL hCN xb := by
    rw [← map_mul, ← map_mul, show xb * xz = xz * xb from Subtype.ext hzb'.symm]
  have hAA : centAct eL hCN xa * centAct eL hCN xa =
      centAct eL hCN xz * centAct eL hCN ya := by
    rw [← map_mul, ← map_mul, show xa * xa = xz * ya from Subtype.ext hA']
  have hBB : centAct eL hCN xb * centAct eL hCN xb =
      centAct eL hCN xz * centAct eL hCN yb := by
    rw [← map_mul, ← map_mul, show xb * xb = xz * yb from Subtype.ext hB']
  have hcc : centAct eL hCN xa * centAct eL hCN xb * (centAct eL hCN xa)⁻¹ *
      (centAct eL hCN xb)⁻¹ = centAct eL hCN xz * centAct eL hCN yc := by
    have h := congrArg (centAct eL hCN) (Subtype.ext hC' :
      xa * xb * xa⁻¹ * xb⁻¹ = xz * yc)
    simpa only [map_mul, map_inv] using h
  exact aut_s4b hζ hζ2 hAζ hBζ hAA hBB hcc
    (odd_orderOf_centAct eL hCN ya (hodd _ hηaN)) (odd_orderOf_centAct eL hCN yb (hodd _ hηbN))
    (odd_orderOf_centAct eL hCN yc (hodd _ hηcN))

end Core

end CFSG.ClassicalInvolution.Q3.Q3AM
