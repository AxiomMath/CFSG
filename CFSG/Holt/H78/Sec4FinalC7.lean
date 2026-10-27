module

public import CFSG.Holt.H78.Sec4FinalC6
public import CFSG.Holt.H78.Sec4SEMultiplier
public import CFSG.Holt.H78.Sec4Sz8Class

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

namespace FinConfig

section Final


variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit
  [Finite G] [Fintype Ω]
  [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem commutator_N : ⁅C.N, C.N⁆ = C.N := by
  rw [← Subgroup.map_subtype_commutator, (C.D.isPerfect_M C.i₀).commutator_eq_top,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

include C in
theorem false_of_splitting (hS : Sec4Setting G Ω) (D : C.Splitting hS) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxv := C.isConj_x hS D
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hxv
  obtain ⟨T, hUT, hT⟩ := exists_fusionIsSylowIn_ge (C.isPGroup_U_sup_Y hS D) (C.U_sup_Y_le hS D)
  obtain ⟨k, hk⟩ := C.exists_dIter_le hS D
  set P := fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))
  set Q := oddCoreOf P
  set Cv := Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)
  set Sab := stabilizer G ({α, β} : Set Ω)
  set X := Subgroup.centralizer ((Subgroup.zpowers C.x : Subgroup G) : Set G) ⊓
    (stabilizer G α ⊓ stabilizer G β)
  have hXS : X ≤ Sab := fun g hg => stabilizer_inf_le_stabilizer_pair α β (Subgroup.mem_inf.mp hg).2
  set Xs := X.subgroupOf Sab
  have hNX : C.N ≤ Xs.map C.psi := fun n hn => by
    obtain ⟨g, hg, hgx, hgn⟩ := C.exists_centralizer_x hS hn
    exact ⟨⟨g, stabilizer_inf_le_stabilizer_pair α β hg⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨mem_centralizer_zpowers hgx.symm, hg⟩), hgn⟩
  have hNk : C.N ≤ (FinalC.dIter k Xs).map C.psi := by
    rw [FinalC.map_dIter, ← FinalC.dIter_eq_of_commutator_eq C.commutator_N k]
    exact FinalC.dIter_mono k hNX
  obtain ⟨n', i', e', hA⟩ := C.isNaturalSE_N.exists_isBenderAction
  have := hA.isPretransitive
  have : Nontrivial (C.D.Ψc C.i₀) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := C.D.five_le_card C.i₀; omega)
  obtain ⟨c, hc⟩ := exists_ne C.bγ
  obtain ⟨n, hn⟩ := exists_smul_eq C.N C.bγ c
  obtain ⟨y', hy'k, hy'n⟩ := hNk n.2
  set y : G := (y' : G) with hy_def
  have hyX : y ∈ FinalC.dIter k X := by
    have h1 : (FinalC.dIter k Xs).map Sab.subtype = FinalC.dIter k X := by
      rw [FinalC.map_dIter, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXS]
    rw [← h1]
    exact ⟨y', hy'k, rfl⟩
  have hyst : y ∈ stabilizer G α ⊓ stabilizer G β :=
    (Subgroup.mem_inf.mp (FinalC.dIter_le k X hyX)).2
  have hX'C : X.map (MulAut.conj g₀⁻¹).toMonoidHom ≤ Cv := by
    rintro _ ⟨g, hg, rfl⟩
    have hgx : C.x * g = g * C.x := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).1
      C.x (Subgroup.mem_zpowers _)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      C.conj_mem_centralizer_v hg₀ hgx
  have hy'C : g₀⁻¹ * y * g₀ ∈ FinalC.dIter k Cv := by
    have h1 : g₀⁻¹ * y * g₀ ∈ (FinalC.dIter k X).map (MulAut.conj g₀⁻¹).toMonoidHom :=
      ⟨y, hyX, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    rw [FinalC.map_dIter] at h1
    exact FinalC.dIter_mono k hX'C h1
  obtain ⟨c₁, hc₁, hq₁⟩ := hk _ hy'C
  have hM := C.isNaturalSE_Dv C.i
  obtain ⟨δ, hδΦ, hδγ⟩ := C.exists_mem_B_ne_γ hS
  have hcoord_ne : ∀ {ω ω' : fixSet Ω (Subgroup.zpowers v)}, (ω : Ω) ≠ ω' →
      C.Dv.coord ω C.i ≠ C.Dv.coord ω' C.i := fun {ω ω'} hne h => hne (by
    have h1 := (C.smul_eq_iff_piM_apply hS 1 ω ω').mpr (by rw [map_one]; exact h)
    rwa [OneMemClass.coe_one, one_smul] at h1)
  obtain ⟨m, hm, hmα⟩ := hM.exists_mem_seRadical_apply_eq (b := C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i)
    (hcoord_ne (ω := C.a) (ω' := ⟨C.γ, C.γ_mem⟩) C.α_ne_γ)
    (hcoord_ne (ω := ⟨δ, hδΦ⟩) (ω' := ⟨C.γ, C.γ_mem⟩) fun h => hδγ (Subtype.ext h))
  obtain ⟨u, hu, hum⟩ := D.exists_piM_U m hm
  obtain ⟨z₀, hz₀, hwP⟩ := C.exists_mem_Z_mul_mem hS D hT hUT hxv hu
  have huα : u • α = δ :=
    (C.smul_eq_iff_piM_apply hS ⟨u, C.U_le_centralizer hS D hu⟩ C.a ⟨δ, hδΦ⟩).mpr
      (by rw [hum]; exact hmα)
  have hwα : (z₀ * u) • α = δ := by
    rw [mul_smul, huα, C.smul_eq_of_mem_Z_of_mem_fixSet hS hz₀ hδΦ]
  have hdP : g₀⁻¹ * (z₀ * u) * g₀ ∈ P := (mem_fixingSubgroup_iff G).mpr fun ω hω => by
    have h1 : g₀ • ω ∈ fixSet Ω (Subgroup.zpowers C.x) := by
      rw [← hg₀, fixSet_zpowers_conj]
      exact Set.smul_mem_smul_set hω
    rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hwP _ h1, inv_smul_smul]
  set y₀ := g₀⁻¹ * y * g₀ with hy₀_def
  set d := g₀⁻¹ * (z₀ * u) * g₀ with hd_def
  have hc₁Y := D.Mc_le hc₁
  have hcomm : y₀ * d * y₀⁻¹ * d⁻¹ ∈ Q := by
    have h1 := C.commutator_mem_oddCoreOf hS D hc₁ hdP
    have h2 : c₁⁻¹ * y₀ * d * (c₁⁻¹ * y₀)⁻¹ * d⁻¹ ∈ Q := by
      have h3 := FinalC.conj_mem_oddCoreOf_of_mem hdP (inv_mem hq₁)
      rw [show c₁⁻¹ * y₀ * d * (c₁⁻¹ * y₀)⁻¹ * d⁻¹ =
        (c₁⁻¹ * y₀) * (d * (c₁⁻¹ * y₀)⁻¹ * d⁻¹) by group]
      exact mul_mem hq₁ h3
    have h4 := FinalC.conj_mem_oddCoreOf_of_normalizes
      (conj_mem_fixingSubgroup_iff (C.centralizer_Y_le hS hc₁Y)) h2
    rw [show y₀ * d * y₀⁻¹ * d⁻¹ = c₁ * (c₁⁻¹ * y₀ * d * (c₁⁻¹ * y₀)⁻¹ * d⁻¹) * c₁⁻¹ *
      (c₁ * d * c₁⁻¹ * d⁻¹) by group]
    exact mul_mem h4 h1
  have hP' : y * (z₀ * u) * y⁻¹ * (z₀ * u)⁻¹ ∈ P := by
    have h1 := C.conj_mem_fixingSubgroup_of_mem_oddCoreOf hS D hT hUT hxv hg₀ hcomm
    rwa [show g₀ * (y₀ * d * y₀⁻¹ * d⁻¹) * g₀⁻¹ = y * (z₀ * u) * y⁻¹ * (z₀ * u)⁻¹ by
      rw [hy₀_def, hd_def]; group] at h1
  have hyα : y • α = α := (Subgroup.mem_inf.mp hyst).1
  have hyδ : y • (δ : Ω) = δ := by
    calc y • (δ : Ω) = y • (z₀ * u) • α := by rw [hwα]
      _ = ((y * (z₀ * u) * y⁻¹ * (z₀ * u)⁻¹) * ((z₀ * u) * y)) • α := by
          rw [smul_smul]
          congr 1
          group
      _ = (y * (z₀ * u) * y⁻¹ * (z₀ * u)⁻¹) • (z₀ * u) • y • α := by
          rw [mul_smul _ ((z₀ * u) * y), mul_smul (z₀ * u) y]
      _ = (y * (z₀ * u) * y⁻¹ * (z₀ * u)⁻¹) • (δ : Ω) := by rw [hyα, hwα]
      _ = δ := (mem_fixingSubgroup_iff G).mp hP' _ hδΦ
  have h1 := C.psi_coord y' δ
  rw [show twoPointHom G Ω α β y' δ = δ from Subtype.ext hyδ, (C.coord_eq_bγ_iff δ).mpr hδΦ,
    hy'n] at h1
  exact hc (hn.symm.trans h1)

include C in
theorem false_of_seTwoCoverConj (hS : Sec4Setting G Ω) (hcov : SETwoCoverConj) : False := by
  obtain ⟨D⟩ := FinConfig.Splitting.nonempty C hS (C.exists_splitting_x_mem hS hcov)
  exact C.false_of_splitting hS D

include C in
theorem false (hS : Sec4Setting G Ω) : False :=
  C.false_of_seTwoCoverConj hS (seTwoCoverConj_of_szEight szEightTwoCoverConj)

end Final

end FinConfig

end CFSG.Holt.H78
