module

public import CFSG.Holt.H78.Sec4FinalC5

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

namespace FinConfig

section QxP

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_fixSet_of_commute {z y : G} (h : z * y = y * z) :
    y • fixSet Ω (Subgroup.zpowers z) = fixSet Ω (Subgroup.zpowers z) := by
  rw [← fixSet_zpowers_conj, show y * z * y⁻¹ = z by rw [← h, mul_inv_cancel_right]]

theorem mem_fixingSubgroup_of_commute (hS : Sec4Setting G Ω) (D : C.Splitting hS)
    {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) {g₀ : G} (hg₀ : g₀ * v * g₀⁻¹ = C.x)
    {q : G} (hq : q ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))))
    {z : G} (hz : z ∈ C.Z) (hz1 : z ≠ 1) (hqz : z * (g₀ * q * g₀⁻¹) = g₀ * q * g₀⁻¹ * z) :
    g₀ * q * g₀⁻¹ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := C.isNaturalSE_Dv C.i
  set q' := g₀ * q * g₀⁻¹ with hq'_def
  set γi := C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i
  have hqP : q ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
    Subgroup.map_subtype_le _ hq
  have hzΦ := C.fixSet_eq_of_mem_Z hS hz hz1
  have hq's : q' ∈ stabilizer G (fixSet Ω (Subgroup.zpowers v)) := by
    rw [mem_stabilizer_iff, ← hzΦ]
    exact smul_fixSet_of_commute hqz
  have hFx : fixSet Ω (Subgroup.zpowers C.x) = g₀ • fixSet Ω (Subgroup.zpowers v) := by
    rw [← hg₀, fixSet_zpowers_conj]
  have hq'odd : Odd (orderOf q') := by
    rw [← SemiconjBy.orderOf_eq g₀ (show g₀ * q = q' * g₀ by rw [hq'_def]; group)]
    exact FinalC.odd_orderOf_of_mem_oddCoreOf hq
  have hq'γ : q' • (C.γ : Ω) = C.γ := by
    rw [hq'_def, mul_smul, mul_smul,
      (mem_fixingSubgroup_iff G).mp hqP _ (C.inv_smul_γ_mem hS hg₀), smul_inv_smul]
  set o := C.piPhi hS ⟨q', hq's⟩
  have hoodd : Odd (orderOf o) := hq'odd.of_dvd_nat
    ((orderOf_map_dvd (C.piPhi hS) ⟨q', hq's⟩).trans (by rw [Subgroup.orderOf_mk]))
  have hoγ : o γi = γi := by
    rw [C.piPhi_coord]
    exact congrArg (fun p => C.Dv.coord p C.i) (Subtype.ext hq'γ)
  have hoN := C.piPhi_mem_normalizer hS ⟨q', hq's⟩
  have hcomm : ∀ r ∈ seRadical (C.Dv.M C.i) γi, o * r = r * o := by
    intro r hr
    obtain ⟨u, hu, hur⟩ := D.exists_piM_U r hr
    obtain ⟨z₀, hz₀, hz₀u⟩ := C.exists_mem_Z_mul_mem hS D hT hUT hxv hu
    have hz₀C := C.mem_centralizer_of_mem_Z hS hz₀
    have huC := C.U_le_centralizer hS D hu
    have hwC := mul_mem hz₀C huC
    have hwr : C.piM hS ⟨z₀ * u, hwC⟩ = r := by
      rw [show (⟨z₀ * u, hwC⟩ : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) :
        Set G)) = ⟨z₀, hz₀C⟩ * ⟨u, huC⟩ from rfl, map_mul,
        (C.piM_eq_one_iff hS _).mpr fun ω hω => C.smul_eq_of_mem_Z_of_mem_fixSet hS hz₀ hω,
        one_mul]
      exact hur
    have hws := centralizer_le_stabilizer (Ω := Ω) v hwC
    have hpiw : C.piPhi hS ⟨z₀ * u, hws⟩ = r := (C.piPhi_eq_piM hS ⟨_, hwC⟩).trans hwr
    have hw'P : g₀⁻¹ * (z₀ * u) * g₀ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
      (mem_fixingSubgroup_iff G).mpr fun ω hω => by
        have h1 : g₀ • ω ∈ fixSet Ω (Subgroup.zpowers C.x) := by
          rw [hFx]
          exact Set.smul_mem_smul_set hω
        rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hz₀u _ h1, inv_smul_smul]
    have he₀ : q * (g₀⁻¹ * (z₀ * u) * g₀) * q⁻¹ * (g₀⁻¹ * (z₀ * u) * g₀)⁻¹ ∈
        oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
      have h1 := FinalC.conj_mem_oddCoreOf_of_mem hw'P (inv_mem hq)
      rw [show q * (g₀⁻¹ * (z₀ * u) * g₀) * q⁻¹ * (g₀⁻¹ * (z₀ * u) * g₀)⁻¹ =
        q * ((g₀⁻¹ * (z₀ * u) * g₀) * q⁻¹ * (g₀⁻¹ * (z₀ * u) * g₀)⁻¹) by group]
      exact mul_mem hq h1
    have hes : q' * (z₀ * u) * q'⁻¹ * (z₀ * u)⁻¹ ∈
        stabilizer G (fixSet Ω (Subgroup.zpowers v)) :=
      mul_mem (mul_mem (mul_mem hq's hws) (inv_mem hq's)) (inv_mem hws)
    have heodd : Odd (orderOf (q' * (z₀ * u) * q'⁻¹ * (z₀ * u)⁻¹)) := by
      rw [← SemiconjBy.orderOf_eq g₀ (show g₀ * (q * (g₀⁻¹ * (z₀ * u) * g₀) * q⁻¹ *
        (g₀⁻¹ * (z₀ * u) * g₀)⁻¹) = q' * (z₀ * u) * q'⁻¹ * (z₀ * u)⁻¹ * g₀ by
          rw [hq'_def]; group)]
      exact FinalC.odd_orderOf_of_mem_oddCoreOf he₀
    have hψe : C.piPhi hS ⟨_, hes⟩ = o * r * o⁻¹ * r⁻¹ := by
      rw [show (⟨_, hes⟩ : stabilizer G (fixSet Ω (Subgroup.zpowers v))) =
        ⟨q', hq's⟩ * ⟨z₀ * u, hws⟩ * (⟨q', hq's⟩)⁻¹ * (⟨z₀ * u, hws⟩)⁻¹ from rfl, map_mul,
        map_mul, map_mul, map_inv, map_inv, hpiw]
    have heR : o * r * o⁻¹ * r⁻¹ ∈ seRadical (C.Dv.M C.i) γi :=
      mul_mem (conj_mem_seRadical hoN hoγ hr) (inv_mem hr)
    obtain ⟨k, hk⟩ := hM.isPGroup_seRadical γi ⟨_, heR⟩
    have hk' : (o * r * o⁻¹ * r⁻¹) ^ 2 ^ k = 1 := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one] using
        congrArg Subtype.val hk
    have hodd' : Odd (orderOf (o * r * o⁻¹ * r⁻¹)) := by
      rw [← hψe]
      exact heodd.of_dvd_nat ((orderOf_map_dvd (C.piPhi hS) _).trans
        (by rw [Subgroup.orderOf_mk]))
    have h1 := eq_one_of_odd_of_pow hodd' hk'
    calc o * r = o * r * o⁻¹ * r⁻¹ * (r * o) := by group
      _ = r * o := by rw [h1, one_mul]
  have hoZ := hM.mem_rootCenter_seRadical_of_commute hoN hcomm
  obtain ⟨k, hk⟩ :=
    hM.isPGroup_seRadical γi ⟨o, CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hoZ⟩
  have hk' : o ^ 2 ^ k = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one] using
      congrArg Subtype.val hk
  have ho1 : o = 1 := eq_one_of_odd_of_pow hoodd hk'
  exact (mem_fixingSubgroup_iff G).mpr ((C.piPhi_eq_one_iff hS _).mp ho1)

theorem conj_mem_fixingSubgroup_of_mem_oddCoreOf (hS : Sec4Setting G Ω) (D : C.Splitting hS)
    {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) {g₀ : G} (hg₀ : g₀ * v * g₀⁻¹ = C.x)
    {q : G} (hq : q ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))) :
    g₀ * q * g₀⁻¹ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))
  set Q := oddCoreOf P
  set Qx := Q.map (MulAut.conj g₀).toMonoidHom
  have hmemQx : ∀ {q : G}, q ∈ Q → g₀ * q * g₀⁻¹ ∈ Qx := fun {q} hq =>
    ⟨q, hq, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hnorm : ∀ {z : G}, z ∈ C.Z → ∀ {y : G}, y ∈ Qx → z * y * z⁻¹ ∈ Qx := by
    rintro z hz _ ⟨q, hq, rfl⟩
    have hz' := C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y hz))
    have h1 := FinalC.conj_mem_oddCoreOf_of_normalizes (conj_mem_fixingSubgroup_iff hz') hq
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  let : MulDistribMulAction C.Z Qx :=
    { smul := fun z y => ⟨(z : G) * y * (z : G)⁻¹, hnorm z.2 y.2⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : C.Z) : G) * y * ((1 : C.Z) : G)⁻¹ = y
        simp)
      mul_smul := fun a b y => Subtype.ext (by
        show ((a * b : C.Z) : G) * y * ((a * b : C.Z) : G)⁻¹ =
          (a : G) * ((b : G) * y * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul]
        group)
      smul_mul := fun a y₁ y₂ => Subtype.ext (by
        show (a : G) * ((y₁ : G) * y₂) * (a : G)⁻¹ =
          (a : G) * y₁ * (a : G)⁻¹ * ((a : G) * y₂ * (a : G)⁻¹)
        group)
      smul_one := fun a => Subtype.ext (by
        show (a : G) * 1 * (a : G)⁻¹ = 1
        group) }
  have : CFSG.IsElementaryAbelian 2 C.Z :=
    { is_comm := ⟨fun a b => Subtype.ext (C.commute_of_mem_Z hS a.2 (C.Z_le_Y b.2))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
        rw [Subgroup.coe_pow, sq, C.mul_self_eq_one_of_mem_Z hS g.2]
        rfl) }
  have hcard : 2 ^ 2 ≤ Nat.card C.Z := by
    obtain ⟨n, i, e, hA⟩ := (C.isNaturalSE_Dv C.i).exists_isBenderAction
    rw [← C.card_V_eq_card_Z hS D hT hUT hxv, C.card_V_eq hS D, hA.card_rootCenter_seRadical]
    exact hA.four_le_q
  have hodd : ¬ 2 ∣ Nat.card Qx := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective]
    have h1 := Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := P))
    rw [show Nat.card Q = Nat.card (CFSG.pPrimeCore 2 P) from
      Subgroup.card_map_of_injective P.subtype_injective]
    exact Nat.not_even_iff_odd.mpr h1 ∘ even_iff_two_dvd.mpr
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := C.Z) (H := Qx) hcard hodd
  have hle : ⨆ (a : C.Z) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) Qx ≤
      P.comap Qx.subtype := by
    refine iSup₂_le fun a ha y hy => ?_
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hy' : (a : G) * y * (a : G)⁻¹ = y := congrArg Subtype.val hy
    obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp y.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqe
    rw [← hqe] at hy'
    have hcomm : (a : G) * (g₀ * q * g₀⁻¹) = g₀ * q * g₀⁻¹ * a := by
      calc (a : G) * (g₀ * q * g₀⁻¹) = (a : G) * (g₀ * q * g₀⁻¹) * (a : G)⁻¹ * a := by group
        _ = g₀ * q * g₀⁻¹ * a := by rw [hy']
    have h1 := C.mem_fixingSubgroup_of_commute hS D hT hUT hxv hg₀ hq a.2
      (fun h => ha (Subtype.ext h)) hcomm
    show (y : G) ∈ P
    rw [← hqe]
    exact h1
  have h1 : (⟨g₀ * q * g₀⁻¹, hmemQx hq⟩ : Qx) ∈ P.comap Qx.subtype :=
    hle (hgen ▸ Subgroup.mem_top _)
  exact h1

end QxP

end FinConfig

end CFSG.Holt.H78
