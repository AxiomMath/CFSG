module

public import CFSG.LieType.SpecialLinear.NormalizerLift.Borel
public import CFSG.LieType.SpecialLinear.NormalizerLift.Lift
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCartanRank

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
  {H : Type*} [Group H] [Finite H]
  (π : SpecialLinearGroup (Fin n) F →* H)

theorem exists_conj_normalizes_unitriangular (hn : 3 ≤ n)
    (E : Subgroup H) (hE : E ≤ rangeNormalizer π) (hE2 : IsPGroup 2 E) :
    ∃ x : SpecialLinearGroup (Fin n) F, ∀ e ∈ E,
      (π x)⁻¹ * e * π x ∈
        Subgroup.normalizer ((unitriangular n F).map π : Set H) := by
  classical
  obtain ⟨P0, hP0⟩ := exists_sylow_unitriangular (K := F) 2 (n := n) (by omega)
  let P : Sylow 2 π.range := P0.mapSurjective π.rangeRestrict_surjective
  have hP : CFSG.ABGLocalTools.IsSylowOf 2 ((unitriangular n F).map π) π.range := by
    refine ⟨P, ?_⟩
    rw [Sylow.coe_mapSurjective, hP0, Subgroup.map_map,
      MonoidHom.subtype_comp_rangeRestrict π]
  let G : Subgroup H := E ⊔ π.range
  have hE_G : E ≤ G := le_sup_left
  have hK_G : π.range ≤ G := le_sup_right
  have hGnorm : G ≤ Subgroup.normalizer (π.range : Set H) := by
    refine sup_le hE ?_
    exact Subgroup.le_normalizer
  have hE2' : IsPGroup 2 (E.subgroupOf G) := hE2.comap_subtype
  obtain ⟨Q, hQ⟩ := hE2'.exists_le_sylow
  let S : Subgroup H := (Q : Subgroup G).map G.subtype
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 S G := ⟨Q, rfl⟩
  have hE_S : E ≤ S := by
    intro e he
    refine Subgroup.mem_map.mpr ⟨⟨e, hE_G he⟩, ?_, rfl⟩
    exact hQ (show (⟨e, hE_G he⟩ : G) ∈ E.subgroupOf G from he)
  have hS_G : S ≤ G := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  let Sinf : Subgroup H := S ⊓ π.range
  have hSinf : CFSG.ABGLocalTools.IsSylowOf 2 Sinf π.range :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (N := π.range) (K := G) hS hK_G hGnorm
  obtain ⟨k, hkK, hconj⟩ := hSinf.exists_mem_conj hP
  let S' : Subgroup H := S.map (MulAut.conj k)
  have hS'_inf : S' ⊓ π.range = (unitriangular n F).map π := by
    ext x
    constructor
    · rintro ⟨hxS', hxK⟩
      have hxS : k⁻¹ * x * k ∈ S := by
        change x ∈ S.map (MulAut.conj k) at hxS'
        rw [Subgroup.mem_map] at hxS'
        obtain ⟨y, hy, hyx⟩ := hxS'
        rw [← hyx]
        change k⁻¹ * (k * y * k⁻¹) * k ∈ S
        have hconj_eq : k⁻¹ * (k * y * k⁻¹) * k = y := by group
        rwa [hconj_eq]
      have hxK' : k⁻¹ * x * k ∈ π.range :=
        π.range.mul_mem (π.range.mul_mem (π.range.inv_mem hkK) hxK) hkK
      exact (hconj x).mpr ⟨hxS, hxK'⟩
    · intro hxU
      have hxSinf : k⁻¹ * x * k ∈ Sinf := (hconj x).mp hxU
      refine ⟨?_, ?_⟩
      · refine Subgroup.mem_map.mpr ⟨k⁻¹ * x * k, hxSinf.1, ?_⟩
        change k * (k⁻¹ * x * k) * k⁻¹ = x
        group
      · have hxK : k * (k⁻¹ * x * k) * k⁻¹ ∈ π.range :=
          π.range.mul_mem (π.range.mul_mem hkK hxSinf.2) (π.range.inv_mem hkK)
        rwa [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at hxK
  have hS'_G : S' ≤ G := by
    intro x hx
    change x ∈ S.map (MulAut.conj k) at hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hyx]
    change k * y * k⁻¹ ∈ G
    exact G.mul_mem (G.mul_mem (hK_G hkK) (hS_G hy)) (G.inv_mem (hK_G hkK))
  have hS'_normalizes_U : S' ≤
      Subgroup.normalizer ((unitriangular n F).map π : Set H) := by
    have hnormalπ : ((π.range).subgroupOf S').Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
      intro s hs
      exact Subgroup.inf_normalizer_le_normalizer_inf (H := π.range) (K := S')
        ⟨(hS'_G.trans hGnorm) hs, Subgroup.le_normalizer hs⟩
    have hU_le_S' : (unitriangular n F).map π ≤ S' := by
      rw [← hS'_inf]
      exact inf_le_left
    have hnormalU : ((unitriangular n F).map π).subgroupOf S' |>.Normal := by
      rw [show (unitriangular n F).map π = π.range ⊓ S' by rw [inf_comm, hS'_inf]]
      rw [Subgroup.inf_subgroupOf_right]
      exact hnormalπ
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hU_le_S').mp hnormalU
  obtain ⟨x0, hx0⟩ := MonoidHom.mem_range.mp hkK
  refine ⟨x0⁻¹, ?_⟩
  intro e he
  have hx : π x0⁻¹ = k⁻¹ := by rw [map_inv, hx0]
  rw [hx, inv_inv]
  refine hS'_normalizes_U ?_
  refine Subgroup.mem_map.mpr ⟨e, hE_S he, ?_⟩
  change k * e * k⁻¹ = k * e * k⁻¹
  rfl

omit [Finite H] in
theorem liftAut_mapsTo_unitriangular (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (e : rangeNormalizer π)
    (he : (e : H) ∈ Subgroup.normalizer ((unitriangular n F).map π : Set H)) :
    ∀ u ∈ unitriangular n F, liftAut π hker hn e u ∈ unitriangular n F := by
  classical
  obtain ⟨P0, hP0⟩ := exists_sylow_unitriangular (K := F) 2 (n := n) (by omega)
  have hU2 : IsPGroup 2 (unitriangular n F) := by
    rw [← hP0]
    exact P0.isPGroup'
  have hZodd : Odd (Nat.card (scalars n F)) :=
    (CFSG.ClassicalGroups.SpecialLinear.odd_card_sub_one_of_char_two (F := F)).of_dvd_nat
      (card_scalars_dvd (K := F) (n := n) (by omega))
  intro u hu
  let Φ := liftAut π hker hn e
  have hπΦ : π (Φ u) = (e : H) * π u * (e : H)⁻¹ :=
    liftAut_spec (π := π) hker hn e u
  have hmem : π (Φ u) ∈ (unitriangular n F).map π := by
    rw [hπΦ]
    exact (Subgroup.mem_normalizer_iff.mp he (π u)).mp (Subgroup.mem_map_of_mem π hu)
  obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.mp hmem
  let z := u'⁻¹ * Φ u
  have hzker : z ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [z]
    rw [map_mul, map_inv, hu'eq, inv_mul_cancel]
  have hzZ : z ∈ scalars n F := hker hzker
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) :=
    scalars_le_center n F hzZ
  have hΦeq : Φ u = u' * z := by
    dsimp [z]
    group
  obtain ⟨a, ha⟩ := hU2.exists_orderOf_eq_pow (⟨u', hu'⟩ : unitriangular n F)
  obtain ⟨b, hb⟩ := hU2.exists_orderOf_eq_pow (⟨u, hu⟩ : unitriangular n F)
  have ha' : orderOf u' = 2 ^ a := by
    rw [Subgroup.orderOf_coe (⟨u', hu'⟩ : unitriangular n F)]
    exact ha
  have hb' : orderOf u = 2 ^ b := by
    rw [Subgroup.orderOf_coe (⟨u, hu⟩ : unitriangular n F)]
    exact hb
  have hΦu : orderOf (Φ u) ∣ 2 ^ b := by
    rw [← hb']
    exact orderOf_map_dvd (Φ : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) u
  have hcomm : Commute u'⁻¹ (Φ u) := by
    rw [hΦeq]
    exact ((Commute.refl u').mul_right (Subgroup.mem_center_iff.mp hzc u')).inv_left
  have hz2 : orderOf z ∣ 2 ^ (a + b) := by
    have hdiv := hcomm.orderOf_mul_dvd_lcm
    rw [show u'⁻¹ * Φ u = z from rfl] at hdiv
    refine hdiv.trans (Nat.lcm_dvd ?_ ?_)
    · rw [orderOf_inv, ha']
      exact Nat.pow_dvd_pow 2 (by omega)
    · exact hΦu.trans (Nat.pow_dvd_pow 2 (by omega))
  have hzcard : orderOf z ∣ Nat.card (scalars n F) :=
    (scalars n F).orderOf_dvd_natCard hzZ
  have hz1 : z = 1 := by
    have hdvd : orderOf z ∣ Nat.gcd (2 ^ (a + b)) (Nat.card (scalars n F)) :=
      Nat.dvd_gcd hz2 hzcard
    rw [((hZodd.coprime_two_left).pow_left (a + b)).gcd_eq_one] at hdvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  rw [hΦeq, hz1, mul_one]
  exact hu'

end CFSG.LieType.SpecialLinear
