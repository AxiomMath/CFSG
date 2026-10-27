module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Parts
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Z
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011B9bCount
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011B9bCover
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011B9bPropS
public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Main

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.ABGLocalTools
open CFSG.GH74.GLS.Stage2.Final.Thm6.I414 (HasPropS IsSectionOf)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 (F20_le_OddCore)
open CFSG.GH74.GLS.Stage2.Local.P34 (GHSchreier)

theorem coprime20b (hSch : GHSchreier) : Coprime20b := by
  intro G _ _ z k S hC g hA hs r hr hrF
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hctx : Stage2Ctx G z k S := hC.1.ctx.ctx17.ctx
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hM : IsCoatom (Cen z) := hC.1.ctx.ctx17.mem.1
  have hGs : IsSimpleGroup G := hctx.std.kps.1
  obtain ⟨Z, hZr, hZne, hZF, hZcF, hZC, hZnorm⟩ := exists_Z20 z hr hrF hz2 hM hGs
  have hJH : J0 z g ≤ H0 z g := J0_le_H0 z g
  have hJn : ∀ h ∈ H0 z g, ∀ j ∈ J0 z g, h * j * h⁻¹ ∈ J0 z g := fun h hh j hj => J0_conj_mem z g hh hj
  have hZH : Z ≤ H0 z g := by
    intro w hw
    have hc : w ∈ Subgroup.centralizer ((F0 z g : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact hZcF f ((show F0 z g ≤ F20 z from inf_le_left) hf) w hw
    exact Subgroup.centralizer_le_normalizer ((F0 z g : Subgroup G) : Set G) hc
  have hzJ : z ∈ J0 z g := hs.z_mem
  have hZN : ∀ w ∈ Z, ∀ n ∈ pPrimeCoreOf 2 (J0 z g), w * n * w⁻¹ ∈ pPrimeCoreOf 2 (J0 z g) :=
    fun w hw n hn => conj_mem_pPrimeCoreOf_of_normal hJn (hZH hw) hn
  have hzNn : ∀ n ∈ pPrimeCoreOf 2 (J0 z g), z * n * z⁻¹ ∈ pPrimeCoreOf 2 (J0 z g) :=
    fun n hn => pPrimeCoreOf_conj_mem hzJ hn
  have hNZ_le_C : ∀ x ∈ normalizer (Z : Set G), x ∈ Cen z := hZnorm
  have hC_le_NZ : ∀ c ∈ Cen z, c ∈ normalizer (Z : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hZC c hc x hx, fun hx => ?_⟩
    have h3 := hZC c⁻¹ ((Cen z).inv_mem hc) _ hx
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rwa [e] at h3
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hfix : ∀ n ∈ pPrimeCoreOf 2 (J0 z g),
      (∀ w ∈ Z, n⁻¹ * w * n ∈ normalizer (Z : Set G)) → n ∈ normalizer (Z : Set G) := by
    intro n hn hw
    have hz'w : ∀ w ∈ Z, w * (n * z * n⁻¹) = (n * z * n⁻¹) * w := by
      intro w hw'
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hNZ_le_C _ (hw w hw'))
      calc w * (n * z * n⁻¹) = n * ((n⁻¹ * w * n) * z) * n⁻¹ := by group
        _ = n * (z * (n⁻¹ * w * n)) * n⁻¹ := by rw [h1]
        _ = (n * z * n⁻¹) * w := by group
    have hz'N : n * z * n⁻¹ ∈ normalizer (Z : Set G) := by
      have hc : n * z * n⁻¹ ∈ Subgroup.centralizer (Z : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        exact hz'w
      exact Subgroup.centralizer_le_normalizer (Z : Set G) hc
    have hz'C := Subgroup.mem_centralizer_singleton_iff.mp (hNZ_le_C _ hz'N)
    have hu : z * (n * z * n⁻¹) ∈ pPrimeCoreOf 2 (J0 z g) := by
      have e : z * (n * z * n⁻¹) = (z * n * z⁻¹) * n⁻¹ := by
        have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
        rw [hzi]; group
      rw [e]
      exact mul_mem (hzNn n hn) (inv_mem hn)
    have hsq : (z * (n * z * n⁻¹)) * (z * (n * z * n⁻¹)) = 1 := by
      have hc : z * (n * z * n⁻¹) = (n * z * n⁻¹) * z := hz'C.symm
      calc (z * (n * z * n⁻¹)) * (z * (n * z * n⁻¹))
          = z * ((n * z * n⁻¹) * z) * (n * z * n⁻¹) := by group
        _ = z * (z * (n * z * n⁻¹)) * (n * z * n⁻¹) := by rw [← hc]
        _ = (z * z) * (n * (z * z) * n⁻¹) := by group
        _ = 1 := by rw [hzz]; group
    have hodd := L20.odd_orderOf_of_mem_pPrimeCoreOf hu
    have hdvd : orderOf (z * (n * z * n⁻¹)) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have hord : orderOf (z * (n * z * n⁻¹)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    have h1 : z * (n * z * n⁻¹) = 1 := orderOf_eq_one_iff.1 hord
    have hnz : n * z * n⁻¹ = z := by
      have : z⁻¹ = n * z * n⁻¹ := inv_eq_of_mul_eq_one_right h1
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
      rw [← this, hzi]
    have hnC : n ∈ Cen z := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : n * z = z * n := by
        have := congrArg (· * n) hnz
        simpa [mul_assoc] using this
      exact this
    exact hC_le_NZ n hnC
  have hcount := not_dvd_index_of_fixed (pPrimeCoreOf 2 (J0 z g)) Z hZr hZN hfix
  have hidx : ¬ r ∣ ((normalizer (Z : Set G) ⊓ pPrimeCoreOf 2 (J0 z g)).subgroupOf
      (pPrimeCoreOf 2 (J0 z g))).index := by
    have : (normalizer (Z : Set G) ⊓ pPrimeCoreOf 2 (J0 z g)).subgroupOf (pPrimeCoreOf 2 (J0 z g)) =
        (normalizer (Z : Set G)).subgroupOf (pPrimeCoreOf 2 (J0 z g)) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    rwa [this]
  obtain ⟨V, hVsyl, hVle⟩ := exists_sylow_of_not_dvd (pPrimeCoreOf 2 (J0 z g)) _ inf_le_right hidx
  have hzV : ∀ v ∈ V, z * v = v * z := fun v hv =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hNZ_le_C v (hVle hv).1)).symm
  have hVJ : V ≤ J0 z g := hVsyl.le.trans (Subgroup.map_subtype_le _)
  let K : Subgroup ↥(H0 z g) := (J0 z g).subgroupOf (H0 z g)
  have hzH : z ∈ H0 z g := hJH hzJ
  let e : ↥K ≃* ↥(J0 z g) := Subgroup.subgroupOfEquivOfLe hJH
  have hsimpleK : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K) := by
    have hsJ : IsSimpleGroup (↥(J0 z g) ⧸ pPrimeCore 2 ↥(J0 z g)) := hs.simple
    let q : (↥K ⧸ pPrimeCore 2 ↥K) ≃* (↥(J0 z g) ⧸ pPrimeCore 2 ↥(J0 z g)) :=
      QuotientGroup.congr _ _ e (CFSG.pPrimeCore_map_iso 2 e)
    exact q.isSimpleGroup
  have hzK : (⟨z, hzH⟩ : ↥(H0 z g)) ∈ K := hzJ
  have hz2' : orderOf (⟨z, hzH⟩ : ↥(H0 z g)) = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  let VH : Subgroup ↥(H0 z g) := V.subgroupOf (H0 z g)
  have hVH : IsSylowOf r VH (pPrimeCoreOf 2 K) := by
    refine (isSylowOf_map_subtype_iff (H0 z g)).mp ?_
    rw [Subgroup.map_subgroupOf_eq_of_le (hVJ.trans hJH), pPrimeCoreOf_subgroupOf_map hJH]
    exact hVsyl
  have hzVH : ∀ v ∈ VH, (⟨z, hzH⟩ : ↥(H0 z g)) * v = v * ⟨z, hzH⟩ := fun v hv =>
    Subtype.ext (hzV v hv)
  have hcov := cover_of_simple_quotient K hsimpleK hVH hzK hz2' hzVH
  have hHtop : H0 z g ≠ ⊤ := by
    intro htop
    have hFn : (F0 z g).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (F0 z g) with h | h
    · exact hA.inter h
    · have hzF : z ∈ F20 z ⊓ Ag z g := by
        have : z ∈ F0 z g := by rw [h]; trivial
        exact this
      exact absurd (hz2 ▸ L20.odd_orderOf_of_mem_pPrimeCoreOf (F20_le_OddCore z hzF.1)) (by decide)
  have hPropSH : HasPropS ↥(H0 z g) := hasPropS_of_kgh hctx.std.kgh hSch hHtop
  have hPropS : HasPropS ↥(pPrimeCore 2 ↥K) :=
    HasPropS.of_isSectionOf (I414.IsSectionOf.trans (I414.IsSectionOf.subgroup (pPrimeCore 2 ↥K))
      (I414.IsSectionOf.subgroup K)) hPropSH
  have key := I414.ig_4_14_cover 2 hs.comp hPropS hVH hcov
  rwa [card_commutator_pPrimeCoreOf_subgroupOf hJH] at key

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
