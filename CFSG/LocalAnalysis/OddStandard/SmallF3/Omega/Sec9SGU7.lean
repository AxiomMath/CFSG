module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGEnd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGD3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Sec9T0_of (h36 : Asc82Lemma36) (hT6 : Asc82Tab6M) : Asc82Sec9T0 := by
  intro G _ _ t L S z g B hctx hs
  obtain ⟨s, hs2, hsC, α, hα⟩ := hs
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have hBL : B ≤ L := fun x hx => (hctx.B_le hx).1
  have hLcent : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hS
  have hP : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf hLcent hN hctx.sylow
  obtain ⟨B'', hB''L, hB''E, hB''c⟩ :=
    sec9u_exists_E16_commute hT6 hLM hBL hctx.B_e16 (hN s hsC) hα
  have hB''p : IsPGroup 2 B'' := IsPGroup.of_card (n := 4) hB''E.2
  obtain ⟨c, hcL, hc⟩ := exists_conj_le_of_isSylow2Of hP hB''p hB''L
  let B' : Subgroup G := B''.map (MulAut.conj c).toMonoidHom
  let t₀ : G := c * s * c⁻¹
  refine ⟨B', t₀, ?_⟩
  refine { toSec8Base := ?_, t0_inv := ?_, t0_cent := ?_, t0_type := ?_, t0_B := ?_ }
  · refine { toSec8Setting := hctx.toSec8Setting, tz := hctx.tz, B_le := ?_, B_e16 := ?_ }
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      have hmem : c * k * c⁻¹ ∈ S ⊓ L := hc k hk
      rw [inf_comm] at hmem
      exact hmem
    · have hcard : Nat.card B' = 2 ^ 4 :=
        (Subgroup.card_map_of_injective (MulAut.conj c).injective).trans hB''E.2
      have hcomm : ∀ x y : ↥B', x * y = y * x := by
        intro x y
        apply Subtype.ext
        obtain ⟨kx, hkx, hxv⟩ := Subgroup.mem_map.mp x.2
        obtain ⟨ky, hky, hyv⟩ := Subgroup.mem_map.mp y.2
        change (x : G) * (y : G) = (y : G) * (x : G)
        rw [← hxv, ← hyv, ← map_mul, ← map_mul]
        have hkk : (⟨kx, hkx⟩ : ↥B'') * ⟨ky, hky⟩ = ⟨ky, hky⟩ * ⟨kx, hkx⟩ := by
          haveI : IsMulCommutative ↥B'' := hB''E.1.1
          exact mul_comm' _ _
        have hkk' : kx * ky = ky * kx := by simpa using congrArg Subtype.val hkk
        rw [hkk']
      refine ⟨⟨isMulCommutative_iff.mpr hcomm, ?_⟩, hcard⟩
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hB''E.1.2 k hk, map_one]
  · change orderOf (c * s * c⁻¹) = 2
    have hconj : (MulAut.conj c) s = c * s * c⁻¹ := MulAut.conj_apply c s
    rw [← hconj]
    exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective s).trans hs2
  · exact mul_mem (mul_mem (hLcent hcL) hsC) (inv_mem (hLcent hcL))
  · exact sec9u_inducesTypeSome_conj (Subgroup.le_normalizer hcL) (r := 3)
      (by norm_num) (by norm_num) hα
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    change c * s * c⁻¹ * (c * k * c⁻¹) = c * k * c⁻¹ * (c * s * c⁻¹)
    calc c * s * c⁻¹ * (c * k * c⁻¹)
        = c * (s * k) * c⁻¹ := by group
      _ = c * (k * s) * c⁻¹ := by rw [hB''c k hk]
      _ = c * k * c⁻¹ * (c * s * c⁻¹) := by group

theorem aschOmega6Minus_of_tab6_t0 (hsh : Asc82Shapes) (h36 : Asc82Lemma36)
    (h37 : Asc82Lemma37) (h66 : Asc82Lemma66) (h68 : Asc82Lemma68) (h82 : Asc82Lemma82)
    (hZ : Asc82ZExists) (hM : Asc82Tab6M) (hN : Asc82NormA6) (hIrr : Asc82Sec9CosIrred)
    (h84 : Asc82Thm84) : AschOmega6Minus :=
  aschOmega6Minus_of_tab6 hsh h36 h37 h66 h68 h82 hZ hM hN ⟨asc82Sec9CosI1_of hM, hIrr⟩ h84
    (asc82Sec9T0_of h36 hM)

end CFSG.OddStandard.SmallF3.Omega
