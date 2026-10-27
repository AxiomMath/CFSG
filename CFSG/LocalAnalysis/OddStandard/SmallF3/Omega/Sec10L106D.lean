module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L106B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L106Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma sec10L106D_conj_mul (x o k0 : G) (h : x * k0 = k0 * x) :
    x * (o * k0) * x⁻¹ = (x * o * x⁻¹) * k0 := by
  have h' : k0 * x⁻¹ = x⁻¹ * k0 := by
    calc k0 * x⁻¹ = x⁻¹ * (x * k0) * x⁻¹ := by group
      _ = x⁻¹ * (k0 * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * k0 := by group
  calc x * (o * k0) * x⁻¹ = x * o * (k0 * x⁻¹) := by group
    _ = x * o * (x⁻¹ * k0) := by rw [h']
    _ = (x * o * x⁻¹) * k0 := by group

private lemma sec10L106D_commutator (x o k0 : G) (h : x * k0 = k0 * x) :
    x * (o * k0) * x⁻¹ * (o * k0)⁻¹ = (x * o * x⁻¹) * o⁻¹ := by
  rw [sec10L106D_conj_mul x o k0 h, mul_inv_rev]
  group

theorem sec10L106_comm [Finite G] (h36 : Asc82Lemma36) (hK0 : Asc82Lemma10K0)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {g : G}
    (hg : g⁻¹ * t * g = t * z) (hgz : g⁻¹ * z * g = z) {x : G}
    (hxL : x ∈ centralizer (L : Set G))
    (hxN : x ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G)) :
    ∀ k ∈ CFSG.conjugate K1 g ⊔ CFSG.conjugate K2 g, x * k = k * x := by
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hq : IsQuasisimple ↥L := hctx.component.isQuasisimple
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2, pow_two] at h
    exact h
  have hK1L : K1 ≤ L := hctx.pocket1.2.1.trans inf_le_left
  have hK2L : K2 ≤ L := hctx.pocket2.2.1.trans inf_le_left
  have hKleL : K1 ⊔ K2 ≤ L := sup_le hK1L hK2L
  have hKleC : K1 ⊔ K2 ≤ centralizer ({t} : Set G) :=
    sup_le (hK1L.trans hLt) (hK2L.trans hLt)
  have hLE : K1 ⊔ K2 ≤ Subgroup.normalizer
      (oddCoreIn (centralizer ({t} : Set G)) : Set G) :=
    hKleC.trans (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)
  have hK0eq : secK0 t z = oddCoreIn (centralizer ({t} : Set G)) ⊔ (K1 ⊔ K2) := by
    rw [(hK0 G t L S z K1 K2 hctx).1, sup_assoc]
  have hKle : K1 ⊔ K2 ≤ secK0 t z := by
    rw [hK0eq]
    exact le_sup_right
  intro k hk
  have hkmap : k ∈ (K1 ⊔ K2).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.map_sup]
    simpa only [CFSG.conjugate] using hk
  obtain ⟨m, hmK, hkm⟩ := hkmap
  have hkm' : g⁻¹ * m * g = k := by simpa [MulAut.conj_apply] using hkm
  have hmsec : m ∈ secK0 t z := hKle hmK
  have hksec : k ∈ secK0 t z := by
    rw [← hkm']
    exact (sec10K0_conj_mem hzsq hg hgz hmsec).1
  have hksec' : k ∈ oddCoreIn (centralizer ({t} : Set G)) ⊔ (K1 ⊔ K2) := by
    rw [← hK0eq]
    exact hksec
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left _ (K1 ⊔ K2) hLE
  change k ∈ (↑(oddCoreIn (centralizer ({t} : Set G)) ⊔ (K1 ⊔ K2)) : Set G) at hksec'
  rw [hcoe, Set.mem_mul] at hksec'
  obtain ⟨o, hoO, k0, hk0K, hok⟩ := hksec'
  have hcomm0 : x * k0 = k0 * x :=
    (Subgroup.mem_centralizer_iff.mp hxL k0 (hKleL hk0K)).symm
  have hgoO : g * o * g⁻¹ ∈ oddCoreIn (centralizer ({t} : Set G)) :=
    sec10K0_conj_oddCore hK0 hP5 hC5 hpsp hctx hg hgz hoO
  have hgoC : g * o * g⁻¹ ∈ centralizer (L : Set G) :=
    sec10K0_oddCore_le_centralizer hpsp hzL hz2 hLt hN hgoO
  have hoCL' : o ∈ centralizer (CFSG.conjugate L g : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l' hl'
    have hl : g * l' * g⁻¹ ∈ L := (mem_conjugate_iff').mp hl'
    have hcomm : (g * l' * g⁻¹) * (g * o * g⁻¹) = (g * o * g⁻¹) * (g * l' * g⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hgoC _ hl
    calc l' * o = g⁻¹ * ((g * l' * g⁻¹) * (g * o * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * o * g⁻¹) * (g * l' * g⁻¹)) * g := by rw [hcomm]
      _ = o * l' := by group
  have hxoCL' : x * o * x⁻¹ ∈ centralizer (CFSG.conjugate L g : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l' hl'
    have hxl' : x⁻¹ * l' * x ∈ CFSG.conjugate L g := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) l').mp hl'
      simpa using this
    have hcomm : (x⁻¹ * l' * x) * o = o * (x⁻¹ * l' * x) :=
      Subgroup.mem_centralizer_iff.mp hoCL' _ hxl'
    calc l' * (x * o * x⁻¹) = x * ((x⁻¹ * l' * x) * o) * x⁻¹ := by group
      _ = x * (o * (x⁻¹ * l' * x)) * x⁻¹ := by rw [hcomm]
      _ = (x * o * x⁻¹) * l' := by group
  have hK1L' : CFSG.conjugate K1 g ≤ CFSG.conjugate L g := by
    simpa only [CFSG.conjugate] using
      Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hK1L
  have hK2L' : CFSG.conjugate K2 g ≤ CFSG.conjugate L g := by
    simpa only [CFSG.conjugate] using
      Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hK2L
  have hkL' : k ∈ CFSG.conjugate L g := (sup_le hK1L' hK2L') hk
  have hwL' : x * k * x⁻¹ * k⁻¹ ∈ CFSG.conjugate L g :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hxN k).mp hkL')
      (Subgroup.inv_mem _ hkL')
  have hwC : x * k * x⁻¹ * k⁻¹ ∈ centralizer (CFSG.conjugate L g : Set G) := by
    have hwo : x * (o * k0) * x⁻¹ * (o * k0)⁻¹ = (x * o * x⁻¹) * o⁻¹ :=
      sec10L106D_commutator x o k0 hcomm0
    rw [← hok, hwo]
    exact Subgroup.mul_mem _ hxoCL' (Subgroup.inv_mem _ hoCL')
  have hw1 : x * k * x⁻¹ * k⁻¹ = 1 := by
    have hinf : CFSG.conjugate L g ⊓ centralizer (CFSG.conjugate L g : Set G) = ⊥ :=
      inf_centralizer_eq_bot_of_psp43 (isQuasisimple_conjugate hq g) (isPSp43_conjugate hpsp g)
    have hwbot : x * k * x⁻¹ * k⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hinf]
      exact ⟨hwL', hwC⟩
    simpa using hwbot
  have hxkx : x * k * x⁻¹ = k := mul_inv_eq_one.mp hw1
  calc x * k = (x * k * x⁻¹) * x := by group
    _ = k * x := by rw [hxkx]

end CFSG.OddStandard.SmallF3.Omega