module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TSwap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TPk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TCent

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step105T_of (hC : Asc82Step105C) (h36 : Asc82Lemma36) (h102 : Asc82Lemma102)
    (hK0 : Asc82Lemma10K0) (hb : Asc82Basic10) (hP5 : Asc82FactPockets5)
    (hC5 : Asc82FactCentZ5) (hCK : Asc82FactCentK5) : Asc82Step105T := by
  intro G _ _ t L S z K1 K2 hctx hneg h hh hs
  set s : G := h⁻¹ * t * h with hsdef
  have ht2 : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [hctx.involution, pow_two] at hpow
    exact hpow
  have ht1 : t ≠ 1 := by
    intro h1
    have h2 : orderOf (1 : G) = 2 := h1 ▸ hctx.involution
    rw [orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hs2 : s * s = 1 := by
    rw [hsdef]
    rw [show (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h by group, ht2]
    group
  have hst : h * s * h⁻¹ = t := by rw [hsdef]; group
  have hhz : Commute h z := Subgroup.mem_centralizer_singleton_iff.mp hh
  have hhz' : h * z * h⁻¹ = z := by rw [hhz.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hsz : s * z = z * s := hctx.central s hs
  obtain ⟨hpsp, -, htnotL, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have key : ∀ k : G, k⁻¹ * s * k = s * z →
      (h * k * h⁻¹)⁻¹ * t * (h * k * h⁻¹) = t * z := by
    intro k hk
    have hk' : k⁻¹ * (h⁻¹ * t * h) * k = (h⁻¹ * t * h) * z := by
      rw [← hsdef]; exact hk
    calc (h * k * h⁻¹)⁻¹ * t * (h * k * h⁻¹)
        = h * (k⁻¹ * (h⁻¹ * t * h) * k) * h⁻¹ := by group
      _ = h * ((h⁻¹ * t * h) * z) * h⁻¹ := by rw [hk']
      _ = (h * (h⁻¹ * t * h) * h⁻¹) * (h * z * h⁻¹) := by group
      _ = t * z := by rw [show h * (h⁻¹ * t * h) * h⁻¹ = t by group, hhz']
  rcases sec10T_pocket_dichotomy hP5 hb hctx hs with ⟨hn1, hn2⟩ | ⟨hsw1, hsw2⟩
  · have hK1 := (sec10KS_equiv hP5 hC5 hpsp hctx).1
    have hK2 := (sec10KS_equiv hP5 hC5 hpsp hctx).2
    rcases sec10T_sl23_involution hK1 hctx.pocket1.1 hz2 hs2 hsz hn1 with h1 | hk1
    · rcases sec10T_sl23_involution hK2 hctx.pocket2.1 hz2 hs2 hsz hn2 with h2 | hk2
      · rcases sec10T_cent_case h102 hb hCK hctx hs hs2 h1 h2 with hgt | hgt | hgt | hgt
        · exfalso
          apply ht1
          rw [← hst, hgt, mul_one, mul_inv_cancel]
        · exfalso
          apply htnotL
          rw [← hst, hgt, hhz']
          exact hzL
        · exact hgt
        · exfalso
          exact hneg ⟨h, by rw [← hsdef]; exact hgt⟩
      · exfalso
        obtain ⟨k, -, hk⟩ := hk2
        exact hneg ⟨h * k * h⁻¹, key k hk⟩
    · exfalso
      obtain ⟨k, -, hk⟩ := hk1
      exact hneg ⟨h * k * h⁻¹, key k hk⟩
  · exfalso
    exact sec10T_swap_false hC hK0 h36 hP5 hC5 hb hctx hneg hh
      (by rw [← hsdef]; exact hs)
      (by intro x hx; rw [← hsdef]; exact hsw1 x hx)

end CFSG.OddStandard.SmallF3.Omega
