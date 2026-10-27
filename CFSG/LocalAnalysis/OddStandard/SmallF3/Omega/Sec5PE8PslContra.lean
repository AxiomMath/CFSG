module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PEF8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PEF9
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5NT

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GH74.GLS.IVK

theorem sec5pe8_contra {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type} [Group K]
    (e : K ≃* L2 F) {κ : MulAut K} {y : MulAut K} (hy : y ∈ innDiagSub e) (hy2 : orderOf y = 2)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : MulAut K} (hx : x ∈ Subgroup.zpowers κ)
    (hxr : orderOf x = r) (hout : x ∉ innDiagSub e)
    (hfix : ∀ w : K, Nat.Coprime (orderOf w) 6 → y w = w → κ w = w) : False := by
  classical
  obtain ⟨q₁, hq₁odd, hq₁ge, hqcard, hCxdvd⟩ :=
    sec5pef_outer_prime_order hF e hr hr2 hxr hout
  obtain ⟨δ, hδ, hfixed⟩ := sec5pef_exists_fixed_of_prime_dvd hF e hy hy2
  obtain ⟨s, hs, hs5, hsdiv, hsnotdiv⟩ := sec5nt_exists_prime_dvd hq₁odd hq₁ge hr hr2 hδ
  have hsdivF : (s : ℤ) ∣ (Nat.card F : ℤ) - δ := by
    rw [hqcard, Nat.cast_pow]
    exact hsdiv
  have hs2 : s ≠ 2 := by omega
  obtain ⟨w, hword, hwy⟩ := hfixed s hs hs2 hsdivF
  have hw6 : Nat.Coprime (orderOf w) 6 := by
    rw [hword, Nat.Prime.coprime_iff_not_dvd hs]
    intro hdvd
    have hle : s ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hs56 : s = 5 ∨ s = 6 := by omega
    rcases hs56 with rfl | rfl
    · norm_num at hdvd
    · norm_num at hs
  have hκw : κ w = w := hfix w hw6 hwy
  have hxw : x w = w := by
    have hstab : Subgroup.zpowers κ ≤ MulAction.stabilizer (MulAut K) w := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hκw
    have hmem : x ∈ MulAction.stabilizer (MulAut K) w := hstab hx
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hmem
  have hwH : w ∈ x.toMonoidHom.eqLocus (MonoidHom.id K) := by
    change x w = w
    exact hxw
  have hs_card : s ∣ Nat.card ↥(x.toMonoidHom.eqLocus (MonoidHom.id K)) := by
    rw [← hword]
    exact Subgroup.orderOf_dvd_natCard _ hwH
  have hs_nat : s ∣ q₁ * (q₁ ^ 2 - 1) := hs_card.trans hCxdvd
  have hs_int : (s : ℤ) ∣ (q₁ : ℤ) * ((q₁ : ℤ) ^ 2 - 1) := by
    have h1 : (s : ℤ) ∣ ((q₁ * (q₁ ^ 2 - 1) : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hs_nat
    rwa [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow 2 q₁ (by omega)), Nat.cast_pow,
      Nat.cast_one] at h1
  exact hsnotdiv hs_int

end CFSG.OddStandard.SmallF3.Omega
