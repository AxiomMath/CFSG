module

public import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.Timmesfeld.Orders.BangField
import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LinearAlgebra.PrimeOrderFixedPoints

public section

namespace CFSG.LieType.Universal.Unitary

open CFSG.LieType.BorelTits CFSG.Timmesfeld CFSG.Open

private lemma three_pair_ne_of_two_le {f : ℕ} (hf : 2 ≤ f) : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
  intro h
  have h2 : 2 ^ f = 2 ^ 1 := congrArg Prod.snd h
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

private lemma card_center_SU_three_of_card {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    Nat.card (Subgroup.center (SU (unitaryInvolution F 2 f) 3)) =
      Nat.gcd 3 (2 ^ f + 1) := by
  have hpair := three_pair_ne_of_two_le hf
  have hcenterStated : Nat.card (Subgroup.center (StatedSU 3 (2 ^ f) F)) =
      Nat.gcd 3 (2 ^ f + 1) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [(isQuasisimple_statedSU_of_card (p := 2) (f := f) hF (n := 3) le_rfl hpair).2]
    exact (CFSG.LinearGroups.unitary_scalar_kernel (p := 2) (f := f) Nat.prime_two hF
      (n := 3) (by norm_num)).2.2
  rw [← hcenterStated, ← Subgroup.map_center_eq (equivStatedSU (p := 2) (f := f) hF 3),
    Subgroup.card_map_of_injective (equivStatedSU (p := 2) (f := f) hF 3).injective]

private lemma exists_primitivePrimeDivisor_dvd_card_SU_three {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    ∃ r : ℕ, IsPrimitivePrimeDivisor r (6 * f) ∧
      r ∣ Nat.card (SU (unitaryInvolution F 2 f) 3) := by
  obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * f)
    (by omega) (by omega)
  have hk0 : 0 < 6 * f := by omega
  have h1 : 6 * f ∣ 2 * (3 * f) := by
    rw [show 2 * (3 * f) = 6 * f by ring]
  have h2 : ¬ 6 * f ∣ 3 * f := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < 3 * f) h
    omega
  have h3 : 2 ^ (3 * f) = (2 ^ f) ^ 3 := by
    rw [show 3 * f = f * 3 by omega, pow_mul]
  have hrdvd : r ∣ (2 ^ f) ^ 3 + 1 := by
    have h := (hr.dvd_add_one_iff hk0 (3 * f)).mpr ⟨h1, h2⟩
    rwa [h3] at h
  have hcardG : Nat.card (SU (unitaryInvolution F 2 f) 3) =
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.Steinberg.card_SU_three (p := 2) (f := f) hF
  refine ⟨r, hr, ?_⟩
  rw [hcardG]
  exact dvd_mul_of_dvd_right hrdvd _

private lemma exists_order_prime_not_mem_center {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    ∃ (r : ℕ) (g : SU (unitaryInvolution F 2 f) 3), IsPrimitivePrimeDivisor r (6 * f) ∧
      orderOf g = r ∧ g ∉ Subgroup.center (SU (unitaryInvolution F 2 f) 3) := by
  obtain ⟨r, hr, hrdvd⟩ := exists_primitivePrimeDivisor_dvd_card_SU_three hF hf
  have hr3 : 3 < r := hr.three_lt_of_two_lt (by omega)
  haveI : Fact r.Prime := ⟨hr.prime⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  refine ⟨r, g, hr, hg, ?_⟩
  intro hgcen
  have hdvd : r ∣ Nat.card (Subgroup.center (SU (unitaryInvolution F 2 f) 3)) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center (SU (unitaryInvolution F 2 f) 3))
      hgcen
    rwa [hg] at this
  rw [card_center_SU_three_of_card hF hf] at hdvd
  have := Nat.le_of_dvd (by norm_num) (hdvd.trans (Nat.gcd_dvd_left 3 (2 ^ f + 1)))
  omega

theorem pow_six_le_natCard_of_SU_three {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution F 2 f) 3) W) (hρ : ρ ≠ 1) :
    (2 ^ f) ^ 6 ≤ Nat.card W := by
  classical
  obtain ⟨r, g, hr, hg, hgnot⟩ := exists_order_prime_not_mem_center hF hf
  have hker_ne_top : ρ.ker ≠ ⊤ := by
    intro htop
    apply hρ
    ext x w
    exact congrArg (fun f : W →ₗ[ZMod 2] W => f w)
      (MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top x))
  have hker_le : ρ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) 3) := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple
      (isQuasisimple_SU (p := 2) (f := f) hF le_rfl (three_pair_ne_of_two_le hf)) ρ.ker with
      h | h
    · exact h
    · exact absurd h hker_ne_top
  have hρg : ρ g ≠ 1 := by
    intro h
    exact hgnot (hker_le (MonoidHom.mem_ker.mpr h))
  obtain ⟨b, hb, hbW, hbdvd⟩ :=
    CFSG.LinearAlgebra.exists_prime_dvd_two_pow_sub_one_of_ne_one (ρ := ρ) (g := g) (r := r)
      hr.prime (hr.ne_two (by omega)) hg hρg
  have hk0 : 0 < 6 * f := by omega
  have hkb : 6 * f ∣ b := (hr.dvd_sub_one_iff hk0 b).mp hbdvd
  have hkle : 6 * f ≤ b := Nat.le_of_dvd hb hkb
  calc (2 ^ f) ^ 6 = 2 ^ (f * 6) := (pow_mul 2 f 6).symm
    _ = 2 ^ (6 * f) := by rw [Nat.mul_comm f 6]
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hkle
    _ ≤ Nat.card W := hbW

end CFSG.LieType.Universal.Unitary
