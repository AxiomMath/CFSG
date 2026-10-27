module

public import CFSG.GH74.GLS.Stage4.T2CentSL
public import CFSG.GH74.GLS.Stage4.T2SL2C

public section

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

namespace CFSG.GH74.GLS.Stage4.Rest.Rem

theorem gen_odd_of_sl2 {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    K ≤ Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)} := by
  let φ : SL2 F →* G := K.subtype.comp e.symm.toMonoidHom
  have hrange : φ.range = K := by
    have h1 : e.symm.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 e.symm.surjective
    rw [MonoidHom.range_comp, h1, Subgroup.map_top, Subgroup.range_subtype]
  have hp : (Nat.card F).minFac = ringChar F := minFac_card_eq_ringChar
  refine t2C_gen_odd (q := Nat.card F) hodd (X := (uSub F).map φ) (X' := (lSub F).map φ) ?_ ?_ ?_
  · rw [← Subgroup.map_sup, uSub_sup_lSub, ← MonoidHom.range_eq_map, hrange]
  · rintro x ⟨u, hu, rfl⟩
    rw [← map_pow, hp, pow_char_uSub (ringChar F) u hu, map_one]
  · rintro x ⟨u, hu, rfl⟩
    rw [← map_pow, hp, pow_char_lSub (ringChar F) u hu, map_one]

theorem pow_two_pow_eq_one_of_sl2 {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ} (hn : 2 ≤ n)
    (hv : (Nat.card ↥K).factorization 2 = n + 1) {x : G} (hx : x ∈ K) {m : ℕ} (hxm : x ^ (2 ^ m) = 1) :
    x ^ (2 ^ n) = 1 := by
  set y : SL2 F := e ⟨x, hx⟩ with hy
  have hym : y ^ (2 ^ m) = 1 := by
    rw [hy, ← map_pow]
    have : (⟨x, hx⟩ : ↥K) ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hxm)
    rw [this, map_one]
  have hcard : (Nat.card (SL2 F)).factorization 2 = n + 1 := by
    rw [← Nat.card_congr e.toEquiv]; exact hv
  suffices hyn : y ^ (2 ^ n) = 1 by
    have : (⟨x, hx⟩ : ↥K) ^ (2 ^ n) = 1 := e.injective (by rw [map_pow, ← hy, hyn, map_one])
    simpa using congrArg Subtype.val this
  have hp2 : IsPGroup 2 (Subgroup.zpowers y) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hym)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨P, hP⟩ := hp2.exists_le_sylow
  have hPcard : Nat.card P = 2 ^ (n + 1) := by rw [Sylow.card_eq_multiplicity, hcard]
  obtain ⟨m', hm3, ⟨ψ⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hodd P
  have hyP : y ∈ (P : Subgroup (SL2 F)) := hP (Subgroup.mem_zpowers y)
  have hQcard : Nat.card (QuaternionGroup (2 ^ (m' - 2))) = 2 ^ m' := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 2 := ⟨m' - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]
    ring
  have hm' : m' = n + 1 := by
    have h1 : Nat.card P = Nat.card (QuaternionGroup (2 ^ (m' - 2))) := Nat.card_congr ψ.toEquiv
    rw [hPcard, hQcard] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hexp : Monoid.exponent (QuaternionGroup (2 ^ (m' - 2))) ∣ 2 ^ n := by
    rw [QuaternionGroup.exponent]
    have h2 : 2 ∣ 2 ^ (m' - 2) := dvd_pow_self 2 (by omega)
    have h3 : lcm (2 ^ (m' - 2)) 2 ∣ 2 ^ (m' - 2) := lcm_dvd dvd_rfl h2
    calc 2 * lcm (2 ^ (m' - 2)) 2 ∣ 2 * 2 ^ (m' - 2) := mul_dvd_mul_left 2 h3
      _ = 2 ^ n := by
        rw [← pow_succ']
        congr 1
        omega
  have hg : (ψ ⟨y, hyP⟩) ^ (2 ^ n) = 1 := by
    obtain ⟨c, hc⟩ := hexp
    rw [hc, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
  have h4 : (⟨y, hyP⟩ : ↥(P : Subgroup (SL2 F))) ^ (2 ^ n) = 1 :=
    ψ.injective (by rw [map_pow, hg, map_one])
  simpa using congrArg Subtype.val h4

end CFSG.GH74.GLS.Stage4.Rest.Rem
