module

public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicCyclic
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.SectionRank.OddCover

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary.SUExtras

variable {K : Type} [Field K] [Finite K]

section Torus

variable {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem isCyclic_levelTorus_three :
    IsCyclic (levelTorus (unitaryInvolution K p f) (0 : Fin (3 / 2))) := by
  set σ := unitaryInvolution K p f
  set T := levelTorus σ (0 : Fin (3 / 2))
  have hne : ∀ h : T, mat σ 3 h 0 0 ≠ 0 := by
    rintro ⟨h, hh⟩
    obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh
    simp [ht]
  let φ : T →* Kˣ :=
    { toFun := fun h => Units.mk0 _ (hne h)
      map_one' := by
        ext
        simp [mat_apply]
      map_mul' := by
        rintro ⟨h, hh⟩ ⟨h', hh'⟩
        ext
        obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh
        obtain ⟨t', ht'⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh'
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, map_mul, ht, ht',
          diagonal_mul_diagonal]
        simp }
  have hφ : Function.Injective φ := by
    rintro ⟨h, hh⟩ ⟨h', hh'⟩ hhh
    obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh
    obtain ⟨t', ht'⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh'
    have h1 := congrArg (fun u : Kˣ => (u : K)) hhh
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, ht, ht'] at h1
    simp only [diagonal_apply_eq, Matrix.cons_val_zero] at h1
    have htt : t = t' := Units.ext h1
    subst htt
    exact Subtype.ext (mat_injective (ht.trans ht'.symm))
  exact isCyclic_of_injective φ hφ

end Torus

section Order

variable {p : ℕ}

theorem card_statedSL_three_prime (hK : Nat.card K = p) :
    (Nat.card (StatedSL 3 K) : ℤ) = p ^ 3 * (p - 1) ^ 2 * (p + 1) * (p ^ 2 + p + 1) := by
  rw [card_statedSL_three, hK]
  have hp1 : 1 ≤ p := hK ▸ Nat.card_pos
  push_cast [Nat.one_le_pow 2 p hp1, Nat.one_le_pow 3 p hp1]
  ring

theorem card_statedSU_three_prime [Fact p.Prime] (hK : Nat.card K = p ^ 2) :
    (Nat.card (StatedSU 3 p K) : ℤ) = p ^ 3 * (p + 1) ^ 2 * (p - 1) * (p ^ 2 - p + 1) := by
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have : CharP K p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  have h := card_statedSU_three hK1
  rw [pow_one] at h
  rw [h]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  push_cast [Nat.one_le_pow 2 p hp1]
  ring

end Order

theorem isCyclic_of_isPGroup_of_le_GL_three {H : Subgroup (GL (Fin 3) K)} {r : ℕ} [Fact r.Prime]
    (hrQ : ¬ r ∣ Nat.card K) (hr1 : ¬ r ∣ Nat.card K - 1) {P : Subgroup H} (hP : IsPGroup r P) :
    IsCyclic P := by
  have hcyc := isCyclic_of_isPGroup_GL_three hrQ hr1 (hP.map H.subtype)
  let e := P.equivMapOfInjective H.subtype H.subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem prime_classical_three_cyclic_odd_sylows {p : ℕ} (hp : p.Prime) {ε : ℤ}
    {H : Subgroup (GL (Fin 3) K)}
    (hH : (ε = 1 ∧ Nat.card K = p ∧ H = StatedSL 3 K) ∨
      (ε = -1 ∧ Nat.card K = p ^ 2 ∧ H = StatedSU 3 p K)) :
    (∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → r ≠ p → ¬ (r : ℤ) ∣ p - ε →
      ∀ P : Sylow r H, IsCyclic (P : Subgroup H)) ∧
    (Nat.card H : ℤ) = p ^ 3 * (p - ε) ^ 2 * (p + ε) * (p ^ 2 + ε * p + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hrp : ∀ r : ℕ, r.Prime → r ≠ p → ¬ r ∣ p := fun r hr hrp h =>
    hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 h)
  rcases hH with ⟨rfl, hK, rfl⟩ | ⟨rfl, hK, rfl⟩
  · refine ⟨fun r hr _ hrp' hr1 P => ?_, ?_⟩
    · refine isCyclic_of_isPGroup_of_le_GL_three (by rw [hK]; exact hrp r hr.out hrp')
        (fun h => hr1 ?_) P.isPGroup'
      rw [hK] at h
      have := Int.natCast_dvd_natCast.2 h
      rwa [Nat.cast_sub hp1, Nat.cast_one] at this
    · rw [card_statedSL_three_prime hK]
      ring
  · refine ⟨fun r hr hr2 hrp' hr1 P => ?_, ?_⟩
    · have hr1' : ¬ r ∣ p + 1 := fun h => hr1 (by
        have := Int.natCast_dvd_natCast.2 h
        rwa [Nat.cast_add, Nat.cast_one, ← sub_neg_eq_add] at this)
      by_cases hrm : r ∣ p - 1
      ·
        have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
        have : CharP K p := by
          have := Fintype.ofFinite K
          exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
        let e : SU (unitaryInvolution K p 1) 3 ≃* StatedSU 3 p K :=
          (equivStatedSU hK1 3).trans (MulEquiv.subgroupCongr (by rw [pow_one]))
        set T := levelTorus (unitaryInvolution K p 1) (0 : Fin (3 / 2))
        have : IsCyclic T := isCyclic_levelTorus_three
        set Z : Subgroup (StatedSU 3 p K) := T.map e.toMonoidHom
        have : IsCyclic Z := isCyclic_of_surjective (e.toMonoidHom.subgroupMap T)
          (MonoidHom.subgroupMap_surjective _ _)
        have hZ : Nat.card Z = p ^ 2 - 1 := by
          rw [Subgroup.card_map_of_injective e.injective, card_levelTorus_three hK1, pow_one]
        have hm : ¬ r ∣ p ^ 3 * (p ^ 3 + 1) := by
          refine hr.out.not_dvd_mul (fun h => hrp r hr.out hrp' (hr.out.dvd_of_dvd_pow h)) ?_
          intro h
          have h3 : r ∣ p ^ 3 - 1 := by
            have : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
              zify [hp1, Nat.one_le_pow 3 p hp1]
              ring
            rw [this]
            exact Dvd.dvd.mul_right hrm _
          have h2 : r ∣ 2 := by
            have := Nat.dvd_sub h h3
            rwa [show p ^ 3 + 1 - (p ^ 3 - 1) = 2 by
              have := Nat.one_le_pow 3 p hp1
              omega] at this
          exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).1 h2)
        refine isCyclic_of_isPGroup_of_card_eq_mul (Z := Z) (m := p ^ 3 * (p ^ 3 + 1)) ?_ hm
          P.isPGroup'
        have hcard := card_statedSU_three_prime (K := K) hK
        have hle : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp1
        rw [hZ]
        zify [hle]
        rw [hcard]
        ring
      · refine isCyclic_of_isPGroup_of_le_GL_three ?_ ?_ P.isPGroup'
        · rw [hK]
          exact fun h => hrp r hr.out hrp' (hr.out.dvd_of_dvd_pow h)
        · rw [hK]
          intro h
          have : p ^ 2 - 1 = (p - 1) * (p + 1) := by
            zify [hp1, Nat.one_le_pow 2 p hp1]
            ring
          rw [this] at h
          rcases (Nat.Prime.dvd_mul hr.out).1 h with h' | h'
          · exact hrm h'
          · exact hr1' h'
    · rw [card_statedSU_three_prime hK]
      ring

end CFSG.SectionRank.OddCover
