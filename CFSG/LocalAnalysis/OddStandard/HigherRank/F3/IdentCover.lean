module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Lift

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG CFSG.Open

theorem false_of_central_cover {P Q : Type} [Group P] [Finite P] [Group Q] [Finite Q]
    (f : P →* Q) (hf : Function.Surjective f) (hk : f.ker ≤ center P)
    (hP : Group.IsPerfect P) (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    {x : P} (hx2 : ∃ a : ℕ, orderOf x = 2 ^ a) (hx : x ^ 2 ≠ 1)
    (hfx : f x ∈ center Q) (hfx2 : f x ^ 2 = 1)
    (h : ¬ PartialCentre Q ∨ ∀ m : griessHopfMultiplier (Q ⧸ center Q), m ^ 2 = 1) :
    False := by
  rcases h with hpc | hexp
  ·
    have hx2mem : x ^ 2 ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, hfx2]
    have h2dvd : 2 ∣ Nat.card f.ker := by
      obtain ⟨a, ha⟩ := hx2
      have hdvd : orderOf (x ^ 2) ∣ 2 ^ a := ha ▸ orderOf_pow_dvd 2
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact hx (orderOf_eq_one_iff.mp hk)
      have hkb : 2 ^ k ∣ Nat.card f.ker := hk ▸ Subgroup.orderOf_dvd_natCard f.ker hx2mem
      exact (dvd_pow_self 2 hk0).trans hkb
    exact (not_two_dvd_card_ker_of_full_cover f hf hk hP hQ hO hpc) h2dvd
  ·
    haveI : Group.IsPerfect P := hP
    haveI : Group.IsPerfect Q := hQ.1
    haveI : Group.IsPerfect (Q ⧸ center Q) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center Q))
        (QuotientGroup.mk'_surjective _)
    set φ : P →* Q ⧸ center Q := (QuotientGroup.mk' (center Q)).comp f with hφ
    have hφs : Function.Surjective φ :=
      (QuotientGroup.mk'_surjective (center Q)).comp hf
    have hφk : φ.ker = center P := by
      rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
        comap_center_eq_of_central_cover f hf hk hP]
    have hC : φ.ker ≤ center P := hφk.le
    obtain ⟨-, h, -, -, -, hmap, -⟩ :=
      CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier
        φ hφs hC
    have hxker : x ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hφ]
      change QuotientGroup.mk' (center Q) (f x) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hfx
    have hxmap : x ∈ (CFSG.RankThree.PerfectCover.hopfMultiplier (Q ⧸ center Q)).map h := by
      rw [hmap]
      exact hxker
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hxmap
    have hm2 : m ^ 2 = 1 := by
      have h2 := hexp
        ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (Q ⧸ center Q)).symm
          ⟨m, hm⟩)
      have h3 := congrArg
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (Q ⧸ center Q)) h2
      rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h3
      simpa using congrArg Subtype.val h3
    have hx2one : x ^ 2 = 1 := by
      rw [← hmx, ← map_pow, hm2, map_one]
    exact hx hx2one

end CFSG.OddStandard.HigherRank.F3.Ident
