module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddCentralHom

public section

namespace CFSG.EvenSporadicStandard.SuzOuter

open Subgroup

variable {K Q S : Type*} [Group K] [Finite K] [Group Q] [Group S]

theorem facts_of_cover (e : (K ⧸ center K) ≃* S) (hodd : Odd (Nat.card (center K)))
    (hS : Nat.card S = 20160) (hS315 : 315 ≤ Nat.card {t : S // t * t = 1 ∧ t ≠ 1})
    (hS64 : ∀ t : S, t * t = 1 → t ≠ 1 → Nat.card (centralizer ({t} : Set S)) = 64)
    (Ψ : K →* Q) (hker : Ψ.ker ≤ center K) :
    315 ≤ Nat.card {u : ↥Ψ.range // u * u = 1 ∧ u ≠ 1} ∧
      (∀ u : ↥Ψ.range, u * u = 1 → u ≠ 1 →
        64 ∣ Nat.card (centralizer ({u} : Set ↥Ψ.range))) ∧
      ¬ 128 ∣ Nat.card ↥Ψ.range ∧ 7 ∣ Nat.card ↥Ψ.range := by
  set Z := center K with hZ
  let π : K →* S := (e : (K ⧸ Z) →* S).comp (QuotientGroup.mk' Z)
  have hπker : π.ker = Z := by
    ext k
    simp [π]
  have hπ : OddCentralHom π :=
    { surjective := fun s => by
        obtain ⟨q, rfl⟩ := e.surjective s
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
        exact ⟨k, rfl⟩
      central := fun k hk x => by
        rw [hπker] at hk
        exact (mem_center_iff.1 hk x).symm
      odd := by rw [hπker]; exact hodd }
  let ψ : K →* ↥Ψ.range := Ψ.rangeRestrict
  have hψker : ψ.ker = Ψ.ker := Ψ.ker_rangeRestrict
  have hψ : OddCentralHom ψ :=
    { surjective := Ψ.rangeRestrict_surjective
      central := fun k hk x => by
        rw [hψker] at hk
        exact (mem_center_iff.1 (hker hk) x).symm
      odd := by
        rw [hψker]
        exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hker) }
  have hinvπ : ∀ u : K, u * u = 1 → u ≠ 1 → π u * π u = 1 ∧ π u ≠ 1 := by
    intro u hu hu1
    refine ⟨by rw [← map_mul, hu, map_one], fun h => hu1 ?_⟩
    exact hπ.eq_one_of_sq_eq_one (MonoidHom.mem_ker.2 h) hu
  have hinvψ : ∀ u : K, u * u = 1 → u ≠ 1 → ψ u * ψ u = 1 ∧ ψ u ≠ 1 := by
    intro u hu hu1
    refine ⟨by rw [← map_mul, hu, map_one], fun h => hu1 ?_⟩
    exact hψ.eq_one_of_sq_eq_one (MonoidHom.mem_ker.2 h) hu
  have hc1 : 315 ≤ Nat.card {u : K // u * u = 1 ∧ u ≠ 1} := by
    refine hS315.trans (Nat.card_le_card_of_surjective
      (fun u : {u : K // u * u = 1 ∧ u ≠ 1} =>
        (⟨π u.1, hinvπ u.1 u.2.1 u.2.2⟩ : {t : S // t * t = 1 ∧ t ≠ 1})) ?_)
    rintro ⟨v, hv, hv1⟩
    obtain ⟨u, hu, hu1, hφ⟩ := hπ.exists_involution_lift hv hv1
    exact ⟨⟨u, hu, hu1⟩, Subtype.ext hφ⟩
  have hc2 : Nat.card {u : K // u * u = 1 ∧ u ≠ 1} ≤
      Nat.card {u : ↥Ψ.range // u * u = 1 ∧ u ≠ 1} := by
    have : Finite ↥Ψ.range := Finite.of_surjective ψ hψ.surjective
    refine Nat.card_le_card_of_injective
      (fun u : {u : K // u * u = 1 ∧ u ≠ 1} =>
        (⟨ψ u.1, hinvψ u.1 u.2.1 u.2.2⟩ : {u : ↥Ψ.range // u * u = 1 ∧ u ≠ 1})) ?_
    intro a b hab
    have := congrArg (fun z : {u : ↥Ψ.range // u * u = 1 ∧ u ≠ 1} => z.1) hab
    exact Subtype.ext (hψ.eq_of_involutions a.2.1 b.2.1 this)
  have hkerψ : Nat.card ψ.ker ∣ Nat.card Z := by
    rw [hψker]
    exact Subgroup.card_dvd_of_le hker
  obtain ⟨t, ht⟩ := hkerψ
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hrangeπ : Nat.card π.range = Nat.card S := by
    rw [MonoidHom.range_eq_top.2 hπ.surjective, Subgroup.card_top]
  have hrangeψ : Nat.card ψ.range = Nat.card ↥Ψ.range := by
    rw [MonoidHom.range_eq_top.2 hψ.surjective, Subgroup.card_top]
  have hKπ := Subgroup.card_ker_mul_card_range π
  have hKψ := Subgroup.card_ker_mul_card_range ψ
  rw [hπker, hrangeπ, hS] at hKπ
  rw [hrangeψ] at hKψ
  have hX : Nat.card ↥Ψ.range = t * 20160 := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hKψ, ← hKπ, ht]
    ring
  have htodd : Odd t := Odd.of_dvd_nat hodd (Dvd.intro_left _ ht.symm)
  refine ⟨hc1.trans hc2, fun v hv hv1 => ?_, ?_, ?_⟩
  · obtain ⟨u, hu, hu1, rfl⟩ := hψ.exists_involution_lift hv hv1
    have h1 := hπ.card_centralizer hu
    have h2 := hψ.card_centralizer hu
    rw [hS64 _ (hinvπ u hu hu1).1 (hinvπ u hu hu1).2, hπker] at h1
    have hcent : Nat.card (centralizer ({ψ u} : Set ↥Ψ.range)) = t * 64 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [← h2, h1, ht]
      ring
    exact ⟨t, by rw [hcent]; ring⟩
  · rw [hX]
    rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := htodd
    omega
  · rw [hX]
    exact Dvd.dvd.mul_left (by norm_num) t

end CFSG.EvenSporadicStandard.SuzOuter
