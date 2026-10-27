module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueBasic

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 Cover

theorem exists_perfect_lift {X : Type} [Group X] (hodd : Odd (Nat.card (center X)))
    {ut : X ⧸ center X} {Kt : Subgroup (X ⧸ center X)} (hut : ut * ut = 1) (hut1 : ut ≠ 1)
    (hKtu : ∀ k ∈ Kt, k * ut = ut * k) (hKt : ⁅Kt, Kt⁆ = Kt) :
    ∃ (K : Subgroup X) (u : X), u * u = 1 ∧ u ≠ 1 ∧ (∀ k ∈ K, k * u = u * k) ∧ ⁅K, K⁆ = K ∧
      K.map (q X) = Kt := by
  set M : Subgroup X := Kt.comap (q X) with hM
  set K : Subgroup X := ⁅M, M⁆ with hK
  have hMmap : M.map (q X) = Kt := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) Kt
  have hKmap : K.map (q X) = Kt := by
    rw [hK, Subgroup.map_commutator, hMmap, hKt]
  have hMK : M = K ⊔ center X := by
    rw [hM, ← hKmap, comap_map_q]
  have hperf : ⁅K, K⁆ = K := by
    refine le_antisymm (commutator_self_le K) ?_
    calc K = ⁅M, M⁆ := rfl
      _ = ⁅K ⊔ center X, K ⊔ center X⁆ := by rw [← hMK]
      _ ≤ ⁅K, K⁆ := commutator_sup_center_le K
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center X) ut
  obtain ⟨u, -, hu2, hu⟩ := exists_involution_lift hodd (K := ⊤) (kt := ut)
    (Subgroup.mem_map.2 ⟨x, Subgroup.mem_top _, hx⟩) hut
  refine ⟨K, u, hu2, ?_, ?_, hperf, hKmap⟩
  · intro h
    rw [h, map_one] at hu
    exact hut1 hu.symm
  · intro k hk
    have hc : u ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff_of_perfect hperf, hu, mem_centralizer_iff]
      intro h hh
      exact hKtu h (hKmap ▸ hh)
    exact mem_centralizer_iff.1 hc k hk

theorem exists_pair_of_pinned_pair {H : Type} [Group H] {L : Subgroup H}
    (hodd : Odd (Nat.card (center ↥L))) {Y : Type} [Group Y] (e : (↥L ⧸ center ↥L) ≃* Y)
    {u₀ : Y} {K₀ : Subgroup Y} (hu : u₀ * u₀ = 1) (hu1 : u₀ ≠ 1)
    (hKu : ∀ k ∈ K₀, k * u₀ = u₀ * k) (hK : ⁅K₀, K₀⁆ = K₀) :
    ∃ (K : Subgroup H) (u : H), u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧
      Group.IsPerfect ↥K ∧ (K.subgroupOf L).map (q ↥L) = K₀.map e.symm.toMonoidHom := by
  obtain ⟨K', u', hu', hu'1, hK'u, hK', hmap⟩ := exists_perfect_lift (X := ↥L) hodd
    (ut := e.symm u₀) (Kt := K₀.map e.symm.toMonoidHom)
    (by rw [← map_mul, hu, map_one]) (fun h => hu1 (e.symm.injective (by rw [h, map_one])))
    (by
      rintro _ ⟨k, hk, rfl⟩
      show e.symm k * e.symm u₀ = e.symm u₀ * e.symm k
      rw [← map_mul, ← map_mul, hKu k hk])
    (by rw [← Subgroup.map_commutator, hK])
  have hperf : Group.IsPerfect ↥K' := isPerfect_iff.mpr hK'
  refine ⟨K'.map L.subtype, (u' : H), u'.2, ?_, Subgroup.map_subtype_le K', ?_, ?_, ?_⟩
  · refine orderOf_eq_two_of_mul_self ?_ ?_
    · exact congrArg Subtype.val hu'
    · intro h
      exact hu'1 (Subtype.ext h)
  · rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (hK'u k hk)
  · exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.equivMapOfInjective K' L.subtype L.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective K' L.subtype L.subtype_injective).surjective
  · have h1 : (K'.map L.subtype).subgroupOf L = K' :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective K'
    rw [h1]
    exact hmap

theorem exists_odd_card_map_q {H : Type} [Group H] {L K : Subgroup H} [Finite ↥K]
    (hKL : K ≤ L) (hodd : Odd (Nat.card (center ↥L))) :
    ∃ r : ℕ, Odd r ∧ Nat.card ↥((K.subgroupOf L).map (q ↥L)) =
      Nat.card (↥K ⧸ CFSG.oddCore ↥K) * r := by
  let ψ : ↥K →* ↥L ⧸ center ↥L := (q ↥L).comp (Subgroup.inclusion hKL)
  have hrange : ψ.range = (K.subgroupOf L).map (q ↥L) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨k.1, hKL k.2⟩, k.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, hx⟩, rfl⟩
  have h1 : Nat.card ψ.range * Nat.card ψ.ker = Nat.card ↥K := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker).symm
  have hkerodd : Odd (Nat.card ψ.ker) := by
    let κ : ↥ψ.ker →* ↥(center ↥L) :=
      { toFun := fun x => ⟨Subgroup.inclusion hKL x.1, q_eq_one_iff.1 (MonoidHom.mem_ker.1 x.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hκ : Function.Injective κ := fun x y h => Subtype.ext (Subtype.ext
      (congrArg (fun z : ↥(center ↥L) => ((z : ↥L) : H)) h))
    exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective κ hκ)
  have hle : ψ.ker ≤ CFSG.oddCore ↥K :=
    RuStd.S2.Glue.le_oddCore ψ.normal_ker hkerodd
  obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hle
  have hrodd : Odd r := by
    have := RuStd.S2.Glue.odd_card_oddCore ↥K
    rw [hr] at this
    exact (Nat.odd_mul.1 this).2
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K)
  refine ⟨r, hrodd, ?_⟩
  rw [← hrange]
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have h3 : Nat.card ψ.range * Nat.card ψ.ker =
      Nat.card (↥K ⧸ CFSG.oddCore ↥K) * r * Nat.card ψ.ker := by
    rw [h1, h2, hr]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h3

theorem card_map_q_eq {H : Type} [Group H] {L K : Subgroup H} [Finite ↥K] (hKL : K ≤ L)
    (hodd : Odd (Nat.card (center ↥L))) {d j a : ℕ} (hd : 0 < d) (hj : Odd j)
    (hq : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = d * j)
    (hdvd : Nat.card ↥((K.subgroupOf L).map (q ↥L)) ∣ d * 2 ^ a) :
    Nat.card ↥((K.subgroupOf L).map (q ↥L)) = d := by
  obtain ⟨r, hr, hcard⟩ := exists_odd_card_map_q hKL hodd
  rw [hcard, hq, mul_assoc] at hdvd ⊢
  have h1 : j * r ∣ 2 ^ a := (Nat.mul_dvd_mul_iff_left hd).1 hdvd
  have h2 : j * r = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right a (Nat.coprime_two_right.2 (hj.mul hr))) h1
  rw [h2, mul_one]

end CFSG.EvenSporadicStandard.Induction
