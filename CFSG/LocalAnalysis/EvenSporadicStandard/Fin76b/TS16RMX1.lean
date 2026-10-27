module

public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native

theorem card_inf_cent_eq {G : Type*} [Group G] {L : Subgroup G} {x : G} (hxL : x ∈ L) :
    Nat.card ↥(L ⊓ centralizer ({x} : Set G)) =
      Nat.card ↥(centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L)) := by
  have h1 : (L ⊓ centralizer ({x} : Set G)).subgroupOf L =
      centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨y.2, congrArg Subtype.val h⟩
  rw [← h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ centralizer ({x} : Set G) ≤ L)).toEquiv).symm

theorem card_cent_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (a : X) :
    Nat.card ↥(centralizer ({a} : Set X)) = Nat.card ↥(centralizer ({e a} : Set Y)) := by
  have h1 : (centralizer ({a} : Set X)).map e.toMonoidHom = centralizer ({e a} : Set Y) := by
    ext y
    simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, hx]
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  rw [← h1]
  exact Nat.card_congr (e.subgroupMap (centralizer ({a} : Set X))).toEquiv

theorem not_dvd_nine_transport {G M : Type*} [Group G] [Group M] {L : Subgroup G}
    {P : Subgroup M} (e : ↥L ≃* ↥P)
    (hP : ∀ y ∈ P, y * y = 1 → y ≠ 1 → ¬ 9 ∣ Nat.card ↥(P ⊓ centralizer ({y} : Set M)))
    {x : G} (hxL : x ∈ L) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ¬ 9 ∣ Nat.card ↥(L ⊓ centralizer ({x} : Set G)) := by
  set a : ↥L := ⟨x, hxL⟩ with ha
  set y : ↥P := e a with hy
  have hy2 : y * y = 1 := by
    rw [hy, ← map_mul]
    have : a * a = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hy1 : y ≠ 1 := by
    intro h1
    apply hx1
    have : a = 1 := e.injective (by rw [← hy, h1, map_one])
    exact congrArg Subtype.val this
  have h1 := hP (y : M) y.2 (congrArg Subtype.val hy2) (fun h => hy1 (Subtype.ext h))
  rw [card_inf_cent_eq y.2] at h1
  rw [card_inf_cent_eq hxL, card_cent_mulEquiv e a]
  exact h1

theorem j2P_invol_not_dvd_nine :
    ∀ y ∈ j2P, y * y = 1 → y ≠ 1 → ¬ 9 ∣ Nat.card ↥(j2P ⊓ centralizer ({y} : Set _)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  intro y hy hy2 hy1
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨r, hr, g, hg, hyg⟩ := hcover y (show y ∈ j2P ⊔ zpowers j2u from Subgroup.mem_sup_left hy) hord
  obtain ⟨-, -, hout, -, hcent, -⟩ := hrows r hr
  have hrepP : tp 315 r.rep ∈ j2P := by
    have : tp 315 r.rep = g⁻¹ * y * g := by rw [hyg]; group
    rw [this]
    exact j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hy) hg
  have hout' : r.outer = false := by
    cases hro : r.outer
    · rfl
    · exact absurd hrepP ((hout.1 hro))
  have hcard : Nat.card ↥(j2P ⊓ centralizer ({y} : Set _)) = r.centOrder := by
    rw [hyg, inf_centralizer_conj j2P hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcent
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      [(true, 1800, 336), (false, 2520, 240), (false, 315, 1920)] := by
    rw [← hmap]
    exact List.mem_map_of_mem hr
  rw [hcard]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨h1, -, -⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
  · rw [hout'] at h1; exact absurd h1 (by decide)
  · rw [h3]; decide
  · rw [h3]; decide

theorem j3P_invol_not_dvd_nine :
    ∀ y ∈ j3P, y * y = 1 → y ≠ 1 → ¬ 9 ∣ Nat.card ↥(j3P ⊓ centralizer ({y} : Set _)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  intro y hy hy2 hy1
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨r, hr, g, hg, hyg⟩ := hcover y (show y ∈ j3P ⊔ zpowers j3u from Subgroup.mem_sup_left hy) hord
  obtain ⟨-, -, hout, -, hcent, -⟩ := hrows r hr
  have hrepP : tp 6156 r.rep ∈ j3P := by
    have : tp 6156 r.rep = g⁻¹ * y * g := by rw [hyg]; group
    rw [this]
    exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) hy) hg
  have hout' : r.outer = false := by
    cases hro : r.outer
    · rfl
    · exact absurd hrepP ((hout.1 hro))
  have hcard : Nat.card ↥(j3P ⊓ centralizer ({y} : Set _)) = r.centOrder := by
    rw [hyg, inf_centralizer_conj j3P hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcent
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      [(false, 26163, 1920), (true, 20520, 2448)] := by
    rw [← hmap]
    exact List.mem_map_of_mem hr
  rw [hcard]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨-, -, h3⟩ | ⟨h1, -, -⟩
  · rw [h3]; decide
  · rw [hout'] at h1; exact absurd h1 (by decide)

theorem not_dvd_nine_cent_involution
    {G : Type} [Group G] {L : Subgroup G} (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) {x : G}
    (hxL : x ∈ L) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ¬ 9 ∣ Nat.card ↥(L ⊓ centralizer ({x} : Set G)) := by
  rcases hJ with hL | hL
  · obtain ⟨eL⟩ := hL
    exact not_dvd_nine_transport (eL.trans j2PermEquiv) j2P_invol_not_dvd_nine hxL hx2 hx1
  · obtain ⟨eL⟩ := hL
    exact not_dvd_nine_transport (eL.trans j3PermEquiv) j3P_invol_not_dvd_nine hxL hx2 hx1

end CFSG.EvenSporadicStandard.Fin76b
