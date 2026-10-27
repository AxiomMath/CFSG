module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.OctadSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Assemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.UniqueCo1
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Perf
public import CFSG.Monster.Existence.Compat.Co1Iso
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster
  CFSG.Monster.Code CFSG.Monster.ScalarKernel CFSG.Monster.Existence.Compat
  CFSG.Monster.B.TwoA.Census

theorem factorization_card_double_cover {G : Type} [Group G]
    {L : Subgroup G} (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Co1) :
    (Nat.card L).factorization 2 = 22 := by
  obtain ⟨e⟩ := hQ
  have h1 : Nat.card (L ⧸ center L) = 4157776806543360000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Co1.card_Co1
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), h1, h2,
    show 4157776806543360000 * 2 = 2 ^ 22 * 1982582476875 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem exists_embedding_latticeO
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hperf : Group.IsPerfect L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Co1) {z : G}
    (hz2 : orderOf z = 2) (hZ : (center L).map L.subtype = zpowers z) :
    ∃ ψ : latticeO →* G, Function.Injective ψ ∧ ψ.range = L ∧ ψ negOneO = z := by
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by decide)
  have hmCo0 : IsSporadic (monsterCo0 ⧸ center monsterCo0) .Co1 := ⟨co1EquivMonsterCo1.symm⟩
  have hnegsq : negCo0 ^ 2 = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    show (negCo0 * negCo0 : monsterCo0).1 v = v
    show (negCo0 : monsterCo0).1 ((negCo0 : monsterCo0).1 v) = v
    rw [coe_negCo0, coe_negCo0, neg_neg]
  have hnegne : negCo0 ≠ 1 := by
    intro h1
    rw [← co0Equiv_negOneO] at h1
    have h2' : negOneO = 1 := co0Equiv.injective (h1.trans (map_one co0Equiv).symm)
    have h3 := congrArg (fun g => mat g (0 : Fin 24) 0) h2'
    simp [mat_negOneO, mat_one] at h3
    norm_num at h3
  have hc2 : Nat.card (center monsterCo0) = 2 := by
    rw [center_monsterCo0, Nat.card_zpowers]
    exact orderOf_eq_prime hnegsq hnegne
  have hfin : Finite monsterCo0 := by
    have hfC : Finite NativeSporadic.Co1 := (CFSG.Sporadic.Co1.fam_co1_simplicity).1
    have hfQ : Finite MonsterCo1 := Finite.of_equiv _ co1EquivMonsterCo1.toEquiv
    refine Nat.finite_of_card_ne_zero ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center monsterCo0), hc2]
    have : Nat.card (monsterCo0 ⧸ center monsterCo0) ≠ 0 := Nat.card_pos.ne'
    omega
  obtain ⟨e⟩ := nonempty_mulEquiv_of_doubleCovers_Co1 hperf monsterCo0_isPerfect h2 hc2 hQ hmCo0
  obtain ⟨w, hw, hwz⟩ : z ∈ (center L).map L.subtype := hZ ▸ mem_zpowers z
  have hez : e w = negCo0 := by
    have hcen : e w ∈ center monsterCo0 := by
      rw [mem_center_iff]
      intro m
      obtain ⟨a, rfl⟩ := e.surjective m
      rw [← map_mul, ← map_mul, mem_center_iff.1 hw a]
    have hne : e w ≠ 1 := fun h1 => hz1 (by
      have : w = 1 := e.injective (h1.trans (map_one e).symm)
      rw [← hwz, this]; rfl)
    rw [center_monsterCo0] at hcen
    rcases eq_one_or_eq_of_mem_zpowers hnegsq hcen with h1 | h1
    · exact absurd h1 hne
    · exact h1
  let e' : L ≃* latticeO := e.trans co0Equiv.symm
  let ψ : latticeO →* G := L.subtype.comp e'.symm.toMonoidHom
  refine ⟨ψ, Subtype.val_injective.comp e'.symm.injective, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e'.symm.surjective]
    simp [Subgroup.map_top]
  · show (e.symm (co0Equiv negOneO) : G) = z
    rw [co0Equiv_negOneO, ← hez, MulEquiv.symm_apply_apply]
    exact hwz

theorem octadIsolation :
    OctadIsolation := by
  intro G _ _ L h h2 hQ z hz2 hCz hZ g hInv
  have hperf : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
  obtain ⟨ψ, hψ, hψL, hψz⟩ := exists_embedding_latticeO hperf h2 hQ hz2 hZ
  obtain ⟨hxL, hx2, hxz, -, hxc⟩ := hInv
  have hfac := factorization_card_double_cover h2 hQ
  have hS1L : (monoSub (sylowP : Subgroup AutPerm)).map ψ ≤ L :=
    hψL ▸ Subgroup.map_le_range ψ _
  have hS1card : Nat.card ((monoSub (sylowP : Subgroup AutPerm)).map ψ) =
      2 ^ (Nat.card L).factorization 2 := by
    rw [Subgroup.card_map_of_injective hψ, card_monoSub_sylowP, hfac]
  have hdvd : 2 ^ (Nat.card L).factorization 2 ∣
      Nat.card (L ⊓ centralizer ({g * z * g⁻¹} : Set G) : Subgroup G) := by
    rw [hfac]
    have : Nat.card (L ⊓ centralizer ({g * z * g⁻¹} : Set G) : Subgroup G) = co0C2 := hxc
    rw [this]
    exact ⟨3 ^ 5 * 5 ^ 2 * 7, by simp [co0C2]⟩
  obtain ⟨c, hcL, hyS1, hSy, hsq⟩ := exists_fusion_in_sylow hz2 hCz hS1L hS1card hxL hdvd
  obtain ⟨y', hy'S, hy'⟩ := hyS1
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 (by rw [hCz]; exact hcL)
  have hy'1 : y' ≠ 1 := by
    rintro rfl
    rw [map_one] at hy'
    have hx1 : g * z * g⁻¹ = 1 := by
      calc g * z * g⁻¹ = c⁻¹ * (c * (g * z * g⁻¹) * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [← hy']
        _ = 1 := by group
    rw [hx1, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  have hy'n : y' ≠ negOneO := by
    rintro rfl
    rw [hψz] at hy'
    refine hxz ?_
    have hy'' : c * (g * z * g⁻¹) * c⁻¹ = z := hy'.symm
    calc g * z * g⁻¹ = c⁻¹ * (c * (g * z * g⁻¹) * c⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [hy'']
      _ = c⁻¹ * (z * c) := mul_assoc _ _ _
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := inv_mul_cancel_left c z
  have hcentral : ∀ s ∈ monoSub (sylowP : Subgroup AutPerm), s * y' = y' * s := by
    intro s hs
    have hmem := hSy (Subgroup.mem_map_of_mem ψ hs)
    rw [mem_centralizer_singleton_iff, ← hy', ← map_mul, ← map_mul] at hmem
    exact hψ hmem
  have hcount : sqCount (monoSub (sylowP : Subgroup AutPerm)) y' =
      sqCount (monoSub (sylowP : Subgroup AutPerm)) negOneO := by
    rw [← hy', ← hψz, sqCount_map ψ hψ, sqCount_map ψ hψ] at hsq
    exact hsq
  exact sqCount_monoSub_ne hy'S hcentral hy'1 hy'n hcount

end CFSG.EvenSporadicStandard.TwoCo1
