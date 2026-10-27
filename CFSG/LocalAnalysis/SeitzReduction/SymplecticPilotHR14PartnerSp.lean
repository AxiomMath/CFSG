module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotClassOrders
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotAutU

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K] {n : ℕ}

section Conj

theorem conj_permSp_siegDiag (π : Equiv.Perm (Fin n)) (p : Fin n) (c : K) :
    permSp K π * siegDiag K p c * (permSp K π)⁻¹ = siegDiag K (π p) c := by
  apply mat_injective
  ext a b
  obtain ⟨x, rfl⟩ := (sumMap_bijective π).surjective a
  obtain ⟨y, rfl⟩ := (sumMap_bijective π).surjective b
  rw [mat_conj_permSp_apply, mat_siegDiag, mat_siegDiag]
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.one_apply, Matrix.single_apply, π.injective.eq_iff]

theorem card_centralizer_siegDiag_eq (p p' : Fin n) (c : K) :
    Nat.card (centralizer ({siegDiag K p c} : Set (StatedSp n K))) =
      Nat.card (centralizer ({siegDiag K p' c} : Set (StatedSp n K))) := by
  have h := map_centralizer_singleton_mulEquiv (MulAut.conj (permSp K (Equiv.swap p p')))
    (siegDiag K p c)
  rw [MulAut.conj_apply, conj_permSp_siegDiag, Equiv.swap_apply_left] at h
  rw [← h]
  exact (Subgroup.card_map_of_injective (MulAut.conj _).injective).symm

end Conj

section TwoCentral

theorem siegDiag_zero_eq_twoCentralElt (m : ℕ) :
    siegDiag K (0 : Fin (m + 2)) 1 = twoCentralElt (m + 2) 0 1 1 0 := by
  rw [twoCentralElt_eq_siegDiag_mul_siegPair]
  rw [show siegPair K (0 : Fin (m + 2)) 1 0 = 1 from by
    rw [siegPair, ← upperUnipotentSp_zero (m := m + 2) (K := K)]
    exact upperUnipotentSp_congr _ _ (by rw [single_zero, single_zero, add_zero]), mul_one]

variable [CharP K 2]

theorem unipotent_le_centralizer_siegDiag_zero (m : ℕ) :
    unipotent (m + 2) K ≤
      centralizer ({siegDiag K (0 : Fin (m + 2)) 1} : Set (StatedSp (m + 2) K)) := by
  have hz : siegDiag K (0 : Fin (m + 2)) 1 ∈
      centralizer (unipotent (m + 2) K : Set (StatedSp (m + 2) K)) := by
    rw [centralizer_unipotent]
    exact ⟨1, 0, (siegDiag_zero_eq_twoCentralElt m).symm⟩
  intro u hu
  rw [mem_centralizer_singleton_iff]
  exact mem_centralizer_iff.1 hz u hu

variable [Finite K]

theorem factorization_card_centralizer_siegDiag (m : ℕ) (p : Fin (m + 2)) :
    (Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 2) K)))).factorization 2 =
      (Nat.card (StatedSp (m + 2) K)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent
    (K := K) 2 (m + 2)
  rw [card_centralizer_siegDiag_eq p 0]
  set C := centralizer ({siegDiag K (0 : Fin (m + 2)) 1} : Set (StatedSp (m + 2) K)) with hC
  have hPC : (P : Subgroup (StatedSp (m + 2) K)) ≤ C := by
    rw [hP]
    exact unipotent_le_centralizer_siegDiag_zero m
  have hdvd1 : Nat.card C ∣ Nat.card (StatedSp (m + 2) K) := Subgroup.card_subgroup_dvd_card C
  have hdvd2 : Nat.card (P : Subgroup (StatedSp (m + 2) K)) ∣ Nat.card C :=
    Subgroup.card_dvd_of_le hPC
  have hPc := P.card_eq_multiplicity
  have hS0 : Nat.card (StatedSp (m + 2) K) ≠ 0 := Nat.card_pos.ne'
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  apply le_antisymm
  · exact (Nat.factorization_le_iff_dvd hC0 hS0).2 hdvd1 2
  · rw [hPc] at hdvd2
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hC0).1 hdvd2

omit [CharP K 2] [Finite K] in
theorem siegDiag_one_ne_one (p : Fin n) : siegDiag K p 1 ≠ 1 := by
  intro h
  have h1 := congrArg (fun g => mat n K g (Sum.inl p) (Sum.inr p)) h
  simp only [mat_siegDiag, map_one, fromBlocks_apply₁₂, single_apply_same, Matrix.one_apply,
    reduceCtorEq, ↓reduceIte] at h1
  exact one_ne_zero h1

theorem card_centralizer_siegDiag_lt (p : Fin n) :
    Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp n K))) < Nat.card (StatedSp n K) := by
  refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun h => ?_
  have htop := Subgroup.card_eq_iff_eq_top _ |>.1 h
  have hz : siegDiag K p 1 ∈ center (StatedSp n K) := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({siegDiag K p 1} : Set (StatedSp n K)) := htop ▸ mem_top g
    exact mem_centralizer_singleton_iff.1 hg
  rw [center_statedSp_eq_bot, mem_bot] at hz
  exact siegDiag_one_ne_one p hz

end TwoCentral

section Class

variable [Finite K] [CharP K 2]

theorem exists_conj_eq_siegDiag_last (hK : 4 ≤ Nat.card K) {m : ℕ} {X : Type*} [Group X]
    [Finite X] (e : X ≃* StatedSp (m + 3) K) {x : X} (hx : x ≠ 1)
    (hperf : ⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆ = centralizer ({x} : Set X))
    {p : Fin (m + 3)}
    (hcard : Nat.card (centralizer ({x} : Set X)) =
      Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 3) K)))) :
    ∃ c : X, c * x * c⁻¹ = e.symm (siegDiag K (Fin.last (m + 2)) 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : (Nat.card (centralizer ({x} : Set X))).factorization 2 =
      (Nat.card X).factorization 2 := by
    rw [hcard, factorization_card_centralizer_siegDiag (m + 1) p, Nat.card_congr e.toEquiv]
  obtain ⟨U₀⟩ : Nonempty (Sylow 2 (centralizer ({x} : Set X))) := inferInstance
  set U : Subgroup X := (U₀ : Subgroup (centralizer ({x} : Set X))).map
    (centralizer ({x} : Set X)).subtype with hU
  have hUc : Nat.card U = 2 ^ (Nat.card X).factorization 2 := by
    rw [hU, Subgroup.card_map_of_injective (subtype_injective _), U₀.card_eq_multiplicity, hv]
  let U' : Sylow 2 X := Sylow.ofCard U hUc
  have hxU : ∀ u ∈ (U' : Subgroup X), u * x = x * u := by
    rintro _ ⟨u, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 u.2
  obtain ⟨κ, c, hc⟩ := exists_conj_eq_spRep_of_mulEquiv e hx hxU
  have hperf1 := commutator_centralizer_siegDiag (K := K) (m := m + 2) hK (p := 1) (by omega)
  have h1 : Nat.card (perfectCore (centralizer ({x} : Set X))) =
      Nat.card (perfectCore (centralizer ({spRep (K := K) m .b1} :
        Set (StatedSp (m + 3) K)))) := by
    rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf, spRep_b1_eq_siegDiag,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf1, hcard,
      card_centralizer_siegDiag_eq p 1]
  have hκ : κ = .b1 := eq_of_card_perfectCore_centralizer_eq m hK e (MulEquiv.refl _) hc
    (c' := 1) (z' := spRep (K := K) m .b1) (κ' := .b1) (by simp) h1
  subst hκ
  rw [spRep_b1_eq_siegDiag] at hc
  set π : Equiv.Perm (Fin (m + 3)) := Equiv.swap (Fin.last (m + 2)) 1 with hπ
  have hz := conj_permSp_siegDiag (K := K) π (Fin.last (m + 2)) 1
  rw [hπ, Equiv.swap_apply_left] at hz
  refine ⟨(e.symm (permSp K π))⁻¹ * c, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  calc (e.symm (permSp K π))⁻¹ * c * x * (c⁻¹ * e.symm (permSp K π)) =
      (e.symm (permSp K π))⁻¹ * (c * x * c⁻¹) * e.symm (permSp K π) := by group
    _ = (e.symm (permSp K π))⁻¹ * e.symm (permSp K π * siegDiag K (Fin.last (m + 2)) 1 *
        (permSp K π)⁻¹) * e.symm (permSp K π) := by rw [hc, ← hz, hπ]
    _ = e.symm (siegDiag K (Fin.last (m + 2)) 1) := by
        rw [map_mul, map_mul, map_inv]
        group

end Class

theorem leviTorusSp_last_le_centralizer_siegDiag [CharP K 2] (m : ℕ) :
    leviTorusSp K ({Fin.last m} : Finset (Fin (m + 1))) ≤
      centralizer ({siegDiag K (Fin.last m) 1} : Set (StatedSp (m + 1) K)) := by
  rintro _ ⟨t, ht, rfl⟩
  have h1 : t (Fin.last m) = 1 :=
    ((mem_leviTorusParam.1 ht) (Fin.last m) (Finset.mem_singleton_self _)).2 (by simp)
  rw [mem_centralizer_siegDiag_iff]
  intro r
  rw [mat_diagSp_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    simp [h1]
  · rfl

end CFSG.SeitzReduction.SymplecticPilot
