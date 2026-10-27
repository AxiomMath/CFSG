module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.RankThree.LocalRank

variable {G : Type*} [Group G]

@[expose] noncomputable def thetaOf (c : G) : Subgroup G :=
  (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))).map
    (Subgroup.centralizer ({c} : Set G)).subtype

theorem thetaOf_le (c : G) : thetaOf c ≤ Subgroup.centralizer ({c} : Set G) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem thetaOf_conj {c x : G} (hx : x ∈ Subgroup.centralizer ({c} : Set G)) {n : G}
    (hn : n ∈ thetaOf c) : x * n * x⁻¹ ∈ thetaOf c := by
  obtain ⟨y, hy, rfl⟩ := hn
  have hN : (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))).Normal :=
    aschbacherSolvableCore_normal 3 _
  let x' : Subgroup.centralizer ({c} : Set G) := ⟨x, hx⟩
  exact ⟨x' * y * x'⁻¹, hN.conj_mem y hy x', rfl⟩

theorem thetaOf_isSolvable [Finite G] (c : G) : Group.IsSolvable (thetaOf c) := by
  have hs := (solvable_prime_complement_core_characterization
    (H := Subgroup.centralizer ({c} : Set G)) Nat.prime_three).1
  exact Group.isSolvable_of_surjective
    ((Subgroup.centralizer ({c} : Set G)).subtype.subgroupMap_surjective
      (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))))

theorem thetaOf_not_three_dvd [Finite G] (c : G) : ¬ 3 ∣ Nat.card (thetaOf c) := by
  have h := (solvable_prime_complement_core_characterization
    (H := Subgroup.centralizer ({c} : Set G)) Nat.prime_three).2.2.1
  rwa [thetaOf, Subgroup.card_map_of_injective (Subgroup.centralizer ({c} : Set G)).subtype_injective]

theorem theta_comm_core [Finite G] {z c : G} (hz : z * z = 1) (hco : orderOf c = 3) (hcz : c * z = z * c)
    (Kg : Subgroup G)
    (hK : ∀ k ∈ Kg, k * c = c * k → ∃ e : Bool, ∃ i < 3, k = (if e then z else 1) * c ^ i)
    (hP : ∀ S : Subgroup G,
      S ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) →
      (∀ l ∈ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({c} : Set G),
        ∀ s ∈ S, l * s * l⁻¹ ∈ S) →
      Group.IsSolvable S → S ≤ Kg)
    {n : G} (hn : n ∈ thetaOf c) (hnz : n * z = z * n) : n = 1 ∨ n = z := by
  set L := Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) with hL
  set M := Subgroup.centralizer ({z} : Set G) with hM
  have hSL : thetaOf c ⊓ M ≤ L := by
    intro s hs
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hs).2, thetaOf_le c (Subgroup.mem_inf.1 hs).1⟩
  have hSn : ∀ l ∈ L, ∀ s ∈ thetaOf c ⊓ M, l * s * l⁻¹ ∈ thetaOf c ⊓ M := by
    intro l hl s hs
    have hlM : l ∈ M := (Subgroup.mem_inf.1 hl).1
    exact Subgroup.mem_inf.2 ⟨thetaOf_conj (Subgroup.mem_inf.1 hl).2 (Subgroup.mem_inf.1 hs).1,
      M.mul_mem (M.mul_mem hlM (Subgroup.mem_inf.1 hs).2) (M.inv_mem hlM)⟩
  have hSs : Group.IsSolvable (thetaOf c ⊓ M : Subgroup G) := by
    have := thetaOf_isSolvable c
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : thetaOf c ⊓ M ≤ thetaOf c))
      (Subgroup.inclusion_injective _)
  have hnM : n ∈ M := Subgroup.mem_centralizer_singleton_iff.2 hnz
  have hnK : n ∈ Kg := hP _ hSL hSn hSs (Subgroup.mem_inf.2 ⟨hn, hnM⟩)
  have hnc : n * c = c * n := Subgroup.mem_centralizer_singleton_iff.1 (thetaOf_le c hn)
  obtain ⟨e, i, hi, rfl⟩ := hK n hnK hnc
  have hcz' : Commute c z := hcz
  have h3 : c ^ 3 = 1 := by rw [← hco]; exact pow_orderOf_eq_one c
  have hx : (if e then z else 1) = 1 ∨ (if e then z else 1) = z := by
    cases e
    · left; rfl
    · right; rfl
  have hi0 : i = 0 := by
    by_contra hne
    set x : G := if e then z else 1 with hxdef
    have hcx : Commute x (c ^ i) := by
      rcases hx with h | h
      · rw [h]; exact Commute.one_left _
      · rw [h]; exact (Commute.pow_left hcz' i).symm
    have hx4 : x ^ 4 = 1 := by
      rcases hx with h | h
      · rw [h]; exact one_pow 4
      · rw [h]
        calc z ^ 4 = (z * z) * (z * z) := by
              rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one, mul_assoc]
          _ = 1 := by rw [hz, one_mul]
    have hc4 : (c ^ i) ^ 4 = c ^ i := by
      rw [← pow_mul, show i * 4 = i + 3 * i by ring, pow_add, pow_mul, h3, one_pow, mul_one]
    have hn4 : (x * c ^ i) ^ 4 = c ^ i := by rw [hcx.mul_pow, hx4, one_mul, hc4]
    have hmem : c ^ i ∈ thetaOf c := hn4 ▸ (thetaOf c).pow_mem hn 4
    have hcop : Nat.Coprime (orderOf c) i := by
      rw [hco]
      interval_cases i
      · exact absurd rfl hne
      · decide
      · decide
    have hdvd := Subgroup.orderOf_dvd_natCard (thetaOf c) hmem
    rw [hcop.orderOf_pow, hco] at hdvd
    exact thetaOf_not_three_dvd c hdvd
  subst hi0
  rcases hx with h | h
  · left; rw [pow_zero, mul_one, h]
  · right; rw [pow_zero, mul_one, h]

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
