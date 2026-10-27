module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10AltThreeOrb
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10AltThreeUp
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Upper
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.AltOrbit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Balance.Alt CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem i1910a3_upper_bound_three {M : Type*} [Group M]
    {n : ℕ} (ι : M →* Equiv.Perm (Fin n)) (hι : Function.Injective ι) (innerM : Subgroup M)
    (hinner : alternatingGroup (Fin n) ≤ innerM.map ι)
    (A D H : Subgroup M) (hDA : D ≤ A) (hA : IsElemAbelian 3 A) (hD : IsElemAbelian 3 D)
    (hD2 : Nat.card D = 3 ^ 2) (hH : innerM ≤ H) (hΔ : localDeltaIn 3 H D ≠ ⊥) :
    ∃ r β : ℕ, (r = 2 ∨ r = 4) ∧ 3 ^ 2 + r ≤ n ∧ Nat.card A = 3 ^ β ∧
      3 ^ 2 * β + 2 * r ≤ 2 * n + 3 ^ 2 * (r / 3) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Finite M := Finite.of_injective ι hι
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ localDeltaIn 3 H D, z₀ ≠ 1 := by
    by_contra h
    apply hΔ
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD2
    have : 1 < 3 ^ 2 := by norm_num
    omega
  have hDne' : D.map ι ≠ ⊥ := fun h =>
    hDne ((Subgroup.map_eq_bot_iff_of_injective D hι).1 h)
  have hHalt : alternatingGroup (Fin n) ≤ H.map ι :=
    hinner.trans (Subgroup.map_mono hH)
  have hDexp : ∀ x ∈ D.map ι, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hD.2 x hx, map_one]
  have hN : ∀ d ∈ D.map ι, d ≠ 1 → ∃ N : Subgroup (Equiv.Perm (Fin n)),
      N ≤ H.map ι ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin n))) ∧
      (N.subgroupOf (H.map ι ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin n))))).Normal ∧
      Nat.Coprime 3 (Nat.card N) ∧ ι z₀ ∈ N := by
    rintro _ ⟨d₀, hd₀, rfl⟩ hd1
    have hd₀1 : d₀ ≠ 1 := fun h => hd1 (by rw [h, map_one])
    have hz : z₀ ∈ GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({d₀} : Set M)) := by
      have := (Subgroup.mem_iInf.1 hz₀) d₀
      have := (Subgroup.mem_iInf.1 this) hd₀
      exact (Subgroup.mem_iInf.1 this) hd₀1
    obtain ⟨N, hNle, hNn, hNc, hzN⟩ := exists_normal_coprime_map ι 3 _ z₀ hz
    rw [map_inf_centralizer_singleton ι hι] at hNle hNn
    exact ⟨N, hNle, hNn, hNc, hzN⟩
  have hz1 : ι z₀ ≠ 1 := fun h => hz₀1 (hι (by rw [h, map_one]))
  obtain ⟨F, hF, hFd⟩ := fixedSet_eq_of_delta hp hp2 (D.map ι) (H.map ι) hDexp
    (isMulCommutative_map ι D hD.1) hHalt hDne' (ι z₀) hz1 hN
  obtain ⟨d₀, hd₀D, hd₀⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hDne (Subgroup.eq_bot_iff_forall _ |>.2 hcon)
  have hdι : ι d₀ ∈ D.map ι := ⟨d₀, hd₀D, rfl⟩
  have hdι1 : ι d₀ ≠ 1 := fun h => hd₀ (hι (by rw [h, map_one]))
  obtain ⟨N, hNle, hNn, hNc, hzN⟩ := hN (ι d₀) hdι hdι1
  have hdord : orderOf (ι d₀) = 3 := orderOf_eq_prime (hDexp _ hdι) hdι1
  obtain ⟨hmoved, hcardle⟩ := fixed_card_le_of_primeCore hp hp2 (H.map ι) hHalt (ι d₀) hdord N
    hNle hNn hNc (ι z₀) hzN hz1
  have hFcard : F.card = Fintype.card {x // ι d₀ x = x} := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hFd _ hdι hdι1 x).symm
  have hne3 := i1910a3_card_fixed_ne_three hp hp2 rfl (H.map ι) hHalt (ι d₀) hdord N hNle hNn
    hNc (ι z₀) hzN hz1
  have hr2 : 2 ≤ F.card := by
    obtain ⟨x₁, hx₁⟩ : ∃ x, ι z₀ x ≠ x := by
      by_contra h
      push Not at h
      exact hz1 (Equiv.ext h)
    have h1 : x₁ ∈ F := (hFd _ hdι hdι1 x₁).1 (hmoved x₁ hx₁)
    have h2 : ι z₀ x₁ ∈ F := (hFd _ hdι hdι1 _).1 (hmoved _ (fun h => hx₁ ((ι z₀).injective h)))
    have : 1 < F.card := Finset.one_lt_card.2 ⟨x₁, h1, ι z₀ x₁, h2, fun h => hx₁ h.symm⟩
    omega
  have hr4 : F.card ≤ 4 := by omega
  have hr : F.card = 2 ∨ F.card = 4 := by
    have : F.card ≠ 3 := by rw [hFcard]; exact hne3
    omega
  have hcomm := isMulCommutative_map ι A hA.1
  have hexp : ∀ x ∈ A.map ι, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hA.2 x hx, map_one]
  have hcardD : Nat.card (D.map ι) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hι]; exact hD2
  obtain ⟨h1, β, hβ, h2⟩ := i1910a3_card_le_of_fixedSet hp (by norm_num) F hF (A.map ι) (D.map ι)
    (Subgroup.map_mono hDA) hcomm hexp hcardD hFd
  rw [Fintype.card_fin] at h1 h2
  refine ⟨F.card, β, hr, h1, ?_, h2⟩
  rw [← hβ, Subgroup.card_map_of_injective hι]

end CFSG.HardMathSupport.Solomon.Coordinator
