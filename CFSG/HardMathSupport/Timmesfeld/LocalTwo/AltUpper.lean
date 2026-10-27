module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Upper
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.AltOrbit

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Balance.Alt

theorem upper_bound_of_delta_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type*} [Group M]
    {n : ℕ} (ι : M →* Equiv.Perm (Fin n)) (hι : Function.Injective ι) (innerM : Subgroup M)
    (hinner : alternatingGroup (Fin n) ≤ innerM.map ι)
    (A D H : Subgroup M) (hDA : D ≤ A) (hA : IsElemAbelian p A) (hD : IsElemAbelian p D)
    (hD2 : Nat.card D = p ^ 2) (hH : innerM ≤ H) (hΔ : localDeltaIn p H D ≠ ⊥) :
    p ^ 2 ≤ n ∧ ∃ β : ℕ, Nat.card A = p ^ β ∧ p ^ 2 * β ≤ 2 * n + p ^ 2 := by
  have : Finite M := Finite.of_injective ι hι
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ localDeltaIn p H D, z₀ ≠ 1 := by
    by_contra h
    apply hΔ
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD2
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hDne' : D.map ι ≠ ⊥ := fun h =>
    hDne ((Subgroup.map_eq_bot_iff_of_injective D hι).1 h)
  have hHalt : alternatingGroup (Fin n) ≤ H.map ι :=
    hinner.trans (Subgroup.map_mono hH)
  obtain ⟨F, hF, hFd⟩ := fixedSet_eq_of_delta hp hp2 (D.map ι) (H.map ι)
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hD.2 x hx, map_one])
    (isMulCommutative_map ι D hD.1) hHalt hDne' (ι z₀) (fun h => hz₀1 (hι (by rw [h, map_one])))
    (by
      rintro _ ⟨d₀, hd₀, rfl⟩ hd1
      have hd₀1 : d₀ ≠ 1 := fun h => hd1 (by rw [h, map_one])
      have hz : z₀ ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d₀} : Set M)) := by
        have := (Subgroup.mem_iInf.1 hz₀) d₀
        have := (Subgroup.mem_iInf.1 this) hd₀
        exact (Subgroup.mem_iInf.1 this) hd₀1
      obtain ⟨N, hNle, hNn, hNc, hzN⟩ := exists_normal_coprime_map ι p _ z₀ hz
      rw [map_inf_centralizer_singleton ι hι] at hNle hNn
      exact ⟨N, hNle, hNn, hNc, hzN⟩)
  have hcomm := isMulCommutative_map ι A hA.1
  have hexp : ∀ x ∈ A.map ι, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hA.2 x hx, map_one]
  have hcardD : Nat.card (D.map ι) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hι]; exact hD2
  obtain ⟨h1, β, hβ, h2⟩ := card_le_of_fixedSet_two hp hp3 F hF (A.map ι) (D.map ι)
    (Subgroup.map_mono hDA) hcomm hexp hcardD hFd
  rw [Fintype.card_fin] at h1 h2
  refine ⟨h1, β, ?_, h2⟩
  rw [← hβ, Subgroup.card_map_of_injective hι]

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
