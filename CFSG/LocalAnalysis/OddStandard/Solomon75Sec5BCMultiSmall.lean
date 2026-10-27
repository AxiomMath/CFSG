module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracZero
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiPiece
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiMirror
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiSwap
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiL54

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Small

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

private theorem bcdSmall_sec5Comp_map {H A : Subgroup X} (hA : Sec5Comp X n H A) (φ : X ≃* X) :
    Sec5Comp X n (H.map φ.toMonoidHom) (A.map φ.toMonoidHom) := by
  obtain ⟨⟨u, hu⟩, hcov⟩ := hA
  refine ⟨⟨_, hu.map_mulEquiv φ⟩, ?_⟩
  let ψ : ↥A ≃* ↥(A.map φ.toMonoidHom) := Subgroup.equivMapOfInjective A _ φ.injective
  exact isDoubleCoverOfAlt_congr' (QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)) hcov

theorem frac53_multi_le11 (h : Sec5Data X n z Z S) (hk : ¬ Sec5One X n Z) (hn : n ≤ 11) {s : X}
    (hs : IsSec5Inv X Z s) {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hsA : s ∈ normalizer (A : Set X)) (M : AhatModel X n A)
    (hσ : fixCount (M.perm s hsA) = 4 ∨
      (transCount (M.perm s hsA) = 3 ∧ fixCount (M.perm s hsA) ≤ 3)) : False := by
  classical
  have hn8 : 8 ≤ n := h.maxdeg.1
  have hk' : ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂ := by
    by_contra hcon
    exact hk fun A₁ A₂ hA₁ hA₂ => by
      by_contra hne
      exact hcon ⟨A₁, A₂, hA₁, hA₂, hne⟩
  obtain ⟨u, hu, huZ, hu1, hus⟩ := h.exists_witness_Z hs hA hsA
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have hs2 : s * s = 1 := hs.sq
  have hsu : s * u = u * s := hus.symm
  obtain ⟨L, E, hL, htL, M', huE, hEAL, hEcov, htE, hperm⟩ :=
    exists_Lu_model h hA huZ hu1 hu hsA hsu M
  have hbad : fixCount (M'.perm s htL) = 4 ∨
      (transCount (M'.perm s htL) = 3 ∧ fixCount (M'.perm s htL) ≤ 3) := by
    rw [hperm]; exact hσ
  have hEL : E ≤ L := fun x hx => (hEAL hx).2
  obtain ⟨Q, hQE, hQ2, hQ8, huQ, hQpow, -, -, hQlp, -⟩ :=
    exists_sl23_piece hn8 hu2 hu1 hs2 hsu hL.isPCompIn hEL huE hEcov htL htE M' hbad
  have hQs : Q ≤ centralizer ({s} : Set X) := hQE.trans inf_le_right
  have hQn : ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → Q ≤ normalizer (B : Set X) :=
    fun B hB => le_normalizer_of_le_lPlus_inf hu2 hus hQlp hB.isPCompIn
  obtain ⟨g, Zs, S₁, hZs, hQN, hQC, hS₁, hinv, hnorm, hdata⟩ :=
    mirror_package h hs huZ hu1 hus hQs hQ2 hQ8 huQ hQpow hQn (by omega)
  have hsnt : ¬ CentModOdd L s := by
    intro hc
    have h1 := (M'.perm_eq_one_iff hn8 htL).2 hc
    have h8 : fixCount (1 : Perm (Fin n)) = n := by unfold fixCount; simp
    have h0 : transCount (1 : Perm (Fin n)) = 0 := by
      unfold transCount; simp
    rw [h1] at hbad
    rcases hbad with h4 | ⟨h3, -⟩
    · omega
    · omega
  have hsw : ∀ L', Sec5Comp X n (centralizer ({u} : Set X)) L' → s ∈ normalizer (L' : Set X) :=
    step5_swap h hs huZ hu1 hus (fun B hB => hQn B hB huQ) hL htL hsnt
  obtain ⟨A₁, A₂, hA₁, hA₂, hne⟩ := hk'
  have hφ : (normalizer ((Z.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X)) =
      (normalizer (Z : Set X)).map (MulAut.conj g).toMonoidHom := normalizer_map_mulEquiv _ Z
  have hA₁' : Sec5Comp X n (normalizer (Zs : Set X)) (A₁.map (MulAut.conj g).toMonoidHom) := by
    rw [hZs, hφ]; exact bcdSmall_sec5Comp_map hA₁ _
  have hA₂' : Sec5Comp X n (normalizer (Zs : Set X)) (A₂.map (MulAut.conj g).toMonoidHom) := by
    rw [hZs, hφ]; exact bcdSmall_sec5Comp_map hA₂ _
  have hne' : A₁.map (MulAut.conj g).toMonoidHom ≠ A₂.map (MulAut.conj g).toMonoidHom :=
    fun e => hne (Subgroup.map_injective (MulAut.conj g).injective e)
  have hk_m : ∃ B₁ B₂ : Subgroup X, Sec5Comp X n (normalizer (Zs : Set X)) B₁ ∧
      Sec5Comp X n (normalizer (Zs : Set X)) B₂ ∧ B₁ ≠ B₂ :=
    ⟨_, _, hA₁', hA₂', hne'⟩
  have hnt : ∀ A', Sec5Comp X n (normalizer (Zs : Set X)) A' → ¬ CentModOdd A' u := by
    intro A' hA' hc
    have hu' := hnorm A' hA'
    have h1 := (AhatModel.ofCover hA'.2).perm_eq_one_iff hn8 hu' |>.2 hc
    exact (hdata A' hA' hu' (AhatModel.ofCover hA'.2)).1 h1
  have hZt : Zs ≤ centralizer ({u} : Set X) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 (hQC huQ) w hw
  have hSS : Sec5S X n s Zs S₁ u :=
    { data := hS₁
      inv := hinv
      norm := hnorm
      frac := fun A' hA' hu' M'' => by
        obtain ⟨-, hf, ht⟩ := hdata A' hA' hu' M''
        exact ⟨by omega, by omega⟩
      l54 := fun A' hA' r hr hr1 hr2 hrt =>
        ⟨l54_a_prime hS₁ hk_m hinv hnorm hnt hA' hr hr1 hr2 hrt,
          l54_b_prime hS₁ hk_m hinv hZt hsw hA' hr hr1 hr2 hrt⟩ }
  exact hSS.small_false hn hA₁' hA₂' hne'

end Small

end CFSG.OddStandard.Solomon75
