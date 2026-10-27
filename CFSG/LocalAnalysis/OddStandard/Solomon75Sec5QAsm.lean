module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QCor
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QFin
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QCore
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QMod
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Mirror

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Transport

variable {X : Type} [Group X]

theorem Sec5Comp.map_mulEquiv {n : ℕ} {H A : Subgroup X} (hA : Sec5Comp X n H A) (φ : X ≃* X) :
    Sec5Comp X n (H.map φ.toMonoidHom) (A.map φ.toMonoidHom) := by
  obtain ⟨⟨u, hu⟩, hcov⟩ := hA
  refine ⟨⟨_, hu.map_mulEquiv φ⟩, ?_⟩
  let ψ : ↥A ≃* ↥(A.map φ.toMonoidHom) := Subgroup.equivMapOfInjective A _ φ.injective
  exact isDoubleCoverOfAlt_congr' (QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)) hcov

end Transport

namespace Sec5Data

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem sec5Comp_K0 (h : Sec5Data X n z Z S) (h1 : Sec5One X n Z) :
    Sec5Comp X n (normalizer (Z : Set X)) (K0 X n (normalizer (Z : Set X))) := by
  obtain ⟨A, hA, hKA⟩ := h.exists_unique_comp h1
  rw [hKA]
  exact hA

theorem pairFacts (h : Sec5Data X n z Z S) (hZ : Z = zpowers z) :
    K0 X n (centralizer ({z} : Set X)) ≤ centralizer ({z} : Set X) ∧
      centralizer ({z} : Set X) ≤ normalizer (K0 X n (centralizer ({z} : Set X)) : Set X) ∧
      z ∈ K0 X n (centralizer ({z} : Set X)) ∧
      ∀ r ∈ centralizer ({z} : Set X), orderOf r = 2 →
        CentModOdd (K0 X n (centralizer ({z} : Set X))) r →
        centralizer ({r} : Set X) = oddCoreOf (centralizer ({r} : Set X)) ⊔
          (centralizer ({z} : Set X) ⊓ centralizer ({r} : Set X)) := by
  have hNC : normalizer (Z : Set X) = centralizer ({z} : Set X) := by
    rw [hZ]
    exact normalizer_zpowers_eq_centralizer h.orderOf_z
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact K0_le n _
  · rw [← hNC]
    exact Sec5Data.le_normalizer_K0 X n _
  · rw [← hNC]
    exact h.z_mem_K0
  · intro r hr hr2 hcomm
    rw [← hNC] at hr hcomm ⊢
    exact h.l52.b r hr hr2 hcomm

theorem exists_pairCtx (hF : Solomon75Frac53) (h : Sec5Data X n z Z S) (h1 : Sec5One X n Z)
    (hZ : Z = zpowers z) :
    ∃ (s : X) (M : AhatModel X n (K0 X n (centralizer ({z} : Set X))))
      (M' : AhatModel X n (K0 X n (centralizer ({s} : Set X)))),
      PairCtx X n z s (K0 X n (centralizer ({z} : Set X))) (K0 X n (centralizer ({s} : Set X)))
        M M' := by
  obtain ⟨-, s, x, hsS, hxS, hs2, hsZ, ⟨g, hgs⟩, hxx⟩ := cor56 X n z Z S h h1
  have hz2 := h.orderOf_z
  have hz1 : z ≠ 1 := fun h1' => by rw [h1', orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hs1 : s ≠ 1 := fun h1' => by rw [h1', orderOf_one] at hs2; exact absurd hs2 (by norm_num)
  have hss : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs2, sq] at this
  have hzz : z * z = 1 := h.Z_sq_eq_one h.z_mem
  have hNC : normalizer (Z : Set X) = centralizer ({z} : Set X) := by
    rw [hZ]
    exact normalizer_zpowers_eq_centralizer hz2
  have hsN : s ∈ normalizer (Z : Set X) := Subgroup.map_subtype_le _ hsS
  have hsC : s ∈ centralizer ({z} : Set X) := hNC ▸ hsN
  have hxC : x ∈ centralizer ({z} : Set X) := hNC ▸ Subgroup.map_subtype_le _ hxS
  have hzs : z * s = s * z := (Subgroup.mem_centralizer_singleton_iff.1 hsC).symm
  have hzC : z ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hzs
  obtain ⟨S', h'⟩ := h.mirror g
  rw [hgs] at h'
  have hφz : (MulAut.conj g⁻¹).toMonoidHom z = s := by simp [hgs]
  have hZ' : Z.map (MulAut.conj g⁻¹).toMonoidHom = zpowers s := by
    rw [hZ, MonoidHom.map_zpowers, hφz]
  have hNC' : normalizer ((Z.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup X) : Set X) =
      centralizer ({s} : Set X) := by
    rw [hZ']
    exact normalizer_zpowers_eq_centralizer hs2
  obtain ⟨hAz, hNz, hzA, h52⟩ := h.pairFacts hZ
  obtain ⟨hAs, hNs, hsA, h52'⟩ := h'.pairFacts hZ'
  have hcomp : Sec5Comp X n (centralizer ({z} : Set X)) (K0 X n (centralizer ({z} : Set X))) := by
    rw [← hNC]
    exact h.sec5Comp_K0 h1
  have hcomp' : Sec5Comp X n (centralizer ({s} : Set X)) (K0 X n (centralizer ({s} : Set X))) := by
    have := (h.sec5Comp_K0 h1).map_mulEquiv (MulAut.conj g⁻¹)
    rw [K0_map, ← normalizer_map_mulEquiv] at this
    rw [← hNC']
    exact this
  have hgz : g * s * g⁻¹ = z := by rw [← hgs]; group
  have hinv : IsSec5Inv X Z s :=
    ⟨hsN, hsZ, hss, g⁻¹, by rw [inv_inv, hgz]; exact h.z_mem, by rw [inv_inv, hgz]; exact hz1⟩
  have hinv' : IsSec5Inv X (Z.map (MulAut.conj g⁻¹).toMonoidHom) z :=
    ⟨by rw [hNC']; exact hzC, by
      rw [hZ']
      intro hmem
      rcases (mem_zpowers_iff_of_orderOf_two hs2).1 hmem with h0 | h0
      · exact hz1 h0
      · exact hsZ (h0 ▸ h.z_mem), hzz, g, by rw [hgs, hZ']; exact Subgroup.mem_zpowers s,
        by rw [hgs]; exact hs1⟩
  let M : AhatModel X n (K0 X n (centralizer ({z} : Set X))) := AhatModel.ofCover hcomp.2
  let M' : AhatModel X n (K0 X n (centralizer ({s} : Set X))) := AhatModel.ofCover hcomp'.2
  have hn : 8 ≤ n := h.maxdeg.1
  have hFz := ((hF X n z Z S h s hinv).1 (K0 X n (centralizer ({z} : Set X)))
    (by rw [hNC]; exact hcomp) (hNz hsC) M)
  have hFs := ((hF X n s _ S' h' z hinv').1 (K0 X n (centralizer ({s} : Set X)))
    (by rw [hNC']; exact hcomp') (hNs hzC) M')
  have hsgn : sign (M.permX s) = 1 := by
    have hxN : x ∈ normalizer (K0 X n (centralizer ({z} : Set X)) : Set X) := hNz hxC
    have : M.permX s = M.permX x * M.permX x := by
      rw [← M.permX_mul hn hxN hxN, hxx]
    rw [this, Perm.sign_mul]
    exact Int.units_mul_self _
  obtain ⟨x₂, -, hx₂s, hx₂z⟩ := h.exists_sq_eq_z h1 hsN hss
  have hx₂C : x₂ ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hx₂s
  have hsgn' : sign (M'.permX z) = 1 := by
    have hxN : x₂ ∈ normalizer (K0 X n (centralizer ({s} : Set X)) : Set X) := hNs hx₂C
    have : M'.permX z = M'.permX x₂ * M'.permX x₂ := by
      rw [← M'.permX_mul hn hxN hxN, hx₂z]
    rw [this, Perm.sign_mul]
    exact Int.units_mul_self _
  refine ⟨s, M, M', ?_⟩
  exact
    { hn := hn, hz := hz2, hs := hs2, hzs := hzs, hzA := hzA, hsA := hsA, hAz := hAz, hNz := hNz
      hAs := hAs, hNs := hNs
      hz52 := fun r hr hr2 hc => h52 r hr hr2 hc
      hs52 := fun r hr hr2 hc => h52' r hr hr2 hc
      hfix := by rw [M.permX_of_mem (hNz hsC)]; exact hFz.1
      hfix' := by rw [M'.permX_of_mem (hNs hzC)]; exact hFs.1
      htr := by rw [M.permX_of_mem (hNz hsC)]; exact hFz.2
      htr' := by rw [M'.permX_of_mem (hNs hzC)]; exact hFs.2
      hsgn := hsgn
      hsgn' := hsgn' }

end Sec5Data

theorem lemma57 (hF : Solomon75Frac53) (hfc : ∀ (n : ℕ) [NeZero n], 8 ≤ n → n ≤ 11 → FCAll n) :
    Solomon75Lemma57 := by
  intro X _ _ n z Z S h h1 hZ
  obtain ⟨s, M, M', hctx⟩ := h.exists_pairCtx hF h1 hZ
  by_cases hn12 : 12 ≤ n
  · have hP : hctx.swap.RCore := hctx.swap.twoElts_of_ge_six
      (six_le_transCount hctx.sq_permX_z hn12 hctx.hfix' hctx.hsgn')
    exact hctx.Qz_eq_of_RCore hP
  · have hn11 : n ≤ 11 := by omega
    have : NeZero n := ⟨by have := hctx.hn; omega⟩
    obtain ⟨M₁, M₁', hctx₁, hM₁, hM₁'⟩ := hctx.exists_sig0 hn11
    have hP : hctx₁.swap.RCore := hctx₁.swap.rcore_of_four hn11 hM₁' hM₁
      (hfc n hctx.hn hn11)
    exact hctx₁.Qz_eq_of_RCore hP

end CFSG.OddStandard.Solomon75
