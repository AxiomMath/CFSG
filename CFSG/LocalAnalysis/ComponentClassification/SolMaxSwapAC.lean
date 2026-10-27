module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapAB

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem card_support_rho_of_swap
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {x : X}
    (hxJ : x ∈ J) (hxN : x ∈ normalizer (M : Set X)) :
    (ρ ⟨x, hxN⟩).support.card = (coreImage e hxJ).support.card := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  have htH := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hMH hMpc hne hJM
  have hJK := S.not_le_coreActionKernel_of_swap hCH hMH hMpc hne hJM θ
  have hperf : ⁅J, J⁆ = J :=
    UnbalancedCorr.commutator_eq_of_isPComponent S.pair.1.2.1 S.pair.1.2.2.1
  have hQ : Nat.card (alternatingGroup (Fin n)) ≤ n.factorial / 2 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨hsurj, hO⟩ := hρ.image_eq_of_le hJN (by omega) e hperf hJK hQ
    (fun y hy => IsPermAction.mem_alternatingGroup_of_perfect hJN hperf hy)
  let f : ↥J →* alternatingGroup (Fin n) :=
    (ρ.comp (Subgroup.inclusion hJN)).codRestrict (alternatingGroup (Fin n))
      (fun z => IsPermAction.mem_alternatingGroup_of_perfect hJN hperf z.2)
  have hfO : pPrimeCore 2 ↥J ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hO z z.2 ⟨z, hz, rfl⟩
  let f' : ↥J ⧸ pPrimeCore 2 ↥J →* alternatingGroup (Fin n) := QuotientGroup.lift _ f hfO
  have hf' : ∀ (z : X) (hz : z ∈ J), ((f' ((⟨z, hz⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) :
      alternatingGroup (Fin n)) : Perm (Fin n)) = ρ ⟨z, hJN hz⟩ := fun z hz => rfl
  let ψ : alternatingGroup (Fin n) →* alternatingGroup (Fin n) := f'.comp e.symm.toMonoidHom
  have hψe : ∀ (z : X) (hz : z ∈ J), ((ψ (e ((⟨z, hz⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) :
      alternatingGroup (Fin n)) : Perm (Fin n)) = ρ ⟨z, hJN hz⟩ := by
    intro z hz
    change ((f' (e.symm (e _)) : alternatingGroup (Fin n)) : Perm (Fin n)) = _
    rw [MulEquiv.symm_apply_apply]
    exact hf' z hz
  have hψs : Function.Surjective ψ := by
    intro b
    obtain ⟨z, hz, hzb⟩ := hsurj b b.2
    exact ⟨e ((⟨z, hz⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J), Subtype.ext ((hψe z hz).trans hzb)⟩
  have hψb : Function.Bijective ψ := ⟨Finite.injective_iff_surjective.mpr hψs, hψs⟩
  have h1 := card_support_mulEquiv_alt (Fintype.card_fin n) (Fintype.card_fin n) (by omega)
    (MulEquiv.ofBijective ψ hψb) (e ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J))
  rw [MulEquiv.ofBijective_apply, hψe x hxJ] at h1
  exact h1

theorem mem_normalizer_of_odd_swap
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {o : X} (hoH : o ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hodd : Odd (orderOf o)) : o ∈ normalizer (M : Set X) := by
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hcomp : ∀ g ∈ H, M.map (MulAut.conj g).toMonoidHom = M ∨
      M.map (MulAut.conj g).toMonoidHom = M.map (MulAut.conj t).toMonoidHom := fun g hg =>
    S.eq_or_eq_of_isPComponent_swap hCH hMH hMpc hne hJM hsmall
      (isPComponent_conj hMH hMpc hg).1 (isPComponent_conj hMH hMpc hg).2
  have ho2 : M.map (MulAut.conj (o * o)).toMonoidHom = M := by
    rcases hcomp o hoH with h | h
    · rw [map_conj_mul, h, h]
    · have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
      rcases hcomp (o * t) (mul_mem hoH htH) with h' | h'
      · rw [map_conj_mul, h, ← map_conj_mul]
        exact h'
      · exfalso
        apply hne
        have h1 : (M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj o).toMonoidHom =
            M.map (MulAut.conj o).toMonoidHom := by rw [← map_conj_mul, h', h]
        exact (map_injective (MulAut.conj o).injective) h1
  obtain ⟨k, hk⟩ := hodd
  have hoo : o = (o * o) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hN : o * o ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.mpr ho2
  rw [hoo]
  exact pow_mem hN _

end Sig36

end CFSG.ComponentClassification.SolMax
