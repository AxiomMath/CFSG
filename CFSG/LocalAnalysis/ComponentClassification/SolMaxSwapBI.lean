module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}

theorem false_of_diagonal_of_le (hs : Setting t J n e E D M)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    {N : Subgroup X} (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hcov : fixA M e₀ r ≤ N ⊔ conjBy N e₀) (hdiag : conjBy N e₀ ≠ N) (hNH : N ≤ Hn E) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  set Ar := fixA M e₀ r with hArdef
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  obtain ⟨hNxC, hNxpc⟩ := isPComponent_conj hNC hNpc he₀r
  have hNxK : conjBy N e₀ ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hNxC hNpc hNxpc (Ne.symm hdiag)
  have hNKx : N ≤ UnbalancedLayer.coreActionKernel (conjBy N e₀) :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNxC hNC hNxpc hNpc hdiag
  have hArM : Ar ≤ M :=
    ((GSLit.fixedLayer_le_inf _ (zpowers r)).trans inf_le_left).trans
      ((GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left)
  have hArperf : ⁅Ar, Ar⁆ = Ar := UnbalancedCorr.commutator_eq_of_isPComponent hArle hArpc
  obtain ⟨-, hArres, hArq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Ar _ hArle).mp hArpc
  have hArnt := LocalCores.isQuasisimple_nontrivial hArq
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hrH : r ∈ Hn E := hMtH hd.rM
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M (Hn E) hs.le).mp hs.pc).2.2
  have hCr : centralizer ((zpowers r : Subgroup X) : Set X) = centralizer ({r} : Set X) :=
    centralizer_zpowers_eq' r
  have hMrpc := GSLit.fixedLayer_isPComponent hs.le hs.pc.choose_spec.2.1 (zpowers_le.mpr hrH)
    (zpowers_le.mpr hrK) hR2 hMq
  rw [hCr] at hMrpc
  have hMrle := GSLit.fixedLayer_le_inf M (zpowers r)
  rw [hCr] at hMrle
  have hMrY : GSLit.fixedLayer M (zpowers r) ≤ Hn E ⊓ centralizer ({r} : Set X) :=
    le_inf ((hMrle.trans inf_le_left).trans hs.le) (hMrle.trans inf_le_right)
  have hArMC : Ar ≤ M ⊓ centralizer ((zpowers r : Subgroup X) : Set X) := by
    rw [hCr]
    exact le_inf hArM (hArle.trans inf_le_left)
  have hArMr : Ar ≤ GSLit.fixedLayer M (zpowers r) :=
    le_fixedLayer_of_primeResidual hMq (zpowers_le.mpr hrK) hR2 hArMC hArres
  have he₀H' : e₀ ∈ Hn E := he₀H (mem_centralizer_singleton_iff.mpr rfl)
  have hNxH : conjBy N e₀ ≤ Hn E := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem he₀H' (hNH hz)) (inv_mem he₀H')
  have hNY : N ≤ Hn E ⊓ centralizer ({r} : Set X) := le_inf hNH hNC
  have hNxY : conjBy N e₀ ≤ Hn E ⊓ centralizer ({r} : Set X) := le_inf hNxH hNxC
  have hNpc' := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hNY inf_le_right hNpc
  have hNxpc' := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hNxY inf_le_right hNxpc
  have hAre : Ar.map (MulAut.conj e₀).toMonoidHom = Ar :=
    map_conj_eq_of_le_centralizer (hArle.trans inf_le_right)
  have hcc : (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom = N :=
    conjBy_conjBy_of_mul_self N he₀2
  by_cases h₁ : GSLit.fixedLayer M (zpowers r) = N
  · have hArN' : Ar ≤ N := h₁ ▸ hArMr
    have hArNx : Ar ≤ conjBy N e₀ := by
      rw [← hAre]
      exact map_mono hArN'
    exact false_of_le_coreActionKernel hArperf hArnt hArN' (hArNx.trans hNxK)
  by_cases h₂ : GSLit.fixedLayer M (zpowers r) = conjBy N e₀
  · have hArNx : Ar ≤ conjBy N e₀ := h₂ ▸ hArMr
    have hArN' : Ar ≤ N := by
      have h1 : Ar.map (MulAut.conj e₀).toMonoidHom ≤
          (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom := map_mono hArNx
      rwa [hAre, hcc] at h1
    exact false_of_le_coreActionKernel hArperf hArnt hArNx (hArN'.trans hNKx)
  have hK1 : N ≤ UnbalancedLayer.coreActionKernel (GSLit.fixedLayer M (zpowers r)) :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMrY hNY hMrpc hNpc' h₁
  have hK2 : conjBy N e₀ ≤ UnbalancedLayer.coreActionKernel (GSLit.fixedLayer M (zpowers r)) :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMrY hNxY hMrpc hNxpc' h₂
  exact false_of_le_coreActionKernel hArperf hArnt hArMr (hcov.trans (sup_le hK1 hK2))

theorem false_of_diagonalZ (hs : Setting t J n e E D M) (hn : n = 11)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (hOr : core (centralizer ({r} : Set X)) ≤ Hn E)
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E)
    (χr : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin 7))
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    {N : Subgroup X} (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hcov : fixA M e₀ r ≤ N ⊔ conjBy N e₀) (hdiag : conjBy N e₀ ≠ N)
    (ψN : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 7)) : False :=
  false_of_diagonal_of_le hs hd he₀H hArle hArpc hNC hNpc hcov hdiag
    (le_of_diagonalZ hs hn hd he₀H hOr hFH χr hArle hArpc hNC hNpc hcov hdiag ψN)

end SwapP2

end CFSG.ComponentClassification.SolMax
