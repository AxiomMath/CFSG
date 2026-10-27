module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9Defs

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

section Layer0

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X}

theorem Setting.J_le_Hn (hs : Setting t J n e E D M) : J ≤ Hn E := by
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, -⟩ := isPComponent_conj hs.le hs.pc htH
  exact hs.diag.trans (sup_le hs.le hMtH)

theorem Setting.completion_eq_of_four (hs : Setting t J n e E D M) {E' : Subgroup X}
    {D' : Finset (Fin n)} (hE'J : E' ≤ J)
    (hE' : Nonempty (E' ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hD' : D'.card = 4) (hs' : ∀ x : J, (x : X) ∈ E' → ∀ ω ∉ D',
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) :
    Sol78.signalizerCompletion E' E' = Sol78.signalizerCompletion E E := by
  have S := hs.sig
  obtain ⟨hE4, hE2⟩ := card_sq_of_klein S.klein
  obtain ⟨hE'4, hE'2⟩ := card_sq_of_klein hE'
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE2 x hx
  have hE'sq : ∀ x ∈ E', x * x = 1 := fun x hx => by rw [← sq]; exact hE'2 x hx
  obtain ⟨j, hj, hjE⟩ := exists_conj_four_subgroup (by have := S.nine_le; omega) e S.le hE'J
    hE4 hE'4 hEsq hE'sq S.card hD' S.supp hs'
  have h1 := signalizerCompletion_map_aut (MulAut.conj j) E E
  rw [hjE] at h1
  rw [← h1]
  exact mem_normalizer_iff_map_conj_eq.mp (hs.J_le_Hn hj)

theorem Setting.core_le_Hn_of_four (hs : Setting t J n e E D M) {E' : Subgroup X}
    {D' : Finset (Fin n)} (hE'J : E' ≤ J)
    (hE' : Nonempty (E' ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hD' : D'.card = 4) (hs' : ∀ x : J, (x : X) ∈ E' → ∀ ω ∉ D',
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω)
    {x : X} (hxE' : x ∈ E') (hx1 : x ≠ 1) : core (centralizer ({x} : Set X)) ≤ Hn E := by
  have h1 := (hs.sig.ofFour hE'J hE' hD' hs').oddCore_le_of_mem_E hxE' hx1
  rwa [hs.completion_eq_of_four hE'J hE' hD' hs'] at h1

theorem Setting.isKGroupCat_centralizer (hs : Setting t J n e E D M) {x : X} (hx1 : x ≠ 1) :
    SectionRank.IsKGroupCat ↥(centralizer ({x} : Set X)) :=
  UnbalancedCorr.isKGroupCat_of_ne_top hs.sig.kProper
    (centralizer_ne_top_of_ne_one hs.sig.nonab hx1)

theorem Setting.orderOf_t (hs : Setting t J n e E D M) : orderOf t = 2 := hs.sig.pair.1.1

theorem Setting.false_of_pump_le (hs : Setting t J n e E D M) (hn : n = 9) {f : X}
    (hfJ : f ∈ J) (hf : orderOf f = 2) {N : Subgroup X} (hNC : N ≤ centralizer ({f} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({f} : Set X)))) (hNt : conjBy N t = N)
    (hNH : N ≤ Hn E) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtt : (conjBy M t).map (MulAut.conj t).toMonoidHom = M :=
    SwapN9.map_conj_map_conj_self M ht2
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hNMM : N ≤ M ⊓ conjBy M t := by
    rcases S.le_or_le_of_isPComponent_swap hs.cent hs.le hs.pc hs.swap hs.diag hs.small hfJ hf
        hNH hNC hNpc with h | h
    · refine le_inf h ?_
      rw [← hNt]
      exact map_mono h
    · refine le_inf ?_ h
      rw [← hNt, ← hMtt]
      exact map_mono h
  have hNO : N ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
    mem_core_of_mem_coreActionKernel hρ (by omega) (hNMM hz).1 (hMtK (hNMM hz).2)
  have h1 := card_dvd_of_le hNO
  rw [card_map_of_injective M.subtype_injective] at h1
  have h2 := two_dvd_card_of_isPComponent_in hNC hNpc
  have h3 := Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  exact absurd h3 (by
    rw [Nat.coprime_two_left]
    exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2))

end Layer0

section Exact

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M F : Subgroup X} {DF : Finset (Fin n)} {f : X} {L N : Subgroup X}

theorem ExactData.core_le_Hn (hs : Setting t J n e E D M) (hx : ExactData t J n e F DF f L N) :
    core (centralizer ({f} : Set X)) ≤ Hn E :=
  hs.core_le_Hn_of_four hx.FJ hx.Fk hx.DFc hx.Fs hx.fF hx.f1

end Exact

end CFSG.ComponentClassification.SolMax.SwapP2
