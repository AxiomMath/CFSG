module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CA

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

section Layer0

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X}

theorem Setting.exists_conj_mul (hs : Setting t J n e E D M) {u : X} (huJ : u ∈ J)
    (hu : u * u = 1) : ∃ h ∈ Hn E, u * t = h * t * h⁻¹ := by
  have S := hs.sig
  have hn9 := S.nine_le
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    have := S.pair.1.1
    rw [h, orderOf_one] at this
    omega
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hMKt : M ≤ UnbalancedLayer.coreActionKernel (conjBy M t) :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMtH hs.le hMtpc hs.pc hs.swap
  have hV : Odd (Nat.card ↥(M ⊓ conjBy M t)) := by
    have hle : M ⊓ conjBy M t ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
      mem_core_of_mem_coreActionKernel hρ (by omega) (mem_inf.mp hz).1
        (hMtK (mem_inf.mp hz).2)
    have h1 : Odd (Nat.card ↥((pPrimeCore 2 ↥M).map M.subtype)) := by
      rw [card_map_of_injective M.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact h1.of_dvd_nat (card_dvd_of_le hle)
  have hJN : J ≤ normalizer (M : Set X) :=
    le_normalizer_of_swap htH hs.le hs.pc hs.swap hs.diag
  have hut : u * t = t * u := mem_centralizer_singleton_iff.mp (S.pair.1.2.1 huJ)
  have huNt : u ∈ normalizer (conjBy M t : Set X) := by
    have hcomm : t * u * t⁻¹ = u := by rw [← hut]; group
    have h1 : u ∈ (normalizer (M : Set X)).map (MulAut.conj t).toMonoidHom :=
      ⟨u, hJN huJ, by simpa using hcomm⟩
    exact le_normalizer_map _ h1
  have hv1 : t * u ≠ 1 := by
    intro h
    apply S.t_not_mem
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_mem huJ
  obtain ⟨h, hh, hht⟩ := SwapN9.exists_conj_eq_mul_of_swap htH ht2 ht1 hs.le
    (fun z hz => (hMKt hz).1) (fun z hz => (hMtK hz).1) hV (hs.diag huJ) hu hut.symm
    (hJN huJ) huNt hv1
  exact ⟨h, hh, by rw [hut]; exact hht⟩

theorem Setting.centralizer_mul_le (hs : Setting t J n e E D M) {u : X} (huJ : u ∈ J)
    (hu : u * u = 1) : centralizer ({u * t} : Set X) ≤ Hn E := by
  intro g hg
  obtain ⟨h, hh, hht⟩ := hs.exists_conj_mul huJ hu
  rw [mem_centralizer_singleton_iff] at hg
  have h1 : g * (h * t * h⁻¹) = (h * t * h⁻¹) * g := by rw [← hht]; exact hg
  have h2 : h⁻¹ * g * h ∈ Hn E := by
    refine hs.cent (mem_centralizer_singleton_iff.mpr ?_)
    calc (h⁻¹ * g * h) * t = h⁻¹ * (g * (h * t * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * t * h⁻¹) * g) * h := by rw [h1]
      _ = t * (h⁻¹ * g * h) := by group
  have h3 : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

end Layer0

end CFSG.ComponentClassification.SolMax.SwapP2
