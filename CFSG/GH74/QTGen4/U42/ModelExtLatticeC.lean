module

public import CFSG.GH74.QTGen4.U42.ModelExtLatticeB
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocKer
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Nrm

public section

namespace CFSG.GH74.QTGen4.U42.ModelExtLatticeC

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42 CFSG.Quasithin.H13.F431.U42Aut
open CFSG.GH74.QTGen4.U42.ModelExtLattice CFSG.GH74.QTGen4.U42.ModelExtLatticeB


theorem conj_c3pow_mem_T {t : Y} (ht : t ∈ T) (k : ℕ) : (c3Y ^ k)⁻¹ * t * c3Y ^ k ∈ T := by
  have hy : (c3Y ^ k)⁻¹ ∈ B0 := B0.inv_mem (B0.pow_mem c3_mem_B0 k)
  have h := (Subgroup.mem_normalizer_iff.1 (B0_le_normalizer_T hy) t).1 ht
  simpa using h

theorem aux_id {G : Type*} [Group G] (t t' x d y : G) :
    x * d * y = (t⁻¹ * (t * x * d * (t' * y))) * (y⁻¹ * t'⁻¹ * y) := by
  group

theorem c3_of_cover {K : Subgroup Y} (hT : T ≤ K) {g : Y} (hg : g ∈ K) {j : ℕ} (hj8 : j < 8)
    (h2 : 2 ≤ j) {b b' : Y} (hb : b ∈ B0) (hb' : b' ∈ B0) (hgeq : g = b * Dj j * b') :
    c3Y ∈ K := by
  obtain ⟨t, ht, k, hk, rfl⟩ := B0_elem hb
  obtain ⟨t', ht', k', hk', rfl⟩ := B0_elem hb'
  subst hgeq
  obtain ⟨⟨j0, a0, b0, w0⟩, hx, e1, e2, e3⟩ := latT_cov h2 hj8 hk hk'
  have e1' : j0 = j := e1
  have e2' : a0 = k := e2
  have e3' : b0 = k' := e3
  have hx' : (j, k, k', w0) ∈ latTData := by
    rw [← e1', ← e2', ← e3']
    exact hx
  have hrK : c3Y ^ k * Dj j * c3Y ^ k' ∈ K := by
    rw [aux_id t t' (c3Y ^ k) (Dj j) (c3Y ^ k')]
    exact K.mul_mem (K.mul_mem (K.inv_mem (hT ht)) hg)
      (hT (conj_c3pow_mem_T (T.inv_mem ht') k'))
  exact c3_mem_of_row hT hx' rfl hrK

theorem lattice_T {H : Subgroup Y} (h : T ≤ H) : H ≤ P1 ∨ H ≤ P2 ∨ H = ⊤ := by
  by_cases hc : c3Y ∈ H
  · have hB : B0 ≤ H := by
      rw [← B0_eq_sup]
      exact sup_le h ((Subgroup.zpowers_le).2 hc)
    rcases lattice hB with e | e | e | e
    · exact Or.inl ((le_of_eq e).trans B0_le_P1)
    · exact Or.inl e.le
    · exact Or.inr (Or.inl e.le)
    · exact Or.inr (Or.inr e)
  · left
    intro g hg
    obtain ⟨j, hj, b, hb, b', hb', hgeq⟩ := cover_B0 g
    by_cases h2 : 2 ≤ j
    · exact absurd (c3_of_cover h hg hj h2 hb hb' hgeq) hc
    · have hj2 : j < 2 := by omega
      interval_cases j
      · rw [hgeq, Dj_zero, mul_one]
        exact P1.mul_mem (B0_le_P1 hb) (B0_le_P1 hb')
      · rw [hgeq]
        exact P1.mul_mem (P1.mul_mem (B0_le_P1 hb) D1_mem_P1) (B0_le_P1 hb')

theorem units_mul_inv_one' (u v : ℤˣ) (hu : u ≠ 1) (hv : v ≠ 1) : u * v⁻¹ = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl
  · exact absurd rfl hu
  · exact absurd rfl hu
  · exact absurd rfl hv
  · rfl

theorem Ah_split (x : Ah) : x ∈ Yh ∨ ∃ y ∈ Yh, x = y * fhatA := by
  by_cases hx : x ∈ Yh
  · exact Or.inl hx
  · refine Or.inr ⟨x * fhatA⁻¹, ?_, by simp⟩
    rw [← signA_eq_one_iff, map_mul, map_inv]
    exact units_mul_inv_one' _ _ (fun h => hx ((signA_eq_one_iff x).1 h))
      (fun h => fhatA_not_mem_Yh ((signA_eq_one_iff fhatA).1 h))

theorem le_of_comap_le_fhat {H Q : Subgroup Ah} (hf : fhatA ∈ H) (hQ : fhatA ∈ Q)
    (hc : H.comap incl ≤ Q.comap incl) : H ≤ Q := by
  intro x hx
  rcases Ah_split x with hxY | ⟨y, hy, rfl⟩
  · obtain ⟨y0, rfl⟩ := (mem_Yh_iff_incl _).1 hxY
    exact Subgroup.mem_comap.1 (hc (Subgroup.mem_comap.2 hx))
  · have hyH : y ∈ H := by
      have := H.mul_mem hx (H.inv_mem hf)
      simpa using this
    obtain ⟨y0, rfl⟩ := (mem_Yh_iff_incl _).1 hy
    exact Q.mul_mem (Subgroup.mem_comap.1 (hc (Subgroup.mem_comap.2 hyH))) hQ

theorem top_of_comap_top {H : Subgroup Ah} (hf : fhatA ∈ H) (hK : H.comap incl = ⊤) : H = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hmem : ∀ y0 : Y, incl y0 ∈ H := fun y0 => by
    have h1 : y0 ∈ H.comap incl := by
      rw [hK]
      exact Subgroup.mem_top _
    exact Subgroup.mem_comap.1 h1
  rcases Ah_split x with hxY | ⟨y, hy, rfl⟩
  · obtain ⟨y0, rfl⟩ := (mem_Yh_iff_incl _).1 hxY
    exact hmem y0
  · obtain ⟨y0, rfl⟩ := (mem_Yh_iff_incl _).1 hy
    exact H.mul_mem (hmem y0) hf

theorem lattice_That {H : Subgroup Ah} (h : That ≤ H) : H ≤ P1h ∨ H ≤ P2h ∨ H = ⊤ := by
  have hf : fhatA ∈ H := h fhatA_mem_That
  have hTK : T ≤ H.comap incl := by
    rw [← comap_That]
    exact Subgroup.comap_mono h
  rcases lattice_T hTK with hK | hK | hK
  · exact Or.inl (le_of_comap_le_fhat hf fhatA_mem_P1h (by rw [comap_P1h]; exact hK))
  · exact Or.inr (Or.inl (le_of_comap_le_fhat hf fhatA_mem_P2h (by rw [comap_P2h]; exact hK)))
  · exact Or.inr (Or.inr (top_of_comap_top hf hK))

theorem isYAmalgamPair_Ah : IsYAmalgamPair That P1h P2h := by
  refine ⟨isSylowTwoOf_That_top, P1h_ne_P2h, fun M => ⟨?_, ?_⟩⟩
  · rintro ⟨hM, hN⟩
    have hTM : That ≤ M := le_trans Subgroup.le_normalizer hN
    rcases lattice_That hTM with h | h | h
    · exact Or.inl (hM.2 P1h P1h_isTwoLocal h).symm
    · exact Or.inr (hM.2 P2h P2h_isTwoLocal h).symm
    · rw [h] at hM
      exact absurd hM.1 not_isTwoLocal_top_A
  · rintro (rfl | rfl)
    · exact ⟨isMaximalTwoLocal_P1h, normalizer_That_le_Bh.trans Bh_le_P1h⟩
    · exact ⟨isMaximalTwoLocal_P2h, normalizer_That_le_Bh.trans Bh_le_P2h⟩

end CFSG.GH74.QTGen4.U42.ModelExtLatticeC
