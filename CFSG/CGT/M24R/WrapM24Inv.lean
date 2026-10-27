module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.CGT.M24R

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

theorem m24_involution_conj_reps
    {u : Equiv.Perm (Fin 24)} (hu : u ∈ NativeSporadic.M24) (hu2 : orderOf u = 2) :
    ∃ r ∈ m24InvReps, ∃ c ∈ NativeSporadic.M24, u = c * r * c⁻¹ := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hreps : ∀ r ∈ m24InvReps,
      (1 : Equiv.Perm (Fin 24))⁻¹ * r ∈ m24Certificate.originalSubgroup ∧ orderOf r = 2 := by
    intro r hr
    rw [m24InvReps_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨by simpa using hr1, hro1⟩
    · exact ⟨by simpa using hr2, hro2⟩
  have hu' : (1 : Equiv.Perm (Fin 24))⁻¹ * u ∈ m24Certificate.originalSubgroup := by
    rwa [inv_one, one_mul, m24Certificate_originalSubgroup]
  have h := (exists_conj_of_repsOK hn m24Certificate m24Certificate_check
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh) (by norm_num) m24InvReps
    hreps 40000 hok).1 u hu' hu2
  rwa [m24Certificate_originalSubgroup] at h

theorem exists_orderOf_five_comm_m24Rep1 :
    ∃ f ∈ NativeSporadic.M24, f * m24Rep1 = m24Rep1 * f ∧ orderOf f = 5 := by
  obtain ⟨-, -, hK, hKc, -⟩ := m24_rep_data1
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := m24CentQ1.originalSubgroup) 5
    (by rw [hKc]; norm_num)
  have hfC := hK f.2
  rw [mem_centralizerIn, m24Certificate_originalSubgroup] at hfC
  exact ⟨f, hfC.1, hfC.2, by rw [Subgroup.orderOf_coe, hf]⟩

theorem m24_conj_rep2_of_forall_orderOf_ne_five
    {u : Equiv.Perm (Fin 24)} (hu : u ∈ NativeSporadic.M24)
    (hu2 : orderOf u = 2)
    (hu5 : ∀ f ∈ NativeSporadic.M24, f * u = u * f → orderOf f ≠ 5) :
    ∃ c ∈ NativeSporadic.M24, u = c * m24Rep2 * c⁻¹ := by
  obtain ⟨r, hr, c, hc, rfl⟩ := m24_involution_conj_reps hu hu2
  rw [m24InvReps_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exfalso
    obtain ⟨f, hf, hfc, hf5⟩ := exists_orderOf_five_comm_m24Rep1
    refine hu5 (c * f * c⁻¹) (NativeSporadic.M24.mul_mem (NativeSporadic.M24.mul_mem hc hf)
      (NativeSporadic.M24.inv_mem hc)) ?_ ?_
    · calc c * f * c⁻¹ * (c * m24Rep1 * c⁻¹) = c * (f * m24Rep1) * c⁻¹ := by group
        _ = c * (m24Rep1 * f) * c⁻¹ := by rw [hfc]
        _ = c * m24Rep1 * c⁻¹ * (c * f * c⁻¹) := by group
    · rw [← hf5]
      exact (MulEquiv.orderOf_eq (MulAut.conj c) f)
  · exact ⟨c, hc, rfl⟩

theorem m24_exists_conj_of_forall_orderOf_ne_five
    {u v : Equiv.Perm (Fin 24)} (hu : u ∈ NativeSporadic.M24)
    (hv : v ∈ NativeSporadic.M24) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2)
    (hu5 : ∀ f ∈ NativeSporadic.M24, f * u = u * f → orderOf f ≠ 5)
    (hv5 : ∀ f ∈ NativeSporadic.M24, f * v = v * f → orderOf f ≠ 5) :
    ∃ c ∈ NativeSporadic.M24, v = c * u * c⁻¹ := by
  obtain ⟨c, hc, rfl⟩ := m24_conj_rep2_of_forall_orderOf_ne_five hu hu2 hu5
  obtain ⟨d, hd, rfl⟩ := m24_conj_rep2_of_forall_orderOf_ne_five hv hv2 hv5
  refine ⟨d * c⁻¹, NativeSporadic.M24.mul_mem hd (NativeSporadic.M24.inv_mem hc), ?_⟩
  group

end CFSG.CGT.M24R
