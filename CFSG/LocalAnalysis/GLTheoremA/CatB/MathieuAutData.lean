module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

variable {n : ℕ}

theorem centralizer_card_of_reps (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    (data : List (Equiv.Perm (Fin n) × Subgroup (Equiv.Perm (Fin n)) × ℕ × ℕ))
    (hreps : ∀ d ∈ data, g₀⁻¹ * d.1 ∈ Q.originalSubgroup ∧ orderOf d.1 = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) (data.map fun d => toTable d.1) cap =
      true)
    (hK : ∀ d ∈ data, d.2.1 ≤ centralizerIn Q.originalSubgroup d.1 ∧
      (conjClosure n gens gensInv (toTable d.1) cap).1.size * Nat.card d.2.1 =
        Nat.card Q.originalSubgroup ∧
      Nat.card d.2.1 = 2 ^ d.2.2.2 * d.2.2.1) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 → ∃ d ∈ data,
      Nat.card (centralizerIn Q.originalSubgroup u) = 2 ^ d.2.2.2 * d.2.2.1 := by
  have hok' : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) ((data.map Prod.fst).map toTable)
      cap = true := by
    rw [List.map_map]
    exact hok
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ (by norm_num)
    (data.map Prod.fst) (fun r hr => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
      exact hreps d hd) cap hok'
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hKle, hKcard, hKv⟩ := hK d hd
  have hcent := centralizerIn_eq_of_le Q.originalSubgroup d.1 hKle (hsize _ hr) hKcard
  refine ⟨d, hd, ?_⟩
  rw [centralizerIn_conj _ hc, hcent, Subgroup.card_map_of_injective (MulAut.conj c).injective, hKv]

theorem m22_inner_card :
    ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
    ¬ 9 ∣ Nat.card (centralizerIn NativeSporadic.M22 u) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := centralizer_card_of_reps hn m22Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m22Rep1, m22CentQ1.originalSubgroup, 3, 7)]
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_, by rw [hKc1]; norm_num⟩
      rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card]) u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  rw [hcard]
  decide

theorem m22_outer_card :
    ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
    ¬ 9 ∣ Nat.card (centralizerIn NativeSporadic.M22 u) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22OutReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := centralizer_card_of_reps hn m22Certificate hQ
    (pairTables_spec hn hA hB) m22Delta hg₀
    [(m22OutRep1, m22OutCentQ1.originalSubgroup, 5, 6),
      (m22OutRep2, m22OutCentQ2.originalSubgroup, 21, 6)]
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨hr1, hro1⟩
      · exact ⟨hr2, hro2⟩) 2000 hok
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨hK1, ?_, by rw [hKc1]; norm_num⟩
        rw [hsz.1, hKc1, m22Certificate_originalSubgroup, m22_card]
      · refine ⟨hK2, ?_, by rw [hKc2]; norm_num⟩
        rw [hsz.2, hKc2, m22Certificate_originalSubgroup, m22_card]) u hu ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> rw [hcard] <;> decide

theorem m12_inner_card :
    ∀ u ∈ NativeSporadic.M12, orderOf u = 2 →
    ¬ 9 ∣ Nat.card (centralizerIn NativeSporadic.M12 u) := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨hok, hsz, -⟩ := m12_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m12_rep_data2
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  rw [m12InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m12Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := centralizer_card_of_reps hn m12Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m12Rep1, m12CentQ1.originalSubgroup, 3, 6), (m12Rep2, m12CentQ2.originalSubgroup, 15, 4)]
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨by simpa using hr1, hro1⟩
      · exact ⟨by simpa using hr2, hro2⟩) 1000 hok
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨hK1, ?_, by rw [hKc1]; norm_num⟩
        rw [hsz.1, hKc1, m12Certificate_originalSubgroup, m12_card]
      · refine ⟨hK2, ?_, by rw [hKc2]; norm_num⟩
        rw [hsz.2, hKc2, m12Certificate_originalSubgroup, m12_card]) u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> rw [hcard] <;> decide

theorem m12D_outer_card : ∀ u,
    m12Sigma⁻¹ * u ∈ m12D.originalSubgroup → orderOf u = 2 →
    ¬ 9 ∣ Nat.card (centralizerIn m12D.originalSubgroup u) := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, hsz, hord⟩ := m12_sigma_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m12_sigma_cent
  have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hK : m12SigmaCentQ.originalSubgroup ≤ centralizerIn m12D.originalSubgroup m12Sigma := by
    rw [m12SigmaCentQ, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m12_gens_memD w) hcomm
  have hKc : Nat.card m12SigmaCentQ.originalSubgroup = 120 := by
    rw [← m12SigmaCentQ.orderCertificate_eq_card hc, ho]
  intro u hu ho2
  obtain ⟨d, hd, hcard⟩ := centralizer_card_of_reps hn m12D m12D_check.1
    (pairTables_spec hn hA hB) m12Sigma (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq)
    [(m12Sigma, m12SigmaCentQ.originalSubgroup, 15, 3)]
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨by simp, ?_⟩
      exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord) 1000 hok
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK, ?_, by rw [hKc]; norm_num⟩
      rw [hsz, hKc, ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]) u hu ho2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  rw [hcard]
  decide

end CFSG.LocalAnalysis.GLTheoremA.CatB
