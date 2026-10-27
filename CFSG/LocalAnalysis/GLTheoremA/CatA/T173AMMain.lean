module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMLinRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMLinDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMLinK
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMLinGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMUniExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups


theorem t173AMNonzeroLin_holds : T173AMNonzeroLin := by
  intro p Ω _ _ S B N D K x n d F _ _ θ hcfg _hcat hmark hn hpd
  exfalso
  obtain ⟨hF, hn1, hd2, -, hpF', hBN, hact⟩ := hmark
  have hp : p.Prime := hcfg.prime
  have hp2 : p ≠ 2 := hcfg.odd
  have hpF : p ∣ 2 ^ n - 1 := by
    rcases hpF' with h | ⟨h1, -⟩
    · exact h
    · omega
  have hd3 : 3 ≤ d := by
    have h1 := Nat.le_of_dvd (by omega) hpd
    have h2 := hp.two_le
    omega
  haveI : CharP F 2 := charP_two_of_card hn1 hF
  have hpF2 : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpF
  obtain ⟨hperf, hcen, hZ, hodd⟩ := lin_model_facts hF hn hd3
  have hact' : ∀ b ∈ B, ∃ A ∈ (⊤ : Subgroup (GL (Fin d) F)), GInduced θ b A := by
    intro b hb
    obtain ⟨φ, ⟨A, -, hA⟩, hind⟩ := hact b hb
    exact ⟨A, Subgroup.mem_top _, φ, hA, hind⟩
  obtain ⟨Gh, -, hGh, hZG, hel, hcard⟩ :=
    gen_ghat (mcfg_of_cfg173 hcfg) θ ⊤ le_top (fun A _ => lin_normalizes A) hcen hact'
  have hup : (LargeEvenScalars (Fin d) F).relIndex Gh ≤ p ^ (d - 1) :=
    tor_rank_le hp hp2 hpF2 hZG hel
  have hlow3 : p ^ 3 ≤ (LargeEvenScalars (Fin d) F).relIndex Gh := by
    have h4 : p ^ 4 ≤ Nat.card B := hcfg.four
    rw [← hcard] at h4
    have : p * p ^ 3 ≤ p * (LargeEvenScalars (Fin d) F).relIndex Gh := by
      calc p * p ^ 3 = p ^ 4 := by ring
        _ ≤ _ := h4
    exact Nat.le_of_mul_le_mul_left this hp.pos
  have hd3' : d ≠ 3 := by
    intro h3
    subst h3
    have h1 : p ^ 3 ≤ p ^ 2 := hlow3.trans hup
    have := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3)
    omega
  have hrow := lin_hopf_row hF hn hd3 (fun h => hd3' h.1)
  haveI : Finite (CFSG.Open.griessHopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin d) F))) := hrow.1
  have hSodd : Odd (Nat.card (Subgroup.center ↥S)) :=
    Odd.of_dvd_nat hodd ((cover_center_dvd hcfg.qs θ).trans hrow.2)
  obtain ⟨ψ, hψ⟩ := cover_exact (k := 0) hcfg.qs hSodd hperf
    (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) (QuotientGroup.mk'_surjective _)
    (proj_ker_le_center _) hodd hZ θ (by simpa using hrow.2)
  obtain ⟨hψS, -⟩ := gen_psi_props hcfg.qs θ ψ hψ
  have hB1 : p ^ (d - 1) ≤ Nat.card B := lin_rank_bmax hcfg hF hn1 hd3 hpd hpF θ ψ hψ
  have hrank : p ^ max 3 (d - 2) ≤ (LargeEvenScalars (Fin d) F).relIndex Gh := by
    have h2 : p ^ (d - 2) ≤ (LargeEvenScalars (Fin d) F).relIndex Gh := by
      rw [← hcard] at hB1
      have : p * p ^ (d - 2) ≤ p * (LargeEvenScalars (Fin d) F).relIndex Gh := by
        calc p * p ^ (d - 2) = p ^ (d - 1) := by
              rw [← pow_succ']
              congr 1
              omega
          _ ≤ _ := hB1
      exact Nat.le_of_mul_le_mul_left this hp.pos
    rcases le_total 3 (d - 2) with h | h
    · rw [max_eq_right h]
      exact h2
    · rw [max_eq_left h]
      exact hlow3
  have htor : MToral p d F Gh := tor_toral_of_rank hp hp2 hpF2 hpd hZG hel hrank
  obtain ⟨⟨P, hdiag⟩, -⟩ := tor_toral_diag hp hp2 hpF2 hZG htor
  have hB : ∀ b ∈ B, GDiagAct p ψ P b := by
    intro b hb
    obtain ⟨A, -, hind⟩ := hact' b hb
    have hAG : A ∈ Gh := (hGh A).2 ⟨Subgroup.mem_top _, b, hb, hind⟩
    exact ⟨A, gen_equivariance hperf θ ψ hψ (hBN hb) (lin_normalizes A) hind, hel.1 A hAG,
      hdiag A hAG⟩
  have hES : ∀ (t : GL (Fin d) F) (u : ↥(LargeEvenSLGroup (Fin d) F)), t ∈ LinDiagTors p d F →
      (u : GL (Fin d) F) = P⁻¹ * t * P → (ψ u : Ω) ∈ B :=
    fun t u ht hu => lin_ES_le hcfg hF hn1 hd3 hpd hpF θ ψ hψ P hB ht hu
  have hN : ∀ (σ : Equiv.Perm (Fin d)) (Pσ : GL (Fin d) F)
      (u : ↥(LargeEvenSLGroup (Fin d) F)), (Pσ : Matrix (Fin d) (Fin d) F) = σ.permMatrix F →
      (u : GL (Fin d) F) = P⁻¹ * Pσ * P → (ψ u : Ω) ∈ N :=
    fun σ Pσ u hPσ hu => lin_perm_mem_N hcfg hF hn1 hd3 hpd hpF θ ψ hψ P hB hES σ Pσ hPσ hu
  obtain ⟨I, hI2, hK⟩ := lin_K_shape hcfg hF hn hd3 hpd θ ψ hψ P hB
  exact cfg_hc_contra hcfg (lin_closure_top hd3 ψ hψS P I hI2 hK hN)

theorem t173AMNonzeroUni_holds : T173AMNonzeroUni := by
  intro p Ω _ _ S B N D K x n d F _ _ θ hcfg _hcat hmark hpd
  by_cases hZodd : Odd (Nat.card (Subgroup.center ↥S))
  · obtain ⟨B', U, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
      uni_odd_case θ (mcfg_of_cfg173 hcfg) hmark hpd hZodd (Or.inl hcfg.bmax)
    exact Or.inr ⟨B', U, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · have hmark0 := hmark
    obtain ⟨hF, hn1, hd3, hdn, hpq, hBN, hact⟩ := hmark
    have hp : p.Prime := hcfg.prime
    have hp2 : p ≠ 2 := hcfg.odd
    have hd4 : d ≠ 4 := by
      intro h4
      subst h4
      have h1 : p ∣ 2 ^ 2 := by simpa using hpd
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h1
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    obtain ⟨hperf, hcen, hZ, hodd⟩ := uni_model_facts hF hn1 hd3 hdn
    have h61 : d = 6 ∧ n = 1 := by
      by_contra hne
      obtain ⟨hfin, hdvd⟩ := uni_hopf_row hF hn1 hd3 hdn hd4
      haveI : Finite (CFSG.Open.griessHopfMultiplier
          (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))) := hfin
      apply hZodd
      refine Odd.of_dvd_nat hodd ((cover_center_dvd hcfg.qs θ).trans (hdvd.trans ?_))
      rw [if_neg hne]
      simp
    obtain ⟨rfl, rfl⟩ := h61
    exact uni_exceptional θ hcfg hmark0 hpd hZodd

theorem t173AMNonzero_holds : T173AMNonzero :=
  ⟨t173AMNonzeroLin_holds, t173AMNonzeroUni_holds⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
