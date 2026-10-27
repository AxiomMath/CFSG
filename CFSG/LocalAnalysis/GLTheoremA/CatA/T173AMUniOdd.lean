module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMCharP
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMTorUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMMult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMGhat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMUniRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMUniWt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMUniK
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMUniComb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMUniIV

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups


theorem uni_odd_case {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    {n d : ℕ} {F : Type} [Field F] [Finite F]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (hcfg : MCfg p S B N D K x) (hmark : UniMarking p S B n d F θ) (hpd : p ∣ d)
    (hZodd : Odd (Nat.card (Subgroup.center ↥S)))
    (hbmax : GLAIsBmax p B ∨ p ^ (d - 2) ≤ Nat.card B) :
    ∃ B' U : Subgroup Ω, IsElemAbelian p B' ∧ B' ≤ S ⊔ B ∧ B ≤ B' ∧ B ≠ B' ∧ U ≠ ⊥ ∧
      IsPGroup 2 U ∧ U ≤ K ∧ B' = (B' ⊓ K) ⊔ (B' ⊓ Subgroup.normalizer (U : Set Ω)) ∧
      B' ≤ Subgroup.normalizer (K : Set Ω) := by
  obtain ⟨hF, hn1, hd3, hdn, hpq, hBN, hact⟩ := id hmark
  have hp : p.Prime := hcfg.prime
  have hp2 : p ≠ 2 := hcfg.odd
  have hd4 : d ≠ 4 := by
    intro h4
    subst h4
    have h1 : p ∣ 2 ^ 2 := by simpa using hpd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  haveI : CharP F 2 := charP_two_of_card (n := 2 * n) (by omega)
    (by rw [hF, ← pow_mul, mul_comm])
  have hpF2 : p ∣ Nat.card F - 1 := by
    have h2 : Nat.card F - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [hF]
      have hsq := sq_tsub_sq (2 ^ n) 1
      rw [one_pow] at hsq
      rw [← hsq, sq]
    rw [h2]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨hperf, hcen, hZ, hodd⟩ := uni_model_facts hF hn1 hd3 hdn
  obtain ⟨hGUiff, hGUN, hGUs, hSUGU⟩ := uni_GU_facts (d := d) (n := n) hF
  have hact' : ∀ b ∈ B, ∃ A ∈ MGU n d F, GInduced θ b A := by
    intro b hb
    obtain ⟨φ, ⟨A, hAmem, hA⟩, hind⟩ := hact b hb
    exact ⟨A, Subgroup.subset_closure hAmem, φ, hA, hind⟩
  obtain ⟨Gh, hGhV, hGh, hZG, hel, hcard⟩ :=
    gen_ghat hcfg θ (MGU n d F) hGUs hGUN hcen hact'
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
  have hd5 : 5 ≤ d := by omega
  have hrow := uni_hopf_row hF hn1 hd3 hdn hd4
  haveI : Finite (CFSG.Open.griessHopfMultiplier
      (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))) := hrow.1
  obtain ⟨ψ, hψ⟩ := cover_exact (k := if d = 6 ∧ n = 1 then 2 else 0) hcfg.qs hZodd hperf
    (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))) (QuotientGroup.mk'_surjective _)
    (proj_ker_le_center _) hodd hZ θ hrow.2
  obtain ⟨hψS, -⟩ := gen_psi_props hcfg.qs θ ψ hψ
  have hB1 : p ^ (d - 2) ≤ Nat.card B :=
    hbmax.elim (fun h => uni_rank_bmax hcfg h hF hn1 hd3 hpd hpq θ ψ hψ) id
  have hrank : p ^ max 3 (d - 3) ≤ (LargeEvenScalars (Fin d) F).relIndex Gh := by
    have h2 : p ^ (d - 3) ≤ (LargeEvenScalars (Fin d) F).relIndex Gh := by
      rw [← hcard] at hB1
      have : p * p ^ (d - 3) ≤ p * (LargeEvenScalars (Fin d) F).relIndex Gh := by
        calc p * p ^ (d - 3) = p ^ (d - 2) := by
              rw [← pow_succ']
              congr 1
              omega
          _ ≤ _ := hB1
      exact Nat.le_of_mul_le_mul_left this hp.pos
    rcases le_total 3 (d - 3) with h | h
    · rw [max_eq_right h]
      exact h2
    · rw [max_eq_left h]
      exact hlow3
  obtain ⟨T, hT2, hT1, hTU, hTN⟩ := gen_two_subgroup hcfg θ hodd (Gh := Gh)
    (fun A hA => hGUN (hGhV hA)) (fun A hA => ((hGh A).1 hA).2)
  have hGU : ∀ A ∈ Gh, A ∈ LargeEvenGUSet (Fin d) F (2 ^ n) :=
    fun A hA => (hGUiff A).1 (hGhV hA)
  have hTGU : ∀ t ∈ T, t ∈ LargeEvenGUSet (Fin d) F (2 ^ n) :=
    fun t ht => (hGUiff t).1 (hSUGU (hTU ht))
  have htor : MToral p d F Gh :=
    uni_toral_of_rank hp hp2 hF hn1 hpq hpd hZG hel hGU hT2 hT1 hTGU hTN hrank
  obtain ⟨P, hP, hdiag⟩ := tor_uni_frame hp hp2 hF hn1 hpq hZG htor hGU
  have hB : ∀ b ∈ B, GDiagAct p ψ P b := by
    intro b hb
    obtain ⟨A, hAV, hind⟩ := hact' b hb
    have hAG : A ∈ Gh := (hGh A).2 ⟨hAV, b, hb, hind⟩
    exact ⟨A, gen_equivariance hperf θ ψ hψ (hBN hb) (hGUN hAV) hind, hel.1 A hAG,
      hdiag A hAG⟩
  obtain ⟨R, hR0, hRiso, hRG⟩ := uni_isotropic_inv hF hn1 hT2 hT1 hTGU hGU hTN
  obtain ⟨a, a', haa, hpair⟩ := m_uni_repeated_weight hF hn1 P hP hGU hdiag R hR0 hRiso hRG
  obtain ⟨I, hI2, hI3, hK, A₀, hA₀, hlev, hD, hsing⟩ :=
    uni_K_shape hcfg hF hn1 hd3 hpd θ ψ hψ P hP hB hGh hmark hdiag
  obtain ⟨s, t, hs, ht, hst, hsep⟩ := uni_comb hp hp2 hF hn1 hpq hpd hd5 P hZG hel htor hdiag
    hrank a a' haa hpair I hI2 hI3 A₀ hA₀ hlev hD hsing
  have hIpair : (a ∈ I ∧ a' ∈ I) ∨ (a ∉ I ∧ a' ∉ I) := by
    obtain ⟨i₀, -, hiff⟩ := hlev
    have h1 : MWt P A₀ a = MWt P A₀ a' := hpair A₀ hA₀
    by_cases ha : a ∈ I
    · refine Or.inl ⟨ha, (hiff a').2 ?_⟩
      rw [← h1]
      exact (hiff a).1 ha
    · refine Or.inr ⟨ha, fun ha' => ha ((hiff a).2 ?_)⟩
      rw [h1]
      exact (hiff a').1 ha'
  exact uni_iv_assembly hcfg hF hn1 hd3 hpq hBN θ ψ hψ hψS hperf hcen P hP hB hGh hdiag
    I hK a a' haa hpair hIpair s t hs ht hst hsep

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
