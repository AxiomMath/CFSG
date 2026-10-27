module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe9A
import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11A
import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11B
import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9P
import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36W
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapAC

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem nonempty_coreQuot_of_le_normalizer [Finite X] {M : Subgroup X} {m : ℕ}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ)
    {e₀ : X} (he₀N : e₀ ∈ normalizer (M : Set X)) (he₀2 : e₀ * e₀ = 1)
    (he₀4 : (ρ ⟨e₀, he₀N⟩).support.card = 4) {k : ℕ} (hk : 5 ≤ k) (hmk : m = k + 4)
    {N : Subgroup X} (hNM : N ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ N, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    (hNC : N ≤ centralizer ({e₀} : Set X)) (hN : ⁅N, N⁆ = N)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin k)) :
    Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin k)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 ↥N with hOdef
  set f : ↥N →* Perm (Fin m) := ρ.comp (inclusion hNM) with hfdef
  have hrange :
      f.range ≤ (fixAlt (ρ ⟨e₀, he₀N⟩)).map (alternatingGroup (Fin m)).subtype := by
    rintro _ ⟨y, rfl⟩
    have hy : (y : X) ∈ oddGen N := by rw [oddGen_eq_of_perfect hN]; exact y.2
    exact rho_mem_fixAlt_of_mem_oddGen he₀N he₀2 he₀4.le hNM hNC hy (hNM y.2)
  have hmk' : m - (ρ ⟨e₀, he₀N⟩).support.card = k := by omega
  have hcard1 : Nat.card f.range ≤ k.factorial / 2 := by
    have h1 := card_le_of_le hrange
    rw [card_map_of_injective (alternatingGroup (Fin m)).subtype_injective,
      card_fixAlt (by omega), hmk'] at h1
    exact h1
  have hkerO : f.ker ≤ O := by
    intro z hz
    have h1 : ρ ⟨(z : X), hNM z.2⟩ = 1 := hz
    obtain ⟨o, ho, hoz⟩ := mem_coreNOf_of_rho_eq_one hρ hNM hker le_rfl z.2 h1
    have h2 : o = z := Subtype.ext hoz
    rw [← h2]
    exact ho
  have hcard2 : Nat.card f.ker ≤ Nat.card O := card_le_of_le hkerO
  have hcardN : Nat.card ↥N = Nat.card f.range * Nat.card f.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hcardO : Nat.card ↥N = Nat.card (↥N ⧸ O) * Nat.card O :=
    card_eq_card_quotient_mul_card_subgroup O
  have hq : Nat.card (↥N ⧸ O) ≤ k.factorial / 2 := by
    have h5 : 0 < Nat.card O := Nat.card_pos
    have h6 : Nat.card (↥N ⧸ O) * Nat.card O ≤ (k.factorial / 2) * Nat.card O := by
      rw [← hcardO, hcardN]
      exact Nat.mul_le_mul hcard1 hcard2
    exact Nat.le_of_mul_le_mul_right h6 h5
  have hZ : center (↥N ⧸ O) = ⊥ := by
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h1 := card_eq_card_quotient_mul_card_subgroup (center (↥N ⧸ O))
    rw [Nat.card_congr ((Sol78.coreQuotientCenterEquiv ↥N).trans ψ).toEquiv,
      nat_card_alternatingGroup, Nat.card_fin] at h1
    have h3 : 0 < k.factorial / 2 := Nat.div_pos (by
      have := Nat.self_le_factorial k
      omega) (by norm_num)
    have h4 : (k.factorial / 2) * Nat.card (center (↥N ⧸ O)) ≤ (k.factorial / 2) * 1 := by
      rw [mul_one, ← h1]
      exact hq
    exact (Subgroup.card_le_one_iff_eq_bot _).mp (Nat.le_of_mul_le_mul_left h4 h3)
  have hZO : Open.fusionZStar ↥N = O := (Sol78.fusionZStar_eq_iff _).mpr hZ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZO).symm.trans ψ⟩

namespace Sig36

section General

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem PumpG.toPumpE {S : Sig36 X t J n e E D} {e₀ : X} {k : ℕ} {L₀ F N : Subgroup X} {r : ℕ}
    {θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)}
    {ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)} {τ' : Perm (Fin r)} {DN : Finset (Fin r)}
    (P : S.PumpG e₀ t k L₀ F N r θN ρN τ' DN) (hk : k = n - 4) (hL₀J : L₀ ≤ J) (hrn : r ≤ n) :
    S.PumpE e₀ L₀ F N r θN ρN τ' DN := by
  subst hk
  exact ⟨hL₀J, P.L₀C, P.L₀pc, P.FL₀, P.F4, P.Fsq, P.FD, P.NC, P.Npc, P.L₀N, P.L₀NN, P.kr, hrn,
    P.perm, P.case, P.τk, P.iso, P.DN4, P.DNfix, P.Fsupp⟩

variable (S : Sig36 X t J n e E D)
include S

theorem false_of_conj_eq_swap
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {N : Subgroup X}
    (hNH : N ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hfix : N.map (MulAut.conj t).toMonoidHom = N) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have hMtt : Mt.map (MulAut.conj t).toMonoidHom = M := by
    rw [hMtdef, ← map_conj_mul, ht2]
    ext z
    simp
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hMtK : Mt ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMH hMtH hMpc hMtpc (Ne.symm hne)
  have hNMM : N ≤ M ⊓ Mt := by
    rcases S.le_or_le_of_isPComponent_swap hCH hMH hMpc hne hJM hsmall he₀J he₀o hNH hNC
      hNpc with h | h
    · refine le_inf h ?_
      rw [← hfix]
      exact map_mono h
    · refine le_inf ?_ h
      rw [← hfix, ← hMtt]
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

theorem nonempty_coreQuot_of_le_swap
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) {e₀ : X} (he₀E : e₀ ∈ E)
    (he₀1 : e₀ ≠ 1) {N : Subgroup X} (hNM : N ≤ M) (hNC : N ≤ centralizer ({e₀} : Set X))
    (hN : ⁅N, N⁆ = N) (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin (n - 4))) :
    Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin (n - 4))) := by
  classical
  have hn9 := S.nine_le
  have htH := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hMH hMpc hne hJM
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀4 : (ρ ⟨e₀, hJN he₀J⟩).support.card = 4 := by
    rw [S.card_support_rho_of_swap hCH hMH hMpc hne hJM θ hρ he₀J,
      S.card_support_coreImage_E he₀E he₀1]
  exact nonempty_coreQuot_of_le_normalizer hρ (hJN he₀J) he₀2 he₀4 (by omega) (by omega)
    (hNM.trans le_normalizer) (fun g hg hgK => odd_orderOf_of_mem_oddCoreIn
      (mem_core_of_mem_coreActionKernel hρ (by omega) (hNM hg) hgK)) hNC hN ψ

end General

section Eleven

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem exists_pumpE_eleven
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    ∃ (L₀ F N : Subgroup X) (r : ℕ) (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r))
      (ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)) (τ' : Perm (Fin r))
      (DN : Finset (Fin r)), S.PumpE e₀ L₀ F N r θN ρN τ' DN ∧
        N ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have hJH : J ≤ H := hJM.trans (sup_le hMH hMtH)
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have hte₀ : t ∈ centralizer ({e₀} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  obtain ⟨L₀, F, χ, DY, hL₀J, hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, hFD, hDY4, hFY⟩ :=
    S.exists_fixed_layer_seven he₀E he₀1
  have hFH : normalizer (F : Set X) ≤ H := by
    obtain ⟨DF, hDF, hFs⟩ := hFD
    have hFW := S.completion_eq_of_four h33 h35 hFJ (klein_of_card_sq hF4 hFsq) hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  have hL₀H : L₀ ≤ H := hL₀J.trans hJH
  obtain ⟨N, hNC, hNpc, hL₀N, hbr⟩ := exists_pump_data_seven hPump hN1 S.nonab S.kProper
    S.unbal S.notU (by norm_num) S.pair.2.2.2.1 he₀o S.pair.1.1 hte₀ hL₀C hL₀pc χ
  have hOH : coreNOf N ≤ H := (pPrimeCore_le_of_isPComponent hNC hNpc).trans hOC
  have hN : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  rcases hbr with ⟨r, hrodd, hr7, -, ⟨θN⟩, hfix, hpc⟩ | ⟨hfix, hpc, ⟨ψ⟩⟩ | ⟨hne', ⟨ψ⟩⟩
  ·
    exfalso
    have hr8 : r ≠ 8 := by
      rintro rfl
      exact (by decide : ¬ Odd 8) hrodd
    obtain ⟨ρN, τ', DN, P⟩ := S.exists_pumpG_of_data ht2 hte₀ le_rfl hL₀C hL₀pc χ
      hFL₀ hFJ hF4 hFsq hFD hDY4 hFY hNC hNpc hL₀N hr7 (by omega) θN (Or.inr ⟨hfix, hpc⟩)
    exact S.false_of_conj_eq_swap hCH hMH hMpc hne hJM θ hsmall he₀E he₀1
      (P.le_of_seven_le le_rfl hr8 hFH hL₀H hOH) hNC hNpc hfix
  ·
    exfalso
    have hL₀N' : L₀ ≤ N := by
      have h1 := hL₀N
      rwa [hfix, sup_idem] at h1
    have hNH : N ≤ H := He9.le_of_held_pump ht2 (mem_normalizer_iff_map_conj_eq.mpr hfix) hN
      (inf_le_right.trans hCH) hOH (le_inf hL₀N' (hL₀C.trans inf_le_left)) hpc χ hFL₀ hF4 hFsq
      hFH hDY4 hFY ψ
    exact S.false_of_conj_eq_swap hCH hMH hMpc hne hJM θ hsmall he₀E he₀1 hNH hNC hNpc hfix
  ·
    have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF4]; norm_num)
    have hNH : N ≤ H := le_of_diagonal ht2 hte₀ (inf_le_left.trans hCH) hOC hL₀C
      hL₀pc χ hFL₀ hF2 hFH hDY4 hFY hNC hNpc hL₀N hne' ψ
    have hθN : Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin 7)) := by
      rcases S.le_or_le_of_isPComponent_swap hCH hMH hMpc hne hJM hsmall he₀J he₀o hNH hNC
        hNpc with hNM | hNM
      · exact S.nonempty_coreQuot_of_le_swap hCH hMH hMpc hne hJM θ he₀E he₀1 hNM hNC hN ψ
      · set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
        have hMtt : Mt.map (MulAut.conj t).toMonoidHom = M := by
          rw [hMtdef, ← map_conj_mul, ht2]
          ext z
          simp
        have hne'' : Mt.map (MulAut.conj t).toMonoidHom ≠ Mt := by
          rw [hMtt]
          exact Ne.symm hne
        have hJM' : J ≤ Mt ⊔ Mt.map (MulAut.conj t).toMonoidHom := by
          rw [hMtt, sup_comm]
          exact hJM
        let θt : ↥Mt ⧸ pPrimeCore 2 ↥Mt ≃* alternatingGroup (Fin 11) :=
          (Sol78.coreQuotCongr (M.equivMapOfInjective (MulAut.conj t).toMonoidHom
            (MulAut.conj t).injective)).symm.trans θ
        exact S.nonempty_coreQuot_of_le_swap hCH hMtH hMtpc hne'' hJM' θt he₀E he₀1 hNM hNC hN ψ
    obtain ⟨θN⟩ := hθN
    obtain ⟨ρN, τ', DN, P⟩ := S.exists_pumpG_of_data ht2 hte₀ le_rfl hL₀C hL₀pc χ
      hFL₀ hFJ hF4 hFsq hFD hDY4 hFY hNC hNpc hL₀N le_rfl (by norm_num) θN (Or.inl rfl)
    exact ⟨L₀, F, N, 7, θN, ρN, τ', DN, P.toPumpE (by norm_num) hL₀J (by norm_num), hNH⟩

end Eleven

end Sig36

end CFSG.ComponentClassification.SolMax
