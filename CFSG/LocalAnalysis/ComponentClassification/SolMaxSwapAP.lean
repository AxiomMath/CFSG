module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapAD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36W
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapAC

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem PumpE.normalizer_le_swap {S : Sig36 X t J n e E D} (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) {e₀ : X} {L₀ F N : Subgroup X} {r : ℕ}
    {θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)}
    {ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)} {τ' : Perm (Fin r)} {DN : Finset (Fin r)}
    (P : S.PumpE e₀ L₀ F N r θN ρN τ' DN) :
    normalizer (F : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  obtain ⟨DF, hDF, hFs⟩ := P.FD
  have hFW := S.completion_eq_of_four h33 h35 (P.FL₀.trans P.L₀J)
    (klein_of_card_sq P.F4 P.Fsq) hDF hFs
  have h1 := normalizer_le_normalizer_signalizerCompletion_self F
  rwa [hFW] at h1

variable (S : Sig36 X t J n e E D)
include S

theorem false_of_two_isPComponent_le_swap
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    (hn : 11 ≤ n) {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1)
    (hOC : (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map (centralizer ({e₀} : Set X)).subtype ≤
      normalizer (Sol78.signalizerCompletion E E : Set X))
    {T T' : Subgroup X} (hTM : T ≤ M) (hT'M : T' ≤ M)
    (hTH : T ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hT'H : T' ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hTC : T ≤ centralizer ({e₀} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({e₀} : Set X))))
    (hT'C : T' ≤ centralizer ({e₀} : Set X))
    (hT'pc : IsPComponent 2 (T'.subgroupOf (centralizer ({e₀} : Set X)))) (hTT' : T ≠ T')
    {r r' : ℕ} (hr : n - 6 ≤ r) (hr' : n - 6 ≤ r')
    (θT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin r))
    (θT' : ↥T' ⧸ pPrimeCore 2 ↥T' ≃* alternatingGroup (Fin r')) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, -⟩ := isPComponent_conj hMH hMpc htH
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hMH hMpc hne hJM
  have hJH : J ≤ H := hJM.trans (sup_le hMH hMtH)
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  set H' := H ⊓ normalizer (M : Set X) with hH'def
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀H' : e₀ ∈ H' := ⟨hJH he₀J, hJN he₀J⟩
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀4 : (ρ ⟨e₀, (inf_le_right : H' ≤ _) he₀H'⟩).support.card = 4 := by
    rw [S.card_support_rho_of_swap hCH hMH hMpc hne hJM θ hρ he₀J,
      S.card_support_coreImage_E he₀E he₀1]
  have hOH' : (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype ≤ H' := by
    intro o ho
    refine ⟨hOC ho, S.mem_normalizer_of_odd_swap hCH hMH hMpc hne hJM hsmall (hOC ho) ?_⟩
    obtain ⟨o', ho', rfl⟩ := ho
    have h1 : Odd (orderOf (⟨o', ho'⟩ : ↥(pPrimeCore 2 ↥(centralizer ({e₀} : Set X))))) :=
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat (orderOf_dvd_natCard _)
    rw [Subgroup.orderOf_mk] at h1
    rw [orderOf_injective _ (centralizer ({e₀} : Set X)).subtype_injective]
    exact h1
  have hnotK : ∀ {L : Subgroup X}, L ≤ M → L ≤ centralizer ({e₀} : Set X) →
      IsPComponent 2 (L.subgroupOf (centralizer ({e₀} : Set X))) →
      ¬ L ≤ UnbalancedLayer.coreActionKernel M := by
    intro L hLM hLC hLpc hLK
    have hLO : L ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
      mem_core_of_mem_coreActionKernel hρ (by omega) (hLM hz) (hLK hz)
    have h1 := card_dvd_of_le hLO
    rw [card_map_of_injective M.subtype_injective] at h1
    have h2 := two_dvd_card_of_isPComponent_in hLC hLpc
    have h3 := Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    exact absurd h3 (by
      rw [Nat.coprime_two_left]
      exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2))
  have hTN : T ≤ normalizer (M : Set X) := hTM.trans le_normalizer
  have hT'N : T' ≤ normalizer (M : Set X) := hT'M.trans le_normalizer
  have hTperf := UnbalancedCorr.commutator_eq_of_isPComponent hTC hTpc
  have hT'perf := UnbalancedCorr.commutator_eq_of_isPComponent hT'C hT'pc
  have hk := mem_coreNOf_of_rho_eq_one_of_not_le hρ hTN (by omega) θT hTperf
    (hnotK hTM hTC hTpc)
  have hk' := mem_coreNOf_of_rho_eq_one_of_not_le hρ hT'N (by omega) θT' hT'perf
    (hnotK hT'M hT'C hT'pc)
  exact false_of_two_components_of_ker hρ (by omega) (inf_le_right : H' ≤ _) he₀H' he₀2 he₀4 hOH'
    hTC hTpc hT'C hT'pc hTT' (le_inf hTH hTN) (le_inf hT'H hT'N) hr hr' hk hk' θT θT'

theorem centralizer_le_of_pumpE_swap (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hn : 11 ≤ n)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {L₀ F N : Subgroup X} {r : ℕ}
    {θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)}
    {ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)} {τ' : Perm (Fin r)} {DN : Finset (Fin r)}
    (P : S.PumpE e₀ L₀ F N r θN ρN τ' DN)
    (hNH : N ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have hMtt : Mt.map (MulAut.conj t).toMonoidHom = M := by
    rw [hMtdef, ← map_conj_mul, ht2]
    ext z
    simp
  have hJH : J ≤ H := hJM.trans (sup_le hMH hMtH)
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have hte₀ : t ∈ centralizer ({e₀} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  have hFH : normalizer (F : Set X) ≤ H := P.normalizer_le_swap h33 h35
  have hL₀H : L₀ ≤ H := P.L₀J.trans hJH
  have hr6 : 6 ≤ r := by have := P.kr; omega
  have hr : n - 6 ≤ r := by have := P.kr; omega
  have hne' : Mt.map (MulAut.conj t).toMonoidHom ≠ Mt := by rw [hMtt]; exact Ne.symm hne
  have hJM' : J ≤ Mt ⊔ Mt.map (MulAut.conj t).toMonoidHom := by rw [hMtt, sup_comm]; exact hJM
  let θt : ↥Mt ⧸ pPrimeCore 2 ↥Mt ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (M.equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective)).symm.trans θ
  set Nt := N.map (MulAut.conj t).toMonoidHom with hNtdef
  obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj P.NC P.Npc hte₀
  have hNtH : Nt ≤ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem htH (hNH hz)) (inv_mem htH)
  have hNsub := S.le_or_le_of_isPComponent_swap hCH hMH hMpc hne hJM hsmall he₀J he₀o hNH P.NC
    P.Npc
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hMtK : Mt ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMH hMtH hMpc hMtpc (Ne.symm hne)
  have hNt : Nt ≠ N := by
    intro hNN
    have hNMM : N ≤ M ⊓ Mt := by
      rcases hNsub with h | h
      · refine le_inf h ?_
        rw [← hNN]
        exact map_mono h
      · refine le_inf ?_ h
        rw [← hNN, ← hMtt]
        exact map_mono h
    have hNO : N ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
      mem_core_of_mem_coreActionKernel hρ (by omega) (hNMM hz).1 (hMtK (hNMM hz).2)
    have h1 := card_dvd_of_le hNO
    rw [card_map_of_injective M.subtype_injective] at h1
    have h2 := two_dvd_card_of_isPComponent_in P.NC P.Npc
    have h3 := Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    exact absurd h3 (by
      rw [Nat.coprime_two_left]
      exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2))
  have hfrat : ∀ y, y ∈ normalizer (N : Set X) → y ∈ normalizer (Nt : Set X) → y ∈ H :=
    fun y h1 h2 => P.mem_of_mem_normalizer_pair hr6 ht2 hte₀ hNt hNH htH hFH hL₀H hOC h1 h2
  have hNtsub := S.le_or_le_of_isPComponent_swap hCH hMH hMpc hne hJM hsmall he₀J he₀o hNtH
    hNtC hNtpc
  let θNt : ↥Nt ⧸ pPrimeCore 2 ↥Nt ≃* alternatingGroup (Fin r) :=
    (Sol78.coreQuotCongr (N.equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective)).symm.trans θN
  have hconj : ∀ g ∈ centralizer ({e₀} : Set X),
      N.map (MulAut.conj g).toMonoidHom = N ∨ N.map (MulAut.conj g).toMonoidHom = Nt := by
    intro g hg
    by_contra hor
    push Not at hor
    obtain ⟨h1, h2⟩ := hor
    set Ng := N.map (MulAut.conj g).toMonoidHom with hNgdef
    obtain ⟨hNgC, hNgpc⟩ := isPComponent_conj P.NC P.Npc hg
    have hNgK : Ng ≤ UnbalancedLayer.coreActionKernel N :=
      GSThmB.B5a.le_coreActionKernel_of_ne P.NC hNgC P.Npc hNgpc (Ne.symm h1)
    have hNgKt : Ng ≤ UnbalancedLayer.coreActionKernel Nt :=
      GSThmB.B5a.le_coreActionKernel_of_ne hNtC hNgC hNtpc hNgpc (Ne.symm h2)
    have hNgH : Ng ≤ H := fun z hz => hfrat z (hNgK hz).1 (hNgKt hz).1
    have hNgsub := S.le_or_le_of_isPComponent_swap hCH hMH hMpc hne hJM hsmall he₀J he₀o hNgH
      hNgC hNgpc
    let θNg : ↥Ng ⧸ pPrimeCore 2 ↥Ng ≃* alternatingGroup (Fin r) :=
      (Sol78.coreQuotCongr (N.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective)).symm.trans θN
    have hcase : ∀ T, T ≤ M → T = N ∨ T = Nt → Ng ≤ M → False := by
      intro T hTM hT hNgM
      have hTH : T ≤ H := by rcases hT with rfl | rfl; exacts [hNH, hNtH]
      have hTC : T ≤ centralizer ({e₀} : Set X) := by rcases hT with rfl | rfl; exacts [P.NC, hNtC]
      have hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({e₀} : Set X))) := by
        rcases hT with rfl | rfl; exacts [P.Npc, hNtpc]
      have hTne : Ng ≠ T := by rcases hT with rfl | rfl; exacts [h1, h2]
      have θT : Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin r)) := by
        rcases hT with rfl | rfl; exacts [⟨θN⟩, ⟨θNt⟩]
      obtain ⟨θT⟩ := θT
      exact S.false_of_two_isPComponent_le_swap hCH hMH hMpc hne hJM θ hsmall (by omega) he₀E he₀1
        hOC hNgM hTM hNgH hTH hNgC hNgpc hTC hTpc hTne hr hr θNg θT
    have hcaset : ∀ T, T ≤ Mt → T = N ∨ T = Nt → Ng ≤ Mt → False := by
      intro T hTM hT hNgM
      have hTH : T ≤ H := by rcases hT with rfl | rfl; exacts [hNH, hNtH]
      have hTC : T ≤ centralizer ({e₀} : Set X) := by rcases hT with rfl | rfl; exacts [P.NC, hNtC]
      have hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({e₀} : Set X))) := by
        rcases hT with rfl | rfl; exacts [P.Npc, hNtpc]
      have hTne : Ng ≠ T := by rcases hT with rfl | rfl; exacts [h1, h2]
      have θT : Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin r)) := by
        rcases hT with rfl | rfl; exacts [⟨θN⟩, ⟨θNt⟩]
      obtain ⟨θT⟩ := θT
      exact S.false_of_two_isPComponent_le_swap hCH hMtH hMtpc hne' hJM' θt hsmall (by omega) he₀E
        he₀1 hOC hNgM hTM hNgH hTH hNgC hNgpc hTC hTpc hTne hr hr θNg θT
    have hNtM : N ≤ M → Nt ≤ Mt := fun h => map_mono h
    have hNtM' : N ≤ Mt → Nt ≤ M := fun h => by rw [← hMtt]; exact map_mono h
    rcases hNgsub with hNgM | hNgM <;> rcases hNsub with hNM | hNM
    · exact hcase N hNM (Or.inl rfl) hNgM
    · exact hcase Nt (hNtM' hNM) (Or.inr rfl) hNgM
    · exact hcaset Nt (hNtM hNM) (Or.inr rfl) hNgM
    · exact hcaset N hNM (Or.inl rfl) hNgM
  have hNtt : Nt.map (MulAut.conj t).toMonoidHom = N := by
    rw [hNtdef, ← map_conj_mul, ht2]
    ext z
    simp
  have hboth : ∀ g ∈ centralizer ({e₀} : Set X), N.map (MulAut.conj g).toMonoidHom = N →
      g ∈ normalizer (N : Set X) ∧ g ∈ normalizer (Nt : Set X) := by
    intro g hg hgN
    refine ⟨mem_normalizer_iff_map_conj_eq.mpr hgN, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    change Nt.map (MulAut.conj g).toMonoidHom = Nt
    rcases hconj (g * t) (mul_mem hg hte₀) with h | h
    · exfalso
      apply hNt
      have h3 : Nt.map (MulAut.conj g).toMonoidHom = N := by rw [hNtdef, ← map_conj_mul, h]
      rw [← hgN] at h3
      exact map_injective (MulAut.conj g).injective h3
    · rw [hNtdef, ← map_conj_mul, h]
  intro g hg
  rcases hconj g hg with h | h
  · obtain ⟨h1, h2⟩ := hboth g hg h
    exact hfrat g h1 h2
  · have htg : N.map (MulAut.conj (t * g)).toMonoidHom = N := by rw [map_conj_mul, h, hNtt]
    obtain ⟨h1, h2⟩ := hboth (t * g) (mul_mem hte₀ hg) htg
    have h3 := mul_mem (inv_mem htH) (hfrat _ h1 h2)
    rwa [inv_mul_cancel_left] at h3

end Sig36

end CFSG.ComponentClassification.SolMax
