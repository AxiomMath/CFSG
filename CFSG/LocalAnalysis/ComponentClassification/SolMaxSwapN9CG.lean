module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CF

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

@[expose] def ExactFivePump (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) : Prop :=
  ∃ (F : Subgroup X) (DF : Finset (Fin n)) (f : X) (L N : Subgroup X),
    F ≤ J ∧ Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧ DF.card = 4 ∧
    (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) ∧
    f ∈ F ∧ f ≠ 1 ∧ L ≤ J ∧ L ≤ centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X) ∧
    IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X))) ∧
    Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin 5)) ∧
    N ≤ centralizer ({f} : Set X) ∧ IsPComponent 2 (N.subgroupOf (centralizer ({f} : Set X))) ∧
    L ≤ N ∧ conjBy N t = N ∧ L ⊔ core N ≠ N

end SwapP2

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_of_mem_E_swap_nine (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hn : n = 9)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) (hnex : ¬ SwapP2.ExactFivePump t J n e) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have hte₀ : t ∈ centralizer ({e₀} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have hMtt : Mt.map (MulAut.conj t).toMonoidHom = M := SwapN9.map_conj_map_conj_self M ht2
  have hne' : Mt.map (MulAut.conj t).toMonoidHom ≠ Mt := by rw [hMtt]; exact Ne.symm hne
  have hJM' : J ≤ Mt ⊔ Mt.map (MulAut.conj t).toMonoidHom := by rw [hMtt, sup_comm]; exact hJM
  let θt : ↥Mt ⧸ pPrimeCore 2 ↥Mt ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (M.equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective)).symm.trans θ
  have hJH : J ≤ H := hJM.trans (sup_le hMH hMtH)
  obtain ⟨L₀, F, P⟩ := S.exists_fiveLayer hn he₀E he₀1
  obtain ⟨DF, hDF, hFs⟩ := P.FD
  have hFH : normalizer (F : Set X) ≤ H := by
    have hFW := S.completion_eq_of_four h33 h35 (P.FL₀.trans P.L₀J) P.Fk hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  have hL₀Y : L₀ ≤ centralizer ({e₀} : Set X) ⊓ centralizer ({t} : Set X) := by
    rw [inf_comm]
    exact P.L₀C
  have hL₀pcY : IsPComponent 2 (L₀.subgroupOf
      (centralizer ({e₀} : Set X) ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]
    exact P.L₀pc
  obtain ⟨N, hNC, hNpc, hL₀N, -⟩ := exists_pump_in hte₀ S.pair.1.1 hL₀Y hL₀pcY
  by_cases hfix : N.map (MulAut.conj t).toMonoidHom = N
  · exfalso
    have hL₀N' : L₀ ≤ N := by
      have h1 := hL₀N
      rwa [hfix, sup_idem] at h1
    by_cases htriv : L₀ ⊔ SwapP2.core N = N
    ·
      have hNH : N ≤ H := by
        rw [← htriv]
        exact sup_le (P.L₀J.trans hJH) ((pPrimeCore_le_of_isPComponent hNC hNpc).trans hOC)
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
    · exact hnex ⟨E, D, e₀, L₀, N, S.le, S.klein, S.card, S.supp, he₀E, he₀1, P.L₀J, P.L₀C,
        P.L₀pc, P.type, hNC, hNpc, hL₀N', hfix, htriv⟩
  ·
    have hNH := S.le_of_diagonal_nine hCH hMH hMpc hne hJM θ he₀E he₀1 P hNC hNpc hL₀N hfix
    have hF2 : IsPGroup 2 F :=
      IsPGroup.of_card (n := 2) (by rw [(card_sq_of_klein P.Fk).1]; norm_num)
    have hFC : F ≤ centralizer ({e₀} : Set X) := P.FL₀.trans (P.L₀C.trans inf_le_right)
    have hFNN : F ≤ N ⊔ N.map (MulAut.conj t).toMonoidHom := P.FL₀.trans hL₀N
    rcases S.le_or_le_of_isPComponent_swap hCH hMH hMpc hne hJM hsmall he₀J he₀o hNH hNC
        hNpc with hNM | hNM
    · exact S.centralizer_le_of_le_nine hn hCH hMH hMpc hne hJM θ hsmall he₀E he₀1 hNC hNpc hNH
        hNM hfix hFNN hF2 hFC hFH
    · exact S.centralizer_le_of_le_nine hn hCH hMtH hMtpc hne' hJM' θt hsmall he₀E he₀1 hNC hNpc
        hNH hNM hfix hFNN hF2 hFC hFH

theorem centralizer_le_of_mem_four_swap_nine (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hn : n = 9)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {F : Subgroup X} (hFJ : F ≤ J)
    (hF : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    {DF : Finset (Fin n)} (hDF : DF.card = 4) (hFs : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω)
    {f : X} (hfF : f ∈ F) (hf1 : f ≠ 1) (hnex : ¬ SwapP2.ExactFivePump t J n e) :
    centralizer ({f} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  have hW := S.completion_eq_of_four h33 h35 hFJ hF hDF hFs
  have S' := S.ofFour hFJ hF hDF hFs
  rw [← hW] at hCH hMH hMpc ⊢
  exact S'.centralizer_le_of_mem_E_swap_nine h33 h35 hn hCH hMH hMpc hne hJM θ hsmall hfF hf1 hnex

end Sig36

namespace SwapP2

theorem claimANine_of_inputs (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35) :
    ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
      (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
      (M : Subgroup X), Setting t J n e E D M → n = 9 → ¬ ExactFivePump t J n e →
      ∀ F : Subgroup X, F ≤ J →
        Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      ∀ DF : Finset (Fin n), DF.card = 4 → (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
          ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) →
      ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E := by
  intro X _ _ _ t J n e E D M hs hn hnex F hFJ hF DF hDF hFs f hfF hf1
  obtain ⟨θ⟩ := hs.alt
  exact hs.sig.centralizer_le_of_mem_four_swap_nine h33 h35 hn hs.cent hs.le hs.pc hs.swap hs.diag θ
    hs.small hFJ hF hDF hFs hfF hf1 hnex

@[expose] def SwapMemberResidueNineExact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → n = 9 →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      (∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
        Nat.card P ≤ 2) →
      (∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
        R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
        R ≤ UnbalancedLayer.coreActionKernel M →
        ¬ centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      ExactFivePump t J n e →
      FooteLit.IsSolomonMember M

end SwapP2

end CFSG.ComponentClassification.SolMax
