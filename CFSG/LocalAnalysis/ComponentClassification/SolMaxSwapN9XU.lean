module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9Defs
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9D

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

section Exact

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M F : Subgroup X} {DF : Finset (Fin n)} {f : X} {L N : Subgroup X}

private theorem le_of_isPComponent_inf (hs : Setting t J n e E D M) (hfJ : f ∈ J)
    (hf : orderOf f = 2) {T : Subgroup X}
    (hTC : T ≤ centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X))
    (hTpc : IsPComponent 2
      (T.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X)))) : T ≤ J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJC : J ≤ centralizer ({t} : Set X) := hs.sig.pair.1.2.1
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set X))) :=
    hs.sig.pair.1.2.2.1
  obtain ⟨K, hKC, hKpc, hTK, -⟩ := exists_pump_in (hJC hfJ) hf hTC hTpc
  have hKJ : K = J := by
    by_contra hne
    have hKker : K ≤ UnbalancedLayer.coreActionKernel J :=
      GSThmB.B5a.le_coreActionKernel_of_ne hJC hKC hJpc hKpc (Ne.symm hne)
    have h4 : 4 ∣ Nat.card K := GSThmB.Cent516.four_dvd_card_of_perfect
      (UnbalancedCorr.commutator_eq_of_isPComponent hKC hKpc)
      (two_dvd_card_of_isPComponent_in hKC hKpc)
    obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2) (G := ↥K)
      (by norm_num; exact h4)
    set P := P₀.map K.subtype with hPdef
    have hPcard : Nat.card P = 4 := by
      rw [hPdef, card_map_of_injective K.subtype_injective, hP₀]
      norm_num
    have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 2) (by rw [hPcard]; norm_num)
    have h1 := hs.small P ((map_subtype_le _).trans hKker) hP2
    omega
  have hJf : J.map (MulAut.conj f).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hfJ)
  rw [hKJ, hJf, sup_idem] at hTK
  exact hTK

theorem ExactData.unique_layer (hs : Setting t J n e E D M) (hn : n = 9)
    (hx : ExactData t J n e F DF f L N) :
    ∀ T : Subgroup X, T ≤ N → T ≤ centralizer ({t} : Set X) →
      IsPComponent 2 (T.subgroupOf (centralizer ({f} : Set X) ⊓ centralizer ({t} : Set X))) →
      T = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJC : J ≤ centralizer ({t} : Set X) := hs.sig.pair.1.2.1
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set X))) :=
    hs.sig.pair.1.2.2.1
  have hfJ : f ∈ J := hx.FJ hx.fF
  have hfN : f ∈ normalizer (J : Set X) := le_normalizer hfJ
  have hf2 : f * f = 1 := by rw [← sq]; exact (card_sq_of_klein hx.Fk).2 f hx.fF
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := J) (by omega) (by omega) e
  have hρf : ρ ⟨f, hfN⟩ = coreImage e hfJ := hρ.apply_of_mem (by omega) ⟨f, hfJ⟩
  have hsupp : (coreImage e hfJ).support ⊆ DF := by
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (hx.Fs ⟨f, hfJ⟩ hx.fF ω hωD)
  have h4 : (ρ ⟨f, hfN⟩).support.card ≤ 4 := by
    rw [hρf]
    exact (Finset.card_le_card hsupp).trans hx.DFc.le
  have h5 : 5 ≤ n - (ρ ⟨f, hfN⟩).support.card := by omega
  obtain ⟨hflC, hflpc, -⟩ := SwapN9.fixedLayer_data hJC hJpc hρ hfN hf2 h4 h5 rfl
  have key : ∀ T : Subgroup X, T ≤ J →
      T ≤ centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X) →
      IsPComponent 2
        (T.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X))) →
      T = GSLit.fixedLayer J (zpowers f) := by
    intro T hTJ hTC hTpc
    have hperf : ⁅T, T⁆ = T := UnbalancedCorr.commutator_eq_of_isPComponent hTC hTpc
    obtain ⟨-, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T _ hTC).mp hTpc
    have hTfl : T ≤ GSLit.fixedLayer J (zpowers f) :=
      le_fixedLayer_of_perfect_of_perm hJC hJpc hρ hfN hf2 h4 h5 hTJ
        (hTC.trans inf_le_right) hperf hres
    exact eq_of_isPComponent_of_le_inf hTC hflC hTpc hflpc le_rfl hTfl hperf
      (LocalCores.isQuasisimple_nontrivial hq)
  intro T hTN hTt hTpc
  have hTC : T ≤ centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X) :=
    le_inf hTt (hTN.trans hx.NC)
  have hTpc' : IsPComponent 2
      (T.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X))) := by
    rw [inf_comm]
    exact hTpc
  exact (key T (le_of_isPComponent_inf hs hfJ hx.orderOf_f hTC hTpc') hTC hTpc').trans
    (key L hx.LJ hx.LC hx.Lpc).symm

end Exact

end CFSG.ComponentClassification.SolMax.SwapP2
