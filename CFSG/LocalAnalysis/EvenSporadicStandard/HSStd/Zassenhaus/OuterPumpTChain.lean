module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTChainVertical
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTChainTable
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainA8

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G]

theorem invariant_of_reflTransGen {P : Subgroup G → Prop}
    (hstep : ∀ K L : Subgroup G, LtF K L → P K → P L) {K₀ M : Subgroup G}
    (h : ReflTransGen LtF K₀ M) (hp : P K₀) : P M := by
  induction h with
  | refl => exact hp
  | tail _ h ih => exact hstep _ _ h ih

theorem l4Type_of_ltF [Finite G] (ctx : PumpCtx G) (hT : KGPumpTableT) {K L : Subgroup G}
    (h : LtF K L) (hp : ∃ i : ℕ, 1 ≤ i ∧ LieModel (↥K ⧸ center ↥K) .PSL 4 2 (2 ^ i)) :
    ∃ i : ℕ, 1 ≤ i ∧ LieModel (↥L ⧸ center ↥L) .PSL 4 2 (2 ^ i) := by
  obtain ⟨i, hi, hL⟩ := hp
  rcases ltF_stepT ctx hT h with ⟨⟨e⟩⟩ | ⟨-, -, -, -, -, -, h6⟩
  · exact ⟨i, hi, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hL⟩
  · exact ⟨i + 1, by omega, h6 i hi hL⟩

theorem l4Type_of_reflTransGen [Finite G] (ctx : PumpCtx G) (hT : KGPumpTableT)
    {K₀ M : Subgroup G} (h : ReflTransGen LtF K₀ M)
    (hp : ∃ i : ℕ, 1 ≤ i ∧ LieModel (↥K₀ ⧸ center ↥K₀) .PSL 4 2 (2 ^ i)) :
    ∃ i : ℕ, 1 ≤ i ∧ LieModel (↥M ⧸ center ↥M) .PSL 4 2 (2 ^ i) :=
  invariant_of_reflTransGen (fun _ _ hl hK => l4Type_of_ltF ctx hT hl hK) h hp

theorem a8_of_ltF [Finite G]
    (ctx : PumpCtx G) (hT : KGPumpTableT) {K L : Subgroup G}
    (h : LtF K L) (hp : PumpType (↥K ⧸ center ↥K))
    (hA : Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 8))) :
    Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨s, t, hs, ht, hst, hK, hL, hKL⟩ := h
  by_cases hLe : L.map (MulAut.conj s).toMonoidHom = L
  · rcases vertical_table ctx (kgPumpTable_of_T hT) hs ht hK hL hLe (le_of_conj_eq hLe hKL) hp
      with rfl | ⟨-, hn, -⟩
    · exact hA
    · exact absurd hA hn
  · obtain ⟨e⟩ := nonempty_quotient_center_equiv_of_ltF_ne hs hst hK hL hKL hLe
    obtain ⟨f⟩ := hA
    exact ⟨e.symm.trans f⟩

theorem a8_of_reflTransGen [Finite G]
    (ctx : PumpCtx G) (hT : KGPumpTableT) {K' K : Subgroup G}
    (h : ReflTransGen LtF K' K) (hp : PumpType (↥K' ⧸ center ↥K'))
    (hA : Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8))) :
    Nonempty (↥K' ⧸ center ↥K' ≃* alternatingGroup (Fin 8)) := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact hA
  | head hl _ ih =>
    exact a8_of_ltF ctx hT hl hp (ih (pumpType_of_ltF ctx (kgPumpTable_of_T hT) hl hp))

theorem a8Partner_of_a8Type [Finite G]
    (ctx : PumpCtx G)
    (hT : KGPumpTableT) {K₀ K : Subgroup G} (hp₀ : PumpType (↥K₀ ⧸ center ↥K₀))
    (hK : K = K₀ ∨ TransGen LtF K₀ K)
    (e : Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8))) : A8Partner K₀ K := by
  have hTab := kgPumpTable_of_T hT
  refine ⟨e, ?_⟩
  by_cases hK0 : K = K₀
  · exact Or.inl hK0
  right
  have hTr : TransGen LtF K₀ K := hK.resolve_left hK0
  obtain ⟨K', hK'K, hK'0, s', t', hs', ht', hst', hK's, hKt', hK'le⟩ :=
    exists_pred_of_transGen hTr (Ne.symm hK0)
  have hpK' : PumpType (↥K' ⧸ center ↥K') := by
    rcases hK'0 with rfl | hT'
    · exact hp₀
    · exact pumpType_of_transGen ctx hTab hT' hp₀
  have hKs : K.map (MulAut.conj s').toMonoidHom ≠ K := by
    intro hKe
    rcases vertical_table ctx hTab hs' ht' hK's hKt' hKe (le_of_conj_eq hKe hK'le) hpK'
      with h | ⟨-, hn, -⟩
    · exact hK'K h
    · exact hn e
  exact ⟨s', t', hs', ht', hst', hKt', hKs, commutator_conj_eq_bot_of_ne hst' hKt' hKs⟩

theorem a10_partner [Finite G]
    (ctx : PumpCtx G) (hT : KGPumpTableT) {K₀ M : Subgroup G}
    (hp₀ : PumpType (↥K₀ ⧸ center ↥K₀)) (hch : TransGen LtF K₀ M) (hne : K₀ ≠ M)
    (hstd : StdBare M)
    (hA10 : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 10))) :
    ∃ (K : Subgroup G) (s t : G), LastLink K₀ M K s t ∧ A8Partner K₀ K := by
  obtain ⟨K, s, t, hl⟩ := exists_last_link hch hne hstd
  have hpK : PumpType (↥K ⧸ center ↥K) := by
    rcases hl.chain with rfl | hTr
    · exact hp₀
    · exact pumpType_of_transGen ctx (kgPumpTable_of_T hT) hTr hp₀
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vertical_tableT ctx hT hl.s_order hl.t_order hl.comp_K
    hl.comp_M hl.conj_eq hl.le hl.ne
  have hA8 : Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8)) := by
    rcases hpK with ⟨k, hk, hQ⟩ | hHS | hMcL | hHN | ⟨i, hi, hL⟩
    · rcases (by omega : k = 4 ∨ 5 ≤ k) with rfl | hk5
      · exact hQ
      · exfalso
        rcases h2 k hk5 hQ with ⟨m, hm, hS⟩ | ⟨-, hS⟩
        · have := alt_degree_unique (by omega) (by omega) hS hA10
          omega
        · exact not_alt_of_hn (by norm_num) hS hA10
    · exact absurd (h3 hHS) (fun hS => not_alt_of_hn (by norm_num) hS hA10)
    · exact absurd hMcL h4
    · exact absurd hHN h5
    · exact absurd hA10 (not_alt_of_lieModel_psl_four (i := i + 1) (n := 10) (by omega)
        (by norm_num) (by norm_num [Nat.factorial]) (h6 i hi hL))
  exact ⟨K, s, t, hl, a8Partner_of_a8Type ctx hT hp₀ hl.chain hA8⟩

theorem last_link_of_a10_or_hs [Finite G]
    (ctx : PumpCtx G)
    (hT : KGPumpTableT) {K₀ M : Subgroup G} (hp₀ : PumpType (↥K₀ ⧸ center ↥K₀))
    (hch : TransGen LtF K₀ M) (hne : K₀ ≠ M) (hstd : StdBare M)
    (hM : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 10)) ∨
      IsSporadic (↥M ⧸ center ↥M) .HS) :
    ∃ (K : Subgroup G) (s t : G), LastLink K₀ M K s t ∧ A8Partner K₀ K ∧
      Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8)) ∧
      ∀ K' : Subgroup G, ReflTransGen LtF K₀ K' → ReflTransGen LtF K' K →
        Nonempty (↥K' ⧸ center ↥K' ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨K, s, t, hl, hP⟩ : ∃ (K : Subgroup G) (s t : G), LastLink K₀ M K s t ∧ A8Partner K₀ K := by
    rcases hM with hA10 | hHS
    · exact a10_partner ctx hT hp₀ hch hne hstd hA10
    · exact a8_partner ctx (kgPumpTable_of_T hT) hp₀ hch hne hstd hHS
  refine ⟨K, s, t, hl, hP, hP.quot, fun K' h0 h1 => ?_⟩
  have hp' : PumpType (↥K' ⧸ center ↥K') := by
    rcases h0.cases_head with rfl | ⟨c, hc, hcK'⟩
    · exact hp₀
    · exact pumpType_of_transGen ctx (kgPumpTable_of_T hT)
        (TransGen.head' hc hcK') hp₀
  exact a8_of_reflTransGen ctx hT h1 hp' hP.quot

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
