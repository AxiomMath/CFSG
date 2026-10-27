module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueDefs
public import CFSG.LocalAnalysis.ComponentClassification.GS82TheoremDTyp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.Residue

open CFSG Subgroup HarrisLit.T1.SporRow

theorem card_quot_dvd {Y : Type*} [Group Y] [Finite Y] (T : Subgroup Y) :
    Nat.card (↥T ⧸ pPrimeCore 2 ↥T) ∣ Nat.card (Y ⧸ pPrimeCore 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥T →* Y ⧸ pPrimeCore 2 Y := (QuotientGroup.mk' (pPrimeCore 2 Y)).comp T.subtype
  have hk : φ.ker = (pPrimeCore 2 Y).comap T.subtype := by
    ext x
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hker : φ.ker ≤ pPrimeCore 2 ↥T := by
    rw [hk]
    exact le_sSup ⟨inferInstance, Nat.Coprime.coprime_dvd_right
      (card_comap_dvd_of_injective _ _ T.subtype_injective) pPrimeCore_coprime_card⟩
  calc Nat.card (↥T ⧸ pPrimeCore 2 ↥T) = (pPrimeCore 2 ↥T).index := (index_eq_card _).symm
    _ ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
    _ = Nat.card φ.range := by
        rw [index_eq_card]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    _ ∣ Nat.card (Y ⧸ pPrimeCore 2 Y) := Subgroup.card_subgroup_dvd_card _

theorem card_quot_dvd_of_le {X : Type} [Group X] [Finite X] {T K : Subgroup X} (h : T ≤ K) :
    Nat.card (↥T ⧸ pPrimeCore 2 ↥T) ∣ Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := by
  rw [← Nat.card_congr (Sol78.coreQuotCongr (subgroupOfEquivOfLe h)).toEquiv]
  exact card_quot_dvd (T.subgroupOf K)

theorem card_of_isSLTwoOver {q : ℕ} {A : Type} [Group A] (h : HarrisLit.IsSLTwoOver q A) :
    Nat.card A = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    Nat.card_eq_fintype_card, hF]

theorem oddLieType_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Blueprint.OddLieType A) : Blueprint.OddLieType B := by
  obtain ⟨t, n, p, f, hp, hp2, ha, hm⟩ := h
  exact ⟨t, n, p, f, hp, hp2, ha, Blueprint.LieModel.of_mulEquiv e hm⟩

theorem coreInvariant_typQ (q₀ : ℕ) : CoreInvariant (TypQ q₀) := by
  rintro A B _ _ ⟨e⟩ ⟨hA, hd⟩
  refine ⟨?_, by rwa [← Nat.card_congr e.toEquiv]⟩
  rcases hA with h | ⟨n, hn, h⟩
  · exact Or.inl (oddLieType_of_mulEquiv (Sol78.fusionZStarQuotOfCore e) h)
  · exact Or.inr ⟨n, hn, isDoubleCoverOfAlt_of_mulEquiv e h⟩

theorem coreInvariant_typL16 : CoreInvariant TypL16 := by
  rintro A B _ _ ⟨e⟩ ⟨hL, hc⟩
  refine ⟨Blueprint.LieModel.of_mulEquiv (Sol78.centerQuotCongr e) hL, ?_⟩
  rw [← Sol78.map_center_eq_of_mulEquiv e, Subgroup.card_map_of_injective e.injective]
  exact hc

theorem diagonalTransfer_typQ (q₀ : ℕ) : DiagonalTransfer q₀ (TypQ q₀) := by
  rintro A B _ _ _ _ hAq hBq ⟨hA, -⟩ ⟨e⟩ N hNp hNSL c hc hcN hNc hcZ
  refine ⟨?_, ?_⟩
  · rcases hA with h | ⟨n, hn, h⟩
    · exact Or.inl (oddLieType_of_mulEquiv e h)
    · exact Or.inr (diagonalTransfer_twoAltTyp q₀ (n := 7) (by norm_num) A B hAq hBq ⟨n, hn, h⟩
        ⟨e⟩ N hNp hNSL c hc hcN hNc hcZ)
  · rw [← card_of_isSLTwoOver hNSL]
    exact card_quot_dvd N

theorem card_of_l34 {S : Type} [Group S]
    (h : Blueprint.LieModel S .PSL 3 2 2) : Nat.card S = 20160 := by
  have hstated : Assembly.LowTwoRank.StatedClassicalModel S .PSL 3 2 2 := by
    rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  obtain ⟨θ⟩ := PSL3Four.nonempty_equiv_of_stated S hstated
  rw [Nat.card_congr θ.toEquiv, PSL3Four.card_S]

theorem not_oddLieOrder_l34 : ¬ OddLieOrder 20160 :=
  not_oddLieOrder_of_check (l := [(2, 6), (3, 2), (5, 1), (7, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieType_of_l34
    {S : Type} [Group S] (h : Blueprint.LieModel S .PSL 3 2 2) : ¬ Blueprint.OddLieType S := by
  rintro ⟨t, n, p, f, hp, hp2, -, hm⟩
  have h1 := oddLieOrder_of_lieModel hp hp2 hm
  rw [card_of_l34 h] at h1
  exact not_oddLieOrder_l34 h1

end CFSG.ComponentClassification.GS82PumpInputs.Residue
