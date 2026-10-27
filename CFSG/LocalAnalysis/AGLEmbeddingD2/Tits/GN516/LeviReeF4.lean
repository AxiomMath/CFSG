module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviDecomp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviResidualFinal
public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelLevi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParReeF4
public import CFSG.RankThree.PartOne.K133X.F4

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LocalAnalysis.EvenBN.TwoF4 CFSG.Open CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


theorem leviAlt_levi_data (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {P V : Subgroup (ModGL F4.tag K)} (i : Idx)
    (hi : i.isCenter = false) (hP : P = V ⊔ leviN K a i ⊔ torusHi K a i)
    (hVn : P ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K))) (hV2 : IsPGroup 2 ↥V) :
    LeviAlt ↥(pElementSubgroup 2 P) := by
  obtain ⟨-, h2, -⟩ := (miyamoto_2_2 ha hK hi)
  obtain ⟨hs, hna⟩ := isSimpleGroup_leviN ha hK i
  have hSyl := isSylowOf_rootV_leviN ha hK hi
  obtain ⟨Q, hQ⟩ := hSyl
  have hV0 : IsPGroup 2 ↥(rootV K a i) := hQ ▸ Q.isPGroup'.map _
  refine leviAlt_pElement_of_levi_decomp hP hVn hV2 hs hna
    (le_pElementSubgroup_of_simple hs (rootV_le_leviN hK i) hV0 (rootV_ne_bot hK i)) ?_ ?_
  · intro x hx
    have hcomm : ∀ m ∈ leviN K a i, x * m = m * x := fun m hm =>
      Subgroup.mem_centralizer_iff.1 (h2 hm) x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hcomm n hn]
      simpa using hn
    · intro h
      have h' := hcomm _ h
      have e : x * n * x⁻¹ = n := mul_left_cancel (a := x) (by rw [h']; group)
      rwa [e] at h
  · rw [card_torusHi hK i]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one

theorem leviAlt_reeLocalParabolic_zero (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    LeviAlt ↥(pElementSubgroup 2 (F4.reeLocalParabolic K a ⟨0, by decide⟩)) := by
  obtain ⟨-, hB, -, hD⟩ := miyamoto_2_3 ha hK
  have hV2 : IsPGroup 2 ↥(radS K a) :=
    IsPGroup.of_card (n := (2 * a + 1) * 11) (by rw [(radS_spec hK).2.2.1, pow_mul])
  refine leviAlt_levi_data ha hK .i3 rfl (hD.symm.trans hB) ?_ hV2
  rw [← hD]
  exact inf_le_right

theorem leviAlt_reeLocalParabolic_one (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    LeviAlt ↥(pElementSubgroup 2 (F4.reeLocalParabolic K a ⟨1, by decide⟩)) := by
  obtain ⟨hA, -, hC, -⟩ := miyamoto_2_3 ha hK
  have hV2 : IsPGroup 2 ↥(radR K a) :=
    IsPGroup.of_card (n := (2 * a + 1) * 10) (by rw [(radR_spec hK).2.2.1, pow_mul])
  refine leviAlt_levi_data ha hK .i1 rfl (hC.symm.trans hA) ?_ hV2
  rw [← hC]
  exact inf_le_right

theorem leviAlt_pElement_subgroupOf {G : Type} [Group G] [Finite G] {Γ P : Subgroup G}
    (hP : P ≤ Γ) (h : LeviAlt ↥(pElementSubgroup 2 P)) :
    LeviAlt ↥(pElementSubgroup 2 (P.subgroupOf Γ)) := by
  have e1 := pElementSubgroup_map_injective Γ.subtype Γ.subtype_injective (P.subgroupOf Γ)
  rw [Subgroup.map_subgroupOf_eq_of_le hP] at e1
  have h1 := leviAlt_of_mulEquiv (MulEquiv.subgroupCongr e1) h
  exact leviAlt_of_mulEquiv
    (Subgroup.equivMapOfInjective (pElementSubgroup 2 (P.subgroupOf Γ)) Γ.subtype
      Γ.subtype_injective).symm h1

structure TwoParLevi (S : Type) [Group S] (T P₁ P₂ : Subgroup S) : Prop where
  tp : TwoPar S T P₁ P₂
  l₁ : LeviAlt ↥(pElementSubgroup 2 P₁)
  l₂ : LeviAlt ↥(pElementSubgroup 2 P₂)

section TwoParLevi

variable {S S' : Type} [Group S] [Group S']

theorem TwoParLevi.map (e : S ≃* S') {T P₁ P₂ : Subgroup S} (h : TwoParLevi S T P₁ P₂) :
    TwoParLevi S' (T.map e.toMonoidHom) (P₁.map e.toMonoidHom) (P₂.map e.toMonoidHom) := by
  have hl : ∀ P : Subgroup S, LeviAlt ↥(pElementSubgroup 2 P) →
      LeviAlt ↥(pElementSubgroup 2 (P.map e.toMonoidHom)) := fun P hP => by
    rw [CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.pElementSubgroup_map_equiv e P]
    exact leviAlt_of_mulEquiv (e.subgroupMap _) hP
  exact ⟨h.tp.map e, hl _ h.l₁, hl _ h.l₂⟩

theorem TwoParLevi.exists_of_equiv [Finite S'] (e : S ≃* S') {T P₁ P₂ : Subgroup S}
    (h : TwoParLevi S T P₁ P₂) {T' : Subgroup S'} (hT' : IsSylowTwoOf T' ⊤) :
    ∃ P₁' P₂' : Subgroup S', TwoParLevi S' T' P₁' P₂' := by
  have h1 := h.map e
  obtain ⟨g, hg⟩ := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.exists_conj_of_sylowTwo h1.tp.sylow hT'
  rw [← hg]
  exact ⟨_, _, h1.map (MulAut.conj g)⟩

theorem minLevi_of_twoParLevi {Y : Type} [Group Y] [Finite Y] (e : Y ≃* S)
    (h : ∃ T P₁ P₂ : Subgroup S, TwoParLevi S T P₁ P₂) : MinLevi Y := by
  intro _ T Q hT hQ hne
  obtain ⟨T₀, P₁, P₂, h⟩ := h
  obtain ⟨P₁', P₂', h'⟩ := TwoParLevi.exists_of_equiv e.symm h hT
  have hNQ : Subgroup.normalizer (T : Set Y) ≤ Q := by simpa using hQ.2.1.le
  rcases h'.tp.hover Q hNQ with e1 | e1 | e1 | e1
  · exact absurd hQ.2.1 (by rw [top_inf_eq, e1]; exact lt_irrefl _)
  · rw [e1]; exact h'.l₁
  · rw [e1]; exact h'.l₂
  · exact absurd e1 hne

end TwoParLevi

theorem reeF4MinLevi_proved :
    ReeF4MinLevi := by
  intro Y _ _ m hv e
  obtain ⟨-, hmodel⟩ := CFSG.RankThree.PartOne.K133X.reeTitsModel_twistedF4_of_isoLie
    (X := Y) (m := m) ⟨hv, ⟨e⟩⟩
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hmodel
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, -, hC, hD⟩ := miyamoto_2_3 ha hK'
  refine minLevi_of_twoParLevi e' ⟨_, _, _, ⟨twoPar_reeF4 ha hK', ?_, ?_⟩⟩
  · exact leviAlt_pElement_subgroupOf (hD ▸ inf_le_left) (leviAlt_reeLocalParabolic_zero ha hK')
  · exact leviAlt_pElement_subgroupOf (hC ▸ inf_le_left) (leviAlt_reeLocalParabolic_one ha hK')

end CFSG.AGLEmbeddingD2.Tits.GN516
