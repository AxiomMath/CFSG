module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP2

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

private theorem map_subtype_subgroupOf_eq {Y N : Subgroup X} (hNY : N ≤ Y) :
    (N.subgroupOf Y).map Y.subtype = N := by
  rw [subgroupOf_map_subtype]
  exact inf_eq_left.mpr hNY

private theorem map_core_subgroupOf_eq {Y N : Subgroup X} (hNY : N ≤ Y) :
    ((pPrimeCore 2 ↥(N.subgroupOf Y)).map (N.subgroupOf Y).subtype).map Y.subtype = core N := by
  have h := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hNY)
  show _ = (pPrimeCore 2 ↥N).map N.subtype
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem centralizer_mk_eq_inf {Y : Subgroup X} {x : X} (hxY : x ∈ Y) :
    centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y) =
      (Y ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
  rw [centralizer_mk_eq hxY, inf_comm]

private theorem layer_data [Finite X] {Y N T : Subgroup X} {x : X} (hxY : x ∈ Y)
    (hTN : T ≤ N)
    (hTC : T ≤ centralizer ({x} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (Y ⊓ centralizer ({x} : Set X)))) :
    T.subgroupOf Y ≤ N.subgroupOf Y ∧
      T.subgroupOf Y ≤ centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y) ∧
      IsPComponent 2 ((T.subgroupOf Y).subgroupOf (centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y))) := by
  have hcent := centralizer_mk_eq_inf hxY
  refine ⟨subgroupOf_mono Y hTN, ?_, ?_⟩
  · rw [hcent]
    intro y hy
    rw [mem_subgroupOf, mem_inf]
    exact ⟨y.2, hTC (mem_subgroupOf.mp hy)⟩
  · rw [hcent, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two]
    exact hTpc

private theorem layer_back [Finite X] {Y N : Subgroup X} {x : X} (hxY : x ∈ Y)
    (hNY : N ≤ Y)
    {T' : Subgroup ↥Y} (h1 : T' ≤ N.subgroupOf Y)
    (h2 : T' ≤ centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y))
    (h3 : IsPComponent 2 (T'.subgroupOf (centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y)))) :
    T'.map Y.subtype ≤ N ∧ T'.map Y.subtype ≤ centralizer ({x} : Set X) ∧
      IsPComponent 2 ((T'.map Y.subtype).subgroupOf (Y ⊓ centralizer ({x} : Set X))) ∧
      (T'.map Y.subtype).subgroupOf Y = T' := by
  have hcent := centralizer_mk_eq_inf hxY
  have hrec : (T'.map Y.subtype).subgroupOf Y = T' :=
    comap_map_eq_self_of_injective Y.subtype_injective T'
  refine ⟨(map_mono h1).trans (map_subtype_subgroupOf_eq hNY).le, ?_, ?_, hrec⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h4 := h2 hy
    rw [hcent, mem_subgroupOf, mem_inf] at h4
    exact h4.2
  · refine (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T'.map Y.subtype)
      (X := Y) (Y := Y ⊓ centralizer ({x} : Set X)) inf_le_left 2 Nat.prime_two).mp ?_
    rw [hrec, ← hcent]
    exact h3

private theorem fivePumpNonAlt_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : FiveCat.FivePumpNonAlt S) : FiveCat.FivePumpNonAlt S' := by
  have hL : ∀ {t : Open.StatedLieTag} {n p f : ℕ},
      Blueprint.LieModel S t n p f → Blueprint.LieModel S' t n p f :=
    fun h => Blueprint.LieModel.of_mulEquiv e h
  have hS : ∀ {s : TauCeti.SporadicName},
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) →
        Nonempty (S' ≃* Blueprint.NativeSporadic.Carrier s) :=
    fun ⟨e'⟩ => ⟨e.symm.trans e'⟩
  unfold FiveCat.FivePumpNonAlt at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (hL h)
  · exact Or.inr (Or.inl (hL h))
  · exact Or.inr (Or.inr (Or.inl (hL h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hL h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hS h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hS h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hS h)))))))))

private theorem fiveTwoLayerOutcome_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : FiveCat.FiveTwoLayerOutcome S) : FiveCat.FiveTwoLayerOutcome S' := by
  unfold FiveCat.FiveTwoLayerOutcome at h ⊢
  exact h.imp (Blueprint.LieModel.of_mulEquiv e) (Blueprint.LieModel.of_mulEquiv e)

theorem five_pump_type_in (hF : FiveCat.FivePumpUpInput) [Finite X] {Y : Subgroup X}
    (hK : SectionRank.IsKGroupCat ↥Y) {x : X} (hxY : x ∈ Y) (hx : orderOf x = 2) {N T : Subgroup X}
    (hNY : N ≤ Y) (hNpc : IsPComponent 2 (N.subgroupOf Y)) (hNx : conjBy N x = N) (hTN : T ≤ N)
    (hTC : T ≤ centralizer ({x} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (Y ⊓ centralizer ({x} : Set X))))
    (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 5)) (hnt : T ⊔ core N ≠ N)
    (huniq : ∀ T' : Subgroup X, T' ≤ N → T' ≤ centralizer ({x} : Set X) →
      IsPComponent 2 (T'.subgroupOf (Y ⊓ centralizer ({x} : Set X))) → T' = T) :
    (∃ m : ℕ, Odd m ∧ 7 ≤ m ∧ Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin m))) ∨
      FiveCat.FivePumpNonAlt (↥N ⧸ Open.fusionZStar ↥N) := by
  have hxN : x ∈ normalizer (N : Set X) := mem_normalizer_iff_map_conj_eq.mpr hNx
  have hTY : T ≤ Y := hTN.trans hNY
  obtain ⟨hTM, hTC', hTpc'⟩ := layer_data hxY hTN hTC hTpc
  have hnt' : T.subgroupOf Y ⊔ (pPrimeCore 2 ↥(N.subgroupOf Y)).map (N.subgroupOf Y).subtype ≠
      N.subgroupOf Y := by
    intro h
    apply hnt
    have h1 := congrArg (Subgroup.map Y.subtype) h
    rwa [Subgroup.map_sup, map_subtype_subgroupOf_eq hTY, map_core_subgroupOf_eq hNY,
      map_subtype_subgroupOf_eq hNY] at h1
  have huniq' : ∀ T' : Subgroup ↥Y, T' ≤ N.subgroupOf Y →
      T' ≤ centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y) →
      IsPComponent 2 (T'.subgroupOf (centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y))) →
      T' = T.subgroupOf Y := by
    intro T' h1 h2 h3
    obtain ⟨hle, hC, hpc, hrec⟩ := layer_back hxY hNY h1 h2 h3
    rw [← hrec, huniq _ hle hC hpc]
  have key := hF ↥Y hK (N.subgroupOf Y) hNpc ⟨x, hxY⟩ (by rw [Subgroup.orderOf_mk]; exact hx)
    (mem_normalizer_subgroupOf_of_mem hxY hxN) (T.subgroupOf Y) hTM hTC' hTpc'
    ⟨(Sol78.coreQuotCongr (subgroupOfEquivOfLe hTY)).trans eT⟩ hnt' huniq'
  rcases key with ⟨m, hm, hm7, ⟨e⟩⟩ | h
  · exact Or.inl ⟨m, hm, hm7, ⟨(Sol78.coreQuotCongr (subgroupOfEquivOfLe hNY)).symm.trans e⟩⟩
  · exact Or.inr
      (fivePumpNonAlt_of_mulEquiv (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hNY)) h)

theorem five_two_layer_type_in (hF : FiveCat.FiveTwoLayerInput) [Finite X] {Y : Subgroup X}
    (hK : SectionRank.IsKGroupCat ↥Y) {x : X} (hxY : x ∈ Y) (hx : orderOf x = 2)
    {N T₁ T₂ : Subgroup X}
    (hNY : N ≤ Y) (hNpc : IsPComponent 2 (N.subgroupOf Y)) (hNx : conjBy N x = N)
    (hne : T₁ ≠ T₂) (hT₁N : T₁ ≤ N) (hT₂N : T₂ ≤ N)
    (hT₁C : T₁ ≤ centralizer ({x} : Set X)) (hT₂C : T₂ ≤ centralizer ({x} : Set X))
    (hT₁pc : IsPComponent 2 (T₁.subgroupOf (Y ⊓ centralizer ({x} : Set X))))
    (hT₂pc : IsPComponent 2 (T₂.subgroupOf (Y ⊓ centralizer ({x} : Set X))))
    (e₁ : ↥T₁ ⧸ pPrimeCore 2 ↥T₁ ≃* alternatingGroup (Fin 5))
    (e₂ : ↥T₂ ⧸ pPrimeCore 2 ↥T₂ ≃* alternatingGroup (Fin 5))
    (huniq : ∀ T' : Subgroup X, T' ≤ N → T' ≤ centralizer ({x} : Set X) →
      IsPComponent 2 (T'.subgroupOf (Y ⊓ centralizer ({x} : Set X))) → T' = T₁ ∨ T' = T₂) :
    FiveCat.FiveTwoLayerOutcome (↥N ⧸ Open.fusionZStar ↥N) := by
  have hxN : x ∈ normalizer (N : Set X) := mem_normalizer_iff_map_conj_eq.mpr hNx
  have hT₁Y : T₁ ≤ Y := hT₁N.trans hNY
  have hT₂Y : T₂ ≤ Y := hT₂N.trans hNY
  obtain ⟨hT₁M, hT₁C', hT₁pc'⟩ := layer_data hxY hT₁N hT₁C hT₁pc
  obtain ⟨hT₂M, hT₂C', hT₂pc'⟩ := layer_data hxY hT₂N hT₂C hT₂pc
  have hne' : T₁.subgroupOf Y ≠ T₂.subgroupOf Y := by
    intro h
    apply hne
    have h1 := congrArg (Subgroup.map Y.subtype) h
    rwa [map_subtype_subgroupOf_eq hT₁Y, map_subtype_subgroupOf_eq hT₂Y] at h1
  have huniq' : ∀ T' : Subgroup ↥Y, T' ≤ N.subgroupOf Y →
      T' ≤ centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y) →
      IsPComponent 2 (T'.subgroupOf (centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y))) →
      T' = T₁.subgroupOf Y ∨ T' = T₂.subgroupOf Y := by
    intro T' h1 h2 h3
    obtain ⟨hle, hC, hpc, hrec⟩ := layer_back hxY hNY h1 h2 h3
    rcases huniq _ hle hC hpc with h | h
    · exact Or.inl (by rw [← hrec, h])
    · exact Or.inr (by rw [← hrec, h])
  have key := hF ↥Y hK (N.subgroupOf Y) hNpc ⟨x, hxY⟩ (by rw [Subgroup.orderOf_mk]; exact hx)
    (mem_normalizer_subgroupOf_of_mem hxY hxN) (T₁.subgroupOf Y) (T₂.subgroupOf Y) hne' hT₁M hT₂M
    hT₁C' hT₂C' hT₁pc' hT₂pc'
    ⟨(Sol78.coreQuotCongr (subgroupOfEquivOfLe hT₁Y)).trans e₁⟩
    ⟨(Sol78.coreQuotCongr (subgroupOfEquivOfLe hT₂Y)).trans e₂⟩ huniq'
  exact fiveTwoLayerOutcome_of_mulEquiv (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hNY)) key

end CFSG.ComponentClassification.SolMax.SwapP2
