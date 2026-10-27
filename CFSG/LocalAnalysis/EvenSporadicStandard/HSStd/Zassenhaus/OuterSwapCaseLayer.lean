module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseLayerSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseLayerTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterStructCatalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseLayerDich
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv4

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv Equiv.Perm CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

structure SwapSingle (h : HSOuterSetup G L t S z n v s) (M : Subgroup G) : Prop where
  comp : IsCompIn M (centralizer ({v} : Set G))
  le : derivedCentralizerIn L v ≤ M
  inv : ∀ x ∈ M, t * x * t⁻¹ ∈ M
  normal : (M.subgroupOf (centralizer ({v} : Set G))).Normal
  center_two : IsPGroup 2 (center ↥M)
  simple : IsSimpleGroup (↥M ⧸ center ↥M)
  catalog : Catalog (↥M ⧸ center ↥M)
  sq : tauQuot M (t_sq h) inv * tauQuot M (t_sq h) inv = 1
  ne : tauQuot M (t_sq h) inv ≠ 1
  card_le : Nat.card (autCentralizer (tauQuot M (t_sq h) inv)) ≤ 161280
  quotient : ∃ D : Subgroup ↥(autCentralizer (tauQuot M (t_sq h) inv)), D.Normal ∧
    Nonempty (↥D ≃* alternatingGroup (Fin 8)) ∧
    ∀ x : ↥(autCentralizer (tauQuot M (t_sq h) inv)), ∃ n : ℕ, x ^ (2 ^ n) ∈ D
  pump : PumpType (↥M ⧸ center ↥M)
  types : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 10)) ∨
    Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 12)) ∨
    IsSporadic (↥M ⧸ center ↥M) .HS ∨ Nat.card (↥M ⧸ center ↥M) = 987033600
  hs_outer : IsSporadic (↥M ⧸ center ↥M) .HS →
    tauQuot M (t_sq h) inv ∉ (MulAut.conj : (↥M ⧸ center ↥M) →* MulAut (↥M ⧸ center ↥M)).range

structure SwapPair (L : Subgroup G) (t v : G) (Q₁ Q₂ : Subgroup G) : Prop where
  comp₁ : IsCompIn Q₁ (centralizer ({v} : Set G))
  comp₂ : IsCompIn Q₂ (centralizer ({v} : Set G))
  ne : Q₁ ≠ Q₂
  swap : Q₂ = Q₁.map (MulAut.conj t).toMonoidHom
  commute : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a
  le : derivedCentralizerIn L v ≤ Q₁ ⊔ Q₂
  normal : ((Q₁ ⊔ Q₂).subgroupOf (centralizer ({v} : Set G))).Normal
  alt₁ : Nonempty (↥Q₁ ⧸ center ↥Q₁ ≃* alternatingGroup (Fin 8))
  alt₂ : Nonempty (↥Q₂ ⧸ center ↥Q₂ ≃* alternatingGroup (Fin 8))

section Lift

variable (v)

theorem subgroupOf_map_subtype (K : Subgroup ↥(centralizer ({v} : Set G))) :
    (K.map (centralizer ({v} : Set G)).subtype).subgroupOf (centralizer ({v} : Set G)) = K :=
  Subgroup.comap_map_eq_self_of_injective (centralizer ({v} : Set G)).subtype_injective _

theorem isQuasisimple_map_subtype {K : Subgroup ↥(centralizer ({v} : Set G))}
    (hK : CFSG.IsQuasisimple ↥K) :
    CFSG.IsQuasisimple ↥(K.map (centralizer ({v} : Set G)).subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K.equivMapOfInjective _ (centralizer ({v} : Set G)).subtype_injective) hK

theorem isCompIn_map_subtype {K : Subgroup ↥(centralizer ({v} : Set G))}
    (hK : CFSG.IsComponent K) :
    IsCompIn (K.map (centralizer ({v} : Set G)).subtype) (centralizer ({v} : Set G)) := by
  refine isCompIn_of_subnormal (Subgroup.map_subtype_le K) (isQuasisimple_map_subtype v hK.1) ?_
  rw [subgroupOf_map_subtype]
  exact hK.2

end Lift

theorem isPGroup_center_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (K : Subgroup X) (hZ : IsPGroup 2 (center ↥K)) :
    IsPGroup 2 (center ↥(K.map f)) := by
  set e := K.equivMapOfInjective f hf with he
  intro z
  have hz : (z : ↥(K.map f)) ∈ (center ↥K).map (e : ↥K →* ↥(K.map f)) := by
    rw [Subgroup.map_center_eq e]
    exact z.2
  obtain ⟨a, ha, haz⟩ := hz
  obtain ⟨m, hm⟩ := hZ ⟨a, ha⟩
  refine ⟨m, ?_⟩
  have h1 : a ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  apply Subtype.ext
  show (z : ↥(K.map f)) ^ (2 ^ m) = 1
  rw [← haz, ← map_pow, h1, map_one]

theorem swapSingle_of_orbit (hq : KGA8Q8) (h15 : FS79Lemma15Sec G)
    (h : HSOuterSetup G L t S z n v s) {K : Subgroup ↥(centralizer ({v} : Set G))}
    (hK : SwapOrbit (lamIn L v) (tIn h) K) (hcj : PartA.cj (tIn h) K = K)
    (hall : ∀ g : ↥(centralizer ({v} : Set G)),
      PartA.cj g K = K ∨ PartA.cj g K = PartA.cj (tIn h) K) (hN : K.Normal) :
    SwapSingle h (K.map (centralizer ({v} : Set G)).subtype) := by
  set f := (centralizer ({v} : Set G)).subtype with hf
  have hfi : Function.Injective f := (centralizer ({v} : Set G)).subtype_injective
  have hX := swapX_of_setup h15 h
  have hinv := SwapOrbit.single_inv hcj
  have hJK : lamIn L v ≤ K := hK.single_le hcj
  set M := K.map f with hM
  have hinvM : ∀ x ∈ M, t * x * t⁻¹ ∈ M := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨tIn h * k * (tIn h)⁻¹, hinv k hk, by simp [hf, tIn, HSOuterSetup.tElem]⟩
  have hqM : CFSG.IsQuasisimple ↥M := isQuasisimple_map_subtype v hK.comp.1
  have hcat : Catalog (↥M ⧸ center ↥M) := by
    have hne : M ≠ ⊤ := by
      intro htop
      apply centralizer_singleton_ne_top h.setting.1.simple h.setting.1.nonabelian h.v_ne_one
      rw [eq_top_iff]
      exact htop ▸ Subgroup.map_subtype_le K
    exact PartA.catalog_quot_center h.setting.1.kProper M hne hqM
  set ε := quotCenterEquiv (K.equivMapOfInjective f hfi) with hε
  have hc : ∀ y : ↥K ⧸ center ↥K, ε (tauQuot K hX.sq hinv y) =
      tauQuot M (t_sq h) hinvM (ε y) := fun y =>
    tauQuot_map_compat f hfi K hX.sq hinv (t_sq h) hinvM y
  obtain ⟨-, hsq, hne, hcard, hD⟩ := hX.single_hyps hK hcj hall
  have hsq' := sq_transport ε hc hsq
  have hne' := ne_transport ε hc hne
  have hcard' : Nat.card (autCentralizer (tauQuot M (t_sq h) hinvM)) ≤ 161280 :=
    (card_autCentralizer_transport ε hc).trans_le hcard
  have hD' := D_transport ε hc hD
  obtain ⟨hpump, htypes, hout⟩ := hq _ hcat hqM.2.1 _ hsq' hne' hcard' hD'
  refine ⟨isCompIn_map_subtype v hK.comp, ?_, hinvM, ?_, ?_, hqM.2.1, hcat, hsq', hne', hcard',
    hD', hpump, htypes, hout⟩
  · intro x hx
    exact ⟨⟨x, derivedCentralizerIn_le_centralizer L v hx⟩, hJK (mem_subgroupOf.2 hx), rfl⟩
  · rw [subgroupOf_map_subtype]
    exact hN
  · exact isPGroup_center_map f hfi K (isPGroup_center_component hX.oddCore hK.comp)

theorem swapPair_of_orbit (h15 : FS79Lemma15Sec G) (h : HSOuterSetup G L t S z n v s)
    {K : Subgroup ↥(centralizer ({v} : Set G))} (hK : SwapOrbit (lamIn L v) (tIn h) K)
    (hcj : PartA.cj (tIn h) K ≠ K) (hN : (K ⊔ PartA.cj (tIn h) K).Normal) :
    SwapPair L t v (K.map (centralizer ({v} : Set G)).subtype)
      ((PartA.cj (tIn h) K).map (centralizer ({v} : Set G)).subtype) := by
  set f := (centralizer ({v} : Set G)).subtype with hf
  have hfi : Function.Injective f := (centralizer ({v} : Set G)).subtype_injective
  have hX := swapX_of_setup h15 h
  have hcomm := hK.pair_comm hcj
  have hK2 : IsComponent (PartA.cj (tIn h) K) := PartA.isComponent_cj _ hK.comp
  refine ⟨isCompIn_map_subtype v hK.comp, isCompIn_map_subtype v hK2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact hcj (Subgroup.map_injective hfi heq).symm
  · rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    exact congrArg f (hcomm k hk k' hk')
  · intro x hx
    have hxJ : (⟨x, derivedCentralizerIn_le_centralizer L v hx⟩ : ↥(centralizer ({v} : Set G))) ∈
        lamIn L v := mem_subgroupOf.2 hx
    have h1 := hK.le hxJ
    rw [← Subgroup.map_sup]
    exact ⟨_, h1, rfl⟩
  · rw [← Subgroup.map_sup, subgroupOf_map_subtype]
    exact hN
  · obtain ⟨e⟩ := hK.pair_quot_alt8 hX hcj
    exact ⟨(quotCenterEquiv (K.equivMapOfInjective f hfi)).symm.trans e⟩
  · obtain ⟨e⟩ := hK.pair_quot_alt8 hX hcj
    let e₂ : ↥((PartA.cj (tIn h) K).map f) ≃* ↥K :=
      ((PartA.cj (tIn h) K).equivMapOfInjective f hfi).symm.trans
        ((K.equivMapOfInjective (MulAut.conj (tIn h)).toMonoidHom
          (MulAut.conj (tIn h)).injective).symm)
    exact ⟨(quotCenterEquiv e₂).trans e⟩

theorem swap_layer_dichotomy (h15 : FS79Lemma15Sec G) (hq : KGA8Q8) (hcover : KGA8CoverElem)
    (h : HSOuterSetup G L t S z n v s) (hE8 : SwapNoE8 L v) :
    (∃ M : Subgroup G, SwapSingle h M) ∨ ∃ Q₁ Q₂ : Subgroup G, SwapPair L t v Q₁ Q₂ := by
  rcases (swapX_of_setup h15 h).dichotomy (swapNoE8_of hE8) hcover with
    ⟨K, hK, hcj, hall, hN⟩ | ⟨K, hK, hcj, hall, hN⟩
  · exact Or.inl ⟨_, swapSingle_of_orbit hq h15 h hK hcj hall hN⟩
  · exact Or.inr ⟨_, _, swapPair_of_orbit h15 h hK hcj hN⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
