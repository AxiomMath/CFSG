module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageModels

import CFSG.GroupTheory.OppositeRadicals
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools Subgroup
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def GomiLeviPackageTop (X : Type) [Group X] : Prop :=
  ∀ U P : Subgroup X, IsSylowOf 2 U ⊤ → normalizer (U : Set X) < P → P < ⊤ →
    ¬ IsGomiAtom ⊤ U P → ∃ ℳ : Set (Subgroup X), IsGomiLeviPackage ⊤ U P ℳ

private theorem map_sSup_subtype {G : Type} [Group G] (L : Subgroup G)
    (ℳ : Set (Subgroup ↥L)) :
    (sSup ℳ).map L.subtype = sSup ((fun M => M.map L.subtype) '' ℳ) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    refine (Subgroup.map_le_iff_le_comap).mp ?_
    exact le_sSup (show M.map L.subtype ∈ (fun M => M.map L.subtype) '' ℳ from ⟨M, hM, rfl⟩)
  · refine sSup_le ?_
    rintro N ⟨M, hM, rfl⟩
    exact Subgroup.map_mono (le_sSup hM)

private theorem pElementSubgroup_map_injective' {S S' : Type} [Group S] [Group S']
    (f : S →* S') (hf : Function.Injective f) (P : Subgroup S) :
    pElementSubgroup 2 (P.map f) = (pElementSubgroup 2 P).map f := by
  unfold pElementSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨hy, k, by rwa [orderOf_injective f hf y] at hk⟩, rfl⟩
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, k, by rwa [orderOf_injective f hf y]⟩

private theorem map_normalizer_subtype {G : Type} [Group G] (L : Subgroup G)
    (U : Subgroup ↥L) :
    (normalizer (U : Set ↥L)).map L.subtype =
      L ⊓ normalizer ((U.map L.subtype : Subgroup G) : Set G) := by
  have hUle : (U.map L.subtype : Subgroup G) ≤ L := Subgroup.map_subtype_le U
  have hsub : (U.map L.subtype).subgroupOf L = U := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hUle]
  rw [inf_normalizer_eq_map_normalizer_subgroupOf hUle, hsub]

private theorem map_center_subtype_eq {G : Type} [Group G] (L : Subgroup G)
    (M : Subgroup ↥L) :
    (center ↥(M.map L.subtype)).map (M.map L.subtype).subtype =
      (center ↥M).map (L.subtype.comp M.subtype) := by
  let e : ↥M ≃* ↥(M.map L.subtype) :=
    Subgroup.equivMapOfInjective M L.subtype L.subtype_injective
  have hcomp : (M.map L.subtype).subtype.comp e.toMonoidHom =
      L.subtype.comp M.subtype := by
    ext x
    exact Subgroup.coe_equivMapOfInjective_apply M L.subtype L.subtype_injective x
  calc (center ↥(M.map L.subtype)).map (M.map L.subtype).subtype
      = ((center ↥M).map e.toMonoidHom).map (M.map L.subtype).subtype := by
        rw [show (center ↥M).map e.toMonoidHom = center ↥(M.map L.subtype) from
          Subgroup.map_center_eq e]
    _ = (center ↥M).map ((M.map L.subtype).subtype.comp e.toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = (center ↥M).map (L.subtype.comp M.subtype) := by
        rw [hcomp]

private theorem map_center_subtype_map {G : Type} [Group G] (L : Subgroup G)
    (M : Subgroup ↥L) :
    ((center ↥M).map M.subtype).map L.subtype =
      (center ↥(M.map L.subtype)).map (M.map L.subtype).subtype := by
  rw [Subgroup.map_map, map_center_subtype_eq L M]

private theorem covBy_map_subtype {G : Type} [Group G] (L : Subgroup G)
    {C M : Subgroup ↥L} (h : C ⋖ M) : (C.map L.subtype) ⋖ (M.map L.subtype) := by
  let f : Subgroup ↥L ↪o Subgroup G := OrderEmbedding.ofMapLEIff
    (fun H => H.map L.subtype) (fun _ _ => Subgroup.map_subtype_le_map_subtype)
  have hrange : (Set.range f).OrdConnected := by
    have hf : Set.range f = Set.Iic L := by
      ext H; constructor
      · rintro ⟨H', rfl⟩; exact Subgroup.map_subtype_le H'
      · intro hH; exact ⟨H.subgroupOf L, Subgroup.map_subgroupOf_eq_of_le hH⟩
    rw [hf]; exact Set.ordConnected_Iic
  exact (Set.OrdConnected.apply_covBy_apply_iff f hrange).mpr h

private theorem map_subtype_atom {G : Type} [Group G] {L : Subgroup G}
    {U P : Subgroup ↥L} {ℳ : Set (Subgroup ↥L)} (h : IsGomiLeviPackage ⊤ U P ℳ)
    (hB : (normalizer (U : Set ↥L)).map L.subtype =
      L ⊓ normalizer ((U.map L.subtype : Subgroup G) : Set G)) :
    ∀ A : Subgroup G, IsGomiAtom L (U.map L.subtype) A → A ≤ P.map L.subtype →
      ∃ M ∈ (fun M => M.map L.subtype) '' ℳ,
        A ≤ L ⊓ normalizer ((U.map L.subtype : Subgroup G) : Set G) ⊔ M ∧
          ∀ M' ∈ (fun M => M.map L.subtype) '' ℳ,
            A ≤ L ⊓ normalizer ((U.map L.subtype : Subgroup G) : Set G) ⊔ M' → M' = M := by
  intro A hA hAP
  have hAeq : (A.subgroupOf L).map L.subtype = A :=
    Subgroup.map_subgroupOf_eq_of_le hA.2.1
  have hA0 : IsGomiAtom ⊤ U (A.subgroupOf L) :=
    (isGomiAtom_map_subtype_iff L U (A.subgroupOf L)).mp (by rw [hAeq]; exact hA)
  have hA0P : A.subgroupOf L ≤ P := by
    rw [← Subgroup.map_le_map_iff_of_injective L.subtype_injective, hAeq]
    exact hAP
  obtain ⟨M, hM, hle, huniq⟩ := h.atom (A.subgroupOf L) hA0 hA0P
  refine ⟨M.map L.subtype, ⟨M, hM, rfl⟩, ?_, ?_⟩
  · have h1 := Subgroup.map_mono (f := L.subtype) (by simpa [top_inf_eq] using hle)
    rwa [hAeq, Subgroup.map_sup, hB] at h1
  · rintro M'' ⟨M₀, hM₀, rfl⟩ hle''
    have hA0le : A.subgroupOf L ≤ normalizer (U : Set ↥L) ⊔ M₀ := by
      rw [← Subgroup.map_le_map_iff_of_injective L.subtype_injective, hAeq,
        Subgroup.map_sup, hB]
      exact hle''
    rw [huniq M₀ hM₀ (by simpa [top_inf_eq] using hA0le)]

private theorem map_subtype_factor {G : Type} [Group G] {L : Subgroup G}
    {U P : Subgroup ↥L} {ℳ : Set (Subgroup ↥L)} (h : IsGomiLeviPackage ⊤ U P ℳ)
    (hB : (normalizer (U : Set ↥L)).map L.subtype =
      L ⊓ normalizer ((U.map L.subtype : Subgroup G) : Set G)) :
    ∀ M : Subgroup G, M ∈ (fun M => M.map L.subtype) '' ℳ →
      IsGomiChevTwo ↥M ∨ Nonempty (↥M ≃* Equiv.Perm (Fin 6)) ∨
        L ⊓ normalizer ((U.map L.subtype : Subgroup G) : Set G) ⊓ M ⋖ M := by
  rintro M ⟨M₀, hM₀, rfl⟩
  rcases h.factor M₀ hM₀ with hC | hS6 | hcov
  · exact Or.inl (IsGomiChevTwo.of_mulEquiv
      (Subgroup.equivMapOfInjective M₀ L.subtype L.subtype_injective) hC)
  · obtain ⟨e⟩ := hS6
    exact Or.inr (Or.inl ⟨(Subgroup.equivMapOfInjective M₀ L.subtype
      L.subtype_injective).symm.trans e⟩)
  · right; right
    have hc := covBy_map_subtype L (C := normalizer (U : Set ↥L) ⊓ M₀) (M := M₀)
      (by simpa [top_inf_eq] using hcov)
    rwa [Subgroup.map_inf_eq (normalizer (U : Set ↥L)) M₀ L.subtype L.subtype_injective,
      hB] at hc

theorem IsGomiLeviPackage.map_subtype {G : Type} [Group G] {L : Subgroup G}
    {U P : Subgroup ↥L} {ℳ : Set (Subgroup ↥L)} (h : IsGomiLeviPackage ⊤ U P ℳ) :
    IsGomiLeviPackage L (U.map L.subtype) (P.map L.subtype) ((fun M => M.map L.subtype) '' ℳ) := by
  have hB := map_normalizer_subtype L U
  refine
    { le_parabolic := fun M hM => by
        obtain ⟨M₀, hM₀, rfl⟩ := hM
        exact Subgroup.map_mono (h.le_parabolic M₀ hM₀)
      inf_eq_bot := fun M hM => by
        obtain ⟨M₀, hM₀, rfl⟩ := hM
        rw [pCoreOf_map_of_injective 2 L.subtype L.subtype_injective,
          ← Subgroup.map_inf_eq (pCoreOf 2 P) M₀ L.subtype L.subtype_injective,
          h.inf_eq_bot M₀ hM₀, Subgroup.map_bot]
      commute := fun M₁ h₁ M₂ h₂ hne => by
        obtain ⟨M₁₀, hM₁₀, rfl⟩ := h₁
        obtain ⟨M₂₀, hM₂₀, rfl⟩ := h₂
        rw [← Subgroup.map_commutator,
          h.commute M₁₀ hM₁₀ M₂₀ hM₂₀ (fun h => hne (by rw [h])), Subgroup.map_bot]
      pElementSubgroup_eq := fun M hM => by
        obtain ⟨M₀, hM₀, rfl⟩ := hM
        rw [pElementSubgroup_map_injective' L.subtype L.subtype_injective,
          h.pElementSubgroup_eq M₀ hM₀]
      sylow_le := ?_
      normal := fun M hM => by
        obtain ⟨M₀, hM₀, rfl⟩ := hM
        calc P.map L.subtype
            ≤ (Subgroup.normalizer ((pCoreOf 2 P ⊔ M₀ : Subgroup ↥L) : Set ↥L)).map L.subtype :=
              Subgroup.map_mono (h.normal M₀ hM₀)
          _ ≤ Subgroup.normalizer
                (((pCoreOf 2 P ⊔ M₀ : Subgroup ↥L).map L.subtype : Subgroup G) : Set G) :=
              Subgroup.le_normalizer_map L.subtype
          _ = Subgroup.normalizer
                ((pCoreOf 2 (P.map L.subtype) ⊔ M₀.map L.subtype : Subgroup G) : Set G) := by
              rw [Subgroup.map_sup, pCoreOf_map_of_injective 2 L.subtype L.subtype_injective]
      center_commutator_le := fun M hM => by
        obtain ⟨M₀, hM₀, rfl⟩ := hM
        rw [← map_center_subtype_map L M₀, ← Subgroup.map_commutator]
        exact (Subgroup.map_mono (h.center_commutator_le M₀ hM₀)).trans_eq
          (pCoreOf_map_of_injective 2 L.subtype L.subtype_injective P).symm
      atom := map_subtype_atom h hB
      factor := map_subtype_factor h hB }
  · have h1 := Subgroup.map_mono (f := L.subtype) h.sylow_le
    rw [Subgroup.map_sup, ← pCoreOf_map_of_injective 2 L.subtype L.subtype_injective,
      map_sSup_subtype] at h1
    exact h1

theorem GomiLeviPackageTop.exists_isGomiLeviPackage {G : Type} [Group G] [Finite G]
    {L U P : Subgroup G} (h : GomiLeviPackageTop ↥L) (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P < L) (hat : ¬ IsGomiAtom L U P) :
    ∃ ℳ : Set (Subgroup G), IsGomiLeviPackage L U P ℳ := by
  have hU0 : IsSylowOf 2 (U.subgroupOf L) ⊤ := (isSylowOf_top_subgroupOf_iff hU.le).mpr hU
  have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← L.subtype.range_eq_map, Subgroup.range_subtype]
  have hN : normalizer ((U.subgroupOf L) : Set ↥L) < P.subgroupOf L := by
    rw [← Subgroup.map_subtype_lt_map_subtype,
      ← inf_normalizer_eq_map_normalizer_subgroupOf hU.le,
      Subgroup.map_subgroupOf_eq_of_le hPL.le]
    exact hBP
  have hP0 : P.subgroupOf L < ⊤ := by
    rw [← Subgroup.map_subtype_lt_map_subtype,
      Subgroup.map_subgroupOf_eq_of_le hPL.le, htop]
    exact hPL
  have hat0 : ¬ IsGomiAtom ⊤ (U.subgroupOf L) (P.subgroupOf L) := fun h' =>
    hat ((isGomiAtom_iff_subgroupOf hU.le hPL.le).mpr h')
  obtain ⟨ℳ₀, hℳ₀⟩ := h (U.subgroupOf L) (P.subgroupOf L) hU0 hN hP0 hat0
  refine ⟨(fun M => M.map L.subtype) '' ℳ₀, ?_⟩
  have hmap := IsGomiLeviPackage.map_subtype hℳ₀
  rwa [Subgroup.map_subgroupOf_eq_of_le hU.le,
    Subgroup.map_subgroupOf_eq_of_le hPL.le] at hmap

theorem gomiChevLeviPackageModel_of_gomiLeviPackageTop {t : StatedLieTag} {n : ℕ}
    (h : ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X t n 2 f → GomiLeviPackageTop X) :
    GomiChevLeviPackageModel t n := fun _ _ _ L _ _ f hm _ _ hU hBP hPL hat =>
  (h ↥L f hm).exists_isGomiLeviPackage hU hBP hPL hat

end CFSG.GroupTheory
