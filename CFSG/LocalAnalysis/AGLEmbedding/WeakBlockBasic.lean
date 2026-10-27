module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasicAux
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

open scoped commutatorElement

section Components

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsTwoPrimeComponent.inf_twoCore {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) :
    L ⊓ pCoreOf 2 M = pCoreOf 2 L := by
  apply le_antisymm
  · refine normal_pGroup_le_pCoreOf 2 _ L inf_le_left ?_
      ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact common_normalizer_le_normalizer_inf L L _ Subgroup.le_normalizer
      (hL.le.trans (localGroup_le_normalizer_pCoreOf 2 M))
  · exact le_inf (pCoreOf_le 2 L) (cfsg_subnormal_pCoreOf_le 2 hL.subnormal)

omit [Finite G] in
theorem barM_map_subtype (M : Subgroup G) (L : Subgroup M) :
    barM M (L.map M.subtype) = L.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
  rw [barM, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

theorem exists_isTwoPrimeComponent {M : Subgroup G} {Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hL : IsComponentOf Lbar ⊤) :
    ∃ L : Subgroup G, IsTwoPrimeComponent M L ∧ barM M L = Lbar := by
  let mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let L₀ := perfectResidualOf (Lbar.comap mk)
  have hperf : Group.IsPerfect Lbar := ⟨hL.2.2.1⟩
  have hbar : barM M (L₀.map M.subtype) = Lbar := by
    rw [barM_map_subtype]
    exact finite_canonical_perfect_preimage_image_eq mk (QuotientGroup.mk'_surjective _) Lbar hperf
  refine ⟨L₀.map M.subtype, ⟨Subgroup.map_subtype_le _, ?_, ?_, by rw [hbar]; exact hL⟩, hbar⟩
  · have h := cfsg_isSubnormal_map M.subtype (canonical_perfect_preimage_subnormal mk Lbar hL.2.1)
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  · rw [← Subgroup.map_commutator,
      Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect (Lbar.comap mk))]

omit [Finite G] in
theorem IsTwoPrimeComponent.isSubnormal_subgroupOf {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) : (L.subgroupOf M).IsSubnormal := by
  have h := cfsg_isSubnormal_comap M.subtype hL.subnormal
  have hM : M.comap M.subtype = ⊤ := Subgroup.subgroupOf_self M
  rw [hM] at h
  exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h
    Subgroup.IsSubnormal.top

omit [Finite G] in
theorem IsTwoPrimeComponent.commutator_subgroupOf {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) : ⁅L.subgroupOf M, L.subgroupOf M⁆ = L.subgroupOf M := by
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hL.le, hL.perfect]

omit [Finite G] in
theorem comap_barM (M X : Subgroup G) :
    (barM M X).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) =
      X.subgroupOf M ⊔ CFSG.pCore 2 ↥M := by
  rw [barM, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem IsTwoPrimeComponent.eq_of_barM_eq {M L L' : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hL' : IsTwoPrimeComponent M L') (he : barM M L = barM M L') : L = L' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : L.subgroupOf M ⊔ CFSG.pCore 2 ↥M = L'.subgroupOf M ⊔ CFSG.pCore 2 ↥M := by
    rw [← comap_barM, ← comap_barM, he]
  have : Group.IsNilpotent (CFSG.pCore 2 ↥M) := CFSG.pCore_isNilpotent (p := 2) (G := ↥M)
  have h₁ : L.subgroupOf M ≤ L'.subgroupOf M :=
    le_of_perfect_of_le_sup_of_isSubnormal hL'.isSubnormal_subgroupOf hL.commutator_subgroupOf
      (le_sup_left.trans hsup.le)
  have h₂ : L'.subgroupOf M ≤ L.subgroupOf M :=
    le_of_perfect_of_le_sup_of_isSubnormal hL.isSubnormal_subgroupOf hL'.commutator_subgroupOf
      (le_sup_left.trans hsup.ge)
  have h := le_antisymm h₁ h₂
  rwa [Subgroup.subgroupOf_inj, inf_of_le_left hL.le, inf_of_le_left hL'.le] at h

omit [Finite G] in
theorem subgroupOf_map_conj {M : Subgroup G} {g : G} (hg : g ∈ M) (X : Subgroup G) :
    (X.map (MulAut.conj g).toMonoidHom).subgroupOf M =
      (X.subgroupOf M).map (MulAut.conj (⟨g, hg⟩ : M)).toMonoidHom := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv,
    Subgroup.mem_subgroupOf, MulAut.conj_symm_apply, MulAut.conj_symm_apply]
  rfl

omit [Finite G] in
theorem barM_map_conj {M : Subgroup G} {g : G} (hg : g ∈ M) (X : Subgroup G) :
    barM M (X.map (MulAut.conj g).toMonoidHom) =
      (barM M X).map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩)).toMonoidHom := by
  rw [barM, barM, subgroupOf_map_conj hg, Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
theorem IsTwoPrimeComponent.map_conj {M L : Subgroup G} {g : G} (hg : g ∈ M)
    (hL : IsTwoPrimeComponent M L) :
    IsTwoPrimeComponent M (L.map (MulAut.conj g).toMonoidHom) := by
  have hM : M.map (MulAut.conj g).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  refine ⟨(Subgroup.map_mono hL.le).trans hM.le, ?_, ?_, ?_⟩
  · have h := cfsg_isSubnormal_map (MulAut.conj g).toMonoidHom hL.subnormal
    rwa [hM] at h
  · rw [← Subgroup.map_commutator, hL.perfect]
  · rw [barM_map_conj hg]
    exact (CFSG.ComponentClassification.LocalComponents.equiv_iff _ _).mpr hL.component

theorem IsTwoPrimeComponent.commutator_le {M L L' : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hL' : IsTwoPrimeComponent M L') (hne : L ≠ L') : ⁅L, L'⁆ ≤ pCoreOf 2 M := by
  have hbar : barM M L ≠ barM M L' := fun he => hne (hL.eq_of_barM_eq hL' he)
  have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.component
    hL'.component hbar
  rw [barM, barM, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    at hc
  have h := Subgroup.map_mono (f := M.subtype) hc
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hL.le,
    Subgroup.map_subgroupOf_eq_of_le hL'.le] at h
  exact h

theorem IsTwoPrimeComponent.le_normalizer {M S L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hS : barM M S ≤ Subgroup.normalizer (barM M L : Set _)) (hSM : S ≤ M) :
    S ≤ Subgroup.normalizer (L : Set G) := by
  intro s hs
  have hsM := hSM hs
  have hsbar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, hsM⟩ ∈ barM M S :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
  have hn := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hS hsbar)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact (hL.map_conj hsM).eq_of_barM_eq hL (by rw [barM_map_conj hsM]; exact hn)

omit [Finite G] in
theorem IsTwoPrimeComponent.isFooteBlock {M L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hs : IsShort2 L) : IsFooteBlock M L := by
  refine ⟨hL.le, hL.subnormal, hs.1, ?_, hs.2.2.2.2⟩
  rcases hs.2.2.2.1 with hq | h3
  · exact ⟨hq.1.1, hq.2.1⟩
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hL.perfect
    have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hcyc : IsCyclic (L ⧸ CFSG.pCore 2 L) := isCyclic_of_prime_card h3
    have : Group.IsSolvable (L ⧸ CFSG.pCore 2 L) :=
      Group.isSolvable_of_comm fun a b =>
        (IsCyclic.commGroup (α := L ⧸ CFSG.pCore 2 L)).mul_comm a b
    have hsub :=
      CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
        (G := L ⧸ CFSG.pCore 2 L)
    have h1 : Nat.card (L ⧸ CFSG.pCore 2 L) = 1 := Nat.card_unique
    omega

end Components

section Short

variable {G : Type} [Group G] [Finite G]

theorem IsShort2.hasIrreducibleCommutatorQuotient {L V : Subgroup G} (hL : IsShort2 L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ ≤ pCoreOf 2 L)
    (hV : IsMulCommutative V) (hnc : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    HasIrreducibleCommutatorQuotient L V := by
  obtain ⟨hres, -, ⟨hUQ, -⟩, -, -, hirr⟩ := hL
  have hWK := commutator_le_commutator_commutator_of_twoGroup hres hLV hV
    ((pCoreOf_isPGroup 2 L).to_le hVL)
  have hWU : ⁅V, L⁆ ≤ blockU L := hWK.trans (Subgroup.commutator_mono hVL le_rfl)
  have hUcomm : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hUQ hb).2 a (hUQ ha).1
  have hZU : blockZ L ≤ blockU L := inf_le_left
  refine ⟨lt_of_le_of_ne inf_le_left fun heq => hnc ?_, fun X hX₁ hX₂ hX₃ => ?_⟩
  · have hK : ⁅⁅V, L⁆, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (inf_eq_left.mp heq)
    have hW : ⁅V, L⁆ = ⊥ := le_bot_iff.mp (hWK.trans hK.le)
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hW)
  have hLZ : L ≤ Subgroup.normalizer (blockZ L : Set G) :=
    common_normalizer_le_normalizer_inf L _ _
      (le_normalizer_commutator_of_le_normalizer (localGroup_le_normalizer_pCoreOf 2 L))
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_centralizer L))
  have hLY : L ≤ Subgroup.normalizer ((X ⊔ blockZ L : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX₃ hl),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLZ hl)]
  rcases hirr (X ⊔ blockZ L) le_sup_right (sup_le (hX₂.trans hWU) hZU) hLY with hY | hY
  · exact Or.inl (le_antisymm (le_inf hX₂ ((le_sup_left.trans hY.le).trans inf_le_right)) hX₁)
  · refine Or.inr (le_antisymm hX₂ ?_)
    have hXZ : X ≤ Subgroup.normalizer (blockZ L : Set G) := fun x hx =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
        hUcomm z (hZU hz) x (hX₂.trans hWU hx))
    have hYX : ⁅X ⊔ blockZ L, L⁆ ≤ X := by
      rw [Subgroup.commutator_le]
      intro y hy l hl
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X _ hXZ] at hy
      obtain ⟨x, hx, z, hz, rfl⟩ := hy
      have hzl : z * l = l * z := (Subgroup.mem_centralizer_iff.mp hz.2 l hl).symm
      have e : ⁅x * z, l⁆ = ⁅x, l⁆ := by
        calc ⁅x * z, l⁆ = x * (z * l) * z⁻¹ * x⁻¹ * l⁻¹ := by
              rw [commutatorElement_def]; group
          _ = x * (l * z) * z⁻¹ * x⁻¹ * l⁻¹ := by rw [hzl]
          _ = ⁅x, l⁆ := by rw [commutatorElement_def]; group
      rw [e]
      exact commutator_le_left_of_le_normalizer hX₃ (Subgroup.commutator_mem_commutator hx hl)
    calc ⁅V, L⁆ ≤ ⁅⁅V, L⁆, L⁆ := hWK
      _ ≤ ⁅blockU L, L⁆ := Subgroup.commutator_mono hWU le_rfl
      _ = ⁅X ⊔ blockZ L, L⁆ := by rw [hY]
      _ ≤ X := hYX

end Short

section PhaseThree

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barM_le_normalizer_barM {M L S : Subgroup G}
    (hLS : L ≤ Subgroup.normalizer (S : Set G)) :
    barM M L ≤ Subgroup.normalizer (barM M S : Set _) := by
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hLS (Subgroup.mem_subgroupOf.mp hx)) y

theorem TwoLocalPair.exists_weakSBlock_or_oddCore {M H : Subgroup G} (h : TwoLocalPair M H)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L) ∨
      ¬ CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) ≤
        Subgroup.centralizer (barM M (pCoreOf 2 H) : Set _) := by
  rcases h.exists_component_or_oddCore hS with ⟨Lbar, hLbar, hnot⟩ | hodd
  · obtain ⟨L, hL, hbar⟩ := exists_isTwoPrimeComponent hLbar
    refine Or.inl ⟨L, { toIsTwoPrimeComponent := hL, not_le_normalizer := fun hLS => hnot ?_ }⟩
    rw [← hbar]
    exact barM_le_normalizer_barM hLS
  · exact Or.inr hodd

theorem D1PhaseThree.exists_weakSBlock_or_oddCore {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) :
    (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L) ∨
      ¬ CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) ≤
        Subgroup.centralizer (barM M (pCoreOf 2 H) : Set _) :=
  h.toD1Escape.toTwoLocalPair.exists_weakSBlock_or_oddCore h.twoCore_inf

end PhaseThree

end CFSG.AGLEmbedding
