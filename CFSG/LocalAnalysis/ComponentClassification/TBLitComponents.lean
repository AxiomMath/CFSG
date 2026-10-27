module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainOrbitTools
public import CFSG.LocalAnalysis.ComponentClassification.TBLitTools
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise

variable {X : Type} [Group X] [Finite X]

theorem commutator_self_of_isPComponent {S C : Subgroup X} (hSC : S ≤ C)
    (hS : IsPComponent 2 (S.subgroupOf C)) : ⁅S, S⁆ = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hS
  have : Group.IsPerfect S :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hSC).toMonoidHom)
      (subgroupOfEquivOfLe hSC).surjective
  exact Subgroup.isPerfect_iff.mp this

theorem isPComponent_data {S C : Subgroup X} (hSC : S ≤ C) (hS : IsPComponent 2 (S.subgroupOf C)) :
    (S.subgroupOf C).IsSubnormal ∧ CatalogueBPrimeJoin.primeResidual 2 S = ⊤ ∧
      IsQuasisimple (S ⧸ pPrimeCore 2 S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 S C hSC).mp hS

theorem commutator_le_oddCoreIn_of_ne {C A B : Subgroup X} (hAC : A ≤ C) (hBC : B ≤ C)
    (hA : IsPComponent 2 (A.subgroupOf C)) (hB : IsPComponent 2 (B.subgroupOf C)) (hne : A ≠ B) :
    ⁅A, B⁆ ≤ oddCoreIn A := by
  have hne' : A.subgroupOf C ≠ B.subgroupOf C := by
    intro h
    apply hne
    rw [subgroupOf_inj, inf_eq_left.mpr hAC, inf_eq_left.mpr hBC] at h
    exact h
  obtain ⟨-, -, hcomm, -⟩ := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ hA hB).2 hne'
  have h1 := map_mono (f := C.subtype) (hcomm.trans inf_le_left)
  rwa [map_commutator, map_subgroupOf_eq_of_le hAC, map_subgroupOf_eq_of_le hBC,
    pPrimeCore_map_subgroupOf 2 A C hAC] at h1

theorem mem_normalizer_of_isPComponent_centralizer {d g : X} (hgd : g * d = d * g)
    {H S : Subgroup X} (hH : H ≤ centralizer ({d} : Set X))
    (hHc : IsPComponent 2 (H.subgroupOf (centralizer ({d} : Set X)))) (hSH : S ≤ H)
    (hS : ⁅S, S⁆ = S) {s : X} (hs : s ∈ S) (hs2 : orderOf s = 2)
    (hgS : g ∈ normalizer (S : Set X)) : g ∈ normalizer (H : Set X) := by
  obtain ⟨hHg, hHgc⟩ := UGSChain.conjugate_isPComponent_centralizer hgd hH hHc
  have hSHg : S ≤ conjugate H g := by
    rw [← UnbalancedLayer.conjugate_eq_of_mem_normalizer hgS]
    exact map_mono hSH
  have heq := eq_of_isPComponent_of_perfect_le hH hHg hHc hHgc hSH hSHg hS hs hs2
  rw [mem_normalizer_iff]
  intro x
  conv_lhs => rw [heq]
  exact UnbalancedLayer.mem_conjugate_iff

theorem exists_not_mem_oddCoreIn_of_le {S H : Subgroup X} (hSH : S ≤ H) {g : X}
    (hgS : g ∈ normalizer (S : Set X)) (h : ¬ ∀ s ∈ S, ⁅s, g⁆ ∈ oddCoreIn S) :
    ∃ k ∈ H, ⁅k, g⁆ ∉ oddCoreIn H := by
  by_contra hall
  apply h
  refine forall_mem_oddCoreIn_of_le hSH hgS fun k hk => ?_
  by_contra hk'
  exact hall ⟨k, hk, hk'⟩

theorem isUnbalancingConfig_of_actsProperly {d a : X} (hd : orderOf d = 2) (ha : orderOf a = 2)
    (had : a * d = d * a) {H E S : Subgroup X} (hH : H ≤ centralizer ({d} : Set X))
    (hHc : IsPComponent 2 (H.subgroupOf (centralizer ({d} : Set X))))
    (hEa : E ≤ oddCentralizerCore a) (hEd : E ≤ centralizer ({d} : Set X))
    (haH : a ∈ normalizer (H : Set X)) (hEH : E ≤ normalizer (H : Set X)) (hSH : S ≤ H)
    (hprop : ActsProperly a E S (oddCoreIn S)) : IsUnbalancingConfig d a H E := by
  obtain ⟨-, hgen, hq⟩ := isPComponent_data hH hHc
  have hEodd : Odd (Nat.card E) := Nat.coprime_two_left.mp
    ((coprime_card_oddCentralizerCore a).coprime_dvd_right (card_dvd_of_le hEa))
  have haS : a ∈ normalizer (S : Set X) := (hprop.1 (subset_closure (Set.mem_insert a _))).1
  obtain ⟨k, hk, hka⟩ := exists_not_mem_oddCoreIn_of_le hSH haS (hprop.not_trivial_left ha hEodd)
  obtain ⟨e, he, s, hs, hes⟩ := hprop.exists_nontrivial
  have heS : e ∈ normalizer (S : Set X) :=
    (hprop.1 (subset_closure (Set.mem_insert_of_mem a he))).1
  obtain ⟨k', hk', hk'e⟩ := exists_not_mem_oddCoreIn_of_le hSH heS (fun h => hes (h s hs))
  refine ⟨hd, ha, had, hH, hHc, hEa, hEd, ?_, ?_⟩
  · exact commutator_eq_self_of_exists hgen hq (zpowers_le.mpr haH)
      ⟨a, mem_zpowers a, k, hk, hka⟩
  · exact commutator_eq_self_of_exists hgen hq hEH ⟨e, he, k', hk', hk'e⟩

theorem isKGroupCat_centralizer (hK : Assembly.KProper Catalog X) {d : X} (hd : d ∉ center X) :
    SectionRank.IsKGroupCat (centralizer ({d} : Set X)) :=
  UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
    (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hK _
    (UnbalancingLocal.centralizer_lt_top hd).ne

theorem le_pLayer_of_isPComponent_inf (hS : LocalAnalysis.ComponentInitial.SchreierFor Catalog)
    {H : Subgroup X} (hK : SectionRank.IsKGroupCat H) {e : X} (heH : e ∈ H) (he : orderOf e = 2)
    {T : Subgroup X} (hT : T ≤ centralizer ({e} : Set X) ⊓ H)
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({e} : Set X) ⊓ H))) :
    T ≤ (pLayer H 2).map H.subtype := by
  have he' : orderOf (⟨e, heH⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact he
  have hcena := UGSChain.centralizer_mk_eq_subgroupOf heH
  have hT'C : T.subgroupOf H ≤ centralizer ({(⟨e, heH⟩ : H)} : Set H) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hT (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf H).subgroupOf
      (centralizer ({(⟨e, heH⟩ : H)} : Set H))) := by
    rw [hcena, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact hTpc
  have h := (UGSChain.kGroup_involution_fixed_two_layer_containment_of_schreier hS hK he').1
    _ hT'C hT'pc
  intro t ht
  exact ⟨⟨t, (hT ht).2⟩, h (show (⟨t, (hT ht).2⟩ : H) ∈ T.subgroupOf H from ht), rfl⟩

end CFSG.ComponentClassification.TBLit
