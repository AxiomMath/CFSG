module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrNormalClosure
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Basic
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.LocalCores CFSG.ComponentClassification.LBalance
  CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.Assembly.LowTwoRank CFSG.GH74 CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

section Abstract

variable {X : Type} [Group X]

theorem perfect_le_of_le_sup_solvable {K N A : Subgroup X} [K.Normal] (hN : Group.IsSolvable N)
    (hA : Group.IsPerfect A) (hAKN : A ≤ K ⊔ N) : A ≤ K := by
  have himage : A.map (QuotientGroup.mk' K) ≤ N.map (QuotientGroup.mk' K) := by
    have h := Subgroup.map_mono (f := QuotientGroup.mk' K) hAKN
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge,
      bot_sup_eq] at h
  have hsolvN : Group.IsSolvable (N.map (QuotientGroup.mk' K)) := by
    have := hN
    exact Group.isSolvable_of_surjective ((QuotientGroup.mk' K).subgroupMap_surjective N)
  have hsolvA : Group.IsSolvable (A.map (QuotientGroup.mk' K)) := by
    have := hsolvN
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective himage)
  have := hA
  have hperfA : Group.IsPerfect (A.map (QuotientGroup.mk' K)) :=
    Group.IsPerfect.map (QuotientGroup.mk' K)
  have hbot : A.map (QuotientGroup.mk' K) = ⊥ := by
    by_contra hne
    have : Nontrivial (A.map (QuotientGroup.mk' K)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable _ hsolvA
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

variable [Finite X]

theorem pPrimeCore_solvable : Group.IsSolvable ↥(pPrimeCore 2 X) :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X)))

theorem fitting_quot_eq_bot (hS : IsSimpleGroup ↥(generalizedFitting (X ⧸ pPrimeCore 2 X)))
    (hSp : Group.IsPerfect ↥(generalizedFitting (X ⧸ pPrimeCore 2 X))) :
    fittingSubgroup (X ⧸ pPrimeCore 2 X) = ⊥ := by
  set Φ := fittingSubgroup (X ⧸ pPrimeCore 2 X) with hΦ
  set F := generalizedFitting (X ⧸ pPrimeCore 2 X) with hF
  have hle : Φ ≤ F := le_sup_left
  by_contra hne
  have hnormal : (Φ.subgroupOf F).Normal := inferInstance
  rcases hS.eq_bot_or_eq_top_of_normal (Φ.subgroupOf F) with h | h
  · apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : F) ∈ Φ.subgroupOf F := hx
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  · have hFΦ : F ≤ Φ := by
      intro x hx
      have : (⟨x, hx⟩ : F) ∈ Φ.subgroupOf F := by rw [h]; exact mem_top _
      exact this
    have : Group.IsNilpotent ↥(F.subgroupOf Φ) := inferInstance
    have hnil : Group.IsNilpotent ↥F :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFΦ)
    have : Group.IsSolvable ↥F := inferInstance
    have := hS.toNontrivial
    have := hSp
    exact Group.IsPerfect.not_isSolvable ↥F inferInstance

theorem pCore_eq_bot (hfit : fittingSubgroup (X ⧸ pPrimeCore 2 X) = ⊥) : pCore 2 X = ⊥ := by
  have hP : IsPGroup 2 ↥(pCore 2 X) := pCore_isPGroup (G := X) (p := 2)
  have hmapnormal : ((pCore 2 X).map (QuotientGroup.mk' (pPrimeCore 2 X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hnil : Group.IsNilpotent ↥((pCore 2 X).map (QuotientGroup.mk' (pPrimeCore 2 X))) := by
    have : IsPGroup 2 ↥((pCore 2 X).map (QuotientGroup.mk' (pPrimeCore 2 X))) :=
      hP.of_surjective ((QuotientGroup.mk' (pPrimeCore 2 X)).subgroupMap (pCore 2 X))
        ((QuotientGroup.mk' (pPrimeCore 2 X)).subgroupMap_surjective _)
    exact this.isNilpotent
  have hle := (CFSG.LocalCores.fitting_characteristic.2.2 _ hmapnormal hnil)
  rw [hfit, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hle
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 X)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  have hk' : orderOf x = 2 ^ k := by rw [← hk]; exact (Subgroup.orderOf_mk x hx).symm
  have hdvd : orderOf x ∣ Nat.card ↥(pPrimeCore 2 X) := Subgroup.orderOf_dvd_natCard _ (hle hx)
  have hoddk : Odd (2 ^ k) := hk' ▸ Odd.of_dvd_nat hodd hdvd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hoddk) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
  exact hk'

theorem map_layer_le :
    (layer X).map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤ layer (X ⧸ pPrimeCore 2 X) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun J hJ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hnot : ¬ J ≤ (QuotientGroup.mk' (pPrimeCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    intro hle
    have hsolv : Group.IsSolvable ↥J := by
      have := pPrimeCore_solvable (X := X)
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have := isQuasisimple_nontrivial hJ.1
    have := hJ.1.1
    exact Group.IsPerfect.not_isSolvable ↥J hsolv
  exact component_le_layer ⟨isQuasisimple_map hJ.1 _ hnot, hJ.2.map (QuotientGroup.mk'_surjective _)⟩

theorem map_layer_eq (hS : IsSimpleGroup ↥(generalizedFitting (X ⧸ pPrimeCore 2 X)))
    (hK : layer X ≠ ⊥) :
    (layer X).map (QuotientGroup.mk' (pPrimeCore 2 X)) =
      generalizedFitting (X ⧸ pPrimeCore 2 X) := by
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set F := generalizedFitting (X ⧸ pPrimeCore 2 X) with hF
  have hle : (layer X).map π ≤ F := map_layer_le.trans le_sup_right
  have hne : (layer X).map π ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
    have hsolv : Group.IsSolvable ↥(layer X) := by
      have := pPrimeCore_solvable (X := X)
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hbot)
    have : Nontrivial ↥(layer X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hK
    have := layer_isPerfect (G := X)
    exact Group.IsPerfect.not_isSolvable _ hsolv
  have hnormal : ((layer X).map π).Normal := by
    have : (layer X).Characteristic := layer_characteristic
    exact Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hnormal' : (((layer X).map π).subgroupOf F).Normal := inferInstance
  rcases hS.eq_bot_or_eq_top_of_normal (((layer X).map π).subgroupOf F) with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : F) ∈ ((layer X).map π).subgroupOf F := hx
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  · refine le_antisymm hle fun x hx => ?_
    have : (⟨x, hx⟩ : F) ∈ ((layer X).map π).subgroupOf F := by rw [h]; exact mem_top _
    exact this

theorem pLayer_eq_layer (hS : IsSimpleGroup ↥(generalizedFitting (X ⧸ pPrimeCore 2 X)))
    (hSp : Group.IsPerfect ↥(generalizedFitting (X ⧸ pPrimeCore 2 X))) (hK : layer X ≠ ⊥) :
    pLayer X 2 = layer X := by
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hfit := fitting_quot_eq_bot hS hSp
  have hlayerF : layer (X ⧸ pPrimeCore 2 X) = generalizedFitting (X ⧸ pPrimeCore 2 X) := by
    rw [generalizedFitting, hfit, bot_sup_eq]
  have hmapK := map_layer_eq hS hK
  have hsolv := pPrimeCore_solvable (X := X)
  apply le_antisymm
  · have hL : pLayer X 2 ≤ layer X ⊔ pPrimeCore 2 X := by
      have h1 : (pLayer X 2).map π = layer (X ⧸ pPrimeCore 2 X) :=
        CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient (H := X) (p := 2)
      have h2 : pLayer X 2 ≤ ((pLayer X 2).map π).comap π := Subgroup.le_comap_map _ _
      rw [h1, hlayerF, ← hmapK, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk'] at h2
      exact h2
    have hperf : Group.IsPerfect ↥(pLayer X 2) :=
      Subgroup.isPerfect_iff.mpr (CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect X)
    have : (layer X).Characteristic := layer_characteristic
    exact perfect_le_of_le_sup_solvable hsolv hperf hL
  · exact solvable_prime_complement_core_perfect_layer_lift hsolv layer_isPerfect map_layer_le

theorem exists_cover (hS : IsSimpleGroup ↥(generalizedFitting (X ⧸ pPrimeCore 2 X)))
    (hK : layer X ≠ ⊥) :
    ∃ f : ↥(layer X) →* ↥(generalizedFitting (X ⧸ pPrimeCore 2 X)),
      Function.Surjective f ∧ f.ker ≤ center ↥(layer X) ∧ Odd (Nat.card f.ker) := by
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hmapK := map_layer_eq hS hK
  have hmem : ∀ k : ↥(layer X), π (k : X) ∈ generalizedFitting (X ⧸ pPrimeCore 2 X) := fun k =>
    hmapK ▸ Subgroup.mem_map_of_mem π k.2
  let f : ↥(layer X) →* ↥(generalizedFitting (X ⧸ pPrimeCore 2 X)) :=
    (π.comp (layer X).subtype).codRestrict _ hmem
  have hker : ∀ k ∈ f.ker, (k : X) ∈ pPrimeCore 2 X := by
    intro k hk
    have h1 : π (k : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hsolv := pPrimeCore_solvable (X := X)
  have hcomm : layer X ≤ centralizer (pPrimeCore 2 X : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.component_solvable_centralizer hsolv
        (pPrimeCore_normal (p := 2) (G := X)).isSubnormal).2
  refine ⟨f, ?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [← hmapK] at hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨k, hk⟩, rfl⟩
  · intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hcomm g.2) (k : X) (hker k hk)).symm
  · have hodd : Odd (Nat.card ↥(pPrimeCore 2 X)) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))
    have hle : f.ker.map (layer X).subtype ≤ pPrimeCore 2 X := by
      rintro _ ⟨k, hk, rfl⟩
      exact hker k hk
    have hcard : Nat.card ↥(f.ker.map (layer X).subtype) = Nat.card ↥f.ker :=
      Subgroup.card_map_of_injective (layer X).subtype_injective
    rw [← hcard]
    exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)

end Abstract

theorem isSimple_isPerfect_of_isPSp4 {K : Type} [Group K] {q : ℕ} (hq : 3 < q) (h : IVK.IsPSp4 K q) :
    IsSimpleGroup K ∧ Group.IsPerfect K := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have hF4 : 4 ≤ Nat.card F := by omega
  have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by omega)
      (Or.inl (Or.inr hF4))
  have hperf : Group.IsPerfect (StatedProj (StatedSp 2 F)) := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF4)
    exact CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2 F (Or.inl ⟨t, ht⟩)
  refine ⟨?_, ?_⟩
  · have := hsimple
    exact e.isSimpleGroup
  · have := hperf
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

section Amb

variable {G : Type} [Group G]

theorem pLayerOf_eq_map (p : ℕ) (H : Subgroup G) :
    pLayerOf p H = (pLayer ↥H p).map H.subtype := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    obtain ⟨hLH, hL2⟩ := hL
    rw [← Subgroup.map_subgroupOf_eq_of_le hLH]
    exact Subgroup.map_mono (le_sSup hL2)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨?_, ?_⟩
    · rintro _ ⟨m, -, rfl⟩
      exact m.2
    · have : (M.map H.subtype).subgroupOf H = M :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective M
      rw [this]
      exact hM

variable [Finite G]

theorem layer_of_PSp4 (hP : PSp4_oddCover) (M : Subgroup G) {q : ℕ} (hqodd : Odd q) (hq3 : 3 < q)
    (hF : IVK.IsPSp4 ↥(generalizedFitting (HBar M)) q) (h17 : H17A M) :
    Op 2 M = ⊥ ∧ Thm4a M ∧ PSp4Layer M q := by
  obtain ⟨hS, hSp⟩ := isSimple_isPerfect_of_isPSp4 hq3 hF
  have hS' : IsSimpleGroup ↥(generalizedFitting (↥M ⧸ pPrimeCore 2 ↥M)) := hS
  have hSp' : Group.IsPerfect ↥(generalizedFitting (↥M ⧸ pPrimeCore 2 ↥M)) := hSp
  have hO : pCore 2 ↥M = ⊥ := pCore_eq_bot (fitting_quot_eq_bot hS' hSp')
  have hOp : Op 2 M = ⊥ := by rw [Op_eq, hO, Subgroup.map_bot]
  have hK : layer ↥M ≠ ⊥ := by
    intro hbot
    apply h17
    rw [Em_eq, hbot, hOp, Subgroup.map_bot, bot_sup_eq]
  have hpl := pLayer_eq_layer hS' hSp' hK
  refine ⟨hOp, ?_, ?_⟩
  · show pLayerOf 2 M = Em M
    rw [pLayerOf_eq_map, hpl, Em_eq]
  · obtain ⟨f, hf, hker, hodd⟩ := exists_cover hS' hK
    have hbot : f.ker = ⊥ :=
      hP ↥(layer ↥M) ↥(generalizedFitting (↥M ⧸ pPrimeCore 2 ↥M)) f hf
        (layer_isPerfect (G := ↥M)) hker hodd q hqodd hF
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hbot
    let e : ↥(layer ↥M) ≃* ↥(generalizedFitting (↥M ⧸ pPrimeCore 2 ↥M)) :=
      MulEquiv.ofBijective f ⟨hinj, hf⟩
    obtain ⟨F, hFfield, hFfin, hcard, ⟨e'⟩⟩ := hF
    refine ⟨F, hFfield, hFfin, hcard, ⟨?_⟩⟩
    exact (Subgroup.equivMapOfInjective (layer ↥M) M.subtype M.subtype_injective).symm.trans
      (e.trans e')

end Amb

end CFSG.GH74.GLS.Stage2.Final.Thm4
