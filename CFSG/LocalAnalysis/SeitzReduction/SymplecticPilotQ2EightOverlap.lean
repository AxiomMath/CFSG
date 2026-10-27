module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldEight

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)

section Triple

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {k : Fin n}

omit [Finite G] [Finite F] in
theorem map_inf_centralizer_singleton_eq_eight {A : Type*} [Group A] {φ : A →* G}
    (hφ : Function.Injective φ) (Y : Subgroup A) (a : A) :
    Y.map φ ⊓ centralizer ({φ a} : Set G) = (Y ⊓ centralizer ({a} : Set A)).map φ := by
  rw [Subgroup.map_inf_eq _ _ _ hφ, LinearPilot.map_centralizer_singleton_of_injective hφ,
    ← inf_assoc, inf_eq_left.2 (map_le_range φ Y)]

theorem NsFieldParam.map_triple_eq [CharP F 2] (P : NsFieldParam e t ι σ k)
    (hF : 4 ≤ Nat.card F) {l m : Fin n} (hkl : k ≠ l) (hkm : k ≠ m) :
    ((spBlock F ({k, l}ᶜ ∩ {m}ᶜ : Finset (Fin n))).subgroupOf
        (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ =
      centralizerPerfectCore (modelToG e (nsTorusSp K k) ⊔ modelToG e (nsTorusSp K l) ⊔
        modelToG e (nsTorusSp K m)) := by
  set S := spBlock F ({k}ᶜ : Finset (Fin n)) with hS
  set a : S := ⟨spFieldMap n ι (nsElt m), spFieldMap_mem_spBlock ι (nsElt_mem_spBlock_compl hkm)⟩
    with ha
  have hPa : P.Φ a = ((e.symm (nsElt m) : L) : G) := P.N1 _ (nsElt_mem_spBlock_compl hkm)
  have hle2 : spBlock F ({k, l}ᶜ : Finset (Fin n)) ≤ S :=
    spBlock_mono fun x hx => mem_compl_singleton_iff'.2 (mem_compl_pair_iff'.1 hx).1
  have hle3 : spBlock F ({k, l}ᶜ ∩ {m}ᶜ : Finset (Fin n)) ≤ S :=
    (spBlock_mono Finset.inter_subset_left).trans hle2
  have hmodel : perfectCore ((spBlock F ({k, l}ᶜ : Finset (Fin n))).subgroupOf S ⊓
      centralizer ({a} : Set S)) = (spBlock F ({k, l}ᶜ ∩ {m}ᶜ : Finset (Fin n))).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_inf_eq _ _ _ S.subtype_injective,
      subgroupOf_map_subtype, subgroupOf_map_subtype,
      LinearPilot.map_centralizer_singleton_of_injective S.subtype_injective, range_subtype,
      inf_of_le_left hle2, inf_of_le_left hle3, ← inf_assoc, inf_of_le_left hle2, coe_subtype, ha]
    change perfectCore (spBlock F ({k, l}ᶜ : Finset (Fin n)) ⊓
      centralizer ({spFieldMap n ι (nsElt m)} : Set (StatedSp n F))) = _
    rw [spFieldMap_nsElt]
    exact perfectCore_spBlock_inf_centralizer_nsElt _ m (commutator_spBlock_eq hF _)
  rw [F4Pilot.centralizerPerfectCore_sup, ← P.map_overlap_eq hF hkl, nsTorusSp,
    centralizer_modelToG_zpowers, ← hPa, map_inf_centralizer_singleton_eq_eight P.injective,
    ← CFSG.Quasithin.map_perfectCore, hmodel]

end Triple

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F} {k : Fin n}

theorem NsFieldParam.map_le_centralizer_map (P : NsFieldParam e t ι σ k)
    {N₁ N₂ : Finset (Fin n)} (h : Disjoint N₁ N₂) :
    ((spBlock F N₁).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ ≤
      centralizer ((((spBlock F N₂).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ :
        Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (commute_of_mem_spBlock_of_disjoint h (mem_subgroupOf.1 hx)
    (mem_subgroupOf.1 hy)).eq.symm

theorem NsFieldParam.map_le_centralizer_modelToG (P : NsFieldParam e t ι σ k)
    {N₁ N₂ : Finset (Fin n)} (h : Disjoint N₁ N₂) (hN₂ : N₂ ⊆ {k}ᶜ) :
    ((spBlock F N₁).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ ≤
      centralizer (modelToG e (spBlock K N₂) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
  have hyk : y ∈ spBlock K ({k}ᶜ : Finset (Fin n)) := spBlock_mono hN₂ hy
  rw [← P.N1 y hyk, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (commute_of_mem_spBlock_of_disjoint h (mem_subgroupOf.1 hx)
    (spFieldMap_mem_spBlock ι hy)).eq.symm

theorem NsFieldParam.map_pair_le_of_le (P : NsFieldParam e t ι σ k) {a b : Fin n} (hab : a ≠ b)
    (hak : a ≠ k) (hbk : b ≠ k) {C : Subgroup G}
    (hA : ((spBlock F {a}).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ ≤ C)
    (hB : ((spBlock F {b}).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ ≤ C)
    (hL : modelToG e (spBlock K ({a, b} : Finset (Fin n))) ≤ C) :
    ((spBlock F ({a, b} : Finset (Fin n))).subgroupOf
      (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ ≤ C := by
  set S := spBlock F ({k}ᶜ : Finset (Fin n)) with hS
  have hsub : ∀ c : Fin n, c ≠ k → ({c} : Finset (Fin n)) ⊆ {k}ᶜ := fun c hc x hx => by
    rw [Finset.mem_singleton] at hx
    exact mem_compl_singleton_iff'.2 (hx ▸ hc)
  have hpair : ({a, b} : Finset (Fin n)) ⊆ {k}ᶜ := fun x hx => by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact mem_compl_singleton_iff'.2 hak
    · rw [Finset.mem_singleton.1 hx]
      exact mem_compl_singleton_iff'.2 hbk
  rw [map_le_iff_le_comap]
  set C' : Subgroup (StatedSp n F) := (C.comap P.Φ).map S.subtype with hC'
  have hmem : ∀ x : S, (x : StatedSp n F) ∈ C' → x ∈ C.comap P.Φ := by
    rintro x ⟨y, hy, hyx⟩
    rwa [← S.subtype_injective hyx]
  have hsingle : ∀ c : Fin n, c ≠ k →
      ((spBlock F {c}).subgroupOf S).map P.Φ ≤ C → spBlock F {c} ≤ C' := by
    intro c hc h x hx
    have hxS : x ∈ S := spBlock_mono (hsub c hc) hx
    exact ⟨⟨x, hxS⟩, h ⟨⟨x, hxS⟩, mem_subgroupOf.2 hx, rfl⟩, rfl⟩
  have hK : (spBlock K ({a, b} : Finset (Fin n))).map (spFieldMap n ι) ≤ C' := by
    rintro _ ⟨y, hy, rfl⟩
    have hyk : y ∈ spBlock K ({k}ᶜ : Finset (Fin n)) := spBlock_mono hpair hy
    refine ⟨⟨spFieldMap n ι y, spFieldMap_mem_spBlock ι hyk⟩, ?_, rfl⟩
    change P.Φ _ ∈ C
    rw [P.N1 y hyk]
    exact hL (symm_mem_modelToG e hy)
  have hle := (spBlock_pair_le_sup_map_spFieldMap (F := F) ι hab).trans
    (sup_le (sup_le (hsingle a hak hA) (hsingle b hbk hB)) hK)
  intro x hx
  exact hmem x (hle (mem_subgroupOf.1 hx))

end Transport

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] [CharP F 2] {e : L ≃* StatedSp 4 K} {t : G} {ι : K →+* F} {σ : F ≃+* F}

theorem commute_overlap_of_nsFieldParam_four (hF : 4 ≤ Nat.card F)
    (P : ∀ k : Fin 4, NsFieldParam e t ι σ k) :
    ∀ a ∈ centralizerPerfectCore (modelToG e (nsTorusSp K 0) ⊔ modelToG e (nsTorusSp K 1)),
      ∀ b ∈ centralizerPerfectCore (modelToG e (nsTorusSp K 2) ⊔ modelToG e (nsTorusSp K 3)),
        Commute a b := by
  have hA0 := (P 0).map_overlap_eq hF (show (0 : Fin 4) ≠ 1 by decide)
  rw [show ({0, 1}ᶜ : Finset (Fin 4)) = {2, 3} by decide] at hA0
  have hA1 := (P 1).map_overlap_eq hF (show (1 : Fin 4) ≠ 0 by decide)
  rw [show ({1, 0}ᶜ : Finset (Fin 4)) = {2, 3} by decide, sup_comm] at hA1
  have hB2 := (P 2).map_overlap_eq hF (show (2 : Fin 4) ≠ 3 by decide)
  rw [show ({2, 3}ᶜ : Finset (Fin 4)) = {0, 1} by decide] at hB2
  have hJ0 : ((spBlock F {0}).subgroupOf (spBlock F ({1}ᶜ : Finset (Fin 4)))).map (P 1).Φ =
      ((spBlock F {0}).subgroupOf (spBlock F ({2}ᶜ : Finset (Fin 4)))).map (P 2).Φ := by
    have h1 := (P 1).map_triple_eq hF (show (1 : Fin 4) ≠ 2 by decide)
      (show (1 : Fin 4) ≠ 3 by decide)
    have h2 := (P 2).map_triple_eq hF (show (2 : Fin 4) ≠ 1 by decide)
      (show (2 : Fin 4) ≠ 3 by decide)
    rw [show ({1, 2}ᶜ ∩ {3}ᶜ : Finset (Fin 4)) = {0} by decide] at h1
    rw [show ({2, 1}ᶜ ∩ {3}ᶜ : Finset (Fin 4)) = {0} by decide] at h2
    rw [h1, h2, sup_comm (modelToG e (nsTorusSp K 1))]
  have hJ1 : ((spBlock F {1}).subgroupOf (spBlock F ({0}ᶜ : Finset (Fin 4)))).map (P 0).Φ =
      ((spBlock F {1}).subgroupOf (spBlock F ({2}ᶜ : Finset (Fin 4)))).map (P 2).Φ := by
    have h1 := (P 0).map_triple_eq hF (show (0 : Fin 4) ≠ 2 by decide)
      (show (0 : Fin 4) ≠ 3 by decide)
    have h2 := (P 2).map_triple_eq hF (show (2 : Fin 4) ≠ 0 by decide)
      (show (2 : Fin 4) ≠ 3 by decide)
    rw [show ({0, 2}ᶜ ∩ {3}ᶜ : Finset (Fin 4)) = {1} by decide] at h1
    rw [show ({2, 0}ᶜ ∩ {3}ᶜ : Finset (Fin 4)) = {1} by decide] at h2
    rw [h1, h2, sup_comm (modelToG e (nsTorusSp K 0))]
  have hJ2 : ((spBlock F {2}).subgroupOf (spBlock F ({0}ᶜ : Finset (Fin 4)))).map (P 0).Φ =
      ((spBlock F {2}).subgroupOf (spBlock F ({3}ᶜ : Finset (Fin 4)))).map (P 3).Φ := by
    have h1 := (P 0).map_triple_eq hF (show (0 : Fin 4) ≠ 1 by decide)
      (show (0 : Fin 4) ≠ 3 by decide)
    have h2 := (P 3).map_triple_eq hF (show (3 : Fin 4) ≠ 0 by decide)
      (show (3 : Fin 4) ≠ 1 by decide)
    rw [show ({0, 1}ᶜ ∩ {3}ᶜ : Finset (Fin 4)) = {2} by decide] at h1
    rw [show ({3, 0}ᶜ ∩ {1}ᶜ : Finset (Fin 4)) = {2} by decide] at h2
    rw [h1, h2, sup_assoc (modelToG e (nsTorusSp K 3)), sup_comm (modelToG e (nsTorusSp K 3))]
  have hJ3 : ((spBlock F {3}).subgroupOf (spBlock F ({0}ᶜ : Finset (Fin 4)))).map (P 0).Φ =
      ((spBlock F {3}).subgroupOf (spBlock F ({2}ᶜ : Finset (Fin 4)))).map (P 2).Φ := by
    have h1 := (P 0).map_triple_eq hF (show (0 : Fin 4) ≠ 1 by decide)
      (show (0 : Fin 4) ≠ 2 by decide)
    have h2 := (P 2).map_triple_eq hF (show (2 : Fin 4) ≠ 0 by decide)
      (show (2 : Fin 4) ≠ 1 by decide)
    rw [show ({0, 1}ᶜ ∩ {2}ᶜ : Finset (Fin 4)) = {3} by decide] at h1
    rw [show ({2, 0}ᶜ ∩ {1}ᶜ : Finset (Fin 4)) = {3} by decide] at h2
    rw [h1, h2, sup_assoc (modelToG e (nsTorusSp K 2)), sup_comm (modelToG e (nsTorusSp K 2))]
  have hS : centralizerPerfectCore (modelToG e (nsTorusSp K 0) ⊔ modelToG e (nsTorusSp K 1)) ≤
      centralizer (modelToG e (spBlock K ({0, 1} : Finset (Fin 4))) : Set G) := by
    rw [← hA0]
    refine (P 0).map_pair_le_of_le (show (2 : Fin 4) ≠ 3 by decide) (by decide) (by decide)
      ?_ ?_ ?_
    · rw [hJ2]
      exact (P 3).map_le_centralizer_modelToG (by decide) (by decide)
    · rw [hJ3]
      exact (P 2).map_le_centralizer_modelToG (by decide) (by decide)
    · refine UnitaryPilot.modelToG_le_centralizer e fun x hx => mem_centralizer_iff.2 fun y hy =>
        (commute_of_mem_spBlock_of_disjoint (by decide : Disjoint ({0, 1} : Finset (Fin 4)) {2, 3})
          hy hx).eq
  have hB : centralizerPerfectCore (modelToG e (nsTorusSp K 2) ⊔ modelToG e (nsTorusSp K 3)) ≤
      centralizer (centralizerPerfectCore
        (modelToG e (nsTorusSp K 0) ⊔ modelToG e (nsTorusSp K 1)) : Set G) := by
    rw [← hB2]
    refine (P 2).map_pair_le_of_le (show (0 : Fin 4) ≠ 1 by decide) (by decide) (by decide)
      ?_ ?_ ?_
    · rw [← hJ0, ← hA1]
      exact (P 1).map_le_centralizer_map (by decide)
    · rw [← hJ1, ← hA0]
      exact (P 0).map_le_centralizer_map (by decide)
    · exact le_centralizer_iff.1 hS
  intro a ha b hb
  exact mem_centralizer_iff.1 (hB hb) a ha

end Main

theorem spTwoFieldOverlapEightInput_holds :
    SpTwoFieldOverlapEightInput := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hfield
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  have hF4 : 4 ≤ Nat.card F := by
    rw [LinearPilot.natCard_eq_sq_of_fixedField ι hσ1 hσσ hfix, hK]
    norm_num
  have hparam : ∀ k : Fin 4, Nonempty (NsFieldParam e t ι σ k) := fun k =>
    nonempty_nsFieldParam (m := 3) hset hK le_rfl e htC ht k ι hσ hfix (hfield k)
  exact commute_overlap_of_nsFieldParam_four hF4 fun k => (hparam k).some

theorem spTwoRowInput_field_holds :
    SpTwoRowInput .field :=
  spTwoRowInput_field_of_overlap spTwoFieldOverlapEightInput_holds

end CFSG.SeitzReduction.SymplecticPilot
