module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Defs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)

variable {τ : Tag}

theorem iform_nonneg_of_pos {σ : Fin τ.rank → ℤ} (hdom : ∀ i, 0 ≤ iform (Pi.single i 1) σ)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β ∧ 0 < height β) : 0 ≤ iform β σ := by
  have hc := (IsRoot.height_pos_iff hβ.1).1 hβ.2
  rw [iform_comm, F4Pilot.iform_eq_sum_mul_iform_single]
  refine Finset.sum_nonneg fun j _ => mul_nonneg (hc j) ?_
  rw [iform_comm]
  exact hdom j

theorem reflect_eq_self_of_iform_eq_zero (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {σ : Fin τ.rank → ℤ} {i : Fin τ.rank} (h : iform (Pi.single i 1) σ = 0) :
    reflect τ i σ = σ := by
  rw [iform_single_left, EvenOddRadical.symmetrizer_apply_self hτ i, one_mul] at h
  rw [reflect, h, zero_smul, sub_zero]

theorem mem_parabolicWeylGroup_of_smul_eq (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {σ : Fin τ.rank → ℤ} (hdom : ∀ i, 0 ≤ iform (Pi.single i 1) σ) :
    ∀ (n : ℕ) (w : WeylGroup τ), (coxeterSystem τ).length w = n → w • σ = σ →
      w ∈ parabolicWeylGroup τ {i | iform (Pi.single i 1) σ = 0} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hlen hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one hw1
    have hroot := IsRoot.smul (isRoot_single τ i) w
    have hdesc : (coxeterSystem τ).IsRightDescent w i :=
      (smul_single_mem_negRoots_iff w i).1 ⟨hroot, hi⟩
    have hl := (isRightDescent_iff_length w i).1 hdesc
    have hcoef := (IsRoot.height_neg_iff hroot).1 hi
    have hzero : iform (Pi.single i 1) σ = 0 := by
      have e : iform (w • (Pi.single i 1 : Fin τ.rank → ℤ)) σ = iform (Pi.single i 1) σ := by
        conv_lhs => rw [← hw]
        exact iform_smul w _ _
      have hle : iform (w • (Pi.single i 1 : Fin τ.rank → ℤ)) σ ≤ 0 := by
        rw [iform_comm, F4Pilot.iform_eq_sum_mul_iform_single]
        refine Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hcoef j) ?_
        rw [iform_comm]
        exact hdom j
      have hge := hdom i
      omega
    have hsi : simple τ i ∈ parabolicWeylGroup τ {i | iform (Pi.single i 1) σ = 0} :=
      Subgroup.subset_closure ⟨i, hzero, rfl⟩
    have hws : (w * simple τ i) • σ = σ := by
      rw [mul_smul, simple_smul, reflect_eq_self_of_iform_eq_zero hτ hzero, hw]
    have hmem := ih _ (by omega) (w * simple τ i) rfl hws
    have := mul_mem hmem hsi
    rwa [mul_assoc, simple_mul_simple_self, mul_one] at this

@[expose] def tupleCheck (F High : List (Fin τ.rank → ℤ)) : Bool :=
  ((F ++ High).sublistsLen F.length).all fun S =>
    !(decide (S.Pairwise fun a b => iform a b = 0)) || S.all fun a => decide (a ∈ F)

theorem smul_mem_of_tupleCheck {F High : List (Fin τ.rank → ℤ)} (hnd : F.Nodup)
    (ho : F.Pairwise fun a b => iform a b = 0) (hc : tupleCheck F High = true)
    {w : WeylGroup τ} (h : ∀ β ∈ F, w • β ∈ F ++ High) : ∀ β ∈ F, w • β ∈ F := by
  set M := F.map fun β => w • β with hM
  have hMnd : M.Nodup := hnd.map (MulAction.injective w)
  have hMsub : M ⊆ F ++ High := fun x hx => by
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
    exact h β hβ
  have hMo : M.Pairwise fun a b => iform a b = 0 := by
    rw [hM, List.pairwise_map]
    exact ho.imp fun hab => by rw [iform_smul]; exact hab
  obtain ⟨S, hSM, hSsub⟩ := List.subperm_of_subset hMnd hMsub
  have hSlen : S.length = F.length := by rw [hSM.length_eq, hM, List.length_map]
  have hSmem : S ∈ (F ++ High).sublistsLen F.length :=
    List.mem_sublistsLen.2 ⟨hSsub, hSlen⟩
  have hSo : S.Pairwise fun a b => iform a b = 0 :=
    (hSM.pairwise_iff fun {a b} hab => by rw [iform_comm]; exact hab).2 hMo
  have h1 := List.all_eq_true.1 hc S hSmem
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    List.all_eq_true, decide_eq_true_eq] at h1
  have hSF : ∀ a ∈ S, a ∈ F := h1.resolve_left (not_not.2 hSo)
  intro β hβ
  exact hSF _ (hSM.symm.subset (List.mem_map_of_mem hβ))

section Coord

variable {K : Type} [Field K]

variable (τ K) in
@[expose] noncomputable def rootProdInvSubgroup (Ψ : List (Fin τ.rank → ℤ))
    (P : ((Fin τ.rank → ℤ) → K) → Prop) : Subgroup (ModGL τ K) where
  carrier := {g | ∀ c, P c →
    (∃ c', g * rootProd τ K Ψ c * g⁻¹ = rootProd τ K Ψ c' ∧ P c') ∧
      (∃ c', g⁻¹ * rootProd τ K Ψ c * g = rootProd τ K Ψ c' ∧ P c')}
  mul_mem' := by
    intro g h hg hh c hc
    obtain ⟨⟨c1, e1, h1⟩, -⟩ := hh c hc
    obtain ⟨⟨c2, e2, h2⟩, -⟩ := hg c1 h1
    obtain ⟨-, ⟨d2, f2, k2⟩⟩ := hg c hc
    obtain ⟨-, ⟨d3, f3, k3⟩⟩ := hh d2 k2
    refine ⟨⟨c2, ?_, h2⟩, ⟨d3, ?_, k3⟩⟩
    · rw [← e2, ← e1]
      group
    · rw [← f3, ← f2]
      group
  one_mem' := fun c hc => ⟨⟨c, by group, hc⟩, ⟨c, by group, hc⟩⟩
  inv_mem' := by
    intro g hg c hc
    obtain ⟨⟨c1, e1, h1⟩, ⟨d1, f1, k1⟩⟩ := hg c hc
    exact ⟨⟨d1, by rw [inv_inv]; exact f1, k1⟩, ⟨c1, by rw [inv_inv]; exact e1, h1⟩⟩

theorem pinnedX_mem_rootProdInvSubgroup {Ψ : List (Fin τ.rank → ℤ)}
    {P : ((Fin τ.rank → ℤ) → K) → Prop} {α : Fin τ.rank → ℤ}
    (h : ∀ (t : K) c, P c → ∃ c', pinnedX τ K α t * rootProd τ K Ψ c *
      (pinnedX τ K α t)⁻¹ = rootProd τ K Ψ c' ∧ P c') (t : K) :
    pinnedX τ K α t ∈ rootProdInvSubgroup τ K Ψ P := by
  intro c hc
  refine ⟨h t c hc, ?_⟩
  obtain ⟨c', e, hc'⟩ := h (-t) c hc
  refine ⟨c', ?_, hc'⟩
  rw [pinnedX_neg]
  rw [pinnedX_neg, neg_neg] at e
  exact e

theorem rootSpan_le_rootProdInvSubgroup {Ψ : List (Fin τ.rank → ℤ)}
    {P : ((Fin τ.rank → ℤ) → K) → Prop} {S : Set (Fin τ.rank → ℤ)}
    (h : ∀ α ∈ S, ∀ t : K, pinnedX τ K α t ∈ rootProdInvSubgroup τ K Ψ P) :
    rootSpan τ K S ≤ rootProdInvSubgroup τ K Ψ P :=
  iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
    rintro _ ⟨t, rfl⟩
    exact h α hα t)


theorem torusGroup_le_rootProdInvSubgroup {Ψ : List (Fin τ.rank → ℤ)}
    (hr : ∀ β ∈ Ψ, IsRoot τ β) {P : ((Fin τ.rank → ℤ) → K) → Prop}
    (h : ∀ g ∈ torusGroup τ K, ∀ c, P c → P fun β => torusRootChar g β * c β) :
    torusGroup τ K ≤ rootProdInvSubgroup τ K Ψ P := by
  intro g hg c hc
  refine ⟨⟨_, E6Pilot.conj_rootProd_of_mem_torusGroup hg hr c, h g hg c hc⟩,
    ⟨_, ?_, h _ (inv_mem hg) c hc⟩⟩
  have := E6Pilot.conj_rootProd_of_mem_torusGroup (inv_mem hg) hr c
  rwa [inv_inv] at this

end Coord

structure FrameBruhatData (F Low High : List (Fin τ.rank → ℤ)) : Prop where
  nodup : (F ++ Low ++ High).Nodup
  pos : ∀ β ∈ F ++ Low ++ High, IsRoot τ β ∧ 0 < height β
  level : ∀ β ∈ F ++ Low ++ High, 2 ≤ iform β F.sum
  complete : ∀ ρ, IsRoot τ ρ → 2 ≤ iform ρ F.sum → ρ ∈ F ++ Low ++ High
  abel : ∀ β ∈ F ++ Low ++ High, ∀ β' ∈ F ++ Low ++ High, ¬ IsRoot τ (β + β')
  low : ∀ ρ ∈ F ++ Low, ∀ β ∈ F ++ Low ++ High, IsRoot τ (ρ - β) → 0 < height (ρ - β) →
    β ∈ Low
  dom : ∀ i, 0 ≤ iform (Pi.single i 1) F.sum
  tuple : ∀ w : WeylGroup τ, (∀ β ∈ F, w • β ∈ F ++ High) → ∀ β ∈ F, w • β ∈ F

@[expose] def BorelCond {K : Type} [Field K] (F Low : List (Fin τ.rank → ℤ))
    (c : (Fin τ.rank → ℤ) → K) : Prop :=
  (∀ β ∈ F, c β ≠ 0) ∧ ∀ β ∈ Low, c β = 0

theorem FrameBruhatData.of_check {F Low High : List (Fin τ.rank → ℤ)}
    (hnd : (F ++ Low ++ High).Nodup)
    (hpos : ∀ β ∈ F ++ Low ++ High,
      List.ofFn β ∈ τ.artifactRoots ∧ 0 < height β ∧ 2 ≤ iform β F.sum)
    (hlow : ∀ ρ ∈ F ++ Low, ∀ β ∈ F ++ High, 0 < height (ρ - β) →
      List.ofFn (ρ - β) ∉ τ.artifactRoots)
    (hdom : ∀ i, 0 ≤ iform (Pi.single i 1) F.sum) (htup : tupleCheck F High = true)
    (hFnd : F.Nodup) (hFo : F.Pairwise fun a b => iform a b = 0)
    (hroots : ∀ k < τ.rootCertificate.roots.length,
      iform (τ.rootCertificate.root k) F.sum ≤ 3 ∧
        (2 ≤ iform (τ.rootCertificate.root k) F.sum →
          τ.rootCertificate.root k ∈ F ++ Low ++ High)) :
    FrameBruhatData F Low High := by
  have hk : ∀ {ρ}, IsRoot τ ρ →
      iform ρ F.sum ≤ 3 ∧ (2 ≤ iform ρ F.sum → ρ ∈ F ++ Low ++ High) := by
    intro ρ hρ
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check τ) hρ
    exact hroots k hk
  refine ⟨hnd, fun β hβ => ⟨isRoot_iff_mem_artifactRoots.2 (hpos β hβ).1, (hpos β hβ).2.1⟩,
    fun β hβ => (hpos β hβ).2.2, fun ρ hρ => (hk hρ).2, fun β hβ β' hβ' h => ?_,
    fun ρ hρ β hβ h1 h2 => ?_, hdom, fun w hw => smul_mem_of_tupleCheck hFnd hFo htup hw⟩
  · have h3 := (hk h).1
    rw [iform_add_left] at h3
    have := (hpos β hβ).2.2
    have := (hpos β' hβ').2.2
    omega
  · have hr := isRoot_iff_mem_artifactRoots.1 h1
    rcases List.mem_append.1 hβ with hβ | hβ
    · rcases List.mem_append.1 hβ with hβ | hβ
      · exact absurd hr (hlow ρ hρ β (List.mem_append_left _ hβ) h2)
      · exact hβ
    · exact absurd hr (hlow ρ hρ β (List.mem_append_right _ hβ) h2)

section Engine

variable
  {K : Type} [Field K]

namespace FrameBruhatData

variable {F Low High : List (Fin τ.rank → ℤ)} (D : FrameBruhatData F Low High)
include D

theorem conj_hyp_of_level_nonneg {α : Fin τ.rank → ℤ} (hα0 : 0 ≤ iform α F.sum) :
    ∀ β ∈ F ++ Low ++ High, α ≠ -β ∧ (IsRoot τ (α + β) → α + β ∈ F ++ Low ++ High) := by
  intro β hβ
  have hβ2 := D.level β hβ
  refine ⟨fun h => ?_, fun hr => D.complete _ hr ?_⟩
  · have h0 : iform (α + β) F.sum = 0 := by
      rw [h, neg_add_cancel]
      simp [iform]
    rw [iform_add_left] at h0
    omega
  · rw [iform_add_left]
    omega

theorem comm : RootCommFamily τ K (F ++ Low ++ High) := fun _ hβ _ hβ' s t =>
  CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (D.pos _ hβ).1 (D.pos _ hβ').1
    (fun h => by
      have h1 := (D.pos _ hβ).2
      have h2 := (D.pos _ hβ').2
      rw [h, height_neg] at h1
      omega) (D.abel _ hβ _ hβ') s t

theorem rootProd_indicator :
    rootProd τ K (F ++ Low ++ High) (fun ρ => if ρ ∈ F then (fun _ => (1 : K)) ρ else 0) =
      (F.map fun σ => pinnedX τ K σ 1).prod := by
  classical
  rw [E6Pilot.rootProd_ite_mem]
  have hF : (F ++ Low ++ High).filter (· ∈ F) = F := by
    have hnd := D.nodup
    rw [List.filter_append, List.filter_append,
      List.filter_eq_self.2 fun a ha => by simpa using ha]
    have h1 : Low.filter (· ∈ F) = [] := List.filter_eq_nil_iff.2 fun a ha haF => by
      rw [List.append_assoc] at hnd
      exact (List.nodup_append.1 hnd).2.2 a (by simpa using haF) a
        (List.mem_append_left _ ha) rfl
    have h2 : High.filter (· ∈ F) = [] := List.filter_eq_nil_iff.2 fun a ha haF => by
      rw [List.append_assoc] at hnd
      exact (List.nodup_append.1 hnd).2.2 a (by simpa using haF) a
        (List.mem_append_right _ ha) rfl
    rw [h1, h2, List.append_nil, List.append_nil]
  rw [hF]
  rfl

theorem conj_borelCond_of_pos {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) (t : K)
    {c : (Fin τ.rank → ℤ) → K} (hc : BorelCond F Low c) :
    BorelCond F Low (conjCoeff α t (F ++ Low ++ High) c) := by
  have hfeed : ∀ ρ, (ρ ∈ F ++ Low) → ρ ∈ F ++ Low ++ High →
      conjCoeff α t (F ++ Low ++ High) c ρ = c ρ := fun ρ hρ hρΨ =>
    E6Pilot.conjCoeff_apply_of_forall D.nodup t c hρΨ fun β hβ he =>
      hc.2 β (D.low ρ hρ β hβ (by rw [← he, add_sub_cancel_right]; exact hα.1)
        (by rw [← he, add_sub_cancel_right]; exact hα.2))
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · rw [hfeed β (List.mem_append_left _ hβ)
      (List.mem_append_left _ (List.mem_append_left _ hβ))]
    exact hc.1 β hβ
  · rw [hfeed β (List.mem_append_right _ hβ)
      (List.mem_append_left _ (List.mem_append_right _ hβ))]
    exact hc.2 β hβ

theorem borelGroup_le_rootProdInvSubgroup (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [CharP K 2] :
    borelGroup τ K ≤ rootProdInvSubgroup τ K (F ++ Low ++ High) (BorelCond F Low) := by
  have hr : ∀ β ∈ F ++ Low ++ High, IsRoot τ β := fun β hβ => (D.pos β hβ).1
  refine sup_le (torusGroup_le_rootProdInvSubgroup hr fun g hg c hc =>
    ⟨fun β hβ => ?_, fun β hβ => ?_⟩) (rootSpan_le_rootProdInvSubgroup fun α hα t =>
      pinnedX_mem_rootProdInvSubgroup (fun t c hc =>
        ⟨_, E6Pilot.conj_rootProd hτ CharTwo.two_eq_zero D.nodup hr D.comm hα.1
          (D.conj_hyp_of_level_nonneg (iform_nonneg_of_pos D.dom hα)) t c,
          D.conj_borelCond_of_pos hα t hc⟩) t)
  · exact mul_ne_zero (torusRootChar_ne_zero (torusGroup_le_diagonalGroup hg) β) (hc.1 β hβ)
  · show torusRootChar g β * c β = 0
    rw [hc.2 β hβ, mul_zero]

theorem map_comm (w : WeylGroup τ) :
    RootCommFamily τ K ((F ++ Low ++ High).map fun β => w • β) := by
  intro β hβ β' hβ' s t
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
  obtain ⟨γ', hγ', rfl⟩ := List.mem_map.1 hβ'
  refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (IsRoot.smul (D.pos γ hγ).1 w)
    (IsRoot.smul (D.pos γ' hγ').1 w) ?_ ?_ s t
  · rw [← smul_neg]
    intro h
    have h' := smul_left_cancel w h
    have h1 := (D.pos _ hγ).2
    have h2 := (D.pos _ hγ').2
    rw [h', height_neg] at h1
    omega
  · rw [← smul_add, isRoot_smul_iff]
    exact D.abel γ hγ γ' hγ'

theorem smul_frame_of_commute (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [CharP K 2]
    {g : ModGL τ K} {w : WeylGroup τ} (hw : g ∈ bruhatCell τ K w)
    (hgx : g * (F.map fun σ => pinnedX τ K σ 1).prod =
      (F.map fun σ => pinnedX τ K σ 1).prod * g) :
    ∀ β ∈ F, w • β ∈ F ++ High := by
  classical
  set Ψ := F ++ Low ++ High with hΨ
  set x := (F.map fun σ => pinnedX τ K σ 1).prod with hx
  set c₀ : (Fin τ.rank → ℤ) → K := fun ρ => if ρ ∈ F then (fun _ => (1 : K)) ρ else 0 with hc₀
  have hc₀B : BorelCond F Low c₀ := by
    refine ⟨fun β hβ => by simp [hc₀, hβ], fun β hβ => ?_⟩
    have hβF : β ∉ F := by
      intro hF
      have hnd := D.nodup
      rw [List.append_assoc] at hnd
      exact (List.nodup_append.1 hnd).2.2 β hF β (List.mem_append_left _ hβ) rfl
    simp [hc₀, hβF]
  have hx₀ : rootProd τ K Ψ c₀ = x := D.rootProd_indicator
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem τ) K w with hn
  obtain ⟨⟨cu, ecu, hcu⟩, -⟩ := D.borelGroup_le_rootProdInvSubgroup hτ hb' c₀ hc₀B
  obtain ⟨-, ⟨cv, ecv, hcv⟩⟩ := D.borelGroup_le_rootProdInvSubgroup hτ hb c₀ hc₀B
  rw [hx₀] at ecu ecv
  have hkey : n * rootProd τ K Ψ cu * n⁻¹ = rootProd τ K Ψ cv := by
    rw [← ecu, ← ecv]
    have e : b * n * b' * x * (b * n * b')⁻¹ = x := by
      rw [hgx]
      group
    calc n * (b' * x * b'⁻¹) * n⁻¹ = b⁻¹ * (b * n * b' * x * (b * n * b')⁻¹) * b := by
          group
      _ = b⁻¹ * x * b := by rw [e]
  have hr : ∀ β ∈ Ψ, IsRoot τ β := fun β hβ => (D.pos β hβ).1
  have htrans : n * rootProd τ K Ψ cu * n⁻¹ =
      rootProd τ K (Ψ.map fun β => w • β) fun ρ => cu (w⁻¹ • ρ) := by
    rw [hn, E6Pilot.rootProd, E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo w hr cu,
      E6Pilot.rootProd, List.map_map]
    congr 1
    refine List.map_congr_left fun β _ => ?_
    simp [inv_smul_smul]
  rw [htrans] at hkey
  intro β hβ
  have hβΨ : β ∈ Ψ := List.mem_append_left _ (List.mem_append_left _ hβ)
  have hLnd : (Ψ.map fun β => w • β).Nodup := D.nodup.map (MulAction.injective w)
  have hLr : ∀ ρ ∈ Ψ.map (fun β => w • β), IsRoot τ ρ := by
    intro ρ hρ
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hρ
    exact IsRoot.smul (hr γ hγ) w
  obtain ⟨hmem, heq⟩ := E6Pilot.mem_and_eq_of_rootProd_eq hLnd hLr (D.map_comm w) D.nodup
    D.pos D.comm hkey (List.mem_map_of_mem hβΨ) (by rw [inv_smul_smul]; exact hcu.1 β hβ)
  rw [inv_smul_smul] at heq
  have hne : cv (w • β) ≠ 0 := by rw [heq]; exact hcu.1 β hβ
  have hnl : w • β ∉ Low := fun h => hne (hcv.2 _ h)
  rcases List.mem_append.1 hmem with h | h
  · rcases List.mem_append.1 h with h' | h'
    · exact List.mem_append_left _ h'
    · exact absurd h' hnl
  · exact List.mem_append_right _ h

theorem mem_parabolicSubgroup_of_commute_frame (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [CharP K 2] {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hgx : g * (F.map fun σ => pinnedX τ K σ 1).prod =
      (F.map fun σ => pinnedX τ K σ 1).prod * g) :
    g ∈ parabolicSubgroup τ K {i | iform (Pi.single i 1) F.sum = 0} := by
  obtain ⟨w, hw⟩ := CFSG.SeitzReduction.exists_mem_bruhatCell_of_mem_adjointGroup hg
  have hperm := D.tuple w (D.smul_frame_of_commute hτ hw hgx)
  have hFnd : F.Nodup := by
    have hnd := D.nodup
    rw [List.append_assoc] at hnd
    exact (List.nodup_append.1 hnd).1
  have hσ : w • F.sum = F.sum := by
    have hsub : F.map (w • ·) ⊆ F := fun β hβ => by
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
      exact hperm γ hγ
    have hp : (F.map (w • ·)).Perm F :=
      (List.subperm_of_subset (hFnd.map (MulAction.injective w)) hsub).perm_of_length_le
        (by rw [List.length_map])
    rw [List.smul_sum, hp.sum_eq]
  have hW := mem_parabolicWeylGroup_of_smul_eq hτ D.dom _ w rfl hσ
  have hmem : g ∈ (parabolicSubgroup τ K {i | iform (Pi.single i 1) F.sum = 0} :
      Set (ModGL τ K)) := by
    rw [(standard_parabolic_cells τ K).1]
    exact Set.mem_biUnion hW hw
  exact hmem

end FrameBruhatData

end Engine

variable
  {K : Type} [Field K]

theorem cent_e7FramePt_le_parabolic [CharP K 2] {F Low High : List (Fin Tag.E7.rank → ℤ)}
    (D : FrameBruhatData F Low High) :
    ∀ g ∈ Exc.cent (e7FramePt K F),
      (g : ModGL .E7 K) ∈ parabolicSubgroup .E7 K {i | iform (Pi.single i 1) F.sum = 0} := by
  intro g hg
  rw [Exc.cent, mem_centralizer_singleton_iff] at hg
  refine D.mem_parabolicSubgroup_of_commute_frame (Or.inr (Or.inr (Or.inl rfl))) g.2 ?_
  have h := congrArg Subtype.val hg
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
  exact h

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
