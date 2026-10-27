module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHighBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem map_conj_centralizer_inf_of_mem {G : Type*} [Group G] {C : Subgroup G} {n : G} (hn : n ∈ C)
    (x : G) :
    (centralizer ({x} : Set G) ⊓ C).map (MulAut.conj n).toMonoidHom =
      centralizer ({n * x * n⁻¹} : Set G) ⊓ C := by
  ext g
  rw [mem_map_equiv, MulAut.conj_symm_apply, mem_inf, mem_inf, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc g * (n * x * n⁻¹) = n * (n⁻¹ * g * n * x) * n⁻¹ := by group
        _ = n * (x * (n⁻¹ * g * n)) * n⁻¹ := by rw [h1]
        _ = n * x * n⁻¹ * g := by group
    · have h := mul_mem (mul_mem hn h2) (inv_mem hn)
      rwa [show n * (n⁻¹ * g * n) * n⁻¹ = g by group] at h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, mul_mem (mul_mem (inv_mem hn) h2) hn⟩
    calc n⁻¹ * g * n * x = n⁻¹ * (g * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * x * n⁻¹ * g) * n := by rw [h1]
      _ = x * (n⁻¹ * g * n) := by group

section InGL


theorem centralizer_pinnedX_highRoot_inf_eq (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {c : K}
    (hc : c ≠ 0) :
    centralizer ({pinnedX τ K (highRoot τ) c} : Set (ModGL τ K)) ⊓ adjointGroup τ K =
      parabolicRadical τ K (perpNodes τ) ⊔ rootSpan τ K (perpRoots τ) := by
  refine le_antisymm (fun g hg => ?_) (sup_le (fun q hq => ?_) (fun l hl => ?_))
  · obtain ⟨hgC, hgG⟩ := mem_inf.1 hg
    have hgz : pinnedX τ K (highRoot τ) c * g = g * pinnedX τ K (highRoot τ) c :=
      mem_centralizer_iff.1 hgC _ rfl
    have hgP := mem_parabolicSubgroup_perpNodes_of_conj hτ hgG hc (e := c)
      (by rw [← hgz]; group)
    have h := mem_parabolicRadical_sup_rootSpan_of_commute (z := pinnedX τ K (highRoot τ) c)
      (J := perpNodes τ)
      (fun q hq => commute_pinnedX_highRoot_of_mem_parabolicRadical hq c)
      (fun l hl => commute_pinnedX_highRoot_of_mem_perpLevi hτ
        (by rwa [parabolicRoots_perpNodes] at hl) c)
      (fun h hh hhz => by
        rw [parabolicRoots_perpNodes]
        exact mem_perpLevi_of_mem_torusGroup_of_commute hτ hh hc hhz)
      hgP hgz.symm
    rwa [parabolicRoots_perpNodes] at h
  · refine mem_inf.2 ⟨mem_centralizer_iff.2 ?_,
      posUnipotent_le_adjointGroup (parabolicRadical_le_posUnipotent _ hq)⟩
    rintro _ rfl
    exact (commute_pinnedX_highRoot_of_mem_parabolicRadical hq c).symm
  · refine mem_inf.2 ⟨mem_centralizer_iff.2 ?_, rootSpan_le_adjointGroup' _ hl⟩
    rintro _ rfl
    exact (commute_pinnedX_highRoot_of_mem_perpLevi hτ hl c).symm

theorem centralizer_pinnedX_highRoot_inf_eq_sup_centralizer [Finite K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : 4 ≤ Nat.card K) {c : K} (hc : c ≠ 0) :
    centralizer ({pinnedX τ K (highRoot τ) c} : Set (ModGL τ K)) ⊓ adjointGroup τ K =
      parabolicRadical τ K (perpNodes τ) ⊔
        adjointGroup τ K ⊓ centralizer (highRootSL2 τ K : Set (ModGL τ K)) := by
  rw [centralizer_highRootSL2_eq hτ hq]
  exact centralizer_pinnedX_highRoot_inf_eq hτ hc

theorem parabolicRadical_perpNodes_inf_rootSpan_perpRoots :
    parabolicRadical τ K (perpNodes τ) ⊓ rootSpan τ K (perpRoots τ) = ⊥ := by
  rw [← parabolicRoots_perpNodes]
  exact F4Pilot.parabolicRadical_inf_rootSpan _

theorem rootSpan_perpRoots_le_normalizer_parabolicRadical :
    rootSpan τ K (perpRoots τ) ≤
      normalizer (parabolicRadical τ K (perpNodes τ) : Set (ModGL τ K)) := by
  rw [← parabolicRoots_perpNodes]
  exact F4Pilot.rootSpan_parabolicRoots_le_normalizer _

theorem isPGroup_parabolicRadical [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (J : Set (Fin τ.rank)) : IsPGroup p (parabolicRadical τ K J) :=
  ((parabolic_root_radical_Levi_factors τ K J).2.2.2.2.2.2.2.2.2.2.2.2 p).2.1

theorem torusGroup_inf_centralizer_pinnedX_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {c : K}
    (hc : c ≠ 0) :
    torusGroup τ K ⊓ centralizer ({pinnedX τ K (highRoot τ) c} : Set (ModGL τ K)) =
      torusGroup τ K ⊓ rootSpan τ K (perpRoots τ) := by
  refine le_antisymm (fun h hh => ?_) (fun h hh => ?_)
  · obtain ⟨hhT, hhC⟩ := mem_inf.1 hh
    exact mem_inf.2 ⟨hhT, mem_perpLevi_of_mem_torusGroup_of_commute hτ hhT hc
      (mem_centralizer_singleton_iff.1 hhC)⟩
  · obtain ⟨hhT, hhD⟩ := mem_inf.1 hh
    exact mem_inf.2 ⟨hhT, mem_centralizer_singleton_iff.2
      (commute_pinnedX_highRoot_of_mem_perpLevi hτ hhD c)⟩

theorem torusGroup_inf_centralizer_highRoot_eq_closure (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : K} (hc : c ≠ 0) :
    torusGroup τ K ⊓ centralizer ({pinnedX τ K (highRoot τ) c} : Set (ModGL τ K)) =
      closure {g | ∃ j : Fin τ.rank, j ≠ highNode τ ∧ ∃ u : Kˣ, torusElt τ K j u = g} := by
  refine le_antisymm (fun h hh => ?_) ((closure_le _).2 ?_)
  · obtain ⟨hhT, hhC⟩ := mem_inf.1 hh
    have hθ := conj_pinnedX_highRoot_one_of_commute hhT hc (mem_centralizer_singleton_iff.1 hhC)
    obtain ⟨c', rfl⟩ := exists_cartanChar_eq_of_mem_torusGroup hhT
    have hc' : c' (highNode τ) = 1 := by
      rw [rootDiagUnit_conj_pinnedX _ (isRoot_highRoot τ)] at hθ
      have e := pinnedX_injective τ K _ hθ
      rw [mul_one, rootChar_cartanChar_highRoot hτ] at e
      exact Units.ext e
    rw [← list_prod_torusElt_eq_rootDiagUnit]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    by_cases hj : j = highNode τ
    · subst hj
      rw [hc', torusElt_eq_rootDiagUnit]
      simp only [one_zpow]
      rw [show (fun _ : Fin τ.rank => (1 : Kˣ)) = 1 from rfl, rootDiagUnit_one]
      exact one_mem _
    · exact subset_closure ⟨j, hj, c' j, rfl⟩
  · rintro _ ⟨j, hj, u, rfl⟩
    exact mem_inf.2 ⟨subset_closure ⟨(j, u), rfl⟩, mem_centralizer_singleton_iff.2
      (commute_pinnedX_highRoot_of_mem_perpLevi hτ (torusElt_mem_rootSpan_perpRoots hj u) c)⟩

theorem parabolicLevi_perpNodes_inf_centralizer_eq (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {c : K}
    (hc : c ≠ 0) :
    parabolicLevi τ K (perpNodes τ) ⊓
        centralizer ({pinnedX τ K (highRoot τ) c} : Set (ModGL τ K)) =
      rootSpan τ K (perpRoots τ) := by
  refine le_antisymm (fun m hm => ?_) (fun l hl => mem_inf.2 ⟨?_, ?_⟩)
  · obtain ⟨hmM, hmC⟩ := mem_inf.1 hm
    have hm' : m ∈ (torusGroup τ K : Set (ModGL τ K)) *
        (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _
        (torusGroup_le_normalizer_rootSpan (fun α hα => hα.1)), ← parabolicRoots_perpNodes]
      exact F4Pilot.parabolicLevi_le_torusGroup_sup _ hmM
    obtain ⟨h, hh, l, hl, rfl⟩ := hm'
    have hcm : Commute (h * l) (pinnedX τ K (highRoot τ) c) := mem_centralizer_singleton_iff.1 hmC
    have hcl : Commute l (pinnedX τ K (highRoot τ) c) :=
      commute_pinnedX_highRoot_of_mem_perpLevi hτ hl c
    have hch : Commute h (pinnedX τ K (highRoot τ) c) := by
      have e : h = h * l * l⁻¹ := by group
      rw [e]
      exact hcm.mul_left hcl.inv_left
    exact mul_mem (mem_perpLevi_of_mem_torusGroup_of_commute hτ hh hc hch.eq) hl
  · rw [← parabolicRoots_perpNodes] at hl
    exact F4Pilot.rootSpan_parabolicRoots_le_parabolicLevi _ hl
  · exact mem_centralizer_singleton_iff.2 (commute_pinnedX_highRoot_of_mem_perpLevi hτ hl c)

end InGL

theorem torusGroup_eq_bot_of_forall_units_eq_one
    (h : ∀ u : Kˣ, u = 1) : torusGroup τ K = ⊥ := by
  refine eq_bot_iff.2 ((closure_le _).2 ?_)
  rintro _ ⟨⟨j, u⟩, rfl⟩
  change torusElt τ K j u ∈ (⊥ : Subgroup (ModGL τ K))
  rw [h u, mem_bot, torusElt_eq_rootDiagUnit]
  simp only [one_zpow]
  rw [show (fun _ : Fin τ.rank => (1 : Kˣ)) = 1 from rfl, rootDiagUnit_one]

section Inside


variable (τ K) in
@[expose] noncomputable def perpLevi : Subgroup (adjointGroup τ K) :=
  (rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K)

variable (τ K) in
@[expose] noncomputable def highRadical : Subgroup (adjointGroup τ K) :=
  (parabolicRadical τ K (perpNodes τ)).subgroupOf (adjointGroup τ K)


theorem isTwoRadicalDecomp_highRoot [Finite K] [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : K} (hc : c ≠ 0) :
    F4Pilot.IsTwoRadicalDecomp (pinnedElt τ (highRoot τ) c) (highRadical τ K) (perpLevi τ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQC : parabolicRadical τ K (perpNodes τ) ≤ adjointGroup τ K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  obtain ⟨h1, h2, h3⟩ := F4Pilot.decomp_subgroupOf hQC (rootSpan_le_adjointGroup' _)
    (pinnedElt τ (highRoot τ) c) (centralizer_pinnedX_highRoot_inf_eq hτ hc)
    parabolicRadical_perpNodes_inf_rootSpan_perpRoots
    rootSpan_perpRoots_le_normalizer_parabolicRadical
  exact ⟨F4Pilot.isPGroup_subgroupOf_of_le hQC (isPGroup_parabolicRadical 2 _), h1, h2, h3⟩

theorem factF3_highRoot [Finite K] [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ Q : Subgroup (adjointGroup τ K), IsPGroup 2 Q ∧
      Q ⊔ perpLevi τ K =
        centralizer ({pinnedElt τ (highRoot τ) (1 : K)} : Set (adjointGroup τ K)) ∧
      Q ⊓ perpLevi τ K = ⊥ ∧ perpLevi τ K ≤ normalizer (Q : Set (adjointGroup τ K)) :=
  ⟨_, isTwoRadicalDecomp_highRoot hτ one_ne_zero⟩

end Inside

@[expose] def rootPerp (τ : Tag) (γ : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {δ | IsRoot τ δ ∧ iform δ γ = 0}

@[expose] def radicalRoots (τ : Tag) (γ : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {δ | IsRoot τ δ ∧ 0 < iform δ γ}

section Transport


theorem rootPerp_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    rootPerp τ (highRoot τ) = perpRoots τ := by
  ext δ
  rw [mem_perpRoots_iff_iform hτ, iform_comm]
  rfl

theorem radicalRoots_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    radicalRoots τ (highRoot τ) = parabolicRadicalRoots τ (perpNodes τ) := by
  ext δ
  rw [mem_parabolicRadicalRoots_perpNodes_iff_iform hτ]
  rfl

theorem highRoot_mem_rootPerp (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ perpRoots τ) : highRoot τ ∈ rootPerp τ γ ∧ -highRoot τ ∈ rootPerp τ γ := by
  have h0 : iform (highRoot τ) γ = 0 := by rw [iform_highRoot hτ, hγ.2]
  refine ⟨⟨isRoot_highRoot τ, h0⟩, IsRoot.neg (isRoot_highRoot τ), ?_⟩
  rw [← neg_one_smul ℤ (highRoot τ), iform_smul_left, h0, mul_zero]

theorem image_smul_rootPerp (w : WeylGroup τ) (γ : Fin τ.rank → ℤ) :
    (fun δ => w • δ) '' rootPerp τ γ = rootPerp τ (w • γ) := by
  ext δ
  constructor
  · rintro ⟨β, ⟨hβ, hβγ⟩, rfl⟩
    exact ⟨IsRoot.smul hβ w, by rw [iform_smul]; exact hβγ⟩
  · rintro ⟨hδ, hδγ⟩
    refine ⟨w⁻¹ • δ, ⟨IsRoot.smul hδ w⁻¹, ?_⟩, smul_inv_smul w δ⟩
    rw [← iform_smul w, smul_inv_smul]
    exact hδγ

theorem image_smul_radicalRoots (w : WeylGroup τ) (γ : Fin τ.rank → ℤ) :
    (fun δ => w • δ) '' radicalRoots τ γ = radicalRoots τ (w • γ) := by
  ext δ
  constructor
  · rintro ⟨β, ⟨hβ, hβγ⟩, rfl⟩
    exact ⟨IsRoot.smul hβ w, by rw [iform_smul]; exact hβγ⟩
  · rintro ⟨hδ, hδγ⟩
    refine ⟨w⁻¹ • δ, ⟨IsRoot.smul hδ w⁻¹, ?_⟩, smul_inv_smul w δ⟩
    rw [← iform_smul w, smul_inv_smul]
    exact hδγ


theorem map_conj_parabolicRadical_perpNodes (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (w : WeylGroup τ) :
    (parabolicRadical τ K (perpNodes τ)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
      rootSpan τ K (radicalRoots τ (w • highRoot τ)) := by
  rw [parabolicRadical, (canonical_weyl_root_transport τ K).1 w _ (fun α hα => hα.1.1),
    ← radicalRoots_highRoot hτ, image_smul_radicalRoots]

theorem map_conj_rootSpan_perpRoots (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (w : WeylGroup τ) :
    (rootSpan τ K (perpRoots τ)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
      rootSpan τ K (rootPerp τ (w • highRoot τ)) := by
  rw [(canonical_weyl_root_transport τ K).1 w _ (fun α hα => hα.1), ← rootPerp_highRoot hτ,
    image_smul_rootPerp]

theorem exists_conj_canonicalRep_pinnedX_highRoot_eq (w : WeylGroup τ) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K,
      canonicalRep (coxeterSystem τ) K w * pinnedX τ K (highRoot τ) (ε * c) *
          (canonicalRep (coxeterSystem τ) K w)⁻¹ = pinnedX τ K (w • highRoot τ) c := by
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_highRoot τ)
  exact ⟨ε, hε, fun c => by rw [hεc, ← mul_assoc, hε, one_mul]⟩


theorem centralizer_pinnedX_inf_eq (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {c : K} (hc : c ≠ 0) :
    centralizer ({pinnedX τ K γ c} : Set (ModGL τ K)) ⊓ adjointGroup τ K =
      rootSpan τ K (radicalRoots τ γ) ⊔ rootSpan τ K (rootPerp τ γ) := by
  obtain ⟨w, rfl⟩ := exists_smul_highRoot_eq hτ hγ
  obtain ⟨ε, hε, hεc⟩ := exists_conj_canonicalRep_pinnedX_highRoot_eq (K := K) w
  have hεc0 : ε * c ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hε) hc
  have h := congrArg (Subgroup.map (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom)
    (centralizer_pinnedX_highRoot_inf_eq hτ hεc0)
  rw [map_conj_centralizer_inf_of_mem (canonicalRep_mem_adjointGroup _ K w), hεc, Subgroup.map_sup,
    map_conj_parabolicRadical_perpNodes hτ, map_conj_rootSpan_perpRoots hτ] at h
  exact h

theorem rootSpan_radicalRoots_inf_rootSpan_rootPerp
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootSpan τ K (radicalRoots τ γ) ⊓ rootSpan τ K (rootPerp τ γ) = ⊥ := by
  obtain ⟨w, rfl⟩ := exists_smul_highRoot_eq hτ hγ
  rw [← map_conj_parabolicRadical_perpNodes hτ, ← map_conj_rootSpan_perpRoots hτ,
    ← map_inf_eq _ _ _ (MulAut.conj _).injective,
    parabolicRadical_perpNodes_inf_rootSpan_perpRoots, Subgroup.map_bot]

theorem rootSpan_rootPerp_le_normalizer_radicalRoots
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootSpan τ K (rootPerp τ γ) ≤
      normalizer (rootSpan τ K (radicalRoots τ γ) : Set (ModGL τ K)) := by
  obtain ⟨w, rfl⟩ := exists_smul_highRoot_eq hτ hγ
  rw [← map_conj_parabolicRadical_perpNodes hτ, ← map_conj_rootSpan_perpRoots hτ,
    ← map_equiv_normalizer_eq]
  exact Subgroup.map_mono rootSpan_perpRoots_le_normalizer_parabolicRadical

theorem isPGroup_rootSpan_radicalRoots [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    IsPGroup p (rootSpan τ K (radicalRoots τ γ)) := by
  obtain ⟨w, rfl⟩ := exists_smul_highRoot_eq hτ hγ
  rw [← map_conj_parabolicRadical_perpNodes hτ]
  exact (isPGroup_parabolicRadical p _).map _

variable (τ K) in
@[expose] noncomputable def rootPerpLevi (γ : Fin τ.rank → ℤ) : Subgroup (adjointGroup τ K) :=
  (rootSpan τ K (rootPerp τ γ)).subgroupOf (adjointGroup τ K)

variable (τ K) in
@[expose] noncomputable def rootRadical (γ : Fin τ.rank → ℤ) : Subgroup (adjointGroup τ K) :=
  (rootSpan τ K (radicalRoots τ γ)).subgroupOf (adjointGroup τ K)

theorem isTwoRadicalDecomp_root [Finite K] [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {c : K} (hc : c ≠ 0) :
    F4Pilot.IsTwoRadicalDecomp (pinnedElt τ γ c) (rootRadical τ K γ) (rootPerpLevi τ K γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2, h3⟩ := F4Pilot.decomp_subgroupOf (rootSpan_le_adjointGroup' _)
    (rootSpan_le_adjointGroup' _) (pinnedElt τ γ c) (centralizer_pinnedX_inf_eq hτ hγ hc)
    (rootSpan_radicalRoots_inf_rootSpan_rootPerp hτ hγ)
    (rootSpan_rootPerp_le_normalizer_radicalRoots hτ hγ)
  exact ⟨F4Pilot.isPGroup_subgroupOf_of_le (rootSpan_le_adjointGroup' _)
    (isPGroup_rootSpan_radicalRoots 2 hτ hγ), h1, h2, h3⟩

theorem factF3_root [Finite K] [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ Q : Subgroup (adjointGroup τ K), IsPGroup 2 Q ∧
      Q ⊔ rootPerpLevi τ K γ = centralizer ({pinnedElt τ γ (1 : K)} : Set (adjointGroup τ K)) ∧
      Q ⊓ rootPerpLevi τ K γ = ⊥ ∧ rootPerpLevi τ K γ ≤ normalizer (Q : Set (adjointGroup τ K)) :=
  ⟨_, isTwoRadicalDecomp_root hτ hγ one_ne_zero⟩

end Transport

section Levi


theorem highRootSL2_le_rootSpan_rootPerp (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ perpRoots τ) :
    highRootSL2 τ K ≤ rootSpan τ K (rootPerp τ γ) := by
  obtain ⟨h1, h2⟩ := highRoot_mem_rootPerp hτ hγ
  exact sup_le
    (le_iSup₂_of_le (f := fun δ (_ : δ ∈ rootPerp τ γ) => rootSubgroup τ K δ) _ h1 le_rfl)
    (le_iSup₂_of_le (f := fun δ (_ : δ ∈ rootPerp τ γ) => rootSubgroup τ K δ) _ h2 le_rfl)

theorem highRootSL2_subgroupOf_le_rootPerpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ perpRoots τ) :
    (highRootSL2 τ K).subgroupOf (adjointGroup τ K) ≤ rootPerpLevi τ K γ :=
  fun _ hx => mem_subgroupOf.2 (highRootSL2_le_rootSpan_rootPerp hτ hγ (mem_subgroupOf.1 hx))

theorem pinnedElt_mem_perpLevi {γ : Fin τ.rank → ℤ} (hγ : γ ∈ perpRoots τ) (c : K) :
    pinnedElt τ γ c ∈ perpLevi τ K :=
  mem_subgroupOf.2 (pinnedX_mem_rootSpan hγ c)

end Levi

end CFSG.SeitzReduction.EPilot
