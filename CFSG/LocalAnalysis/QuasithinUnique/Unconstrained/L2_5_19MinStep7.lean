module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinSwap
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20A6Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def L2pGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X D : Subgroup G), IsL2pType ↥X → IsSylowTwoOf D X →
    ∀ W : Subgroup G, (∀ a ∈ D, a ≠ 1 → a ^ 2 = 1 →
      X ⊓ Subgroup.centralizer ({a} : Set G) ≤ W) → X ≤ W

section Step7

variable {G : Type} [Group G]

theorem IsComponentIn.ne_bot' {L H : Subgroup G} (h : IsComponentIn L H) : L ≠ ⊥ := by
  have hq := BenderBranch.isQuasisimple_of_isComponentIn h
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have : Nontrivial ↥L := (QuotientGroup.mk_surjective (s := Subgroup.center ↥L)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot L).mp this

theorem isL2pType_conjugate {K : Subgroup G} (g : G) (hK : IsL2pType ↥K) :
    IsL2pType ↥(CFSG.conjugate K g) := by
  let e : ↥K ≃* ↥(CFSG.conjugate K g) :=
    Subgroup.equivMapOfInjective K (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  rcases hK with ⟨p, hp, h7, hm⟩ | hm
  · exact Or.inl ⟨p, hp, h7, Unc25Small.statedClassicalModel_psl_of_mulEquiv e.symm hm⟩
  · exact Or.inr (Unc25Small.statedClassicalModel_psl_of_mulEquiv e.symm hm)

variable [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP R2 : Subgroup G}

theorem isL2pType_of_K0_ne (h : Lv2518 N t zK) (hne : N.K0 ≠ N.K) : IsL2pType ↥N.K := by
  obtain ⟨s₀, hs₀S, hne₁, hK0, hcomm⟩ := (h.facts254.shape).resolve_left hne
  rcases h.concl2516 with h1 | ⟨h2, -⟩ | ⟨h3, -⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exfalso
    have he : CFSG.Assembly.evenRank G ≤ 2 := hs.setting.qtke.2.2
    let e : ↥N.K ≃* ↥(CFSG.conjugate N.K s₀) :=
      Subgroup.equivMapOfInjective N.K (MulAut.conj s₀⁻¹).toMonoidHom (MulAut.conj s₀⁻¹).injective
    have hAB : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K s₀, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    exact false_of_A6_pair he a6RankFacts (A := N.K) (B := CFSG.conjugate N.K s₀) h3
      ⟨e.symm.trans h3.some⟩ hAB

theorem Ident2519.t_not_mem_centralizer (hid : Ident2519 N t i Ki KP R2) :
    t ∉ Subgroup.centralizer (KP : Set G) := by
  intro htc
  have hcomm : ∀ x ∈ KP, x * t = t * x := fun x hx => Subgroup.mem_centralizer_iff.mp htc x hx
  rcases hid.shape with ⟨hne1, hKPeq, -⟩ | ⟨hKPeq, hcomm'⟩
  · apply hne1
    have hKi : Ki ≤ KP := hKPeq ▸ le_sup_left
    symm
    rw [BenderBranch.conjugate_eq_iff_mem_normalizer]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x (hKi hx))
  · apply hid.comp.ne_bot'
    rw [← hcomm']
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute x t := hcomm x (hKPeq ▸ hx)
    exact (hc.zpow_right k).symm.eq

theorem Ident2519.false_of_claim (hL2p : L2pFacts) (hGen : L2pGen)
    (hid : Ident2519 N t i Ki KP R2) (h : Lv2518 N t zK) (hi : Hyp2519 N i)
    (hiZ : ∀ n ∈ N.S, n ∈ Subgroup.normalizer (N.K : Set G) → n * i = i * n) : False := by
  have hf := h.facts2511
  have he : CFSG.Assembly.evenRank G ≤ 2 := hs.setting.qtke.2.2
  have hne : N.K0 ≠ N.K := by
    intro hK0
    apply hi.not_mem_centerOf_S h
    refine ⟨hi.mem_S, Subgroup.mem_centralizer_iff.mpr fun s hs' => ?_⟩
    have hsN : s ∈ Subgroup.normalizer (N.K : Set G) := by
      have := N.S_le_normalizer_K0 hs'
      rwa [hK0] at this
    exact hiZ s hs' hsN
  have hKtype : IsL2pType ↥N.K := isL2pType_of_K0_ne h hne
  obtain ⟨s₀, hs₀S, hne₁, hK0, hcomm⟩ := (h.facts254.shape).resolve_left hne
  set K₂ : Subgroup G := CFSG.conjugate N.K s₀ with hK₂
  have hAB : ∀ a ∈ N.K, ∀ b ∈ K₂, a * b = b * a := fun a ha b hb =>
    BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
  have hK₂type : IsL2pType ↥K₂ := isL2pType_conjugate s₀ hKtype
  have hamb : L2pAmb K₂ := L2pAmb.of_data _ (hL2p _ hK₂type)
  have hSB : IsSylowTwoOf (N.S ⊓ K₂) K₂ := by
    have h1 := N.SK_sylow.map_equiv (MulAut.conj s₀⁻¹)
    have hS : CFSG.conjugate N.S s₀ = N.S :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hs₀S)
    have h2 : IsSylowTwoOf (CFSG.conjugate (N.S ⊓ N.K) s₀) (CFSG.conjugate N.K s₀) := h1
    rwa [BenderBranch.conjugate_inf, hS] at h2
  have hK₂K0 : K₂ ≤ N.K0 := by rw [hK0]; exact le_sup_right
  have hK₂cent : K₂ ≤ Subgroup.centralizer (N.K : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun k hk => hAB k hk y hy
  have htK₂ : ∀ y ∈ K₂, y * t = t * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp hf.t_mem.2 y (hK₂K0 hy)
  have htR : t ∈ Rgrp2519 N i := N.t_mem_R hf hi.mem_S
  have hidx := hid.R0_index hKtype
  have hN_of_inv : ∀ a ∈ N.S ⊓ K₂, a ≠ 1 → a ^ 2 = 1 →
      K₂ ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (KP : Set G) := by
    intro a ha ha1 ha2
    have haK : a ∈ Subgroup.centralizer (N.K : Set G) := hK₂cent ha.2
    have haR : a ∈ Rgrp2519 N i :=
      ⟨⟨ha.1, Subgroup.mem_centralizer_singleton_iff.mpr
        (hiZ a ha.1 (Subgroup.centralizer_le_normalizer _ haK))⟩, ha.1, haK⟩
    have hat : a * t = t * a := (N.t_comm_of_mem_S hf ha.1).symm
    have haa : a * a = 1 := by rw [← pow_two]; exact ha2
    obtain ⟨j, hjR0, hj1, hj2, hCj⟩ : ∃ j ∈ Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G),
        j ≠ 1 ∧ j ^ 2 = 1 ∧ ∀ y ∈ K₂, y * a = a * y → y * j = j * y := by
      rcases mem_or_mul_mem_of_relIndex_two hidx haR htR
          (fun htm => hid.t_not_mem_centralizer htm.2) with h0 | h0
      · exact ⟨a, h0, ha1, ha2, fun y _ hy => hy⟩
      · refine ⟨a * t, h0, ?_, ?_, ?_⟩
        · intro h1
          have hta : t = a := by
            have h2 : t = a⁻¹ := eq_inv_of_mul_eq_one_right h1
            rw [h2]
            exact inv_eq_of_mul_eq_one_right haa
          have htK : t ∈ K₂ := hta ▸ ha.2
          exact hf.t_ne_one (hamb.center_trivial t htK (fun y hy => htK₂ y hy))
        · rw [pow_two]
          calc a * t * (a * t) = a * (t * a) * t := by group
            _ = a * (a * t) * t := by rw [← hat]
            _ = (a * a) * (t * t) := by group
            _ = 1 := by rw [haa, N.t_mul_self' hf, one_mul]
        · intro y hy hya
          calc y * (a * t) = (y * a) * t := by group
            _ = (a * y) * t := by rw [hya]
            _ = a * (y * t) := by group
            _ = a * (t * y) := by rw [htK₂ y hy]
            _ = (a * t) * y := by group
    intro y hy
    exact hid.normal_C hKtype j hjR0 hj1 hj2
      (Subgroup.mem_centralizer_singleton_iff.mpr
        (hCj y hy.1 (Subgroup.mem_centralizer_singleton_iff.mp hy.2)))
  have hK₂N : K₂ ≤ Subgroup.normalizer (KP : Set G) :=
    hGen G K₂ (N.S ⊓ K₂) hK₂type hSB _ hN_of_inv
  have hperf : ⁅K₂, K₂⁆ = K₂ := by
    have hperfK : ⁅N.K, N.K⁆ = N.K :=
      Subgroup.isPerfect_iff.mp (BenderBranch.isQuasisimple_of_isComponentIn N.isComp).1
    show ⁅Subgroup.map _ N.K, Subgroup.map _ N.K⁆ = Subgroup.map _ N.K
    rw [← Subgroup.map_commutator, hperfK]
  have hK₂C : K₂ ≤ Subgroup.centralizer (KP : Set G) :=
    hid.perfect_cent hKtype K₂ hK₂N hK₂cent hperf
  obtain ⟨V, hVK, hV1, hV2, hV3, hVZ⟩ := hamb.a4
  have hKPV : KP ≤ Subgroup.normalizer (V : Set G) := by
    have h1 : KP ≤ Subgroup.centralizer (K₂ : Set G) := Subgroup.le_centralizer_iff.mp hK₂C
    have h2 : Subgroup.centralizer (K₂ : Set G) ≤ Subgroup.centralizer (V : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVK)
    exact (h1.trans h2).trans (Subgroup.centralizer_le_normalizer _)
  have hpc : pCoreOf 2 (Subgroup.normalizer (V : Set G)) ≠ ⊥ := by
    have hle : V ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V _ Subgroup.le_normalizer
        ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hV2
    intro hbot
    rw [hbot] at hle
    exact hV1 (le_bot_iff.mp hle)
  have hcomm' : ⁅KP, K₂ ⊓ Subgroup.normalizer (V : Set G)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mpr (inf_le_left.trans hK₂C))
  exact Unc25K1.false_of_commuting_copy he (X := Subgroup.normalizer (V : Set G)) (K := KP)
    (K' := K₂ ⊓ Subgroup.normalizer (V : Set G)) hpc hKPV inf_le_right hcomm' hid.three_rank hV3
    hVZ

end Step7

end CFSG.QuasithinUnique
