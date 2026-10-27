module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3SolvableStrong
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G]

theorem centralizer_singleton_conj_eq_map (c x : G) :
    Subgroup.centralizer ({c * x * c⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro hy
    refine ⟨c⁻¹ * y * c, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h : c * ((c⁻¹ * y * c) * x) * c⁻¹ = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by
        calc c * ((c⁻¹ * y * c) * x) * c⁻¹ = y * (c * x * c⁻¹) := by group
          _ = (c * x * c⁻¹) * y := hy
          _ = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * z * c⁻¹ * (c * x * c⁻¹) = c * (z * x) * c⁻¹ := by group
      _ = c * (x * z) * c⁻¹ := by rw [hz]
      _ = c * x * c⁻¹ * (c * z * c⁻¹) := by group

variable [Finite G]

theorem exists_conj_pRank_centralizer_le_of_sylow {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    {x₀ : G} (hx₀ : x₀ ∈ (P : Subgroup G)) :
    ∃ c : G, c * x₀ * c⁻¹ ∈ (P : Subgroup G) ∧
      CFSG.Open.pRank p (Subgroup.centralizer ({c * x₀ * c⁻¹} : Set G)) ≤
        CFSG.Open.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer ({c * x₀ * c⁻¹} : Set G)) := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  set C₀ : Subgroup G := Subgroup.centralizer ({x₀} : Set G) with hC₀
  have hxC₀ : x₀ ∈ C₀ := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hT : IsPGroup p ↥((P : Subgroup G) ⊓ C₀) := P.isPGroup'.to_inf_left
  have hT' : IsPGroup p (((P : Subgroup G) ⊓ C₀).subgroupOf C₀) := hT.comap_subtype
  obtain ⟨S, hS⟩ := hT'.exists_le_sylow
  set S' : Subgroup G := (S : Subgroup C₀).map C₀.subtype with hS'
  have hS'p : IsPGroup p S' := S.isPGroup'.map C₀.subtype
  have hS'C : S' ≤ C₀ := Subgroup.map_subtype_le _
  have hx₀S' : x₀ ∈ S' := by
    refine Subgroup.mem_map.mpr ⟨⟨x₀, hxC₀⟩, hS ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨hx₀, hxC₀⟩
  obtain ⟨c, hc⟩ := exists_conjugate_le_sylow_of_le p P (le_top : (P : Subgroup G) ≤ ⊤) le_top hS'p
  refine ⟨(c : G), ?_, ?_⟩
  · refine hc ⟨x₀, hx₀S', ?_⟩
    simp [MulAut.conj_apply]
  · rw [centralizer_singleton_conj_eq_map]
    have h1 : CFSG.Open.pRank p C₀ = CFSG.Open.pRank p (⊤ : Subgroup C₀) :=
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup C₀
    have h2 : CFSG.Open.pRank p (S : Subgroup C₀) = CFSG.Open.pRank p (⊤ : Subgroup C₀) :=
      (CFSG.SectionRank.pRank_sylow S).1
    have h3 : CFSG.Open.pRank p (S : Subgroup C₀) ≤ CFSG.Open.pRank p S' :=
      CFSG.SectionRank.pRank_le_map hp1 C₀.subtype C₀.subtype_injective _
    have h4 : CFSG.Open.pRank p (S'.map (MulAut.conj (c : G)).toMonoidHom) =
        CFSG.Open.pRank p S' :=
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_map_automorphism p hp1 S' (MulAut.conj (c : G))
    have h5 : S'.map (MulAut.conj (c : G)).toMonoidHom ≤
        (P : Subgroup G) ⊓ C₀.map (MulAut.conj (c : G)).toMonoidHom :=
      le_inf hc (Subgroup.map_mono hS'C)
    have h6 : CFSG.Open.pRank p (C₀.map (MulAut.conj (c : G)).toMonoidHom) =
        CFSG.Open.pRank p C₀ :=
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_map_automorphism p hp1 C₀ (MulAut.conj (c : G))
    calc CFSG.Open.pRank p (C₀.map (MulAut.conj (c : G)).toMonoidHom)
        = CFSG.Open.pRank p C₀ := h6
      _ ≤ CFSG.Open.pRank p S' := by rw [h1, ← h2]; exact h3
      _ = CFSG.Open.pRank p (S'.map (MulAut.conj (c : G)).toMonoidHom) := h4.symm
      _ ≤ _ := pRank_mono p hp.out h5

theorem D2L34SideCtx3.normalizer_zpowers_le_of_pure {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {x : G} (hxP : x ∈ (P : Subgroup G))
    (hxo : orderOf x = 3)
    (hpure : 3 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x ⊔
        ((P : Subgroup G) ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)))) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M := by
  have hQP : Subgroup.zpowers x ≤ (P : Subgroup G) := Subgroup.zpowers_le.mpr hxP
  have hQ1 : Subgroup.zpowers x ≠ ⊥ := by
    intro hbot
    have : x = 1 := by
      have := Subgroup.mem_zpowers x
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [this, orderOf_one] at hxo
    omega
  exact (h.threeClause h.sigma P h.core).1 (Subgroup.zpowers x) hQP hQ1
    (by simpa [Subgroup.centralizer, Set.centralizer] using hpure)

theorem D2L34SideCtx3.exists_rankTwo_of_not_stronglyEmbedded {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) (hns : ¬ GLBStronglyEmbedded 3 M) :
    ∃ x ∈ (P : Subgroup G), orderOf x = 3 ∧
      CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set G)) ≤ 2 ∧
      ¬ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₀, hx₀P, hx₀o, -, hx₀N⟩ := h.exists_impure_of_not_stronglyEmbedded hns
  obtain ⟨c, hcP, hcrank⟩ := exists_conj_pRank_centralizer_le_of_sylow P hx₀P
  set x : G := c * x₀ * c⁻¹ with hx
  have hxo : orderOf x = 3 := by
    have h1 := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x₀
    have h2 : (MulAut.conj c).toMonoidHom x₀ = x := by simp [hx, MulAut.conj_apply]
    rw [h2, hx₀o] at h1
    exact h1
  have hU := h.fullCore 3 h.sigma P h.core
  have hA : Subgroup.zpowers x₀ ≤ (P : Subgroup G) := Subgroup.zpowers_le.mpr hx₀P
  have hg : (Subgroup.zpowers x₀).map (MulAut.conj (c⁻¹)⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hcP
  obtain ⟨m, hmM, hm⟩ :=
    exists_mem_conj_eq_of_map_le_of_gamma_two h.setting h.sigma h.core hU hA hg
  have hxm : m⁻¹ * x₀ * m = x := by
    have := hm x₀ (Subgroup.mem_zpowers x₀)
    simpa [hx] using this
  have hxN : ¬ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M := by
    intro hN
    refine hx₀N (normalizer_zpowers_le_of_conj (m := m⁻¹) (M.inv_mem hmM) ?_)
    rw [inv_inv, hxm]
    exact hN
  have hlt : CFSG.Open.pRank 3 (Subgroup.zpowers x ⊔ ((P : Subgroup G) ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set G))) < 3 := by
    by_contra hge
    exact hxN (h.normalizer_zpowers_le_of_pure hcP hxo (not_lt.mp hge))
  have hsub : (P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.zpowers x ⊔
        ((P : Subgroup G) ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
    intro y hy
    have hyC : y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hxy : Commute x y := (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
      exact (Commute.zpow_left hxy k).eq
    exact Subgroup.mem_sup_right ⟨hy.1, hyC⟩
  have hP2 : CFSG.Open.pRank 3 ((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 2 := by
    have := pRank_mono 3 Nat.prime_three hsub
    omega
  exact ⟨x, hcP, hxo, hcrank.trans hP2, hxN⟩

@[expose] def D2L34BetaMSolvableImpure3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → Group.IsSolvable M →
    ∀ x ∈ (P : Subgroup G), orderOf x = 3 →
      CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set G)) ≤ 2 →
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M

theorem D2L34BetaMSolvableImpure3.toStrong3 (h : D2L34BetaMSolvableImpure3 G) :
    D2L34BetaMSolvableStrong3 G := by
  intro d P M A H R Rbar K ctx hs
  by_contra hns
  obtain ⟨x, hxP, hxo, hrk, hN⟩ := ctx.exists_rankTwo_of_not_stronglyEmbedded hns
  exact hN (h d P M A H R Rbar K ctx hs x hxP hxo hrk)

theorem D2L34BetaMSolvableStrong3.toImpure3 (h : D2L34BetaMSolvableStrong3 G) :
    D2L34BetaMSolvableImpure3 G := by
  intro d P M A H R Rbar K ctx hs x hxP hxo _
  have hstr := h d P M A H R Rbar K ctx hs
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have hxM : x ∈ M := hPM hxP
  have hzp : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hxo]
    simp
  have hne : Subgroup.zpowers x ≠ ⊥ := by
    intro hbot
    have : x = 1 := by
      have := Subgroup.mem_zpowers x
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [this, orderOf_one] at hxo
    omega
  exact CFSG.AGLEmbeddingD2.normalizer_le_of_stronglyEmbedded Nat.prime_three hstr hzp
    (Subgroup.zpowers_le.mpr hxM) hne

end CFSG.LocalAnalysis.RankThreeTheoremC
