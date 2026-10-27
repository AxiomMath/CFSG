module

public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.LU.Arith
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.GH74.GLS.LU

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open

@[expose] def MaxOverCentralizerPSp4 {G : Type} [Group G] (z : G) (p f : ℕ) : Prop :=
  ∀ M : Subgroup G, IsCoatom M → Subgroup.centralizer ({z} : Set G) < M →
    IsCoatom ((Subgroup.centralizer ({z} : Set G)).subgroupOf M) ∧
      LieModel ↥(CFSG.generalizedFitting ↥M) StatedLieTag.PSp 2 p f

theorem natCard_of_lieModel_psp {N : Type} [Group N] {p f : ℕ} (hp2 : p ≠ 2)
    (h : LieModel N StatedLieTag.PSp 2 p f) : Nat.card N = ordBC 2 (p ^ f) := by
  rcases h with ⟨-, h⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 h).2.2.1 rfl
  · omega
  · omega
  · omega

theorem ordA_three_le_natCard_of_lieModel_psl {G₀ : Type} [Group G₀] [Finite G₀] {p f : ℕ}
    (hp2 : p ≠ 2) (h : LieModel (G₀ ⧸ Subgroup.center G₀) StatedLieTag.PSL 4 p f) :
    ordA 3 (p ^ f) ≤ Nat.card G₀ := by
  rcases h with ⟨-, h⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · have := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 h).1 rfl
    rw [← this]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
  · omega
  · omega
  · omega

theorem ordTwistedA_three_le_natCard_of_lieModel_psu {G₀ : Type} [Group G₀] [Finite G₀]
    {p f : ℕ} (hp2 : p ≠ 2) (h : LieModel (G₀ ⧸ Subgroup.center G₀) StatedLieTag.PSU 4 p f) :
    ordTwistedA 3 (p ^ f) ≤ Nat.card G₀ := by
  rcases h with ⟨-, h⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · have := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 h).2.1 rfl
    rw [← this]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
  · omega
  · omega
  · omega

theorem isQuasisimple_of_mulEquiv_aux {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.IsQuasisimple A) : CFSG.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

theorem eq_top_of_normalizer_ge_centralizer {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    {z : G} {G0 : Subgroup G} (hq : CFSG.IsQuasisimple ↥G0)
    (hCN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (G0 : Set G))
    (hnc : ∃ x ∈ G0, x * z ≠ z * x) {p f : ℕ} (hp2 : p ≠ 2)
    (h6A : MaxOverCentralizerPSp4 z p f) (hord : ordBC 2 (p ^ f) < Nat.card ↥G0) : G0 = ⊤ := by
  by_contra hne
  obtain ⟨x, hxG0, hxz⟩ := hnc
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  set M0 : Subgroup G := Subgroup.normalizer (G0 : Set G) with hM0def
  have hG0M0 : G0 ≤ M0 := Subgroup.le_normalizer
  have hxC : x ∉ C := fun hx => hxz (by
    have := Subgroup.mem_centralizer_iff.mp hx z rfl
    exact this.symm)
  have hCM0 : C < M0 := lt_of_le_of_ne hCN (fun h => hxC (h ▸ hG0M0 hxG0))
  by_cases htop : M0 = ⊤
  · have hnorm : G0.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.eq_bot_or_eq_top_of_normal G0 with hbot | htop'
    · apply hxz
      rw [hbot, Subgroup.mem_bot] at hxG0
      rw [hxG0, one_mul, mul_one]
    · exact hne htop'
  · obtain ⟨M, hMcoat, hM0M⟩ := (IsCoatomic.eq_top_or_exists_le_coatom M0).resolve_left htop
    have hCM : C < M := lt_of_lt_of_le hCM0 hM0M
    obtain ⟨hmax, hFM⟩ := h6A M hMcoat hCM
    have hlt : C.subgroupOf M < M0.subgroupOf M := by
      refine lt_of_le_of_ne (Subgroup.subgroupOf_mono M hCM0.le) fun h => ?_
      have h' := Subgroup.subgroupOf_inj.mp h
      rw [inf_eq_left.mpr hCM.le, inf_eq_left.mpr hM0M] at h'
      exact hCM0.ne h'
    have hM0eq : M ≤ M0 := Subgroup.subgroupOf_eq_top.mp (hmax.2 _ hlt)
    have hM0M' : M0 = M := le_antisymm hM0M hM0eq
    have hG0M : G0 ≤ M := hM0M' ▸ hG0M0
    have hnormM : (G0.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hG0M).mpr (hM0M' ▸ le_refl _)
    have hcomp : CFSG.IsComponent (G0.subgroupOf M) :=
      ⟨isQuasisimple_of_mulEquiv_aux (Subgroup.subgroupOfEquivOfLe hG0M).symm hq,
        hnormM.isSubnormal⟩
    have hle : G0.subgroupOf M ≤ CFSG.generalizedFitting ↥M :=
      le_trans (le_sSup hcomp : G0.subgroupOf M ≤ CFSG.layer ↥M) le_sup_right
    have hcard : Nat.card ↥G0 ≤ Nat.card ↥(CFSG.generalizedFitting ↥M) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hG0M).toEquiv]
      exact Subgroup.card_le_of_le hle
    rw [natCard_of_lieModel_psp hp2 hFM] at hcard
    omega

section Linear

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] {z u : G}
  {Y : Fin 3 → Subgroup G}

theorem IsLinearA3Neighborhood.lieModel (hG : IsSimpleGroup G) (h : IsLinearA3Neighborhood K z u Y)
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hq : 5 ≤ p ^ f)
    (hCN : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G))
    (h6A : MaxOverCentralizerPSp4 z p f) : LieModel G StatedLieTag.PSL 4 p f := by
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard
    (by rw [hK]; exact (hp.odd_of_ne_two hp2).pow)
  obtain ⟨ψ, hψr, hψk, hqs, hmodel⟩ := h.exists_surjection p f hp hp2 hK hq
  obtain ⟨hcomm, hpair⟩ := h.comm_pairs (by rw [hK]; omega) h2
  have hnc : ∃ x ∈ (⨆ i, Y i : Subgroup G), x * z ≠ z * x := by
    obtain ⟨x, hx, hxz⟩ := h.exists_noncommuting p f hp hp2 hK hq
    exact ⟨x, (le_iSup Y 1) hx, hxz⟩
  have hord : ordBC 2 (p ^ f) < Nat.card ↥(⨆ i, Y i : Subgroup G) :=
    lt_of_lt_of_le (ordBC_two_lt_ordA_three hq)
      (ordA_three_le_natCard_of_lieModel_psl hp2 hmodel)
  have htop : (⨆ i, Y i : Subgroup G) = ⊤ :=
    eq_top_of_normalizer_ge_centralizer hG hqs hCN hnc hp2 h6A hord
  exact CFSG.GH74.L5U5.lieModel_of_iSup_eq_top p f hp hK (by omega) (n := 3) (by norm_num) Y hcomm
    hpair htop hG

end Linear

section Unitary

variable {G : Type} [Group G] [Finite G] {K F : Type} [Field K] [Finite K] [Field F] [Finite F]
  {p f : ℕ} [Fact p.Prime] [CharP K p] {z u : G} {Y : Fin 3 → Subgroup G}

theorem IsUnitaryA3Neighborhood.lieModel (hG : IsSimpleGroup G)
    (h : IsUnitaryA3Neighborhood (p ^ f) K F z u Y) (hK : Nat.card K = (p ^ f) ^ 2)
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hCN : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G))
    (h6A : MaxOverCentralizerPSp4 z p f) : LieModel G StatedLieTag.PSU 4 p f := by
  obtain ⟨ψ, hψr, hψk, hqs, hmodel⟩ := h.exists_surjection hK hF hp2 hq
  obtain ⟨hcomm, hpair⟩ := h.comm_pairs hK hF hp2 hq
  have hnc : ∃ x ∈ (⨆ i, Y i : Subgroup G), x * z ≠ z * x := by
    obtain ⟨x, hx, hxz⟩ := h.exists_noncommuting hK hF hp2 hq
    exact ⟨x, (le_iSup Y 1) hx, hxz⟩
  have hord : ordBC 2 (p ^ f) < Nat.card ↥(⨆ i, Y i : Subgroup G) :=
    lt_of_lt_of_le (ordBC_two_lt_ordTwistedA_three hq)
      (ordTwistedA_three_le_natCard_of_lieModel_psu hp2 hmodel)
  have htop : (⨆ i, Y i : Subgroup G) = ⊤ :=
    eq_top_of_normalizer_ge_centralizer hG hqs hCN hnc hp2 h6A hord
  exact CFSG.GH74.L5U5.lieModel_unitary_of_iSup_eq_top K p f hK hq (n := 3) (by norm_num) Y hcomm
    hpair htop hG

end Unitary

end CFSG.GH74.GLS.LU
