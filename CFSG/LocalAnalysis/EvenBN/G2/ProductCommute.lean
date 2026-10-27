module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductWeyl
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCommute

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (diagonalHom)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

namespace DiagonalPair

variable {d : G2Data L K} (X : DiagonalPair d t)

@[expose] def Δ₁ : X.A₁ →* G :=
  diagonalHom X.A₁ t X.comm₁

@[expose] def Δ₂ : X.A₂ →* G :=
  diagonalHom X.A₂ t X.comm₂

@[expose] def diag₁ (T : Subgroup G) : Subgroup G :=
  (T.subgroupOf X.A₁).map X.Δ₁

@[expose] def diag₂ (T : Subgroup G) : Subgroup G :=
  (T.subgroupOf X.A₂).map X.Δ₂

@[expose] def hat (T : Subgroup G) : Subgroup G :=
  ((T.comap X.Δ₁) ⊓ X.P₀.subgroupOf X.A₁).map X.A₁.subtype

end DiagonalPair

namespace ProductCommuteAux

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductCommuteAux
  (dg mem_dg_iff dg_eq_of_le transport_all)

theorem roots_le_S (d : G2Data L K) :
    d.rootGroup g2r ≤ d.S ∧ d.rootGroup g2a ≤ d.S ∧ d.rootGroup g2u ≤ d.S ∧
      d.rootGroup g2v ≤ d.S ∧ d.rootGroup g2b ≤ d.S ∧ d.rootGroup g2c ≤ d.S := by
  obtain ⟨hUY, hYX, -, hXF, hWF, hFD, -, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨hY, hX, hW, -, hD, hM, -⟩ := d.yamada_defs
  have hFS : d.F ≤ d.S := hFD.trans hDS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (le_sup_left.trans hM.le).trans hMS
  · exact (le_sup_left.trans hD.le).trans hDS
  · exact (le_sup_left.trans hX.le).trans (hXF.trans hFS)
  · exact (le_sup_left.trans hW.le).trans (hWF.trans hFS)
  · exact (le_sup_left.trans hY.le).trans (hYX.trans (hXF.trans hFS))
  · exact (show d.rootGroup g2c = d.U from rfl) ▸ hUY.trans (hYX.trans (hXF.trans hFS))

theorem wa_mem_leviA (d : G2Data L K) : d.wa ∈ d.leviA :=
  d.emb_mem_image (weylElt_mem_g2RankOne g2ir 1)

theorem wa_mem_yamadaK₁ (d : G2Data L K) (hK : 4 ≤ Nat.card K) : d.wa ∈ yamadaK₁ d := by
  rw [yamadaK₁_eq d hK]
  exact mem_sup_right (wa_mem_leviA d)

theorem wb_mem_yamadaK₂ (d : G2Data L K) (hK : 4 ≤ Nat.card K) : d.wb ∈ yamadaK₂ d := by
  rw [yamadaK₂_eq d hK]
  exact mem_sup_right d.wb_mem_leviB

variable {d : G2Data L K} (X : DiagonalPair d t)

theorem mem_hat_iff {T : Subgroup G} {y : G} :
    y ∈ X.hat T ↔ y ∈ X.P₀ ∧ y * (t⁻¹ * y * t) ∈ T := by
  constructor
  · rintro ⟨x, ⟨hxT, hxP⟩, rfl⟩
    exact ⟨hxP, hxT⟩
  · rintro ⟨hy, hyT⟩
    exact ⟨⟨y, X.le₁ hy⟩, ⟨hyT, hy⟩, rfl⟩

theorem hat_le (T : Subgroup G) : X.hat T ≤ X.P₀ := fun _ hy => ((mem_hat_iff X).1 hy).1

theorem dg₁_P₀ : dg X.A₁ X.comm₁ X.P₀ = d.S := X.rangeP

theorem dg₂_P₀ : dg X.A₂ X.comm₂ X.P₀ = d.S := by
  rw [← dg₁_P₀ X]
  exact dg_eq_of_le X.le₂ X.le₁

theorem diag₁_hat {T : Subgroup G} (hT : T ≤ d.S) : X.diag₁ (X.hat T) = T := by
  ext y
  change y ∈ dg X.A₁ X.comm₁ (X.hat T) ↔ y ∈ T
  rw [mem_dg_iff]
  constructor
  · rintro ⟨x, -, hxT, rfl⟩
    exact ((mem_hat_iff X).1 hxT).2
  · intro hy
    have hy' : y ∈ dg X.A₁ X.comm₁ X.P₀ := by rw [dg₁_P₀ X]; exact hT hy
    obtain ⟨x, hxA, hxP, rfl⟩ := mem_dg_iff.1 hy'
    exact ⟨x, hxA, (mem_hat_iff X).2 ⟨hxP, hy⟩, rfl⟩

theorem diag₂_hat {T : Subgroup G} (hT : T ≤ d.S) : X.diag₂ (X.hat T) = T := by
  ext y
  change y ∈ dg X.A₂ X.comm₂ (X.hat T) ↔ y ∈ T
  rw [mem_dg_iff]
  constructor
  · rintro ⟨x, -, hxT, rfl⟩
    exact ((mem_hat_iff X).1 hxT).2
  · intro hy
    have hy' : y ∈ dg X.A₂ X.comm₂ X.P₀ := by rw [dg₂_P₀ X]; exact hT hy
    obtain ⟨x, hxA, hxP, rfl⟩ := mem_dg_iff.1 hy'
    exact ⟨x, hxA, (mem_hat_iff X).2 ⟨hxP, hy⟩, rfl⟩

theorem exists_a₁ (hK : 4 ≤ Nat.card K) : ∃ a : X.A₁, X.Δ₁ a = d.wa := by
  have hu : d.wa ∈ (diagonalHom X.A₁ t X.comm₁).range := X.range₁ ▸ wa_mem_yamadaK₁ d hK
  obtain ⟨a, ha⟩ := hu
  exact ⟨a, ha⟩

theorem exists_a₂ (hK : 4 ≤ Nat.card K) : ∃ a : X.A₂, X.Δ₂ a = d.wb := by
  have hv : d.wb ∈ (diagonalHom X.A₂ t X.comm₂).range := X.range₂ ▸ wb_mem_yamadaK₂ d hK
  obtain ⟨a, ha⟩ := hv
  exact ⟨a, ha⟩

theorem hat_conj_wa_eq (hK : 4 ≤ Nat.card K) {T T' : Subgroup G} (hT : T ≤ d.S)
    (hT' : T' ≤ d.S) (h : Tᵍ[d.wa] = T') : (X.hat T)ᵍ[d.wa] = X.hat T' := by
  subst h
  obtain ⟨a, ha⟩ := exists_a₁ X hK
  have h2 := (transport_all X.comm₁ X.injective₁ X.le₁ (dg₁_P₀ X) a ha (hat_le X T)).2
  rw [show dg X.A₁ X.comm₁ (X.hat T) = T from diag₁_hat X hT] at h2
  obtain ⟨-, hiff⟩ := h2 hT'
  ext y
  rw [hiff y, mem_hat_iff]

theorem hat_conj_wb_eq (hK : 4 ≤ Nat.card K) {T T' : Subgroup G} (hT : T ≤ d.S)
    (hT' : T' ≤ d.S) (h : Tᵍ[d.wb] = T') : (X.hat T)ᵍ[d.wb] = X.hat T' := by
  subst h
  obtain ⟨a, ha⟩ := exists_a₂ X hK
  have h2 := (transport_all X.comm₂ X.injective₂ X.le₂ (dg₂_P₀ X) a ha (hat_le X T)).2
  rw [show dg X.A₂ X.comm₂ (X.hat T) = T from diag₂_hat X hT] at h2
  obtain ⟨-, hiff⟩ := h2 hT'
  ext y
  rw [hiff y, mem_hat_iff]

end ProductCommuteAux

namespace DiagonalPair

variable {d : G2Data L K} (X : DiagonalPair d t)

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductCommuteAux
  (dg dg_sup eq_of_dg_eq transport_all conjSub_conjSub conjSub_mono conjSub_sup
    commutator_conjSub conjSub_bot comm_eq_bot_of_le comm_sup_sup_eq_bot)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (map_conj_inv_map_conj_inv)
open ProductCommuteAux

theorem eq_sup_conj (hK : 4 ≤ Nat.card K) (htt : t * t = 1)
    (htL : t ∈ centralizer (L : Set G)) :
    X.A₁ = X.P₀ ⊔ X.P₀ᵍ[d.wa] ∧ X.A₂ = X.P₀ ⊔ X.P₀ᵍ[d.wb] := by
  obtain ⟨-, -, -, ⟨hK₁, hK₂⟩, -⟩ := d.weyl_facts hK
  obtain ⟨a₁, ha₁⟩ := exists_a₁ X hK
  obtain ⟨a₂, ha₂⟩ := exists_a₂ X hK
  have T₁ := transport_all X.comm₁ X.injective₁ X.le₁ (dg₁_P₀ X) a₁ ha₁ (T := X.P₀) le_rfl
  have T₂ := transport_all X.comm₂ X.injective₂ X.le₂ (dg₂_P₀ X) a₂ ha₂ (T := X.P₀) le_rfl
  have hPu : X.P₀ᵍ[d.wa] ≤ X.A₁ := T₁.1.2.1
  have hPv : X.P₀ᵍ[d.wb] ≤ X.A₂ := T₂.1.2.1
  refine ⟨?_, ?_⟩
  · have e1 : dg X.A₁ X.comm₁ X.A₁ = yamadaK₁ d := by
      unfold dg
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
      exact X.range₁
    have e2 : dg X.A₁ X.comm₁ (X.P₀ ⊔ X.P₀ᵍ[d.wa]) = yamadaK₁ d := by
      rw [dg_sup X.le₁ hPu, T₁.1.2.2, dg₁_P₀ X, hK₁]
    exact eq_of_dg_eq X.injective₁ le_rfl (sup_le X.le₁ hPu) (e1.trans e2.symm)
  · have e1 : dg X.A₂ X.comm₂ X.A₂ = yamadaK₂ d := by
      unfold dg
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
      exact X.range₂
    have e2 : dg X.A₂ X.comm₂ (X.P₀ ⊔ X.P₀ᵍ[d.wb]) = yamadaK₂ d := by
      rw [dg_sup X.le₂ hPv, T₂.1.2.2, dg₂_P₀ X, hK₂]
    exact eq_of_dg_eq X.injective₂ le_rfl (sup_le X.le₂ hPv) (e1.trans e2.symm)

theorem paths (hK : 4 ≤ Nat.card K) (htt : t * t = 1) (htL : t ∈ centralizer (L : Set G)) :
    ((X.hat (d.rootGroup g2r))ᵍ[d.wb] = X.hat (d.rootGroup g2u) ∧
      ((X.hat (d.rootGroup g2r))ᵍ[d.wb])ᵍ[d.wa] = X.hat (d.rootGroup g2v) ∧
      (((X.hat (d.rootGroup g2r))ᵍ[d.wb])ᵍ[d.wa])ᵍ[d.wb] = X.hat (d.rootGroup g2v) ∧
      ((((X.hat (d.rootGroup g2r))ᵍ[d.wb])ᵍ[d.wa])ᵍ[d.wb])ᵍ[d.wa] = X.hat (d.rootGroup g2u) ∧
      (((((X.hat (d.rootGroup g2r))ᵍ[d.wb])ᵍ[d.wa])ᵍ[d.wb])ᵍ[d.wa])ᵍ[d.wb] =
        X.hat (d.rootGroup g2r) ∧
      (X.hat (d.rootGroup g2r))ᵍ[d.wa] ≤ X.P₀ᵍ[(d.wa * d.wb) ^ 3]) ∧
    ((X.hat (d.rootGroup g2a))ᵍ[d.wa] = X.hat (d.rootGroup g2b) ∧
      ((X.hat (d.rootGroup g2a))ᵍ[d.wa])ᵍ[d.wb] = X.hat (d.rootGroup g2c) ∧
      (((X.hat (d.rootGroup g2a))ᵍ[d.wa])ᵍ[d.wb])ᵍ[d.wa] = X.hat (d.rootGroup g2c) ∧
      ((((X.hat (d.rootGroup g2a))ᵍ[d.wa])ᵍ[d.wb])ᵍ[d.wa])ᵍ[d.wb] = X.hat (d.rootGroup g2b) ∧
      (((((X.hat (d.rootGroup g2a))ᵍ[d.wa])ᵍ[d.wb])ᵍ[d.wa])ᵍ[d.wb])ᵍ[d.wa] =
        X.hat (d.rootGroup g2a) ∧
      (X.hat (d.rootGroup g2a))ᵍ[d.wb] ≤ X.P₀ᵍ[(d.wa * d.wb) ^ 3]) := by
  obtain ⟨⟨-, -, hw⟩, ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩, -⟩ := d.weyl_facts hK
  obtain ⟨hSr, hSa, hSu, hSv, hSb, hSc⟩ := roots_le_S d
  have p1 := hat_conj_wb_eq X hK hSr hSu c1
  have p2 := hat_conj_wa_eq X hK hSu hSv c8
  have p3 := hat_conj_wb_eq X hK hSv hSv c3
  have p4 := hat_conj_wa_eq X hK hSv hSu c9
  have p5 := hat_conj_wb_eq X hK hSu hSr c2
  have q1 := hat_conj_wa_eq X hK hSa hSb c6
  have q2 := hat_conj_wb_eq X hK hSb hSc c4
  have q3 := hat_conj_wa_eq X hK hSc hSc c10
  have q4 := hat_conj_wb_eq X hK hSc hSb c5
  have q5 := hat_conj_wa_eq X hK hSb hSa c7
  refine ⟨⟨p1, by rw [p1, p2], by rw [p1, p2, p3], by rw [p1, p2, p3, p4],
    by rw [p1, p2, p3, p4, p5], ?_⟩, ⟨q1, by rw [q1, q2], by rw [q1, q2, q3],
    by rw [q1, q2, q3, q4], by rw [q1, q2, q3, q4, q5], ?_⟩⟩
  · have h5 : (X.hat (d.rootGroup g2r))ᵍ[d.wb * d.wa * d.wb * d.wa * d.wb] =
        X.hat (d.rootGroup g2r) := by
      have h : (((((X.hat (d.rootGroup g2r))ᵍ[d.wb])ᵍ[d.wa])ᵍ[d.wb])ᵍ[d.wa])ᵍ[d.wb] =
          X.hat (d.rootGroup g2r) := by rw [p1, p2, p3, p4, p5]
      simpa only [conjSub_conjSub] using h
    have h6 := conjSub_mono (A := X.hat (d.rootGroup g2r)) (hat_le X _)
      (d.wb * d.wa * d.wb * d.wa * d.wb)
    rw [h5] at h6
    have h7 := conjSub_mono h6 d.wa
    rw [conjSub_conjSub] at h7
    have e : d.wb * d.wa * d.wb * d.wa * d.wb * d.wa = (d.wa * d.wb) ^ 3 := by
      rw [hw]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e] at h7
    exact h7
  · have h5 : (X.hat (d.rootGroup g2a))ᵍ[d.wa * d.wb * d.wa * d.wb * d.wa] =
        X.hat (d.rootGroup g2a) := by
      have h : (((((X.hat (d.rootGroup g2a))ᵍ[d.wa])ᵍ[d.wb])ᵍ[d.wa])ᵍ[d.wb])ᵍ[d.wa] =
          X.hat (d.rootGroup g2a) := by rw [q1, q2, q3, q4, q5]
      simpa only [conjSub_conjSub] using h
    have h6 := conjSub_mono (A := X.hat (d.rootGroup g2a)) (hat_le X _)
      (d.wa * d.wb * d.wa * d.wb * d.wa)
    rw [h5] at h6
    have h7 := conjSub_mono h6 d.wb
    rw [conjSub_conjSub] at h7
    have e : d.wa * d.wb * d.wa * d.wb * d.wa * d.wb = (d.wa * d.wb) ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e] at h7
    exact h7

theorem factorizations (hK : 4 ≤ Nat.card K) (htt : t * t = 1)
    (htL : t ∈ centralizer (L : Set G)) :
    (X.P₀ᵍ[d.wa] = (X.hat (d.rootGroup g2r))ᵍ[d.wa] ⊔ X.hat d.D ∧
      (X.hat (d.rootGroup g2r))ᵍ[d.wa] ≤ X.A₁) ∧
    (X.P₀ᵍ[d.wb] = X.hat d.M ⊔ (X.hat (d.rootGroup g2a))ᵍ[d.wb] ∧
      (X.hat (d.rootGroup g2a))ᵍ[d.wb] ≤ X.A₂) := by
  obtain ⟨-, -, ⟨hS₁, hS₂, -, -, hDa, hMb⟩, -⟩ := d.weyl_facts hK
  obtain ⟨a₁, ha₁⟩ := exists_a₁ X hK
  obtain ⟨a₂, ha₂⟩ := exists_a₂ X hK
  obtain ⟨hSr, hSa, -, -, -, -⟩ := roots_le_S d
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  refine ⟨?_, ?_⟩
  · have T1 := transport_all X.comm₁ X.injective₁ X.le₁ (dg₁_P₀ X) a₁ ha₁ (T := X.P₀) le_rfl
    have T2 := transport_all X.comm₁ X.injective₁ X.le₁ (dg₁_P₀ X) a₁ ha₁
      (T := X.hat (d.rootGroup g2r)) (hat_le X _)
    have hA : (X.hat (d.rootGroup g2r))ᵍ[d.wa] ≤ X.A₁ := T2.1.2.1
    have hD' : X.hat d.D ≤ X.A₁ := (hat_le X _).trans X.le₁
    refine ⟨eq_of_dg_eq X.injective₁ T1.1.2.1 (sup_le hA hD') ?_, hA⟩
    rw [T1.1.2.2, dg_sup hA hD', T2.1.2.2, dg₁_P₀ X,
      show dg X.A₁ X.comm₁ (X.hat (d.rootGroup g2r)) = d.rootGroup g2r from diag₁_hat X hSr,
      show dg X.A₁ X.comm₁ (X.hat d.D) = d.D from diag₁_hat X hDS, hS₁, conjSub_sup, hDa]
  · have T1 := transport_all X.comm₂ X.injective₂ X.le₂ (dg₂_P₀ X) a₂ ha₂ (T := X.P₀) le_rfl
    have T2 := transport_all X.comm₂ X.injective₂ X.le₂ (dg₂_P₀ X) a₂ ha₂
      (T := X.hat (d.rootGroup g2a)) (hat_le X _)
    have hA : (X.hat (d.rootGroup g2a))ᵍ[d.wb] ≤ X.A₂ := T2.1.2.1
    have hM' : X.hat d.M ≤ X.A₂ := (hat_le X _).trans X.le₂
    refine ⟨eq_of_dg_eq X.injective₂ T1.1.2.1 (sup_le hM' hA) ?_, hA⟩
    rw [T1.1.2.2, dg_sup hM' hA, T2.1.2.2, dg₂_P₀ X,
      show dg X.A₂ X.comm₂ (X.hat (d.rootGroup g2a)) = d.rootGroup g2a from diag₂_hat X hSa,
      show dg X.A₂ X.comm₂ (X.hat d.M) = d.M from diag₂_hat X hMS, hS₂, conjSub_sup, hMb,
      sup_comm]

theorem commutator_cross_eq_bot (hK : 4 ≤ Nat.card K) (htt : t * t = 1)
    (htL : t ∈ centralizer (L : Set G)) :
    ⁅X.A₁, X.A₂ᵍ[t]⁆ = ⊥ ∧ ⁅X.A₁ᵍ[t], X.A₂⁆ = ⊥ := by
  obtain ⟨a₁, ha₁⟩ := exists_a₁ X hK
  obtain ⟨a₂, ha₂⟩ := exists_a₂ X hK
  obtain ⟨⟨-, -, -, -, -, hŜ₁⟩, ⟨-, -, -, -, -, hŜ₂⟩⟩ := X.paths hK htt htL
  obtain ⟨⟨hI4a, hŜA⟩, ⟨hI4b, hŜ'A⟩⟩ := X.factorizations hK htt htL
  obtain ⟨hA₁, hA₂⟩ := X.eq_sup_conj hK htt htL
  have T₁ := transport_all X.comm₁ X.injective₁ X.le₁ (dg₁_P₀ X) a₁ ha₁ (T := X.P₀) le_rfl
  have T₂ := transport_all X.comm₂ X.injective₂ X.le₂ (dg₂_P₀ X) a₂ ha₂ (T := X.P₀) le_rfl
  have hPu : X.P₀ᵍ[d.wa] ≤ X.A₁ := T₁.1.2.1
  have hPv : X.P₀ᵍ[d.wb] ≤ X.A₂ := T₂.1.2.1
  have hP₁ : ⁅X.P₀, X.P₀ᵍ[t]⁆ = ⊥ := comm_eq_bot_of_le X.le₁ (conjSub_mono X.le₁ t) X.comm₁
  have hP₂ : ⁅X.P₀, (X.P₀ᵍ[d.wb])ᵍ[t]⁆ = ⊥ :=
    comm_eq_bot_of_le X.le₂ (conjSub_mono hPv t) X.comm₂
  have hP₃ : ⁅X.P₀ᵍ[d.wa], X.P₀ᵍ[t]⁆ = ⊥ :=
    comm_eq_bot_of_le hPu (conjSub_mono X.le₁ t) X.comm₁
  have hwL : (d.wa * d.wb) ^ 3 ∈ L :=
    Subgroup.pow_mem L (mul_mem (d.emb_mem _) (d.emb_mem _)) 3
  have hwt : (d.wa * d.wb) ^ 3 * t = t * (d.wa * d.wb) ^ 3 := mem_centralizer_iff.1 htL _ hwL
  have hP₄ : ⁅X.P₀ᵍ[d.wa], (X.P₀ᵍ[d.wb])ᵍ[t]⁆ = ⊥ := by
    rw [hI4a, hI4b, conjSub_sup]
    have hM₀ : X.hat d.M ≤ X.A₁ := (hat_le X _).trans X.le₁
    have hD₀ : X.hat d.D ≤ X.A₁ := (hat_le X _).trans X.le₁
    refine comm_sup_sup_eq_bot ?_ ?_ ?_ ?_
    · exact comm_eq_bot_of_le hŜA (conjSub_mono hM₀ t) X.comm₁
    · have h1 : ((X.hat (d.rootGroup g2a))ᵍ[d.wb])ᵍ[t] ≤ (X.P₀ᵍ[t])ᵍ[(d.wa * d.wb) ^ 3] := by
        have h2 : (X.P₀ᵍ[(d.wa * d.wb) ^ 3])ᵍ[t] = (X.P₀ᵍ[t])ᵍ[(d.wa * d.wb) ^ 3] := by
          rw [conjSub_conjSub, conjSub_conjSub, hwt]
        exact (conjSub_mono hŜ₂ t).trans h2.le
      have h4 : ⁅X.P₀ᵍ[(d.wa * d.wb) ^ 3], (X.P₀ᵍ[t])ᵍ[(d.wa * d.wb) ^ 3]⁆ = ⊥ := by
        rw [commutator_conjSub, hP₁, conjSub_bot]
      exact comm_eq_bot_of_le hŜ₁ h1 h4
    · exact comm_eq_bot_of_le hD₀ (conjSub_mono hM₀ t) X.comm₁
    · exact comm_eq_bot_of_le ((hat_le X _).trans X.le₂) (conjSub_mono hŜ'A t) X.comm₂
  have h2 : ⁅X.A₁, X.A₂ᵍ[t]⁆ = ⊥ := by
    rw [hA₁, hA₂, conjSub_sup]
    exact comm_sup_sup_eq_bot hP₁ hP₂ hP₃ hP₄
  refine ⟨h2, ?_⟩
  have h3 : ⁅X.A₁, X.A₂ᵍ[t]⁆ᵍ[t] = (⊥ : Subgroup G)ᵍ[t] := by rw [h2]
  rw [← commutator_conjSub, conjSub_bot, map_conj_inv_map_conj_inv htt] at h3
  exact h3

end DiagonalPair

end Local

end CFSG.LocalAnalysis.EvenBN.G2
