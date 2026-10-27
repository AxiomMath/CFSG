module

public import CFSG.ClassicalInvolution.RouteD.TypeCLayers
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplit
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSimple
public import CFSG.ClassicalInvolution.RouteD.GapsR2
public import CFSG.ClassicalInvolution.RouteD.LocalTwinDict
public import CFSG.ClassicalInvolution.RouteD.TwinTenModel
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD

open scoped MatrixGroups
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem eq_top_of_index_le_four {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    {H : Subgroup L} (hH : H.index ≤ 4) : H = ⊤ := by
  classical
  have hcard : Nat.card (L ⧸ H) ≤ 4 := hH
  have hsolv : Group.IsSolvable (Equiv.Perm (L ⧸ H)) := Equiv.Perm.isSolvable hcard
  let φ : L →* Equiv.Perm (L ⧸ H) := MulAction.toPermHom L (L ⧸ H)
  obtain ⟨n, hn⟩ := hsolv.solvable
  have h1 : (derivedSeries L n).map φ ≤ derivedSeries (Equiv.Perm (L ⧸ H)) n :=
    map_derivedSeries_le_derivedSeries φ n
  rw [Group.IsPerfect.derivedSeries_eq_top, hn] at h1
  rw [eq_top_iff]
  intro g _
  have hg : φ g = 1 := by
    have : φ g ∈ (⊤ : Subgroup L).map φ := ⟨g, Subgroup.mem_top g, rfl⟩
    exact Subgroup.mem_bot.mp (h1 this)
  have h2 : g • (((1 : L) : L ⧸ H)) = ((1 : L) : L ⧸ H) := by
    have := congrArg (fun π : Equiv.Perm (L ⧸ H) => π (((1 : L) : L ⧸ H))) hg
    simpa [φ] using this
  have h3 : ((g : L) : L ⧸ H) = ((1 : L) : L ⧸ H) := by
    simpa [MulAction.Quotient.smul_mk] using h2
  have h4 := QuotientGroup.eq.mp h3
  simpa using H.inv_mem h4

theorem range_eq_of_central_ker {S L : Type*} [Group S] [Finite S] [Group L]
    [Group.IsPerfect S] (hZ : Nat.card (Subgroup.center S) ≤ 4) (ψ Ψ : S →* L)
    (hΨ : Ψ.ker ≤ Subgroup.center S)
    (hle : Ψ.range ≤ ψ.range) : Ψ.range = ψ.range := by
  classical
  have hB : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hfψ : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hfΨ : Finite Ψ.range := Finite.of_surjective Ψ.rangeRestrict Ψ.rangeRestrict_surjective
  have e1 := Subgroup.card_ker_mul_card_range ψ
  have e2 := Subgroup.card_ker_mul_card_range Ψ
  set A' : Subgroup ψ.range := Ψ.range.subgroupOf ψ.range with hA'
  have e3 : Nat.card A' * A'.index = Nat.card ψ.range := Subgroup.card_mul_index A'
  have e4 : Nat.card A' = Nat.card Ψ.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hpos : 0 < Nat.card Ψ.range := Nat.card_pos
  have e5 : Nat.card Ψ.ker = Nat.card ψ.ker * A'.index := by
    have : Nat.card Ψ.ker * Nat.card Ψ.range =
        Nat.card ψ.ker * (Nat.card Ψ.range * A'.index) := by
      rw [e2, ← e1, ← e3, e4]
    have h' : Nat.card Ψ.ker * Nat.card Ψ.range =
        (Nat.card ψ.ker * A'.index) * Nat.card Ψ.range := by
      rw [this]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  have e6 : Nat.card Ψ.ker ≤ 4 := (Subgroup.card_le_of_le hΨ).trans hZ
  have hker_pos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hidx : A'.index ≤ 4 := by
    have : A'.index ≤ Nat.card ψ.ker * A'.index := Nat.le_mul_of_pos_left _ hker_pos
    omega
  have : A' = ⊤ := eq_top_of_index_le_four hidx
  rw [hA', Subgroup.subgroupOf_eq_top] at this
  exact le_antisymm hle this

theorem card_center_sl4_le_four (F : Type*) [Field F] :
    Nat.card (Subgroup.center SL(4, F)) ≤ 4 := by
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 4) (R := F)
  rw [Nat.card_congr e.toEquiv]
  have : NeZero (max (Fintype.card (Fin 4)) 1) := ⟨by simp⟩
  have := card_rootsOfUnity F (max (Fintype.card (Fin 4)) 1)
  simpa using this


section Chain

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {x : G}

theorem range_le_locImg_of_chain (hq : 4 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (ψ : SL(4, GaloisField p f) →* locQuot Ω x) {L : Fin 3 → Subgroup G}
    (hL : ∀ k, L k ∈ centralizingMembers Ω {x}) (hψ : ∀ k, locImg Ω x (L k) ≤ ψ.range)
    (hcomm : Commutes (L 0) (L 2))
    (hp01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L 0) (L 1))
    (hp12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L 1) (L 2)) :
    ψ.range ≤ locImg Ω x (⨆ k, L k) := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  set H : Subgroup G := ⨆ k, L k with hHdef
  have hLle : ∀ k, L k ≤ H := fun k => le_iSup L k
  have hHlayer : H ≤ locLayer Ω x := iSup_le fun k => le_centralizingLayer (hL k)
  obtain ⟨Ψ₀, hsurj, -, -⟩ := weakCT_recognition_nodes (GaloisField p f) p f hp.out hK hq
    (n := 3) (by omega) (X := ↥H) (U := fun k => (L k).subgroupOf H)
    (fun i j hij u hu v hv => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exact Subtype.ext (hcomm u (Subgroup.mem_subgroupOf.mp hu) v
        (Subgroup.mem_subgroupOf.mp hv)))
    (fun i j hij => by
      have hpair : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L i) (L j) := by
        fin_cases i <;> fin_cases j <;> simp at hij
        · exact hp01
        · exact hp12
      obtain ⟨W, hW⟩ := hpair
      have hWle : W ≤ H := (linearBlockStandardPair_le_sup hW).trans (sup_le (hLle i) (hLle j))
      exact ⟨W.subgroupOf H, linearBlockStandardPair_subgroupOf hWle hW⟩)
    (iSup_subgroupOf_self L)
  let Ψ : SL(4, GaloisField p f) →* locQuot Ω x :=
    (locMk Ω x).comp ((Subgroup.inclusion hHlayer).comp Ψ₀)
  have hrange : Ψ.range = locImg Ω x H := by
    unfold locImg
    rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.map_top, Subgroup.inclusion_range]
  have hrange' : locImg Ω x H = ⨆ k, locImg Ω x (L k) :=
    locImg_iSup L fun k => le_centralizingLayer (hL k)
  have hadm : StatedLieAdmissible .PSL 4 p f :=
    ⟨hp.out, Nat.one_le_iff_ne_zero.mpr hf, by show 2 ≤ 4; omega,
      fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hqs : CFSG.IsQuasisimple SL(4, GaloisField p f) :=
    CFSG.ClassicalInvolution.ModelFacts.native_isQuasisimple
      (CFSG.ClassicalInvolution.ModelFacts.isQuasisimple_modelUniv .PSL 4 p f hp.out trivial hadm)
  have hΨker : Ψ.ker ≤ Subgroup.center SL(4, GaloisField p f) := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqs Ψ.ker with h | h
    · exact h
    · exfalso
      have hbot : Ψ.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨s, rfl⟩
        have : s ∈ Ψ.ker := h ▸ Subgroup.mem_top s
        simp [MonoidHom.mem_ker.mp this]
      have h0 : locImg Ω x (L 0) ≤ ⊥ := by
        rw [← hbot, hrange, hrange']
        exact le_iSup (fun k => locImg Ω x (L k)) 0
      exact locImg_ne_bot hΩ hex (hL 0) (le_bot_iff.mp h0)
  have hle : Ψ.range ≤ ψ.range := by
    rw [hrange, hrange']
    exact iSup_le hψ
  have : Group.IsPerfect SL(4, GaloisField p f) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have heq := range_eq_of_central_ker (card_center_sl4_le_four _) ψ Ψ hΨker hle
  rw [← heq, hrange]

theorem le_iSup_of_chain (hq : 4 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (ψ : SL(4, GaloisField p f) →* locQuot Ω x)
    {L : Fin 3 → Subgroup G} (hL : ∀ k, L k ∈ centralizingMembers Ω {x})
    (hψ : ∀ k, locImg Ω x (L k) ≤ ψ.range) (hcomm : Commutes (L 0) (L 2))
    (hp01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L 0) (L 1))
    (hp12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L 1) (L 2)) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) (hNψ : locImg Ω x N ≤ ψ.range) : N ≤ ⨆ k, L k :=
  le_of_locImg_le hΩ hP1 hN
    (hNψ.trans (range_le_locImg_of_chain hq hΩ hex ψ hL hψ hcomm hp01 hp12))

end Chain

section Dict

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem TCtx.le_iSup_of_chain (c : TCtx p f .PSL 4 Ω K z) {L : Fin 3 → Subgroup G}
    (hL : ∀ k, L k ∈ centralizingMembers Ω {z}) (hLK : ∀ k, L k ≠ K)
    (hLQ : ∀ k, ¬ locImg Ω z (L k) ≤ c.d.Q₁) (hcomm : Commutes (L 0) (L 2))
    (hp01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L 0) (L 1))
    (hp12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L 1) (L 2)) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) (hNQ : ¬ locImg Ω z N ≤ c.d.Q₁) :
    N ≤ ⨆ k, L k := by
  have hψ : ∀ {M : Subgroup G}, M ∈ centralizingMembers Ω {z} → M ≠ K →
      ¬ locImg Ω z M ≤ c.d.Q₁ → locImg Ω z M ≤ c.d.ψ.range := by
    intro M hM hMK hMQ
    obtain ⟨R, -, hR⟩ := c.exists_fund_of_ne hM hMK hMQ
    rw [hR]
    exact Subgroup.map_le_range _ _
  exact CFSG.ClassicalInvolution.RouteD.le_iSup_of_chain (by have := c.hq; omega) c.hΩ c.hex
    c.hP1 c.d.ψ hL (fun k => hψ (hL k) (hLK k) (hLQ k)) hcomm hp01 hp12 hN (hψ hN hNK hNQ)

end Dict

end CFSG.ClassicalInvolution.RouteD
