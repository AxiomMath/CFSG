module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldG2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom
  centerQuotientHom_injective onCenterQuotient_apply_mk)

@[expose] def KFactOuterThreeRankFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex), IsRankTwoPlus d.1 →
    RankThreeList d.1 → LieClAut.FieldExponentThree d.1 →
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) → Subgroup.center X = ⊥ →
    ∀ H : Subgroup (MulAut X),
    (MulAut.conj : X →* MulAut X).range ≤ H →
    (∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range) →
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81

@[expose] def KFactTenElevenOneLieAutFieldTwo : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → Open.IsQuasisimple ↥L →
    CFSG.pCore 2 Y = ⊥ → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
    RankTwoList d.1 → (∀ q : TauCeti.PrimePower, d.1 ≠ .A 2 q) →
    LieClAut.FieldExponentThree d.1 →
    (∀ q : TauCeti.PrimePower, d.1 = .G2 q → 3 ∣ q.exponent) →
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    (∃ u : Y, (∃ k : ℕ, u ^ 3 ^ k = 1) ∧ u ∉ L ⊔ Subgroup.centralizer (L : Set Y)) →
    (∃ T J : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set _) ≤ J ∧ J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤) →
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (L : Set Y)) →
    Open.pRank 3 (⊤ : Subgroup Y) = 3 →
    (∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Open.pRank 3 (Subgroup.centralizer (E : Set Y)) ≤ 2) →
    (∃ N : Subgroup Y, N.Normal ∧ N.index = 3) → False

namespace LieClAut

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]

noncomputable abbrev conjQuot (L : Subgroup Y) [L.Normal] : Y →* MulAut (↥L ⧸ center ↥L) :=
  (centerQuotientHom ↥L).comp (MulAut.conjNormal : Y →* MulAut ↥L)

theorem conjQuot_apply_mem (l : ↥L) :
    conjQuot L (l : Y) = MulAut.conj (l : ↥L ⧸ center ↥L) := by
  ext z
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (center ↥L) z
  change (QuotientGroup.mk' (center ↥L)) (MulAut.conjNormal (l : Y) z) = _
  have hz : MulAut.conjNormal (l : Y) z = l * z * l⁻¹ := Subtype.ext (by simp)
  rw [hz, MulAut.conj_apply]
  simp

theorem mem_centralizer_of_conjQuot_eq_one (hLp : Group.IsPerfect ↥L) {y : Y}
    (hy : conjQuot L y = 1) : y ∈ centralizer (L : Set Y) := by
  have h1 : (MulAut.conjNormal y : MulAut ↥L) = 1 :=
    centerQuotientHom_injective ↥L (by rw [map_one]; exact hy)
  refine mem_centralizer_iff.2 fun l hl => ?_
  have h2 := congrArg (fun τ : MulAut ↥L => ((τ ⟨l, hl⟩ : ↥L) : Y)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc l * y = y * l * y⁻¹ * y := by rw [h2]
    _ = y * l := by group

end LieClAut

theorem kFactTenElevenOneLieAutFieldG2_of_rankFour (hK : KFactOuterThreeRankFour)
    (h2 : KFactTenElevenOneLieAutFieldTwo) : KFactTenElevenOneLieAutFieldG2 := by
  intro Y _ _ L hLn hq hO2 d hd hlist hA2 h3 hG he hu hJ hC3 hrk hE hN
  rcases hlist with hl | hl
  · exact h2 Y L hLn hq hO2 d hd hl hA2 h3 hG he hu hJ hC3 hrk hE hN
  haveI := hLn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  set ρ := LieClAut.conjQuot L with hρ
  have hker : ρ.ker ≤ centralizer (L : Set Y) := fun y hy =>
    LieClAut.mem_centralizer_of_conjQuot_eq_one inferInstance hy
  have hinn : (MulAut.conj : ↥L ⧸ center ↥L →* MulAut (↥L ⧸ center ↥L)).range ≤ ρ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨(l : Y), LieClAut.conjQuot_apply_mem l⟩
  obtain ⟨u, ⟨k, hk⟩, huLC⟩ := hu
  have hout : ρ u ∉ (MulAut.conj : ↥L ⧸ center ↥L →* MulAut (↥L ⧸ center ↥L)).range := by
    rintro ⟨x, hx⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    apply huLC
    have h1 : ρ ((l : Y)⁻¹ * u) = 1 := by
      rw [map_mul, map_inv, ← hx, LieClAut.conjQuot_apply_mem, inv_mul_cancel]
    have h2 := hker h1
    have : u = (l : Y) * ((l : Y)⁻¹ * u) := by group
    rw [this]
    exact Subgroup.mul_mem_sup l.2 h2
  obtain ⟨e⟩ := he
  obtain ⟨F, hFH, hF, hFc⟩ := hK _ d hd hl h3 ⟨e⟩ (LieClAut.center_quotient_eq_bot hq) ρ.range hinn
    ⟨ρ u, ⟨u, rfl⟩, ⟨k, by rw [← map_pow, hk, map_one]⟩, hout⟩
  have h4 : 4 ≤ Open.pRank 3 ρ.range :=
    CFSG.SectionRank.le_pRank (by norm_num) hFH hF (by rw [hFc]; norm_num)
  have hk3 : ¬ 3 ∣ Nat.card ρ.ker := fun h =>
    hC3 (h.trans (Subgroup.card_dvd_of_le hker))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (QuotientGroup.quotientKerEquivRange ρ),
    CFSG.SectionRank.pRank_quotient_eq ρ.ker hk3, hrk] at h4
  omega

theorem kFactTenElevenOneLieAutRes_of_rankFour
    (hK : KFactOuterThreeRankFour) (h2 : KFactTenElevenOneLieAutFieldTwo) :
    KFactTenElevenOneLieAutRes :=
  kFactTenElevenOneLieAutRes_of_fieldG2 (kFactTenElevenOneLieAutFieldG2_of_rankFour hK h2)

end CFSG.LocalAnalysis.RankThreeTheoremC
