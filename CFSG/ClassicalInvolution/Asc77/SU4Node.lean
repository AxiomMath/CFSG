module

public import CFSG.ClassicalInvolution.Asc77.SU4Model
public import CFSG.ClassicalInvolution.Asc77.SU4Chain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel)
open CFSG.ClassicalInvolution.RouteD.SU4Pattern
open CFSG.ClassicalInvolution.ModelFacts.OddCover (NoCover)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair diagConj2)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

theorem Gaps.locAut_locAut_eq (hΩ : ConjInvariant Ω) {ρ t : G} (hρx : ρ * x * ρ⁻¹ = x)
    (htx : t * x * t⁻¹ = x) (hρρ : ρ * ρ = t) (a : locQuot Ω x) :
    Gaps.locAut hΩ hρx (Gaps.locAut hΩ hρx a) = Gaps.locAut hΩ htx a := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  show Gaps.locMk Ω x (Gaps.layerAut hΩ hρx (Gaps.layerAut hΩ hρx y)) =
    Gaps.locMk Ω x (Gaps.layerAut hΩ htx y)
  congr 1
  apply Subtype.ext
  show ρ * (ρ * (y : G) * ρ⁻¹) * ρ⁻¹ = t * y * t⁻¹
  rw [← hρρ]
  group

namespace SuLayer

variable {a : ℕ} (Λ : SuLayer p f a Ω x)

theorem range_normal : ((Λ.D.hom Λ.i₁).range).Normal := by
  refine ⟨fun c hc g => ?_⟩
  have hg : g ∈ ⨆ i, (Λ.D.hom i).range := by rw [Λ.D.generate]; trivial
  refine Subgroup.iSup_induction (fun i => (Λ.D.hom i).range)
    (C := fun g => ∀ c ∈ (Λ.D.hom Λ.i₁).range, g * c * g⁻¹ ∈ (Λ.D.hom Λ.i₁).range) hg ?_ ?_ ?_ c hc
  · intro i y hy c hc
    by_cases hi : i = Λ.i₁
    · subst hi
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hc) (Subgroup.inv_mem _ hy)
    · obtain ⟨u, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := hc
      rw [Λ.D.commute i Λ.i₁ hi u v, mul_inv_cancel_right]
      exact ⟨v, rfl⟩
  · intro c hc
    simpa using hc
  · intro y z hy hz c hc
    have := hy _ (hz c hc)
    simpa [mul_assoc] using this

theorem exists_shortNode_of_pair [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {b c : GaloisField p f}
    {hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0} (hg6 : SpinMinus6Generated hirr)
    (hcov : NoCover.{0} Odd (spinGroup (Spin.quadMinus 3 (GaloisField p f) b c)))
    {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {x})
    (hMi : locImg Ω x M ≤ (Λ.D.hom Λ.i₁).range)
    {R S : Subgroup (Su (GaloisField p (2 * f)) p f 4)} {W : Subgroup (locQuot Ω x)}
    (hMR : locImg Ω x M = R.map (Λ.ψ hp2))
    (hpair : TwistedB2BlockPair hirr W (R.map (Λ.ψ hp2)) (S.map (Λ.ψ hp2)))
    (hRS : R ⊔ S = ⊤) :
    ∃ Us : Subgroup G, Λ.IsShortNode hirr M Us ∧ locImg Ω x Us = S.map (Λ.ψ hp2) := by
  have := fact_shortField hirr
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hcard]; omega
  have hSperf : S.map (Λ.ψ hp2) ≤ ⁅S.map (Λ.ψ hp2), S.map (Λ.ψ hp2)⁆ :=
    (twistedB2BlockPair_perfect h4 hpair).2
  obtain ⟨A, hAperf, hAmap⟩ := exists_perfect_lift hP1 hSperf
  set Yl : Subgroup G := locLayer Ω x with hYl
  let Us : Subgroup G := A.map Yl.subtype
  have hUsimg : locImg Ω x Us = S.map (Λ.ψ hp2) := by
    show locImg Ω x (A.map Yl.subtype) = _
    rw [locImg_map_subtype, hAmap]
  have hUsY : Us ≤ Yl := Subgroup.map_subtype_le _
  have hUsperf : Us ≤ ⁅Us, Us⁆ := by
    show A.map Yl.subtype ≤ ⁅A.map Yl.subtype, A.map Yl.subtype⁆
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hAperf
  have hMY : M ≤ Yl := le_centralizingLayer hM
  have hMperf : M ≤ ⁅M, M⁆ := by
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    exact (commutator_eq_of_isClassicalMember hz).ge
  have hUsrange : locImg Ω x Us ≤ (Λ.D.hom Λ.i₁).range := by
    rw [hUsimg, ← (Λ.ψ_spec hp2).2.1]
    exact Subgroup.map_le_range _ _
  have hW : TwistedB2BlockPair hirr W (locImg Ω x M) (locImg Ω x Us) := by
    rw [hMR, hUsimg]
    exact hpair
  refine ⟨Us, ⟨hUsY, le_antisymm (commutator_self_le _) hUsperf, hUsrange,
    twistedB2BlockPair_of_locImg_perfect hirr hg6 hcov h4 hP1 hMY hUsY hMperf hUsperf hW, ?_, ?_⟩,
    hUsimg⟩
  · intro N hN j hj hNj
    have hNY : N ≤ Yl := le_centralizingLayer hN
    have hNperf : N ≤ ⁅N, N⁆ := by
      obtain ⟨z, hz⟩ := hΩ.classical N hN.1
      exact (commutator_eq_of_isClassicalMember hz).ge
    refine commutes_of_commutes_locImg_perfect hP1 hNY hUsY hNperf ?_
    intro u hu w hw
    exact range_commute_of_ne Λ.D hj u (hNj hu) w (hUsrange hw)
  · rw [hMR, hUsimg, ← Subgroup.map_sup, hRS, Subgroup.map_top, (Λ.ψ_spec hp2).2.1]

end SuLayer

theorem SuLayer.exists_shortNode_centralizer_of_one_mod_four [Finite G] (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hq4 : p ^ f % 4 = 1) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) (Λ : SuLayer p f 2 Ω x) {K K₁ K₂ : Subgroup G} {z₁ : G}
    (hK : IsClassicalMember p f K x) (hz₁ : IsClassicalMember p f K₁ z₁)
    (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hK₂ : K₂ ∈ centralizingMembers Ω {x}) (hK₂i : locImg Ω x K₂ ≤ (Λ.D.hom Λ.i₁).range) :
    ∃ Us : Subgroup G, Λ.IsShortNode (minusCoeffs_irr p f) K₂ Us ∧
      Us ≤ Subgroup.centralizer ({z₁} : Set G) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hz₁x : z₁ * x * z₁⁻¹ = x := partner_involution_commutes hp2 hK hz₁ p01
  have hz₁2 : z₁ * z₁ = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one z₁
    rwa [hz₁.orderOf_eq_two] at this
  have hcard : Nat.card (GaloisField p f) % 4 = 1 := by
    rw [GaloisField.card p f hf]
    exact hq4
  obtain ⟨u, hu⟩ := exists_unit_sq_eq_neg_one hcard
  obtain ⟨ρ, hρx, θ, hρρ, hθrange, hθρ⟩ := exists_square_root_chart hp2 hΩ.conjInvariant hK hz₁
    (le_centralizingLayer hK₂) hK₂.2 p01 p12 u hu
  obtain ⟨R, hR, hMR⟩ := Λ.exists_longRoot_of_mem hp2 hΩ hP1 hK₂ hK₂i
  have hnorm : (Λ.ψ hp2).range.Normal := by
    rw [(Λ.ψ_spec hp2).2.1]
    exact Λ.range_normal
  have hτ : ∀ a, Gaps.locAut hΩ.conjInvariant hρx (Gaps.locAut hΩ.conjInvariant hρx a) =
      Gaps.locAut hΩ.conjInvariant hz₁x a :=
    Gaps.locAut_locAut_eq hΩ.conjInvariant hρx hz₁x hρρ
  have hρ4 : ∀ a, Gaps.locAut hΩ.conjInvariant hρx (Gaps.locAut hΩ.conjInvariant hρx
      (Gaps.locAut hΩ.conjInvariant hρx (Gaps.locAut hΩ.conjInvariant hρx a))) = a := fun a => by
    rw [hτ, hτ, Gaps.locAut_locAut hΩ.conjInvariant hz₁x hz₁2]
  have := fact_shortField (minusCoeffs_irr p f)
  obtain ⟨S, W, hpair, hRS, hfix⟩ := exists_fixed_shortPair hp2 hq hq4
    (spinMinus6Generated_galois hp2) (Λ.ψ hp2) (Λ.ψ_spec hp2).1 hnorm
    (Gaps.locAut hΩ.conjInvariant hρx) hρ4 hR θ (hθrange.trans hMR) u hu hθρ
  obtain ⟨Us, hsn, hUsimg⟩ := Λ.exists_shortNode_of_pair hp2 hq hΩ hP1
    (spinMinus6Generated_galois hp2) (spinMinus6_noCover_galois hp2 hq) hK₂ hK₂i hMR hpair hRS
  refine ⟨Us, hsn, ?_⟩
  obtain ⟨hUsY, hUsperf, -⟩ := hsn
  refine (locAut_fixed_iff_of_perfect hΩ hP1 hz₁x hUsY hUsperf.ge).2 ?_
  intro a ha
  rw [hUsimg] at ha
  obtain ⟨y, hy, rfl⟩ := ha
  exact (hτ _).symm.trans (hfix y hy)

end CFSG.ClassicalInvolution.RouteD
