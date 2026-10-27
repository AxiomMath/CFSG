module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OutStep
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Rank
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwSetup

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.RankThree.PartOne.OutStructure CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LieType.Ree CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.Timmesfeld.ExceptionalOrders
  CFSG.ClassicalInvolution CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] noncomputable def diagJ
    (K : Type) [Field K] : Subgroup (MulAut (adjointGroup Tag.E6 K)) :=
  inner (adjointGroup Tag.E6 K) ⊔ (rootDiagAutHom Tag.E6 K).range

@[expose] def E6JBoundUntw : Prop :=
  ∀ (K : Type) [Field K] [Finite K],
    3 ∣ Nat.card K - 1 → CFSG.Open.pRank 3 (diagJ K) ≤ 6

@[expose] def E6JBoundTw : Prop :=
  ∀
    (r f : ℕ), r.Prime → 1 ≤ f → 3 ∣ r ^ f + 1 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (r ^ f) ^ 2 → ∀ σ : K ≃+* K,
      (∀ c, σ c = c ^ (r ^ f)) →
        CFSG.Open.pRank 3 (twistedE6Inn K σ ⊔ twistedE6Diag K σ) ≤ 6

theorem untwistedModel_of_lieModel_E6 {X : Type} [Group X] {n r f : ℕ}
    (hm : CFSG.Blueprint.LieModel X .E6 n r f) :
    r.Prime ∧ 1 ≤ f ∧ UntwistedChevalleyModel X .E6 (r ^ f) := by
  rcases hm with ⟨ht, -⟩ | ⟨-, -, ⟨⟨hrp, hf1, -⟩, hc⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact ⟨hrp, hf1, hc⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem twistedModel_of_lieModel_E6 {X : Type} [Group X] {n r f : ℕ}
    (hm : CFSG.Blueprint.LieModel X .twistedE6 n r f) :
    r.Prime ∧ 1 ≤ f ∧ TwistedChevalleyModel X .E6 (r ^ f) :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hm

section Untwisted


theorem pRank_adjointGroup_le_diagJ (K : Type) [Field K] [Finite K] :
    CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ CFSG.Open.pRank 3 (diagJ K) := by
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hZ := center_adjointGroup_eq_bot (τ := Tag.E6) (K := K)
  have hinj : Function.Injective (MulAut.conj : adjointGroup Tag.E6 K →* MulAut _) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : g ∈ Subgroup.center (adjointGroup Tag.E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := congrArg (fun φ : MulAut (adjointGroup Tag.E6 K) => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  refine (pRank_le_map (by norm_num) _ hinj ⊤).trans (pRank_mono (by norm_num) ?_)
  rintro _ ⟨g, -, rfl⟩
  exact Subgroup.mem_sup_left ⟨g, rfl⟩

theorem e6RankUpper_untw_of_J (hJ : E6JBoundUntw) {S : Type} [Group S] [Finite S]
    {n r f : ℕ} (hm : CFSG.Blueprint.LieModel S .E6 n r f) (h3 : 3 ∣ r ^ f - 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 6 ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut S)) ≤ 7 := by
  obtain ⟨hr, hf1, hU⟩ := untwistedModel_of_lieModel_E6 hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.E6 hU
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hJK : CFSG.Open.pRank 3 (diagJ K) ≤ 6 := hJ K hK3
  have hS : CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 6 :=
    (pRank_adjointGroup_le_diagJ K).trans hJK
  refine ⟨(pRank_top_eq_of_mulEquiv (by norm_num) e).trans_le hS, ?_⟩
  rw [pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr e)]
  obtain ⟨Φ, -, hkerΦ, -⟩ := exists_outer_hom_E (K := K) (τ := .E6) (Or.inl rfl)
  have hring := card_ringAut_and_isCyclic hr K hK
  have hfinR : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have hcycR : IsCyclic (RingAut K) := hring.2
  set Θ : MulAut (adjointGroup Tag.E6 K) →* RingAut K × Multiplicative (ZMod (exactE Tag.E6)) :=
    Φ.comp (QuotientGroup.mk' (inner (adjointGroup Tag.E6 K))) with hΘ
  have key : ∀ x : ZMod 2, 2 • x = 0 := by decide
  have hM : ∀ y : Multiplicative (ZMod (exactE Tag.E6)), y ^ 2 = 1 := by
    intro y
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    exact key _
  have hstep := pRank_le_of_hom_ker Θ
    (fun F hF => card_le_three_of_elemAbelian_prod hM F hF)
  have hker : Θ.ker ≤ diagJ K := by
    intro α hα
    have h1 : Φ (QuotientGroup.mk α) = 1 := hα
    have h2 : (QuotientGroup.mk α : Outer (adjointGroup Tag.E6 K)) ∈ Φ.ker := h1
    rw [hkerΦ] at h2
    obtain ⟨a, ha⟩ := h2
    have h3 : (QuotientGroup.mk (rootDiagAutHom Tag.E6 K a) : Outer (adjointGroup Tag.E6 K)) =
        QuotientGroup.mk α := ha
    rw [QuotientGroup.eq] at h3
    have hα' : α ∈ (rootDiagAutHom Tag.E6 K).range ⊔ inner (adjointGroup Tag.E6 K) := by
      have := Subgroup.mul_mem_sup (MonoidHom.mem_range.2 ⟨a, rfl⟩ :
        rootDiagAutHom Tag.E6 K a ∈ (rootDiagAutHom Tag.E6 K).range) h3
      simpa using this
    rw [diagJ, sup_comm]
    exact hα'
  have := pRank_mono (p := 3) (by norm_num) hker
  omega

end Untwisted

theorem three_dvd_sq_sub_one {x : ℕ} (hx : 3 ∣ x + 1) : 3 ∣ x ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · simp
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have : (y + 1) ^ 2 - 1 = y * (y + 2) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [this]
  exact Dvd.dvd.mul_left (by simpa using hx) _

section Twisted


theorem e6RankUpper_tw_of_J (hJ : E6JBoundUntw) (hT : E6JBoundTw) {S : Type} [Group S] [Finite S]
    {n r f : ℕ} (hm : CFSG.Blueprint.LieModel S .twistedE6 n r f) (h3 : 3 ∣ r ^ f + 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 6 ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut S)) ≤ 7 := by
  obtain ⟨hrp, hf1, hTm⟩ := twistedModel_of_lieModel_E6 hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hTm
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 hrp hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hrp hf1 K hcard σ' hσ'
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (pow_ne_zero _ hrp.ne_zero))
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [hcard]; exact three_dvd_sq_sub_one h3
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hJK : CFSG.Open.pRank 3 (diagJ K) ≤ 6 := hJ K hK3
  have hSK : CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 6 :=
    (pRank_adjointGroup_le_diagJ K).trans hJK
  have hle : twistedE6RootGroup K σ' ≤ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ'.toRingHom).trans
      (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ'.toRingHom)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hC0' := pRank_top_le_of_injective (p := 3) (by norm_num) (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  have hC0 : CFSG.Open.pRank 3 (⊤ : Subgroup (twistedE6RootGroup K σ')) ≤ 6 :=
    hC0'.trans hSK
  have e' : S ≃* twistedE6RootGroup K σ' := e.trans E
  refine ⟨(pRank_top_eq_of_mulEquiv (by norm_num) e').trans_le hC0, ?_⟩
  rw [pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr e')]
  have hK3' : Nat.card K = r ^ (f * 2) := by rw [hcard, ← pow_mul]; rfl
  have hring := card_ringAut_and_isCyclic hrp K hK3'
  have hfinR : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have hcycR : IsCyclic (RingAut K) := hring.2
  have hstep := pRank_le_of_hom_ker Θ
    (fun F hF => card_le_three_of_elemAbelian_cyclic F hF)
  have hB := hT r f hrp hf1 h3 K hcard σ' hσ'
  rw [hker] at hstep
  omega

end Twisted

theorem e6RankUpper_of_J (hJ : E6JBoundUntw) (hT : E6JBoundTw) :
    E6RankUpper := by
  intro S _ _ t n r f hm hpar
  rcases hpar with ⟨rfl, h3⟩ | ⟨rfl, h3⟩
  · exact e6RankUpper_untw_of_J hJ hm h3
  · exact e6RankUpper_tw_of_J hJ hT hm h3

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
