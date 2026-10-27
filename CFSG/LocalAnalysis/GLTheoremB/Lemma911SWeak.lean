module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma911SProof
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

@[expose] def Lemma911TypeWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M → p = 3 →
      ∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
        IsTwoPrimeComp (alphaOf p M ⊓ Subgroup.centralizer ({b} : Set G)) J →
          Nonempty (((↥J ⧸ CFSG.pCore 2 ↥J) ⧸ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) ≃*
            ↥(alternatingGroup (Fin 7)))

theorem nonempty_quot_center_alt7_transport {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Nonempty ((X ⧸ Subgroup.center X) ≃* ↥(alternatingGroup (Fin 7)))) :
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* ↥(alternatingGroup (Fin 7))) := by
  obtain ⟨f⟩ := h
  exact ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm.trans f⟩

section Main

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem lemma911S_of_typeWeak (hT : Lemma911TypeWeak) : Lemma911S := by
  intro G _ _ m p hSt B M hB hM hp3 b hb hb1 J hJX
  have hp := hSt.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set X := alphaOf p M ⊓ C with hX
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hb
  have hH₀X : M ⊓ C ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq, hX, gLBConj_inf,
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_alphaOf p M hg.1),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg.2)]
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := fun x hx => hH₀X ⟨hBM hx, hBC hx⟩
  have hJle : J ≤ X := hJX.1
  have hJ3 := hT G m p hSt B M hB hM hp3 b hb hb1 J hJX
  set N : Subgroup ↥X := CFSG.pCore 2 ↥X with hN
  have hchar : N.Characteristic := by
    rw [hN]
    exact CFSG.LieType.BorelTits.pCore_characteristic 2
  have hN2 : IsPGroup 2 ↥N := by
    rw [hN]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  let ρ : ↥B →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hBX)
  have hρ : ∀ (x : ↥B) (q : ↥X), (((ρ x) q : ↥X) : G) = (x : G) * q * (x : G)⁻¹ := fun x q =>
    X.normalizerMonoidHom_apply_apply_coe (Subgroup.inclusion hBX x) q
  have hρN : ∀ x : ↥B, N.map (ρ x).toMonoidHom = N := fun x =>
    Subgroup.characteristic_iff_map_eq.1 hchar (ρ x)
  have hΓ : IsPGroup 3 ↥B := hp3 ▸ isPGroup_of_isElemAbelian' hB.1.1
  set Jq : Subgroup ↥X := J.subgroupOf X with hJq
  have hJp : ⁅Jq, Jq⁆ = Jq := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hJq, Subgroup.map_subgroupOf_eq_of_le hJle]
    exact hJX.2.2.1
  have hA7 : Nonempty ((↥(Jq.map (QuotientGroup.mk' N)) ⧸
      Subgroup.center ↥(Jq.map (QuotientGroup.mk' N))) ≃* ↥(alternatingGroup (Fin 7))) :=
    nonempty_quot_center_alt7_transport (quotEquivTwoImage hJle hJX.2.1) hJ3
  obtain ⟨SQ, hSQ2, hSQJ, hSQinv, hSQgen⟩ :=
    exists_invariant_two_subgroup_of_quot hΓ ρ N hN2 hρN hJp hJX.2.2.2 hA7
  set JstQ : Subgroup ↥X := ⨆ x : ↥B, Jq.map (ρ x).toMonoidHom with hJstQ
  have hmapJ : ∀ x : ↥B, (Jq.map (ρ x).toMonoidHom).map X.subtype = GLBConj ((x : G)⁻¹) J := by
    intro x
    ext z
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      rw [mem_gLBConj]
      have hq' : (q : G) ∈ J := (Subgroup.mem_subgroupOf).1 hq
      show (x : G)⁻¹ * (((ρ x) q : ↥X) : G) * (x : G)⁻¹⁻¹ ∈ J
      rw [hρ]
      have : (x : G)⁻¹ * ((x : G) * (q : G) * (x : G)⁻¹) * (x : G)⁻¹⁻¹ = (q : G) := by group
      rw [this]
      exact hq'
    · intro hz
      rw [mem_gLBConj] at hz
      have hzX : (x : G)⁻¹ * z * (x : G)⁻¹⁻¹ ∈ X := hJle hz
      have hzX' : z ∈ X := by
        have := (Subgroup.mem_normalizer_iff.1 (hBX x.2) ((x : G)⁻¹ * z * (x : G)⁻¹⁻¹)).1 hzX
        simpa [mul_assoc] using this
      refine ⟨ρ x ⟨(x : G)⁻¹ * z * (x : G)⁻¹⁻¹, hzX⟩, ⟨⟨(x : G)⁻¹ * z * (x : G)⁻¹⁻¹, hzX⟩,
        (Subgroup.mem_subgroupOf).2 hz, rfl⟩, ?_⟩
      show (((ρ x) ⟨(x : G)⁻¹ * z * (x : G)⁻¹⁻¹, hzX⟩ : ↥X) : G) = z
      rw [hρ]
      group
  have hJst : JstQ.map X.subtype = bConjJoin B J := by
    rw [hJstQ, Subgroup.map_iSup]
    refine le_antisymm (iSup_le fun x => ?_) ?_
    · rw [hmapJ]
      exact le_iSup₂_of_le ((x : G)⁻¹) (B.inv_mem x.2) le_rfl
    · refine iSup₂_le fun g hg => ?_
      refine le_iSup_of_le ⟨g⁻¹, B.inv_mem hg⟩ ?_
      rw [hmapJ]
      show GLBConj g J ≤ GLBConj ((g⁻¹ : G)⁻¹) J
      rw [inv_inv]
  refine ⟨SQ.map X.subtype, hSQ2.map _, ?_, ?_, ?_⟩
  ·
    have key : ∀ g ∈ B, ∀ z ∈ SQ.map X.subtype, g * z * g⁻¹ ∈ SQ.map X.subtype := by
      rintro g hg _ ⟨sq, hsq, rfl⟩
      refine ⟨ρ ⟨g, hg⟩ sq, hSQinv ⟨g, hg⟩ ⟨sq, hsq, rfl⟩, ?_⟩
      show (((ρ ⟨g, hg⟩) sq : ↥X) : G) = g * (sq : G) * g⁻¹
      rw [hρ]
    intro g hg
    refine Subgroup.mem_normalizer_iff.2 fun z => ⟨key g hg z, fun hz => ?_⟩
    have := key g⁻¹ (B.inv_mem hg) _ hz
    simpa [mul_assoc] using this
  · rw [← hJst]
    exact Subgroup.map_mono hSQJ
  · rw [← hJst]
    refine (Subgroup.map_mono hSQgen).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hy => ?_
    have hyJ : (y : G) ∈ JstQ.map X.subtype := ⟨y, hy, rfl⟩
    refine le_trans ?_ (le_iSup₂_of_le ((y : G)⁻¹) ((JstQ.map X.subtype).inv_mem hyJ) le_rfl)
    rintro _ ⟨_, ⟨sq, hsq, rfl⟩, rfl⟩
    show (y : G) * (sq : G) * (y : G)⁻¹ ∈ GLBConj ((y : G)⁻¹) (SQ.map X.subtype)
    rw [mem_gLBConj]
    have : (y : G)⁻¹ * ((y : G) * (sq : G) * (y : G)⁻¹) * (y : G)⁻¹⁻¹ = (sq : G) := by group
    rw [this]
    exact ⟨sq, hsq, rfl⟩

end Main

end CFSG.LocalAnalysis.GLTheoremB
