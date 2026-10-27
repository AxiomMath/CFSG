module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxGroup
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Vocab
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def actB {B X : Subgroup G} (hBX : B ≤ Subgroup.normalizer (X : Set G)) :
    ↥B →* MulAut ↥X :=
  X.normalizerMonoidHom.comp (Subgroup.inclusion hBX)

omit [Finite G] in
theorem actB_apply {B X : Subgroup G} (hBX : B ≤ Subgroup.normalizer (X : Set G)) (b : B)
    (x : X) : ((actB hBX b x : ↥X) : G) = (b : G) * x * (b : G)⁻¹ := by
  change (((X.normalizerMonoidHom) (Subgroup.inclusion hBX b)) x : G) = _
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

omit [Finite G] in
theorem le_normalizer_map_subtype {B X : Subgroup G} (hBX : B ≤ Subgroup.normalizer (X : Set G))
    {S : Subgroup ↥X} (hS : ∀ γ : B, S.map (actB hBX γ).toMonoidHom = S) :
    B ≤ Subgroup.normalizer (S.map X.subtype : Set G) := by
  have fwd : ∀ b : B, ∀ g ∈ S.map X.subtype, (b : G) * g * (b : G)⁻¹ ∈ S.map X.subtype := by
    intro b g hg
    obtain ⟨s, hs, rfl⟩ := hg
    have hmem : actB hBX b s ∈ S.map (actB hBX b).toMonoidHom := Subgroup.mem_map_of_mem _ hs
    rw [hS b] at hmem
    refine ⟨actB hBX b s, hmem, ?_⟩
    simpa using actB_apply hBX b s
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fwd ⟨b, hb⟩ g, fun h => ?_⟩
  have := fwd ⟨b, hb⟩⁻¹ _ h
  simpa [mul_assoc] using this

omit [Finite G] in
theorem exists_isComponentOf_of_glaPLayer_ne_bot {X : Subgroup G} (h : GLAPLayer 2 X ≠ ⊥) :
    ∃ K : Subgroup (Qt ↥X), IsComponentOf K ⊤ := by
  by_contra hno
  push Not at hno
  apply h
  have : {L | GLAPComponent 2 X L} = (∅ : Set (Subgroup G)) := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hL
    exact hno _ hL.2.2.1
  unfold GLAPLayer
  rw [this, sSup_empty]

private theorem pCore_two_le_open (H : Type) [Group H] :
    CFSG.pCore 2 H ≤ CFSG.Open.pCore 2 H :=
  le_rfl

omit [Finite G] in
theorem layerPreimage_le_map_preimQ (X : Subgroup G) :
    layerPreimage X ≤ (preimQ (Ybar ↥X)).map X.subtype := by
  refine sup_le (sSup_le fun J hJ => ?_) ?_
  · have hcomp : IsComponentOf (barX 2 X J) ⊤ := hJ.2.2.1
    have h1 : barX 2 X J ≤ Ybar ↥X :=
      (CFSG.ComponentClassification.Layer.component_le hcomp).trans le_sup_left
    refine (le_preimBarX 2 hJ.1).trans ?_
    exact Subgroup.map_mono (Subgroup.comap_mono h1)
  · refine Subgroup.map_mono (Subgroup.comap_mono ?_)
    exact (pCore_two_le_open _).trans le_sup_right

omit [Finite G] in
theorem hFaith_of_h83 {B X : Subgroup G} (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (h83 : ∀ b ∈ B, (∀ y ∈ layerPreimage X, b * y * b⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 2 X) → b = 1) :
    ∀ γ : B, (∀ y ∈ preimQ (Ybar ↥X), actB hBX γ y * y⁻¹ ∈ GLAPPrimeCore 2 ↥X) → γ = 1 := by
  intro γ hγ
  refine Subtype.ext (h83 γ γ.2 fun y hy => ?_)
  obtain ⟨y', hy', rfl⟩ := layerPreimage_le_map_preimQ X hy
  refine ⟨actB hBX γ y' * y'⁻¹, hγ y' hy', ?_⟩
  simp [actB_apply]

theorem hS2_of_h82 {B X : Subgroup G} (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (h82 : ∀ N : Subgroup G, IsTwoLocal N → B ≤ N → ∀ J : Subgroup G, GLAPComponent 2 X J →
      ¬ J ≤ (N ⊓ X) ⊔ GLAPPrimeCoreOf 2 X) :
    ∀ S : Subgroup ↥X, IsPGroup 2 S → (∀ γ : B, S.map (actB hBX γ).toMonoidHom = S) → S ≠ ⊥ →
      ∀ K : Subgroup (Qt ↥X), IsComponentOf K ⊤ →
        ¬ S.map (mkQ ↥X) ≤ Subgroup.centralizer (K : Set (Qt ↥X)) := by
  intro S hS2 hinv hne K hK hcent
  obtain ⟨J, hJ, hbar⟩ := exists_glaPComponent_barX_eq X hK
  set SG : Subgroup G := S.map X.subtype with hSG
  set O : Subgroup G := GLAPPrimeCoreOf 2 X with hO
  have hSGX : SG ≤ X := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hSGne : SG ≠ ⊥ := by
    intro h
    apply hne
    have h' : S.map X.subtype = ⊥ := h
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have : X.subtype x ∈ (⊥ : Subgroup G) := h' ▸ Subgroup.mem_map_of_mem _ hx
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  have hSG2 : IsPGroup 2 SG :=
    hS2.map X.subtype
  have hOodd : ¬ 2 ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf Nat.prime_two X
  have hSGnorm : SG ≤ Subgroup.normalizer (O : Set G) := hSGX.trans (le_normalizer_glaPPrimeCoreOf 2 X)
  have hsyl := sylow_sup_of_coprime hSG2 hSGnorm hOodd
  refine h82 (Subgroup.normalizer (SG : Set G)) ⟨SG, hSGne, hSG2, rfl⟩
    (le_normalizer_map_subtype hBX hinv) J hJ ?_
  intro j hj
  have hjX : j ∈ X := hJ.1 hj
  obtain ⟨o, ho, hoj⟩ := exists_mem_normalizer_of_sylow hSG2 hSGnorm hsyl (j := j) (by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : mkQ ↥X ⟨j, hjX⟩ ∈ K := by
      rw [← hbar]
      exact ⟨⟨j, hjX⟩, hj, rfl⟩
    have h2 : mkQ ↥X s ∈ Subgroup.centralizer (K : Set (Qt ↥X)) :=
      hcent (Subgroup.mem_map_of_mem _ hs)
    have h3 : mkQ ↥X ⟨j, hjX⟩ * mkQ ↥X s = mkQ ↥X s * mkQ ↥X ⟨j, hjX⟩ :=
      (Subgroup.mem_centralizer_iff.1 h2) _ h1
    have h4 : (⟨j, hjX⟩ * s * ⟨j, hjX⟩⁻¹ * s⁻¹ : ↥X) ∈ GLAPPrimeCore 2 ↥X := by
      rw [← QuotientGroup.ker_mk' (GLAPPrimeCore 2 ↥X), MonoidHom.mem_ker]
      show mkQ ↥X _ = 1
      simp only [map_mul, map_inv]
      calc _ = (mkQ ↥X s * mkQ ↥X ⟨j, hjX⟩) * (mkQ ↥X ⟨j, hjX⟩)⁻¹ * (mkQ ↥X s)⁻¹ := by rw [h3]
        _ = 1 := by group
    exact ⟨_, h4, rfl⟩)
  have hoX : o ∈ X := by
    obtain ⟨o', -, rfl⟩ := ho
    exact o'.2
  have hnX : o⁻¹ * j ∈ X := X.mul_mem (X.inv_mem hoX) hjX
  have : j = o * (o⁻¹ * j) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ho)
    (Subgroup.mem_sup_left (show o⁻¹ * j ∈ Subgroup.normalizer (SG : Set G) ⊓ X from ⟨hoj, hnX⟩))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
