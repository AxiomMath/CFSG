module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartner
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseS

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

section Order

variable {G : Type} [Group G] [Finite G]

theorem card_le_card_fixSubgroup_of_le {L M : Subgroup G} (hLM : L ≤ M) (hZL : center L = ⊥)
    {X : Type*} [Group X] (eM : M ⧸ center M ≃* X) {t : G} (htC : t ∈ centralizer (L : Set G))
    (htM : t ∈ normalizer (M : Set G)) :
    Nat.card L ≤ Nat.card (E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) := by
  have : Finite X := Finite.of_equiv _ eM.toEquiv
  have hfix : ∀ l : L, eM (QuotientGroup.mk' (center M) ⟨l, hLM l.2⟩) ∈
      E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
    intro l
    change normalizerQuotMulAut eM ⟨t, htM⟩ _ = eM (QuotientGroup.mk' (center M) ⟨l, hLM l.2⟩)
    rw [normalizerQuotMulAut_apply]
    congr 2
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change t * (l : G) * t⁻¹ = l
    rw [(mem_centralizer_iff.1 htC l l.2).symm, mul_inv_cancel_right]
  refine Nat.card_le_card_of_injective (fun l => ⟨_, hfix l⟩) fun a b hab => ?_
  have h1 : eM (QuotientGroup.mk' (center M) ⟨a, hLM a.2⟩) =
      eM (QuotientGroup.mk' (center M) ⟨b, hLM b.2⟩) := congrArg Subtype.val hab
  have h2 := QuotientGroup.eq.1 (eM.injective h1)
  have h3 : a⁻¹ * b ∈ center L := by
    rw [mem_center_iff]
    intro l
    apply Subtype.ext
    have := congrArg Subtype.val (mem_center_iff.1 h2 ⟨l, hLM l.2⟩)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  rw [hZL, mem_bot, inv_mul_eq_one] at h3
  exact h3

theorem false_of_le_of_conj_xi_E6 {L M : Subgroup G} (hLM : L ≤ M) (hZL : center L = ⊥)
    {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {K' : Type} [Field K'] (hK' : Nat.card K' = 2 ^ f)
    (eM : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K') {t : G}
    (htC : t ∈ centralizer (L : Set G)) (htM : t ∈ normalizer (M : Set G))
    {η φ : MulAut (adjointGroup TwistTag.E6.tag K')}
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K', (η h : ModGL TwistTag.E6.tag K') =
      diagramMap TwistTag.E6 K' * h * (diagramMap TwistTag.E6 K')⁻¹)
    (hx : pinnedX TwistTag.E6.tag K' e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K')
    (hφ : φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η) : False := by
  have := finite_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK'
  have hf : 1 ≤ f := one_le_of_natCard_eq_two_pow hK'
  have : Finite (ModGL TwistTag.E6.tag K') := finite_modGL
  set M' := GaloisField 2 (2 * f)
  have hM' : Nat.card M' = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hK' hM'
  let _ : Algebra K' M' := ι.toAlgebra
  have hσM : ∀ c : M', iterateFrobenius M' 2 f c = c ^ 2 ^ f := fun c =>
    iterateFrobenius_def (p := 2) f c
  obtain ⟨-, -, -, -, ⟨eJ, -, -, hsec⟩, -⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf K' M' hK' hM' _ hσM
  have hlt := card_eqLocus_secondGraph_lt hsec center_adjointGroup_eq_bot hη hx
  rw [Nat.card_congr eJ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK']
    at hlt
  have hle := card_le_card_fixSubgroup_of_le hLM hZL eM htC htM
  have hmap := map_eqLocus_eq_of_conj hφ
  have hcard : Nat.card (E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) =
      Nat.card ((MulAut.conj (⟨_, hx⟩ : adjointGroup TwistTag.E6.tag K') * η).toMonoidHom.eqLocus
        (MonoidHom.id _)) := by
    rw [← hmap, card_map_of_injective φ.injective]
    rfl
  rw [hcard, Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
    hK] at hle
  omega

theorem false_of_le_of_conj_xi_twistedE6 {L M : Subgroup G} (hLM : L ≤ M) (hZL : center L = ⊥)
    {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2) {σ : K₂ →+* K₂}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 K₂ σ)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (htM : t ∈ normalizer (M : Set G))
    {η φ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
      diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹)
    (hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K₂ σ)
    (hφ : φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η) : False := by
  have := finite_of_natCard_eq_two_pow hK
  have hf : 1 ≤ f := one_le_of_natCard_eq_two_pow hK
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by rw [hK₂]; positivity)
  have : Finite (ModGL TwistTag.E6.tag K₂) := finite_modGL
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK₂
  let _ : Algebra (GaloisField 2 f) K₂ := ι.toAlgebra
  obtain ⟨-, -, -, -, -, ⟨eJ, -, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf (GaloisField 2 f) K₂ hk hK₂ σ hσ
  have hlt := card_eqLocus_secondGraph_lt hsec center_adjointGroup_eq_bot hη hx
  rw [Nat.card_congr eJ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hk]
    at hlt
  have hle := card_le_card_fixSubgroup_of_le hLM hZL eM htC htM
  have hmap := map_eqLocus_eq_of_conj hφ
  have hcard : Nat.card (E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) =
      Nat.card ((MulAut.conj (⟨_, hx⟩ : graphFixedRootGroup TwistTag.E6 K₂ σ) *
        η).toMonoidHom.eqLocus (MonoidHom.id _)) := by
    rw [← hmap, card_map_of_injective φ.injective]
    rfl
  rw [hcard, Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
    hK] at hle
  omega

end Order

section Dichotomy

theorem conj_eta_or_conj_xi_of_exhaustion {E : Type} [Field E]
    {C : Subgroup (ModGL TwistTag.E6.tag E)}
    (hPP : diagramMap TwistTag.E6 E * diagramMap TwistTag.E6 E = 1)
    (hexh : ∀ a ∈ C, (a * diagramMap TwistTag.E6 E) ^ 2 = 1 →
        (∃ g ∈ C, g * (a * diagramMap TwistTag.E6 E) * g⁻¹ = diagramMap TwistTag.E6 E) ∨
        ∃ g ∈ C, g * (a * diagramMap TwistTag.E6 E) * g⁻¹ =
          pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E)
    (hfaith : ∀ c ∈ C, (∀ g ∈ C, c * g * c⁻¹ = g) → c = 1)
    (hx : pinnedX TwistTag.E6.tag E e6HighestRoot 1 ∈ C)
    {η : MulAut C} (hη : ∀ h : C, (η h : ModGL TwistTag.E6.tag E) =
      diagramMap TwistTag.E6 E * h * (diagramMap TwistTag.E6 E)⁻¹)
    (a : C) (hB2 : (MulAut.conj a * η) ^ 2 = 1) :
    (∃ g : C, MulAut.conj g * (MulAut.conj a * η) * (MulAut.conj g)⁻¹ = η) ∨
      ∃ g : C, MulAut.conj g * (MulAut.conj a * η) * (MulAut.conj g)⁻¹ =
        MulAut.conj ⟨_, hx⟩ * η := by
  set P := diagramMap TwistTag.E6 E with hPdef
  have hPi : P⁻¹ = P := inv_eq_of_mul_eq_one_right hPP
  have hη2 : ∀ h : C, η (η h) = h := fun h => Subtype.ext (by
    rw [hη, hη, hPi]
    calc P * (P * (h : ModGL TwistTag.E6.tag E) * P) * P = (P * P) * h * (P * P) := by group
      _ = h := by rw [hPP, one_mul, mul_one])
  have hηη : η * η = 1 := MulEquiv.ext fun h => hη2 h
  have hsq : (MulAut.conj a * η) ^ 2 = MulAut.conj (a * η a) := by
    rw [sq, map_mul]
    calc MulAut.conj a * η * (MulAut.conj a * η) = MulAut.conj a * (η * MulAut.conj a) * η := by
          group
      _ = MulAut.conj a * (MulAut.conj (η a) * η) * η := by
          rw [← mulAut_conj_conj_eq η a, inv_mul_cancel_right]
      _ = MulAut.conj a * MulAut.conj (η a) * (η * η) := by group
      _ = MulAut.conj a * MulAut.conj (η a) := by rw [hηη, mul_one]
  have haa : ((a : ModGL TwistTag.E6.tag E) * (η a : ModGL TwistTag.E6.tag E)) = 1 := by
    refine hfaith _ (mul_mem a.2 (η a).2) fun g hg => ?_
    have h1 := congrArg (fun β : MulAut C => ((β ⟨g, hg⟩ : C) : ModGL TwistTag.E6.tag E)) hB2
    simp only [hsq, MulAut.conj_apply, MulAut.one_apply] at h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have haP : ((a : ModGL TwistTag.E6.tag E) * P) ^ 2 = 1 := by
    have h1 : ((a : ModGL TwistTag.E6.tag E) * P) ^ 2 =
        (a : ModGL TwistTag.E6.tag E) * (P * a * P⁻¹) * (P * P) := by
      rw [sq]; group
    rw [h1, ← hη, haa, hPP, one_mul]
  have key : ∀ (g : ModGL TwistTag.E6.tag E) (hg : g ∈ C) (h : C),
      (((MulAut.conj (⟨g, hg⟩ : C) * (MulAut.conj a * η) * (MulAut.conj (⟨g, hg⟩ : C))⁻¹) h : C) :
        ModGL TwistTag.E6.tag E) = (g * (a * P) * g⁻¹) * h * (g * (a * P) * g⁻¹)⁻¹ := by
    intro g hg h
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
      MulAut.conj_symm_apply, MulAut.conj_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hη]
    group
  rcases hexh a a.2 haP with ⟨g, hg, hgP⟩ | ⟨g, hg, hgP⟩
  · refine Or.inl ⟨⟨g, hg⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    rw [key g hg h, hgP, hη]
  · refine Or.inr ⟨⟨g, hg⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    rw [key g hg h, hgP, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη]
    group

theorem inner_or_xi_of_mem {G : Type*} [Group G] {G₀ : Subgroup G} {E : Type} [Field E]
    {C : Subgroup (ModGL TwistTag.E6.tag E)}
    (hPP : diagramMap TwistTag.E6 E * diagramMap TwistTag.E6 E = 1)
    (hexh : ∀ a ∈ C, (a * diagramMap TwistTag.E6 E) ^ 2 = 1 →
        (∃ g ∈ C, g * (a * diagramMap TwistTag.E6 E) * g⁻¹ = diagramMap TwistTag.E6 E) ∨
        ∃ g ∈ C, g * (a * diagramMap TwistTag.E6 E) * g⁻¹ =
          pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E)
    (hfaith : ∀ c ∈ C, (∀ g ∈ C, c * g * c⁻¹ = g) → c = 1)
    (hx : pinnedX TwistTag.E6.tag E e6HighestRoot 1 ∈ C)
    {η : MulAut C} (hη : ∀ h : C, (η h : ModGL TwistTag.E6.tag E) =
      diagramMap TwistTag.E6 E * h * (diagramMap TwistTag.E6 E)⁻¹)
    (e₀ : G₀ ⧸ center G₀ ≃* C) {t : G} (htN : t ∈ normalizer (G₀ : Set G)) {ψ : MulAut C}
    (hψ : ψ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * ψ⁻¹ = η) {w : G} (hwG : w ∈ G₀)
    (htw2 : (t * w) * (t * w) = 1) :
    (∃ y : G₀, normalizerQuotMulAut e₀ ⟨t * w, mul_mem htN (le_normalizer hwG)⟩ =
        MulAut.conj (e₀ (QuotientGroup.mk' (center G₀) y)) * normalizerQuotMulAut e₀ ⟨t, htN⟩ *
          (MulAut.conj (e₀ (QuotientGroup.mk' (center G₀) y)))⁻¹) ∨
      ∃ φ : MulAut C, φ * normalizerQuotMulAut e₀ ⟨t * w, mul_mem htN (le_normalizer hwG)⟩ * φ⁻¹ =
        MulAut.conj ⟨_, hx⟩ * η := by
  set A := normalizerQuotMulAut e₀ ⟨t, htN⟩ with hAdef
  set wb : C := e₀ (QuotientGroup.mk' (center G₀) ⟨w, hwG⟩) with hwb
  have hsplit : (⟨t * w, mul_mem htN (le_normalizer hwG)⟩ : normalizer (G₀ : Set G)) =
      ⟨t, htN⟩ * ⟨w, le_normalizer hwG⟩ := rfl
  have hAtw : normalizerQuotMulAut e₀ ⟨t * w, mul_mem htN (le_normalizer hwG)⟩ =
      A * MulAut.conj wb := by
    rw [hsplit, map_mul, EPilot.normalizerQuotMulAut_of_mem e₀ hwG]
  set a : C := η (ψ wb) with hadef
  have hB : ψ * normalizerQuotMulAut e₀ ⟨t * w, mul_mem htN (le_normalizer hwG)⟩ * ψ⁻¹ =
      MulAut.conj a * η := by
    rw [hAtw]
    calc ψ * (A * MulAut.conj wb) * ψ⁻¹ = (ψ * A * ψ⁻¹) * (ψ * MulAut.conj wb * ψ⁻¹) := by group
      _ = η * MulAut.conj (ψ wb) := by rw [hψ, mulAut_conj_conj_eq]
      _ = MulAut.conj a * η := by
          rw [hadef, ← mulAut_conj_conj_eq η (ψ wb)]
          group
  have hB2 : (MulAut.conj a * η) ^ 2 = 1 := by
    rw [← hB, sq]
    have h1 : (⟨t * w, mul_mem htN (le_normalizer hwG)⟩ : normalizer (G₀ : Set G)) *
        ⟨t * w, mul_mem htN (le_normalizer hwG)⟩ = 1 := Subtype.ext htw2
    calc ψ * normalizerQuotMulAut e₀ ⟨t * w, mul_mem htN (le_normalizer hwG)⟩ * ψ⁻¹ *
          (ψ * normalizerQuotMulAut e₀ ⟨t * w, mul_mem htN (le_normalizer hwG)⟩ * ψ⁻¹) =
          ψ * (normalizerQuotMulAut e₀ ⟨t * w, mul_mem htN (le_normalizer hwG)⟩ *
            normalizerQuotMulAut e₀ ⟨t * w, mul_mem htN (le_normalizer hwG)⟩) * ψ⁻¹ := by group
      _ = 1 := by rw [← map_mul, h1, map_one, mul_one, mul_inv_cancel]
  rcases conj_eta_or_conj_xi_of_exhaustion hPP hexh hfaith hx hη a hB2 with ⟨g, hg⟩ | ⟨g, hg⟩
  · left
    obtain ⟨q, hq⟩ := e₀.surjective (ψ⁻¹ g⁻¹)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center G₀) q
    refine ⟨y, ?_⟩
    rw [hq]
    have h1 : normalizerQuotMulAut e₀ ⟨t * w, mul_mem htN (le_normalizer hwG)⟩ =
        ψ⁻¹ * (MulAut.conj g)⁻¹ * η * MulAut.conj g * ψ := by
      rw [← hg, ← hB]
      group
    rw [h1, ← hψ, ← mulAut_conj_conj_eq ψ⁻¹ g⁻¹, map_inv]
    group
  · right
    exact ⟨MulAut.conj g * ψ, by rw [← hg, ← hB]; group⟩

end Dichotomy

section Statements

theorem conj_mem_normalizer_of_mem_normalizer_conjugate_inv {G : Type*} [Group G]
    {G₀ : Subgroup G} {g s : G} (h : s ∈ normalizer (CFSG.conjugate G₀ g⁻¹ : Set G)) :
    g⁻¹ * s * g ∈ normalizer (G₀ : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have h1 := mem_normalizer_iff.1 h (g * x * g⁻¹)
  rw [mem_conjugate_iff_of_mul, mem_conjugate_iff_of_mul, inv_inv] at h1
  have e1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  have e2 : g⁻¹ * (s * (g * x * g⁻¹) * s⁻¹) * g = (g⁻¹ * s * g) * x * (g⁻¹ * s * g)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

@[expose] def XiFixPerfectE6Input : Prop :=
  ∀ (f : ℕ) (K' : Type) [Field K'] [Finite K'], 2 ≤ f → Nat.card K' = 2 ^ f →
    ∀ (η : MulAut (adjointGroup TwistTag.E6.tag K')),
      (∀ h : adjointGroup TwistTag.E6.tag K', (η h : ModGL TwistTag.E6.tag K') =
        diagramMap TwistTag.E6 K' * h * (diagramMap TwistTag.E6 K')⁻¹) →
      ∀ hx : pinnedX TwistTag.E6.tag K' e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K',
        ⁅E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : adjointGroup TwistTag.E6.tag K') * η),
          E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : adjointGroup TwistTag.E6.tag K') * η)⁆ =
        E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : adjointGroup TwistTag.E6.tag K') * η)

@[expose] def XiFixPerfectTwistedE6Input : Prop :=
  ∀ (f : ℕ) (K₂ : Type) [Field K₂] [Finite K₂] (σ : K₂ →+* K₂), 2 ≤ f →
    Nat.card K₂ = (2 ^ f) ^ 2 → (∀ c, σ c = c ^ 2 ^ f) →
    ∀ (η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)),
      (∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
        diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) →
      ∀ hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K₂ σ,
        ⁅E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : graphFixedRootGroup TwistTag.E6 K₂ σ) * η),
          E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : graphFixedRootGroup TwistTag.E6 K₂ σ) * η)⁆ =
        E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : graphFixedRootGroup TwistTag.E6 K₂ σ) * η)

@[expose] def E6RowXiCaseLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f → E6RowKinds e t f →
    ∀ (K' : Type) [Field K'] [Finite K'], Nat.card K' = 2 ^ f →
    ∀ (e₀ : pieceSpan e ⧸ center (pieceSpan e) ≃* adjointGroup TwistTag.E6.tag K')
      (M : Subgroup G), (∃ g : G, M = CFSG.conjugate (pieceSpan e) g) →
    ∀ (htM : t ∈ normalizer (M : Set G)) (eM : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K')
      (η : MulAut (adjointGroup TwistTag.E6.tag K')),
      (∀ h : adjointGroup TwistTag.E6.tag K', (η h : ModGL TwistTag.E6.tag K') =
        diagramMap TwistTag.E6 K' * h * (diagramMap TwistTag.E6 K')⁻¹) →
    ∀ (hx : pinnedX TwistTag.E6.tag K' e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K')
      (φ : MulAut (adjointGroup TwistTag.E6.tag K')),
      φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η →
    ∀ (w : G) (hwM : w ∈ M), w ∈ L → w * w = 1 → t * w = w * t →
      eM (QuotientGroup.mk' (center M) ⟨w, hwM⟩) = φ⁻¹ ⟨_, hx⟩ →
      w ∈ perfectCore (M ⊓ centralizer ({t} : Set G)) →
      (∀ c ∈ M ⊓ centralizer ({t} : Set G), c * w = w * c) →
    ∀ (htwM : t * w ∈ normalizer (M : Set G)),
      (∃ φ₁ : MulAut (adjointGroup TwistTag.E6.tag K'),
        φ₁ * normalizerQuotMulAut eM ⟨t * w, htwM⟩ * φ₁⁻¹ = η) →
    ∀ (htN : t ∈ normalizer (pieceSpan e : Set G))
      (htwN : t * w ∈ normalizer (pieceSpan e : Set G)),
      pieceSpan e ⊓ centralizer ({t} : Set G) = L →
      (∃ ψ : MulAut (adjointGroup TwistTag.E6.tag K'),
        ψ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * ψ⁻¹ = η) →
      (∃ φ' : MulAut (adjointGroup TwistTag.E6.tag K'),
        φ' * normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ * φ'⁻¹ = MulAut.conj ⟨_, hx⟩ * η) →
      False

@[expose] def TwistedE6RowXiCaseLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    TwistedE6RowKinds e t f →
    ∀ (K₂ : Type) [Field K₂] [Finite K₂] (σ : K₂ →+* K₂), Nat.card K₂ = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ (2 ^ f)) →
    ∀ (e₀ : pieceSpan e ⧸ center (pieceSpan e) ≃* graphFixedRootGroup TwistTag.E6 K₂ σ),
      t ∉ pieceSpan e →
    ∀ (M : Subgroup G), (∃ g : G, M = CFSG.conjugate (pieceSpan e) g) →
    ∀ (htM : t ∈ normalizer (M : Set G))
      (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 K₂ σ)
      (η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)),
      (∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
        diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) →
    ∀ (hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K₂ σ)
      (φ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)),
      φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η →
    ∀ (w : G) (hwM : w ∈ M), w ∈ L → w * w = 1 → t * w = w * t →
      eM (QuotientGroup.mk' (center M) ⟨w, hwM⟩) = φ⁻¹ ⟨_, hx⟩ →
      w ∈ perfectCore (M ⊓ centralizer ({t} : Set G)) →
      (∀ c ∈ M ⊓ centralizer ({t} : Set G), c * w = w * c) →
    ∀ (htwM : t * w ∈ normalizer (M : Set G)),
      (∃ φ₁ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
        φ₁ * normalizerQuotMulAut eM ⟨t * w, htwM⟩ * φ₁⁻¹ = η) →
    ∀ (htN : t ∈ normalizer (pieceSpan e : Set G))
      (htwN : t * w ∈ normalizer (pieceSpan e : Set G)),
      pieceSpan e ⊓ centralizer ({t} : Set G) = L →
      (∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
        ψ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * ψ⁻¹ = η) →
      (∃ φ' : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
        φ' * normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ * φ'⁻¹ = MulAut.conj ⟨_, hx⟩ * η) →
      False

end Statements

section RowE6

theorem e6RowXiExclusionInput_of_caseL (hperf : XiFixPerfectE6Input) (hL : E6RowXiCaseLInput) :
    E6RowXiExclusionInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk K' _ _ hK' he₆ M hM htM eM η hη hx φ hφ
  obtain ⟨e₀⟩ : Nonempty (pieceSpan e ⧸ center (pieceSpan e) ≃*
    adjointGroup TwistTag.E6.tag K') := he₆
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hG₀ := commutator_pieceSpan e
  have hLG₀ := le_pieceSpan hq e
  have htN : t ∈ normalizer (pieceSpan e : Set G) :=
    mem_normalizer_iSup fun J => le_normalizer_pieceCore e hw.mem_centralizer J.1
  have h36 : 2 ^ (36 * f) ∣ Nat.card (adjointGroup TwistTag.E6.tag K') := by
    change 2 ^ (36 * f) ∣ Nat.card (adjointGroup Tag.E6 K')
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hK']
    obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordE6' (by omega : 1 ≤ f)).two
    rw [hr, mul_comm 36 f]
    exact Dvd.intro r rfl
  have htC : t ∉ centralizer (pieceSpan e : Set G) :=
    not_mem_centralizer_of_two_pow_dvd_quot hw.standard hw.one_le hw.card_eq e
      hw.mem_centralizer hw.orderOf_eq hG₀ e₀ h36
  have hC := odd_card_centralizer_pieceSpan hw e hLG₀ htC
  have hZ := odd_card_center_of_odd_card_centralizer hC
  have hK'2 : ringChar K' = 2 :=
    CFSG.LieType.Chevalley.E6SecondGraphFixed.ringChar_eq_two_of_card hw.one_le hK'
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  obtain ⟨g₁, hg₁⟩ := hM
  set g : G := g₁⁻¹ with hgdef
  have hMg : M = CFSG.conjugate (pieceSpan e) g⁻¹ := by rw [hgdef, inv_inv]; exact hg₁
  subst hMg
  have hZM : Odd (Nat.card (center (CFSG.conjugate (pieceSpan e) g⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  obtain ⟨hx2, hηx, hfix⟩ := xi_data_of_le hK'2 le_rfl hη hx
  obtain ⟨w, hww, htw, hwq, htwM, hφw⟩ :=
    exists_partner_of_conj_eq_conj_mul hZM eM htM hx2 hηx hφ
  have hperfA := fixSubgroup_perfect_of_conj hφ (hperf f K' hf hK' η hη hx)
  have hwΛ := mem_perfectCore_of_fixSubgroup_perfect hZM eM hw.orderOf_eq htM hperfA hww htw
  have hwL : (w : G) ∈ L :=
    perfectCore_inf_centralizer_le hw.standard hOut hw.mem_centralizer hw.orderOf_eq _ hwΛ
  have hwG₀ : (w : G) ∈ pieceSpan e := hLG₀ hwL
  have hcomm : ∀ c ∈ CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G),
      c * w = w * c := fun c hc =>
    commute_partner_of_fix hZM eM htM hφ hfix hww hwq hc.1
      (mem_centralizer_singleton_iff.1 hc.2)
  have hww' : (w : G) * w = 1 := by rw [← Subgroup.coe_mul, hww, Subgroup.coe_one]
  rcases inf_centralizer_eq_or_xi_E6_quot hw.standard hf hw.card_eq e hw.mem_centralizer
      hw.orderOf_eq hw.inf_eq hG₀ hZ hK' e₀ htN with
    ⟨hC₀, η₀, hη₀, φ₀, hφ₀⟩ | ⟨η₀, hη₀, hx₀, φ₀, hφ₀⟩
  swap
  · exact false_of_le_of_conj_xi_E6 hLG₀ hw.center_eq_bot hw.card_eq e hK' e₀ hw.mem_centralizer
      htN hη₀ hx₀ hφ₀
  have hηη₀ : η₀ = η := MulEquiv.ext fun x => Subtype.ext ((hη₀ x).trans (hη x).symm)
  rw [hηη₀] at hφ₀
  have hM' : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hw.one_le hK' hM'
  let _ : Algebra K' (GaloisField 2 (2 * f)) := ι.toAlgebra
  obtain ⟨⟨-, hPP, -, -, hexh, hfaith, -⟩, -⟩ :=
    even_E6_graph_inner_coset_exhaustion f hw.one_le K' (GaloisField 2 (2 * f)) hK' hM'
      (iterateFrobenius (GaloisField 2 (2 * f)) 2 f) (fun c => iterateFrobenius_def (p := 2) f c)
  have hfaith' : ∀ c ∈ adjointGroup TwistTag.E6.tag K',
      (∀ h ∈ adjointGroup TwistTag.E6.tag K', c * h * c⁻¹ = h) → c = 1 := fun c hc h =>
    hfaith c (Subgroup.mem_sup_left hc) h
  have ht2 : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have htw2 : (t * w) * (t * w) = 1 := by
    calc (t * w) * (t * w) = t * ((w : G) * t) * w := by group
      _ = t * (t * w) * w := by rw [htw]
      _ = (t * t) * ((w : G) * w) := by group
      _ = 1 := by rw [ht2, hww', mul_one]
  have hgs : g⁻¹ * (t * w) * g ∈ normalizer (pieceSpan e : Set G) :=
    conj_mem_normalizer_of_mem_normalizer_conjugate_inv htwM
  have hη' : ∃ φ₂ : MulAut (adjointGroup TwistTag.E6.tag K'),
      φ₂ * normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ * φ₂⁻¹ = η := by
    rw [← normalizerQuotMulAut_conjugate e₀ hgs htwM]
    set eM' := (E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g⁻¹).symm.trans e₀
    have heM : eM = eM'.trans (eM'.symm.trans eM) := MulEquiv.ext fun x => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [heM] at hφw
    exact (exists_conj_eq_iff_trans eM' (eM'.symm.trans eM) _ η).1 ⟨φ, hφw⟩
  have hMC : CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G) ≠ L := by
    intro hCM
    have hLM : L ≤ CFSG.conjugate (pieceSpan e) g⁻¹ := fun x hx => by
      rw [← hCM] at hx
      exact hx.1
    exact false_of_le_of_conj_xi_E6 hLM hw.center_eq_bot hw.card_eq e hK' eM hw.mem_centralizer
      htM hη hx hφ
  rcases inner_or_xi_of_mem hPP hexh hfaith' hx hη e₀ htN hφ₀ hwG₀ htw2 with ⟨y, hy⟩ | ⟨φ', hφ'⟩
  · exact false_of_xi_partner_inner_E6 hw hf hK' e₀ hZ hC htN hη ⟨hC₀, φ₀, hφ₀⟩ g hMC hww' htw hgs
      hη' (mul_mem htN (le_normalizer hwG₀)) y hy
  · exact hL G L K e t f hw hf hk K' hK' e₀ _ ⟨g⁻¹, rfl⟩ htM eM η hη hx φ hφ w w.2 hwL hww' htw
      hwq hwΛ hcomm htwM ⟨φ, hφw⟩ htN (mul_mem htN (le_normalizer hwG₀)) hC₀ ⟨φ₀, hφ₀⟩ ⟨φ', hφ'⟩

end RowE6

section RowTwistedE6

theorem twistedE6RowXiExclusionInput_of_caseL (hperf : XiFixPerfectTwistedE6Input)
    (hL : TwistedE6RowXiCaseLInput) : TwistedE6RowXiExclusionInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk K₂ _ _ σ' hK₂ hσ' he₆ htG M hM htM eM hx φ η hη hφ
  have hσ : ∀ c, σ'.toRingHom c = c ^ 2 ^ f := hσ'
  obtain ⟨e₀⟩ := he₆
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hG₀ := commutator_pieceSpan e
  have hLG₀ := le_pieceSpan hq e
  have htN : t ∈ normalizer (pieceSpan e : Set G) :=
    mem_normalizer_iSup fun J => le_normalizer_pieceCore e hw.mem_centralizer J.1
  have h36 : 2 ^ (36 * f) ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K₂ σ'.toRingHom) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two (by omega) hK₂
      σ'.toRingHom hσ]
    obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordTwistedE6' (by omega : 1 ≤ f)).two
    rw [hr, mul_comm 36 f]
    exact Dvd.intro r rfl
  have htC : t ∉ centralizer (pieceSpan e : Set G) :=
    not_mem_centralizer_of_two_pow_dvd_quot hw.standard hw.one_le hw.card_eq e
      hw.mem_centralizer hw.orderOf_eq hG₀ e₀ h36
  have hC := odd_card_centralizer_pieceSpan hw e hLG₀ htC
  have hZ := odd_card_center_of_odd_card_centralizer hC
  have hK₂' : Nat.card K₂ = 2 ^ (2 * f) := by rw [hK₂, ← pow_mul, mul_comm]
  have hK₂2 : ringChar K₂ = 2 :=
    CFSG.LieType.Chevalley.E6SecondGraphFixed.ringChar_eq_two_of_card (by omega) hK₂'
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  obtain ⟨g₁, hg₁⟩ := hM
  set g : G := g₁⁻¹ with hgdef
  have hMg : M = CFSG.conjugate (pieceSpan e) g⁻¹ := by rw [hgdef, inv_inv]; exact hg₁
  subst hMg
  have hZM : Odd (Nat.card (center (CFSG.conjugate (pieceSpan e) g⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  obtain ⟨hx2, hηx, hfix⟩ :=
    xi_data_of_le hK₂2 (graphFixedRootGroup_E6_le_adjointGroup σ'.toRingHom) hη hx
  obtain ⟨w, hww, htw, hwq, htwM, hφw⟩ :=
    exists_partner_of_conj_eq_conj_mul hZM eM htM hx2 hηx hφ
  have hperfA := fixSubgroup_perfect_of_conj hφ (hperf f K₂ σ'.toRingHom hf hK₂ hσ η hη hx)
  have hwΛ := mem_perfectCore_of_fixSubgroup_perfect hZM eM hw.orderOf_eq htM hperfA hww htw
  have hwL : (w : G) ∈ L :=
    perfectCore_inf_centralizer_le hw.standard hOut hw.mem_centralizer hw.orderOf_eq _ hwΛ
  have hwG₀ : (w : G) ∈ pieceSpan e := hLG₀ hwL
  have hcomm : ∀ c ∈ CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G),
      c * w = w * c := fun c hc =>
    commute_partner_of_fix hZM eM htM hφ hfix hww hwq hc.1
      (mem_centralizer_singleton_iff.1 hc.2)
  have hww' : (w : G) * w = 1 := by rw [← Subgroup.coe_mul, hww, Subgroup.coe_one]
  have hout₀ := not_inner_quot_twistedE6_row hw.standard hf hw.card_eq e hw.mem_centralizer
    hw.orderOf_eq hw.inf_eq hG₀ hZ hK₂ hσ e₀ htN
  rcases inf_centralizer_eq_or_xi_twistedE6_quot hw.standard hw.card_eq e hw.mem_centralizer
      hw.orderOf_eq hw.inf_eq hZ hK₂ σ'.toRingHom hσ e₀ htN hout₀ with
    ⟨hC₀, η₀, hη₀, φ₀, hφ₀⟩ | ⟨hx₀, φ₀, η₀, hη₀, hφ₀⟩
  swap
  · exact false_of_le_of_conj_xi_twistedE6 hLG₀ hw.center_eq_bot hw.card_eq e hK₂ hσ e₀
      hw.mem_centralizer htN hη₀ hx₀ hφ₀
  have hηη₀ : η₀ = η := MulEquiv.ext fun x => Subtype.ext ((hη₀ x).trans (hη x).symm)
  rw [hηη₀] at hφ₀
  have hkG : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hw.one_le hkG hK₂
  let _ : Algebra (GaloisField 2 f) K₂ := ι.toAlgebra
  obtain ⟨-, ⟨-, hPP, -, -, hexh, hfaith, -⟩⟩ :=
    even_E6_graph_inner_coset_exhaustion f hw.one_le (GaloisField 2 f) K₂ hkG hK₂ σ'.toRingHom hσ
  have hfaith' : ∀ c ∈ graphFixedRootGroup TwistTag.E6 K₂ σ'.toRingHom,
      (∀ h ∈ graphFixedRootGroup TwistTag.E6 K₂ σ'.toRingHom, c * h * c⁻¹ = h) → c = 1 :=
    fun c hc h =>
    hfaith c (Subgroup.mem_sup_left hc) h
  have ht2 : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have htw2 : (t * w) * (t * w) = 1 := by
    calc (t * w) * (t * w) = t * ((w : G) * t) * w := by group
      _ = t * (t * w) * w := by rw [htw]
      _ = (t * t) * ((w : G) * w) := by group
      _ = 1 := by rw [ht2, hww', mul_one]
  have hgs : g⁻¹ * (t * w) * g ∈ normalizer (pieceSpan e : Set G) :=
    conj_mem_normalizer_of_mem_normalizer_conjugate_inv htwM
  have hη' : ∃ φ₂ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ'.toRingHom),
      φ₂ * normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ * φ₂⁻¹ = η := by
    rw [← normalizerQuotMulAut_conjugate e₀ hgs htwM]
    set eM' := (E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g⁻¹).symm.trans e₀
    have heM : eM = eM'.trans (eM'.symm.trans eM) := MulEquiv.ext fun x => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [heM] at hφw
    exact (exists_conj_eq_iff_trans eM' (eM'.symm.trans eM) _ η).1 ⟨φ, hφw⟩
  have hMC : CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G) ≠ L := by
    intro hCM
    have hLM : L ≤ CFSG.conjugate (pieceSpan e) g⁻¹ := fun x hx => by
      rw [← hCM] at hx
      exact hx.1
    exact false_of_le_of_conj_xi_twistedE6 hLM hw.center_eq_bot hw.card_eq e hK₂ hσ eM
      hw.mem_centralizer htM hη hx hφ
  rcases inner_or_xi_of_mem hPP hexh hfaith' hx hη e₀ htN hφ₀ hwG₀ htw2 with ⟨y, hy⟩ | ⟨φ', hφ'⟩
  · exact false_of_xi_partner_inner_twistedE6 hw hf hK₂ hσ e₀ hZ hC htN hη ⟨hC₀, φ₀, hφ₀⟩ g hMC
      hww' htw hgs hη' (mul_mem htN (le_normalizer hwG₀)) y hy
  · exact hL G L K e t f hw hf hk K₂ σ'.toRingHom hK₂ hσ e₀ htG _ ⟨g⁻¹, rfl⟩ htM eM η hη hx φ hφ w
      w.2 hwL hww' htw hwq hwΛ hcomm htwM ⟨φ, hφw⟩ htN (mul_mem htN (le_normalizer hwG₀)) hC₀ ⟨φ₀, hφ₀⟩
      ⟨φ', hφ'⟩

end RowTwistedE6

end CFSG.SeitzReduction.F4Pilot
