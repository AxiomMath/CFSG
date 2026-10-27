module

public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.Assembly.LowTwoRank

noncomputable def derivedCentralQuotientEquiv' {M M' : Type} [Group M] [Group M'] (f : M →* M')
    (hf : Function.Injective f) {H : Subgroup M} {H' : Subgroup M'} (h : H.map f = H') :
    DerivedCentralQuotient H ≃* DerivedCentralQuotient H' := by
  have hC : (⁅H, H⁆).map f = ⁅H', H'⁆ := by rw [Subgroup.map_commutator, h]
  let eC : ↥⁅H, H⁆ ≃* ↥⁅H', H'⁆ :=
    ((⁅H, H⁆).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hC)
  exact QuotientGroup.congr _ _ eC (Subgroup.map_center_eq eC)

section Twisted

theorem map_twistedFixedGroup_eq {t : TwistTag} {K K' : Type} [Field K] [Field K']
    (φ : K ≃+* K') (σ : K →+* K) (σ' : K' →+* K') (h : ∀ c, σ' (φ c) = φ (σ c)) :
    (twistedFixedGroup t K σ).map (baseChangeGL (φ : K →+* K')) = twistedFixedGroup t K' σ' := by
  have hcomp : (φ : K →+* K').comp σ = σ'.comp (φ : K →+* K') :=
    RingHom.ext fun c => (h c).symm
  have hadj := CFSG.TauCetiBridge.map_baseChangeGL_adjointGroup_eq (τ := t.tag) φ
  ext g'
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hadj]
      exact ⟨g, hg.1, rfl⟩
    · show twistHom t K' σ' (baseChangeGL (φ : K →+* K') g) = baseChangeGL (φ : K →+* K') g
      rw [twistHom_baseChangeGL (φ : K →+* K') hcomp]
      have hF : twistHom t K σ g = g := hg.2
      rw [hF]
  · intro hg'
    have h1 : g' ∈ (adjointGroup t.tag K).map (baseChangeGL (φ : K →+* K')) := by
      rw [hadj]
      exact hg'.1
    obtain ⟨g, hg, rfl⟩ := h1
    refine ⟨g, ⟨hg, ?_⟩, rfl⟩
    have hF : twistHom t K' σ' (baseChangeGL (φ : K →+* K') g) =
        baseChangeGL (φ : K →+* K') g := hg'.2
    rw [twistHom_baseChangeGL (φ : K →+* K') hcomp] at hF
    exact baseChangeGL_injective (φ : K →+* K') hF

end Twisted

theorem twistedE6_model_data {G : Type} [Group G] (h : LieModel G .twistedE6 0 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 1) ^ TwistTag.E6.order ∧
      ∃ σ : K →+* K, (∀ c, σ c = c ^ (2 ^ 1)) ∧
        Nonempty (G ≃* DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ)) := by
  rcases h with ⟨ht, -⟩ | ⟨-, -, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact hm
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

@[expose] def E6TwoUnique : Prop :=
  ∀ (X Y : Type) [Group X] [Group Y], LieModel X .twistedE6 0 2 1 →
    LieModel Y .twistedE6 0 2 1 → Nonempty (X ≃* Y)

theorem lieModel_twistedE6_two_unique
    {X Y : Type} [Group X] [Group Y]
    (hX : LieModel X .twistedE6 0 2 1) (hY : LieModel Y .twistedE6 0 2 1) :
    Nonempty (X ≃* Y) := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨eX⟩⟩ := twistedE6_model_data hX
  obtain ⟨K', _, _, hK', σ', hσ', ⟨eY⟩⟩ := twistedE6_model_data hY
  have : Fintype K := Fintype.ofFinite K
  have : Fintype K' := Fintype.ofFinite K'
  have hc : Fintype.card K = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hK']
  let φ : K ≃+* K' := FiniteField.ringEquivOfCardEq hc
  have hφ : ∀ c, σ' (φ c) = φ (σ c) := fun c => by
    rw [hσ', hσ, map_pow]
  have hmap := map_twistedFixedGroup_eq (t := TwistTag.E6) φ σ σ' hφ
  exact ⟨eX.trans ((derivedCentralQuotientEquiv' _
    (baseChangeGL_injective (φ : K →+* K')) hmap).trans eY.symm)⟩

theorem e6TwoUnique :
    E6TwoUnique :=
  fun _ _ _ _ hX hY => lieModel_twistedE6_two_unique hX hY

end CFSG.EvenSporadicStandard.Induction
