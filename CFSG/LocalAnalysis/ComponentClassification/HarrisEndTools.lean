module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly46e

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open Standing.Setup42

namespace HarrisEnd

variable {G : Type} [Group G] [Finite G]

@[expose] def conjEquiv (Y : Subgroup G) (c : G) : ↥Y ≃* ↥(Y.map (MulAut.conj c).toMonoidHom) :=
  equivMapOfInjective Y _ (MulAut.conj c).injective

theorem layerIn_map_conj (Y : Subgroup G) (c : G) :
    GSThmB.layerIn (Y.map (MulAut.conj c).toMonoidHom) =
      (GSThmB.layerIn Y).map (MulAut.conj c).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 (conjEquiv Y c)
  unfold GSThmB.layerIn
  rw [← h, map_map, map_map]
  congr 1

omit [Finite G] in
theorem isPGroup_quot_map_conj {Y : Subgroup G} (c : G)
    (h : IsPGroup 2 (↥Y ⧸ pPrimeCore 2 ↥Y)) :
    IsPGroup 2 (↥(Y.map (MulAut.conj c).toMonoidHom) ⧸
      pPrimeCore 2 ↥(Y.map (MulAut.conj c).toMonoidHom)) :=
  isPGroup_quot_of_mulEquiv (conjEquiv Y c) h

theorem nonempty_bar_map_conj (Y : Subgroup G) (c : G) :
    Nonempty (Bar (Y.map (MulAut.conj c).toMonoidHom) ≃* Bar Y) := by
  have hk : ¬ 2 ∣ Nat.card (conjEquiv Y c).symm.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (conjEquiv Y c).symm.injective, card_bot]
    norm_num
  exact GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective _ (conjEquiv Y c).symm.surjective hk

omit [Finite G] in
theorem map_conj_inf_centralizer' (a b c : G) :
    (centralizer ({a} : Set G) ⊓ centralizer {b}).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * a * c⁻¹} : Set G) ⊓ centralizer {c * b * c⁻¹} := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, map_conj_centralizer,
    map_conj_centralizer]

end HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace Setting46e

theorem lemma44_conj (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hs : Setting46e t L p f S w z V i j) (g : X) {σ : X}
    (hστ : σ ∈ centralizer ({g * t * g⁻¹} : Set X)) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hσt : σ ≠ g * t * g⁻¹) :
    IsPGroup 2 (↥(centralizer ({g * t * g⁻¹} : Set X) ⊓ centralizer {σ}) ⧸
        pPrimeCore 2 ↥(centralizer ({g * t * g⁻¹} : Set X) ⊓ centralizer {σ})) ∨
      Blueprint.LieModel (Bar (GSThmB.layerIn
        (centralizer ({g * t * g⁻¹} : Set X) ⊓ centralizer {σ}))) .PSL 2 p (f / 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({t} : Set X) with hH
  set σ' := g⁻¹ * σ * g with hσ'
  have hσ'H : σ' ∈ H := by
    rw [hH, mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.mp hστ
    calc g⁻¹ * σ * g * t = g⁻¹ * (σ * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * σ) * g := by rw [this]
      _ = t * (g⁻¹ * σ * g) := by group
  have hσ'2 : σ' ^ 2 = 1 := by
    rw [hσ', sq, show g⁻¹ * σ * g * (g⁻¹ * σ * g) = g⁻¹ * (σ * σ) * g by group, ← sq, hσ2]
    group
  have hz2 : IsPGroup 2 (zpowers σ') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    exact ⟨1, by rw [pow_one]; exact orderOf_eq_prime hσ'2 (fun h1 => hσ1 (by
      rw [hσ'] at h1
      calc σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group))⟩
  obtain ⟨S', hS', hσ'S'⟩ := exists_isSylowOf_ge hz2 (zpowers_le.mpr hσ'H)
  obtain ⟨h, hh, hhS⟩ := hs.sylow.exists_mem_conj hS'
  set σ'' := h⁻¹ * σ' * h with hσ''
  have hσ''S : σ'' ∈ S := (hhS σ').mp (hσ'S' (mem_zpowers σ'))
  have hσ''2 : σ'' ^ 2 = 1 := by
    rw [hσ'', sq, show h⁻¹ * σ' * h * (h⁻¹ * σ' * h) = h⁻¹ * (σ' * σ') * h by group, ← sq,
      hσ'2]
    group
  set c := g * h with hc
  have hct : c * t * c⁻¹ = g * t * g⁻¹ := by
    rw [hc, show g * h * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ by group,
      show h * t * h⁻¹ = t by rw [mem_centralizer_singleton_iff.mp hh]; group]
  have hcσ : c * σ'' * c⁻¹ = σ := by rw [hc, hσ'', hσ']; group
  have hmap : (H ⊓ centralizer {σ''}).map (MulAut.conj c).toMonoidHom =
      centralizer ({g * t * g⁻¹} : Set X) ⊓ centralizer {σ} := by
    rw [hH, HarrisEnd.map_conj_inf_centralizer', hct, hcσ]
  have hσ''1 : σ'' ≠ 1 := by
    intro h1
    apply hσ1
    rw [← hcσ, h1]
    group
  have hσ''t : σ'' ≠ t := by
    intro h1
    apply hσt
    rw [← hcσ, h1, hct]
  by_cases h2 : IsPGroup 2 (↥(H ⊓ centralizer {σ''}) ⧸ pPrimeCore 2 ↥(H ⊓ centralizer {σ''}))
  · left
    have := HarrisEnd.isPGroup_quot_map_conj c h2
    rw [hmap] at this
    exact this
  · right
    obtain ⟨k, hk, i', j', hk', -⟩ := hs.setup.lemma44b hI hKF hKC hσ''S hσ''2 hσ''1 hσ''t h2
    have hmap2 : (H ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i' * z ^ j'}).map
        (MulAut.conj k⁻¹).toMonoidHom = H ⊓ centralizer {σ''} := by
      have e1 : k⁻¹ * t * k⁻¹⁻¹ = t := by
        rw [inv_inv, show k⁻¹ * t = t * k⁻¹ from mem_centralizer_singleton_iff.mp (inv_mem hk)]
        group
      have e2 : k⁻¹ * (w ^ (orderOf w / 2) * t ^ i' * z ^ j') * k⁻¹⁻¹ = σ'' := by
        rw [← hk']
        group
      rw [hH, HarrisEnd.map_conj_inf_centralizer', e1, e2]
    have hlay : GSThmB.layerIn (H ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i' * z ^ j'}) =
        centralizerResidual L (w ^ (orderOf w / 2) * t ^ i' * z ^ j') :=
      hs.setup.pLayer_M hFC hKC i' j'
    have hall : GSThmB.layerIn (centralizer ({g * t * g⁻¹} : Set X) ⊓ centralizer {σ}) =
        ((centralizerResidual L (w ^ (orderOf w / 2) * t ^ i' * z ^ j')).map
          (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
      rw [← hmap, HarrisEnd.layerIn_map_conj, ← hmap2, HarrisEnd.layerIn_map_conj, hlay]
    rw [hall]
    obtain ⟨e₁⟩ := HarrisEnd.nonempty_bar_map_conj
      ((centralizerResidual L (w ^ (orderOf w / 2) * t ^ i' * z ^ j')).map
        (MulAut.conj k⁻¹).toMonoidHom) c
    obtain ⟨e₂⟩ := HarrisEnd.nonempty_bar_map_conj
      (centralizerResidual L (w ^ (orderOf w / 2) * t ^ i' * z ^ j')) k⁻¹
    exact lieModel_psl2_of_mulEquiv (e₁.trans e₂) (hs.setup.lieModel_bar_K hFC hKC i' j')

end Setting46e

end CFSG.ComponentClassification.HarrisLit
