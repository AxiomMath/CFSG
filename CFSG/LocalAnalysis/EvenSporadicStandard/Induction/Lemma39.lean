module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma39

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N L K : Subgroup H} {t u : H}

theorem SolomonSettingQ.toHypQ (S : SolomonSettingQ H N L K t u) (hne : (vPairs L K u).Nonempty)
    (hfus : Sol78Fusion39 L K u) (hgen : Sol78Generate L K u) : SolomonHypQ H N L K t u := by
  have hK : ∀ g ∈ centralizer ({u} : Set H), g * u * g⁻¹ = u ∧ K.map (conjHom g) = K := by
    intro g hg
    have hug : g * u * g⁻¹ = u := by
      have := mem_centralizer_singleton_iff.1 hg
      rw [this]
      group
    refine ⟨hug, ?_⟩
    have h := componentProduct_conj K u g
    rw [hug, ← S.hyp35] at h
    exact h.symm
  have h1 : ∀ g ∈ centralizer ({u} : Set H), ∀ w ∈ vPairs L K u, g * w * g⁻¹ ∈ vPairs L K u := by
    intro g hg w hw
    obtain ⟨v, hv, rfl, l, hl, hlw⟩ := hw
    obtain ⟨hug, hKg⟩ := hK g hg
    obtain ⟨c, hc, hcv⟩ := hfus v hv g hg
    have hcu : c * u * c⁻¹ = u := by
      have := mem_centralizer_singleton_iff.1 hc.2
      rw [this]
      group
    have hgv : g * (u * v) * g⁻¹ = u * (g * v * g⁻¹) := by
      calc g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
        _ = u * (g * v * g⁻¹) := by rw [hug]
    refine ⟨g * v * g⁻¹, vMaximal_conj hKg hug hv, hgv, c * l, mul_mem hc.1 hl, ?_⟩
    calc c * l * u * (c * l)⁻¹ = c * (l * u * l⁻¹) * c⁻¹ := by group
      _ = c * (u * v) * c⁻¹ := by rw [hlw]
      _ = (c * u * c⁻¹) * (c * v * c⁻¹) := by group
      _ = u * (c * v * c⁻¹) := by rw [hcu]
      _ = u * (g * v * g⁻¹) := by rw [hcv]
      _ = g * (u * v) * g⁻¹ := hgv.symm
  refine ⟨S, h1, ?_⟩
  intro g hg
  obtain ⟨w, hw⟩ := hne
  obtain ⟨hug, hKg⟩ := hK g hg
  have hw' := h1 g hg w hw
  have hw0 := hw
  obtain ⟨-, -, -, l, hl, hlw⟩ := hw
  obtain ⟨-, -, -, l', hl', hlw'⟩ := hw'
  have hL1 := hgen l hl (by rw [hlw]; exact hw0)
  have hL2 := hgen l' hl' (by rw [hlw']; exact h1 g hg w hw0)
  have hcp1 : componentProduct K w = K.map (conjHom l) := by
    rw [← hlw, componentProduct_conj K u l, ← S.hyp35]
  have hcp2 : componentProduct K (g * w * g⁻¹) = K.map (conjHom l') := by
    rw [← hlw', componentProduct_conj K u l', ← S.hyp35]
  have e : (K.map (conjHom l)).map (conjHom g) = K.map (conjHom l') := by
    rw [← hcp1, ← componentProduct_conj, hcp2]
  have hL : L.map (conjHom g) = L := by
    calc L.map (conjHom g) = (K ⊔ K.map (conjHom l)).map (conjHom g) := by rw [hL1]
      _ = K.map (conjHom g) ⊔ (K.map (conjHom l)).map (conjHom g) := Subgroup.map_sup _ _ _
      _ = K ⊔ K.map (conjHom l') := by rw [hKg, e]
      _ = L := hL2
  refine mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · have : g * h * g⁻¹ ∈ L.map (conjHom g) := Subgroup.mem_map_of_mem (conjHom g) hh
    rwa [hL] at this
  · have : g * h * g⁻¹ ∈ L.map (conjHom g) := by rwa [hL]
    obtain ⟨h₀, hh₀, he⟩ := this
    have : h₀ = h := conjHom_injective g (by simpa [conjHom_apply] using he)
    exact this ▸ hh₀

@[expose] def Sol78Local39Q (s : TauCeti.SporadicName) (P : PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), OddCover s L →
    SolomonSettingQ H N L K t u → P H L K u →
      (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u

end CFSG.EvenSporadicStandard.Induction
