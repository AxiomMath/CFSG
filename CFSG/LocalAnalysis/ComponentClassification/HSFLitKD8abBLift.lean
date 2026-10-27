module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Tower
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8abB

variable {X : Type} [Group X]

@[expose] def ActsAs (K : Subgroup X) (g h : X) : Prop := ∀ r ∈ K, g * r * g⁻¹ = h * r * h⁻¹

theorem conj_mem_of_mem_normalizer {g : X} {K : Subgroup X} (hg : g ∈ normalizer (K : Set X))
    {r : X} (hr : r ∈ K) : g * r * g⁻¹ ∈ K := (mem_normalizer_iff.mp hg r).mp hr

theorem conj_inv_mem_of_mem_normalizer {g : X} {K : Subgroup X}
    (hg : g ∈ normalizer (K : Set X)) {r : X} (hr : r ∈ K) : g⁻¹ * r * g ∈ K := by
  have := conj_mem_of_mem_normalizer (inv_mem hg) hr
  rwa [inv_inv] at this

theorem ActsAs.mul {K : Subgroup X} {g g' h h' : X} (hh' : h' ∈ normalizer (K : Set X))
    (hg : ActsAs K g h) (hg' : ActsAs K g' h') : ActsAs K (g * g') (h * h') := by
  intro r hr
  have e1 : g * g' * r * (g * g')⁻¹ = g * (g' * r * g'⁻¹) * g⁻¹ := by group
  rw [e1, hg' r hr, hg _ (conj_mem_of_mem_normalizer hh' hr)]
  group

theorem ActsAs.inv {K : Subgroup X} {g h : X} (hh : h ∈ normalizer (K : Set X))
    (hg : ActsAs K g h) : ActsAs K g⁻¹ h⁻¹ := by
  intro r hr
  have h1 := hg _ (conj_inv_mem_of_mem_normalizer hh hr)
  rw [show h * (h⁻¹ * r * h) * h⁻¹ = r by group] at h1
  calc g⁻¹ * r * g⁻¹⁻¹ = g⁻¹ * (g * (h⁻¹ * r * h) * g⁻¹) * g := by rw [h1]; group
    _ = h⁻¹ * r * h⁻¹⁻¹ := by group

theorem ActsAs.refl (K : Subgroup X) (g : X) : ActsAs K g g := fun _ _ => rfl

@[expose] def actSub (W H K : Subgroup X) (hHK : H ≤ normalizer (K : Set X)) : Subgroup X where
  carrier := {w | w ∈ W ∧ ∃ h ∈ H, ActsAs K w h}
  mul_mem' := by
    rintro a b ⟨haW, h, hh, ha⟩ ⟨hbW, h', hh', hb⟩
    exact ⟨mul_mem haW hbW, h * h', mul_mem hh hh', ha.mul (hHK hh') hb⟩
  one_mem' := ⟨one_mem W, 1, one_mem H, fun r _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haW, h, hh, ha⟩
    exact ⟨inv_mem haW, h⁻¹, inv_mem hh, ha.inv (hHK hh)⟩

variable [Finite X]

theorem exists_actsAs {K H : Subgroup X} {g₀ : X} (hH : IsPGroup 2 H)
    (hHK : H ≤ normalizer (K : Set X)) (hg₀K : g₀ ∈ normalizer (K : Set X))
    (h2 : ∀ h ∈ H, ∃ h' ∈ H, ActsAs K (g₀ * h * g₀⁻¹) h')
    (h3 : ∃ h₀ ∈ H, ActsAs K (g₀ * g₀) h₀) (h4 : ∀ h ∈ H, ¬ ActsAs K g₀ h) :
    ∃ P : Subgroup X, IsPGroup 2 P ∧ H ≤ P ∧ P ≤ H ⊔ zpowers g₀ ∧ ∃ c ∈ P, ActsAs K c g₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := H ⊔ zpowers g₀ with hW
  set W₁ := actSub W H K hHK with hW₁
  have hg₀W : g₀ ∈ W := mem_sup_right (mem_zpowers g₀)
  have hW₁W : W₁ ≤ W := fun _ hx => hx.1
  have hHW₁ : H ≤ W₁ := fun h hh => ⟨mem_sup_left hh, h, hh, ActsAs.refl K h⟩
  have hg₀W₁ : g₀ ∉ W₁ := fun ⟨_, h, hh, hg⟩ => h4 h hh hg
  have hn : ∀ w ∈ W₁, g₀ * w * g₀⁻¹ ∈ W₁ := by
    rintro w ⟨hwW, h, hh, hw⟩
    refine ⟨mul_mem (mul_mem hg₀W hwW) (inv_mem hg₀W), ?_⟩
    obtain ⟨h', hh', hact⟩ := h2 h hh
    refine ⟨h', hh', fun r hr => ?_⟩
    have hr' := conj_inv_mem_of_mem_normalizer hg₀K hr
    calc g₀ * w * g₀⁻¹ * r * (g₀ * w * g₀⁻¹)⁻¹ = g₀ * (w * (g₀⁻¹ * r * g₀) * w⁻¹) * g₀⁻¹ := by
          group
      _ = g₀ * (h * (g₀⁻¹ * r * g₀) * h⁻¹) * g₀⁻¹ := by rw [hw _ hr']
      _ = g₀ * h * g₀⁻¹ * r * (g₀ * h * g₀⁻¹)⁻¹ := by group
      _ = h' * r * h'⁻¹ := hact r hr
  have he2 : g₀ * g₀ ∈ W₁ := by
    obtain ⟨h₀, hh₀, hact⟩ := h3
    exact ⟨mul_mem hg₀W hg₀W, h₀, hh₀, hact⟩
  have hmem : ∀ x ∈ W, x ∈ W₁ ∨ g₀⁻¹ * x ∈ W₁ := by
    intro x hx
    refine Sec8.mem_or_mem_of_mem_sup he2 hn ?_
    exact (sup_le (hHW₁.trans le_sup_left) (zpowers_le.mpr (mem_sup_right (mem_zpowers g₀))))
      hx
  have hidx : W₁.relIndex W = 2 := by
    rw [relIndex, index_eq_two_iff]
    refine ⟨⟨g₀, hg₀W⟩, fun b => ?_⟩
    have hb := b.2
    by_cases hbW : (b : X) ∈ W₁
    · have hbg : (b : X) * g₀ ∉ W₁ := fun h => hg₀W₁ (by
        have := mul_mem (inv_mem hbW) h
        rwa [inv_mul_cancel_left] at this)
      exact Or.inr ⟨hbW, hbg⟩
    · have h1 := (hmem _ hb).resolve_left hbW
      have hbg : (b : X) * g₀ ∈ W₁ := by
        have := mul_mem (hn _ h1) he2
        rwa [show g₀ * (g₀⁻¹ * (b : X)) * g₀⁻¹ * (g₀ * g₀) = (b : X) * g₀ by group] at this
      exact Or.inl ⟨hbg, hbW⟩
  obtain ⟨Q, hQ⟩ := (hH.comap_subtype (K := W)).exists_le_sylow
  set P := (Q : Subgroup W).map W.subtype with hP
  have hPp : IsPGroup 2 P := Q.isPGroup'.map _
  have hPW : P ≤ W := map_subtype_le _
  have hHP : H ≤ P := fun h hh => ⟨⟨h, mem_sup_left hh⟩, hQ hh, rfl⟩
  have hnot : ¬ P ≤ W₁ := by
    intro hle
    have hmul := relIndex_mul_relIndex P W₁ W hle hW₁W
    rw [hidx] at hmul
    have hdvd : 2 ∣ P.relIndex W := ⟨_, hmul.symm.trans (mul_comm _ _)⟩
    have hPQ : P.relIndex W = (Q : Subgroup W).index := by
      rw [relIndex, hP, subgroupOf, comap_map_eq_self_of_injective W.subtype_injective]
    rw [hPQ] at hdvd
    exact Q.not_dvd_index hdvd
  obtain ⟨c₁, hc₁P, hc₁W₁⟩ := Set.not_subset.mp hnot
  obtain ⟨_, h, hh, hact⟩ := (hmem c₁ (hPW hc₁P)).resolve_left hc₁W₁
  refine ⟨P, hPp, hHP, hPW, c₁ * h⁻¹, mul_mem hc₁P (inv_mem (hHP hh)), fun r hr => ?_⟩
  have hr' := conj_inv_mem_of_mem_normalizer (hHK hh) hr
  have := hact _ hr'
  calc c₁ * h⁻¹ * r * (c₁ * h⁻¹)⁻¹ = g₀ * (g₀⁻¹ * c₁ * (h⁻¹ * r * h) * (g₀⁻¹ * c₁)⁻¹) * g₀⁻¹ := by
        group
    _ = g₀ * (h * (h⁻¹ * r * h) * h⁻¹) * g₀⁻¹ := by rw [this]
    _ = g₀ * r * g₀⁻¹ := by group

end KD8abB

end CFSG.ComponentClassification.HSFLit
