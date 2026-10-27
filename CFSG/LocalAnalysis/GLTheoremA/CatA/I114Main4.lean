module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Main3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Main2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

@[expose] def HK (K B : Subgroup Y) : Subgroup (MulAut ↥K) :=
  (psiK K (NBK K B) (NBK_le_normalizer K B)).range

theorem NBK_mem_B {K B : Subgroup Y} (m : ↥(NBK K B)) : (m : Y) ∈ B :=
  (Subgroup.mem_inf.1 m.2).2

theorem NBK_mem_N {K B : Subgroup Y} (m : ↥(NBK K B)) :
    (m : Y) ∈ Subgroup.normalizer (K : Set Y) :=
  (Subgroup.mem_inf.1 m.2).1

theorem card_B_eq [Finite Y] {B K : Subgroup Y}
    (hrel : (Subgroup.normalizer (K : Set Y)).relIndex B = 3) :
    Nat.card B = 3 * (Nat.card (CBK K B) * Nat.card (HK K B)) := by
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (K : Set Y)) (K := B)
  rw [hrel] at h1
  rw [← h1]
  congr 1
  exact card_NBK_eq K B

theorem isElemAbelian_HK {B K : Subgroup Y} (hB : IsElemAbelian 3 B) :
    IsElemAbelian 3 (HK K B) := by
  apply isElemAbelian_of 3
  · intro a ha b hb
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.1 ha
    obtain ⟨n, rfl⟩ := MonoidHom.mem_range.1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_commute hB (NBK_mem_B m) (NBK_mem_B n))
  · intro a ha
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.1 ha
    rw [← map_pow]
    have h3 : m ^ 3 = 1 := Subtype.ext (by simpa using hB.2 (m : Y) (NBK_mem_B m))
    rw [h3, map_one]

theorem comm_conj_gen {g w c : Y} (hw : g * w = w * g) (hc : g * c = c * g) :
    g * (w * c * w⁻¹) = (w * c * w⁻¹) * g := by
  have hw' : g * w⁻¹ = w⁻¹ * g := by
    calc g * w⁻¹ = w⁻¹ * (w * g) * w⁻¹ := by group
      _ = w⁻¹ * (g * w) * w⁻¹ := by rw [hw]
      _ = w⁻¹ * g := by group
  calc g * (w * c * w⁻¹) = (g * w) * c * w⁻¹ := by group
    _ = (w * g) * c * w⁻¹ := by rw [hw]
    _ = w * (g * c) * w⁻¹ := by group
    _ = w * (c * g) * w⁻¹ := by rw [hc]
    _ = w * c * (g * w⁻¹) := by group
    _ = w * c * (w⁻¹ * g) := by rw [hw']
    _ = (w * c * w⁻¹) * g := by group

theorem B0_E_commute {B K : Subgroup Y} {x y : Y} (hB : IsElemAbelian 3 B) (hxB : x ∈ B)
    (hyK : y ∈ K) (hKK₂ : ElemCommute K (cj x K)) (hKK₃ : ElemCommute K (cj (x * x) K)) :
    ElemCommute (CBK K B) (Subgroup.zpowers y ⊔ (Subgroup.zpowers (x * y * x⁻¹) ⊔
      Subgroup.zpowers ((x * x) * y * (x * x)⁻¹))) := by
  have hy₁K : x * y * x⁻¹ ∈ cj x K := conj_mem_cj x hyK
  have hy₂K : (x * x) * y * (x * x)⁻¹ ∈ cj (x * x) K := conj_mem_cj (x * x) hyK
  have hB₀y : ElemCommute (CBK K B) (Subgroup.zpowers y) := by
    intro β hβ c hc
    exact ((cent_CBK hB hxB hβ).1 c (Subgroup.zpowers_le.2 hyK hc)).symm
  have hB₀y₁ : ElemCommute (CBK K B) (Subgroup.zpowers (x * y * x⁻¹)) := by
    intro β hβ c hc
    exact ((cent_CBK hB hxB hβ).2.1 c (Subgroup.zpowers_le.2 hy₁K hc)).symm
  have hB₀y₂ : ElemCommute (CBK K B) (Subgroup.zpowers ((x * x) * y * (x * x)⁻¹)) := by
    intro β hβ c hc
    exact ((cent_CBK hB hxB hβ).2.2 c (Subgroup.zpowers_le.2 hy₂K hc)).symm
  exact commutes_sup_right hB₀y (commutes_sup_right hB₀y₁ hB₀y₂)

theorem S'_invariant {B K P₀ : Subgroup Y} (hP₀n : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set Y) →
    cj b P₀ = P₀) (m : ↥(NBK K B)) :
    (P₀.subgroupOf K).map (MulEquiv.toMonoidHom (psiK K (NBK K B) (NBK_le_normalizer K B) m)) =
      P₀.subgroupOf K := by
  have hcj : cj (m : Y) P₀ = P₀ := hP₀n _ (NBK_mem_B m) (NBK_mem_N m)
  have hcj' : cj (m : Y)⁻¹ P₀ = P₀ :=
    hP₀n _ (B.inv_mem (NBK_mem_B m)) ((Subgroup.normalizer _).inv_mem (NBK_mem_N m))
  ext k
  constructor
  · rintro ⟨k', hk', rfl⟩
    have hk'' : (k' : Y) ∈ P₀ := hk'
    rw [Subgroup.mem_subgroupOf]
    change ((psiK K (NBK K B) (NBK_le_normalizer K B) m) k' : Y) ∈ P₀
    rw [psiK_apply]
    exact (conj_mem_iff_of_cj hcj).2 hk''
  · intro hk
    have hk' : (k : Y) ∈ P₀ := hk
    refine ⟨(psiK K (NBK K B) (NBK_le_normalizer K B) m⁻¹) k, ?_, ?_⟩
    · show ((psiK K (NBK K B) (NBK_le_normalizer K B) m⁻¹) k : Y) ∈ P₀
      rw [psiK_apply, Subgroup.coe_inv]
      exact (conj_mem_iff_of_cj hcj').2 hk'
    · change (psiK K (NBK K B) (NBK_le_normalizer K B) m) ((psiK K (NBK K B)
        (NBK_le_normalizer K B) m⁻¹) k) = k
      have hmm : psiK K (NBK K B) (NBK_le_normalizer K B) m *
          psiK K (NBK K B) (NBK_le_normalizer K B) m⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      calc (psiK K (NBK K B) (NBK_le_normalizer K B) m)
            ((psiK K (NBK K B) (NBK_le_normalizer K B) m⁻¹) k)
          = (psiK K (NBK K B) (NBK_le_normalizer K B) m *
              psiK K (NBK K B) (NBK_le_normalizer K B) m⁻¹) k := rfl
        _ = k := by rw [hmm, MulAut.one_apply]

end CFSG.LocalAnalysis.GLTheoremA.I114
