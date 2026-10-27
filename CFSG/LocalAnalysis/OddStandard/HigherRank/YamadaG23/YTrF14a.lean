module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrMap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrSec

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

private lemma closure_pair_map {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] (f : Γ₁ →* Γ₂)
    (x y : Γ₁) : closure ({f x, f y} : Set Γ₂) = (closure ({x, y} : Set Γ₁)).map f := by
  have h : ({f x, f y} : Set Γ₂) = f '' ({x, y} : Set Γ₁) := by
    ext z
    simp
  rw [h, ← MonoidHom.map_closure f ({x, y} : Set Γ₁)]

theorem f14a_map_iff (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (gf.map f).F14a ↔ gf.F14a := by
  have hS : (gf.map f).S = gf.S.map f := GFrame.map_S f gf
  have hZ : (gf.map f).Z = gf.Z.map f := GFrame.map_Z f gf
  have hA : (gf.map f).A = gf.A.map f := GFrame.map_A f gf
  have hcl1 : closure ({(gf.map f).a₁, (gf.map f).b₁} : Set Γ₂) =
      (closure ({(gf.a₁), (gf.b₁)} : Set Γ₁)).map f :=
    closure_pair_map f gf.a₁ gf.b₁
  have hcl2 : closure ({(gf.map f).a₂, (gf.map f).b₂} : Set Γ₂) =
      (closure ({(gf.a₂), (gf.b₂)} : Set Γ₁)).map f :=
    closure_pair_map f gf.a₂ gf.b₂
  have hclb : closure ({(gf.map f).b₁, (gf.map f).b₂} : Set Γ₂) =
      (closure ({(gf.b₁), (gf.b₂)} : Set Γ₁)).map f :=
    closure_pair_map f gf.b₁ gf.b₂
  have h_cen : (cen (gf.map f).S = (gf.map f).Z) ↔ (cen gf.S = gf.Z) := by
    rw [hS, hZ, cen_map hf gf.S]
    exact (Subgroup.map_injective hf).eq_iff
  have h_zSeries : (zSeries 2 (gf.map f).S = ⁅(gf.map f).S, (gf.map f).S⁆) ↔
      (zSeries 2 gf.S = ⁅gf.S, gf.S⁆) := by
    rw [hS, zSeries_map hf 2 gf.S, ← Subgroup.map_commutator gf.S gf.S f]
    exact (Subgroup.map_injective hf).eq_iff
  have h_commut : (⁅(gf.map f).S, (gf.map f).S⁆ =
        closure ({(gf.map f).b₁, (gf.map f).b₂} : Set Γ₂)) ↔
      (⁅gf.S, gf.S⁆ = closure ({(gf.b₁), (gf.b₂)} : Set Γ₁)) := by
    rw [hS, hclb, ← Subgroup.map_commutator gf.S gf.S f]
    exact (Subgroup.map_injective hf).eq_iff
  have h_sec : SecProp (gf.map f).S (zSeries 2 (gf.map f).S) (fun Y _ _ _ => IsE 3 Y) ↔
      SecProp gf.S (zSeries 2 gf.S) (fun Y _ _ _ => IsE 3 Y) := by
    rw [hS, zSeries_map hf 2 gf.S]
    exact secProp_map_type hf gf.S (zSeries 2 gf.S) (fun Y => IsE 3 Y)
      (fun Y Y' _ _ e => isE_equiv e 3)
  have h_q8a : Nonempty (↥(closure ({(gf.map f).a₁, (gf.map f).b₁} : Set Γ₂)) ≃*
        QuaternionGroup 2) ↔
      Nonempty (↥(closure ({(gf.a₁), (gf.b₁)} : Set Γ₁)) ≃* QuaternionGroup 2) := by
    rw [hcl1]
    exact nonempty_equiv_map hf (closure ({(gf.a₁), (gf.b₁)} : Set Γ₁)) (QuaternionGroup 2)
  have h_q8b : Nonempty (↥(closure ({(gf.map f).a₂, (gf.map f).b₂} : Set Γ₂)) ≃*
        QuaternionGroup 2) ↔
      Nonempty (↥(closure ({(gf.a₂), (gf.b₂)} : Set Γ₁)) ≃* QuaternionGroup 2) := by
    rw [hcl2]
    exact nonempty_equiv_map hf (closure ({(gf.a₂), (gf.b₂)} : Set Γ₁)) (QuaternionGroup 2)
  have hcomm : (∀ u ∈ (closure ({(gf.map f).a₁, (gf.map f).b₁} : Set Γ₂)),
        ∀ v ∈ (closure ({(gf.map f).a₂, (gf.map f).b₂} : Set Γ₂)), u * v = v * u) ↔
      (∀ u ∈ (closure ({(gf.a₁), (gf.b₁)} : Set Γ₁)),
        ∀ v ∈ (closure ({(gf.a₂), (gf.b₂)} : Set Γ₁)), u * v = v * u) := by
    constructor
    · intro h u hu v hv
      have hmem1 : f u ∈ closure ({(gf.map f).a₁, (gf.map f).b₁} : Set Γ₂) := by
        rw [hcl1]
        exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      have hmem2 : f v ∈ closure ({(gf.map f).a₂, (gf.map f).b₂} : Set Γ₂) := by
        rw [hcl2]
        exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
      exact hf (by simpa only [map_mul] using h (f u) hmem1 (f v) hmem2)
    · intro h u hu v hv
      rw [hcl1] at hu
      rw [hcl2] at hv
      obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
      obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
      rw [← map_mul, ← map_mul, h u₀ hu₀ v₀ hv₀]
  have hsup : (closure ({(gf.map f).a₁, (gf.map f).b₁} : Set Γ₂) ⊔
        closure ({(gf.map f).a₂, (gf.map f).b₂} : Set Γ₂) = (gf.map f).A) ↔
      (closure ({(gf.a₁), (gf.b₁)} : Set Γ₁) ⊔
        closure ({(gf.a₂), (gf.b₂)} : Set Γ₁) = gf.A) := by
    rw [hcl1, hcl2, hA,
      ← Subgroup.map_sup (closure ({(gf.a₁), (gf.b₁)} : Set Γ₁))
        (closure ({(gf.a₂), (gf.b₂)} : Set Γ₁)) f]
    exact (Subgroup.map_injective hf).eq_iff
  have hinf : (closure ({(gf.map f).a₁, (gf.map f).b₁} : Set Γ₂) ⊓
        closure ({(gf.map f).a₂, (gf.map f).b₂} : Set Γ₂) = (gf.map f).Z) ↔
      (closure ({(gf.a₁), (gf.b₁)} : Set Γ₁) ⊓
        closure ({(gf.a₂), (gf.b₂)} : Set Γ₁) = gf.Z) := by
    rw [hcl1, hcl2, hZ,
      ← Subgroup.map_inf_eq (closure ({(gf.a₁), (gf.b₁)} : Set Γ₁))
        (closure ({(gf.a₂), (gf.b₂)} : Set Γ₁)) f hf]
    exact (Subgroup.map_injective hf).eq_iff
  have hext : IsExtraspecialTwo 2 (gf.map f).A ↔ IsExtraspecialTwo 2 gf.A := by
    rw [hA]
    exact isExtraspecialTwo_map hf 2 gf.A
  have hall : (∀ X : Subgroup Γ₂, X ≤ (gf.map f).S → IsExtraspecialTwo 2 X →
        X = (gf.map f).A) ↔
      (∀ X : Subgroup Γ₁, X ≤ gf.S → IsExtraspecialTwo 2 X → X = gf.A) := by
    constructor
    · intro h X hXle hX
      have hXS : X.map f ≤ (gf.map f).S := by
        rw [hS]
        exact Subgroup.map_mono hXle
      have hext' : IsExtraspecialTwo 2 (X.map f) := (isExtraspecialTwo_map hf 2 X).mpr hX
      have hres := h (X.map f) hXS hext'
      rw [hA] at hres
      exact (Subgroup.map_injective hf).eq_iff.mp hres
    · intro h X hXS hX
      rw [hS] at hXS
      obtain ⟨X₁, hX₁le, hX₁eq⟩ := exists_eq_map_of_le hf (V := gf.S) hXS
      have hX' : IsExtraspecialTwo 2 X₁ := by
        rw [← isExtraspecialTwo_map hf 2 X₁, hX₁eq]
        exact hX
      rw [← hX₁eq, h X₁ hX₁le hX', hA]
  unfold GFrame.F14a
  exact and_congr
    (and_congr h_cen (and_congr h_zSeries (and_congr h_commut h_sec)))
    (and_congr h_q8a (and_congr h_q8b (and_congr hcomm
      (and_congr hsup (and_congr hinf (and_congr hext hall))))))

end CFSG.OddStandard.HigherRank.YamadaG23