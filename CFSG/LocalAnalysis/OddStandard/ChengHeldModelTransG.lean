module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelSFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelTables

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.ChengHeld.M1b (evalE)

namespace GAux

variable {G : Type} [Group G]

theorem isOrbitOf_image {H K : Type} [Group H] [Group K] (φ : H → K) {Fs : List (H → H)}
    {FKs : List (K → K)} (h₁ : ∀ F ∈ Fs, ∃ FK ∈ FKs, ∀ h, φ (F h) = FK (φ h))
    (h₂ : ∀ FK ∈ FKs, ∃ F ∈ Fs, ∀ h, φ (F h) = FK (φ h)) {a : H} {O : Set H}
    (hO : IsOrbitOf Fs a O) : IsOrbitOf FKs (φ a) (φ '' O) := by
  obtain ⟨ha, hcl, hmin⟩ := hO
  refine ⟨⟨a, ha, rfl⟩, ?_, ?_⟩
  · rintro FK hFK _ ⟨y, hy, rfl⟩
    obtain ⟨F, hF, hFF⟩ := h₂ FK hFK
    exact ⟨F y, hcl F hF y hy, hFF y⟩
  · rintro P hP hPcl _ ⟨y, hy, rfl⟩
    refine hmin (φ ⁻¹' P) hP (fun F hF z hz => ?_) hy
    obtain ⟨FK, hFK, hFF⟩ := h₁ F hF
    rw [Set.mem_preimage, hFF z]
    exact hPcl FK hFK _ hz

theorem gMaps_rel {S : Subgroup G} (x : Fin 7 → ↥S) {g : G} {γ : ↥S →* ↥S}
    (hγ : ∀ s : ↥S, ((γ s : ↥S) : G) = g⁻¹ * s * g) :
    (∀ F ∈ gMaps γ x, ∃ FK ∈ gMapsG g (fun j => ((x j : ↥S) : G)),
      ∀ h, ((F h : ↥S) : G) = FK h) ∧
    ∀ FK ∈ gMapsG g (fun j => ((x j : ↥S) : G)), ∃ F ∈ gMaps γ x,
      ∀ h, ((F h : ↥S) : G) = FK h := by
  constructor
  · intro F hF
    simp only [gMaps, List.mem_cons, List.mem_map, List.mem_range] at hF
    rcases hF with rfl | ⟨j, hj, rfl⟩
    · exact ⟨_, List.mem_cons_self, hγ⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_range.2 hj)),
        fun h => rfl⟩
  · intro FK hFK
    simp only [gMapsG, List.mem_cons, List.mem_map, List.mem_range] at hFK
    rcases hFK with rfl | ⟨j, hj, rfl⟩
    · exact ⟨_, List.mem_cons_self, hγ⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_range.2 hj)),
        fun h => rfl⟩

theorem image_closure (S : Subgroup G) (U : Set ↥S) :
    Subtype.val '' ((closure U : Subgroup ↥S) : Set ↥S) =
      ((closure (Subtype.val '' U) : Subgroup G) : Set G) := by
  rw [← coe_subtype, ← coe_map, MonoidHom.map_closure]

theorem stable_of {S : Subgroup G} {g : G} {γ : ↥S →* ↥S}
    (hγ : ∀ s : ↥S, ((γ s : ↥S) : G) = g⁻¹ * s * g) (U : Set ↥S)
    (h : ∀ y ∈ closure U, γ y ∈ closure U) :
    ∀ s ∈ closure (Subtype.val '' U), g⁻¹ * s * g ∈ closure (Subtype.val '' U) := by
  intro s hs
  rw [← SetLike.mem_coe, ← image_closure] at hs ⊢
  obtain ⟨y, hy, rfl⟩ := hs
  exact ⟨γ y, h y hy, hγ y⟩

theorem coe_mem_zpowers {S : Subgroup G} (a b : ↥S) :
    (a : G) ∈ zpowers (b : G) ↔ a ∈ zpowers b := by
  have h := mem_map_iff_mem (K := zpowers b) (x := a) S.subtype_injective
  rw [MonoidHom.map_zpowers] at h
  exact h

end GAux

section Generic

variable {G : Type} [Group G]

theorem gFactsG_of {S : Subgroup G} (x : Fin 7 → ↥S) {g : G}
    (hg : ∀ s ∈ S, g⁻¹ * s * g ∈ S) {α : ℕ}
    (hG : ∀ γ : ↥S →* ↥S, GTable α γ x → GFacts α γ x)
    (hact : ∀ e ∈ gRels α,
      g⁻¹ * ((natFam x e.1 : ↥S) : G) * g = ((evalE (natFam x) e.2 : ↥S) : G)) :
    GFactsG S (fun j => ((x j : ↥S) : G)) α g := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥S →* ↥S, ∀ s : ↥S, ((γ s : ↥S) : G) = g⁻¹ * s * g :=
    ⟨{ toFun := fun s => ⟨g⁻¹ * s * g, hg s s.2⟩
       map_one' := Subtype.ext (by simp)
       map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun _ => rfl⟩
  have hF : GFacts α γ x := hG γ fun e he => Subtype.ext ((hγ _).trans (hact e he))
  have hrel := GAux.gMaps_rel x hγ
  have horb : ∀ {a : ↥S} {O : Set ↥S}, IsOrbitOf (gMaps γ x) a O →
      IsOrbitOf (gMapsG g fun j => ((x j : ↥S) : G)) (a : G) (Subtype.val '' O) :=
    fun hO => GAux.isOrbitOf_image Subtype.val hrel.1 hrel.2 hO
  refine ⟨fun s hs => ?_, ?_, fun s hs h => ?_, ?_, fun h2 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have h := congrArg Subtype.val (hF.ord3.1 ⟨s, hs⟩)
    simpa only [hγ] using h
  · obtain ⟨y, hy⟩ := hF.ord3.2
    exact ⟨y, y.2, fun e => hy (Subtype.ext ((hγ y).trans e))⟩
  · refine (GAux.coe_mem_zpowers ⟨s, hs⟩ (x 0)).2
      (hF.fixed_free _ ((GAux.coe_mem_zpowers _ (x 0)).1 ?_))
    rw [coe_mul, coe_inv, hγ]
    exact h
  · have h := GAux.stable_of hγ {x 0, x 1, x 2} hF.D_stable
    simpa only [Set.image_insert_eq, Set.image_singleton] using h
  · obtain ⟨o1, o2, o3, hnd⟩ := hF.orbits2 h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Set.image_singleton] using horb o1
    · simpa only [Set.image_insert_eq, Set.image_singleton, coe_mul] using horb o2
    · simpa only [Set.image_insert_eq, Set.image_singleton, coe_mul] using horb o3
    · simpa only [List.map_cons, List.map_nil, coe_mul] using hnd.map Subtype.val_injective
  · have h := GAux.stable_of hγ {x 0 ^ 2, x 1, x 0 * x 2} (hF.V_stable h1)
    simpa only [Set.image_insert_eq, Set.image_singleton, coe_pow, coe_mul] using h
  · have h := horb (hF.orbit4 h1)
    rw [Set.image_sdiff Subtype.val_injective, sV, GAux.image_closure] at h
    simpa only [Set.image_insert_eq, Set.image_singleton, coe_pow, coe_mul, coe_one] using h

end Generic

end CFSG.OddStandard.ChengHeld
