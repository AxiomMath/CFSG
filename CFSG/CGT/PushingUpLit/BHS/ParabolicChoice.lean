module

public import CFSG.CGT.PushingUpLit.BHS.CStar
public import CFSG.CGT.PushingUpLit.BHS.SL2Facts
public import CFSG.CGT.PushingUpLit.BHS.Defs

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_minimal_not_le {S Y M : Subgroup Γ} (hSY : S ≤ Y) (hY : ¬ Y ≤ M) :
    ∃ P : Subgroup Γ, S ≤ P ∧ P ≤ Y ∧ ¬ P ≤ M ∧
      ∀ P' : Subgroup Γ, S ≤ P' → P' < P → P' ≤ M := by
  obtain ⟨P, hP⟩ := (Set.toFinite {P : Subgroup Γ | S ≤ P ∧ P ≤ Y ∧ ¬ P ≤ M}).exists_minimal
    ⟨Y, hSY, le_rfl, hY⟩
  refine ⟨P, hP.prop.1, hP.prop.2.1, hP.prop.2.2, fun P' hSP' hlt => ?_⟩
  by_contra hP'M
  exact absurd (hP.2 ⟨hSP', hlt.le.trans hP.prop.2.1, hP'M⟩ hlt.le) (not_le_of_gt hlt)

omit [Finite Γ] in
theorem isSylowTwoOf_of_le {S M J : Subgroup Γ} (hS : IsSylowTwoOf S J) (hSM : S ≤ M)
    (hMJ : M ≤ J) : IsSylowTwoOf S M :=
  ⟨hSM, hS.2.1, fun hd => hS.2.2 (hd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex S M J hSM
    hMJ)))⟩

section SL2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G T V : Subgroup Γ}

omit [Finite Γ] [Finite F] [CharP F 2] in
theorem le_normalizer_inf_centralizer (hVG : G ≤ Subgroup.normalizer (V : Set Γ)) :
    G ≤ Subgroup.normalizer ((G ⊓ Subgroup.centralizer (V : Set Γ) : Subgroup Γ) : Set Γ) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hVG hg⟩

omit [Finite F] [CharP F 2] in
theorem mem_cStarIn_of_map_mem_normalizer (hT : IsSylowTwoOf T G) (hT0 : T ≠ ⊥)
    (hVG : G ≤ Subgroup.normalizer (V : Set Γ))
    (hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ cStarIn G T)
    (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    {g : Γ} (hg : g ∈ G)
    (hgn : α ⟨g, hg⟩ ∈ Subgroup.normalizer (((T.subgroupOf G).map α : Subgroup _) : Set _)) :
    g ∈ cStarIn G T := by
  classical
  set K : Subgroup Γ := G ⊓ Subgroup.centralizer (V : Set Γ) with hK
  have hKG : K ≤ G := inf_le_left
  have hGK : G ≤ Subgroup.normalizer (K : Set Γ) := le_normalizer_inf_centralizer hVG
  have hTK : T ≤ Subgroup.normalizer (K : Set Γ) := hT.1.trans hGK
  have hker : ∀ (x : Γ) (hx : x ∈ G), α ⟨x, hx⟩ = 1 ↔ x ∈ K := by
    intro x hx
    rw [← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  set T' : Subgroup Γ := T ⊔ K with hT'
  have hT'G : T' ≤ G := sup_le hT.1 hKG
  have hT'mul : ((T' : Subgroup Γ) : Set Γ) = (T : Set Γ) * (K : Set Γ) :=
    Subgroup.coe_mul_of_left_le_normalizer_right T K hTK
  have hcl : ∀ (x : Γ) (hx : x ∈ G), α ⟨x, hx⟩ ∈
      Subgroup.normalizer (((T.subgroupOf G).map α : Subgroup _) : Set _) →
      ∀ y ∈ T', x * y * x⁻¹ ∈ T' := by
    intro x hx hxn y hy
    have hy' : y ∈ ((T' : Subgroup Γ) : Set Γ) := hy
    rw [hT'mul] at hy'
    obtain ⟨t, ht, k, hk, rfl⟩ := hy'
    have htG : t ∈ G := hT.1 ht
    have hkG : k ∈ G := hKG hk
    have hxkx : x * k * x⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hGK hx) k).mp hk
      exact this
    have hxtx : x * t * x⁻¹ ∈ T' := by
      have hxtxG : x * t * x⁻¹ ∈ G := G.mul_mem (G.mul_mem hx htG) (G.inv_mem hx)
      have himg : α ⟨t, htG⟩ ∈ ((T.subgroupOf G).map α : Subgroup _) :=
        ⟨⟨t, htG⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp hxn (α ⟨t, htG⟩)).mp himg
      obtain ⟨u, hu, hu'⟩ := h1
      have hu2 : (u : Γ) ∈ T := Subgroup.mem_subgroupOf.mp hu
      have heq : α u = α ⟨x * t * x⁻¹, hxtxG⟩ := by
        rw [hu']
        have e : (⟨x * t * x⁻¹, hxtxG⟩ : G) = ⟨x, hx⟩ * ⟨t, htG⟩ * ⟨x, hx⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
      have hdiv : (u : Γ)⁻¹ * (x * t * x⁻¹) ∈ K := by
        rw [← hker _ (G.mul_mem (G.inv_mem u.2) hxtxG)]
        have : α (u⁻¹ * ⟨x * t * x⁻¹, hxtxG⟩) = 1 := by
          rw [map_mul, map_inv, heq, inv_mul_cancel]
        exact this
      have : x * t * x⁻¹ = (u : Γ) * ((u : Γ)⁻¹ * (x * t * x⁻¹)) := by group
      rw [this]
      exact T'.mul_mem (Subgroup.mem_sup_left hu2) (Subgroup.mem_sup_right hdiv)
    have : x * (t * k) * x⁻¹ = (x * t * x⁻¹) * (x * k * x⁻¹) := by group
    rw [this]
    exact T'.mul_mem hxtx (Subgroup.mem_sup_right hxkx)
  have hnormT' : g ∈ Subgroup.normalizer (T' : Set Γ) := by
    have hgn' : α ⟨g⁻¹, G.inv_mem hg⟩ ∈
        Subgroup.normalizer (((T.subgroupOf G).map α : Subgroup _) : Set _) := by
      have e : α ⟨g⁻¹, G.inv_mem hg⟩ = (α ⟨g, hg⟩)⁻¹ := by rw [← map_inv]; rfl
      rw [e]
      exact inv_mem hgn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hcl g hg hgn y, fun hy => ?_⟩
    have := hcl g⁻¹ (G.inv_mem hg) hgn' _ hy
    simpa [mul_assoc] using this
  have hH : IsSylowTwoOf T T' := isSylowTwoOf_of_le hT le_sup_left hT'G
  have hfr := B6.frattini_two (H := G ⊓ Subgroup.normalizer (T' : Set Γ)) (N := T') (S := T)
    (le_inf hT'G Subgroup.le_normalizer) inf_le_right hH
  have hgmem : g ∈ G ⊓ Subgroup.normalizer (T' : Set Γ) := ⟨hg, hnormT'⟩
  have hgfr := hfr hgmem
  have hTC : T ≤ cStarIn G T :=
    fun t ht => inf_normalizer_le_cStarIn hT.2.1 hT0 ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  have hT'C : T' ≤ cStarIn G T := sup_le hTC hC
  have hHC : (G ⊓ Subgroup.normalizer (T' : Set Γ)) ⊓ Subgroup.normalizer (T : Set Γ) ≤
      cStarIn G T := fun x hx => inf_normalizer_le_cStarIn hT.2.1 hT0 ⟨hx.1.1, hx.2⟩
  have hsup : T' ⊔ ((G ⊓ Subgroup.normalizer (T' : Set Γ)) ⊓ Subgroup.normalizer (T : Set Γ)) ≤
      cStarIn G T := sup_le hT'C hHC
  exact hsup hgfr

omit [Finite Γ] [Finite F] [CharP F 2] in
theorem map_eq_one_iff_centralizer (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G) {x : Γ} (hx : x ∈ G) :
    α ⟨x, hx⟩ = 1 ↔ x ∈ Subgroup.centralizer (V : Set Γ) := by
  rw [← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]

theorem map_eq_top_of_not_le_cStarIn (hT : IsSylowTwoOf T G) (hT0 : T ≠ ⊥)
    (hVG : G ≤ Subgroup.normalizer (V : Set Γ))
    (hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ cStarIn G T)
    (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    {X : Subgroup Γ} (hTX : T ≤ X ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ))) (hXG : X ≤ G)
    (hX : ¬ X ≤ cStarIn G T) :
    (X.subgroupOf G).map α = ⊤ := by
  obtain ⟨ℓ, hℓ⟩ := exists_rootGrp_eq_map_of_isSylowTwoOf hT α hα
  have hle : rootGrp ℓ ≤ (X.subgroupOf G).map α := by
    rw [← hℓ]
    rintro _ ⟨t, ht, rfl⟩
    have htT : (t : Γ) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hmem : (t : Γ) ∈ ((X ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) : Subgroup Γ) : Set Γ) :=
      hTX htT
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X (G ⊓ Subgroup.centralizer (V : Set Γ))
      (hXG.trans (le_normalizer_inf_centralizer hVG))] at hmem
    obtain ⟨x, hx, k, hk, hxk⟩ := hmem
    have hxG : x ∈ G := hXG hx
    have hkα : α ⟨k, hk.1⟩ = 1 := (map_eq_one_iff_centralizer α hαk hk.1).mpr hk.2
    refine ⟨⟨x, hxG⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
    have e : t = ⟨x, hxG⟩ * ⟨k, hk.1⟩ := Subtype.ext hxk.symm
    rw [e, map_mul, hkα, mul_one]
  refine eq_top_of_rootGrp_le hle ?_
  by_contra hcon
  push Not at hcon
  apply hX
  intro x hx
  have hxG : x ∈ G := hXG hx
  have hmem : α ⟨x, hxG⟩ ∈ (X.subgroupOf G).map α :=
    ⟨⟨x, hxG⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  refine mem_cStarIn_of_map_mem_normalizer hT hT0 hVG hC α hαk hxG ?_
  rw [hℓ, mem_normalizer_rootGrp_iff]
  exact hcon _ hmem

end SL2

omit [Finite Γ] in
theorem le_cStarIn_self [Finite Γ] {G T : Subgroup Γ} (hTG : T ≤ G) (hT2 : IsPGroup 2 T)
    (hT0 : T ≠ ⊥) : T ≤ cStarIn G T :=
  fun _ ht => inf_normalizer_le_cStarIn hT2 hT0 ⟨hTG ht, Subgroup.le_normalizer ht⟩

theorem isMinParabolic2_of_minimal {G T P : Subgroup Γ} (hT : IsSylowTwoOf T G) (hT0 : T ≠ ⊥)
    (hTP : T ≤ P) (hPG : P ≤ G) (hP : ¬ P ≤ cStarIn G T)
    (hmin : ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ cStarIn G T) : IsMinParabolic2 T P := by
  have hTC : T ≤ cStarIn G T := le_cStarIn_self hT.1 hT.2.1 hT0
  refine ⟨isSylowTwoOf_of_le hT hTP hPG, ?_, P ⊓ cStarIn G T, le_inf hTP hTC, ?_, ?_⟩
  · intro hPN
    exact hP fun x hx => inf_normalizer_le_cStarIn hT.2.1 hT0 ⟨hPG hx, hPN hx⟩
  · exact lt_of_le_of_ne inf_le_left fun h => hP (h ▸ inf_le_right)
  · exact fun X hTX hXP => le_inf hXP.le (hmin X hTX hXP)

end CFSG.CGT.PushingUpLit.BHS
