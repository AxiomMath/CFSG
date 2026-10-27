module

public import CFSG.ClassicalInvolution.Balance.Delta

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification

section Constant

variable {G : Type*} [Group G]

theorem deltaCore_anti {D D' : Subgroup G} (h : D ≤ D') : deltaCore D' ≤ deltaCore D :=
  le_deltaCore fun _ hd hd1 => deltaCore_le_involutionOddCore (h hd) hd1

@[expose] def CentralizedDelta (A : Subgroup G) : Prop :=
  ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F ≤ Subgroup.centralizer (A : Set G)

@[expose] def StronglyBalanced (A : Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → involutionOddCore a ≤ Subgroup.centralizer (A : Set G)

theorem StronglyBalanced.centralizedDelta [Finite G] {A : Subgroup G} (h : StronglyBalanced A) :
    CentralizedDelta A := by
  intro F hF
  obtain ⟨f₀, hf₀, hf₀1⟩ := exists_ne_one_of_card_eq_two_pow (by norm_num) hF.2
  exact (deltaCore_le_involutionOddCore hf₀ hf₀1).trans (h f₀ (hF.1 hf₀) hf₀1)

theorem deltaCore_eq_deltaCore_of_centralized {A F : Subgroup G} (hFA : F ≤ A)
    (hS : deltaCore F ≤ Subgroup.centralizer (A : Set G))
    (h2 : ∀ a ∈ A, a ≠ 1 → deltaCore F ⊓ Subgroup.centralizer {a} ≤ involutionOddCore a) :
    deltaCore F = deltaCore A := by
  refine le_antisymm (fun x hx => ?_) (deltaCore_anti hFA)
  refine mem_deltaCore_iff.mpr fun a ha ha1 => ?_
  exact h2 a ha ha1 ⟨hx, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha) (hS hx)⟩

end Constant

section Equivariance

variable {G : Type*} [Group G]

theorem exists_map_four {A F' : Subgroup G} (g : G)
    (hF' : F' ∈ signalizerFunctorEk 2 2 (A.map (MulAut.conj g).toMonoidHom)) :
    ∃ F ∈ signalizerFunctorEk 2 2 A, F.map (MulAut.conj g).toMonoidHom = F' := by
  set e : G ≃* G := MulAut.conj g with he
  refine ⟨F'.map e.symm.toMonoidHom, ⟨fun y hy => ?_, ?_⟩, ?_⟩
  · obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have := hF'.1 hy'
    rw [Subgroup.mem_map_equiv] at this
    exact this
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hF'.2
  · ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simp

theorem StronglyBalanced.map {A : Subgroup G} (h : StronglyBalanced A) (g : G) :
    StronglyBalanced (A.map (MulAut.conj g).toMonoidHom) := by
  intro a' ha' ha'1 x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  have ha1 : a ≠ 1 := fun h1 => ha'1 (by simp [h1])
  have hx' : x ∈ (involutionOddCore a).map (MulAut.conj g).toMonoidHom := by
    rw [involutionOddCore_map]; exact hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨c, hc, rfl⟩
  have := Subgroup.mem_centralizer_iff.mp (h a ha ha1 hy) c hc
  change g * c * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * c * g⁻¹)
  calc g * c * g⁻¹ * (g * y * g⁻¹) = g * (c * y) * g⁻¹ := by group
    _ = g * (y * c) * g⁻¹ := by rw [this]
    _ = g * y * g⁻¹ * (g * c * g⁻¹) := by group

theorem centralizedDelta_map {A : Subgroup G} (h : CentralizedDelta A) (g : G) :
    CentralizedDelta (A.map (MulAut.conj g).toMonoidHom) := by
  intro F' hF' x hx
  obtain ⟨F, hF, rfl⟩ := exists_map_four g hF'
  rw [← deltaCore_map] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨c, hc, rfl⟩
  have := Subgroup.mem_centralizer_iff.mp (h F hF hy) c hc
  change g * c * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * c * g⁻¹)
  calc g * c * g⁻¹ * (g * y * g⁻¹) = g * (c * y) * g⁻¹ := by group
    _ = g * (y * c) * g⁻¹ := by rw [this]
    _ = g * y * g⁻¹ * (g * c * g⁻¹) := by group

@[expose] def ShareFour (X Y : Subgroup G) : Prop :=
  ∃ F ∈ signalizerFunctorEk 2 2 X, F ∈ signalizerFunctorEk 2 2 Y

theorem ShareFour.symm {X Y : Subgroup G} (h : ShareFour X Y) : ShareFour Y X :=
  let ⟨F, hX, hY⟩ := h
  ⟨F, hY, hX⟩

theorem twoBalancedWrt_map {A : Subgroup G} (h : TwoBalancedWrt A) (g : G) :
    TwoBalancedWrt (A.map (MulAut.conj g).toMonoidHom) := by
  intro F' hF' a' ha' ha'1 x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  have ha1 : a ≠ 1 := fun h1 => ha'1 (by simp [h1])
  obtain ⟨F, hFA, rfl⟩ := exists_map_four g hF'
  set e : G ≃* G := MulAut.conj g with he
  have hx1 : x ∈ (deltaCore F).map e.toMonoidHom := by
    rw [he, deltaCore_map]
    exact hx.1
  have hy1 : e.symm x ∈ deltaCore F := by
    rw [Subgroup.mem_map_equiv] at hx1
    exact hx1
  have hy2 : e.symm x ∈ Subgroup.centralizer {a} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    apply e.injective
    simpa using this
  have hy := h F hFA a ha ha1 ⟨hy1, hy2⟩
  have : x ∈ (involutionOddCore a).map e.toMonoidHom := by
    rw [Subgroup.mem_map_equiv]
    exact hy
  rw [he, involutionOddCore_map] at this
  exact this

end Equivariance

section Descent

variable {G : Type*} [Group G]

theorem normal_of_constant_on_connected {𝒯 : Set (Subgroup G)} (Φ : Subgroup G → Subgroup G)
    (r : Subgroup G → Subgroup G → Prop)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hequi : ∀ A ∈ 𝒯, ∀ g : G,
      (Φ A).map (MulAut.conj g).toMonoidHom = Φ (A.map (MulAut.conj g).toMonoidHom))
    (hr : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, r A A' → Φ A = Φ A')
    (hconn : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ r X Y) A A') :
    ∀ A ∈ 𝒯, (Φ A).Normal := by
  intro A hA
  have hconst : ∀ A', A' ∈ 𝒯 → Φ A = Φ A' := by
    intro A' hA'
    have hpath := hconn A hA A' hA'
    clear hA'
    induction hpath with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (hr _ hbc.1 _ hbc.2.1 hbc.2.2)
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n * g⁻¹ ∈ (Φ A).map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
  rwa [hequi A hA g, ← hconst _ (hinv A hA g)] at h1

theorem reflTransGen_symm_of_symm {α : Type*} {r : α → α → Prop} (hr : ∀ x y, r x y → r y x)
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hr _ _ hbc) ih

end Descent

section Triviality

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem deltaCore_eq_of_shareFour {A A' : Subgroup G} (hAA' : ShareFour A A')
    (hS : CentralizedDelta A) (hS' : CentralizedDelta A') (h2 : TwoBalancedWrt A)
    (h2' : TwoBalancedWrt A') : deltaCore A = deltaCore A' := by
  obtain ⟨F, hF, hF'⟩ := hAA'
  exact (deltaCore_eq_deltaCore_of_centralized hF.1 (hS F hF)
      fun a ha ha1 => h2 F hF a ha ha1).symm.trans
    (deltaCore_eq_deltaCore_of_centralized hF'.1 (hS' F hF')
      fun a ha ha1 => h2' F hF' a ha ha1)

theorem deltaCore_eq_bot_of_connected {𝒯 : Set (Subgroup G)}
    (hO : componentClassificationOddCore G = ⊥)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hne : ∀ A ∈ 𝒯, ∃ a ∈ A, a ≠ 1) (hS : ∀ A ∈ 𝒯, CentralizedDelta A)
    (h2 : ∀ A ∈ 𝒯, TwoBalancedWrt A)
    (hconn : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A') :
    ∀ A ∈ 𝒯, ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ := by
  have hnormal := normal_of_constant_on_connected (𝒯 := 𝒯) deltaCore ShareFour hinv
    (fun A _ g => deltaCore_map g A)
    (fun A hA A' hA' hAA' => deltaCore_eq_of_shareFour hAA' (hS A hA) (hS A' hA') (h2 A hA)
      (h2 A' hA')) hconn
  intro A hA F hF
  obtain ⟨a, ha, ha1⟩ := hne A hA
  have hodd : Odd (Nat.card (deltaCore A)) := odd_card_deltaCore ha ha1
  have hle : deltaCore A ≤ componentClassificationOddCore G :=
    CFSG.ComponentClassification.OddCore.maximal G _ (hnormal A hA) hodd
  rw [hO] at hle
  rw [deltaCore_eq_deltaCore_of_centralized hF.1 (hS A hA F hF)
    fun a ha ha1 => h2 A hA F hF a ha ha1]
  exact le_bot_iff.mp hle

@[expose] def conjClass (A : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ g : G, X = A.map (MulAut.conj g).toMonoidHom}

theorem deltaCore_eq_bot_of_class {A : Subgroup G} (hO : componentClassificationOddCore G = ⊥)
    (hne : ∃ a ∈ A, a ≠ 1) (hS : CentralizedDelta A) (h2 : TwoBalancedWrt A)
    (hconn : ∀ g : G, Relation.ReflTransGen
      (fun X Y => X ∈ conjClass A ∧ Y ∈ conjClass A ∧ ShareFour X Y) A
      (A.map (MulAut.conj g).toMonoidHom)) :
    ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ := by
  have hAmem : A ∈ conjClass A := ⟨1, by ext x; simp⟩
  have hsymm : ∀ X Y : Subgroup G, (X ∈ conjClass A ∧ Y ∈ conjClass A ∧ ShareFour X Y) →
      (Y ∈ conjClass A ∧ X ∈ conjClass A ∧ ShareFour Y X) :=
    fun _ _ h => ⟨h.2.1, h.1, ShareFour.symm h.2.2⟩
  refine deltaCore_eq_bot_of_connected (𝒯 := conjClass A) hO ?_ ?_ ?_ ?_ ?_ A hAmem
  · rintro X ⟨h, rfl⟩ g
    refine ⟨g * h, ?_⟩
    ext x
    simp [mul_assoc]
  · rintro X ⟨h, rfl⟩
    obtain ⟨a, ha, ha1⟩ := hne
    refine ⟨h * a * h⁻¹, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, fun h1 => ha1 ?_⟩
    simpa using h1
  · rintro X ⟨h, rfl⟩
    exact centralizedDelta_map hS h
  · rintro X ⟨h, rfl⟩
    exact twoBalancedWrt_map h2 h
  · rintro X ⟨h, rfl⟩ X' ⟨h', rfl⟩
    exact (reflTransGen_symm_of_symm hsymm (hconn h)).trans (hconn h')

omit [Finite G] in
theorem reflTransGen_conjClass_of_centralizer_generated {A : Subgroup G}
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤) (g : G) :
    Relation.ReflTransGen
      (fun X Y => X ∈ conjClass A ∧ Y ∈ conjClass A ∧ ShareFour X Y) A
      (A.map (MulAut.conj g).toMonoidHom) := by
  set S : Set G := ⋃ F ∈ signalizerFunctorEk 2 2 A, (Subgroup.centralizer (F : Set G) : Set G)
    with hS
  have hcl : Subgroup.closure S = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hgen]
    refine iSup₂_le fun F hF x hx => Subgroup.subset_closure ?_
    exact Set.mem_iUnion₂.mpr ⟨F, hF, hx⟩
  have hg : g ∈ Subgroup.closure S := hcl ▸ Subgroup.mem_top g
  have hmap : ∀ (x c : G), A.map (MulAut.conj (x * c)).toMonoidHom =
      (A.map (MulAut.conj c).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro x c
    ext y
    simp [Subgroup.mem_map, mul_assoc]
  have hstep : ∀ x : G, ∀ y ∈ S, ShareFour (A.map (MulAut.conj x).toMonoidHom)
      (A.map (MulAut.conj (x * y)).toMonoidHom) := by
    intro x y hy
    obtain ⟨F, hF, hyF⟩ := Set.mem_iUnion₂.mp hy
    have hyF' : ∀ f ∈ F, y * f * y⁻¹ = f := by
      intro f hf
      have := Subgroup.mem_centralizer_iff.mp hyF f hf
      calc y * f * y⁻¹ = (y * f) * y⁻¹ := rfl
        _ = (f * y) * y⁻¹ := by rw [← this]
        _ = f := by group
    have hFy : F ≤ A.map (MulAut.conj y).toMonoidHom := fun f hf =>
      Subgroup.mem_map.mpr ⟨f, hF.1 hf, hyF' f hf⟩
    refine ⟨F.map (MulAut.conj x).toMonoidHom, ⟨Subgroup.map_mono hF.1, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hF.2
    · rw [hmap]
      exact Subgroup.map_mono hFy
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hF.2
  refine Subgroup.closure_induction_right (p := fun x _ => Relation.ReflTransGen
      (fun X Y => X ∈ conjClass A ∧ Y ∈ conjClass A ∧ ShareFour X Y) A
      (A.map (MulAut.conj x).toMonoidHom)) ?_ ?_ ?_ hg
  · have : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by ext x; simp
    rw [this]
  · intro x _ y hy ih
    exact ih.tail ⟨⟨x, rfl⟩, ⟨x * y, rfl⟩, hstep x y hy⟩
  · intro x _ y hy ih
    have hy' : y⁻¹ ∈ S := by
      obtain ⟨F, hF, hyF⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr ⟨F, hF, (Subgroup.centralizer (F : Set G)).inv_mem hyF⟩
    exact ih.tail ⟨⟨x, rfl⟩, ⟨x * y⁻¹, rfl⟩, hstep x y⁻¹ hy'⟩

theorem deltaCore_eq_bot_of_four_centralizer_generated {A : Subgroup G}
    (hO : componentClassificationOddCore G = ⊥) (hne : ∃ a ∈ A, a ≠ 1) (hS : CentralizedDelta A)
    (h2 : TwoBalancedWrt A)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤) :
    ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ :=
  deltaCore_eq_bot_of_class hO hne hS h2 (reflTransGen_conjClass_of_centralizer_generated hgen)

end Triviality

end CFSG.ClassicalInvolution.Balance.Bootstrap
