module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open scoped MatrixGroups Matrix IsMulCommutative

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

section Transport

variable {F : Type} [Field F] {Λ Λ' : Type} [Group Λ] [Group Λ']

theorem Cover.congr {φ : SL(3, F) →* Λ} (h : Cover φ) (e : Λ ≃* Λ') :
    Cover (e.toMonoidHom.comp φ) where
  surjective := e.surjective.comp h.surjective
  ker_le := fun x hx => h.ker_le x (e.injective (by simpa using hx))
  map_scalars := by
    rw [← Subgroup.map_map, h.map_scalars]
    exact Subgroup.map_center_eq e

end Transport

section Exchange

variable {F : Type} [Field F] [CharP F 2] [Fintype F]

theorem exists_exchange_of_cpt {X : Type} [Group X] [Finite X] {ι : Type*} {Lf : ι → Subgroup X}
    {i₀ : ι} {T M : Subgroup X} (hc : CentralProductTransfer 2 T M Lf i₀)
    (hq : Group.IsPerfect ↥(Lf i₀)) {φ : SL(3, F) →* ↥(Lf i₀)} (h : Cover φ) {f : ℕ}
    (hf : 1 ≤ f) (hF : Fintype.card F = 2 ^ f) :
    ∃ n ∈ normL (Lf i₀), ∃ (B : GL (Fin 3) F) (j : ℕ), ∀ x : SL(3, F),
      n * ((φ x : ↥(Lf i₀)) : X) * n⁻¹ = ((φ (graphFieldHom B j x) : ↥(Lf i₀)) : X) := by
  have hAS : actImg (Lf i₀) (normL (Lf i₀)) =
      OuterAutomorphisms.inner ↥(Lf i₀) ⊔ actImg (Lf i₀) (normT T (Lf i₀)) :=
    hc.range_eq_inn_mul
  have hS : IsSylowTwoOf (actImg (Lf i₀) (normT T (Lf i₀))) (actImg (Lf i₀) (normL (Lf i₀))) :=
    isSylowTwoOf_iff_isSylowOf.2 hc.sylow_S
  obtain ⟨hSP, hPA, hY⟩ := hc.P_max
  have hmax : actImg (Lf i₀) (normT T (Lf i₀)) ≤ actImg (Lf i₀) (maxL T M (Lf i₀)) ∧
      actImg (Lf i₀) (maxL T M (Lf i₀)) ⋖ actImg (Lf i₀) (normL (Lf i₀)) ∧
      ∀ M' : Subgroup (MulAut ↥(Lf i₀)), M' ⋖ actImg (Lf i₀) (normL (Lf i₀)) →
        actImg (Lf i₀) (normT T (Lf i₀)) ≤ M' → M' = actImg (Lf i₀) (maxL T M (Lf i₀)) := by
    refine ⟨hSP, ⟨hPA, fun c hPc hcA => ?_⟩, fun M' hM'A hSM' => ?_⟩
    · exact absurd (hY c hcA.le (hSP.trans hPc.le) hcA) (not_le_of_gt hPc)
    · have hM'P : M' ≤ actImg (Lf i₀) (maxL T M (Lf i₀)) := hY M' hM'A.lt.le hSM' hM'A.lt
      by_contra hne
      exact hM'A.2 (lt_of_le_of_ne hM'P hne) hPA
  obtain ⟨α, hαS, hα⟩ := h.exists_typeExchanging hAS hS hmax
  obtain ⟨n, -, hnN, rfl⟩ := mem_actImg.1 hαS
  rcases h.dichotomy hF hf (actOf (Lf i₀) n) with h1 | ⟨B, j, hB⟩
  · exact absurd h1 hα
  · refine ⟨n, hnN, B, j, fun x => ?_⟩
    have := congrArg (fun l : ↥(Lf i₀) => (l : X)) (hB x)
    simpa [actOf_coe hnN] using this

end Exchange

section Linear

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W]

theorem section_linear {H T M E : Subgroup (W ≃ₗ[ZMod 2] W)} (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N →
      N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (W ≃ₗ[ZMod 2] W), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card W ≤ weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) E)
    {L : Subgroup (W ≃ₗ[ZMod 2] W)} (hL : IsComponentIn L H) {f : ℕ} (hf : 2 ≤ f)
    (hF : Fintype.card F = 2 ^ f) {φ : SL(3, F) →* ↥L} (h : Cover φ) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module (ZMod 2) U) (_ : Finite U)
      (ρL : Representation (ZMod 2) ↥L U) (A' : Subgroup (U ≃ₗ[ZMod 2] U)),
      (∀ x : SL(3, F), ρL (φ x) = 1 → x ∈ scalars 3 F) ∧
      Representation.IsIrreducible (ρL.comp φ) ∧
      Nonempty (Representation.Equiv (ρL.comp φ) (Representation.dual (ρL.comp φ))) ∧
      CFSG.IsElementaryAbelian 2 ↥A' ∧ A' ≠ ⊥ ∧
      (∀ a ∈ A', ∀ x : SL(3, F), ∃ y : SL(3, F), Intertwines (ρL.comp φ) a x y) ∧
      Nat.card U ≤ Nat.card A' * Nat.card {u : U // ∀ a ∈ A', a u = u} := by
  classical
  have : Finite (W ≃ₗ[ZMod 2] W) := finite_linearEquiv
  have hf1 : 1 ≤ f := by omega
  have hLH : L ≤ H := hL.1
  have hLc : CFSG.IsComponent (L.subgroupOf H) := hL.2
  have hqL : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isComponentIn hL
  have hAct := Final.actual_component_minimal_parabolic hns hO2 hT hTn hTM hMH hmax hEH hEne hEel
    hEoff
  let c : Comp ↥H := ⟨L.subgroupOf H, hLc⟩
  have hcpt := hAct.transfer c
  obtain ⟨A₀, hA₀le, hA₀min, hA₀comm⟩ := hAct.offender c
  obtain ⟨hA₀H, hA₀ne, hA₀el, hA₀off, hA₀strict⟩ := hA₀min
  have hmapL : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hA₀L : ⁅L, A₀⁆ = L := by
    have h1 : ⁅(L.subgroupOf H).map H.subtype, A₀⁆ = (L.subgroupOf H).map H.subtype := hA₀comm
    rwa [hmapL] at h1
  obtain ⟨hquad0, -⟩ := Final.minimal_best_offenders_normalize_components (G := H) (A := A₀)
    (fun a ha => Subgroup.le_normalizer (hA₀H ha)) hA₀el hA₀ne hA₀off hA₀strict
  set N' : Subgroup (W ≃ₗ[ZMod 2] W) := Subgroup.normalizer (L : Set (W ≃ₗ[ZMod 2] W)) with hN'
  have hLN : L ≤ N' := Subgroup.le_normalizer
  have hA₀N : A₀ ≤ N' := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := hA₀le ha
    have hnN : n ∈ normL (L.subgroupOf H) := hn.2
    have := map_subtype_mem_normalizer (H := H) (L := L.subgroupOf H) hnN
    rwa [hmapL] at this
  let L₁ : Subgroup ↥N' := L.subgroupOf N'
  have hL₁N : L₁.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.1 g.2 x).1 hx⟩
  let e : ↥L ≃* ↥L₁ := (Subgroup.subgroupOfEquivOfLe hLN).symm
  let φ₁ : SL(3, F) →* ↥L₁ := e.toMonoidHom.comp φ
  have h₁ : Cover φ₁ := h.congr e
  have hq₁ : CFSG.IsQuasisimple ↥L₁ := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqL
  let A : Subgroup ↥N' := A₀.subgroupOf N'
  have hmapA : A.map N'.subtype = A₀ := Subgroup.map_subgroupOf_eq_of_le hA₀N
  have hmapL₁ : L₁.map N'.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLN
  have hAne : A ≠ ⊥ := by
    intro hbot
    apply hA₀ne
    rw [← hmapA, hbot, Subgroup.map_bot]
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := IsElementaryAbelian.subgroupOf hA₀N
  have hLA : ⁅L₁, A⁆ = L₁ := by
    apply Subgroup.map_injective N'.subtype_injective
    rw [Subgroup.map_commutator, hmapL₁, hmapA]
    exact hA₀L
  have hw : ∀ B : Subgroup ↥N', weight N'.subtype B =
      weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (B.map N'.subtype) := fun B =>
    weight_comp_subtype (MonoidHom.id (W ≃ₗ[ZMod 2] W)) N' B
  have hoff : Nat.card W ≤ weight N'.subtype A := by
    rw [hw, hmapA]
    exact hA₀off
  have hstrict : ∀ D : Subgroup ↥N', ⊥ < D → D < A → weight N'.subtype D < weight N'.subtype A := by
    intro B hB0 hBA
    rw [hw B, hw A, hmapA]
    refine hA₀strict (B.map N'.subtype) ?_ ?_
    · refine bot_lt_iff_ne_bot.mpr fun h => (bot_lt_iff_ne_bot.mp hB0) ?_
      exact (Subgroup.map_eq_bot_iff_of_injective B N'.subtype_injective).mp h
    · rw [← hmapA]
      exact (Subgroup.map_lt_map_iff_of_injective N'.subtype_injective).mpr hBA
  have hquad : QuadAct N'.subtype A := by
    intro b hb c' hc v
    exact hquad0 (b : W ≃ₗ[ZMod 2] W) hb (c' : W ≃ₗ[ZMod 2] W) hc v
  have hex : ∃ (g : ↥N') (B : GL (Fin 3) F) (j : ℕ), ∀ x : SL(3, F),
      g * ((φ₁ x : ↥L₁) : ↥N') * g⁻¹ = ((φ₁ (graphFieldHom B j x) : ↥L₁) : ↥N') := by
    let φ₀ : SL(3, F) →* ↥(L.subgroupOf H) :=
      (Subgroup.subgroupOfEquivOfLe hLH).symm.toMonoidHom.comp φ
    have h₀ : Cover φ₀ := h.congr (Subgroup.subgroupOfEquivOfLe hLH).symm
    have hperf₀ : Group.IsPerfect ↥(L.subgroupOf H) := hLc.1.1
    obtain ⟨n, hnN, B, j, hnB⟩ := exists_exchange_of_cpt (hc := hcpt) hperf₀ h₀ hf1 hF
    have hgN : (n : W ≃ₗ[ZMod 2] W) ∈ N' := by
      have := map_subtype_mem_normalizer (H := H) (L := L.subgroupOf H) hnN
      rwa [hmapL] at this
    refine ⟨⟨(n : W ≃ₗ[ZMod 2] W), hgN⟩, B, j, fun x => ?_⟩
    apply Subtype.ext
    have h2 := congrArg (fun y : ↥H => (y : W ≃ₗ[ZMod 2] W)) (hnB x)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    exact h2
  obtain ⟨U, iU1, iU2, iU3, ρL₁, A', hker, hirr, hsd, hel, hne, hint, hoffU⟩ :=
    section_core hf hF N'.subtype N'.subtype_injective L₁ hq₁ h₁ hex hAne hAel hLA hoff hstrict
      hquad
  exact ⟨U, iU1, iU2, iU3, ρL₁.comp e.toMonoidHom, A', hker, hirr, hsd, hel, hne, hint, hoffU⟩

end Linear

end CFSG.QuasithinUnique.Setup.X7Sec
