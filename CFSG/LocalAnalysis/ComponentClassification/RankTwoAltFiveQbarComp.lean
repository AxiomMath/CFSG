module

public import CFSG.LocalAnalysis.ComponentClassification.AS81QbarComp
public import CFSG.Goldschmidt.Steps.Components
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores

namespace CFSG.ComponentClassification.RankTwoAltFive

section Count

variable {G : Type*} [Group G]

theorem exists_card_eq_add_mul {Q B : Subgroup G} [Finite Q] (hBQ : B ≤ Q) (P : G → Prop)
    [DecidablePred P]
    (hT : ∀ x ∈ Q, x ∉ B → ∀ x' ∈ Q, x' ∉ B → ∃ c : G, (∀ y ∈ Q, c * y * c⁻¹ ∈ Q) ∧
      (∀ b ∈ B, c * b * c⁻¹ ∈ B) ∧ x'⁻¹ * (c * x * c⁻¹) ∈ B ∧
      ∀ y ∈ Q, (P y ↔ P (c * y * c⁻¹))) :
    ∃ m : ℕ, Nat.card {y : Q // P y} = Nat.card {y : B // P y} + (B.relIndex Q - 1) * m := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : Finite B := Finite.of_injective (inclusion hBQ) (inclusion_injective hBQ)
  set B' := B.subgroupOf Q with hB'
  have : Fintype (Q ⧸ B') := Fintype.ofFinite _
  have hmk : ∀ y y' : Q, (QuotientGroup.mk y : Q ⧸ B') = QuotientGroup.mk y' ↔
      (y : G)⁻¹ * y' ∈ B := fun y y' => by
    rw [QuotientGroup.eq, hB', mem_subgroupOf]
    rfl
  let F : Q ⧸ B' → ℕ := fun κ =>
    (Finset.univ.filter fun y : Q => P y ∧ (QuotientGroup.mk y : Q ⧸ B') = κ).card
  have hle : ∀ x x' : Q, (x : G) ∉ B → (x' : G) ∉ B →
      F (QuotientGroup.mk x) ≤ F (QuotientGroup.mk x') := by
    intro x x' hx hx'
    obtain ⟨c, hcQ, hcB, hcx, hcP⟩ := hT x x.2 hx x' x'.2 hx'
    let φ : Q → Q := fun y => ⟨c * y * c⁻¹, hcQ y y.2⟩
    have hφ : Function.Injective φ := fun y y' h => by
      have h' : c * (y : G) * c⁻¹ = c * y' * c⁻¹ := congrArg Subtype.val h
      exact Subtype.ext (by simpa using h')
    refine Finset.card_le_card_of_injOn φ ?_ hφ.injOn
    intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨hPy, hyx⟩ := hy
    refine ⟨(hcP y y.2).mp hPy, ?_⟩
    rw [hmk] at hyx ⊢
    have h1 : (x : G)⁻¹ * y ∈ B := by
      have := inv_mem hyx
      rwa [mul_inv_rev, inv_inv] at this
    have h2 := mul_mem hcx (hcB _ h1)
    have e : (c * (y : G) * c⁻¹)⁻¹ * x' =
        ((x' : G)⁻¹ * (c * x * c⁻¹) * (c * ((x : G)⁻¹ * y) * c⁻¹))⁻¹ := by group
    change (c * (y : G) * c⁻¹)⁻¹ * x' ∈ B
    rw [e]
    exact inv_mem h2
  have hF1 : F (QuotientGroup.mk 1) = Nat.card {y : B // P y} := by
    change Finset.card _ = _
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
        invFun := fun y => ⟨⟨y.1, hBQ y.1.2⟩, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
    · have h := (Finset.mem_filter.mp y.2).2.2
      rw [hmk] at h
      simpa using h
    · exact (Finset.mem_filter.mp y.2).2.1
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2, ?_⟩
      rw [hmk]
      simp
  have hsum : Nat.card {y : Q // P y} = ∑ κ : Q ⧸ B', F κ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.card_eq_sum_card_fiberwise (f := fun y : Q => (QuotientGroup.mk y : Q ⧸ B'))
        (t := Finset.univ) (fun y _ => Finset.mem_univ _)]
    exact Finset.sum_congr rfl fun κ _ => by rw [Finset.filter_filter]
  by_cases hex : ∃ x₀ : Q, (x₀ : G) ∉ B
  · obtain ⟨x₀, hx₀⟩ := hex
    refine ⟨F (QuotientGroup.mk x₀), ?_⟩
    have hconst : ∀ κ ∈ Finset.univ.erase (QuotientGroup.mk 1 : Q ⧸ B'),
        F κ = F (QuotientGroup.mk x₀) := by
      intro κ hκ
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective κ
      have hx : (x : G) ∉ B := by
        intro hxB
        apply (Finset.mem_erase.mp hκ).1
        rw [hmk]
        simpa using inv_mem hxB
      exact le_antisymm (hle x x₀ hx hx₀) (hle x₀ x hx₀ hx)
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ _), hF1, Finset.sum_congr rfl hconst,
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      smul_eq_mul]
    congr 2
    rw [relIndex, index, Nat.card_eq_fintype_card]
  · push Not at hex
    refine ⟨0, ?_⟩
    rw [mul_zero, add_zero, hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ _), hF1]
    have hsub : Finset.univ.erase (QuotientGroup.mk 1 : Q ⧸ B') = ∅ := by
      ext κ
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.notMem_empty, iff_false,
        not_not]
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective κ
      rw [hmk]
      simpa using inv_mem (hex x)
    rw [hsub, Finset.sum_empty, add_zero]

end Count

variable {Y : Type} [Group Y] [Finite Y]

theorem center_component_le_pCore (hO : goldschmidtOddCore Y = ⊥) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) {ζ : K} (hζ : ζ ∈ center K) : (ζ : Y) ∈ CFSG.Open.pCore 2 Y := by
  have hZE := (N8d Y hO).2.1
  refine hZE ?_
  have hzE : (ζ : Y) ∈ goldschmidtLayer Y := ComponentClassification.Layer.component_le hK ζ.2
  have hzc := ComponentClassification.ComponentAutomorphisms.center_le_layer_center K hK
    (Subgroup.mem_map_of_mem K.subtype hζ)
  refine ⟨⟨ζ, hzE⟩, Subgroup.mem_center_iff.mpr fun e => Subtype.ext ?_, rfl⟩
  exact Subgroup.mem_centralizer_iff.mp hzc e e.2

theorem exists_conj_mem_of_component
    (Sb : Sylow 2 Y) {A K : Subgroup Y} (hO : goldschmidtOddCore Y = ⊥)
    (hAS : A ≤ Sb) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAinv : ∀ t ∈ (Sb : Subgroup Y) ⊓ goldschmidtLayer Y, t ^ 2 = 1 → t ∈ A)
    (hAO : CFSG.Open.pCore 2 Y ≤ A)
    (hK : IsComponentOf K ⊤) (htype : goldschmidtSimpleType (K ⧸ center K))
    (hcover : ∀ a ∈ A, ∃ x ∈ A ⊓ K, ∀ y ∈ K, a⁻¹ * y * a = x⁻¹ * y * x)
    {a a' : Y} (ha : a ∈ A) (ha' : a' ∈ A) (hna : a ∉ centralizer (K : Set Y))
    (hna' : a' ∉ centralizer (K : Set Y)) :
    ∃ n ∈ K, (∀ b ∈ A, n * b * n⁻¹ ∈ A) ∧ a'⁻¹ * (n * a * n⁻¹) ∈ centralizer (K : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (K ⧸ center K) := hK.2.2.2
  have hK' : CFSG.IsComponent K := (CFSG.isComponent_iff_open K).mpr hK
  have hcov : ∀ b ∈ A, ∃ x ∈ A ⊓ K, b * x⁻¹ ∈ centralizer (K : Set Y) := by
    intro b hb
    obtain ⟨x, hx, hbx⟩ := hcover b hb
    refine ⟨x, hx, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 := hbx y hy
    calc y * (b * x⁻¹) = b * (b⁻¹ * y * b) * x⁻¹ := by group
      _ = b * (x⁻¹ * y * x) * x⁻¹ := by rw [h1]
      _ = b * x⁻¹ * y := by group
  obtain ⟨P, hP⟩ := AS81.Qbar.isSylowOf_inf_component Sb hK'
  set TL : Sylow 2 (K ⧸ center K) := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
    with hTL
  have hTLcoe : (TL : Subgroup (K ⧸ center K)) = (P : Subgroup K).map (QuotientGroup.mk' _) :=
    Sylow.coe_mapSurjective _ _
  set W := Omega1 (TL : Subgroup (K ⧸ center K)) with hW
  have hWab : IsMulCommutative W := AS81.Qbar.isMulCommutative_omega1 htype TL
  have hZS : ∀ ζ : K, ζ ∈ center K → (ζ : Y) ∈ (Sb : Subgroup Y) :=
    fun ζ hζ => hAS (hAO (center_component_le_pCore hO hK hζ))
  have hmemS : ∀ k : K, (QuotientGroup.mk k : K ⧸ center K) ∈ (TL : Subgroup (K ⧸ center K)) →
      (k : Y) ∈ (Sb : Subgroup Y) := by
    intro k hk
    rw [hTLcoe] at hk
    obtain ⟨p, hp, hpk⟩ := hk
    have hpS : (p : Y) ∈ (Sb : Subgroup Y) := by
      have : (p : Y) ∈ (P : Subgroup K).map K.subtype := ⟨p, hp, rfl⟩
      rw [hP] at this
      exact this.1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hpk
    have h1 := hZS _ hpk
    have e : (k : Y) = p * ((p⁻¹ * k : K) : Y) := by simp
    rw [e]
    exact mul_mem hpS h1
  have hAW : ∀ x : K, (x : Y) ∈ A →
      (QuotientGroup.mk x : K ⧸ center K) ∈ W := by
    intro x hx
    refine GoldType.mem_omega1 ?_ ?_
    · rw [hTLcoe]
      refine ⟨x, ?_, rfl⟩
      have hxS : (x : Y) ∈ (Sb : Subgroup Y) ⊓ K := ⟨hAS hx, x.2⟩
      rw [← hP] at hxS
      obtain ⟨y, hy, hyx⟩ := hxS
      rwa [Subtype.ext hyx] at hy
    · rw [← QuotientGroup.mk_pow]
      have h2 : x ^ 2 = 1 := Subtype.ext (by simpa using hA2 x hx)
      rw [h2, QuotientGroup.mk_one]
  have hconjA : ∀ m : K, (QuotientGroup.mk m : K ⧸ center K) ∈ normalizer (W : Set (K ⧸ center K)) →
      ∀ x : K, (x : Y) ∈ A → (m : Y)⁻¹ * x * m ∈ A := by
    intro m hm x hx
    have hxW := hAW x hx
    have h1 : (QuotientGroup.mk (m⁻¹ * x * m) : K ⧸ center K) ∈ W := by
      have := (mem_normalizer_iff.mp (inv_mem hm) _).mp hxW
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this
    have h2 : (((m⁻¹ * x * m : K)) : Y) ∈ (Sb : Subgroup Y) :=
      hmemS _ (GoldType.omega1_le _ h1)
    have h3 : (((m⁻¹ * x * m : K)) : Y) ∈ goldschmidtLayer Y :=
      ComponentClassification.Layer.component_le hK (m⁻¹ * x * m).2
    have h2' : (m : Y)⁻¹ * x * m ∈ (Sb : Subgroup Y) := by simpa using h2
    have h3' : (m : Y)⁻¹ * x * m ∈ goldschmidtLayer Y := by simpa using h3
    refine hAinv _ (mem_inf.mpr ⟨h2', h3'⟩) ?_
    have := hA2 x hx
    calc ((m : Y)⁻¹ * x * m) ^ 2 = (m : Y)⁻¹ * (x ^ 2) * m := by rw [sq, sq]; group
      _ = 1 := by rw [this]; group
  obtain ⟨x, ⟨hxA, hxK⟩, hax⟩ := hcov a ha
  obtain ⟨x', ⟨hx'A, hx'K⟩, ha'x'⟩ := hcov a' ha'
  have hx1 : (QuotientGroup.mk (⟨x, hxK⟩ : K) : K ⧸ center K) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff, mem_center_iff] at h1
    apply hna
    have hxc : x ∈ centralizer (K : Set Y) := mem_centralizer_iff.mpr fun y hy =>
      (congrArg Subtype.val (h1 ⟨y, hy⟩) : _)
    have := mul_mem hax hxc
    rwa [inv_mul_cancel_right] at this
  have hx'1 : (QuotientGroup.mk (⟨x', hx'K⟩ : K) : K ⧸ center K) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff, mem_center_iff] at h1
    apply hna'
    have hxc : x' ∈ centralizer (K : Set Y) := mem_centralizer_iff.mpr fun y hy =>
      (congrArg Subtype.val (h1 ⟨y, hy⟩) : _)
    have := mul_mem ha'x' hxc
    rwa [inv_mul_cancel_right] at this
  obtain ⟨nb, hnb, hnbx⟩ := (N11b (K ⧸ center K) htype TL hWab).2 _ (hAW ⟨x, hxK⟩ hxA) _
    (hAW ⟨x', hx'K⟩ hx'A) hx1 hx'1
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective nb
  refine ⟨(m : Y)⁻¹, inv_mem m.2, ?_, ?_⟩
  ·
    intro b hb
    obtain ⟨y, ⟨hyA, hyK⟩, hby⟩ := hcov b hb
    have e : (m : Y)⁻¹ * b * (m : Y)⁻¹⁻¹ = (b * y⁻¹) * ((m : Y)⁻¹ * y * m) := by
      have hc := mem_centralizer_iff.mp hby (m : Y) m.2
      calc (m : Y)⁻¹ * b * (m : Y)⁻¹⁻¹ = (m : Y)⁻¹ * ((b * y⁻¹) * y) * m := by group
        _ = (m : Y)⁻¹ * (b * y⁻¹) * (y * m) := by group
        _ = (m : Y)⁻¹ * (b * y⁻¹ * (m : Y)) * ((m : Y)⁻¹ * (y * m)) := by group
        _ = (m : Y)⁻¹ * ((m : Y) * (b * y⁻¹)) * ((m : Y)⁻¹ * (y * m)) := by rw [hc]
        _ = (b * y⁻¹) * ((m : Y)⁻¹ * y * m) := by group
    rw [e]
    exact mul_mem (mul_mem hb (inv_mem hyA)) (hconjA m hnb ⟨y, hyK⟩ hyA)
  ·
    have hmx : (QuotientGroup.mk (m⁻¹ * ⟨x, hxK⟩ * m) : K ⧸ center K) =
        QuotientGroup.mk ⟨x', hx'K⟩ := by
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hnbx
    rw [QuotientGroup.eq] at hmx
    obtain ⟨ζ, hζ⟩ : ∃ ζ : K, (m⁻¹ * ⟨x, hxK⟩ * m)⁻¹ * ⟨x', hx'K⟩ = ζ := ⟨_, rfl⟩
    rw [hζ] at hmx
    have hζc : (ζ : Y) ∈ centralizer (K : Set Y) := mem_centralizer_iff.mpr fun y hy =>
      (congrArg Subtype.val (mem_center_iff.mp hmx ⟨y, hy⟩) : _)
    have hζ' : (m : Y)⁻¹ * x * m = x' * (ζ : Y)⁻¹ := by
      have := congrArg Subtype.val hζ
      simp only [coe_mul, coe_inv] at this
      rw [← this]
      group
    have hc1 : (a' * x'⁻¹)⁻¹ * (a * x⁻¹) ∈ centralizer (K : Set Y) :=
      mul_mem (inv_mem ha'x') hax
    have hcx := mem_centralizer_iff.mp hc1 x' hx'K
    have hcm := mem_centralizer_iff.mp hax (m : Y) m.2
    have e : a'⁻¹ * ((m : Y)⁻¹ * a * (m : Y)⁻¹⁻¹) =
        ((a' * x'⁻¹)⁻¹ * (a * x⁻¹)) * (ζ : Y)⁻¹ := by
      calc a'⁻¹ * ((m : Y)⁻¹ * a * (m : Y)⁻¹⁻¹) =
          a'⁻¹ * ((m : Y)⁻¹ * ((a * x⁻¹) * m) * ((m : Y)⁻¹ * (x * m))) := by group
        _ = a'⁻¹ * ((m : Y)⁻¹ * (m * (a * x⁻¹)) * ((m : Y)⁻¹ * (x * m))) := by rw [hcm]
        _ = a'⁻¹ * (a * x⁻¹) * ((m : Y)⁻¹ * x * m) := by group
        _ = a'⁻¹ * (a * x⁻¹) * (x' * (ζ : Y)⁻¹) := by rw [hζ']
        _ = x'⁻¹ * ((a' * x'⁻¹)⁻¹ * (a * x⁻¹) * x') * (ζ : Y)⁻¹ := by group
        _ = x'⁻¹ * (x' * ((a' * x'⁻¹)⁻¹ * (a * x⁻¹))) * (ζ : Y)⁻¹ := by rw [hcx]
        _ = ((a' * x'⁻¹)⁻¹ * (a * x⁻¹)) * (ζ : Y)⁻¹ := by group
    rw [e]
    exact mul_mem hc1 (inv_mem hζc)

theorem isEmpty_componentIndex_of_singular
    (Sb : Sylow 2 Y) {A : Subgroup Y} (hO : goldschmidtOddCore Y = ⊥)
    (hAS : A ≤ Sb) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAinv : ∀ t ∈ (Sb : Subgroup Y) ⊓ goldschmidtLayer Y, t ^ 2 = 1 → t ∈ A)
    (hAO : CFSG.Open.pCore 2 Y ≤ A)
    (htype : ∀ K : ComponentIndex Y, goldschmidtSimpleType (K.1 ⧸ center K.1))
    (hind : ∀ K : ComponentIndex Y, InducesOmega1 A K.1 Sb)
    (hcover : ∀ K : ComponentIndex Y, ∀ a ∈ A, ∃ x ∈ A ⊓ K.1, ∀ y ∈ K.1,
      a⁻¹ * y * a = x⁻¹ * y * x)
    (hA16 : Nat.card A = 16) (sing : Y → Prop) [DecidablePred sing]
    (hsing : ∀ n : Y, (∀ b ∈ A, n * b * n⁻¹ ∈ A) → ∀ a ∈ A, (sing a ↔ sing (n * a * n⁻¹)))
    (h5 : Nat.card {a : A // sing a ∧ (a : Y) ≠ 1} = 5)
    {H : Type*} [Group H] (σ : H →* MulAut Y) (hσA : ∀ h, ∀ a ∈ A, σ h a ∈ A)
    (horb : ∀ D : Subgroup Y, D ≤ A → Nat.card D = 4 → (∀ h, ∀ d ∈ D, σ h d ∈ D) →
      Nat.card {d : D // sing d ∧ (d : Y) ≠ 1} ≠ 2) :
    IsEmpty (ComponentIndex Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : ∀ K : ComponentIndex Y, A ≤ normalizer (K.1 : Set Y) := fun K =>
    AS81.Qbar.le_normalizer_of_inducesOmega1 Sb (hind K)
  set P : Y → Prop := fun a => sing a ∧ a ≠ 1 with hPdef
  have hPinv : ∀ n : Y, (∀ b ∈ A, n * b * n⁻¹ ∈ A) → ∀ a ∈ A, (P a ↔ P (n * a * n⁻¹)) := by
    intro n hn a ha
    simp only [hPdef]
    rw [hsing n hn a ha]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun he => h2 (by
        calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
          _ = 1 := by rw [he]; group)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun he => h2 (by rw [he]; group)⟩
  have hcomp : ∀ K : ComponentIndex Y, ∃ m : ℕ,
      Nat.card {a : A // P a} = Nat.card {b : ↥(A ⊓ centralizer (K.1 : Set Y)) // P b} +
        ((A ⊓ centralizer (K.1 : Set Y)).relIndex A - 1) * m := by
    intro K
    refine exists_card_eq_add_mul inf_le_left P ?_
    intro x hx hxB x' hx' hx'B
    have hxK : x ∉ centralizer (K.1 : Set Y) := fun h => hxB (mem_inf.mpr ⟨hx, h⟩)
    have hx'K : x' ∉ centralizer (K.1 : Set Y) := fun h => hx'B (mem_inf.mpr ⟨hx', h⟩)
    obtain ⟨n, hnK, hnA, hnx⟩ := exists_conj_mem_of_component Sb hO hAS hA2 hAinv hAO
      ((CFSG.isComponent_iff_open K.1).mp K.2) (htype K) (hcover K) hx hx' hxK hx'K
    refine ⟨n, hnA, fun b hb => ?_, mem_inf.mpr ⟨mul_mem (inv_mem hx') (hnA x hx), hnx⟩,
      fun y hy => hPinv n hnA y hy⟩
    have hc := mem_centralizer_iff.mp (mem_inf.mp hb).2 n hnK
    rw [hc, mul_inv_cancel_right]
    exact hb
  have hker : ∀ K : ComponentIndex Y,
      (AS81.Qbar.conjAutOn K.1 A (hAN K)).ker = (A ⊓ centralizer (K.1 : Set Y)).subgroupOf A := by
    intro K
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    constructor
    · intro h
      refine ⟨a.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h1 := congrArg (fun e : MulAut K.1 => ((e ⟨y, hy⟩ : K.1) : Y)) h
      simp only [AS81.Qbar.conjAutOn_apply, MulAut.one_apply] at h1
      calc y * a = (a : Y) * y * (a : Y)⁻¹ * a := by rw [h1]
        _ = a * y := by group
    · rintro ⟨-, h⟩
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [AS81.Qbar.conjAutOn_apply]
      change (a : Y) * w * (a : Y)⁻¹ = w
      rw [← mem_centralizer_iff.mp h w w.2]
      group
  have h4 : ∀ K : ComponentIndex Y, 4 ≤ (A ⊓ centralizer (K.1 : Set Y)).relIndex A := by
    intro K
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact AS81.Qbar.four_le_card_range Sb K.2 (htype K) (hind K)
  have hmul : ∀ K : ComponentIndex Y, (A ⊓ centralizer (K.1 : Set Y)).relIndex A *
      Nat.card ↥(A ⊓ centralizer (K.1 : Set Y)) = 16 := by
    intro K
    have h1 := Subgroup.relIndex_mul_card (A ⊓ centralizer (K.1 : Set Y)) A
    rwa [inf_assoc, inf_comm _ A, ← inf_assoc, inf_idem, hA16] at h1
  have hlt : ∀ K : ComponentIndex Y, Nat.card {b : ↥(A ⊓ centralizer (K.1 : Set Y)) // P b} <
      Nat.card ↥(A ⊓ centralizer (K.1 : Set Y)) := by
    intro K
    have : Fintype ↥(A ⊓ centralizer (K.1 : Set Y)) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_lt (x := (1 : ↥(A ⊓ centralizer (K.1 : Set Y))))
      (fun h => h.2 rfl)
  have harith : ∀ s w b m : ℕ, 5 = s + (w - 1) * m → w * b = 16 → 4 ≤ w → s < b →
      w = 4 ∧ b = 4 ∧ s = 2 := by
    intro s w b m h1 h2 h3 h4
    have hw : w ≤ 16 := by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · omega
      · nlinarith
    interval_cases w <;> omega
  have hK : ∀ K : ComponentIndex Y, (A ⊓ centralizer (K.1 : Set Y)).relIndex A = 4 ∧
      Nat.card ↥(A ⊓ centralizer (K.1 : Set Y)) = 4 ∧
      Nat.card {b : ↥(A ⊓ centralizer (K.1 : Set Y)) // P b} = 2 := by
    intro K
    obtain ⟨m, hm⟩ := hcomp K
    rw [h5] at hm
    exact harith _ _ _ m hm (hmul K) (h4 K) (hlt K)
  rw [← not_nonempty_iff]
  rintro ⟨K₀⟩
  have hc : 4 ^ Nat.card (ComponentIndex Y) ≤ 16 :=
    hA16 ▸ AS81.Qbar.four_pow_card_componentIndex_le Sb htype hind hcover
  have : Nonempty (ComponentIndex Y) := ⟨K₀⟩
  have hc1 : 1 ≤ Nat.card (ComponentIndex Y) := Nat.card_pos (α := ComponentIndex Y)
  have hc2 : Nat.card (ComponentIndex Y) ≤ 2 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 4) h
    omega
  obtain ⟨-, hB4, hs2⟩ := hK K₀
  rcases (show Nat.card (ComponentIndex Y) = 1 ∨ Nat.card (ComponentIndex Y) = 2 by omega)
    with h1 | h2
  ·
    have hsub : Subsingleton (ComponentIndex Y) :=
      (Nat.card_eq_one_iff_unique.mp h1).1
    refine horb _ inf_le_left hB4 (fun h d hd => ?_) hs2
    obtain ⟨hdA, hdC⟩ := mem_inf.mp hd
    refine mem_inf.mpr ⟨hσA h d hdA, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hK' : AS81.Qbar.compPerm (σ h)⁻¹ K₀ = K₀ := Subsingleton.elim _ _
    have hy' : (σ h)⁻¹ y ∈ K₀.1 := AS81.Qbar.apply_mem_of_compPerm hK' hy
    have hc := mem_centralizer_iff.mp hdC _ hy'
    have e : y = σ h ((σ h)⁻¹ y) := (MulAut.apply_inv_self Y (σ h) y).symm
    rw [e, ← map_mul, ← map_mul, hc]
  ·
    have : Nontrivial (ComponentIndex Y) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨K₁, hK₁⟩ := exists_ne K₀
    have hall : ∀ K : ComponentIndex Y, K = K₀ ∨ K = K₁ := by
      intro K
      by_contra h
      push Not at h
      have h3 : 2 < Fintype.card (ComponentIndex Y) :=
        Fintype.two_lt_card_iff.mpr ⟨K₀, K₁, K, Ne.symm hK₁, Ne.symm h.1, Ne.symm h.2⟩
      rw [← Nat.card_eq_fintype_card, h2] at h3
      omega
    have hW : ∀ K : ComponentIndex Y,
        Nat.card (AS81.Qbar.conjAutOn K.1 A (hAN K)).range = 4 := by
      intro K
      rw [← Subgroup.index_ker, hker, ← Subgroup.relIndex]
      exact (hK K).1
    have hsurj := AS81.Qbar.surjective_conjAutOn_pi hAN hcover
    have : Fintype A := Fintype.ofFinite _
    have hcardpi : Fintype.card ((K : ComponentIndex Y) →
        (AS81.Qbar.conjAutOn K.1 A (hAN K)).range) = Fintype.card A := by
      rw [Fintype.card_pi, ← Nat.card_eq_fintype_card (α := A), hA16]
      simp only [← Nat.card_eq_fintype_card, hW]
      rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, h2]
      norm_num
    have hinj := ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcardpi.symm⟩).1
    have hB01 : ∀ b ∈ A, b ∈ centralizer (K₀.1 : Set Y) → b ∈ centralizer (K₁.1 : Set Y) →
        b = 1 := by
      intro b hb h0 h1
      have hone : ∀ K : ComponentIndex Y, b ∈ centralizer (K.1 : Set Y) →
          AS81.Qbar.conjAutOn K.1 A (hAN K) ⟨b, hb⟩ = 1 := fun K hbK => by
        have : (⟨b, hb⟩ : A) ∈ (AS81.Qbar.conjAutOn K.1 A (hAN K)).ker := by
          rw [hker, mem_subgroupOf]
          exact mem_inf.mpr ⟨hb, hbK⟩
        exact this
      have hfb := hinj (a₁ := ⟨b, hb⟩) (a₂ := 1) (funext fun K => Subtype.ext (by
        show AS81.Qbar.conjAutOn K.1 A (hAN K) ⟨b, hb⟩ = AS81.Qbar.conjAutOn K.1 A (hAN K) 1
        rw [map_one]
        rcases hall K with rfl | rfl
        · exact hone _ h0
        · exact hone _ h1))
      exact congrArg Subtype.val hfb
    have hconst : ∀ b ∈ A ⊓ centralizer (K₀.1 : Set Y), ∀ b' ∈ A ⊓ centralizer (K₀.1 : Set Y),
        b ≠ 1 → b' ≠ 1 → P b → P b' := by
      intro b hb b' hb' hb1 hb'1 hPb
      obtain ⟨hbA, hbC⟩ := mem_inf.mp hb
      obtain ⟨hb'A, hb'C⟩ := mem_inf.mp hb'
      have hbK₁ : b ∉ centralizer (K₁.1 : Set Y) := fun h => hb1 (hB01 b hbA hbC h)
      have hb'K₁ : b' ∉ centralizer (K₁.1 : Set Y) := fun h => hb'1 (hB01 b' hb'A hb'C h)
      obtain ⟨n, hnK, hnA, hnb⟩ := exists_conj_mem_of_component Sb hO hAS hA2 hAinv hAO
        ((CFSG.isComponent_iff_open K₁.1).mp K₁.2) (htype K₁) (hcover K₁) hbA hb'A hbK₁ hb'K₁
      have hnC : n ∈ centralizer (K₀.1 : Set Y) := mem_centralizer_iff.mpr fun y hy =>
        (componentIndex_commute (Ne.symm hK₁) y n hy hnK).eq
      have hnbC : n * b * n⁻¹ ∈ centralizer (K₀.1 : Set Y) :=
        mul_mem (mul_mem hnC hbC) (inv_mem hnC)
      have h1 : b'⁻¹ * (n * b * n⁻¹) = 1 := hB01 _ (mul_mem (inv_mem hb'A) (hnA b hbA))
        (mul_mem (inv_mem hb'C) hnbC) hnb
      have h2' : n * b * n⁻¹ = b' := by
        calc n * b * n⁻¹ = b' * (b'⁻¹ * (n * b * n⁻¹)) := by group
          _ = b' := by rw [h1, mul_one]
      rw [← h2']
      exact (hPinv n hnA b hbA).mp hPb
    have : Fintype ↥(A ⊓ centralizer (K₀.1 : Set Y)) := Fintype.ofFinite _
    by_cases hex : ∃ b : ↥(A ⊓ centralizer (K₀.1 : Set Y)), P b
    · obtain ⟨b₀, hb₀⟩ := hex
      have heq : Nat.card {b : ↥(A ⊓ centralizer (K₀.1 : Set Y)) // P b} =
          Nat.card {b : ↥(A ⊓ centralizer (K₀.1 : Set Y)) // b ≠ 1} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ⟨fun h => ?_, fun h => ?_⟩)
        · exact fun he => h.2 (by rw [he]; rfl)
        · exact hconst _ b₀.2 _ b.2 (fun he => hb₀.2 he)
            (fun he => h (Subtype.ext he)) hb₀
      rw [heq, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        ← Nat.card_eq_fintype_card, hB4] at hs2
      omega
    · push Not at hex
      have h0 : Nat.card {b : ↥(A ⊓ centralizer (K₀.1 : Set Y)) // P b} = 0 := by
        rw [Nat.card_eq_zero]
        left
        exact ⟨fun b => hex b.1 b.2⟩
      omega

end CFSG.ComponentClassification.RankTwoAltFive
