module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveStar

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

@[expose] def HasType (D : Subgroup G) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (t k : G) : Prop :=
  ∃ i, aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i))
    (k * t * k⁻¹)

theorem hasType_unique (hC : Counterexample G D r Abar) {t k k' : G}
    (ht2 : ∃ n : ℕ, t ^ (2 ^ n) = 1) (ht1 : t ≠ 1) (hk : HasType D Abar t k)
    (hk' : HasType D Abar t k') : k * k'⁻¹ ∈ Subgroup.normalizer (D : Set G) := by
  obtain ⟨i, hi⟩ := hk
  obtain ⟨j, hj⟩ := hk'
  have hne : k * t * k⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  refine mem_normalizer_of_fusion hC i j (t := k * t * k⁻¹) (g := k * k'⁻¹)
    (twoElt_conj ht2 k) hne hi ?_
  have : (k * k'⁻¹)⁻¹ * (k * t * k⁻¹) * (k * k'⁻¹) = k' * t * k'⁻¹ := by group
  rw [this]
  exact hj

omit [Finite G] in
theorem hasType_conj {t k : G} (h : HasType D Abar t k) (x : G) :
    HasType D Abar (x⁻¹ * t * x) (k * x) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  have : k * x * (x⁻¹ * t * x) * (k * x)⁻¹ = k * t * k⁻¹ := by group
  rw [this]
  exact hi

theorem hasType_of_mem_factor (hC : Counterexample G D r Abar) {a : Fin r} {t : G}
    (ht : t ∈ aschbacherThm5Preimage D (Abar a)) : HasType D Abar t 1 := by
  obtain ⟨b, hba⟩ := exists_other hC a
  refine ⟨b, ?_⟩
  rw [one_mul, inv_one, mul_one]
  exact cross_factor_centralizes D Abar hC.hyp.hcomm b a hba t ht

theorem hasType_of_mem_conj_factor (hC : Counterexample G D r Abar) {a : Fin r} {g t : G}
    (ht : t ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) g) : HasType D Abar t g := by
  obtain ⟨b, hba⟩ := exists_other hC a
  rw [mem_rightConjugate_iff] at ht
  exact ⟨b, cross_factor_centralizes D Abar hC.hyp.hcomm b a hba _ ht⟩

theorem le_rightConjugate_of_spread (hC : Counterexample G D r Abar)
    {K X Y Y₁ Z : Subgroup G} {κX κY κZ : G} (hK2 : IsPGroup 2 K) (hXK : X ≤ K)
    (hYK : Y ≤ K) (hcard : Nat.card K = Nat.card X * Nat.card Y)
    (hXY : Nat.card X = Nat.card Y) (hY₁K : Y₁ ≤ Subgroup.normalizer (K : Set G))
    (hY₁ : Nat.card Y₁ = Nat.card Y)
    (htX : ∀ x ∈ X, x ≠ 1 → HasType D Abar x κX)
    (htY : ∀ y ∈ Y, y ≠ 1 → HasType D Abar y κY)
    (hdist : ∀ y₁ ∈ Y₁, ∀ y₁' ∈ Y₁, κY * y₁ * (κY * y₁')⁻¹ ∈ Subgroup.normalizer (D : Set G) →
      y₁ = y₁')
    (hdistX : ∀ y₁ ∈ Y₁, κY * y₁ * κX⁻¹ ∉ Subgroup.normalizer (D : Set G))
    (hZK : Z ≤ K) (hZX : Z ⊓ X = ⊥) (htZ : ∀ z ∈ Z, z ≠ 1 → HasType D Abar z κZ) :
    ∃ y₁ ∈ Y₁, Z ≤ rightConjugate Y y₁ := by
  classical
  have hmemK : ∀ y₁ ∈ Y₁, ∀ y ∈ Y, y₁⁻¹ * y * y₁ ∈ K := fun y₁ hy₁ y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hY₁K hy₁)) y).mp (hYK hy)
    simpa using this
  have htype : ∀ y₁ ∈ Y₁, ∀ y ∈ Y, y ≠ 1 → HasType D Abar (y₁⁻¹ * y * y₁) (κY * y₁) :=
    fun y₁ _ y hy hy1 => hasType_conj (htY y hy hy1) y₁
  have hne1 : ∀ y₁ y : G, y ≠ 1 → y₁⁻¹ * y * y₁ ≠ 1 := fun y₁ y hy h => by
    apply hy
    calc y = y₁ * (y₁⁻¹ * y * y₁) * y₁⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hnotX : ∀ y₁ ∈ Y₁, ∀ y ∈ Y, y ≠ 1 → y₁⁻¹ * y * y₁ ∉ X := by
    intro y₁ hy₁ y hy hy1 hX
    have h1 := hasType_unique hC (twoElt_of_mem hK2 (hmemK y₁ hy₁ y hy)) (hne1 y₁ y hy1)
      (htype y₁ hy₁ y hy hy1) (htX _ hX (hne1 y₁ y hy1))
    exact hdistX y₁ hy₁ h1
  let Φ : Y₁ × {y : Y // y ≠ 1} → {k : K // (k : G) ∉ X} := fun p =>
    ⟨⟨(p.1 : G)⁻¹ * (p.2 : Y) * p.1, hmemK p.1 p.1.2 _ (p.2 : Y).2⟩,
      hnotX p.1 p.1.2 _ (p.2 : Y).2 (fun h => p.2.2 (Subtype.ext h))⟩
  have hΦinj : Function.Injective Φ := by
    rintro ⟨y₁, y, hy⟩ ⟨y₁', y', hy'⟩ heq
    have heq' : (y₁ : G)⁻¹ * (y : G) * y₁ = (y₁' : G)⁻¹ * (y' : G) * y₁' :=
      congrArg (fun k : {k : K // (k : G) ∉ X} => ((k : K) : G)) heq
    have hy1 : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
    have hy1' : (y' : G) ≠ 1 := fun h => hy' (Subtype.ext h)
    have h1 := htype y₁ y₁.2 y y.2 hy1
    have h2 := htype y₁' y₁'.2 y' y'.2 hy1'
    rw [← heq'] at h2
    have h3 := hasType_unique hC (twoElt_of_mem hK2 (hmemK y₁ y₁.2 y y.2)) (hne1 _ _ hy1) h1 h2
    have h4 : y₁ = y₁' := Subtype.ext (hdist y₁ y₁.2 y₁' y₁'.2 h3)
    subst h4
    have h5 : (y : G) = y' := by
      have := congrArg (fun x => (y₁ : G) * x * (y₁ : G)⁻¹) heq'
      simpa [mul_assoc] using this
    have h6 : y = y' := Subtype.ext h5
    subst h6
    rfl
  have hcardΦ : Nat.card {k : K // (k : G) ∉ X} ≤ Nat.card (Y₁ × {y : Y // y ≠ 1}) := by
    have h1 : Nat.card {k : K // (k : G) ∉ X} = Nat.card K - Nat.card X := by
      have := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Nat.card_eq_fintype_card]
      congr 1
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hXK).toEquiv)
    have h2 : Nat.card {y : Y // y ≠ 1} = Nat.card Y - 1 := by
      have := Fintype.ofFinite Y
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq]
    rw [Nat.card_prod, h1, h2, hcard, hY₁, hXY, Nat.mul_sub_one]
  have hΦsurj := (hΦinj.bijective_of_nat_card_le hcardΦ).2
  by_cases hZ : Z = ⊥
  · exact ⟨1, Y₁.one_mem, by rw [hZ]; exact bot_le⟩
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hnot : ∀ z ∈ Z, z ≠ 1 → z ∉ X := fun z hz hz1 hzX => by
    have : z ∈ Z ⊓ X := ⟨hz, hzX⟩
    rw [hZX, Subgroup.mem_bot] at this
    exact hz1 this
  obtain ⟨⟨y₁₀, y₀, hy₀⟩, hΦ₀⟩ := hΦsurj ⟨⟨z₀, hZK hz₀⟩, hnot z₀ hz₀ hz₀1'⟩
  have hz₀eq : (y₁₀ : G)⁻¹ * (y₀ : G) * y₁₀ = z₀ :=
    congrArg (fun k : {k : K // (k : G) ∉ X} => ((k : K) : G)) hΦ₀
  have hy₀1 : (y₀ : G) ≠ 1 := fun h => hy₀ (Subtype.ext h)
  have hτ₀ : κY * y₁₀ * κZ⁻¹ ∈ Subgroup.normalizer (D : Set G) := by
    have h1 := htype y₁₀ y₁₀.2 y₀ y₀.2 hy₀1
    rw [hz₀eq] at h1
    exact hasType_unique hC (twoElt_of_mem hK2 (hZK hz₀)) hz₀1' h1 (htZ z₀ hz₀ hz₀1')
  refine ⟨y₁₀, y₁₀.2, fun z hz => ?_⟩
  by_cases hz1 : z = 1
  · rw [hz1]
    exact (rightConjugate Y y₁₀).one_mem
  obtain ⟨⟨y₁, y, hy⟩, hΦz⟩ := hΦsurj ⟨⟨z, hZK hz⟩, hnot z hz hz1⟩
  have hzeq : (y₁ : G)⁻¹ * (y : G) * y₁ = z :=
    congrArg (fun k : {k : K // (k : G) ∉ X} => ((k : K) : G)) hΦz
  have hy1 : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
  have hτ : κY * y₁ * κZ⁻¹ ∈ Subgroup.normalizer (D : Set G) := by
    have h1 := htype y₁ y₁.2 y y.2 hy1
    rw [hzeq] at h1
    exact hasType_unique hC (twoElt_of_mem hK2 (hZK hz)) hz1 h1 (htZ z hz hz1)
  have hy₁eq : y₁ = y₁₀ := by
    refine Subtype.ext (hdist y₁ y₁.2 y₁₀ y₁₀.2 ?_)
    have : κY * y₁ * (κY * y₁₀)⁻¹ = (κY * y₁ * κZ⁻¹) * (κY * y₁₀ * κZ⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hτ (Subgroup.inv_mem _ hτ₀)
  subst hy₁eq
  rw [← hzeq, mem_rightConjugate_iff]
  have : (y₁ : G) * ((y₁ : G)⁻¹ * (y : G) * y₁) * (y₁ : G)⁻¹ = y := by group
  rw [this]
  exact y.2

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
