module

public import CFSG.CGT.Stroth77.Section226A
public import CFSG.CGT.Stroth77.Section226Z2Z8
public import CFSG.CGT.Stroth77.Section226Z2Z8Idx

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open Sec226ZIdx

namespace Sec226ZIdx

variable (τ : StrothTypeIndex)

@[expose] def FiveFact : Prop :=
  ∀ v : Torus τ.k, five τ (five τ v) = v ∧ (4 • v = (0 : Torus τ.k) ∨ five τ v ≠ v)

instance : Decidable (FiveFact τ) := by unfold FiveFact; infer_instance

theorem fiveFact_t200 : FiveFact τ₀ := by decide +kernel

theorem fiveFact_t201 : FiveFact τ₁ := by decide +kernel

theorem fiveFact_of {τ : StrothTypeIndex} (hτ : τ = .t200 1 ∨ τ = .t201 1) : FiveFact τ := by
  rcases hτ with rfl | rfl
  exacts [fiveFact_t200, fiveFact_t201]

end Sec226ZIdx

variable {G : Type} [Group G]

namespace StrothFrame.IsD

private theorem conj_eq_of_commute {x g : G} (h : g * x = x * g) : x⁻¹ * g * x = g := by
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem mem_centralizer_of_conj {B : Subgroup G} {x : G}
    (hx : ∀ d ∈ B, x⁻¹ * d * x = d) : x ∈ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  calc d * x = x * (x⁻¹ * d * x) := by group
    _ = x * d := by rw [hx d hd]

variable {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

private theorem conj_mul_eq_of_five (hF : IdxFacts τ) (h5 : FiveFact τ) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (D : Set G)) (hyN : y ∈ Subgroup.normalizer (D : Set G))
    (hx : x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
      x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5)
    (hy : y⁻¹ * (dD.c : G) * y = dD.c ∧ y⁻¹ * (dD.a : G) * y = (dD.a : G) ^ 5 ∧
      y⁻¹ * (dD.b : G) * y = (dD.b : G) ^ 5) {d : G} (hd : d ∈ D) :
    (x * y)⁻¹ * d * (x * y) = d := by
  obtain ⟨v, rfl⟩ := exists_ofTorus_eq dD hd
  calc (x * y)⁻¹ * dD.ofTorus v * (x * y) = y⁻¹ * (x⁻¹ * dD.ofTorus v * x) * y := by group
    _ = dD.ofTorus v := by
      rw [conj_ofTorus_five dD hF hxN hx.1 hx.2.1 hx.2.2,
        conj_ofTorus_five dD hF hyN hy.1 hy.2.1 hy.2.2, (h5 v).1]

private theorem card_inf_centralizer_le_of_five (hF : IdxFacts τ) (h5 : FiveFact τ)
    (hcard4 : Nat.card {w : Torus τ.k // 4 • w = (0 : Torus τ.k)} ≤ 32) {x : G}
    (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hx : x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
      x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5) :
    Nat.card ↥(D ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 32 := by
  have hfix : ∀ d ∈ D ⊓ Subgroup.centralizer ({x} : Set G), ∀ hd : d ∈ D,
      4 • dD.e (Additive.ofMul (⟨d, hd⟩ : D)) = (0 : Torus τ.k) := by
    intro d hdC hdD
    have hdv : dD.ofTorus (dD.e (Additive.ofMul (⟨d, hdD⟩ : D))) = d := dD.ofTorus_e ⟨d, hdD⟩
    have hfv : five τ (dD.e (Additive.ofMul (⟨d, hdD⟩ : D))) =
        dD.e (Additive.ofMul (⟨d, hdD⟩ : D)) := by
      apply dD.ofTorus_injective
      rw [← conj_ofTorus_five dD hF hxN hx.1 hx.2.1 hx.2.2, hdv]
      exact conj_eq_of_commute
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hdC).2)
    exact (h5 _).2.resolve_right (not_not_intro hfv)
  let f : ↥(D ⊓ Subgroup.centralizer ({x} : Set G)) → {w : Torus τ.k // 4 • w = (0 : Torus τ.k)} :=
    fun d => ⟨_, hfix d.1 d.2 (Subgroup.mem_inf.mp d.2).1⟩
  have hf : Function.Injective f := by
    intro d₁ d₂ h12
    apply Subtype.ext
    calc (d₁ : G) = dD.ofTorus (f d₁).1 := (dD.ofTorus_e ⟨d₁, (Subgroup.mem_inf.mp d₁.2).1⟩).symm
      _ = dD.ofTorus (f d₂).1 := by rw [h12]
      _ = d₂ := dD.ofTorus_e ⟨d₂, (Subgroup.mem_inf.mp d₂.2).1⟩
  exact (Nat.card_le_card_of_injective f hf).trans hcard4

variable [Finite G] {F : StrothFrame G}

private theorem relIndex_le_two_of_t2m1 (h : F.IsD D dD) (hF : IdxFacts τ) (h5 : FiveFact τ)
    (hCA : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((F.A : Subgroup G) : Set G),
      (∀ d ∈ D, x⁻¹ * d * x = d) ∨
      (x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
        x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5)) :
    D.relIndex ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((F.A : Subgroup G) : Set G)) ≤ 2 := by
  refine Nat.le_of_dvd two_pos (Subgroup.relIndex_dvd_two_iff'.mpr ?_)
  have hfive : ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((F.A : Subgroup G) : Set G), y ∉ D →
      y⁻¹ * (dD.c : G) * y = dD.c ∧ y⁻¹ * (dD.a : G) * y = (dD.a : G) ^ 5 ∧
        y⁻¹ * (dD.b : G) * y = (dD.b : G) ^ 5 := fun y hy hyD =>
    (hCA y hy).resolve_left fun h1 =>
      hyD (h.mem_of_mem_centralizer (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).1
        (mem_centralizer_of_conj h1))
  by_cases hall : ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((F.A : Subgroup G) : Set G), y ∈ D
  · exact ⟨1, one_mem _, fun b hb => Or.inr (hall b hb)⟩
  push Not at hall
  obtain ⟨x₀, hx₀, hx₀D⟩ := hall
  refine ⟨x₀, hx₀, fun y hy => ?_⟩
  by_cases hyD : y ∈ D
  · exact Or.inr hyD
  left
  obtain ⟨hx₀S, hx₀N⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx₀).1
  obtain ⟨hyS, hyN⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1
  exact h.mem_of_mem_centralizer (mul_mem hx₀S hyS) (mem_centralizer_of_conj fun d hd =>
    conj_mul_eq_of_five hF h5 hx₀N hyN (hfive x₀ hx₀ hx₀D) (hfive y hy hyD) hd)

theorem false_of_le_R_of_t2m1 (h : F.IsD D dD)
    (hτ : τ = .t200 1 ∨ τ = .t201 1)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) {B : Subgroup G}
    (hBR : B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hcard : Nat.card B = Nat.card D) (hne : B ≠ D) :
    False := by
  have hF := idxFacts_of hτ
  have h5 := fiveFact_of hτ
  have hcard4 : Nat.card {w : Torus τ.k // 4 • w = (0 : Torus τ.k)} ≤ 32 := by
    rcases hτ with rfl | rfl
    exacts [Sec226Z.card4_t200, Sec226Z.card4_t201]
  have hD : Nat.card D = 128 := by
    rw [dD.card]
    rcases hτ with rfl | rfl <;> rfl
  have hCA : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((F.A : Subgroup G) : Set G),
      (∀ d ∈ D, x⁻¹ * d * x = d) ∨
      (x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
        x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5) :=
    fun x hx => h.conj_eq_of_mem_centralizer_A_of_t2m1 hτ hns hx
  have hne0 : ∀ K : Subgroup G, D.relIndex K ≠ 0 := fun K =>
    (Subgroup.isFiniteRelIndex_of_finiteIndex (H := D) (K := K)).relIndex_ne_zero
  have hKR : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((F.A : Subgroup G) : Set G) ≤
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) :=
    inf_le_inf_left _ h.centralizer_A_le
  have hDK : D ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((F.A : Subgroup G) : Set G) := fun d hd =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h.le_S hd, Subgroup.le_normalizer hd⟩,
      h.mem_centralizer_A_of_mem hd⟩
  have hDK2 := relIndex_le_two_of_t2m1 h hF h5 hCA
  have hDR4 : D.relIndex ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) ≤ 4 := by
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hDK hKR]
    exact Nat.mul_le_mul hDK2 (h.relIndex_centralizer_A_le_two_of_t2m1 hτ hCA)
  by_cases hBA : B ≤ Subgroup.centralizer ((F.A : Subgroup G) : Set G)
  ·
    have hBK : B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((F.A : Subgroup G) : Set G) := fun y hy =>
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (hBR hy)).1, hBA hy⟩
    have hBD : ¬ B ≤ D := fun hle => hne (Subgroup.eq_of_le_of_card_ge hle hcard.ge)
    obtain ⟨x, hxB, hxD⟩ := SetLike.not_le_iff_exists.mp hBD
    have hxK := hBK hxB
    obtain ⟨hxS, hxN⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hxK).1
    have hx5 := (hCA x hxK).resolve_left fun h1 =>
      hxD (h.mem_of_mem_centralizer hxS (mem_centralizer_of_conj h1))
    have h32 := card_inf_centralizer_le_of_five hF h5 hcard4 hxN hx5
    have hidx : D.relIndex B ≤ 2 := (Subgroup.relIndex_le_of_le_right hBK (hne0 _)).trans hDK2
    exact false_of_relIndex_mul_card_lt hB hcard hxB hidx (by omega)
  ·
    obtain ⟨x, hxB, hxA⟩ := SetLike.not_le_iff_exists.mp hBA
    have hle := Subgroup.card_le_of_le (h.inf_centralizer_le_omegaIn_of_t2m1 hτ hCA (hBR hxB) hxA)
    have h8 : Nat.card ↥(omegaIn 1 D) = 8 := by
      rw [h.omegaIn_one_eq]
      exact F.card_omegaIn_one_A
    have hidx : D.relIndex B ≤ 4 := (Subgroup.relIndex_le_of_le_right hBR (hne0 _)).trans hDR4
    exact false_of_relIndex_mul_card_lt hB hcard hxB hidx (by omega)

end StrothFrame.IsD

end CFSG.CGT.Stroth77
