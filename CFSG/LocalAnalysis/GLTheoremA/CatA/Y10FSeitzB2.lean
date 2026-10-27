module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


theorem isPGroup_map_hom {X Y : Type} [Group X] [Group Y] {p : ℕ} (f : X →* Y) {T : Subgroup X}
    (hT : IsPGroup p ↥T) : IsPGroup p ↥(T.map f) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
  obtain ⟨n, hn⟩ := hT ⟨x, hx⟩
  refine ⟨n, Subtype.ext ?_⟩
  have h1 : x ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
  show (y : Y) ^ (p ^ n) = 1
  rw [← hxy, ← map_pow, h1, map_one]

theorem mem_center_of_commutators_central' {J : Type} [Group J] (hperf : Group.IsPerfect J) {x : J}
    (hx : ∀ y : J, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center J) : x ∈ Subgroup.center J := by
  let φ : J →* J :=
    { toFun := fun y => x * y * x⁻¹ * y⁻¹
      map_one' := by simp
      map_mul' := fun y w => by
        have hw := Subgroup.mem_center_iff.mp (hx w) y
        calc x * (y * w) * x⁻¹ * (y * w)⁻¹
            = (x * y * x⁻¹ * y⁻¹) * (y * (x * w * x⁻¹ * w⁻¹) * y⁻¹) := by group
          _ = (x * y * x⁻¹ * y⁻¹) * (x * w * x⁻¹ * w⁻¹) := by rw [hw]; group }
  have hφ : ∀ y, φ y = x * y * x⁻¹ * y⁻¹ := fun y => rfl
  have hle : commutator J ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h : φ b * φ a = φ a * φ b := Subgroup.mem_center_iff.mp (hx a) (φ b)
    simp only [commutatorElement_def, MonoidHom.mem_ker, map_mul, map_inv]
    calc φ a * φ b * (φ a)⁻¹ * (φ b)⁻¹ = φ b * φ a * (φ a)⁻¹ * (φ b)⁻¹ := by rw [h]
      _ = 1 := by group
  rw [Group.IsPerfect.commutator_eq_top] at hle
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : φ y = 1 := hle (Subgroup.mem_top y)
  rw [hφ] at h1
  calc y * x = (x * y * x⁻¹ * y⁻¹) * (y * x) := by rw [h1]; group
    _ = x * y := by group

theorem quotEquiv_of_perfect_central {J K : Type} [Group J] [Group K] (φ : J →* K)
    (hφ : Function.Surjective φ) (hperf : Group.IsPerfect J) (hker : φ.ker ≤ Subgroup.center J) :
    Nonempty ((J ⧸ Subgroup.center J) ≃* (K ⧸ Subgroup.center K)) := by
  let ψ : J →* K ⧸ Subgroup.center K := (QuotientGroup.mk' (Subgroup.center K)).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hψker : ψ.ker = Subgroup.center J := by
    apply le_antisymm
    · intro x hx
      have hxK : φ x ∈ Subgroup.center K := by
        have h1 : QuotientGroup.mk' (Subgroup.center K) (φ x) = 1 := hx
        exact (QuotientGroup.eq_one_iff _).mp h1
      apply mem_center_of_commutators_central' hperf
      intro y
      apply hker
      simp only [MonoidHom.mem_ker, map_mul, map_inv]
      have h := Subgroup.mem_center_iff.mp hxK (φ y)
      calc φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹ = φ y * φ x * (φ x)⁻¹ * (φ y)⁻¹ := by rw [← h]
        _ = 1 := by group
    · intro x hx
      have hc : φ x ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := hφ g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
      exact (QuotientGroup.eq_one_iff _).mpr hc
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem isChevSimple_two_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsChevSimple 2 B) : IsChevSimple 2 A := by
  rcases h with ⟨i, hi, ⟨e'⟩⟩ | ⟨i, hi, ⟨e'⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.trans e'⟩⟩

theorem eq_one_of_central_two_power {Kb : Type} [Group Kb] [Finite Kb] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hbot : GLAPPrimeCore p Kb = ⊥) {z : Kb} (hz : z ∈ Subgroup.center Kb) {n : ℕ}
    (hzn : z ^ (2 ^ n) = 1) : z = 1 := by
  have hnorm : (Subgroup.zpowers z).Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have : g * z ^ m * g⁻¹ = z ^ m := by
      have hc := Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hz m) g
      calc g * z ^ m * g⁻¹ = z ^ m * g * g⁻¹ := by rw [hc]
        _ = z ^ m := by group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) m
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers]
    have hd : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hzn
    refine Nat.Coprime.coprime_dvd_right hd ?_
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hle : Subgroup.zpowers z ≤ GLAPPrimeCore p Kb := le_sSup ⟨hnorm, hcop⟩
  rw [hbot] at hle
  exact Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers z))

end CFSG.LocalAnalysis.GLTheoremA.Y10F
