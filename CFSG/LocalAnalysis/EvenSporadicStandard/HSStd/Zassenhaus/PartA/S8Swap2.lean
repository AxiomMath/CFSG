module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Swap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Layer

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Swapped

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem center_eq_bot_of_simple {J : Type*} [Group J] (hJs : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) : center J = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center J) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    exact absurd (mem_center_iff.mp (by rw [h]; exact mem_top b) a) hab

theorem swapped_structure {t : Γ} (ht : t * t = 1) {J : Subgroup Γ} (hJs : IsSimpleGroup J)
    (hJna : ∃ a b : ↥J, a * b ≠ b * a)
    (hJp : ⁅J, J⁆ = J) (hJt : ∀ j ∈ J, j * t = t * j)
    (hHJ : ∀ Q : Subgroup Γ, Q ≤ layer Γ → (∀ q ∈ Q, q * t = t * q) → ⁅Q, Q⁆ = Q → Q ≤ J)
    {K : Subgroup Γ} (hK : IsComponent K) (hne : cj t K ≠ K)
    (hlayer : layer Γ = K ⊔ cj t K) (hJN : J ≤ K ⊔ cj t K) :
    (∀ x ∈ K, ∀ y ∈ K, x * (t * y * t⁻¹) = (t * y * t⁻¹) * x) ∧
    Nonempty (↥K ⧸ center ↥K ≃* ↥J) ∧
    (∀ z : ↥K, z ∈ center ↥K → t * (z : Γ) * t⁻¹ = (z : Γ)⁻¹ ∧ (z : Γ) ∈ cj t K) ∧
    (∀ k ∈ K, k * (t * k * t⁻¹) ∈ J) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hK' := isComponent_cj t hK
  have hcen : K ≤ Subgroup.centralizer ((cj t K : Subgroup Γ) : Set Γ) :=
    le_centralizer_of_ne hK hK' hne.symm
  have hcomm : ∀ x ∈ K, ∀ y ∈ cj t K, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (hcen hx) y hy).symm
  have hc : ∀ x ∈ K, ∀ y ∈ K, x * (t * y * t⁻¹) = (t * y * t⁻¹) * x := fun x hx y hy =>
    hcomm x hx _ ⟨y, hy, rfl⟩
  set φ := diagMap t K hc with hφ
  have hφapp : ∀ k : ↥K, φ k = (k : Γ) * (t * k * t⁻¹) := fun k => rfl
  have hKperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
    have := hK.1.1
    rw [Group.isPerfect_def, _root_.commutator_def] at this
    exact this
  have hrange_layer : ∀ q ∈ φ.range, q ∈ layer Γ := by
    rintro _ ⟨k, rfl⟩
    rw [hφapp, hlayer]
    exact mul_mem (mem_sup_left k.2) (mem_sup_right ⟨k, k.2, rfl⟩)
  have hrange_t : ∀ q ∈ φ.range, q * t = t * q := by
    rintro _ ⟨k, rfl⟩
    rw [hφapp]
    have e : t * ((k : Γ) * (t * k * t⁻¹)) * t⁻¹ = (t * k * t⁻¹) * k := by
      rw [hti]
      calc t * (↑k * (t * ↑k * t)) * t = (t * ↑k * t) * ↑k * (t * t) := by group
        _ = (t * ↑k * t) * ↑k := by rw [ht]; group
    have e2 : (t * k * t⁻¹ : Γ) * k = (k : Γ) * (t * k * t⁻¹) := (hc k k.2 k k.2).symm
    have : t * ((k : Γ) * (t * k * t⁻¹)) * t⁻¹ = (k : Γ) * (t * k * t⁻¹) := by rw [e, e2]
    calc ((k : Γ) * (t * k * t⁻¹)) * t = (t * ((k : Γ) * (t * k * t⁻¹)) * t⁻¹) * t := by rw [this]
      _ = t * ((k : Γ) * (t * k * t⁻¹)) := by group
  have hrange_perf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hKperf]
  have hrange_J : φ.range ≤ J := hHJ _ (fun q hq => hrange_layer q hq) hrange_t hrange_perf
  have hcN : ∀ c ∈ K ⊓ cj t K, ∀ y ∈ K ⊔ cj t K, c * y = y * c := by
    intro c hc' y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hy
    have h1 : c * a = a * c := (hcomm a ha c hc'.2).symm
    have h2 : c * b = b * c := hcomm c hc'.1 b hb
    calc c * (a * b) = (c * a) * b := by group
      _ = a * (c * b) := by rw [h1]; group
      _ = a * (b * c) := by rw [h2]
      _ = a * b * c := by group
  have hJ1 : ∀ j ∈ J, ∃ k : ↥K, ∃ c ∈ K ⊓ cj t K, j = φ k * c := by
    intro j hj
    obtain ⟨k, hk, k'', hk'', rfl⟩ := exists_mul_of_mem_sup hcomm (hJN hj)
    have hk2 : t * k'' * t⁻¹ ∈ K := (mem_cj ht).1 hk''
    have hk1 : t * k * t⁻¹ ∈ cj t K := ⟨k, hk, rfl⟩
    have e1 : (t * k * t⁻¹) * (t * k'' * t⁻¹) = k * k'' := by
      calc (t * k * t⁻¹) * (t * k'' * t⁻¹) = t * (k * k'') * t⁻¹ := by group
        _ = k * k'' := by rw [← hJt _ hj]; group
    have e2 : (t * k'' * t⁻¹) * (t * k * t⁻¹) = k * k'' := by
      rw [hcomm _ hk2 _ hk1]; exact e1
    have hc0 : k⁻¹ * (t * k'' * t⁻¹) = k'' * (t * k * t⁻¹)⁻¹ := by
      calc k⁻¹ * (t * k'' * t⁻¹) = k⁻¹ * ((t * k'' * t⁻¹) * (t * k * t⁻¹)) * (t * k * t⁻¹)⁻¹ := by group
        _ = _ := by rw [e2]; group
    set c₀ : Γ := k⁻¹ * (t * k'' * t⁻¹) with hc₀
    have hc0K : c₀ ∈ K := mul_mem (inv_mem hk) hk2
    have hc0K' : c₀ ∈ cj t K := by rw [hc0]; exact mul_mem hk'' (inv_mem hk1)
    have hc1K' : t * c₀ * t⁻¹ ∈ cj t K := ⟨c₀, hc0K, rfl⟩
    have hc1K : t * c₀ * t⁻¹ ∈ K := (mem_cj ht).1 hc0K'
    refine ⟨⟨k, hk⟩, t * c₀ * t⁻¹, ⟨hc1K, hc1K'⟩, ?_⟩
    rw [hφapp]
    have e3 : k'' = (t * k * t⁻¹) * (t * c₀ * t⁻¹) := by
      have : k'' = t * (t * k'' * t⁻¹) * t⁻¹ := by
        rw [hti]; calc k'' = (t * t) * k'' * (t * t) := by rw [ht]; group
          _ = _ := by group
      rw [this]
      have : t * k'' * t⁻¹ = k * c₀ := by rw [hc₀]; group
      rw [this]; group
    simp only
    conv_lhs => rw [e3]
    group
  have hJ_range : J ≤ φ.range := by
    calc J = ⁅J, J⁆ := hJp.symm
      _ ≤ φ.range := by
        refine Subgroup.commutator_le.mpr fun j hj j' hj' => ?_
        obtain ⟨k, c, hc1, rfl⟩ := hJ1 j hj
        obtain ⟨k', c', hc1', rfl⟩ := hJ1 j' hj'
        have hφk : ∀ x : ↥K, φ x ∈ K ⊔ cj t K := fun x => by
          rw [hφapp]; exact mul_mem (mem_sup_left x.2) (mem_sup_right ⟨x, x.2, rfl⟩)
        rw [comm_mul_central (hcN c hc1 _ (hφk k')) (hcN c' hc1' _ (hφk k))
          (hcN c' hc1' c (mem_sup_left hc1.1))]
        exact ⟨⁅k, k'⁆, map_commutatorElement φ k k'⟩
  have hrJ : φ.range = J := le_antisymm hrange_J hJ_range
  have hcJ : center ↥J = ⊥ := center_eq_bot_of_simple hJs hJna
  have hker1 : ∀ z : ↥K, φ z = 1 → (z : Γ) ∈ cj t K := by
    intro z hz
    have h1 : (z : Γ) * (t * z * t⁻¹) = 1 := hz
    have h2 : t * (z : Γ) * t⁻¹ = (z : Γ)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [mem_cj ht, h2]
    exact inv_mem z.2
  have hker : φ.ker = center ↥K := by
    ext z
    constructor
    · intro hz
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2 z (hker1 z hz))
    · intro hz
      rw [MonoidHom.mem_ker]
      have hzJ : φ z ∈ J := hrange_J ⟨z, rfl⟩
      have : (⟨φ z, hzJ⟩ : ↥J) ∈ center ↥J := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : (g : Γ) ∈ φ.range := hrJ.symm ▸ g.2
        obtain ⟨k, hk⟩ := hg
        apply Subtype.ext
        show (g : Γ) * φ z = φ z * (g : Γ)
        rw [← hk, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k]
      rw [hcJ, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
  refine ⟨hc, ⟨?_⟩, ?_, fun k hk => hrange_J ⟨⟨k, hk⟩, rfl⟩⟩
  · exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrJ))
  · intro z hz
    have hz1 : φ z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hz
    have h1 : (z : Γ) * (t * z * t⁻¹) = 1 := hz1
    exact ⟨eq_inv_of_mul_eq_one_right h1, hker1 z hz1⟩

end Swapped

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
