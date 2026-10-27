module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.Heisenberg
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.NormalizingCoreTwo

public section

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Open CFSG.AGLEmbedding.Norton.OrdinaryProofs
open scoped commutatorElement

section Algebra

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  let f : H → H := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have e : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel e))
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hinj ⟨g * x * g⁻¹, hx⟩
  have e : g * (y : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hy
  have hyx : (y : G) = x := mul_left_cancel (mul_right_cancel e)
  rw [← hyx]
  exact y.2

theorem mem_normalizer_closure_pair [Finite G] {a b g : G}
    (ha : g * a * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G))
    (hb : g * b * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({a, b} : Set G) : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro x hx
  have hle : Subgroup.closure ({a, b} : Set G) ≤
      (Subgroup.closure ({a, b} : Set G)).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hb
  exact hle hx

theorem conj_mem_of_mul_eq {H : Subgroup G} {g s n : G} (hn : n ∈ H) (h : g * s = n * g) :
    g * s * g⁻¹ ∈ H := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]
  exact hn

end Algebra

variable {G : Type*} [Group G] [Finite G]

theorem mem_closure_of_comm_relation {x y z : G} (hz13 : z ^ 13 = 1)
    (hcomm : y * x = x * (y * z ^ 4)) : z ∈ Subgroup.closure ({x, y} : Set G) := by
  have hxS : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyS : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hz4 : z ^ 4 = y⁻¹ * x⁻¹ * y * x := by
    calc z ^ 4 = y⁻¹ * x⁻¹ * (x * (y * z ^ 4)) := by group
      _ = y⁻¹ * x⁻¹ * (y * x) := by rw [hcomm]
      _ = y⁻¹ * x⁻¹ * y * x := by group
  have hz4S : z ^ 4 ∈ Subgroup.closure ({x, y} : Set G) := by
    rw [hz4]
    exact mul_mem (mul_mem (mul_mem (inv_mem hyS) (inv_mem hxS)) hyS) hxS
  have hz40 : z ^ 40 = z := by
    have : z ^ 40 = (z ^ 13) ^ 3 * z := by rw [← pow_mul, ← pow_succ]
    rw [this, hz13]
    simp
  have : z = (z ^ 4) ^ 10 := by rw [← pow_mul]; exact hz40.symm
  rw [this]
  exact pow_mem hz4S _

theorem glbCore_two_thirteen_of_heisenberg {x y z : G} (hx : x ^ 13 = 1) (hy : y ^ 13 = 1)
    (hz13 : z ^ 13 = 1) (hzx : z * x = x * z) (hzy : z * y = y * z)
    (hcomm : y * x = x * (y * z ^ 4)) (hz1 : z ≠ 1) {T : Set G} (hT : Subgroup.closure T = ⊤)
    (hN : ∀ g ∈ T, g ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set G) : Set G) ∨
      g ∈ Subgroup.normalizer (Subgroup.closure ({z, y} : Set G) : Set G)) :
    ∀ P : Sylow 13 G, GLBCore 13 2 (P : Subgroup G) = ⊤ := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hxS : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyS : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hzA : z ∈ Subgroup.closure ({z, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyA : y ∈ Subgroup.closure ({z, y} : Set G) := Subgroup.subset_closure (by simp)
  have hz40 : z ^ 40 = z := by
    have : z ^ 40 = (z ^ 13) ^ 3 * z := by rw [← pow_mul, ← pow_succ]
    rw [this, hz13]
    simp
  have hzS : z ∈ Subgroup.closure ({x, y} : Set G) := mem_closure_of_comm_relation hz13 hcomm
  have hAS : Subgroup.closure ({z, y} : Set G) ≤ Subgroup.closure ({x, y} : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hzS
    · exact hyS
  have hzx' : Commute z x := hzx
  have hzy' : Commute z y := hzy
  have hwx : Commute (z ^ 4)⁻¹ x := (hzx'.pow_left 4).inv_left
  have hwy : Commute (z ^ 4)⁻¹ y := (hzy'.pow_left 4).inv_left
  have hxy : x * y = y * x * (z ^ 4)⁻¹ := by
    calc x * y = x * (y * z ^ 4) * (z ^ 4)⁻¹ := by group
      _ = y * x * (z ^ 4)⁻¹ := by rw [← hcomm]
  have hK : ⁅x, y⁆ = (z ^ 4)⁻¹ := by
    have h1 : x * (z ^ 4)⁻¹ * x⁻¹ = (z ^ 4)⁻¹ := by rw [← hwx.eq, mul_inv_cancel_right]
    have h2 : y * (z ^ 4)⁻¹ * y⁻¹ = (z ^ 4)⁻¹ := by rw [← hwy.eq, mul_inv_cancel_right]
    calc ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := by rw [commutatorElement_def]
      _ = y * x * (z ^ 4)⁻¹ * x⁻¹ * y⁻¹ := by rw [hxy]
      _ = y * (x * (z ^ 4)⁻¹ * x⁻¹) * y⁻¹ := by group
      _ = y * (z ^ 4)⁻¹ * y⁻¹ := by rw [h1]
      _ = (z ^ 4)⁻¹ := h2
  have hP : IsPGroup 13 (Subgroup.closure ({x, y} : Set G)) :=
    isPGroup_closure_of_central_commutator (by norm_num) hx hy (by rw [hK]; exact hwx)
      (by rw [hK]; exact hwy)
  have hyz : y ∉ Subgroup.zpowers z := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have hc : Commute x y := by
      rw [← hk]
      exact hzx'.symm.zpow_right k
    have h3 : y * x = y * x * z ^ 4 := by
      calc y * x = x * (y * z ^ 4) := hcomm
        _ = x * y * z ^ 4 := by rw [mul_assoc]
        _ = y * x * z ^ 4 := by rw [hc.eq]
    have h4 : z ^ 4 = 1 := mul_left_cancel (h3.symm.trans (mul_one (y * x)).symm)
    apply hz1
    have : z = (z ^ 4) ^ 10 := by rw [← pow_mul]; exact hz40.symm
    rw [this, h4, one_pow]
  have hr1 : 2 ≤ CFSG.Open.pRank 13 (Subgroup.closure ({x, y} : Set G)) :=
    two_le_pRank_of_commute hzS hyS hz13 hy hzy' hz1 hyz
  have hr2 : 2 ≤ CFSG.Open.pRank 13 (Subgroup.closure ({z, y} : Set G)) :=
    two_le_pRank_of_commute hzA hyA hz13 hy hzy' hz1 hyz
  exact glbCore_two_top_of_normalizing (p := 13) (Subgroup.closure ({x, y} : Set G)) hP
    ![Subgroup.closure ({x, y} : Set G), Subgroup.closure ({z, y} : Set G)]
    (by intro i; fin_cases i <;> simp [hAS]) (by intro i; fin_cases i <;> simp [hr1, hr2]) T hT
    (by
      intro g hg
      rcases hN g hg with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩)

end CFSG.AGLEmbedding.Norton.MON11_13
