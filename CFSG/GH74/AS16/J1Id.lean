module

public import CFSG.GH74.AS16.Defs
public import CFSG.Walter.Models
public import CFSG.Walter.AStar.Basic
public import CFSG.Walter.J1Recog.Main

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG.Blueprint
open scoped Pointwise

section Group

variable {G : Type*} [Group G]

theorem decomp_of_mem_sup {z : G} (hz2 : z ^ 2 = 1) {F : Subgroup G}
    (hF : ∀ f ∈ F, z * f = f * z) {a : G} (ha : a ∈ zpowers z ⊔ F) :
    ∃ f ∈ F, a = f ∨ a = z * f := by
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hle : zpowers z ≤ normalizer (F : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hF h hh, mul_inv_cancel_right]
      exact hh
    · intro hh
      have h1 : z * (z * h * z⁻¹) = (z * h * z⁻¹) * z := hF _ hh
      have h2 : h = z * (z * h * z⁻¹) * z⁻¹ := by
        rw [hzinv]
        calc h = (z * z) * h * (z * z) := by rw [hzz]; simp
          _ = z * (z * h * z) * z := by simp only [mul_assoc]
      have h3 : z * (z * h * z⁻¹) * z⁻¹ = z * h * z⁻¹ := by
        rw [h1, mul_inv_cancel_right]
      have h4 : h = z * h * z⁻¹ := h2.trans h3
      rw [h4]
      exact hh
  have hmem : a ∈ ((zpowers z : Subgroup G) : Set G) * (F : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact ha
  obtain ⟨y, hy, f, hf, rfl⟩ := hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨f, hf, ?_⟩
  rcases zpow_eq_one_or_self hz2 k with h | h
  · left
    simp [h]
  · right
    simp [h]

theorem comm_of_two_elements {F T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hFT : ∀ x ∈ F, (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ^ 2 = 1)
    {f g : G} (hfF : f ∈ F) (hfT : f ∈ T) (hgF : g ∈ F) (hgT : g ∈ T) : f * g = g * f := by
  have two : ∀ x : G, x ∈ F → x ∈ T → x ^ 2 = 1 := by
    intro x hxF hxT
    apply hFT x hxF
    obtain ⟨k, hk⟩ := hT2 ⟨x, hxT⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hf2 := two f hfF hfT
  have hg2 := two g hgF hgT
  have hfg2 := two (f * g) (F.mul_mem hfF hgF) (T.mul_mem hfT hgT)
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hf2)
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hg2)
  have hfginv : (f * g)⁻¹ = f * g := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hfg2)
  have h : g⁻¹ * f⁻¹ = f * g := by rw [← mul_inv_rev]; exact hfginv
  rw [hfinv, hginv] at h
  exact h.symm

theorem isMulCommutative_of_decomp {z : G} (hz2 : z ^ 2 = 1) {F T : Subgroup G}
    (hF : ∀ f ∈ F, z * f = f * z) (hzT : z ∈ T) (hT2 : IsPGroup 2 T)
    (hFT : ∀ x ∈ F, (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ^ 2 = 1)
    (hTC : T ≤ zpowers z ⊔ F) : IsMulCommutative T := by
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  apply Subtype.ext
  show a * b = b * a
  obtain ⟨f, hfF, hf⟩ := decomp_of_mem_sup hz2 hF (hTC ha)
  obtain ⟨g, hgF, hg⟩ := decomp_of_mem_sup hz2 hF (hTC hb)
  have hzmul : ∀ x : G, z * (z * x) = x := fun x => by rw [← mul_assoc, hzz, one_mul]
  have hfT : f ∈ T := by
    rcases hf with h | h
    · rw [← h]
      exact ha
    · have : f = z * a := by rw [h, hzmul]
      rw [this]
      exact T.mul_mem hzT ha
  have hgT : g ∈ T := by
    rcases hg with h | h
    · rw [← h]
      exact hb
    · have : g = z * b := by rw [h, hzmul]
      rw [this]
      exact T.mul_mem hzT hb
  have hfg : f * g = g * f := comm_of_two_elements hT2 hFT hfF hfT hgF hgT
  have hzf : z * f = f * z := hF f hfF
  have hzg : z * g = g * z := hF g hgF
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
  · exact hfg
  · calc a * (z * g) = (a * z) * g := by simp only [mul_assoc]
      _ = (z * a) * g := by rw [← hzf]
      _ = z * (a * g) := by simp only [mul_assoc]
      _ = z * (g * a) := by rw [hfg]
      _ = z * g * a := by simp only [mul_assoc]
  · calc z * f * b = z * (f * b) := by simp only [mul_assoc]
      _ = z * (b * f) := by rw [hfg]
      _ = z * b * f := by simp only [mul_assoc]
      _ = (b * z) * f := by rw [← hzg]
      _ = b * (z * f) := by simp only [mul_assoc]
  · calc z * f * (z * g) = z * (f * z) * g := by simp only [mul_assoc]
      _ = z * (z * f) * g := by rw [← hzf]
      _ = z * z * (f * g) := by simp only [mul_assoc]
      _ = z * z * (g * f) := by rw [hfg]
      _ = z * (z * g) * f := by simp only [mul_assoc]
      _ = z * (g * z) * f := by rw [hzg]
      _ = z * g * (z * f) := by simp only [mul_assoc]

end Group

variable {G : Type} [Group G]

theorem sq_eq_one_of_two_element {F : Subgroup G} (e : F ≃* alternatingGroup (Fin 5)) {x : G}
    (hx : x ∈ F) (hk : ∃ k : ℕ, x ^ (2 ^ k) = 1) : x ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hk
  rcases Walter.J1.A5Sub.pow_eq_one e hx with h | h | h
  · exact h
  · have h1 := pow_gcd_eq_one.mpr ⟨h, hk⟩
    have hc : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    rw [hc, pow_one] at h1
    rw [h1]
    simp
  · have h1 := pow_gcd_eq_one.mpr ⟨h, hk⟩
    have hc : Nat.gcd 5 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    rw [hc, pow_one] at h1
    rw [h1]
    simp

theorem isSporadic_J1_of_involution_centralizer [Finite G] (hG : IsSimpleGroup G)
    (T : Sylow 2 G) {z : G} (hz : orderOf z = 2) (hzT : z ∈ (T : Subgroup G))
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t) {F : Subgroup G} (hzF : z ∉ F)
    (he : Nonempty (F ≃* alternatingGroup (Fin 5)))
    (hC : centralizer ({z} : Set G) = zpowers z ⊔ F) :
    NativeSporadic.IsSporadic G .J1 := by
  obtain ⟨e⟩ := he
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hFC : F ≤ centralizer ({z} : Set G) := hC ▸ le_sup_right
  have hFz : ∀ f ∈ F, z * f = f * z := fun f hf =>
    (mem_centralizer_singleton_iff.mp (hFC hf)).symm
  have hTC : (T : Subgroup G) ≤ zpowers z ⊔ F := by
    rw [← hC]
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzc t ht)
  have hab : IsMulCommutative (T : Subgroup G) :=
    isMulCommutative_of_decomp hz2 hFz hzT T.isPGroup'
      (fun x hx hk => sq_eq_one_of_two_element e hx hk) hTC
  have hJ : Walter.J1.JankoHyp G :=
    { isSimpleGroup := hG
      abelian_sylow := Walter.hasAbelianSylowTwo_of_sylow T hab
      t := z
      orderOf_t := hz
      F := F
      le_centralizer := hFC
      t_not_mem := hzF
      centralizer_eq := hC
      iso := e }
  obtain ⟨e'⟩ := Walter.J1Recog.nonempty_mulEquiv_walterJ1 hJ
  exact Walter.isSporadic_J1_of_mulEquiv e'

theorem isSporadic_J1_of_jankoLocal [Finite G] (hG : IsSimpleGroup G)
    (T : Sylow 2 G) {z : G} (hz : orderOf z = 2) (hzT : z ∈ (T : Subgroup G))
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t) {L : Subgroup G} (hL : JankoLocal z L) :
    NativeSporadic.IsSporadic G .J1 :=
  isSporadic_J1_of_involution_centralizer hG T hz hzT hzc hL.1 hL.2.1 hL.2.2

end CFSG.GH74.AS16
