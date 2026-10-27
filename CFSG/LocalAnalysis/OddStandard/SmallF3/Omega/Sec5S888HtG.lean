module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L512H
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B514Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem heart_comm_of_mem_centerIn {K : Subgroup G} {a : G} (h : a ∈ centerIn K) :
    ∀ k ∈ K, a * k = k * a := by
  rw [centerIn, Subgroup.mem_map] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨k, hk⟩)).symm

private theorem heart_mem_conjClassIn {M : Subgroup G} {t m y : G} (hm : m ∈ M)
    (hy : y ∈ conjClassIn M t) : m * y * m⁻¹ ∈ conjClassIn M t := by
  obtain ⟨n, hn, rfl⟩ := hy
  exact ⟨m * n, mul_mem hm hn, by group⟩

section Ctx

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

theorem heart_t_not_mem_sup (h37 : Asc82Lemma37) (fact : Asc82Fact512H)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t ∉ K₁ ⊔ K₂ := by
  intro htK
  have hC : Sec5Ctx G t L S z := c.toSec5Ctx
  have hΩ : IsOm6Z2 L := hC.toSec5Setting.isOm6Z2
  have htTwo : t ∈ twoRes (L ⊓ centralizer ({z} : Set G)) := c.prod ▸ htK
  obtain ⟨g, hgL, hg⟩ := fact.inv_class G L hΩ t hC.involution c.centre z c.pocket t htTwo
    hC.involution (c.t_ne_z h37)
  have htc : t ∈ centerIn L := c.centre ▸ Subgroup.mem_zpowers t
  have hgt : t * g = g * t := heart_comm_of_mem_centerIn htc g hgL
  have h1 : t = t * (g * z * g⁻¹) :=
    calc t = g * (t * z) * g⁻¹ := hg
      _ = (g * t) * z * g⁻¹ := by group
      _ = (t * g) * z * g⁻¹ := by rw [← hgt]
      _ = t * (g * z * g⁻¹) := by group
  have hX : g * z * g⁻¹ = 1 := mul_left_cancel (a := t) (h1.symm.trans (mul_one t).symm)
  exact c.z_ne_one (calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
    _ = 1 := by rw [hX]; group)

theorem heart_A₁_class (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52b : Asc82Lemma52b)
    (h53 : Asc82Lemma53) (tab : Asc82Tab5) (fact : Asc82Fact512H)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) (h2 : Case59Two t z A) {x : G} (hxA : x ∈ A)
    (hxK : x ∈ K₁ ⊔ K₂) (hx1 : x ≠ 1) (hxz : x ≠ z) :
    x ∈ conjClassIn (normalizer (A : Set G)) t := by
  have hR : Sec5RCtx G t L S z r B A := c.toSec5RCtx
  have hC : Sec5Ctx G t L S z := hR.toSec5Ctx
  have hΩ : IsOm6Z2 L := hC.toSec5Setting.isOm6Z2
  obtain ⟨-, hsq⟩ := sec5b_A_elemAb hR
  have hxTwo : x ∈ twoRes (L ⊓ centralizer ({z} : Set G)) := c.prod ▸ hxK
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hsq x hxA) hx1
  exact sec5b_mem_tclass h36 h37 h52b h53 tab hC h2 hxA hx1
    (fact.inv_class G L hΩ t hC.involution c.centre z c.pocket x hxTwo hord hxz)

theorem heart_A₂_class (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52b : Asc82Lemma52b)
    (h53 : Asc82Lemma53) (tab : Asc82Tab5) (fact : Asc82Fact512H)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) (h2 : Case59Two t z A) {x : G} (hxA : x ∈ A)
    (hxK : x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) (hx1 : x ≠ 1) (hxz : x ≠ z) :
    x ∈ conjClassIn (normalizer (A : Set G)) t := by
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp c.h_z
  have hyK : h * x * h⁻¹ ∈ K₁ ⊔ K₂ := by
    rw [← sec5b_conjugate_sup] at hxK
    exact sec5b_mem_conjugate_iff.mp hxK
  have hyA : h * x * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp c.h_mem x).mp hxA
  have hy1 : h * x * h⁻¹ ≠ 1 := by
    intro hy
    apply hx1
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = 1 := by rw [hy]; group
  have hyz : h * x * h⁻¹ ≠ z := by
    intro hy
    apply hxz
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = h⁻¹ * z * h := by rw [hy]
      _ = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [hhz]
      _ = z := by group
  have hcl := heart_A₁_class h36 h37 h52b h53 tab fact c h2 hyA hyK hy1 hyz
  have := heart_mem_conjClassIn (inv_mem c.h_mem) hcl
  rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this

theorem heart_card_A₂ (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    (h8 : 8 ≤ Nat.card ↥(A ⊓ (K₁ ⊔ K₂))) :
    8 ≤ Nat.card ↥(A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h)) := by
  have hmem : ∀ y : ↥(A ⊓ (K₁ ⊔ K₂)),
      h⁻¹ * (y : G) * h ∈ A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) := by
    intro y
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem c.h_mem) (y : G)).mp y.2.1
      simpa using this
    · rw [← sec5b_conjugate_sup]
      refine sec5b_mem_conjugate_iff.mpr ?_
      rw [show h * (h⁻¹ * (y : G) * h) * h⁻¹ = (y : G) by group]
      exact y.2.2
  let f : ↥(A ⊓ (K₁ ⊔ K₂)) → ↥(A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h)) :=
    fun y => ⟨h⁻¹ * (y : G) * h, hmem y⟩
  have hf : Function.Injective f := by
    intro y y' hyy
    have h1 : h⁻¹ * (y : G) * h = h⁻¹ * (y' : G) * h := congrArg Subtype.val hyy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  exact le_trans h8 (Nat.card_le_card_of_injective f hf)

end Ctx

end CFSG.OddStandard.SmallF3.Omega
