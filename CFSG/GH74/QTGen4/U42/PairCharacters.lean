module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.GH74.QTGen4.U42

open scoped commutatorElement

theorem extend_hom_of_sup_eq_top {K A : Type*} [Group K] [Group A]
    (B N : Subgroup K) [N.Normal] (hBN : B ⊔ N = ⊤) (δ : ↥B →* A)
    (hδ : ∀ b : ↥B, (b : K) ∈ N → δ b = 1) :
    ∃ χ : K →* A, ∀ b : ↥B, χ (b : K) = δ b := by
  classical
  let π : ↥B →* K ⧸ N := (QuotientGroup.mk' N).comp B.subtype
  have hπ : Function.Surjective π := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ B ⊔ N := by rw [hBN]; exact Subgroup.mem_top _
    obtain ⟨b, hb, n, hn, hbn⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk b : K ⧸ N) = QuotientGroup.mk x
    rw [← hbn, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
  have hker : π.ker ≤ δ.ker := by
    intro b hb
    exact hδ b ((QuotientGroup.eq_one_iff (b : K)).mp (MonoidHom.mem_ker.mp hb))
  let e : (↥B ⧸ π.ker) ≃* K ⧸ N := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let δq : (↥B ⧸ π.ker) →* A := QuotientGroup.lift π.ker δ hker
  refine ⟨δq.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' N)), ?_⟩
  intro b
  have hi : e.symm (π b) = QuotientGroup.mk b := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  change δq (e.symm (π b)) = δ b
  rw [hi]
  rfl

theorem hom_trivial_of_cube_mem {K A : Type*} [Group K] [Group A]
    (B U N : Subgroup K) (δ : ↥B →* A) (hA : ∀ a : A, a ^ 2 = 1)
    (hU : ∀ b : ↥B, (b : K) ∈ U → δ b = 1)
    (hN : ∀ b : ↥B, (b : K) ∈ N → (b : K) ^ 3 ∈ U) :
    ∀ b : ↥B, (b : K) ∈ N → δ b = 1 := by
  intro b hb
  have h3 : (δ b) ^ 3 = 1 := by
    rw [← map_pow]
    exact hU (b ^ 3) (hN b hb)
  calc
    δ b = (δ b) ^ 2 * δ b := by rw [hA, one_mul]
    _ = (δ b) ^ 3 := (pow_succ (δ b) 2).symm
    _ = 1 := h3

theorem hom_trivial_on_commutator {K A : Type*} [Group K] [CommGroup A] (δ : K →* A) :
    ∀ (x : K), x ∈ ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ → δ x = 1 := by
  have hker : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ δ.ker := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    change δ ⁅a, b⁆ = 1
    simp [commutatorElement_def, mul_comm, mul_left_comm, mul_assoc]
  exact fun x hx => hker hx

theorem hom_trivial_of_mem_commutator_subgroup {K A : Type*} [Group K] [CommGroup A]
    (B : Subgroup K) (δ : ↥B →* A) (b : ↥B) (hb : (b : K) ∈ ⁅B, B⁆) : δ b = 1 := by
  have hmap : (⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆).map B.subtype = ⁅B, B⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hmap] at hb
  obtain ⟨a, ha, hab⟩ := hb
  have hab' : a = b := B.subtype_injective hab
  exact hom_trivial_on_commutator δ b (hab' ▸ ha)

end CFSG.GH74.QTGen4.U42
