module

public import CFSG.GH74.GLS.IVK.Lifted.Lem31c

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf

section Swap

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem odd_normalizes_comps (h : Std4 G z S K₁ K₂) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hodd : Odd (orderOf x)) :
    x ∈ normalizer (K₁ : Set G) ∧ x ∈ normalizer (K₂ : Set G) := by
  rcases IVK.Lifted.std4_perm_cmap h hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(IVK.Lifted.cmap_eq_iff_normalizer K₁ x).1 h1,
      (IVK.Lifted.cmap_eq_iff_normalizer K₂ x).1 h2⟩
  · exfalso
    have h3 : cmap (x * x) K₁ = K₁ := by
      rw [← cmap_cmap, h1, h2]
    have h4 : x * x ∈ normalizer (K₁ : Set G) :=
      (IVK.Lifted.cmap_eq_iff_normalizer K₁ (x * x)).1 h3
    obtain ⟨k, hk⟩ := hodd
    have hx1 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    have hxe : x = ((x * x) ^ k)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      calc x * (x * x) ^ k = x * x ^ (2 * k) := by rw [← sq, ← pow_mul]
        _ = 1 := by rw [← pow_succ']; exact hx1
    have h5 : x ∈ normalizer (K₁ : Set G) := by
      rw [hxe]
      exact inv_mem (pow_mem h4 k)
    have := (IVK.Lifted.cmap_eq_iff_normalizer K₁ x).2 h5
    rw [h1] at this
    exact h.ne this.symm

omit [Finite G] in
theorem phi_comm (A : Subgroup G) {x y c : G} (hcdef : c = x * y * x⁻¹ * y⁻¹)
    (hx : x ∈ normalizer (A : Set G)) (hy : y ∈ normalizer (A : Set G))
    (hc : c ∈ normalizer (A : Set G)) :
    phi A c hc = ⁅phi A x hx, phi A y hy⁆ := by
  subst hcdef
  have hxy : x * y ∈ normalizer (A : Set G) := mul_mem hx hy
  have hxyx : x * y * x⁻¹ ∈ normalizer (A : Set G) := mul_mem hxy (inv_mem hx)
  rw [phi_mul A hxyx (inv_mem hy), phi_mul A hxy (inv_mem hx), phi_mul A hx hy,
    IVK.Lifted.phi_inv_aux A hx (inv_mem hx), IVK.Lifted.phi_inv_aux A hy (inv_mem hy),
    commutatorElement_def]

theorem comm_mem_of_normalizes (h44 : II4_44) (h2A7 : IVK.Lifted.II4_2A7) (hII : II4_4_4_center)
    (hFS : FStar_C) (h : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z)
    {x y : G} (hxC : x ∈ centralizer ({z} : Set G)) (hyC : y ∈ centralizer ({z} : Set G))
    (hx₁ : x ∈ normalizer (K₁ : Set G)) (hx₂ : x ∈ normalizer (K₂ : Set G))
    (hy₁ : y ∈ normalizer (K₁ : Set G)) (hy₂ : y ∈ normalizer (K₂ : Set G)) :
    x * y * x⁻¹ * y⁻¹ ∈ K₁ ⊔ K₂ ⊔ Oz z := by
  classical
  have hM := m4_of_std hII h
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  rw [← hcdef]
  have hcC : c ∈ Cz z := by
    rw [hcdef]
    exact mul_mem (mul_mem (mul_mem hxC hyC) (inv_mem hxC)) (inv_mem hyC)
  have hcN : ∀ N : Subgroup G, x ∈ normalizer (N : Set G) → y ∈ normalizer (N : Set G) →
      c ∈ normalizer (N : Set G) := fun N hxN hyN => by
    rw [hcdef]
    exact mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
  have hcN₁ := hcN K₁ hx₁ hy₁
  have hcN₂ := hcN K₂ hx₂ hy₂
  have hinn : ∀ (A : Subgroup G), A ∈ ({K₁, K₂} : Set (Subgroup G)) →
      ∀ (hxA : x ∈ normalizer (A : Set G)) (hyA : y ∈ normalizer (A : Set G))
        (hcA : c ∈ normalizer (A : Set G)), ∃ k ∈ A, c * k⁻¹ ∈ cSec A := by
    intro A hA hxA hyA hcA
    have hOK := IVK.Lifted.std4_hatOK h44 h hA
    have h1 : phi A c hcA ∈ innOf (Hat A) := by
      rw [phi_comm A hcdef hxA hyA hcA]
      exact IVK.Lifted.dict_out_abelian h2A7 hOK.sl2 (phi A x hxA) (phi A y hyA)
    exact (phi_mem_inn_iff A hcA).1 h1
  obtain ⟨k₁, hk₁, hk₁c⟩ := hinn K₁ (Set.mem_insert _ _) hx₁ hy₁ hcN₁
  obtain ⟨k₂, hk₂, hk₂c⟩ := hinn K₂ (Set.mem_insert_of_mem _ rfl) hx₂ hy₂ hcN₂
  have hK₂c : ∀ k ∈ K₂, k ∈ cSec K₁ := fun k hk => hM.cs₁ hk
  have hK₁c : ∀ k ∈ K₁, k ∈ cSec K₂ := fun k hk => hM.cs₂ hk
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  have hk₁N₁ : k₁ ∈ normalizer (K₁ : Set G) := le_normalizer hk₁
  have hk₂N₂ : k₂ ∈ normalizer (K₂ : Set G) := le_normalizer hk₂
  have hk₁N₂ : k₁ ∈ normalizer (K₂ : Set G) := (hK₁c k₁ hk₁).1
  have hk₂N₁ : k₂ ∈ normalizer (K₁ : Set G) := (hK₂c k₂ hk₂).1
  have hN₁ : c * k₂⁻¹ * k₁⁻¹ ∈ normalizer (K₁ : Set G) :=
    mul_mem (mul_mem hcN₁ (inv_mem hk₂N₁)) (inv_mem hk₁N₁)
  have hN₂ : c * k₂⁻¹ * k₁⁻¹ ∈ normalizer (K₂ : Set G) :=
    mul_mem (mul_mem hcN₂ (inv_mem hk₂N₂)) (inv_mem hk₁N₂)
  have hy'1 : c * k₂⁻¹ * k₁⁻¹ ∈ cSec K₁ := by
    refine (phi_eq_one_iff K₁ hN₁).1 ?_
    have h2 : phi K₁ k₂ hk₂N₁ = 1 := (phi_eq_one_iff K₁ hk₂N₁).2 (hK₂c k₂ hk₂)
    have h3 : phi K₁ (c * k₁⁻¹) (mul_mem hcN₁ (inv_mem hk₁N₁)) = 1 :=
      (phi_eq_one_iff K₁ _).2 hk₁c
    rw [phi_mul K₁ hcN₁ (inv_mem hk₁N₁), IVK.Lifted.phi_inv_aux K₁ hk₁N₁ (inv_mem hk₁N₁)] at h3
    rw [phi_mul K₁ (mul_mem hcN₁ (inv_mem hk₂N₁)) (inv_mem hk₁N₁),
      phi_mul K₁ hcN₁ (inv_mem hk₂N₁), IVK.Lifted.phi_inv_aux K₁ hk₂N₁ (inv_mem hk₂N₁),
      IVK.Lifted.phi_inv_aux K₁ hk₁N₁ (inv_mem hk₁N₁), h2, inv_one, mul_one]
    exact h3
  have hy'2 : c * k₂⁻¹ * k₁⁻¹ ∈ cSec K₂ := by
    refine (phi_eq_one_iff K₂ hN₂).1 ?_
    have h2 : phi K₂ k₁ hk₁N₂ = 1 := (phi_eq_one_iff K₂ hk₁N₂).2 (hK₁c k₁ hk₁)
    have h3 : phi K₂ (c * k₂⁻¹) (mul_mem hcN₂ (inv_mem hk₂N₂)) = 1 :=
      (phi_eq_one_iff K₂ _).2 hk₂c
    rw [phi_mul K₂ (mul_mem hcN₂ (inv_mem hk₂N₂)) (inv_mem hk₁N₂), h3,
      IVK.Lifted.phi_inv_aux K₂ hk₁N₂ (inv_mem hk₁N₂), h2, inv_one, mul_one]
  have hy'C : c * k₂⁻¹ * k₁⁻¹ ∈ Cz z :=
    mul_mem (mul_mem hcC (inv_mem (hK₂C hk₂))) (inv_mem (hK₁C hk₁))
  obtain ⟨-, -, hy1c⟩ := id hy'1
  obtain ⟨-, -, hy2c⟩ := id hy'2
  have hbr := IVK.Lifted.commutes_mod_O_of_gens h hy1c hy2c
  have hFSy : c * k₂⁻¹ * k₁⁻¹ ∈ zpowers z ⊔ Oz z := hFS G z S K₁ K₂ h hQ _ hy'C hbr
  have hzK₁ : z ∈ K₁ := hM.z_mem_comp (Or.inl rfl)
  have hK₁le : K₁ ≤ K₁ ⊔ K₂ ⊔ Oz z :=
    (le_sup_left : K₁ ≤ K₁ ⊔ K₂).trans (le_sup_left : K₁ ⊔ K₂ ≤ K₁ ⊔ K₂ ⊔ Oz z)
  have hK₂le : K₂ ≤ K₁ ⊔ K₂ ⊔ Oz z :=
    (le_sup_right : K₂ ≤ K₁ ⊔ K₂).trans (le_sup_left : K₁ ⊔ K₂ ≤ K₁ ⊔ K₂ ⊔ Oz z)
  have hz_le : zpowers z ≤ K₁ ⊔ K₂ ⊔ Oz z := (zpowers_le.2 hzK₁).trans hK₁le
  have hdec : c = (c * k₂⁻¹ * k₁⁻¹) * k₁ * k₂ := by group
  rw [hdec]
  exact mul_mem (mul_mem (sup_le hz_le le_sup_right hFSy) (hK₁le hk₁)) (hK₂le hk₂)

end Swap

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf
