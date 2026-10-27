module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64Glue

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

@[expose] def OG {G : Type*} [Group G] (β : G) : Subgroup G :=
  (fusionOddCore ↥(centralizer ({β} : Set G))).map (centralizer ({β} : Set G)).subtype

variable {G : Type} [Group G]

theorem normalizer_cent_of_conj {β u : G} (hu : u * β * u⁻¹ = β ∨ u * β * u⁻¹ = β⁻¹) :
    u ∈ normalizer ((centralizer ({β} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hcomm : ∀ x : G, x * (u * β * u⁻¹) = (u * β * u⁻¹) * x ↔ x * β = β * x := by
    intro x
    rcases hu with hu | hu
    · rw [hu]
    · rw [hu]
      exact Commute.inv_right_iff
  have hconj : u * h * u⁻¹ * (u * β * u⁻¹) = (u * β * u⁻¹) * (u * h * u⁻¹) ↔ h * β = β * h := by
    have e1 : u * h * u⁻¹ * (u * β * u⁻¹) = u * (h * β) * u⁻¹ := by group
    have e2 : u * β * u⁻¹ * (u * h * u⁻¹) = u * (β * h) * u⁻¹ := by group
    rw [e1, e2]
    simp
  simp only [SetLike.mem_coe, mem_centralizer_singleton_iff]
  exact hconj.symm.trans (hcomm _)

theorem inv_of_mem_normalizer_zpowers {β y : G} (hβ3 : orderOf β = 3)
    (hy : y ∈ normalizer ((zpowers β : Subgroup G) : Set G)) (hyK : y ∉ centralizer ({β} : Set G)) :
    y * β * y⁻¹ = β⁻¹ := by
  rw [Subgroup.mem_normalizer_iff] at hy
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ((hy β).1 (mem_zpowers β))
  have hord : orderOf (y * β * y⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hβ3]
  have hmod : β ^ (k % 3) = β ^ k := by
    have h := zpow_mod_orderOf β k
    rw [hβ3] at h
    simp only [Nat.cast_ofNat] at h
    exact h
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  ·
    exfalso
    have hy1 : y * β * y⁻¹ = 1 := by rw [← hk, ← hmod, h0, zpow_zero]
    rw [hy1, orderOf_one] at hord
    norm_num at hord
  ·
    exfalso
    have hyb : y * β * y⁻¹ = β := by rw [← hk, ← hmod, h1, zpow_one]
    apply hyK
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.1 hyb
  ·
    have h3 : β ^ 3 = 1 := by
      rw [← hβ3]
      exact pow_orderOf_eq_one β
    rw [← hk, ← hmod, h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
      eq_inv_iff_mul_eq_one, ← pow_succ]
    exact h3

theorem OG_le_cent (β : G) : OG β ≤ centralizer ({β} : Set G) := by
  unfold OG
  exact Subgroup.map_subtype_le _

theorem OG_normal_conj [Finite G] {β k o : G} (hk : k ∈ centralizer ({β} : Set G)) (ho : o ∈ OG β) :
    k * o * k⁻¹ ∈ OG β := by
  unfold OG at ho ⊢
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ho
  let g : centralizer ({β} : Set G) := ⟨k, hk⟩
  refine Subgroup.mem_map.2 ⟨g * x * g⁻¹, Subgroup.Normal.conj_mem inferInstance x hx g, ?_⟩
  rfl

theorem conj_mem_OG [Finite G] {β u o : G}
    (hu : u ∈ normalizer ((centralizer ({β} : Set G) : Subgroup G) : Set G)) (ho : o ∈ OG β) :
    u * o * u⁻¹ ∈ OG β := by
  let φ : centralizer ({β} : Set G) ≃* centralizer ({β} : Set G) :=
    { toFun := fun x => ⟨u * (x : G) * u⁻¹, (Subgroup.mem_normalizer_iff.1 hu (x : G)).1 x.2⟩
      invFun := fun y => ⟨u⁻¹ * (y : G) * u, (Subgroup.mem_normalizer_iff.1 hu (u⁻¹ * (y : G) * u)).2
        (by
          rw [show u * (u⁻¹ * (y : G) * u) * u⁻¹ = (y : G) by group]
          exact y.2)⟩
      left_inv := fun x => Subtype.ext (by dsimp only; group)
      right_inv := fun y => Subtype.ext (by dsimp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  unfold OG at ho ⊢
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ho
  refine Subgroup.mem_map.2 ⟨φ x, ?_, rfl⟩
  exact map_fusionOddCore_le φ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)

theorem odd_orderOf_OG [Finite G] {β o : G} (ho : o ∈ OG β) : Odd (orderOf o) := by
  unfold OG at ho
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ho
  show Odd (orderOf (x : G))
  rw [Subgroup.orderOf_coe]
  exact Odd.of_dvd_nat (odd_natCard_fusionOddCore _) (Subgroup.orderOf_dvd_natCard _ hx)

end CFSG.EvenSporadicStandard.Fin76b
