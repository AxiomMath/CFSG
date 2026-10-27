module

public import CFSG.ClassicalInvolution.Q3.TL4D1Thin
public import CFSG.ClassicalInvolution.Q3.TL3T16

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem T4Hyp.eq_or_commutes_of_mul_center {r : ℕ} (h : T4Hyp r G Δ)
    (h2 : ∀ K ∈ Δ, IsPGroup 2 K) {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ) {a b : G}
    (ha : IsUniqueInvolution A a) (hb : IsUniqueInvolution B b) {c : G}
    (hc : ∀ g : G, g * c = c * g) (hab : b = a * c) : A = B ∨ Commutes A B := by
  have hAN : A ≤ Subgroup.normalizer (B : Set G) := by
    intro x hx
    refine h.tight B hB b hb (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    rw [hab]
    have h1 := isUniqueInvolution_comm ha hx
    refine (?_ : a * c * x = x * (a * c)).symm
    calc a * c * x = a * (c * x) := mul_assoc _ _ _
      _ = a * (x * c) := by rw [hc x]
      _ = x * a * c := by rw [← mul_assoc, ← h1]
      _ = x * (a * c) := mul_assoc _ _ _
  by_cases heq : A = B
  · exact Or.inl heq
  · exact Or.inr (commutes_of_le_two h.hyp h2 hA hB heq
      ((h2 A hA).to_sup_of_normal_right' (h2 B hB) hAN) le_sup_left le_sup_right)

variable {X : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem comm_of_mem_center {c : ↥X} (hc : c ∈ Subgroup.center ↥X) {g : G} (hg : g ∈ X) :
    g * c = c * g :=
  congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g, hg⟩)

theorem injOn_of_not_mem_center {H : Type} [Group H] (φ : ↥X →* H)
    (hk : φ.ker ≤ Subgroup.center ↥X) {L : Subgroup G} (hLX : L ≤ X) (hL2 : IsPGroup 2 L)
    {v : G} (hv : IsUniqueInvolution L v) (hvZ : (⟨v, hLX hv.mem⟩ : ↥X) ∉ Subgroup.center ↥X)
    {l₁ l₂ : G} (h₁ : l₁ ∈ L) (h₂ : l₂ ∈ L) (he : φ ⟨l₁, hLX h₁⟩ = φ ⟨l₂, hLX h₂⟩) :
    l₁ = l₂ := by
  by_contra hne
  set c : G := l₁⁻¹ * l₂ with hc
  have hcL : c ∈ L := L.mul_mem (L.inv_mem h₁) h₂
  have hc1 : c ≠ 1 := fun h1 => hne (by rw [hc] at h1; exact (inv_mul_eq_one.mp h1))
  have hcker : (⟨c, hLX hcL⟩ : ↥X) ∈ φ.ker := by
    have : (⟨c, hLX hcL⟩ : ↥X) = (⟨l₁, hLX h₁⟩ : ↥X)⁻¹ * ⟨l₂, hLX h₂⟩ := rfl
    rw [MonoidHom.mem_ker, this, map_mul, map_inv, he, inv_mul_cancel]
  have hZ : Subgroup.zpowers c ≤ L := Subgroup.zpowers_le.mpr hcL
  have hvc : v ∈ Subgroup.zpowers c := mem_of_isPGroup_of_ne_bot hv hZ (hL2.to_le hZ)
    (fun hb => hc1 (by
      have : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
      rw [hb] at this
      exact Subgroup.mem_bot.mp this))
  obtain ⟨k, hk'⟩ := hvc
  apply hvZ
  have : (⟨v, hLX hv.mem⟩ : ↥X) = (⟨c, hLX hcL⟩ : ↥X) ^ k := by
    apply Subtype.ext
    simp only [Subgroup.coe_zpow]
    exact hk'.symm
  rw [this]
  exact Subgroup.zpow_mem _ (hk hcker) k

omit [Finite G] in
theorem map_conjSub_subgroupOf {H : Type} [Group H] (φ : ↥X →* H) (L : Subgroup G)
    {g : G} (hg : g ∈ X) :
    ((conjSub g L).subgroupOf X).map φ = conjSub (φ ⟨g, hg⟩) ((L.subgroupOf X).map φ) := by
  ext y
  constructor
  · rintro ⟨⟨x, hxX⟩, hx, rfl⟩
    have hx' : x ∈ conjSub g L := hx
    rw [mem_conjSub_iff] at hx'
    rw [mem_conjSub_iff]
    refine ⟨⟨g⁻¹ * x * g, X.mul_mem (X.mul_mem (X.inv_mem hg) hxX) hg⟩,
      Subgroup.mem_subgroupOf.mpr hx', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · intro hy
    rw [mem_conjSub_iff] at hy
    obtain ⟨⟨x, hxX⟩, hx, hxe⟩ := hy
    refine ⟨⟨g, hg⟩ * ⟨x, hxX⟩ * ⟨g, hg⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hx)
    · rw [map_mul, map_mul, map_inv, hxe]
      group

end CFSG.ClassicalInvolution.Q3.TL4
