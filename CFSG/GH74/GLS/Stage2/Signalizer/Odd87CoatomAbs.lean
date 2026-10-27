module

public import Mathlib.GroupTheory.PGroup
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped Pointwise

theorem false_of_coatom_centralizer {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnonab : ∃ a b : T, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] (k : T)
    (hco : IsCoatom (centralizer ({k} : Set T)))
    (hOp : ∀ Y : Subgroup T, Y ≤ centralizer ({k} : Set T) →
      (∀ c ∈ centralizer ({k} : Set T), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) → IsPGroup p ↥Y → Y = ⊥)
    {X : Subgroup T} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hN : centralizer ({k} : Set T) ≤ normalizer (X : Set T)) : False := by
  classical
  have hXN : X ≤ normalizer (X : Set T) := Subgroup.le_normalizer
  rcases (hco.le_iff).mp hN with hNtop | hNC
  · have hXn : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h | h
    · exact hX1 h
    · have hT : IsPGroup p T := by
        have : IsPGroup p ↥(⊤ : Subgroup T) := h ▸ hX
        exact this.of_equiv Subgroup.topEquiv
      have : Nontrivial T := by
        obtain ⟨a, b, hab⟩ := hnonab
        exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
      have hcn : Nontrivial (center T) := hT.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center T) with h1 | h1
      · obtain ⟨x, hx⟩ := exists_ne (1 : center T)
        exact hx (Subtype.ext ((Subgroup.eq_bot_iff_forall (center T)).mp h1 x x.2))
      · obtain ⟨a, b, hab⟩ := hnonab
        have : a ∈ center T := by rw [h1]; exact mem_top a
        exact hab ((Subgroup.mem_center_iff.mp this b).symm)
  · have hXC : X ≤ centralizer ({k} : Set T) := hNC ▸ hXN
    refine hX1 (hOp X hXC ?_ hX)
    intro c hc y hy
    have hcN : c ∈ normalizer (X : Set T) := by rw [hNC]; exact hc
    exact (Subgroup.mem_normalizer_iff.mp hcN y).mp hy

theorem isCoatom_centralizer_of_equiv {T Γ : Type*} [Group T] [Group Γ] (ψ : T ≃* Γ) (k : T)
    (h : IsCoatom (centralizer ({ψ k} : Set Γ))) : IsCoatom (centralizer ({k} : Set T)) := by
  have hmap : (centralizer ({k} : Set T)).map ψ.toMonoidHom = centralizer ({ψ k} : Set Γ) :=
    CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' ψ k
  refine ⟨fun htop => h.1 ?_, fun M hM => ?_⟩
  · rw [← hmap, htop]
    exact Subgroup.map_top_of_surjective _ ψ.surjective
  · have hlt : (centralizer ({ψ k} : Set Γ)) < M.map ψ.toMonoidHom := by
      rw [← hmap]
      exact lt_of_le_of_ne (Subgroup.map_mono hM.le) (fun heq => hM.ne
        (by
          have := congrArg (Subgroup.comap ψ.toMonoidHom) heq
          rwa [Subgroup.comap_map_eq_self_of_injective ψ.injective,
            Subgroup.comap_map_eq_self_of_injective ψ.injective] at this))
    have htop := h.2 _ hlt
    have := congrArg (Subgroup.comap ψ.toMonoidHom) htop
    rwa [Subgroup.comap_map_eq_self_of_injective ψ.injective, Subgroup.comap_top] at this

theorem mem_of_pPow_of_sup {Γ : Type*} [Group Γ] {t : Γ} (ht : orderOf t = 2) {F : Subgroup Γ}
    (hcomm : ∀ f ∈ F, f * t = t * f) (htF : t ∉ F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : Γ}
    (hy : y ∈ zpowers t ⊔ F) {m : ℕ} (hym : y ^ (p ^ m) = 1) : y ∈ F := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hcomm' : ∀ f ∈ F, t * f * t⁻¹ = f := fun f hf => by
    rw [← hcomm f hf]; group
  have hLE : zpowers t ≤ normalizer (F : Set Γ) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hcomm' x hx]
      exact hx
    · intro hx
      have h1 := hcomm' _ hx
      have h2 : t * x * t⁻¹ = x := by
        have h3 : t * (t * x * t⁻¹) * t⁻¹ = t * x * t⁻¹ := h1
        have h4 : t * (t * x * t⁻¹ * t⁻¹) = t * (x * t⁻¹) := by
          have : t * (t * x * t⁻¹ * t⁻¹) = t * (t * x * t⁻¹) * t⁻¹ := by group
          rw [this, h3]; group
        have h5 := mul_left_cancel h4
        exact mul_right_cancel h5
      rw [← h2]
      exact hx
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) F hLE
  have hy' : y ∈ ((zpowers t : Set Γ) * (F : Set Γ)) := by
    rw [← hmul]; exact hy
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy'
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hodd : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
  have hcm : Commute (t ^ e) b := by
    have : Commute t b := (hcomm b hb).symm
    exact this.zpow_left e
  rw [← hab] at hym ⊢
  rcases Int.even_or_odd' e with ⟨s, rfl | rfl⟩
  · have : t ^ (2 * s) = 1 := by
      rw [zpow_mul]; simp [ht2]
    rw [this, one_mul]
    rw [this, one_mul] at hym
    exact hb
  · exfalso
    have hte : t ^ (2 * s + 1) = t := by
      rw [zpow_add_one, zpow_mul]; simp [ht2]
    rw [hte] at hcm hym
    have hcm' : Commute t b := hcm
    rw [hcm'.mul_pow] at hym
    obtain ⟨r, hr⟩ := hodd
    have htn : t ^ (p ^ m) = t := by
      rw [hr, pow_succ, pow_mul, ht2]; simp
    rw [htn] at hym
    have : t = (b ^ (p ^ m))⁻¹ := eq_inv_of_mul_eq_one_left hym
    exact htF (by rw [this]; exact F.inv_mem (F.pow_mem hb _))

theorem two_dvd_psl_card (q : ℕ) (hq : Odd q) : 2 ∣ q * (q ^ 2 - 1) / 2 := by
  obtain ⟨r, rfl⟩ := hq
  have h1 : (2 * r + 1) ^ 2 - 1 = 4 * (r * (r + 1)) := by
    have : (2 * r + 1) ^ 2 = 4 * (r * (r + 1)) + 1 := by ring
    omega
  obtain ⟨s, hs⟩ := Nat.even_mul_succ_self r
  rw [h1, hs]
  have : (2 * r + 1) * (4 * (s + s)) = 2 * ((2 * r + 1) * (4 * s)) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  exact ⟨(2 * r + 1) * (2 * s), by ring⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
