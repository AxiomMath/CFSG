module

import CFSG.Goldschmidt.Steps.Sec84b
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem exists_card_le_mul {P E : Subgroup G} {p : ℕ} (hp : p.Prime) {s : G}
    (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hsP : s ∈ Subgroup.normalizer (P : Set G))
    (hs2 : s * s = 1) (hc : IsCyclic (P ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G))
    (hEP : E ≤ P) (hE : ∀ x ∈ E, x ^ p = 1) :
    ∃ K : Subgroup G, K ≤ E ∧ (∀ x ∈ K, s * x * s⁻¹ = x⁻¹) ∧ Nat.card E ≤ p * Nat.card K := by
  have hsx : ∀ x ∈ P, s * x * s⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp hsP x).mp hx
  let φ : E →* G :=
    { toFun := fun x => (x : G) * (s * x * s⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        have hcomm := hP _ (hEP y.2) _ (hsx _ (hEP x.2))
        simp only [Subgroup.coe_mul]
        calc (x : G) * y * (s * (x * y) * s⁻¹) = x * (y * (s * x * s⁻¹)) * (s * y * s⁻¹) := by
              group
          _ = x * ((s * x * s⁻¹) * y) * (s * y * s⁻¹) := by rw [hcomm]
          _ = x * (s * x * s⁻¹) * (y * (s * y * s⁻¹)) := by group }
  have hφ : ∀ x : E, φ x = (x : G) * (s * x * s⁻¹) := fun _ => rfl
  have hrange : φ.range ≤ P ⊓ Subgroup.centralizer ({s} : Set G) := by
    rintro _ ⟨x, rfl⟩
    rw [hφ]
    have hx := hEP x.2
    refine ⟨P.mul_mem hx (hsx _ hx), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hcomm := hP _ hx _ (hsx _ hx)
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    calc (x : G) * (s * x * s⁻¹) * s = x * s * x := by group
      _ = s * s * x * s⁻¹ * x := by rw [hs2, hs', one_mul]
      _ = s * ((s * x * s⁻¹) * x) := by group
      _ = s * (x * (s * x * s⁻¹)) := by rw [hcomm]
  have hcr : IsCyclic φ.range := Subgroup.isCyclic_of_le hrange
  have hrp : Nat.card φ.range ≤ p := by
    have hexp : Monoid.exponent φ.range ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one
      fun y => by
        obtain ⟨x, hx⟩ := y.2
        refine Subtype.ext ?_
        rw [Subgroup.coe_pow, ← hx, ← map_pow]
        have : x ^ p = 1 := Subtype.ext (by simpa using hE x x.2)
        rw [this, map_one, Subgroup.coe_one]
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd hp.pos hexp
  refine ⟨φ.ker.map E.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : φ x = 1 := MonoidHom.mem_ker.mp hx
    rw [hφ] at h1
    simp only [Subgroup.coe_subtype]
    exact eq_inv_of_mul_eq_one_right h1
  · rw [Subgroup.card_map_of_injective E.subtype_injective]
    have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h
    calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := h.symm
      _ ≤ Nat.card φ.ker * p := Nat.mul_le_mul_left _ hrp
      _ = p * Nat.card φ.ker := Nat.mul_comm _ _

theorem card_le_sq {P E : Subgroup G} {p : ℕ} (hp : p.Prime) {b t : G}
    (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hodd : ∀ x ∈ P, x * x = 1 → x = 1)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (ht2 : t * t = 1)
    (hb : ∀ x ∈ P, b * x * b⁻¹ = x⁻¹) (hbt : b * t = t * b) (hb2 : b * b = 1)
    (hc₁ : IsCyclic (P ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G))
    (hc₂ : IsCyclic (P ⊓ Subgroup.centralizer ({b * t} : Set G) : Subgroup G))
    (hEP : E ≤ P) (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 2 := by
  have hbP : b ∈ Subgroup.normalizer (P : Set G) :=
    mem_normalizer_of_conj_le fun x hx => by
      have h := hb x hx
      have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      rw [hbi] at h ⊢
      rw [h]
      exact P.inv_mem hx
  have hbt2 : b * t * (b * t) = 1 := by
    calc b * t * (b * t) = b * (t * b) * t := by group
      _ = b * (b * t) * t := by rw [hbt]
      _ = (b * b) * (t * t) := by group
      _ = 1 := by rw [hb2, ht2, one_mul]
  obtain ⟨K₁, hK₁E, hK₁, h₁⟩ := exists_card_le_mul hp hP htP ht2 hc₁ hEP hE
  obtain ⟨K₂, hK₂E, hK₂, h₂⟩ := exists_card_le_mul hp hP (Subgroup.mul_mem _ hbP htP) hbt2 hc₂
    hEP hE
  have hK : ∀ x ∈ K₁, x ∈ K₂ → x = 1 := fun x hx₁ hx₂ => by
    have e₁ := hK₁ x hx₁
    have e₂ := hK₂ x hx₂
    have hxP := hEP (hK₁E hx₁)
    have e₃ : b * t * x * (b * t)⁻¹ = (t * x * t⁻¹)⁻¹ := by
      rw [← hb _ ((Subgroup.mem_normalizer_iff.mp htP x).mp hxP)]
      group
    rw [e₃, e₁, inv_inv] at e₂
    refine hodd x hxP ?_
    calc x * x = x⁻¹ * x := by rw [← e₂]
      _ = 1 := inv_mul_cancel x
  have h₃ : Nat.card K₁ * Nat.card K₂ ≤ Nat.card E := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun k => ⟨(k.1 : G) * k.2, E.mul_mem (hK₁E k.1.2)
      (hK₂E k.2.2)⟩) fun k k' hkk' => ?_
    have h : (k.1 : G) * k.2 = k'.1 * k'.2 := congrArg Subtype.val hkk'
    have hm : (k'.1 : G)⁻¹ * k.1 = k'.2 * (k.2 : G)⁻¹ := by
      calc (k'.1 : G)⁻¹ * k.1 = (k'.1 : G)⁻¹ * (k.1 * k.2) * (k.2 : G)⁻¹ := by group
        _ = (k'.1 : G)⁻¹ * (k'.1 * k'.2) * (k.2 : G)⁻¹ := by rw [h]
        _ = k'.2 * (k.2 : G)⁻¹ := by group
    have h1 := hK _ (K₁.mul_mem (K₁.inv_mem k'.1.2) k.1.2)
      (hm ▸ K₂.mul_mem k'.2.2 (K₂.inv_mem k.2.2))
    have e1 : (k.1 : G) = k'.1 := by
      calc (k.1 : G) = k'.1 * ((k'.1 : G)⁻¹ * k.1) := by group
        _ = k'.1 := by rw [h1, mul_one]
    have e2 : (k.2 : G) = k'.2 := by
      rw [e1] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  have hE0 : 0 < Nat.card E := Nat.card_pos
  have h4 : Nat.card E * Nat.card E ≤ p ^ 2 * Nat.card E :=
    calc Nat.card E * Nat.card E ≤ (p * Nat.card K₁) * (p * Nat.card K₂) := Nat.mul_le_mul h₁ h₂
      _ = p ^ 2 * (Nat.card K₁ * Nat.card K₂) := by ring
      _ ≤ p ^ 2 * Nat.card E := Nat.mul_le_mul_left _ h₃
  exact Nat.le_of_mul_le_mul_right h4 hE0

end CFSG.Goldschmidt.Sec8
