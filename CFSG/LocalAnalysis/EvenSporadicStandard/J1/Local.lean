module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Setting

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

@[expose] def NL : Subgroup G := normalizer (H.E : Set G) ⊓ H.L

@[expose] def B : Subgroup G := normalizer (H.V : Set G) ⊓ centralizer ({H.z} : Set G)

theorem V_inf_L : H.V ⊓ H.L = H.E := by
  refine le_antisymm (fun y ⟨hyV, hyL⟩ => ?_) (le_inf H.E_le_V H.E_le)
  rcases H.mem_V_iff'.1 hyV with h | ⟨e, he, rfl⟩
  · exact h
  · exfalso
    apply H.z_not_mem_L
    have := mul_mem (inv_mem (H.E_le he)) hyL
    simpa using this

theorem mem_NL_iff {x : G} : x ∈ H.NL ↔ x ∈ H.L ∧ x ∈ normalizer (H.E : Set G) := by
  unfold NL; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem NL_le_centralizer_z : H.NL ≤ centralizer ({H.z} : Set G) := fun x hx => by
  rw [mem_centralizer_singleton_iff]
  exact H.comm_z ((H.mem_NL_iff.1 hx).1)


theorem mem_B_def {x : G} :
    x ∈ H.B ↔ x ∈ normalizer (H.V : Set G) ∧ x ∈ centralizer ({H.z} : Set G) :=
  Subgroup.mem_inf

theorem z_mem_B : H.z ∈ H.B := by
  refine H.mem_B_def.2 ⟨le_normalizer H.z_mem_V, ?_⟩
  exact mem_centralizer_singleton_iff.2 rfl

theorem NL_le_B : H.NL ≤ H.B := by
  intro x hx
  obtain ⟨hxL, hxN⟩ := H.mem_NL_iff.1 hx
  refine H.mem_B_def.2 ⟨?_, H.NL_le_centralizer_z hx⟩
  rw [mem_normalizer_iff]
  intro v
  have hxz := H.comm_z hxL
  have hE := mem_normalizer_iff.1 hxN
  constructor
  · intro hv
    rcases H.mem_V_iff'.1 hv with h | ⟨e, he, rfl⟩
    · exact H.E_le_V ((hE v).1 h)
    · refine H.mem_V_iff'.2 (Or.inr ⟨x * e * x⁻¹, (hE e).1 he, ?_⟩)
      calc x * (e * H.z) * x⁻¹ = x * e * (H.z * x⁻¹) := by group
        _ = x * e * (x⁻¹ * H.z) := by
          have : H.z * x⁻¹ = x⁻¹ * H.z := by
            calc H.z * x⁻¹ = x⁻¹ * (x * H.z) * x⁻¹ := by group
              _ = x⁻¹ * (H.z * x) * x⁻¹ := by rw [hxz]
              _ = x⁻¹ * H.z := by group
          rw [this]
        _ = x * e * x⁻¹ * H.z := by group
  · intro hv
    have hxinv : x⁻¹ ∈ H.NL := inv_mem hx
    obtain ⟨hxL', hxN'⟩ := H.mem_NL_iff.1 hxinv
    have hE' := mem_normalizer_iff.1 hxN'
    have : v = x⁻¹ * (x * v * x⁻¹) * x := by group
    rw [this]
    rcases H.mem_V_iff'.1 hv with h | ⟨e, he, he'⟩
    · exact H.E_le_V (by
        have := (hE' (x * v * x⁻¹)).1 h
        simpa using this)
    · refine H.mem_V_iff'.2 (Or.inr ⟨x⁻¹ * e * x, ?_, ?_⟩)
      · have := (hE' e).1 he
        simpa using this
      · rw [he']
        calc x⁻¹ * (e * H.z) * x = x⁻¹ * e * (H.z * x) := by group
          _ = x⁻¹ * e * (x * H.z) := by rw [← H.comm_z hxL]
          _ = x⁻¹ * e * x * H.z := by group

theorem mem_B_iff {x : G} : x ∈ H.B ↔ x ∈ H.NL ∨ x * H.z ∈ H.NL := by
  constructor
  · intro hx
    obtain ⟨hxN, hxC⟩ := H.mem_B_def.1 hx
    have hxN' : x * H.z ∈ normalizer (H.V : Set G) := mul_mem hxN (le_normalizer H.z_mem_V)
    have key : ∀ y : G, y ∈ H.L → y ∈ normalizer (H.V : Set G) → y ∈ H.NL := by
      intro y hyL hyN
      refine H.mem_NL_iff.2 ⟨hyL, mem_normalizer_iff.2 fun h => ?_⟩
      have hV := mem_normalizer_iff.1 hyN h
      constructor
      · intro hh
        have h1 : y * h * y⁻¹ ∈ H.V := hV.1 (H.E_le_V hh)
        have h2 : y * h * y⁻¹ ∈ H.L := mul_mem (mul_mem hyL (H.E_le hh)) (inv_mem hyL)
        exact H.V_inf_L ▸ (⟨h1, h2⟩ : y * h * y⁻¹ ∈ H.V ⊓ H.L)
      · intro hh
        have h1 : h ∈ H.V := hV.2 (H.E_le_V hh)
        have h2 : h ∈ H.L := by
          have := mul_mem (mul_mem (inv_mem hyL) (H.E_le hh)) hyL
          simpa [mul_assoc] using this
        exact H.V_inf_L ▸ (⟨h1, h2⟩ : h ∈ H.V ⊓ H.L)
    rcases H.mem_centralizer_iff.1 hxC with h | h
    · exact Or.inl (key x h hxN)
    · exact Or.inr (key _ h hxN')
  · rintro (h | h)
    · exact H.NL_le_B h
    · have : x = (x * H.z) * H.z⁻¹ := by group
      rw [this]
      exact mul_mem (H.NL_le_B h) (inv_mem H.z_mem_B)

theorem V_le_B : H.V ≤ H.B := by
  intro x hx
  rcases H.mem_V_iff'.1 hx with h | ⟨e, he, rfl⟩
  · exact H.mem_B_iff.2 (Or.inl (H.mem_NL_iff.2 ⟨H.E_le h, le_normalizer h⟩))
  · exact mul_mem (H.mem_B_iff.2 (Or.inl (H.mem_NL_iff.2 ⟨H.E_le he, le_normalizer he⟩)))
      H.z_mem_B

theorem B_le_centralizer : H.B ≤ centralizer ({H.z} : Set G) := inf_le_right

theorem card_NL : Nat.card H.NL = 168 := H.card_normalizer_E

theorem card_B : Nat.card H.B = 336 := by
  have hBeq : H.B = H.NL ⊔ zpowers H.z := by
    refine le_antisymm (fun x hx => ?_) (sup_le H.NL_le_B (zpowers_le.2 H.z_mem_B))
    rcases H.mem_B_iff.1 hx with h | h
    · exact mem_sup_left h
    · have : x = (x * H.z) * H.z⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left h) (inv_mem (mem_sup_right (mem_zpowers _)))
  have hz : zpowers H.z ≤ centralizer (H.NL : Set G) :=
    zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun x hx =>
      H.comm_z (H.mem_NL_iff.1 hx).1)
  have hd : Disjoint H.NL (zpowers H.z) :=
    H.disjoint.mono_left (fun x hx => (H.mem_NL_iff.1 hx).1)
  have := Nat.card_congr (mulEquivProdSup hz hd).toEquiv
  rw [Nat.card_prod, Nat.card_zpowers, H.order_z, H.card_NL] at this
  rw [hBeq]
  omega


theorem exists_sigma : ∃ σ : G, σ ∈ H.NL ∧ orderOf σ = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := H.NL) 7 (by rw [H.card_NL]; norm_num)
  exact ⟨σ, σ.2, by rw [Subgroup.orderOf_coe]; exact hσ⟩

end Setting

end CFSG.EvenSporadicStandard.J1Std
