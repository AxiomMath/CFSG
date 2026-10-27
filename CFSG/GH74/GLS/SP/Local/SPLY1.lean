module

public import CFSG.GH74.GLS.SP.Local.SPLStages
public import CFSG.GH74.GLS.LU.Local.GenCore

public section

open Subgroup CFSG CFSG.GH74.BNPair CFSG.GH74.GLS.LU.Local
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section Y1

variable {G : Type} [Group G]

theorem mem_conjBy_conj {t : G} (ht : t * t = 1) {X₁ : Subgroup G} {u : G} (hu : u ∈ X₁) :
    t * u * t⁻¹ ∈ conjBy t X₁ := by
  rw [mem_conjBy_iff]
  have e : t * (t * u * t⁻¹) * t⁻¹ = u := by
    calc t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
      _ = u := by rw [ht]; group
  rw [e]; exact hu

theorem commDiag_mul {t : G} (ht : t * t = 1) {X₁ : Subgroup G}
    (hab : ∀ a ∈ X₁, ∀ b ∈ X₁, a * b = b * a)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ conjBy t X₁, a * b = b * a) {u v : G} (hu : u ∈ X₁) (hv : v ∈ X₁) :
    (u * v) * (t * (u * v)⁻¹ * t⁻¹) = (u * (t * u⁻¹ * t⁻¹)) * (v * (t * v⁻¹ * t⁻¹)) := by
  have ha : t * u⁻¹ * t⁻¹ ∈ conjBy t X₁ := mem_conjBy_conj ht (X₁.inv_mem hu)
  have hb : t * v⁻¹ * t⁻¹ ∈ conjBy t X₁ := mem_conjBy_conj ht (X₁.inv_mem hv)
  have hba : (t * v⁻¹ * t⁻¹) * (t * u⁻¹ * t⁻¹) = (t * u⁻¹ * t⁻¹) * (t * v⁻¹ * t⁻¹) := by
    have := hab v⁻¹ (X₁.inv_mem hv) u⁻¹ (X₁.inv_mem hu)
    calc (t * v⁻¹ * t⁻¹) * (t * u⁻¹ * t⁻¹) = t * (v⁻¹ * u⁻¹) * t⁻¹ := by group
      _ = t * (u⁻¹ * v⁻¹) * t⁻¹ := by rw [this]
      _ = (t * u⁻¹ * t⁻¹) * (t * v⁻¹ * t⁻¹) := by group
  have hva : v * (t * u⁻¹ * t⁻¹) = (t * u⁻¹ * t⁻¹) * v := hcomm v hv _ ha
  have hvb : v * (t * v⁻¹ * t⁻¹) = (t * v⁻¹ * t⁻¹) * v := hcomm v hv _ hb
  have e : t * (u * v)⁻¹ * t⁻¹ = (t * v⁻¹ * t⁻¹) * (t * u⁻¹ * t⁻¹) := by group
  rw [e]
  calc u * v * ((t * v⁻¹ * t⁻¹) * (t * u⁻¹ * t⁻¹))
      = u * (v * ((t * v⁻¹ * t⁻¹) * (t * u⁻¹ * t⁻¹))) := by group
    _ = u * (v * ((t * u⁻¹ * t⁻¹) * (t * v⁻¹ * t⁻¹))) := by rw [hba]
    _ = u * ((v * (t * u⁻¹ * t⁻¹)) * (t * v⁻¹ * t⁻¹)) := by group
    _ = u * (((t * u⁻¹ * t⁻¹) * v) * (t * v⁻¹ * t⁻¹)) := by rw [hva]
    _ = (u * (t * u⁻¹ * t⁻¹)) * (v * (t * v⁻¹ * t⁻¹)) := by group

@[expose] def commDiagHom {t : G} (ht : t * t = 1) {X₁ : Subgroup G}
    (hab : ∀ a ∈ X₁, ∀ b ∈ X₁, a * b = b * a)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ conjBy t X₁, a * b = b * a) : ↥X₁ →* G where
  toFun u := (u : G) * (t * (u : G)⁻¹ * t⁻¹)
  map_one' := by simp
  map_mul' u v := by
    simpa using commDiag_mul ht hab hcomm u.2 v.2

theorem commDiagHom_apply {t : G} (ht : t * t = 1) {X₁ : Subgroup G}
    (hab : ∀ a ∈ X₁, ∀ b ∈ X₁, a * b = b * a)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ conjBy t X₁, a * b = b * a) (u : ↥X₁) :
    commDiagHom ht hab hcomm u = (u : G) * (t * (u : G)⁻¹ * t⁻¹) := rfl

theorem commDiagHom_injective {t : G} (ht : t * t = 1) {X₁ : Subgroup G}
    (hab : ∀ a ∈ X₁, ∀ b ∈ X₁, a * b = b * a)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ conjBy t X₁, a * b = b * a) (hinter : X₁ ⊓ conjBy t X₁ = ⊥) :
    Function.Injective (commDiagHom ht hab hcomm) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  rw [commDiagHom_apply] at hu
  have h1 : (u : G) = (t * (u : G)⁻¹ * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hu
  have h2 : (u : G) ∈ conjBy t X₁ := by
    rw [h1]
    refine Subgroup.inv_mem _ (mem_conjBy_conj ht (X₁.inv_mem u.2))
  have h3 : (u : G) ∈ X₁ ⊓ conjBy t X₁ := ⟨u.2, h2⟩
  rw [hinter] at h3
  exact Subtype.ext (Subgroup.mem_bot.mp h3)

theorem commutator_eq_range {t : G} (ht : t * t = 1) {X₁ : Subgroup G}
    (hab : ∀ a ∈ X₁, ∀ b ∈ X₁, a * b = b * a)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ conjBy t X₁, a * b = b * a) :
    ⁅X₁ ⊔ conjBy t X₁, zpowers t⁆ = (commDiagHom ht hab hcomm).range := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx g hg
    have hgt : g = 1 ∨ g = t := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
      have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
      rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
      · left; rw [zpow_mul, h2, one_zpow]
      · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
    rcases hgt with hg1 | hg1
    · rw [hg1]
      simp [commutatorElement_def]
    · rw [hg1]
      obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ X₁, ∃ b ∈ conjBy t X₁, x = a * b :=
        mem_sup_of_commute hcomm hx
      have hb' : t * b * t⁻¹ ∈ X₁ := by
        have := (mem_conjBy_iff).mp hb
        exact this
      have hb'' : t * b⁻¹ * t⁻¹ ∈ X₁ := by
        have e : t * b⁻¹ * t⁻¹ = (t * b * t⁻¹)⁻¹ := by group
        rw [e]; exact X₁.inv_mem hb'
      have hu : a * (t * b⁻¹ * t⁻¹) ∈ X₁ := X₁.mul_mem ha hb''
      refine ⟨⟨a * (t * b⁻¹ * t⁻¹), hu⟩, ?_⟩
      show (a * (t * b⁻¹ * t⁻¹)) * (t * (a * (t * b⁻¹ * t⁻¹))⁻¹ * t⁻¹) = ⁅a * b, t⁆
      have hcb : (t * b⁻¹ * t⁻¹) * b = b * (t * b⁻¹ * t⁻¹) := hcomm _ hb'' b hb
      have e1 : t * (a * (t * b⁻¹ * t⁻¹))⁻¹ * t⁻¹ = b * (t * a⁻¹ * t⁻¹) := by
        calc t * (a * (t * b⁻¹ * t⁻¹))⁻¹ * t⁻¹
            = (t * t) * b * (t * t)⁻¹ * (t * a⁻¹ * t⁻¹) := by group
          _ = b * (t * a⁻¹ * t⁻¹) := by rw [ht]; group
      rw [e1, commutatorElement_def]
      calc a * (t * b⁻¹ * t⁻¹) * (b * (t * a⁻¹ * t⁻¹))
          = a * ((t * b⁻¹ * t⁻¹) * b) * (t * a⁻¹ * t⁻¹) := by group
        _ = a * (b * (t * b⁻¹ * t⁻¹)) * (t * a⁻¹ * t⁻¹) := by rw [hcb]
        _ = a * b * t * (a * b)⁻¹ * t⁻¹ := by group
  · rintro _ ⟨u, rfl⟩
    have hu : (u : G) ∈ X₁ ⊔ conjBy t X₁ := Subgroup.mem_sup_left u.2
    have := Subgroup.commutator_mem_commutator hu (mem_zpowers t)
    simpa [commutatorElement_def, commDiagHom_apply, mul_assoc] using this

theorem Y1_spec {p : ℕ} {t : G} (ht : t * t = 1) {X₁ : Subgroup G} (hX : IsEAb p X₁)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ conjBy t X₁, a * b = b * a) (hinter : X₁ ⊓ conjBy t X₁ = ⊥) :
    ∃ φ : ↥X₁ ≃* ↥(⁅X₁ ⊔ conjBy t X₁, zpowers t⁆),
      (∀ u : ↥X₁, (φ u : G) = (u : G) * (t * (u : G)⁻¹ * t⁻¹)) ∧
      IsEAb p ⁅X₁ ⊔ conjBy t X₁, zpowers t⁆ ∧
      (∀ y ∈ ⁅X₁ ⊔ conjBy t X₁, zpowers t⁆, t * y * t⁻¹ = y⁻¹) ∧
      Nat.card ↥(⁅X₁ ⊔ conjBy t X₁, zpowers t⁆) = Nat.card ↥X₁ := by
  have hab := hX.1
  have hinj := commDiagHom_injective ht hab hcomm hinter
  have hrange := commutator_eq_range ht hab hcomm
  let φ₀ : ↥X₁ ≃* ↥(commDiagHom ht hab hcomm).range :=
    MonoidHom.ofInjective hinj
  let φ : ↥X₁ ≃* ↥(⁅X₁ ⊔ conjBy t X₁, zpowers t⁆) :=
    φ₀.trans (MulEquiv.subgroupCongr hrange.symm)
  have hφ : ∀ u : ↥X₁, (φ u : G) = (u : G) * (t * (u : G)⁻¹ * t⁻¹) := fun u => rfl
  have hmem : ∀ y ∈ ⁅X₁ ⊔ conjBy t X₁, zpowers t⁆, ∃ u : ↥X₁, y = (u : G) * (t * (u : G)⁻¹ * t⁻¹) := by
    intro y hy
    rw [hrange] at hy
    obtain ⟨u, rfl⟩ := hy
    exact ⟨u, rfl⟩
  refine ⟨φ, hφ, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro y hy y' hy'
    obtain ⟨u, rfl⟩ := hmem y hy
    obtain ⟨u', rfl⟩ := hmem y' hy'
    have h1 := (commDiagHom ht hab hcomm).map_mul u u'
    have h2 := (commDiagHom ht hab hcomm).map_mul u' u
    have hcu : u * u' = u' * u := Subtype.ext (hab u u.2 u' u'.2)
    rw [hcu] at h1
    simp only [commDiagHom_apply] at h1 h2
    exact h1.symm.trans h2
  · intro y hy
    obtain ⟨u, rfl⟩ := hmem y hy
    have h1 := (commDiagHom ht hab hcomm).map_pow u p
    have hup : u ^ p = 1 := Subtype.ext (hX.2 u u.2)
    rw [hup, map_one] at h1
    simpa [commDiagHom_apply] using h1.symm
  · intro y hy
    obtain ⟨u, rfl⟩ := hmem y hy
    calc t * ((u : G) * (t * (u : G)⁻¹ * t⁻¹)) * t⁻¹
        = (t * (u : G) * t⁻¹) * (t * t) * (u : G)⁻¹ * (t * t)⁻¹ := by group
      _ = (t * (u : G) * t⁻¹) * (u : G)⁻¹ := by rw [ht]; group
      _ = ((u : G) * (t * (u : G)⁻¹ * t⁻¹))⁻¹ := by group
  · exact (Nat.card_congr φ.toEquiv).symm

end Y1

end CFSG.GH74.GLS.SP.Local
