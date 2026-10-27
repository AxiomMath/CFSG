module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G]

@[expose] def cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g x : G} {H : Subgroup G} : x ∈ cj g H ↔ g⁻¹ * x * g ∈ H := by
  simp only [cj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    convert hy using 1
    group
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by group⟩

theorem conj_mem_cj {g a : G} {H : Subgroup G} (ha : a ∈ H) : g * a * g⁻¹ ∈ cj g H := by
  rw [mem_cj]
  convert ha using 1
  group

theorem cj_cj (g h : G) (H : Subgroup G) : cj g (cj h H) = cj (g * h) H := by
  ext x
  rw [mem_cj, mem_cj, mem_cj]
  have e : h⁻¹ * (g⁻¹ * x * g) * h = (g * h)⁻¹ * x * (g * h) := by group
  rw [e]

theorem cj_one (H : Subgroup G) : cj (1 : G) H = H := by
  ext x
  rw [mem_cj]
  simp

theorem cj_inf (g : G) (A B : Subgroup G) : cj g (A ⊓ B) = cj g A ⊓ cj g B := by
  simp only [cj]
  exact Subgroup.map_inf_eq A B (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem cj_sup (g : G) (A B : Subgroup G) : cj g (A ⊔ B) = cj g A ⊔ cj g B := by
  simp only [cj]
  exact Subgroup.map_sup A B (MulAut.conj g).toMonoidHom

theorem cj_mono {g : G} {A B : Subgroup G} (h : A ≤ B) : cj g A ≤ cj g B := by
  simp only [cj]
  exact Subgroup.map_mono h

theorem cj_injective (g : G) : Function.Injective (cj g) := by
  intro A B h
  have h1 : cj g⁻¹ (cj g A) = cj g⁻¹ (cj g B) := by rw [h]
  rw [cj_cj, inv_mul_cancel, cj_one, cj_cj, inv_mul_cancel, cj_one] at h1
  exact h1

theorem card_cj (g : G) (H : Subgroup G) : Nat.card (cj g H) = Nat.card H := by
  simpa only [cj] using
    Subgroup.card_map_of_injective (K := H) (MulAut.conj g).injective

theorem isPGroup_cj {p : ℕ} {g : G} {H : Subgroup G} (h : IsPGroup p H) : IsPGroup p (cj g H) := by
  have e : ↥H ≃* ↥(cj g H) :=
    Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact h.of_equiv e

theorem isElemAbelian_cj {g : G} {H : Subgroup G} (h : CFSG.Open.IsElemAbelian 2 H) :
    CFSG.Open.IsElemAbelian 2 (cj g H) := by
  obtain ⟨hcomm, hpow⟩ := h
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    have ha : g⁻¹ * (a : G) * g ∈ H := (mem_cj (H := H)).mp a.2
    have hb : g⁻¹ * (b : G) * g ∈ H := (mem_cj (H := H)).mp b.2
    haveI : IsMulCommutative ↥H := hcomm
    have key : (g⁻¹ * (a : G) * g) * (g⁻¹ * (b : G) * g) =
        (g⁻¹ * (b : G) * g) * (g⁻¹ * (a : G) * g) :=
      congrArg Subtype.val (mul_comm' (⟨g⁻¹ * (a : G) * g, ha⟩ : ↥H)
        (⟨g⁻¹ * (b : G) * g, hb⟩ : ↥H))
    have h1 : g * ((g⁻¹ * (a : G) * g) * (g⁻¹ * (b : G) * g)) * g⁻¹ =
        (a : G) * (b : G) := by group
    have h2 : g * ((g⁻¹ * (b : G) * g) * (g⁻¹ * (a : G) * g)) * g⁻¹ =
        (b : G) * (a : G) := by group
    have hcongr := congrArg (fun z => g * z * g⁻¹) key
    rw [h1, h2] at hcongr
    exact hcongr
  · intro x hx
    have hxH : g⁻¹ * x * g ∈ H := (mem_cj (H := H)).mp hx
    have hx2 : (g⁻¹ * x * g) ^ 2 = 1 := hpow _ hxH
    have e : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
      rw [pow_two, pow_two]
      group
    rw [e] at hx2
    have h1 : g * (g⁻¹ * x ^ 2 * g) * g⁻¹ = x ^ 2 := by group
    have h2 : g * 1 * g⁻¹ = (1 : G) := by group
    have hcongr := congrArg (fun z => g * z * g⁻¹) hx2
    rw [h1, h2] at hcongr
    exact hcongr

theorem cj_centralizer (g : G) (A : Subgroup G) :
    cj g (centralizer (A : Set G)) = centralizer ((cj g A : Subgroup G) : Set G) := by
  ext x
  rw [mem_cj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    have hyA : g⁻¹ * y * g ∈ A := (mem_cj (H := A)).mp hy
    have h := hx (g⁻¹ * y * g) hyA
    have e1 : g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ = y * x := by group
    have e2 : g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ = x * y := by group
    have h' := congrArg (fun z => g * z * g⁻¹) h
    rw [e1, e2] at h'
    exact h'
  · intro hx h hh
    have hy : g * h * g⁻¹ ∈ cj g A := conj_mem_cj hh
    have hcomm := hx (g * h * g⁻¹) hy
    have e1 : g⁻¹ * ((g * h * g⁻¹) * x) * g = h * (g⁻¹ * x * g) := by group
    have e2 : g⁻¹ * (x * (g * h * g⁻¹)) * g = (g⁻¹ * x * g) * h := by group
    have hcongr := congrArg (fun z => g⁻¹ * z * g) hcomm
    rw [e1, e2] at hcongr
    exact hcongr

theorem cj_commutator (g : G) (A B : Subgroup G) : cj g ⁅A, B⁆ = ⁅cj g A, cj g B⁆ := by
  simpa only [cj] using
    Subgroup.map_commutator A B (MulAut.conj g).toMonoidHom

theorem cj_eq_self_of_centralizes {c : G} {H : Subgroup G} (h : ∀ x ∈ H, c * x * c⁻¹ = x) :
    cj c H = H := by
  ext x
  rw [mem_cj]
  constructor
  · intro hx
    have hh := h (c⁻¹ * x * c) hx
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rw [e] at hh
    rw [hh]
    exact hx
  · intro hx
    have hh := h x hx
    rw [← hh]
    convert hx using 1
    group

theorem cj_eq_self_of_normalizes [Finite G] {c : G} {H : Subgroup G}
    (h : ∀ x ∈ H, c * x * c⁻¹ ∈ H) : cj c H = H := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    have hxH : c⁻¹ * x * c ∈ H := (mem_cj (H := H)).mp hx
    have hc := h (c⁻¹ * x * c) hxH
    convert hc using 1
    group
  · rw [card_cj]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
