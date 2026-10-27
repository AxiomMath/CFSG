module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLike

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

@[expose] noncomputable def cInv (H : Subgroup G) (w : G) : ℕ :=
  Nat.card {x : G // x ∈ H ∧ x * x = 1 ∧ x ≠ 1 ∧ x * w = w * x}

theorem cInv_conj {S S' : Subgroup G} {v w : G} (hS : S.map (MulAut.conj v).toMonoidHom = S')
    (hw : v * w * v⁻¹ = w) : cInv S' w = cInv S w := by
  unfold cInv
  set φ := MulAut.conj v
  have hw' : φ w = w := by rw [MulAut.conj_apply, hw]
  refine card_subtype_map φ fun x => ?_
  have e1 : φ x ∈ S' ↔ x ∈ S := by rw [← hS, mem_map_equiv, MulEquiv.symm_apply_apply]
  have e2 : φ x * φ x = 1 ↔ x * x = 1 := by rw [← map_mul, MulEquiv.map_eq_one_iff]
  have e3 : φ x ≠ 1 ↔ x ≠ 1 := by rw [ne_eq, MulEquiv.map_eq_one_iff]
  have e4 : φ x * w = w * φ x ↔ x * w = w * x := by
    conv_lhs => rw [← hw']
    rw [← map_mul, ← map_mul]
    exact φ.injective.eq_iff
  rw [e1, e2, e3, e4]

theorem cInv_iota {S S' : Subgroup G} (ι : S ≃* S') (a : S) : cInv S' (ι a) = cInv S a := by
  unfold cInv
  refine Nat.card_congr
    { toFun := fun y => ⟨ι.symm ⟨y.1, y.2.1⟩, (ι.symm ⟨y.1, y.2.1⟩).2, ?_, ?_, ?_⟩
      invFun := fun x => ⟨ι ⟨x.1, x.2.1⟩, (ι ⟨x.1, x.2.1⟩).2, ?_, ?_, ?_⟩
      left_inv := fun y => by simp
      right_inv := fun x => by simp }
  · have h := y.2.2.1
    have : (⟨y.1, y.2.1⟩ : S') * ⟨y.1, y.2.1⟩ = 1 := Subtype.ext h
    have := congrArg ι.symm this
    rw [map_mul, map_one] at this
    exact congrArg Subtype.val this
  · intro h
    apply y.2.2.2.1
    have : ι.symm ⟨y.1, y.2.1⟩ = 1 := Subtype.ext h
    have := congrArg ι this
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact congrArg Subtype.val this
  · have h := y.2.2.2.2
    have : (⟨y.1, y.2.1⟩ : S') * ι a = ι a * ⟨y.1, y.2.1⟩ := Subtype.ext h
    have := congrArg ι.symm this
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
    exact congrArg Subtype.val this
  · have h := x.2.2.1
    have : (⟨x.1, x.2.1⟩ : S) * ⟨x.1, x.2.1⟩ = 1 := Subtype.ext h
    have := congrArg ι this
    rw [map_mul, map_one] at this
    exact congrArg Subtype.val this
  · intro h
    apply x.2.2.2.1
    have : ι ⟨x.1, x.2.1⟩ = 1 := Subtype.ext h
    have := congrArg ι.symm this
    rw [MulEquiv.symm_apply_apply, map_one] at this
    exact congrArg Subtype.val this
  · have h := x.2.2.2.2
    have : (⟨x.1, x.2.1⟩ : S) * a = a * ⟨x.1, x.2.1⟩ := Subtype.ext h
    have := congrArg ι this
    rw [map_mul, map_mul] at this
    exact congrArg Subtype.val this

theorem eq_one_of_comm {S S' K : Subgroup G} (ι : S ≃* S') (hKS : K ≤ S ⊓ S')
    (hK : ∀ a : S, ((ι a : S') : G) ∈ K → ((ι a : S') : G) ≠ 1 →
      cInv S (ι a : S') ≠ cInv S a)
    {v : G} (hv : S.map (MulAut.conj v).toMonoidHom = S') {w : G} (hwK : w ∈ K)
    (hwv : v * w = w * v) : w = 1 := by
  by_contra hw1
  have hwS' : w ∈ S' := (hKS hwK).2
  set a := ι.symm ⟨w, hwS'⟩
  have hιa : ((ι a : S') : G) = w := by simp [a]
  apply hK a (by rw [hιa]; exact hwK) (by rw [hιa]; exact hw1)
  have h1 : cInv S' w = cInv S w := cInv_conj hv (by rw [hwv]; group)
  have h2 : cInv S' (ι a : S') = cInv S a := cInv_iota ι a
  rw [hιa] at h2 ⊢
  rw [← h1, h2]

variable [Finite G]

theorem card_mul_le_of_inf_eq_bot {A B D : Subgroup G} (hA : A ≤ D) (hB : B ≤ D)
    (h : ∀ x ∈ A, x ∈ B → x = 1) : Nat.card A * Nat.card B ≤ Nat.card D := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p => (⟨p.1 * p.2, D.mul_mem (hA p.1.2) (hB p.2.2)⟩ : D))
    fun p q hpq => ?_
  have e : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val hpq
  have h1 : (q.1 : G)⁻¹ * p.1 = q.2 * (p.2 : G)⁻¹ := by
    calc (q.1 : G)⁻¹ * p.1 = (q.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
      _ = (q.1 : G)⁻¹ * (q.1 * q.2) * (p.2 : G)⁻¹ := by rw [e]
      _ = q.2 * (p.2 : G)⁻¹ := by group
  have h2 := h _ (A.mul_mem (A.inv_mem q.1.2) p.1.2) (h1 ▸ B.mul_mem q.2.2 (B.inv_mem p.2.2))
  have hp1 : (p.1 : G) = q.1 := by
    calc (p.1 : G) = q.1 * ((q.1 : G)⁻¹ * p.1) := by group
      _ = q.1 := by rw [h2]; group
  have hp2 : (p.2 : G) = q.2 := by
    have : (p.2 : G) = (p.1 : G)⁻¹ * (q.1 * q.2) := by rw [← e]; group
    rw [this, hp1]; group
  exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)

omit [Finite G] in
theorem card_le_two_mul {T H C : Subgroup G} (hC : C ≤ T) (hH : H.relIndex T = 2) :
    Nat.card C ≤ 2 * Nat.card (C ⊓ H : Subgroup G) := by
  have h1 := relIndex_mul_card (H := H) (K := C)
  have h2 : H.relIndex C ≤ 2 := hH ▸ relIndex_le_of_le_right hC (by rw [hH]; norm_num)
  rw [inf_comm] at h1
  calc Nat.card C = H.relIndex C * Nat.card (C ⊓ H : Subgroup G) := h1.symm
    _ ≤ 2 * Nat.card (C ⊓ H : Subgroup G) := Nat.mul_le_mul_right _ h2

theorem card_centralizer_le {S S' K T₁ T₂ : Subgroup G} (ι : S ≃* S') (hKS : K ≤ S ⊓ S')
    (hK : ∀ a : S, ((ι a : S') : G) ∈ K → ((ι a : S') : G) ≠ 1 →
      cInv S (ι a : S') ≠ cInv S a)
    (hS : S.relIndex T₁ = 2) (hT : T₁.relIndex T₂ = 2)
    {v : G} (hv : S.map (MulAut.conj v).toMonoidHom = S') :
    Nat.card K * Nat.card (T₂ ⊓ centralizer ({v} : Set G) : Subgroup G) ≤
      4 * Nat.card (S ⊓ S' : Subgroup G) := by
  set C₂ := T₂ ⊓ centralizer ({v} : Set G)
  set C₁ := C₂ ⊓ T₁
  set C₀ := C₁ ⊓ S
  have hC₀D : C₀ ≤ S ⊓ S' := by
    intro x hx
    have hxS : x ∈ S := hx.2
    have hxv := mem_centralizer_singleton_iff.1 hx.1.1.2
    refine ⟨hxS, ?_⟩
    rw [← hv]
    refine ⟨x, hxS, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxv.symm]; group
  have hbot : ∀ x ∈ C₀, x ∈ K → x = 1 := fun x hx hxK =>
    eq_one_of_comm ι hKS hK hv hxK (mem_centralizer_singleton_iff.1 hx.1.1.2).symm
  have h0 := card_mul_le_of_inf_eq_bot hC₀D hKS hbot
  have h1 : Nat.card C₁ ≤ 2 * Nat.card C₀ :=
    card_le_two_mul (T := T₁) inf_le_right hS
  have h2 : Nat.card C₂ ≤ 2 * Nat.card C₁ :=
    card_le_two_mul (T := T₂) inf_le_left hT
  calc Nat.card K * Nat.card C₂ ≤ Nat.card K * (4 * Nat.card C₀) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 4 * (Nat.card C₀ * Nat.card K) := by ring
    _ ≤ 4 * Nat.card (S ⊓ S' : Subgroup G) := Nat.mul_le_mul_left _ h0

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
