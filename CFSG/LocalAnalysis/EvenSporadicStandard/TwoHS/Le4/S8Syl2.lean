module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Syl

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix Finset

variable {G : Type*} [Group G]

namespace ECoord

variable (C : ECoord G)

theorem card_E : Nat.card C.E = 256 := by
  rw [Nat.card_congr C.φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  simp [Fintype.card_pi, ZMod.card]

theorem ncard_omega (hQ : Q0Facts) : {e : G | e ∈ C.E ∧ e * e = 1}.ncard = 16 := by
  have : {e : G | e ∈ C.E ∧ e * e = 1} =
      C.elt '' ((Finset.univ.filter fun v : V4 => v + v = 0 : Finset V4) : Set V4) := by
    ext e
    constructor
    · rintro ⟨he, hee⟩
      refine ⟨C.vec e, ?_, C.elt_vec he⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      exact (C.mul_self_eq_one_iff he).1 hee
    · rintro ⟨v, hv, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
      refine ⟨C.elt_mem v, ?_⟩
      rw [← C.elt_add, hv, C.elt_zero]
  rw [this, Set.ncard_image_of_injective _ C.elt_injective, Set.ncard_coe_finset, hQ.om_card]

end ECoord

section SylowFields2

variable [Finite G] {C : ECoord G} {f n : G} {S₀ : Subgroup G} (h : Sect8Hyp C f n S₀)
  (hQ : Q0Facts) {α : M4} (hT : TFacts α)
  (hS : ∀ m ∈ normalizer (C.E : Set G), C.mat m ∈ sList α)
  (hR : ∀ B ∈ sList α, ∃ m ∈ normalizer (C.E : Set G), C.mat m = B)
include h hQ hT hS hR

theorem T_normalizer : ∀ w ∈ normalizer (Tα C hT : Set G), w ∈ normalizer (C.E : Set G) →
    w ∈ Tα C hT := by
  intro w hwT hwE
  have hB : C.mat w ∈ sList α := hS w hwE
  by_contra hw
  have hBn : C.mat w ∉ tList α := fun hB' => hw ⟨hwE, hB'⟩
  obtain ⟨A, hA, hne⟩ := hT.normalizer _ hB hBn
  obtain ⟨z, hz, hzA⟩ := realize_T h hQ hT hS hR A hA
  have hwz : w * z * w⁻¹ ∈ Tα C hT := ((mem_normalizer_iff.1 hwT) z).1 hz
  have key : C.mat (w * z * w⁻¹) * C.mat w = C.mat w * A := by
    rw [C.mat_mul (mul_mem hwE hz.1) (inv_mem hwE), C.mat_mul hwE hz.1, hzA]
    calc C.mat w * A * C.mat w⁻¹ * C.mat w = C.mat w * A * (C.mat w⁻¹ * C.mat w) := by
          rw [mul_assoc]
      _ = C.mat w * A := by rw [C.mat_inv_mul hwE, mul_one]
  exact hne _ hwz.2 key.symm

theorem T_K_cent_small : ∀ x ∈ Kα C hT, x ∉ C.E →
    Nat.card ((centralizer ({x} : Set G)) ⊓ Kα C hT : Subgroup G) < Nat.card C.E := by
  intro x hx hxE
  have hm := K_mat_neg h hQ hT hS hR hx hxE
  have hxn := (mem_Kα.1 hx).1.1
  have hxi : C.mat x⁻¹ = -1 := by
    have h1 := C.mat_inv_mul hxn
    rw [hm] at h1
    have h2 : C.mat x⁻¹ * -1 = -(C.mat x⁻¹) := by simp
    rw [h2] at h1
    exact (neg_eq_iff_eq_neg.1 h1)
  have hsub : ((centralizer ({x} : Set G) ⊓ Kα C hT : Subgroup G) : Set G) ⊆
      {e : G | e ∈ C.E ∧ e * e = 1} ∪ (fun e => e * x) '' {e : G | e ∈ C.E ∧ e * e = 1} := by
    intro y hy
    obtain ⟨hyc, hyK⟩ := Subgroup.mem_inf.1 hy
    have hcomm : x * y = y * x := (Subgroup.mem_centralizer_iff.1 hyc) x rfl
    have hyn := (mem_Kα.1 hyK).1.1
    have inv_of : ∀ e : G, e ∈ C.E → x * e = e * x → e * e = 1 := by
      intro e he hxe
      have h1 : x * e * x⁻¹ = e⁻¹ := by
        calc x * e * x⁻¹ = x * C.elt (C.vec e) * x⁻¹ := by rw [C.elt_vec he]
          _ = C.elt (C.mat x *ᵥ C.vec e) := C.conj_elt hxn _
          _ = C.elt (-(C.vec e)) := by rw [hm, neg_mulVec, one_mulVec]
          _ = (C.elt (C.vec e))⁻¹ := C.elt_neg _
          _ = e⁻¹ := by rw [C.elt_vec he]
      have h2 : x * e * x⁻¹ = e := by
        calc x * e * x⁻¹ = e * x * x⁻¹ := by rw [hxe]
          _ = e := by group
      exact mul_eq_one_iff_eq_inv.2 (h1.symm.trans h2).symm
    rcases K_mat h hQ hT hS hR hyK with h1 | h1
    · left
      have hyE := h.mem_E_of_mat_eq_one hyn h1
      exact ⟨hyE, inv_of y hyE hcomm⟩
    · right
      have hmat_e : C.mat (y * x⁻¹) = 1 := by
        rw [C.mat_mul hyn (inv_mem hxn), h1, hxi]
        simp
      have heE := h.mem_E_of_mat_eq_one (mul_mem hyn (inv_mem hxn)) hmat_e
      refine ⟨y * x⁻¹, ⟨heE, inv_of _ heE ?_⟩, by group⟩
      calc x * (y * x⁻¹) = (x * y) * x⁻¹ := by group
        _ = (y * x) * x⁻¹ := by rw [hcomm]
        _ = y * x⁻¹ * x * x⁻¹ * x * x⁻¹ * x := by group
        _ = (y * x⁻¹) * x := by group
  have hcard : Nat.card ((centralizer ({x} : Set G)) ⊓ Kα C hT : Subgroup G) ≤ 32 := by
    calc Nat.card ((centralizer ({x} : Set G)) ⊓ Kα C hT : Subgroup G)
        = ((centralizer ({x} : Set G) ⊓ Kα C hT : Subgroup G) : Set G).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ ({e : G | e ∈ C.E ∧ e * e = 1} ∪
          (fun e => e * x) '' {e : G | e ∈ C.E ∧ e * e = 1}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ {e : G | e ∈ C.E ∧ e * e = 1}.ncard +
          ((fun e => e * x) '' {e : G | e ∈ C.E ∧ e * e = 1}).ncard := Set.ncard_union_le _ _
      _ ≤ {e : G | e ∈ C.E ∧ e * e = 1}.ncard + {e : G | e ∈ C.E ∧ e * e = 1}.ncard :=
          Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
      _ = 32 := by rw [C.ncard_omega hQ]
  rw [C.card_E]
  omega

theorem sylowData (hf2 : f ^ 2 = C.elt tVec) :
    Sect7SylowData (f ^ 2) (Tα C hT) C.E (C.Fsub hQ) (Kα C hT) where
  pgroup := T_pgroup h hQ hT hS hR
  E_le := E_le_Tsub
  F_le := fun x hx => hx.1
  K_le := inf_le_left
  E_comm := fun a ha b hb => C.comm ha hb
  F_exp := fun x hx => C.Fsub_mul_self hQ hx
  E_inv := by
    intro x hx hxx
    have h1 : C.vec x + C.vec x = 0 := (C.mul_self_eq_one_iff hx).1 hxx
    rcases hQ.om_f _ h1 with h2 | h2
    · exact Or.inl ⟨hx, h2⟩
    · refine Or.inr ⟨C.elt (C.vec x - tVec), ⟨C.elt_mem _, ?_⟩, ?_⟩
      · rw [C.vec_elt]; exact h2
      · rw [hf2, ← C.elt_add, add_sub_cancel, C.elt_vec hx]
  E_sq_onto := by
    intro x hx hxx
    have h1 : C.vec x + C.vec x = 0 := (C.mul_self_eq_one_iff hx).1 hxx
    obtain ⟨w, hw⟩ := hQ.om_sq _ h1
    refine ⟨C.elt w, C.elt_mem w, ?_⟩
    rw [← C.elt_add, hw, C.elt_vec hx]
  star := T_star h hQ hT hS hR
  F_small := T_F_small h hQ hT hS hR
  tF_large := T_tF_large h hQ hT hS hR hf2
  CF_sq := T_CF_sq h hQ hT hS hR
  K_def := T_K_def h hQ hT hS hR
  K_cent_small := T_K_cent_small h hQ hT hS hR
  normalizer_M1 := T_normalizer h hQ hT hS hR

end SylowFields2

end CFSG.EvenSporadicStandard.TwoHS
