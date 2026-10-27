module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldDef
public import CFSG.GH74.BNPair.Cells
public import CFSG.GH74.GLS.SP.Local.SPLFaith

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem chainProd_map_mem (f : X →* X) (A : ℤ → Subgroup X) :
    ∀ l : List ℤ, (∀ k ∈ l, ∀ y ∈ A k, f y ∈ A k) → ∀ u ∈ chainProd A l, f u ∈ chainProd A l
  | [], _, u, hu => by
    simp only [chainProd, List.map_nil, List.prod_nil, Set.mem_one] at hu ⊢
    rw [hu, map_one]
  | k :: l, hA, u, hu => by
    rw [chainProd_cons] at hu ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hu
    exact ⟨f a, hA k List.mem_cons_self a ha, f b,
      chainProd_map_mem f A l (fun k' hk' => hA k' (List.mem_cons_of_mem _ hk')) b hb,
      by rw [map_mul]⟩

structure FoldStab (R : RGD2 6 H r₁ r₂ U root) (θ : X ≃* X) : Prop where
  mem_H : ∀ h ∈ H, θ h ∈ H
  mem_root : ∀ k, IsRoot 6 k → ∀ x ∈ root k, θ x ∈ root k
  r₁_mem : r₁⁻¹ * θ r₁ ∈ H
  r₂_mem : r₂⁻¹ * θ r₂ ∈ H

namespace FoldStab

variable {R : RGD2 6 H r₁ r₂ U root} {θ : X ≃* X}

theorem lift_mem (hS : FoldStab R θ) {m : X} (hm : m ∈ R.N) : m⁻¹ * θ m ∈ H := by
  unfold RGD2.N at hm
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact H.mul_mem (H.inv_mem hx) (hS.mem_H x hx)
    · rcases hx with rfl | rfl
      · exact hS.r₁_mem
      · exact hS.r₂_mem
  | one => simp
  | mul x y hxN hyN hx hy =>
    have h1 : y⁻¹ * (x⁻¹ * θ x) * y ∈ H := (R.N_normalizes_H hyN _ hx).2
    have e : (x * y)⁻¹ * θ (x * y) = (y⁻¹ * (x⁻¹ * θ x) * y) * (y⁻¹ * θ y) := by
      rw [map_mul]; group
    rw [e]
    exact H.mul_mem h1 hy
  | inv x hxN hx =>
    have h1 : x * (x⁻¹ * θ x)⁻¹ * x⁻¹ ∈ H := (R.N_normalizes_H hxN _ (H.inv_mem hx)).1
    have e : (x⁻¹)⁻¹ * θ x⁻¹ = x * (x⁻¹ * θ x)⁻¹ * x⁻¹ := by
      rw [map_inv]; group
    rw [e]
    exact h1

theorem mem_U (hS : FoldStab R θ) {u : X} (hu : u ∈ U) : θ u ∈ U := by
  have hu' : u ∈ chainProd root (intList 1 ((6 : ℕ) : ℤ)) := by rw [← R.carrier_eq]; exact hu
  have := chainProd_map_mem θ.toMonoidHom root _ (fun k hk y hy => by
    have hk' := mem_intList_iff.1 hk
    exact hS.mem_root k (isRoot_of_pos_le hk'.1 hk'.2) y hy) u hu'
  rw [← R.carrier_eq] at this
  exact this

theorem cell (hS : FoldStab R θ) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1) {x : X}
    (hx : θ x = x) :
    ∃ v ∈ U ⊓ foldFix θ, ∃ n ∈ R.N ⊓ foldFix θ, ∃ u ∈ U ⊓ foldFix θ, x = v * n * u := by
  classical
  have := R.cartan_normal
  let D : RankTwoSystem X 6 := (R.toPre hgen).toSystem (R.faithful hgen hZ)
  obtain ⟨u, hu, b, hb, hxe⟩ := D.exists_coord x
  set m : D.N := D.lift (D.bw x) with hm
  have hmN : (m : X) ∈ R.N := m.2
  have hbB : b ∈ H ⊔ U := hb
  have huU : u ∈ U := hu.1
  have hc := hS.lift_mem hmN
  set c : X := (m : X)⁻¹ * θ (m : X) with hcdef
  have hθm : θ (m : X) = (m : X) * c := by rw [hcdef]; group
  have hUminusH : ∀ h ∈ H, ∀ y ∈ D.Uminus, h * y * h⁻¹ ∈ D.Uminus := by
    intro h hh y hy
    have := chainProd_map_mem (MulAut.conj h).toMonoidHom root ((intList 1 ((6 : ℕ) : ℤ)).map Neg.neg)
      (fun k hk z hz => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
        have hj' := mem_intList_iff.1 hj
        have := R.invariant (-j) ⟨by omega, by omega⟩ h hh z hz
        simpa [MulAut.conj_apply] using this) y hy
    exact this
  have hUminusθ : ∀ y ∈ D.Uminus, θ y ∈ D.Uminus := by
    intro y hy
    exact chainProd_map_mem θ.toMonoidHom root ((intList 1 ((6 : ℕ) : ℤ)).map Neg.neg)
      (fun k hk z hz => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
        have hj' := mem_intList_iff.1 hj
        exact hS.mem_root (-j) ⟨by omega, by omega⟩ z hz) y hy
  have hUwH : ∀ h ∈ H, ∀ y ∈ D.UwMinus m, h * y * h⁻¹ ∈ D.UwMinus m := by
    intro h hh y hy
    refine ⟨R.conj_mem_U hh hy.1, ?_⟩
    have h1 : (m : X) * (h * y * h⁻¹) * (m : X)⁻¹ =
        ((m : X) * h * (m : X)⁻¹) * ((m : X) * y * (m : X)⁻¹) * ((m : X) * h * (m : X)⁻¹)⁻¹ := by
      group
    rw [h1]
    have h2 : (m : X) * h * (m : X)⁻¹ ∈ H := (R.N_normalizes_H hmN h hh).1
    have h3 := hUminusH _ h2 _ hy.2
    simpa [mul_assoc] using h3
  have hθu : θ u ∈ D.UwMinus m := by
    have h1 : c * θ u * c⁻¹ ∈ D.UwMinus m := by
      refine ⟨R.conj_mem_U hc (hS.mem_U huU), ?_⟩
      have h2 := hUminusθ _ hu.2
      have e : θ ((m : X) * u * (m : X)⁻¹) = (m : X) * (c * θ u * c⁻¹) * (m : X)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hθm]; group
      rw [e] at h2
      exact h2
    have h3 := hUwH c⁻¹ (H.inv_mem hc) _ h1
    simpa [mul_assoc] using h3
  have hη : (m : X) * c * (m : X)⁻¹ ∈ H := (R.N_normalizes_H hmN c hc).1
  obtain ⟨v, hv, h, hh, rfl⟩ := (R.mem_sup_iff_UH).1 hbB
  set η : X := θ h * ((m : X) * c * (m : X)⁻¹) with hηdef
  have hηH : η ∈ H := H.mul_mem (hS.mem_H h hh) hη
  have hb' : θ v * η ∈ D.B := by
    exact (H ⊔ U).mul_mem ((le_sup_right : U ≤ H ⊔ U) (hS.mem_U hv))
      ((le_sup_left : H ≤ H ⊔ U) hηH)
  have hxθ : (θ v * η) * (m : X) * θ u = (v * h) * (m : X) * u := by
    have h1 : θ (v * h * (m : X) * u) = x := by rw [← hxe]; exact hx
    rw [map_mul, map_mul, map_mul, hθm] at h1
    calc (θ v * η) * (m : X) * θ u = θ v * θ h * ((m : X) * c) * θ u := by rw [hηdef]; group
      _ = x := h1
      _ = (v * h) * (m : X) * u := hxe
  have hu_eq : θ u = u := D.coord_unique m hb' hbB hθu hu hxθ
  rw [hu_eq] at hxθ
  have hbb : θ v * η = v * h := mul_right_cancel (mul_right_cancel hxθ)
  have h5 : v⁻¹ * θ v = h * η⁻¹ := by
    have : θ v = v * h * η⁻¹ := by
      calc θ v = (θ v * η) * η⁻¹ := by group
        _ = v * h * η⁻¹ := by rw [hbb]
    rw [this]; group
  have hU1 : v⁻¹ * θ v ∈ U ⊓ H := ⟨U.mul_mem (U.inv_mem hv) (hS.mem_U hv), by
    rw [h5]; exact H.mul_mem hh (H.inv_mem hηH)⟩
  rw [R.U_inf_H, Subgroup.mem_bot] at hU1
  have hθv : θ v = v := by
    have := hU1
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hηh : η = h := by
    rw [hθv] at hbb
    exact mul_left_cancel hbb
  refine ⟨v, ⟨hv, hθv⟩, h * (m : X), ⟨R.N.mul_mem (R.H_le_N hh) hmN, ?_⟩, u, ⟨huU, hu_eq⟩, ?_⟩
  · show θ (h * (m : X)) = h * (m : X)
    rw [map_mul, hθm]
    calc θ h * ((m : X) * c) = (θ h * ((m : X) * c * (m : X)⁻¹)) * (m : X) := by group
      _ = η * (m : X) := rfl
      _ = h * (m : X) := by rw [hηh]
  · rw [hxe]; group

theorem chain_factors_fixed (hS : FoldStab R θ) {F : ℤ → X}
    (hF : ∀ k ∈ intList 1 ((6 : ℕ) : ℤ), F k ∈ root k)
    (hfix : θ ((intList 1 ((6 : ℕ) : ℤ)).map F).prod = ((intList 1 ((6 : ℕ) : ℤ)).map F).prod) :
    ∀ k ∈ intList 1 ((6 : ℕ) : ℤ), θ (F k) = F k := by
  have hmem : ∀ k ∈ intList 1 ((6 : ℕ) : ℤ), θ (F k) ∈ root k := by
    intro k hk
    have := mem_intList_iff.1 hk
    exact hS.mem_root k (isRoot_of_pos_le this.1 this.2) _ (hF k hk)
  refine R.unique (fun k => θ (F k)) F hmem hF ?_
  rw [← hfix, map_list_prod, List.map_map]
  rfl

end FoldStab

theorem FoldData.toStab {R : RGD2 6 H r₁ r₂ U root} {θ : X ≃* X} (hf : FoldData R θ) :
    FoldStab R θ :=
  ⟨hf.mem_H, hf.mem_root, hf.r₁_mem, hf.r₂_mem⟩

theorem FoldStab.conj_of_mem_H {R : RGD2 6 H r₁ r₂ U root} {z : X} (hz : z ∈ H) :
    FoldStab R (MulAut.conj z) where
  mem_H h hh := by
    have : z * h * z⁻¹ ∈ H := H.mul_mem (H.mul_mem hz hh) (H.inv_mem hz)
    simpa [MulAut.conj_apply] using this
  mem_root k hk x hx := by
    have := R.invariant k hk z hz x hx
    simpa [MulAut.conj_apply] using this
  r₁_mem := by
    have : r₁⁻¹ * (z * r₁ * z⁻¹) ∈ H := by
      have e : r₁⁻¹ * (z * r₁ * z⁻¹) = (r₁⁻¹ * z * r₁) * z⁻¹ := by group
      rw [e]
      exact H.mul_mem (R.conj_H₁' hz) (H.inv_mem hz)
    simpa [MulAut.conj_apply] using this
  r₂_mem := by
    have : r₂⁻¹ * (z * r₂ * z⁻¹) ∈ H := by
      have e : r₂⁻¹ * (z * r₂ * z⁻¹) = (r₂⁻¹ * z * r₂) * z⁻¹ := by group
      rw [e]
      exact H.mul_mem (R.conj_H₂' hz) (H.inv_mem hz)
    simpa [MulAut.conj_apply] using this

end CFSG.GH74.GLS.SP
