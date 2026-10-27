module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionB

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

section Hpart

variable {H H₁ H₂ M₁ Pb W₁ Mf M : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem mem_H_iff_zOf [Finite G] (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (x : G) :
    x ∈ H ↔ zOf e * x = x * zOf e := by
  have hinf : H₁ ⊓ H₂ = Subgroup.zpowers (zOf e) := by
    have h := Subgroup.eq_of_le_of_card_ge
      (show Subgroup.zpowers (zOf e) ≤ H₁ ⊓ H₂ from
        Subgroup.zpowers_le.mpr (zOf_mem_inf hlet))
      (by
        rw [hone.card_inf, Nat.card_zpowers, orderOf_zOf hone hlet])
    exact h.symm
  have hH : H = Subgroup.centralizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) := hone.eq_centralizer
  rw [hH, hinf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact h (zOf e) (Subgroup.mem_zpowers _)
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute (zOf e) x from h) k).eq

theorem orderOf_e4 (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    orderOf (e 4) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    exact e4_sq hlet
  · intro h
    apply e4_not_mem_K hone hlet
    rw [h]
    exact Subgroup.one_mem _

theorem orderOf_e4z (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    orderOf (e 4 * zOf e) = 2 := by
  have hcomm : e 4 * zOf e = zOf e * e 4 := zOf_central hone hlet (e 4) (e4_mem_H hlet)
  apply orderOf_eq_prime
  · rw [pow_two]
    calc e 4 * zOf e * (e 4 * zOf e) = e 4 * (zOf e * e 4) * zOf e := by group
      _ = e 4 * (e 4 * zOf e) * zOf e := by rw [← hcomm]
      _ = (e 4 * e 4) * (zOf e * zOf e) := by group
      _ = 1 := by rw [e4_sq hlet, zOf_mul_self hone hlet, mul_one]
  · intro h
    apply e4_not_mem_K hone hlet
    have h' : e 4 = (zOf e)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact h
    rw [h', zOf_inv_eq hone hlet]
    exact Subgroup.mem_sup_left (zOf_mem_inf hlet).1

theorem conj_zOf_of_orderOf (hO : OneClass e) (t : G) (ht : orderOf t = 2) :
    ∃ c : G, c * zOf e * c⁻¹ = t :=
  isConj_iff.mp (hO t ht)

theorem conj_inv_mem_H [Finite G] (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (c : G) (hc : c * zOf e * c⁻¹ = t') (B : Subgroup G) (hB : ∀ y ∈ B, t' * y = y * t')
    (y : G) (hy : y ∈ B) : c⁻¹ * y * c ∈ H := by
  rw [mem_H_iff_zOf hone hlet]
  have hty := hB y hy
  rw [← hc] at hty
  have key : c * zOf e * c⁻¹ * y = y * (c * zOf e * c⁻¹) := hty
  calc zOf e * (c⁻¹ * y * c) = c⁻¹ * (c * zOf e * c⁻¹ * y) * c := by group
    _ = c⁻¹ * (y * (c * zOf e * c⁻¹)) * c := by rw [key]
    _ = (c⁻¹ * y * c) * zOf e := by group

theorem card_centralizer_Psub [Finite G] (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hL : PbarCore e Pb) (hPb : Nat.card Pb = 27) :
    Nat.card ↥(Subgroup.centralizer (Psub e : Set G)) = 54 := by
  rw [card_of_centComplement hL.compl, hPb, Nat.card_zpowers, orderOf_zOf hone hlet]

theorem exists_conj_Psub_le [Finite G] (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) (c : G) (hc : c * zOf e * c⁻¹ = t') (B : Subgroup G)
    (hB : ∀ y ∈ B, t' * y = y * t') (hBcard : Nat.card B = 9) :
    ∃ g : G, ∀ x ∈ Psub e, g * x * g⁻¹ ∈ B := by
  let T : Subgroup G := B.map (MulAut.conj c⁻¹).toMonoidHom
  have hTcard : Nat.card T = 9 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom)
      (MulEquiv.injective _), hBcard]
  have hTH : T ≤ H := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 := conj_inv_mem_H hone hlet c hc B hB y hy
    simpa [MulAut.conj_apply] using h1
  have hodd : Odd (Nat.card T) := by
    rw [hTcard]
    exact ⟨4, by norm_num⟩
  obtain ⟨-, hex⟩ := hF.odd_sub T hTH hodd
  obtain ⟨h, -, hmem⟩ := hex hTcard
  refine ⟨c * h, fun x hx => ?_⟩
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hmem x hx)
  have hyc : c⁻¹ * y * c = h * x * h⁻¹ := by
    simpa [MulAut.conj_apply] using hyeq
  have key : (c * h) * x * (c * h)⁻¹ = y := by
    calc c * h * x * (c * h)⁻¹ = c * (h * x * h⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * y * c) * c⁻¹ := by rw [hyc]
      _ = y := by group
  rw [key]
  exact hy

theorem card_le_centralizer_Psub [Finite G] {B K : Subgroup G} {g : G}
    (hg : ∀ x ∈ Psub e, g * x * g⁻¹ ∈ B) (hK : ∀ y ∈ K, ∀ b ∈ B, y * b = b * y) :
    Nat.card K ≤ Nat.card ↥(Subgroup.centralizer (Psub e : Set G)) := by
  let φ : K → ↥(Subgroup.centralizer (Psub e : Set G)) := fun y =>
    ⟨g⁻¹ * (y : G) * g, by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hb := hg p hp
      have hc := hK (y : G) y.2 _ hb
      calc p * (g⁻¹ * (y : G) * g) = g⁻¹ * ((g * p * g⁻¹) * (y : G)) * g := by group
        _ = g⁻¹ * ((y : G) * (g * p * g⁻¹)) * g := by rw [hc]
        _ = (g⁻¹ * (y : G) * g) * p := by group⟩
  have hinj : Function.Injective φ := by
    intro y1 y2 h
    have h' : g⁻¹ * (y1 : G) * g = g⁻¹ * (y2 : G) * g := congrArg Subtype.val h
    apply Subtype.ext
    have := congrArg (fun z => g * z * g⁻¹) h'
    simpa using this
  exact Nat.card_le_card_of_injective φ hinj

end Hpart

end CFSG.GH74.QTGen4.Recog.G23.P7
