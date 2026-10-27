module

import CFSG.ClassicalInvolution.Asc77.AscC5O7Eng
public import CFSG.ClassicalInvolution.Asc77.AscC5O1
public import CFSG.ClassicalInvolution.Asc77.AscC5O1G

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Ctx

theorem bar_ne_of_swap [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {σ : G}
    (hσX : σ ∈ exactLayer Ω a) (hσK : conjSub σ K = K') (hzY : z ∈ exactLayer Ω a) :
    (QuotientGroup.mk ⟨σ, hσX⟩ : ↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))
      ≠ QuotientGroup.mk ⟨z, hzY⟩ := by
  intro h
  obtain ⟨hzY', hu₁Y, hu₂Y, -, -, hD⟩ := C.om5
  apply hD.twin.ne
  have h1 : T7H.exactImg Ω a (conjSub σ K) = conjSub (QuotientGroup.mk ⟨σ, hσX⟩)
      (T7H.exactImg Ω a K) := C25Y.exactImg_conjSub_layer ⟨σ, hσX⟩
  rw [hσK, h] at h1
  rw [h1]
  exact (conjSub_eq_self_of_mem hD.twin.hzA.mem).symm

theorem interchange [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {σ h : G} (hhX : h ∈ exactLayer Ω a)
    (hh : h * z * h⁻¹ = σ) (hσz : σ * z = z * σ) (hσK : conjSub σ K = K') :
    ∃ m ∈ exactLayer Ω a, m * z * m⁻¹ = σ ∧ m * σ * m⁻¹ = z := by
  classical
  obtain ⟨hzY, hu₁Y, hu₂Y, -, -, hD⟩ := C.om5
  set X := exactLayer Ω a with hX
  have hz2 := C.hz2
  have hσX : σ ∈ X := by rw [← hh]; exact X.mul_mem (X.mul_mem hhX hzY) (X.inv_mem hhX)
  have hσ2 : σ * σ = 1 := by
    rw [← hh]
    calc h * z * h⁻¹ * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  set zb := T7H.toBar Ω a z hzY with hzbdef
  have hzbmk : zb = QuotientGroup.mk ⟨z, hzY⟩ := rfl
  set sb : ↥X ⧸ classicalInvolutionOddCore ↥X := QuotientGroup.mk ⟨σ, hσX⟩ with hsb
  have hsbne : sb ≠ zb := C.bar_ne_of_swap hσX hσK hzY
  have hsbeq : sb = MulAut.conj (QuotientGroup.mk ⟨h, hhX⟩ :
      ↥X ⧸ classicalInvolutionOddCore ↥X) zb := by
    rw [MulAut.conj_apply, hzbmk, hsb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hh.symm
  have hsbz : sb * zb = zb * sb := by
    rw [hsb, hzbmk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hσz
  have hsb2 : sb * sb = 1 := by
    rw [hsb, ← QuotientGroup.mk_mul]
    have e : (⟨σ, hσX⟩ : ↥X) * ⟨σ, hσX⟩ = 1 := Subtype.ext hσ2
    rw [e, QuotientGroup.mk_one]
  obtain ⟨⟨xb, hx1, hx2⟩, -⟩ := hM.interchange _ _ _ _ _ _ _ hD
    (MulAut.conj (QuotientGroup.mk ⟨h, hhX⟩)) sb hsbeq hsbne hsbz
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xb
  have hx₀X : (x₀ : G) ∈ X := x₀.2
  set w₀ : G := (x₀ : G) * z * (x₀ : G)⁻¹ with hw₀
  have hw₀X : w₀ ∈ X := X.mul_mem (X.mul_mem hx₀X hzY) (X.inv_mem hx₀X)
  have hw₀2 : w₀ * w₀ = 1 := by
    calc w₀ * w₀ = (x₀ : G) * (z * z) * (x₀ : G)⁻¹ := by rw [hw₀]; group
      _ = 1 := by rw [hz2]; group
  have hprod : w₀ * σ ∈ oddCoreIn X := by
    have hmem : w₀ * σ ∈ X := X.mul_mem hw₀X hσX
    refine (mk_eq_one_iff X ⟨_, hmem⟩).mp ?_
    have e : (⟨w₀ * σ, hmem⟩ : ↥X) = x₀ * ⟨z, hzY⟩ * x₀⁻¹ * ⟨σ, hσX⟩ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      ← hzbmk, hx1]
    exact hsb2
  obtain ⟨n, hn, hnσ⟩ := C25Y.exists_conj_of_involutions_odd (odd_card_oddCoreIn X) hw₀2 hσ2 hprod
  have hnX : n ∈ X := oddCoreIn_le X hn
  set x₁ : G := n * (x₀ : G) with hx₁
  have hx₁X : x₁ ∈ X := X.mul_mem hnX hx₀X
  have hx₁z : x₁ * z * x₁⁻¹ = σ := by rw [hnσ, hx₁, hw₀]; group
  set w : G := x₁ * σ * x₁⁻¹ with hw
  have hw2 : w * w = 1 := by
    calc w * w = x₁ * (σ * σ) * x₁⁻¹ := by rw [hw]; group
      _ = 1 := by rw [hσ2]; group
  have hwX : w ∈ X := X.mul_mem (X.mul_mem hx₁X hσX) (X.inv_mem hx₁X)
  have hzw : z * w ∈ oddCoreIn X ⊓ Subgroup.centralizer ({σ} : Set G) := by
    refine ⟨?_, ?_⟩
    · have hmem : z * w ∈ X := X.mul_mem hzY hwX
      refine (mk_eq_one_iff X ⟨_, hmem⟩).mp ?_
      have hn1 : (QuotientGroup.mk ⟨n, hnX⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) = 1 :=
        (mk_eq_one_iff X ⟨n, hnX⟩).mpr hn
      have e : (⟨z * w, hmem⟩ : ↥X) = ⟨z, hzY⟩ * (⟨n, hnX⟩ * x₀ * ⟨σ, hσX⟩ *
          (⟨n, hnX⟩ * x₀)⁻¹) := rfl
      have himg : (QuotientGroup.mk ⟨z * w, hmem⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) =
          zb * ((QuotientGroup.mk x₀ : ↥X ⧸ classicalInvolutionOddCore ↥X) * sb *
            (QuotientGroup.mk x₀)⁻¹) := by
        rw [e]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hn1, one_mul]
        rfl
      rw [himg, hx2]
      exact hD.twin.hzA.sq
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hwσ : w * σ = σ * w := by
        calc w * σ = x₁ * (σ * z) * x₁⁻¹ := by rw [hw, ← hx₁z]; group
          _ = x₁ * (z * σ) * x₁⁻¹ := by rw [hσz]
          _ = σ * w := by rw [hw, ← hx₁z]; group
      calc z * w * σ = z * (w * σ) := by group
        _ = z * (σ * w) := by rw [hwσ]
        _ = (z * σ) * w := by group
        _ = (σ * z) * w := by rw [hσz]
        _ = σ * (z * w) := by group
  have hNodd : Odd (Nat.card ↥(oddCoreIn X ⊓ Subgroup.centralizer ({σ} : Set G))) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn X) (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨c, hc, hcw⟩ := C25Y.exists_conj_of_involutions_odd hNodd hz2 hw2 hzw
  have hcX : c ∈ X := oddCoreIn_le X hc.1
  have hcσ : c * σ = σ * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  refine ⟨c⁻¹ * x₁, X.mul_mem (X.inv_mem hcX) hx₁X, ?_, ?_⟩
  · calc c⁻¹ * x₁ * z * (c⁻¹ * x₁)⁻¹ = c⁻¹ * (x₁ * z * x₁⁻¹) * c := by group
      _ = c⁻¹ * (σ * c) := by rw [hx₁z]; group
      _ = c⁻¹ * (c * σ) := by rw [hcσ]
      _ = σ := by group
  · calc c⁻¹ * x₁ * σ * (c⁻¹ * x₁)⁻¹ = c⁻¹ * w * c := by rw [hw]; group
      _ = z := by rw [hcw]; group

theorem not_conj_au [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) (g : G) :
    g * z * g⁻¹ ≠ a * (u₁ * u₂) := by
  obtain ⟨t', hT⟩ := T7T.exists_hyp25T C.hyp
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  exact CFSG.ClassicalInvolution.Asc77.C5O7Eng.not_conj_au_gen hs.hz C.hz1 C.hyp.hR.2.1 C.hyp.hu₁.1 C.hyp.hu₁.2.1 C.hyp.hu₂.1
    hT.hcomm hT.hqR C.haR
    (fun hu hord => C25X.sq_eq_of_orderOf_four hs.hz hu hord)
    (fun {y} hya {x} hx hx4 =>
      T7ER.not_commute_of_conj hs C.hyp.hW C.hyp.hE4 hs.stand.mem hs.hz hya hx hx4) g

theorem not_conj_az_swap [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {σ h : G} (hhX : h ∈ exactLayer Ω a)
    (hh : h * z * h⁻¹ = σ) (hσz : σ * z = z * σ) (hσK : conjSub σ K = K') :
    ¬ ∃ g : G, g * z * g⁻¹ = (a * z) * σ := by
  classical
  rintro ⟨g, hg⟩
  obtain ⟨hzY, hu₁Y, hu₂Y, -, -, hD⟩ := C.om5
  obtain ⟨t', hT⟩ := T7T.exists_hyp25T C.hyp
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  set X := exactLayer Ω a with hX
  have hz2 := C.hz2
  have hσX : σ ∈ X := by rw [← hh]; exact X.mul_mem (X.mul_mem hhX hzY) (X.inv_mem hhX)
  set zb := T7H.toBar Ω a z hzY with hzbdef
  have hzbmk : zb = QuotientGroup.mk ⟨z, hzY⟩ := rfl
  set sb : ↥X ⧸ classicalInvolutionOddCore ↥X := QuotientGroup.mk ⟨σ, hσX⟩ with hsb
  have hsbne : sb ≠ zb := C.bar_ne_of_swap hσX hσK hzY
  have hsbeq : sb = MulAut.conj (QuotientGroup.mk ⟨h, hhX⟩ :
      ↥X ⧸ classicalInvolutionOddCore ↥X) zb := by
    rw [MulAut.conj_apply, hzbmk, hsb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hh.symm
  have hsbz : sb * zb = zb * sb := by
    rw [hsb, hzbmk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hσz
  obtain ⟨-, ⟨yb, hy⟩⟩ := hM.interchange _ _ _ _ _ _ _ hD
    (MulAut.conj (QuotientGroup.mk ⟨h, hhX⟩)) sb hsbeq hsbne hsbz
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective yb
  have hu₁K : u₁ ∈ K := C.hyp.hR.2.1 C.hyp.hu₁.1
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hu₁sq : u₁ * u₁ = z := C25X.sq_eq_of_orderOf_four hs.hz hu₁K C.hyp.hu₁.2.1
  have hu₂sq : u₂ * u₂ = z :=
    C25X.sq_eq_of_orderOf_four hz' (C.hyp.hR'.2.1 C.hyp.hu₂.1) C.hyp.hu₂.2.1
  have hu12 : u₁ * u₂ = u₂ * u₁ := hT.hcomm u₁ C.hyp.hu₁.1 u₂ C.hyp.hu₂.1
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [hu12]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [hu₁sq, hu₂sq, hz2]
  have huX : u₁ * u₂ ∈ X := X.mul_mem hu₁Y hu₂Y
  have hy₀X : (y₀ : G) ∈ X := y₀.2
  set v₀ : G := (y₀ : G) * (z * σ) * (y₀ : G)⁻¹ with hv₀
  have hzσ2 : (z * σ) * (z * σ) = 1 := by
    have hσ2 : σ * σ = 1 := by
      rw [← hh]
      calc h * z * h⁻¹ * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    calc (z * σ) * (z * σ) = z * (σ * z) * σ := by group
      _ = z * (z * σ) * σ := by rw [hσz]
      _ = (z * z) * (σ * σ) := by group
      _ = 1 := by rw [hz2, hσ2, one_mul]
  have hv₀2 : v₀ * v₀ = 1 := by
    calc v₀ * v₀ = (y₀ : G) * ((z * σ) * (z * σ)) * (y₀ : G)⁻¹ := by rw [hv₀]; group
      _ = 1 := by rw [hzσ2]; group
  have hprod : v₀ * (u₁ * u₂) ∈ oddCoreIn X := by
    have hmem : v₀ * (u₁ * u₂) ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem hy₀X (X.mul_mem hzY hσX)) (X.inv_mem hy₀X)) huX
    refine (mk_eq_one_iff X ⟨_, hmem⟩).mp ?_
    have e : (⟨v₀ * (u₁ * u₂), hmem⟩ : ↥X) =
        y₀ * (⟨z, hzY⟩ * ⟨σ, hσX⟩) * y₀⁻¹ * (⟨u₁, hu₁Y⟩ * ⟨u₂, hu₂Y⟩) := rfl
    have himg : (QuotientGroup.mk ⟨v₀ * (u₁ * u₂), hmem⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) =
        ((QuotientGroup.mk y₀ : ↥X ⧸ classicalInvolutionOddCore ↥X) * (zb * sb) *
          (QuotientGroup.mk y₀)⁻¹) * (T7H.toBar Ω a u₁ hu₁Y * T7H.toBar Ω a u₂ hu₂Y) := by
      rw [e]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rfl
    rw [himg, hy]
    have hb : T7H.toBar Ω a u₁ hu₁Y * T7H.toBar Ω a u₂ hu₂Y =
        QuotientGroup.mk ⟨u₁ * u₂, huX⟩ := rfl
    rw [hb, ← QuotientGroup.mk_mul]
    have e2 : (⟨u₁ * u₂, huX⟩ : ↥X) * ⟨u₁ * u₂, huX⟩ = 1 := Subtype.ext hu2
    rw [e2, QuotientGroup.mk_one]
  obtain ⟨n, hn, hnu⟩ := C25Y.exists_conj_of_involutions_odd (odd_card_oddCoreIn X) hv₀2 hu2 hprod
  have hnX : n ∈ X := oddCoreIn_le X hn
  set y : G := n * (y₀ : G) with hydef
  have hyX : y ∈ X := X.mul_mem hnX hy₀X
  have hya : y * a = a * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω a hyX)
  apply C.not_conj_au (y * g)
  calc y * g * z * (y * g)⁻¹ = y * (g * z * g⁻¹) * y⁻¹ := by group
    _ = y * a * (z * σ) * y⁻¹ := by rw [hg]; group
    _ = a * (y * (z * σ) * y⁻¹) := by rw [hya]; group
    _ = a * (u₁ * u₂) := by rw [hnu, hydef, hv₀]; group

end Ctx

end CFSG.ClassicalInvolution.Asc77.C5O
