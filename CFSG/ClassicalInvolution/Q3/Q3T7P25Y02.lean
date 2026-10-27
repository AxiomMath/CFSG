module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25Y01
public import CFSG.ClassicalInvolution.Asc77.AscC5O8B
import CFSG.ClassicalInvolution.Asc77.AscC5O7Eng
public import CFSG.ClassicalInvolution.Q3.Q3T7P25W01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YH01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.C5O.Ctx

theorem refSwap [IsSimpleGroup G] (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    ∃ σ : G, (∃ h ∈ ExactLayer.exactLayer Ω a, h * z * h⁻¹ = σ) ∧ σ * z = z * σ ∧ σ ≠ z ∧
      conjSub σ K = K' ∧ (¬ ∃ y : G, y * z * y⁻¹ = σ * z) ∧
      ∀ m : G, m * z * m⁻¹ = σ → m * (a * z) ≠ (a * z) * m := by
  classical
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hz2 : z * z = 1 := C.hz2
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hD⟩ := C.om5
  set X := ExactLayer.exactLayer Ω a with hX
  set zb := T7H.toBar Ω a z hzY with hzbdef
  have hzbmk : zb = QuotientGroup.mk ⟨z, hzY⟩ := rfl
  obtain ⟨sb, hsb2, hsbK, xb, hxb⟩ := hM.zSwap _ _ _ _ _ _ _ hD
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hzb := hD.twin.hzA
  have hzb' := hD.twin.hzA'
  have hsz : sb * zb * sb⁻¹ = zb := by
    have h1 := hzb.conj sb
    rw [hsbK] at h1
    rcases hzb'.unique _ h1.mem h1.sq with h | h
    · exact absurd h h1.ne_one
    · exact h
  have hsne : sb ≠ zb := by
    intro h
    apply hD.twin.ne
    rw [← hsbK, h]
    exact (conjSub_eq_self_of_mem hzb.mem).symm
  set σ₀ : G := (x : G) * z * (x : G)⁻¹ with hσ₀
  have hσ₀X : σ₀ ∈ X := X.mul_mem (X.mul_mem x.2 hzY) (X.inv_mem x.2)
  have hσ₀mk : (QuotientGroup.mk ⟨σ₀, hσ₀X⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) = sb := by
    rw [← hxb, hzbmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hσ₀2 : σ₀ * σ₀ = 1 := by
    calc σ₀ * σ₀ = (x : G) * (z * z) * (x : G)⁻¹ := by rw [hσ₀]; group
      _ = 1 := by rw [hz2]; group
  have hzσ : z * σ₀ * z * σ₀ ∈ oddCoreIn X := by
    have hmem : z * σ₀ * z * σ₀ ∈ X := X.mul_mem (X.mul_mem (X.mul_mem hzY hσ₀X) hzY) hσ₀X
    refine (mk_eq_one_iff X ⟨_, hmem⟩).mp ?_
    have e : (⟨z * σ₀ * z * σ₀, hmem⟩ : ↥X) =
        ⟨z, hzY⟩ * ⟨σ₀, hσ₀X⟩ * ⟨z, hzY⟩ * ⟨σ₀, hσ₀X⟩ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hσ₀mk, ← hzbmk]
    have hsi : sb⁻¹ = sb := inv_eq_of_mul_eq_one_right hsb2
    calc zb * sb * zb * sb = zb * (sb * zb * sb⁻¹) := by rw [hsi]; group
      _ = 1 := by rw [hsz]; exact hzb.sq
  obtain ⟨o, ho, hoc⟩ := exists_conj_comm_of_odd (odd_card_oddCoreIn X) hz2 hσ₀2 hzσ
  have hoX : o ∈ X := oddCoreIn_le X ho
  set σ := o * σ₀ * o⁻¹ with hσ
  have hσX : σ ∈ X := X.mul_mem (X.mul_mem hoX hσ₀X) (X.inv_mem hoX)
  have hσmk : (QuotientGroup.mk ⟨σ, hσX⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) = sb := by
    have ho1 : (QuotientGroup.mk ⟨o, hoX⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) = 1 :=
      (mk_eq_one_iff X ⟨o, hoX⟩).mpr ho
    have e : (⟨σ, hσX⟩ : ↥X) = ⟨o, hoX⟩ * ⟨σ₀, hσ₀X⟩ * (⟨o, hoX⟩)⁻¹ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ho1, hσ₀mk]
    group
  have hσz : σ * z = z * σ := hoc
  have hσzc : σ * z * σ⁻¹ = z := by rw [hσz]; group
  have hσne : σ ≠ z := by
    intro h
    apply hsne
    rw [← hσmk, hzbmk]
    congr 1
    exact Subtype.ext h
  have hσK : conjSub σ K = K' := by
    rcases C25Y.conjSub_pair_of_central hs hσzc with ⟨e1, -⟩ | ⟨e1, -⟩
    · exfalso
      apply hD.twin.ne
      have h1 : T7H.exactImg Ω a (conjSub σ K) = conjSub sb (T7H.exactImg Ω a K) := by
        rw [← hσmk]
        exact C25Y.exactImg_conjSub_layer ⟨σ, hσX⟩
      rw [e1, hsbK] at h1
      exact h1
    · exact e1
  have hcomm : sb * zb = zb * sb := by
    calc sb * zb = (sb * zb * sb⁻¹) * sb := by group
      _ = zb * sb := by rw [hsz]
  have hsz2 : (sb * zb) * (sb * zb) = 1 := by
    calc (sb * zb) * (sb * zb) = sb * (zb * sb) * zb := by group
      _ = sb * (sb * zb) * zb := by rw [hcomm]
      _ = (sb * sb) * (zb * zb) := by group
      _ = 1 := by rw [hsb2, hzb.sq, one_mul]
  have hsz1 : sb * zb ≠ 1 := by
    intro h
    apply hsne
    calc sb = (sb * zb) * zb⁻¹ := by group
      _ = zb⁻¹ := by rw [h, one_mul]
      _ = zb := inv_eq_of_mul_eq_one_right hzb.sq
  have hnotz : ¬ ∃ y : G, y * z * y⁻¹ = σ * z := by
    rintro ⟨y, hy⟩
    have hσzX : σ * z ∈ X := X.mul_mem hσX hzY
    have hyX : y * z * y⁻¹ ∈ X := by rw [hy]; exact hσzX
    have hbC : y * z * y⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
      ExactLayer.exactLayer_le_centralizer Ω a hyX
    obtain ⟨J, hJ, e, heJ, he4, he2, hecomm⟩ :=
      hM.invFixFour _ _ _ _ _ _ _ hD _ hsz2 hsz1
    obtain ⟨D, hD1, i₀, hDi⟩ := hD.lie
    have hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
      intro i
      have hi : i = i₀ := Fin.ext (by have h1 := i.2; have h2 := i₀.2; omega)
      subst hi
      simp only [IsOrthTag] at hDi
      rcases hDi with ⟨-, ht, -⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
      · rw [ht]; exact ⟨by decide, by decide⟩
      all_goals omega
    have hfix : C25Y.layerAut X (ExactLayer.conjSub_exactLayer hΩ.conjInvariant hbC) e = e := by
      rw [layerAut_of_mem X hyX]
      have e1 : (QuotientGroup.mk ⟨y * z * y⁻¹, hyX⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) =
          sb * zb := by
        have e2 : (⟨y * z * y⁻¹, hyX⟩ : ↥X) = ⟨σ, hσX⟩ * ⟨z, hzY⟩ := Subtype.ext hy
        rw [e2, QuotientGroup.mk_mul, hσmk, ← hzbmk]
      rw [e1]
      calc sb * zb * e * (sb * zb)⁻¹ = e * (sb * zb) * (sb * zb)⁻¹ := by rw [hecomm]
        _ = e := by group
    obtain ⟨h, hhC, hh⟩ :=
      C25Y.c25_8_one C.hyp C.ha2 hzY hK₂ D hD1 hD4 hbC hJ heJ he4 he2 hfix
    have hhX : conjSub h X = X := ExactLayer.conjSub_exactLayer hΩ.conjInvariant hhC
    apply hM.uSwapNotZ _ _ _ _ _ _ _ hD sb hsbK ⟨QuotientGroup.mk x, hxb⟩ (C25Y.layerAut X hhX)
    rw [hzbmk, C25Y.layerAut_mk]
    have e2 : C25Y.conjOnSub X hhX ⟨z, hzY⟩ = ⟨σ, hσX⟩ * ⟨z, hzY⟩ := by
      apply Subtype.ext
      show h * z * h⁻¹ = σ * z
      rw [hh, hy]
    rw [e2, QuotientGroup.mk_mul, hσmk]
  refine ⟨σ, ⟨o * (x : G), X.mul_mem hoX x.2, by rw [hσ, hσ₀]; group⟩, hσz, hσne, hσK,
    hnotz, fun m hm hma => ?_⟩
  have hhX : o * (x : G) ∈ X := X.mul_mem hoX x.2
  have hha : (o * (x : G)) * a = a * (o * (x : G)) :=
    Subgroup.mem_centralizer_singleton_iff.mp (ExactLayer.exactLayer_le_centralizer Ω a hhX)
  have hzσ' : z * σ * z⁻¹ = σ := by rw [← hσz]; group
  exact C25Y.not_swap_in_both C.hyp hK₂.2 hK₂'.2 (Ne.symm hσne) hzσ' hnotz
    (by rw [hσ, hσ₀]; group) hha hm hma
end Ctx
end Asc77.C5O

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.C5O.Ctx

theorem bar_ne_of_swap [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {σ : G}
    (hσX : σ ∈ ExactLayer.exactLayer Ω a) (hσK : conjSub σ K = K') (hzY : z ∈ ExactLayer.exactLayer
        Ω a) :
    (QuotientGroup.mk ⟨σ, hσX⟩ : ↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω a))
      ≠ QuotientGroup.mk ⟨z, hzY⟩ := by
  intro h
  obtain ⟨hzY', hu₁Y, hu₂Y, -, -, hD⟩ := C.om5
  apply hD.twin.ne
  have h1 : T7H.exactImg Ω a (conjSub σ K) = conjSub (QuotientGroup.mk ⟨σ, hσX⟩)
      (T7H.exactImg Ω a K) := C25Y.exactImg_conjSub_layer ⟨σ, hσX⟩
  rw [hσK, h] at h1
  rw [h1]
  exact (conjSub_eq_self_of_mem hD.twin.hzA.mem).symm
theorem interchange [IsSimpleGroup G] (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {σ h : G} (hhX : h ∈ ExactLayer.exactLayer Ω a)
    (hh : h * z * h⁻¹ = σ) (hσz : σ * z = z * σ) (hσK : conjSub σ K = K') :
    ∃ m ∈ ExactLayer.exactLayer Ω a, m * z * m⁻¹ = σ ∧ m * σ * m⁻¹ = z := by
  classical
  obtain ⟨hzY, hu₁Y, hu₂Y, -, -, hD⟩ := C.om5
  set X := ExactLayer.exactLayer Ω a with hX
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

theorem not_conj_au [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) (g : G) :
    g * z * g⁻¹ ≠ a * (u₁ * u₂) := by
  obtain ⟨t', hT⟩ := T7T.exists_hyp25T C.hyp
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  exact CFSG.ClassicalInvolution.Asc77.C5O7Eng.not_conj_au_gen hs.hz C.hz1 C.hyp.hR.2.1 C.hyp.hu₁.1 C.hyp.hu₁.2.1 C.hyp.hu₂.1
    hT.hcomm hT.hqR C.haR
    (fun hu hord => C25X.sq_eq_of_orderOf_four hs.hz hu hord)
    (fun {y} hya {x} hx hx4 =>
      T7ER.not_commute_of_conj hs C.hyp.hW C.hyp.hE4 hs.stand.mem hs.hz hya hx hx4) g

theorem not_conj_az_swap [IsSimpleGroup G] (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {σ h : G} (hhX : h ∈ ExactLayer.exactLayer Ω a)
    (hh : h * z * h⁻¹ = σ) (hσz : σ * z = z * σ) (hσK : conjSub σ K = K') :
    ¬ ∃ g : G, g * z * g⁻¹ = (a * z) * σ := by
  classical
  rintro ⟨g, hg⟩
  obtain ⟨hzY, hu₁Y, hu₂Y, -, -, hD⟩ := C.om5
  obtain ⟨t', hT⟩ := T7T.exists_hyp25T C.hyp
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  set X := ExactLayer.exactLayer Ω a with hX
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
    Subgroup.mem_centralizer_singleton_iff.mp (ExactLayer.exactLayer_le_centralizer Ω a hyX)
  apply C.not_conj_au (y * g)
  calc y * g * z * (y * g)⁻¹ = y * (g * z * g⁻¹) * y⁻¹ := by group
    _ = y * a * (z * σ) * y⁻¹ := by rw [hg]; group
    _ = a * (y * (z * σ) * y⁻¹) := by rw [hya]; group
    _ = a * (u₁ * u₂) := by rw [hnu, hydef, hv₀]; group
end Ctx
end Asc77.C5O

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement MatrixGroups
variable {G : Type} [Group G]
variable [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.C5O.Ctx

theorem normalizes_of_perfect [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a)
    {L₀ : Subgroup G} (hLz : L₀ ≤ Subgroup.centralizer ({z} : Set G)) (hLp : ⁅L₀, L₀⁆ = L₀) :
    ∀ g ∈ L₀, conjSub g K = K ∧ conjSub g K' = K' := by
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hKK : K ≠ K' := hs.hne.symm
  have hcz : ∀ x ∈ Subgroup.centralizer ({z} : Set G), x * z * x⁻¹ = z := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff.mp hx]; group
  have hpair := fun x hx => C25Y.conjSub_pair_of_central hs (hcz x hx)
  have hmul : ∀ x ∈ Subgroup.centralizer ({z} : Set G), ∀ y ∈ Subgroup.centralizer ({z} : Set G),
      (conjSub (x * y) K = K ↔ (conjSub x K = K ↔ conjSub y K = K)) := by
    intro x hx y hy
    rw [conjSub_mul]
    rcases hpair x hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
      rcases hpair y hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · simp [hx1, hy1]
    · rw [hy1, hx2]; simp [hx1, hKK.symm]
    · rw [hy1, hx1]; simp [hKK.symm]
    · rw [hy1, hx2]; simp [hx1, hKK.symm]
  have hinv : ∀ x ∈ Subgroup.centralizer ({z} : Set G),
      (conjSub x⁻¹ K = K ↔ conjSub x K = K) := by
    intro x _
    constructor
    · intro h
      have := congrArg (conjSub x) h
      rwa [conjSub_conjSub_inv, eq_comm] at this
    · intro h
      have := congrArg (conjSub x⁻¹) h
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, eq_comm] at this
  have hK : ∀ g ∈ L₀, conjSub g K = K := by
    have hle : ⁅L₀, L₀⁆ ≤ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.commutator_le]
      intro g hg h hh
      have hgz := hLz hg
      have hhz := hLz hh
      have hgi := Subgroup.inv_mem _ hgz
      have hhi := Subgroup.inv_mem _ hhz
      refine mem_normalizer_of_conjSub_eq ?_
      rw [commutatorElement_def]
      have e1 := hmul _ (mul_mem (mul_mem hgz hhz) hgi) _ hhi
      have e2 := hmul _ (mul_mem hgz hhz) _ hgi
      have e3 := hmul _ hgz _ hhz
      have e4 := hinv _ hgz
      have e5 := hinv _ hhz
      tauto
    intro g hg
    rw [← hLp] at hg
    exact conjSub_eq_of_mem_normalizer (hle hg)
  intro g hg
  refine ⟨hK g hg, ?_⟩
  rcases hpair g (hLz hg) with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd ((hK g hg).symm.trans h1) hKK

theorem A_comm (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {b b' : G}
    (hb : b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hb' : b' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) :
    b * b' = b' * b := by
  have haz := C.comm
  have hgen : ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      x * a = a * x ∧ x * z = z * x := by
    intro x hx
    rcases C.hA0 x hx with h | h | h | h <;> rw [h]
    · simp
    · exact ⟨rfl, haz⟩
    · exact ⟨haz.symm, rfl⟩
    · constructor
      · calc a * z * a = a * (z * a) := by group
          _ = a * (a * z) := by rw [haz]
      · calc a * z * z = a * z * z := rfl
          _ = z * (a * z) := by rw [mul_assoc, ← mul_assoc z, ← haz]; group
  obtain ⟨h1, h2⟩ := hgen b hb
  rcases C.hA0 b' hb' with h | h | h | h <;> rw [h]
  · simp
  · exact h1
  · exact h2
  · calc b * (a * z) = (b * a) * z := by group
      _ = a * (b * z) := by rw [h1]; group
      _ = a * z * b := by rw [h2]; group

theorem comm_mem_oddCore_cOne [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a)
    {x y : G} (hx : x ∈ cOne z K K') (hy : y ∈ cOne z K K') :
    ⁅x, y⁆ ∈ oddCoreIn (cOne z K K') := by
  obtain ⟨o, ho, b, hb, rfl⟩ := C.cOne_eq_mul x hx
  obtain ⟨o', ho', b', hb', rfl⟩ := C.cOne_eq_mul y hy
  have hbC : b ∈ cOne z K K' := C.A_le_cOne hb
  have hb'C : b' ∈ cOne z K K' := C.A_le_cOne hb'
  have hbb := C.A_comm hb hb'
  have hn₁ : b * o' * b⁻¹ ∈ oddCoreIn (cOne z K K') := conj_mem_oddCoreIn hbC ho'
  have hn₂ : b' * o * b'⁻¹ ∈ oddCoreIn (cOne z K K') := conj_mem_oddCoreIn hb'C ho
  have e : ⁅o * b, o' * b'⁆ = (o * (b * o' * b⁻¹)) * (o' * (b' * o * b'⁻¹))⁻¹ := by
    calc ⁅o * b, o' * b'⁆ = (o * (b * o' * b⁻¹)) * (b * b') *
          ((o' * (b' * o * b'⁻¹)) * (b' * b))⁻¹ := by
          rw [commutatorElement_def]; group
      _ = (o * (b * o' * b⁻¹)) * (o' * (b' * o * b'⁻¹))⁻¹ := by rw [hbb]; group
  rw [e]
  exact mul_mem (mul_mem ho hn₁) (inv_mem (mul_mem ho' hn₂))

theorem card_le_of_perfect [IsSimpleGroup G]
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a)
    {L₀ : Subgroup G} (hLz : L₀ ≤ Subgroup.centralizer ({z} : Set G)) (hLp : ⁅L₀, L₀⁆ = L₀)
    {Q : Type} [Group Q] [IsSimpleGroup Q] (hQ : ∃ x y : Q, x * y ≠ y * x)
    (φ : ↥L₀ →* Q) (hφ : Function.Surjective φ) :
    4 * Nat.card Q ≤ Nat.card (SL(2, GaloisField 3 1)) ^ 2 := by
  classical
  have : Finite Q := Finite.of_surjective φ hφ
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hnorm := C.normalizes_of_perfect hLz hLp
  obtain ⟨zK, hzK⟩ := hΩ.classical K hs.stand.mem
  obtain ⟨zK', hzK'⟩ := hΩ.classical K' hs.hK'.1
  obtain ⟨e⟩ := hzK.witness.2
  obtain ⟨e'⟩ := hzK'.witness.2
  set ρ := quotAutHom K L₀ (fun g hg => (hnorm g hg).1) e with hρ
  set ρ' := quotAutHom K' L₀ (fun g hg => (hnorm g hg).2) e' with hρ'
  
  have hperf : commutator ↥L₀ = ⊤ := by
    apply Subgroup.map_injective L₀.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hLp]
  
  have hsmall : ∀ σ : ↥L₀ →* MulAut (SL(2, GaloisField 3 1)),
      2 * Nat.card σ.range ≤ Nat.card (SL(2, GaloisField 3 1)) := by
    intro σ
    refine Q3T7P25.sl2PerfectAut3 σ.range ?_
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]
  
  set N := ρ.ker ⊓ ρ'.ker with hN
  have hNC : ∀ g ∈ N, (g : G) ∈ cOne z K K' := by
    intro g hg
    exact ⟨⟨hLz g.2, (quotAutHom_eq_one_iff g).mp hg.1⟩, (quotAutHom_eq_one_iff g).mp hg.2⟩
  set O₁ := (oddCoreIn (cOne z K K')).comap L₀.subtype with hO₁
  have hcommN : ⁅N, N⁆ ≤ O₁ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    show ((⁅x, y⁆ : ↥L₀) : G) ∈ oddCoreIn (cOne z K K')
    rw [show ((⁅x, y⁆ : ↥L₀) : G) = ⁅(x : G), (y : G)⁆ from rfl]
    exact C.comm_mem_oddCore_cOne (hNC x hx) (hNC y hy)
  have hO₁odd : Odd (Nat.card O₁) := by
    have h1 : Nat.card (O₁.map L₀.subtype) = Nat.card O₁ :=
      Subgroup.card_map_of_injective L₀.subtype_injective
    have h2 : O₁.map L₀.subtype ≤ oddCoreIn (cOne z K K') := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [← h1]
    exact Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.card_dvd_of_le h2)
  have hNn : (N.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map φ) with hbot | htop
  ·
    have hNk : N ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    have hQcard : Nat.card Q = φ.ker.index := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
    have h1 : φ.ker.index ≤ N.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hNk)
    have h2 : N.index ≤ ρ.ker.index * ρ'.ker.index := Subgroup.index_inf_le
    rw [Subgroup.index_ker, Subgroup.index_ker] at h2
    have h3 := hsmall ρ
    have h4 := hsmall ρ'
    calc 4 * Nat.card Q ≤ 4 * (Nat.card ρ.range * Nat.card ρ'.range) := by
          rw [hQcard]; exact Nat.mul_le_mul_left _ (h1.trans h2)
      _ = (2 * Nat.card ρ.range) * (2 * Nat.card ρ'.range) := by ring
      _ ≤ Nat.card (SL(2, GaloisField 3 1)) * Nat.card (SL(2, GaloisField 3 1)) :=
          Nat.mul_le_mul h3 h4
      _ = Nat.card (SL(2, GaloisField 3 1)) ^ 2 := by ring
  ·
    exfalso
    have hQperf : commutator Q = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
      · exfalso
        obtain ⟨x, y, hxy⟩ := hQ
        apply hxy
        have hc : ⁅x, y⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator
          (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc
      · exact h
    have hO₁top : O₁.map φ = ⊤ := by
      apply eq_top_iff.mpr
      rw [← hQperf, commutator_def, ← htop, ← Subgroup.map_commutator]
      exact Subgroup.map_mono hcommN
    have hQodd : Odd (Nat.card Q) := by
      have h1 : Nat.card (O₁.map φ) ∣ Nat.card O₁ := Subgroup.card_map_dvd _ _
      rw [hO₁top, Subgroup.card_top] at h1
      exact Odd.of_dvd_nat hO₁odd h1
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd
    obtain ⟨x, y, hxy⟩ := hQ
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv x y)

theorem not_hasBigFix [IsSimpleGroup G]
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {b c : G} (hb2 : b * b = 1)
    (hbX : conjSub b (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a) (hcb : c * z * c⁻¹ =
        b) :
    ¬ HasBigFix (C25Y.layerAut (ExactLayer.exactLayer Ω a) hbX) := by
  classical
  rintro ⟨L, hLfix, hLs, hLnc, hLcard⟩
  set H₁ : Subgroup ↥(ExactLayer.exactLayer Ω a) :=
    L.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a))) ⊓
    (Subgroup.centralizer ({b} : Set G)).comap (ExactLayer.exactLayer Ω a).subtype with hH₁
  have hH₁map : H₁.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
      a))) = L := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
    · intro l hl
      obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective l
      have hfix := hLfix _ hl
      rw [layerAut_mk_eq_iff] at hfix
      have hy : (y₀ : G)⁻¹ * b * (y₀ : G) * b ∈ oddCoreIn (ExactLayer.exactLayer Ω a) := by
        have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
        have h1 := conj_mem_oddCoreIn ((ExactLayer.exactLayer Ω a).inv_mem y₀.2) hfix
        have e : (y₀ : G)⁻¹ * ⁅b, (y₀ : G)⁆ * (y₀ : G)⁻¹⁻¹ = (y₀ : G)⁻¹ * b * (y₀ : G) * b := by
          rw [commutatorElement_def, hbi]; group
        rwa [e] at h1
      obtain ⟨o, ho, hoc⟩ := exists_mul_comm_of_odd (odd_card_oddCoreIn (ExactLayer.exactLayer Ω
          a)) hb2 hy
      have hoX : o ∈ ExactLayer.exactLayer Ω a := oddCoreIn_le (ExactLayer.exactLayer Ω a) ho
      refine ⟨y₀ * ⟨o, hoX⟩, ⟨?_, ?_⟩, ?_⟩
      · show QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a)) (y₀ * ⟨o,
          hoX⟩) ∈ L
        rw [map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          (mk_eq_one_iff (ExactLayer.exactLayer Ω a) ⟨o, hoX⟩).mpr ho, mul_one]
        exact hl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hoc
      · rw [map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          (mk_eq_one_iff (ExactLayer.exactLayer Ω a) ⟨o, hoX⟩).mpr ho, mul_one]
  have hLperf : ⁅L, L⁆ = L := by
    have hc : commutator ↥L = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
      · exfalso
        obtain ⟨x, y, hxy⟩ := hLnc
        apply hxy
        have hc : ⁅x, y⁆ ∈ commutator ↥L :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc
      · exact h
    have := congrArg (Subgroup.map L.subtype) hc
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at this
  have hex : ∃ n : ℕ, ∃ H₀ : Subgroup ↥(ExactLayer.exactLayer Ω a), H₀ ≤ H₁ ∧
      H₀.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a))) = L ∧
      Nat.card H₀ = n := ⟨_, H₁, le_rfl, hH₁map, rfl⟩
  obtain ⟨H₀, hH₀le, hH₀map, hH₀card⟩ := Nat.find_spec hex
  have hH₀perf : ⁅H₀, H₀⁆ = H₀ := by
    have hle : ⁅H₀, H₀⁆ ≤ H₀ := Subgroup.commutator_le_self _
    have hmap :
        (⁅H₀, H₀⁆).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
            a))) = L := by
      rw [Subgroup.map_commutator, hH₀map, hLperf]
    have hmin := Nat.find_min' hex ⟨⁅H₀, H₀⁆, hle.trans hH₀le, hmap, rfl⟩
    rw [← hH₀card] at hmin
    exact Subgroup.eq_of_le_of_card_ge hle hmin
  have hH₀L : ∀ y ∈ H₀,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a)) y ∈ L :=
    fun y hy => (hH₀le hy).1
  set L₀ : Subgroup G := (H₀.map (ExactLayer.exactLayer Ω a).subtype).map (MulAut.conj
      c⁻¹).toMonoidHom
    with hL₀
  have hL₀z : L₀ ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyb : (y : G) * b = b * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hH₀le hy).2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hz : z = c⁻¹ * b * c := by rw [← hcb]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]
    rw [hz]
    calc c⁻¹ * (y : G) * c * (c⁻¹ * b * c) = c⁻¹ * ((y : G) * b) * c := by group
      _ = c⁻¹ * (b * (y : G)) * c := by rw [hyb]
      _ = c⁻¹ * b * c * (c⁻¹ * (y : G) * c) := by group
  have hL₀p : ⁅L₀, L₀⁆ = L₀ := by
    rw [hL₀, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hH₀perf]
  let ψ : ↥H₀ →* ↥L :=
    ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a))).comp
        H₀.subtype).codRestrict
      L (fun y => hH₀L y y.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨l, hl⟩
    rw [← hH₀map] at hl
    obtain ⟨y, hy, rfl⟩ := hl
    exact ⟨⟨y, hy⟩, rfl⟩
  let e₁ := Subgroup.equivMapOfInjective H₀ (ExactLayer.exactLayer Ω a).subtype
    (ExactLayer.exactLayer Ω a).subtype_injective
  let e₂ := Subgroup.equivMapOfInjective (H₀.map (ExactLayer.exactLayer Ω a).subtype)
    (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective
  let φ : ↥L₀ →* ↥L := ψ.comp (e₁.trans e₂).symm.toMonoidHom
  have hφ : Function.Surjective φ := hψ.comp (e₁.trans e₂).symm.surjective
  have h4 := C.card_le_of_perfect hL₀z hL₀p hLnc φ hφ
  omega
end Ctx
end Asc77.C5O

end

end CFSG.ClassicalInvolution.Q3.Q3T8
