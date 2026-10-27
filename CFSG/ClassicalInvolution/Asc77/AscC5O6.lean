module

public import CFSG.ClassicalInvolution.Asc77.AscC25Y5
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

theorem refSwap [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    ∃ σ : G, (∃ h ∈ exactLayer Ω a, h * z * h⁻¹ = σ) ∧ σ * z = z * σ ∧ σ ≠ z ∧
      conjSub σ K = K' ∧ (¬ ∃ y : G, y * z * y⁻¹ = σ * z) ∧
      ∀ m : G, m * z * m⁻¹ = σ → m * (a * z) ≠ (a * z) * m := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz2 : z * z = 1 := C.hz2
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hD⟩ := C.om5
  set X := exactLayer Ω a with hX
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
      exactLayer_le_centralizer Ω a hyX
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
    have hfix : C25Y.layerAut X (conjSub_exactLayer hΩ.conjInvariant hbC) e = e := by
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
    have hhX : conjSub h X = X := conjSub_exactLayer hΩ.conjInvariant hhC
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
    Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω a hhX)
  have hzσ' : z * σ * z⁻¹ = σ := by rw [← hσz]; group
  exact C25Y.not_swap_in_both C.hyp hK₂.2 hK₂'.2 (Ne.symm hσne) hzσ' hnotz
    (by rw [hσ, hσ₀]; group) hha hm hma

end Ctx

end CFSG.ClassicalInvolution.Asc77.C5O
