module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6DN
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFQ8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Hx

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement

theorem conj_mem_ae6P {Y : Type} [Group Y] {Ω : Set (Subgroup Y)} (hinv : ConjInvariant Ω) {c h : Y}
    (hh : h * c * h⁻¹ = c) {x : Y} (hx : x ∈ ae6P Ω c) : h * x * h⁻¹ ∈ ae6P Ω c := by
  have hle : conjSub h (ae6P Ω c) ≤ ae6P Ω c := by
    unfold ae6P
    rw [conjSub_iSup₂]
    refine iSup₂_le fun J hJ => ?_
    have hJ' : conjSub h J ∈ ae6Vc Ω c := by
      refine ⟨hinv h J hJ.1, ?_⟩
      have := hJ.2.conj h
      rwa [hh] at this
    exact le_iSup₂_of_le (f := fun J (_ : J ∈ ae6Vc Ω c) => J) (conjSub h J) hJ' le_rfl
  exact hle (conj_mem_conjSub hx)

theorem le_ae6P {Y : Type} [Group Y] {Ω : Set (Subgroup Y)} {c : Y} {J : Subgroup Y} (hJ : J ∈ Ω)
    (hc : IsUniqueInvolution J c) : J ≤ ae6P Ω c :=
  le_iSup₂_of_le (f := fun J (_ : J ∈ ae6Vc Ω c) => J) J ⟨hJ, hc⟩ le_rfl

theorem normalizes_and_comm_of_commutator {Y : Type} [Group Y] {D : Subgroup Y} {x : Y}
    (hD : ∀ d ∈ D, d * d = 1) (hx : x * x = 1) (hDx : ⁅D, Subgroup.zpowers x⁆ ≤ D) :
    (∀ d ∈ D, x * d * x⁻¹ ∈ D) ∧ ∀ c ∈ ⁅D, Subgroup.zpowers x⁆, x * c = c * x := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    have h1 := hD (a * b) (D.mul_mem ha hb)
    have h2 := hD a ha
    have h3 := hD b hb
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [h2, h3]; group
  have hnorm : ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro d hd
    have hc : ⁅d⁻¹, x⁆ ∈ ⁅D, Subgroup.zpowers x⁆ :=
      Subgroup.commutator_mem_commutator (D.inv_mem hd) (Subgroup.mem_zpowers x)
    have := D.mul_mem hd (hDx hc)
    rw [commutatorElement_def, inv_inv, hxinv] at this
    rw [hxinv]
    simpa [mul_assoc] using this
  refine ⟨hnorm, ?_⟩
  have hle : ⁅D, Subgroup.zpowers x⁆ ≤ Subgroup.centralizer ({x} : Set Y) := by
    rw [Subgroup.commutator_le]
    intro d hd g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hk : x ^ k = 1 ∨ x ^ k = x := by
      have hxo : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
      obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
      · left
        rw [hm, zpow_mul, hxo, one_zpow]
      · right
        rw [hm, zpow_add, zpow_mul, hxo, one_zpow, one_mul, zpow_one]
    rcases hk with hk | hk
    · rw [hk, commutatorElement_one_right, mul_one, one_mul]
    · rw [hk, commutatorElement_def, hxinv]
      have hd' : x * d * x ∈ D := by simpa [hxinv] using hnorm d hd
      have hsq' := hD _ (D.mul_mem hd' (D.inv_mem hd))
      have key : (x * d * x) * d⁻¹ = d * (x * d * x)⁻¹ := by
        have h4 : (x * d * x) * d⁻¹ = ((x * d * x) * d⁻¹)⁻¹ :=
          (inv_eq_of_mul_eq_one_right hsq').symm
        rw [h4]; group
      have hinv' : (x * d * x)⁻¹ = x * d⁻¹ * x := by
        rw [mul_inv_rev, mul_inv_rev, hxinv, ← mul_assoc]
      symm
      calc x * (d * x * d⁻¹ * x) = (x * d * x) * d⁻¹ * x := by group
        _ = d * (x * d * x)⁻¹ * x := by rw [key]
        _ = d * x * d⁻¹ * x * x := by rw [hinv']; group
  intro c hc
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Datum

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}

theorem twins_facts (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    IsUniqueInvolution K' t ∧ IsUniqueInvolution K₃ t ∧ IsUniqueInvolution K₄ t ∧
      (∀ g ∈ K, ∀ x ∈ K', g * x = x * g) ∧ (∀ g ∈ K, ∀ x ∈ K₃, g * x = x * g) ∧
      (∀ g ∈ K, ∀ x ∈ K₄, g * x = x * g) := by
  have hStd := H.ex.1
  have hF := H.ex.2.1
  have hd := hStd.datum
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S hStd.perp.core).hyp
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hz4 : IsUniqueInvolution K₄ t := Asc77.isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  refine ⟨hd.hzK', hd.hzK₃, hz4, ?_, ?_, ?_⟩
  · exact TC.Thin.twin_comm hΩ h2g hd.mem hd.hK'.1 hd.hne.symm hd.hz hd.hzK'
  · exact TC.Thin.twin_comm hΩ h2g hd.mem hd.hK₃.1 hd.hK₃K.symm hd.hz hd.hzK₃
  · exact TC.Thin.twin_comm hΩ h2g hd.mem hF.1.1 hF.2.1.symm hd.hz hz4

theorem tau_ne_t (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) : y * t * y⁻¹ ≠ t := by
  intro hτ
  have hStd := H.ex.1
  have hd := hStd.datum
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  obtain ⟨-, -, -, c2, c3, c4⟩ := twins_facts H
  obtain ⟨e⟩ := members_q8_of_isPGroup hStd.perp h2g K hd.mem
  have hq := WF.q8Facts_of_iso hd.hz e
  have hprod : a₁ * a₂ * a₃ * a₄ = t := by rw [← fr.hy, hτ]
  have hcent : ∀ g ∈ K, a₁ * g = g * a₁ := by
    intro g hg
    have ha₁ : a₁ = t * (a₂ * a₃ * a₄)⁻¹ := by
      rw [← hprod]; group
    have h2 := c2 g hg a₂ fr.h₂.1
    have h3 := c3 g hg a₃ fr.h₃.1
    have h4 := c4 g hg a₄ fr.h₄.1
    have hrest : g * (a₂ * a₃ * a₄) = (a₂ * a₃ * a₄) * g := by
      calc g * (a₂ * a₃ * a₄) = (g * a₂) * a₃ * a₄ := by group
        _ = a₂ * (g * a₃) * a₄ := by rw [h2]; group
        _ = a₂ * a₃ * (g * a₄) := by rw [h3]; group
        _ = (a₂ * a₃ * a₄) * g := by rw [h4]; group
    have hrest' : g * (a₂ * a₃ * a₄)⁻¹ = (a₂ * a₃ * a₄)⁻¹ * g := by
      calc g * (a₂ * a₃ * a₄)⁻¹ = (a₂ * a₃ * a₄)⁻¹ * ((a₂ * a₃ * a₄) * g) * (a₂ * a₃ * a₄)⁻¹ := by
            group
        _ = (a₂ * a₃ * a₄)⁻¹ * (g * (a₂ * a₃ * a₄)) * (a₂ * a₃ * a₄)⁻¹ := by rw [hrest]
        _ = (a₂ * a₃ * a₄)⁻¹ * g := by group
    have htg := hq.z_central g hg
    rw [ha₁]
    calc t * (a₂ * a₃ * a₄)⁻¹ * g = t * (g * (a₂ * a₃ * a₄)⁻¹) := by rw [mul_assoc, hrest']
      _ = g * (t * (a₂ * a₃ * a₄)⁻¹) := by rw [← mul_assoc, htg, mul_assoc]
  rcases hq.center a₁ fr.h₁.1 hcent with h | h
  · have ho := fr.o₁
    rw [h, orderOf_one] at ho
    exact absurd ho (by decide)
  · have h2 : orderOf a₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [h, pow_two]; exact hq.z_sq)
    rw [fr.o₁] at h2
    exact absurd h2 (by decide)

theorem t_tau_mem_ae6P (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    t ∈ ae6P Ω[R] t ∧ y * t * y⁻¹ ∈ ae6P Ω[R] t := by
  have hStd := H.ex.1
  have hF := H.ex.2.1
  have hd := hStd.datum
  obtain ⟨h2, h3, h4, -, -, -⟩ := twins_facts H
  have hK := le_ae6P (Ω := Ω[R]) hd.mem hd.hz
  refine ⟨hK hd.hz.mem, ?_⟩
  rw [fr.hy]
  refine (ae6P Ω[R] t).mul_mem ((ae6P Ω[R] t).mul_mem ((ae6P Ω[R] t).mul_mem ?_ ?_) ?_) ?_
  · exact hK fr.h₁.1
  · exact le_ae6P hd.hK'.1 h2 fr.h₂.1
  · exact le_ae6P hd.hK₃.1 h3 fr.h₃.1
  · exact le_ae6P hF.1.1 h4 fr.h₄.1

theorem ae6E3_elemAb_le (hE : V3AE6E n) (hC : V3AE6EComm n) {h : Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y)
    (hx : AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h) :
    IsElemAbelian2 (Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y)) 3 ∧
      Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) ≤ ae6P Ω[R] t := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hinv := conjInvariant_conjClass (tightCore R)
  obtain ⟨hhC, hxD, hcomm⟩ := hx
  have hEab := (hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr)
  have hDsq := A6DN.ae6D_sq_eq_one hE hC H fr
  set τ := y * t * y⁻¹ with hτdef
  set x := h * τ * h⁻¹ with hxdef
  set D := ae6D Ω[R] W (u₁ * u₂) with hDdef
  have htt : t * t = 1 := hd.hz.sq
  have hτ1 : τ * τ = 1 := by
    rw [hτdef]; calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hxx : x * x = 1 := by
    rw [hxdef]; calc h * τ * h⁻¹ * (h * τ * h⁻¹) = h * (τ * τ) * h⁻¹ := by group
      _ = 1 := by rw [hτ1]; group
  have hED : ae6E Ω[R] (u₁ * u₂) ≤ D := by
    rw [hDdef]
    unfold ae6D
    refine le_trans ?_ (le_iSup _ (1 : ↥(MGrp Ω[R] W)))
    simp [conjSub_one]
  have htD : t ∈ D := hED hEab.2.2.1
  have hτD : τ ∈ D := hED hEab.2.2.2
  have hcD : ⁅D, Subgroup.zpowers x⁆ ≤ D := by
    rw [hcomm]
    exact (Subgroup.closure_le _).mpr (by
      rintro _ (rfl | rfl)
      · exact htD
      · exact hτD)
  obtain ⟨-, hxc⟩ := normalizes_and_comm_of_commutator hDsq hxx hcD
  have hxτ : x * τ = τ * x := hxc τ (by rw [hcomm]; exact Subgroup.subset_closure (by simp))
  have hxt : x * t = t * x := hxc t (by rw [hcomm]; exact Subgroup.subset_closure (by simp))
  have htτ : t * τ = τ * t := by
    have := (hEab.1.2)
    have hab : ∀ a ∈ ae6E Ω[R] (u₁ * u₂), ∀ b ∈ ae6E Ω[R] (u₁ * u₂), a * b = b * a := by
      intro a ha b hb
      have h1 := hEab.1.2 (a * b) ((ae6E Ω[R] (u₁ * u₂)).mul_mem ha hb)
      have h2 := hEab.1.2 a ha
      have h3 := hEab.1.2 b hb
      calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
        _ = (a * a) * b * a * (b * b) := by group
        _ = b * a := by rw [h2, h3]; group
    exact hab t hEab.2.2.1 τ hEab.2.2.2
  have hτne : τ ≠ t := tau_ne_t H fr
  have hτ1' : τ ≠ 1 := by
    rw [hτdef]; intro e; apply hd.hz.ne_one
    calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
      _ = 1 := by rw [e]; group
  have hx1 : x ≠ 1 := fun e => hxD (by rw [e]; exact D.one_mem)
  have hxt' : x ≠ t := fun e => hxD (by rw [e]; exact htD)
  have hxτ' : x ≠ τ := fun e => hxD (by rw [e]; exact hτD)
  have hxtτ : x ≠ t * τ := fun e => hxD (by rw [e]; exact D.mul_mem htD hτD)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact ChainFrame.card_closure_triple_eq_eight htt hτ1 hxx htτ hxt.symm hxτ.symm hd.hz.ne_one
      hτ1' hτne hx1 hxt' hxτ' hxtτ
  · intro z hz
    rcases ChainFrame.mem_closure_eight htt hτ1 hxx htτ hxt.symm hxτ.symm hz with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact htt
    · exact hτ1
    · exact hxx
    · calc t * τ * (t * τ) = (t * t) * (τ * τ) := by rw [show t * τ * (t * τ) = t * (τ * t) * τ by group, ← htτ]; group
        _ = 1 := by rw [htt, hτ1, one_mul]
    · calc t * x * (t * x) = (t * t) * (x * x) := by rw [show t * x * (t * x) = t * (x * t) * x by group, hxt]; group
        _ = 1 := by rw [htt, hxx, one_mul]
    · calc τ * x * (τ * x) = (τ * τ) * (x * x) := by rw [show τ * x * (τ * x) = τ * (x * τ) * x by group, hxτ]; group
        _ = 1 := by rw [hτ1, hxx, one_mul]
    · have hc1 : (τ * x) * t = t * (τ * x) := by
        calc τ * x * t = τ * (x * t) := by group
          _ = τ * (t * x) := by rw [hxt]
          _ = (τ * t) * x := by group
          _ = (t * τ) * x := by rw [htτ]
          _ = t * (τ * x) := by group
      have hsq : (τ * x) * (τ * x) = 1 := by
        calc τ * x * (τ * x) = τ * (x * τ) * x := by group
          _ = τ * (τ * x) * x := by rw [hxτ]
          _ = (τ * τ) * (x * x) := by group
          _ = 1 := by rw [hτ1, hxx, one_mul]
      calc t * (τ * x) * (t * (τ * x)) = t * ((τ * x) * t) * (τ * x) := by group
        _ = t * (t * (τ * x)) * (τ * x) := by rw [hc1]
        _ = (t * t) * ((τ * x) * (τ * x)) := by group
        _ = 1 := by rw [htt, hsq, one_mul]
  · obtain ⟨htP, hτP⟩ := t_tau_mem_ae6P H fr
    have hhc : h * t * h⁻¹ = t := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hhC
      rw [hhC, mul_inv_cancel_right]
    have hxP : x ∈ ae6P Ω[R] t := conj_mem_ae6P hinv hhc hτP
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (rfl | rfl | rfl)
    exacts [htP, hτP, hxP]

end Datum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Hx
