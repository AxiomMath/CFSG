module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Sig

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section AWTr

open scoped commutatorElement

variable {n : ℕ}

@[expose] def P23E8AWFib (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ →
        ∀ d ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({e} : Set Y),
          ∃ x ∈ rLayer (Om R) e, conjSub x W = conjSub d W

@[expose] def P23E8AWMove (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ → ∀ b : Y,
        Nonempty (TC.Thin.AEIdent {J | J ∈ Om R ∧ J ≤ p23XE R e b} 7) →
        tightCore R ≤ p23XE R e b →
          ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∃ x ∈ p23XE R e b, x * t = t * x ∧
            ∃ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), x * e * x⁻¹ = o * (c * e * c⁻¹) * o⁻¹

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K' W : Subgroup Y}
  {u e g : Y}

theorem oddCoreOf_centralizer_t_le_centralizer_e (hα : P23Alpha n) (hc : P23Cfg n Y R S t K' W u e g)
    (hA5 : SecAE R u 5) (hα0 : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤ Subgroup.centralizer ({e} : Set Y) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hz' : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hue_t : u * e * t = t * (u * e) := hWab _ (W.mul_mem hd.huW heW) _ hd.hzW
  have hue2 : u * e * (u * e) = 1 := by
    have hue : u * e = e * u := hWab _ hd.huW _ heW
    calc u * e * (u * e) = u * (e * u) * e := by group
      _ = u * (u * e) * e := by rw [hue]
      _ = (u * u) * (e * e) := by group
      _ = 1 := by rw [hd.hu2, hd.he2, one_mul]
  have hsup : ∀ x, x ∈ tightCore R ⊔ K' → u⁻¹ * x ∈ tightCore R ⊔ K' := fun x hx =>
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hd.hu) hx
  have hue1 : u * e ≠ 1 := by
    intro h
    apply e_not_mem_sup hc
    have : e = u⁻¹ * 1 := by rw [← h]; group
    rw [this]; exact hsup 1 (Subgroup.one_mem _)
  have hue_ne : u * e ≠ t := by
    intro h
    apply e_not_mem_sup hc
    have : e = u⁻¹ * t := by rw [← h]; group
    rw [this]; exact hsup t (Subgroup.mem_sup_left hz'.mem)
  obtain ⟨-, hbal⟩ := hα Y R S t K' W u e g hc (Or.inr (Or.inr (Or.inr hA5)))
  have hA2 : alphaOf (Subgroup.closure ({u * e, t} : Set Y)) = ⊥ := by
    rw [← hα0]
    refine hbal _ ?_ (T7A.isElemAbelian2_closure_pair hue2 hz'.sq hue1 hz'.ne_one hue_ne hue_t)
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  intro o ho
  have ht1 : t ≠ 1 := hz'.ne_one
  have h1 : ⁅o, u⁆ = 1 := by
    have hle := commutator_oddCore_le_alphaOf ht1 (Subgroup.closure ({u, t} : Set Y))
      (Subgroup.subset_closure (by simp))
    rw [hα0] at hle
    exact (Subgroup.mem_bot.mp (hle (Subgroup.commutator_mem_commutator ho
      (Subgroup.subset_closure (by simp)))))
  have h2 : ⁅o, u * e⁆ = 1 := by
    have hle := commutator_oddCore_le_alphaOf ht1 (Subgroup.closure ({u * e, t} : Set Y))
      (Subgroup.subset_closure (by simp))
    rw [hA2] at hle
    exact (Subgroup.mem_bot.mp (hle (Subgroup.commutator_mem_commutator ho
      (Subgroup.subset_closure (by simp)))))
  rw [commutatorElement_eq_one_iff_mul_comm] at h1 h2
  have h1' : o * u⁻¹ = u⁻¹ * o := by
    calc o * u⁻¹ = u⁻¹ * (u * o) * u⁻¹ := by group
      _ = u⁻¹ * (o * u) * u⁻¹ := by rw [h1]
      _ = u⁻¹ * o := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc o * e = (o * u⁻¹) * (u * e) := by group
    _ = (u⁻¹ * o) * (u * e) := by rw [h1']
    _ = u⁻¹ * (o * (u * e)) := by group
    _ = u⁻¹ * ((u * e) * o) := by rw [h2]
    _ = e * o := by group

theorem p23E8AWTr_of_parts (hα : P23Alpha n) (hF : P23E8AWFib n) (hM : P23E8AWMove n) : P23E8AWTr n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 hα0 b hId hKX W₁ hW₁ htW₁
  obtain ⟨c, hcC, rfl⟩ := p23WTrans_proved Y R S t K' W u e g hc W₁ hW₁ htW₁
  obtain ⟨x, hxX, hxt, o, ho, hxe⟩ := hM hcit hP Y R S t K' W u e g hc hno hA5 hA6 hα0 b hId hKX c hcC
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hxt
  have hoC : o ∈ C := oddCoreOf_le_self C ho
  have hOe := oddCoreOf_centralizer_t_le_centralizer_e hα hc hA5 hα0
  set d₀ := x⁻¹ * o * c with hd₀
  have hd₀C : d₀ ∈ C := C.mul_mem (C.mul_mem (C.inv_mem hxC) hoC) hcC
  have hd₀e : d₀ ∈ Subgroup.centralizer ({e} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : o * (c * e * c⁻¹) * o⁻¹ = x * e * x⁻¹ := hxe.symm
    calc d₀ * e = x⁻¹ * (o * (c * e * c⁻¹) * o⁻¹) * (o * c) := by rw [hd₀]; group
      _ = x⁻¹ * (x * e * x⁻¹) * (o * c) := by rw [h1]
      _ = e * d₀ := by rw [hd₀]; group
  have ho' : x⁻¹ * o⁻¹ * x⁻¹⁻¹ ∈ oddCoreOf C :=
    T7R.conj_mem_oddCoreOf (C.inv_mem hxC) ((oddCoreOf C).inv_mem ho)
  rw [inv_inv] at ho'
  set d' := (x⁻¹ * o⁻¹ * x) * d₀ with hd'
  have hd'C : d' ∈ C := C.mul_mem (oddCoreOf_le_self C ho') hd₀C
  have hd'e : d' ∈ Subgroup.centralizer ({e} : Set Y) :=
    Subgroup.mul_mem _ (hOe ho') hd₀e
  obtain ⟨x', hx'E, hx'⟩ := hF hcit hP Y R S t K' W u e g hc hno hA5 hA6 hα0 d' ⟨hd'C, hd'e⟩
  have hceq : c = x * d' := by rw [hd', hd₀]; group
  refine ⟨x * x', (p23XE R e b).mul_mem hxX (le_sup_left (a := rLayer (Om R) e) hx'E), ?_⟩
  rw [hceq, conjSub_mul, conjSub_mul, hx']

end AWTr

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
