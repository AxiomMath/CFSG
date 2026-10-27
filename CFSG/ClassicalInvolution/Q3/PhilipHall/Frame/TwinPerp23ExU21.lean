module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU20
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU19
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A04

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section U21

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem orderOf_four_of_sq {a t : Y} (ht1 : t ≠ 1) (ht2 : t * t = 1) (h : a * a = t) :
    orderOf a = 4 := by
  have h2 : a ^ 2 = t := by rw [pow_two]; exact h
  have h4 : a ^ 4 = 1 := by
    have : a ^ 4 = (a ^ 2) ^ 2 := by group
    rw [this, h2, pow_two]; exact ht2
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a) (by rw [pow_one, h2]; exact ht1)
    (by rw [show 2 ^ (1 + 1) = 4 by norm_num]; exact h4)
  simpa using this

theorem gamma_t (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) :
    Subgroup.centralizer ({t} : Set Y) ≤
      gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (Subgroup.centralizer ({t} : Set Y)) := by
  classical
  set M := gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (Subgroup.centralizer ({t} : Set Y))
    with hM
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hne' : K' ≠ tightCore R := hc.std.hne
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc, hz, hc.std.hK',
      hc.std.hne, hperp⟩
  obtain ⟨A, A', hA, hA', hAe, hA'e, hAA', hAc⟩ := exists_std hc
  have hKM : tightCore R ≤ M := twin_le_gamma2_t hc hK hz hA hAe
  have hK'M : K' ≤ M := twin_le_gamma2_t hc hK'Ω hz' hA' hA'e
  have hLM : tightCore R ⊔ K' ≤ M := sup_le hKM hK'M
  have hueB : u * e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({u * e, u, t} : Set Y) := T7K.u_mem_B t u e
  have heB : e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ huB) hueB
    rwa [show u⁻¹ * (u * e) = e by group] at h
  have het : e ≠ t := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hz.mem)
  have hCeM : ∀ x ∈ Subgroup.centralizer ({t} : Set Y), x ∈ Subgroup.centralizer ({e} : Set Y) →
      x ∈ M := fun x h1 h2 => inf_cent_t_le_gamma2 hc heB hd.he1 het ⟨h1, h2⟩
  have hCuM : ∀ x ∈ Subgroup.centralizer ({t} : Set Y), x ∈ Subgroup.centralizer ({u} : Set Y) →
      x ∈ M := fun x h1 h2 => inf_cent_t_le_gamma2 hc huB hd.hu1 hd.huz ⟨h1, h2⟩
  have hLC : tightCore R ⊔ K' ≤ Subgroup.centralizer ({t} : Set Y) :=
    sup_le (le_centralizer_of_unique hz) (le_centralizer_of_unique hz')
  have ht1 := hz.ne_one
  have ht2 := hz.sq
  have hstd : ∀ a ∈ A, ∀ x ∈ A, ∀ b ∈ A', ∀ y ∈ A', a * a = t → x * x = t → b * b = t →
      y * y = t → ∃ g ∈ Subgroup.centralizer ({t} : Set Y), g ∈ M ∧ g * a * g⁻¹ = x ∧
        g * b * g⁻¹ = y := by
    intro a ha x hx b hb y hy haa hxx hbb hyy
    obtain ⟨g', hgt, hge, h1, h2⟩ := fuse_stdC hP hc.std.perp hc.std.hK' hc.std.hne hd.he2 hd.he1
      hno hA hA' hAe hA'e hAA' ha hx hb hy haa hxx hbb hyy
    exact ⟨g', hgt, hCeM g' hgt hge, h1, h2⟩
  intro c hct
  have hu'M : c * u * c⁻¹ ∈ tightCore R ⊔ K' :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7K.conj_mem_sup hs hct hd.hu
  have hct' : c * t * c⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hct
    calc c * t * c⁻¹ = (t * c) * c⁻¹ := by rw [this]
      _ = t := by group
  have hu'1 : c * u * c⁻¹ ≠ 1 := fun h => hd.hu1 (by
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = c⁻¹ * 1 * c := by rw [h]
      _ = 1 := by group)
  have hu't : c * u * c⁻¹ ≠ t := fun h => hd.huz (by
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = c⁻¹ * t * c := by rw [h]
      _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [hct']
      _ = t := by group)
  have hu'2 : (c * u * c⁻¹) * (c * u * c⁻¹) = 1 := by
    calc (c * u * c⁻¹) * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [hd.hu2]; group
  obtain ⟨m, hmM, a, ha, b, hb, haa, hbb, hmu⟩ := exists_ab hΩ hK hK'Ω hne' hz hz' hu'M hu'1 hu't
    hu'2 hA hA' hAc
  obtain ⟨c', hc't, hc'M, hc'u⟩ := fuse_generalM hΩ hK hK'Ω hne' hz hz' hLM hA hA' hAc hstd hd.hu
    hd.hu1 hd.huz hd.hu2 hA hA' hAc ha hb (orderOf_four_of_sq ht1 ht2 haa)
    (orderOf_four_of_sq ht1 ht2 hbb)
  have hmC : m ∈ Subgroup.centralizer ({t} : Set Y) := hLC hmM
  set d := c'⁻¹ * m * c with hdd
  have hdt : d ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc't) hmC) hct
  have hdu : d ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : d * u * d⁻¹ = u := by
      calc d * u * d⁻¹ = c'⁻¹ * (m * (c * u * c⁻¹) * m⁻¹) * c' := by rw [hdd]; group
        _ = c'⁻¹ * (a * b) * c' := by rw [hmu]
        _ = c'⁻¹ * (c' * u * c'⁻¹) * c' := by rw [hc'u]
        _ = u := by group
    calc d * u = (d * u * d⁻¹) * d := by group
      _ = u * d := by rw [this]
  have hdM : d ∈ M := hCuM d hdt hdu
  have : c = m⁻¹ * c' * d := by rw [hdd]; group
  rw [this]
  exact M.mul_mem (M.mul_mem (M.inv_mem (hLM hmM)) hc'M) hdM

end U21

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
