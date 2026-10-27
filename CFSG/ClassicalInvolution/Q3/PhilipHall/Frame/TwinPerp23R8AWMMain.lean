module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AWTr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AWMCls
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AWMNondeg
import CFSG.ClassicalInvolution.Q3.TL4AE286None
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
open CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.TC.Thin

section Gen

variable {Y : Type} [Group Y]

theorem conjSub_le_of_mem {H A : Subgroup Y} {m : Y} (hm : m ∈ H) (hA : A ≤ H) : conjSub m A ≤ H := by
  intro x hx
  have h1 : m⁻¹ * x * m ∈ A := mem_conjSub_iff.mp hx
  have h2 : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
  rw [h2]
  exact H.mul_mem (H.mul_mem hm (hA h1)) (H.inv_mem hm)

end Gen

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem exists_x0 (hc : P23Cfg n Y R S t K' W u e g) (b : Y) (hKX : tightCore R ≤ p23XE R e b)
    (I : AEIdent {J | J ∈ Om R ∧ J ≤ p23XE R e b} 7) :
    ∃ x₀ ∈ p23XE R e b, x₀ * t = t * x₀ ∧ (∃ k : ℕ, x₀ ^ 3 ^ k = 1) ∧
      ∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), x₀ * e * x₀⁻¹ ≠ o * e * o⁻¹ := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hst := CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC
  set X := p23XE R e b with hX
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', -, -, hb₁b₁, hb'b', hub⟩ :=
    e_decomp_W hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hK'mem : K' ∈ Om R := hc.std.hK'.1
  have hK'X : K' ≤ X := by
    obtain ⟨m, hmX, hmK⟩ := p23_conj_of_D hc b K' hK'mem ⟨R₁', hR'D, hR₁'⟩
    rw [← hmK]
    exact conjSub_le_of_mem hmX hKX
  have hgX : g ∈ X := p23_mGrp_le_XE hc b hd.hg
  have hKgX : conjSub g (tightCore R) ≤ X := conjSub_le_of_mem hgX hKX
  have hKgmem : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hR₂ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  set P : Set (Subgroup Y) := {J | J ∈ Om R ∧ J ≤ X} with hP
  have hKP : tightCore R ∈ P := ⟨hK, hKX⟩
  have hK'P : K' ∈ P := ⟨hK'mem, hK'X⟩
  have hKgP : conjSub g (tightCore R) ∈ P := ⟨hKgmem, hKgX⟩
  have hn5 : (5 : ℕ) ≤ 7 := by norm_num
  obtain ⟨α₀, h₀, c₀, hl₀⟩ := I.label _ hKP
  obtain ⟨α₁, h₁, c₁, hl₁⟩ := I.label _ hK'P
  obtain ⟨α₂, h₂', c₂, hl₂⟩ := I.label _ hKgP
  have hR₁P : R₁ ≤ pSpan P := hR₁.1.trans (le_pSpan hKP)
  have hR₁'P : R₁' ≤ pSpan P := hR₁'.1.trans (le_pSpan hK'P)
  have hR₂P : conjSub g R₁ ≤ pSpan P := hR₂.1.trans (le_pSpan hKgP)
  have hlR₁ := map_eq_of_le_sup_oddCore I hn5 (le_pSpan hKP) hR₁.1
    (TL4.le_sup_oddCoreOf_of_isSylow2In (h2 _ hK) hR₁) hl₀ (oddCoreOf_odd_natCard _)
  have hlR₁' := map_eq_of_le_sup_oddCore I hn5 (le_pSpan hK'P) hR₁'.1
    (TL4.le_sup_oddCoreOf_of_isSylow2In (h2 _ hK'mem) hR₁') hl₁ (oddCoreOf_odd_natCard _)
  have hlR₂ := map_eq_of_le_sup_oddCore I hn5 (le_pSpan hKgP) hR₂.1
    (TL4.le_sup_oddCoreOf_of_isSylow2In (h2 _ hKgmem) hR₂) hl₂ (oddCoreOf_odd_natCard _)
  have h8₁ : Nat.card R₁ = 8 := hst.card8 _ hK R₁ hR₁
  have h8₁' : Nat.card R₁' = 8 := hst.card8 _ hK'mem R₁' hR₁'
  have h8₂ : Nat.card (conjSub g R₁) = 8 := hst.card8 _ hKgmem _ hR₂
  have ht₁ : IsUniqueInvolution R₁ t :=
    ⟨hb₁b₁ ▸ R₁.mul_mem hb₁R hb₁R, hz.ne_one, hz.sq, fun y hy h => hz.unique y (hR₁.1 hy) h⟩
  have ht₁' : IsUniqueInvolution R₁' t :=
    ⟨hb'b' ▸ R₁'.mul_mem hb'R' hb'R', hz.ne_one, hz.sq, fun y hy h => hz'.unique y (hR₁'.1 hy) h⟩
  have hv₂ : IsUniqueInvolution (conjSub g R₁) (u * e) := hd.hgt ▸ ht₁.conj g
  have hQ : IsQuatSub R₁ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR₁)
  obtain ⟨k, hk, hkb⟩ : ∃ k ∈ R₁, k * b₁ ≠ b₁ * k := by
    by_contra hcon
    push Not at hcon
    have := hQ.sq_eq_one_of_central hb₁R (fun y hy => (hcon y hy).symm)
    exact hz.ne_one (hb₁b₁ ▸ this)
  have hkt : k * t = t * k := (hz.commute_of_mem (hR₁.1 hk)).symm
  have he : e = b₁ * b' * (u * e) := by
    rw [← hub, ← mul_assoc, hd.hu2, one_mul]
  have heR₁ : ∀ x ∈ R₁, x * e = e * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hR₁e hx)
  have heR₁' : ∀ x ∈ R₁', x * e = e * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hR₁'e hx)
  obtain ⟨he', β₀, hβ₀, hφt, hne1, hnez, hcommE⟩ := twin_calculus I hR₁P hR₁'P hR₂P h8₁ h8₁' h8₂
    ⟨α₀, h₀, c₀, hlR₁⟩ ⟨α₁, h₁, c₁, hlR₁'⟩ ⟨α₂, h₂', c₂, hlR₂⟩ ht₁ ht₁' hv₂ hb₁R hb'R'
    (fun x hx y hy => hcomm x hx y hy) hk hkb hkt he heR₁ heR₁'
  have hεmem : I.φ ⟨e, he'⟩ ∈ (aeSub 7).map (mkQ 7) := by
    rw [← I.range_eq]
    exact ⟨_, rfl⟩
  have hε2 : I.φ ⟨e, he'⟩ * I.φ ⟨e, he'⟩ = 1 := by
    rw [← map_mul]
    have : (⟨e, he'⟩ * ⟨e, he'⟩ : ↥(pSpan P)) = 1 := Subtype.ext hd.he2
    rw [this, map_one]
  obtain ⟨w, hwmem, hw3, hwz, hwne, hwsq⟩ :=
    exists_three_elt_moving β₀ hβ₀ hεmem hε2 hne1 hnez hcommE
  obtain ⟨x, hxw, k', hxk⟩ := I.exists_lift_pow_three (by rw [I.range_eq]; exact hwmem) hw3
  have htX : t ∈ pSpan P := hR₁P ht₁.mem
  have hxt : x * ⟨t, htX⟩ = ⟨t, htX⟩ * x := by
    refine comm_of_pow_three_of_central_ker I.φ I.ker_le ?_ hxk ?_
    · exact Subtype.ext hz.sq
    · rw [hxw, hφt]
      exact hwz
  have hXp : pSpan P ≤ X := pSpan_le (fun J hJ => hJ.2)
  refine ⟨(x : Y), hXp x.2, congrArg Subtype.val hxt, ⟨k', ?_⟩, ?_⟩
  · have := congrArg Subtype.val hxk
    rwa [Subgroup.coe_pow] at this
  ·
    intro o ho heq
    have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
    have heW : e ∈ W := (T7K.e_mem_inf hd).1
    have het : e * t = t * e := hWab _ heW _ hd.hzW
    have heC : e ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr het
    have heO : ∀ q ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)),
        e * q * e⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := fun q hq =>
      (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf _ heC) q).mp hq
    have hcO : (x : Y) * e * (x : Y)⁻¹ * e⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
      rw [heq]
      have : o * e * o⁻¹ * e⁻¹ = o * (e * o⁻¹ * e⁻¹) := by group
      rw [this]
      exact (oddCoreOf _).mul_mem ho (heO o⁻¹ ((oddCoreOf _).inv_mem ho))
    have hcm : ((x : Y) * e * (x : Y)⁻¹ * e⁻¹) ^
        Nat.card ↥(oddCoreOf (Subgroup.centralizer ({t} : Set Y))) = 1 := by
      have := pow_card_eq_one'
        (G := ↥(oddCoreOf (Subgroup.centralizer ({t} : Set Y)))) (x := ⟨_, hcO⟩)
      exact congrArg Subtype.val this
    set cX : ↥(pSpan P) := x * ⟨e, he'⟩ * x⁻¹ * ⟨e, he'⟩⁻¹ with hcX
    have hcXY : (cX : Y) = (x : Y) * e * (x : Y)⁻¹ * e⁻¹ := rfl
    have hcXm : cX ^ Nat.card ↥(oddCoreOf (Subgroup.centralizer ({t} : Set Y))) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hcXY]; exact hcm)
    have hφcX : I.φ cX = w * I.φ ⟨e, he'⟩ * w⁻¹ * (I.φ ⟨e, he'⟩)⁻¹ := by
      simp only [hcX, map_mul, map_inv, hxw]
    exact false_of_odd_pow_of_image I.φ (oddCoreOf_odd_natCard _) hcXm
      (by rw [hφcX]; exact hwsq) (by rw [hφcX]; exact hwne)

theorem p23E8AWMove_of_cls (hCls : P23E8AZ8Cls n) : P23E8AWMove n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 _hα0 b hId hKX c hcC
  obtain ⟨I⟩ := hId
  obtain ⟨y, hyY, hyt, hy3, hmove⟩ := AY.exists_y hc hA5
  obtain ⟨x₀, hx₀X, hx₀t, ⟨k, hxk⟩, hx₀move⟩ := exists_x0 hc b hKX I
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  set O := oddCoreOf C with hOdef
  have hOC : ∀ q ∈ C, ∀ o ∈ O, q * o * q⁻¹ ∈ O := fun q hq o ho =>
    (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf _ hq) o).mp ho
  have hcls : ∀ c ∈ C, ∃ i : ℕ, i < 3 ∧ OConj O (c * e * c⁻¹) (y ^ i * e * (y ^ i)⁻¹) := by
    intro c hc'
    obtain ⟨i, hi, o, ho, heq⟩ :=
      hCls hcit hP Y R S t K' W u e g hc hno hA5 hA6 y hyY hyt hy3 hmove c hc'
    exact ⟨i, hi, o, ho, heq⟩
  have hx₀C : x₀ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hx₀t
  have hmoveO : ¬ OConj O (x₀ * e * x₀⁻¹) e := fun ⟨o, ho, h⟩ => hx₀move o ho h
  obtain ⟨j, -, o, ho, heq⟩ := exists_pow_of_three_classes hOC hcls hx₀C hxk hmoveO c hcC
  refine ⟨x₀ ^ j, (p23XE R e b).pow_mem hx₀X j, ?_, o⁻¹, O.inv_mem ho, ?_⟩
  · exact (Commute.pow_left (show Commute x₀ t from hx₀t) j).eq
  · rw [heq]
    group

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM
