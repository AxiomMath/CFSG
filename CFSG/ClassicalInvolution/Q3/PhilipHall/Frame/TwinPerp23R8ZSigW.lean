module

import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AWFMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23SigC
public import CFSG.ClassicalInvolution.Q3.Sec13L94Tight

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section ThreeAct

variable {Y : Type} [Group Y]

theorem three_act_distinct {α : Type*} (f : Y → α → α) (hmul : ∀ a b x, f (a * b) x = f a (f b x))
    (hone : ∀ x, f 1 x = x) {x₀ : Y} {k : ℕ} (hxk : x₀ ^ 3 ^ k = 1) {w : α} (hmove : f x₀ w ≠ w) :
    w ≠ f x₀ w ∧ f x₀ w ≠ f (x₀ ^ 2) w ∧ w ≠ f (x₀ ^ 2) w := by
  refine ⟨fun h => hmove h.symm, ?_, ?_⟩
  · intro h
    apply hmove
    have h1 := congrArg (f x₀⁻¹) h
    rw [← hmul, ← hmul, inv_mul_cancel, hone, show x₀⁻¹ * x₀ ^ 2 = x₀ by group] at h1
    exact h1.symm
  · intro h
    apply hmove
    have key : ∀ m : ℕ, f (x₀ ^ (2 * m)) w = w := by
      intro m
      induction m with
      | zero => simpa using hone w
      | succ m ih =>
        rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, hmul, ← h, ih]
    obtain ⟨r, hr⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have h2 := key (r + 1)
    rw [show 2 * (r + 1) = 3 ^ k + 1 by omega, pow_succ, hxk, one_mul] at h2
    exact h2

end ThreeAct


section WTransX0

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

@[expose] def eClass (t e : Y) : Set Y :=
  {f : Y | ∃ c ∈ Subgroup.centralizer ({t} : Set Y), f = c * e * c⁻¹}

theorem wTrans_of_x0 (hc : P23Cfg n Y R S t K' W u e g) (hT : (eClass t e).ncard ≤ 3)
    {X : Subgroup Y} {x₀ : Y} (hEX : rLayer (Om R) e ≤ X) (hx₀X : x₀ ∈ X) (hx₀t : x₀ * t = t * x₀)
    (hx₀3 : IsPGroup 3 (Subgroup.zpowers x₀)) (hx₀e : x₀ * e * x₀⁻¹ ≠ e) :
    ∀ W₁ ∈ WSet (Om R), t ∈ W₁ → ∃ c ∈ X, conjSub c W = W₁ := by
  classical
  intro W₁ hW₁ htW₁
  obtain ⟨c, hcC, rfl⟩ := p23WTrans_proved Y R S t K' W u e g hc W₁ hW₁ htW₁
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x₀ ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hx₀3 ⟨x₀, Subgroup.mem_zpowers x₀⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hx₀C : x₀ ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr hx₀t
  obtain ⟨h01, h12, h02⟩ := three_act_distinct (fun (a : Y) (x : Y) => a * x * a⁻¹)
    (fun a b x => by group) (fun x => by group) hk (w := e) hx₀e
  have hmem : ∀ j : ℕ, x₀ ^ j * e * (x₀ ^ j)⁻¹ ∈ eClass t e := fun j =>
    ⟨x₀ ^ j, (Subgroup.centralizer ({t} : Set Y)).pow_mem hx₀C j, rfl⟩
  have hcls : ∃ j : ℕ, j < 3 ∧ c * e * c⁻¹ = x₀ ^ j * e * (x₀ ^ j)⁻¹ := by
    by_contra hno
    push Not at hno
    have n1 : e ∉ ({x₀ * e * x₀⁻¹, x₀ ^ 2 * e * (x₀ ^ 2)⁻¹, c * e * c⁻¹} : Set Y) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h01, h02, fun h => hno 0 (by norm_num) (by simpa using h.symm)⟩
    have n2 : x₀ * e * x₀⁻¹ ∉ ({x₀ ^ 2 * e * (x₀ ^ 2)⁻¹, c * e * c⁻¹} : Set Y) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h12, fun h => hno 1 (by norm_num) (by simpa using h.symm)⟩
    have n3 : x₀ ^ 2 * e * (x₀ ^ 2)⁻¹ ∉ ({c * e * c⁻¹} : Set Y) := by
      simpa using fun h => hno 2 (by norm_num) h.symm
    have hsub : ({e, x₀ * e * x₀⁻¹, x₀ ^ 2 * e * (x₀ ^ 2)⁻¹, c * e * c⁻¹} : Set Y) ⊆ eClass t e := by
      intro f hf
      rcases hf with rfl | rfl | rfl | rfl
      · simpa using hmem 0
      · simpa using hmem 1
      · exact hmem 2
      · exact ⟨c, hcC, rfl⟩
    have hcard : ({e, x₀ * e * x₀⁻¹, x₀ ^ 2 * e * (x₀ ^ 2)⁻¹, c * e * c⁻¹} : Set Y).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
        Set.ncard_insert_of_notMem n3, Set.ncard_singleton]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  obtain ⟨j, -, hj⟩ := hcls
  set d : Y := (x₀ ^ j)⁻¹ * c with hd
  have hde : d ∈ Subgroup.centralizer ({e} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : d * e * d⁻¹ = e := by
      calc d * e * d⁻¹ = (x₀ ^ j)⁻¹ * (c * e * c⁻¹) * (x₀ ^ j) := by rw [hd]; group
        _ = e := by rw [hj]; group
    calc d * e = d * e * d⁻¹ * d := by group
      _ = e * d := by rw [h1]
  obtain ⟨x', hx'E, hx'⟩ := AWF.exists_rLayer_conj hc hde
  refine ⟨x₀ ^ j * x', X.mul_mem (X.pow_mem hx₀X j) (hEX hx'E), ?_⟩
  have hcd : c = x₀ ^ j * d := by rw [hd]; group
  rw [hcd, conjSub_mul, conjSub_mul, hx']

end WTransX0

section SigX0

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_mGrp_le_E (hc : P23Cfg n Y R S t K' W u e g) : MGrp (Om R) W ≤ rLayer (Om R) e := by
  have hNe := normalizer_le_centralizer_e hc.data
  unfold MGrp
  refine iSup₂_le fun R' hR' => ?_
  unfold rLayer
  exact le_iSup₂_of_le (f := fun R'' (_ : R'' ∈ RSet (Om R)) =>
    ⨆ (_ : R'' ≤ Subgroup.centralizer ({e} : Set Y)), R'') R' hR'.1
    (le_iSup_of_le (hR'.2.trans hNe) le_rfl)

theorem p23_conj_of_D_le (hc : P23Cfg n Y R S t K' W u e g) {X : Subgroup Y}
    (hEX : rLayer (Om R) e ≤ X) :
    ∀ J ∈ Om R, (∃ T ∈ DSet (Om R) W, IsSylow2In T J) →
      ∃ m ∈ X, conjSub m (tightCore R) = J := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have htrans : ∀ J ∈ Om R, ∃ a : Y, conjSub a (tightCore R) = J := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  obtain ⟨R₁, -, -, -, hR₁, -, hR₁D, -⟩ := e_decomp hc
  rintro J hJ ⟨T, hTD, hTJ⟩
  obtain ⟨a, rfl⟩ := htrans J hJ
  obtain ⟨m, hm, hmK, -⟩ := Sec13.L94T.exists_mGrp_conj hPG hd.hW hK htrans hz hc.std.hK'
    hc.std.hne hperp hd.hS4 hR₁ hR₁D hJ hTJ hTD (hz.conj a)
  exact ⟨m, hEX (p23_mGrp_le_E hc hm), hmK⟩

theorem sig_of_x0 (hc : P23Cfg n Y R S t K' W u e g)
    (hT : (eClass t e).ncard ≤ 3)
    {X : Subgroup Y} {x₀ : Y} (hEX : rLayer (Om R) e ≤ X) (hKX : tightCore R ≤ X)
    (hx₀X : x₀ ∈ X) (hx₀t : x₀ * t = t * x₀)
    (hx₀3 : IsPGroup 3 (Subgroup.zpowers x₀)) (hx₀e : x₀ * e * x₀⁻¹ ≠ e) :
    ∀ J ∈ dstarComp (Om R) (tightCore R), J ≤ X := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  exact SigC.le_of_mem_dstarComp hΩ hK hz hKX
    (SigC.key_of_trans hΩ (wTrans_of_x0 hc hT hEX hx₀X hx₀t hx₀3 hx₀e) (p23_conj_of_D_le hc hEX))

end SigX0

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23



