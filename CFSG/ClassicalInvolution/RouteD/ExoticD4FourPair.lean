module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourSpin
public import CFSG.ClassicalInvolution.RouteD.ExoticD4TwinModel
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.RouteD.NonClassical (IsFundSpin eq_of_map_eq_fund
  exists_inv_of_commutes)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Facts

structure D4Facts (F : Type) [Field F] [Finite F] : Prop where
  odd : Odd (Nat.card F)
  single : Generic.FundamentalSingleClass .POmegaPlus (plusDatum 4 F (by norm_num))
  perf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)),
    ⁅R, R⁆ = R
  long : ∀ k : Fin 4, Generic.IsLongestRoot (plusDatum 4 F (by norm_num)) (Pi.single k 1)
  sl2 : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)),
    Nonempty (R ≃* SL(2, F))
  gen : ∀ x : spinGroup (quadPlus 4 F),
    ⨆ k : Fin 4, rankOneRoot (plusDatum 4 F (by norm_num)) x (Pi.single k 1) = ⊤

variable {p f : ℕ} [Fact p.Prime]

theorem D4Facts.of_galoisField (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : D4Facts (GaloisField p f) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf, le_rfl⟩
  obtain ⟨hodd, -⟩ := card_galoisField_facts hp2 hq
  have hM : Generic.modelUniv .POmegaPlus 4 p f Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus 4 p f Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 p f Fact.out).trans (modelUniv_POmegaPlus hn3)
  have hsingle : Generic.FundamentalSingleClass .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D :=
    fundamentalSingleClass .POmegaPlus 4 p f Fact.out trivial hadm (by decide) (by decide)
  have hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D, ⁅R, R⁆ = R := fun R hR =>
    le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy))
      (fundPerfect_core .POmegaPlus 4 p f hp2 trivial hadm (by omega) R hR)
  have hlong : ∀ k : Fin (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D.rank,
      Generic.IsLongestRoot (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .POmegaPlus 4 p f Fact.out trivial hadm k trivial
  have hgen : ∀ g : (Generic.modelUniv .POmegaPlus 4 p f Fact.out).K,
      ⨆ i : Fin (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D.rank,
        rankOneRoot (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D g (Pi.single i 1) = ⊤ :=
    iSup_rankOneRoot_simple_eq_top .POmegaPlus 4 p f Fact.out trivial hadm
  have hsl2 : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 p f Fact.out).D, Nonempty (R ≃* SL(2, GaloisField p f)) :=
    fun R hR => nonempty_equiv_sl2_of_mem_fundamentalSubgroups (t := .POmegaPlus) (n := 4)
      hp2 trivial hadm (by decide) (by decide) hR
  have key : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hn3⟩ →
      Generic.FundamentalSingleClass .POmegaPlus M.D →
      (∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus M.D, ⁅R, R⁆ = R) →
      (∀ k : Fin M.D.rank, Generic.IsLongestRoot M.D (Pi.single k 1)) →
      (∀ g : M.K, ⨆ i : Fin M.D.rank, rankOneRoot M.D g (Pi.single i 1) = ⊤) →
      (∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus M.D,
        Nonempty (R ≃* SL(2, GaloisField p f))) → D4Facts (GaloisField p f) := by
    intro M hM hs hp hl hg hs2
    subst hM
    exact ⟨hodd, hs, hp, hl, hs2, hg⟩
  exact key _ hM hsingle hperf hlong hgen hsl2

end Facts


section Partner

variable {F : Type} [Field F] [Finite F]

abbrev fundD4 (F : Type) [Field F] : Set (Subgroup (spinGroup (quadPlus 4 F))) :=
  Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num))

theorem D4Facts.two_ne_zero (hF : D4Facts F) : (2 : F) ≠ 0 :=
  IsFundamental.two_ne_zero_of_odd hF.odd

theorem D4Facts.eq_of_map_eq (hF : D4Facts F) {R R' : Subgroup (spinGroup (quadPlus 4 F))}
    (hR : R ∈ fundD4 F) (hR' : R' ∈ fundD4 F)
    (h : R.map (spinAction (quadPlus 4 F)) = R'.map (spinAction (quadPlus 4 F))) : R = R' :=
  eq_of_map_eq_fund hF.perf hR hR' h

theorem D4Facts.exists_frame (hF : D4Facts F) {R : Subgroup (spinGroup (quadPlus 4 F))}
    (hR : R ∈ fundD4 F) :
    ∃ fr : OFrame (quadPlus 4 F), R.map (spinAction (quadPlus 4 F)) = fr.La.range :=
  exists_frame_of_mem_fund_plus (by norm_num) hF.single hF.long hR

theorem D4Facts.theta_central (hF : D4Facts F) {R : Subgroup (spinGroup (quadPlus 4 F))}
    (hR : R ∈ fundD4 F) {fr : OFrame (quadPlus 4 F)}
    (hfr : R.map (spinAction (quadPlus 4 F)) = fr.La.range) {c : spinGroup (quadPlus 4 F)}
    (hc : c ∈ R) (hz : ∀ r ∈ R, c * r = r * c) (h1 : c ≠ 1) :
    spinAction (quadPlus 4 F) c = fr.La (-1) :=
  (map_central_eq_one_or_neg_one _ R fr hfr hc hz).resolve_left fun h =>
    h1 (spinAction_injOn_fund hF.odd (by norm_num) hF.single hF.perf hF.long hF.sl2 hR hc h)

omit [Finite F] in
theorem slB_mul_slB : slB F * slB F = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  exact mB_mul_mB

theorem D4Facts.sq_eq_of_central (hF : D4Facts F) {R : Subgroup (spinGroup (quadPlus 4 F))}
    (hR : R ∈ fundD4 F) {fr : OFrame (quadPlus 4 F)}
    (hfr : R.map (spinAction (quadPlus 4 F)) = fr.La.range) {u : spinGroup (quadPlus 4 F)}
    (hu : u ∈ R) {A : SL(2, F)} (hθ : spinAction (quadPlus 4 F) u = fr.La A) (hA : A * A = -1)
    {c : spinGroup (quadPlus 4 F)} (hc : c ∈ R) (hz : ∀ r ∈ R, c * r = r * c) (h1 : c ≠ 1) :
    u * u = c := by
  have hθc := hF.theta_central hR hfr hc hz h1
  have hmem : u * u * c⁻¹ ∈ R := R.mul_mem (R.mul_mem hu hu) (R.inv_mem hc)
  have h0 : spinAction (quadPlus 4 F) (u * u * c⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hθ, hθc, ← map_mul, hA, mul_inv_cancel]
  have := spinAction_injOn_fund hF.odd (by norm_num) hF.single hF.perf hF.long hF.sl2 hR hmem h0
  exact mul_inv_eq_one.mp this

theorem D4Facts.not_central_of_sq (hF : D4Facts F) {R : Subgroup (spinGroup (quadPlus 4 F))}
    (hR : R ∈ fundD4 F) {u c : spinGroup (quadPlus 4 F)} (hu : u ∈ R) (hc : c ∈ R)
    (hz : ∀ r ∈ R, c * r = r * c) (h1 : c ≠ 1) (hsq : u * u = c) :
    ¬ ∀ r ∈ R, u * r = r * u := by
  intro hu'
  obtain ⟨e⟩ := hF.sl2 R hR
  have hcenR : ∀ (g : spinGroup (quadPlus 4 F)) (hg : g ∈ R), (∀ r ∈ R, g * r = r * g) →
      e ⟨g, hg⟩ = 1 ∨ e ⟨g, hg⟩ = -1 := by
    intro g hg hgc
    have : (⟨g, hg⟩ : R) ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hgc y y.2).symm
    exact (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp
      ((CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e _).mp this)
  have hec : e ⟨c, hc⟩ = -1 := by
    rcases hcenR c hc hz with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm) :
        (⟨c, hc⟩ : R) = 1)) h1
    · exact h
  have hsq' : e ⟨c, hc⟩ = e ⟨u, hu⟩ * e ⟨u, hu⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hsq.symm
  rcases hcenR u hu hu' with h | h
  · rw [hec, h, one_mul] at hsq'
    exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hF.odd hsq'
  · rw [hec, h] at hsq'
    exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hF.odd (by simpa using hsq')

omit [Finite F] in
theorem one_ne_neg_of_frame (h2 : (2 : F) ≠ 0) (F₁ : OFrame (quadPlus 4 F)) :
    (1 : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) ≠ LinearEquiv.neg F := by
  intro h
  have hv : F₁.incl (1 : Matrix (Fin 2) (Fin 2) F) ≠ 0 := fun h0 => by
    have := Frame.Q_incl F₁ (1 : Matrix (Fin 2) (Fin 2) F)
    rw [h0, QuadraticMap.map_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have h1 := congrArg (fun T : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) =>
    T (F₁.incl (1 : Matrix (Fin 2) (Fin 2) F))) h
  simp only [LinearEquiv.neg_apply] at h1
  exact hv (eq_zero_of_neg_eq_self h2 h1.symm)

theorem D4Facts.exists_central (hF : D4Facts F) {R : Subgroup (spinGroup (quadPlus 4 F))}
    (hR : R ∈ fundD4 F) {fr : OFrame (quadPlus 4 F)}
    (hfr : R.map (spinAction (quadPlus 4 F)) = fr.La.range) :
    ∃ c ∈ R, (∀ r ∈ R, c * r = r * c) ∧ c ≠ 1 ∧ spinAction (quadPlus 4 F) c = fr.La (-1) := by
  have hker := ker_spinAction_le_center (quadPlus 4 F)
  obtain ⟨r, hr, hθr⟩ : fr.La (-1) ∈ R.map (spinAction (quadPlus 4 F)) := hfr ▸ ⟨-1, rfl⟩
  have hne : fr.La (-1) ≠ 1 := fun h =>
    CFSG.ClassicalInvolution.sl2_neg_one_ne_one hF.odd (fr.La_injective (by rw [h, map_one]))
  have hrcent : r ∈ Subgroup.centralizer (R : Set _) :=
    Models.Transfer.mem_centralizer_of_map hker (hF.perf R hR) (g := r) (by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, hs, rfl⟩
      have hs' : spinAction (quadPlus 4 F) s ∈ fr.La.range := hfr ▸ ⟨s, hs, rfl⟩
      obtain ⟨A, hA⟩ := hs'
      show _ * spinAction (quadPlus 4 F) r = spinAction (quadPlus 4 F) r * _
      rw [hθr, ← hA, ← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_center_iff.mp
        ((CFSG.ClassicalInvolution.mem_center_sl2_iff (-1 : SL(2, F))).mpr (Or.inr rfl)) A))
  refine ⟨r, hr, fun r' hr' => (Subgroup.mem_centralizer_iff.mp hrcent r' hr').symm, ?_, hθr⟩
  rintro rfl
  exact hne (hθr.symm.trans (map_one _))

omit [Finite F] in
theorem uB_mul_self' (F₃ : OFrame (quadPlus 4 F)) : uB (F := F) F₃ * uB (F := F) F₃ = 1 := by
  have hc : ∀ A B : SL(2, F), F₃.swap.La A * F₃.La B = F₃.La B * F₃.swap.La A := fun A B =>
    (F₃.La_comm_La_swap B A).symm
  calc uB (F := F) F₃ * uB (F := F) F₃
      = F₃.La (slB F) * (F₃.swap.La (slB F) * F₃.La (slB F)) * F₃.swap.La (slB F) := by
        simp only [uB]
        group
    _ = F₃.La (slB F) * (F₃.La (slB F) * F₃.swap.La (slB F)) * F₃.swap.La (slB F) := by
        rw [hc]
    _ = F₃.La (slB F * slB F) * F₃.swap.La (slB F * slB F) := by
        rw [map_mul, map_mul]
        group
    _ = 1 := by
        rw [slB_mul_slB, Frame.La_swap_neg_one, Frame.La_neg_one_mul_self]

theorem partner_of_opposite (hF : D4Facts F) {R₁ Ra Rb : Subgroup (spinGroup (quadPlus 4 F))}
    (h₁ : R₁ ∈ fundD4 F) (ha : Ra ∈ fundD4 F) (hb : Rb ∈ fundD4 F) (hab : Ra ≠ Rb)
    {F₁ : OFrame (quadPlus 4 F)} (hF₁ : R₁.map (spinAction (quadPlus 4 F)) = F₁.La.range)
    (ca1 : Commutes R₁ Ra) {ia ib : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)}
    (hia : IsFundSpin Ra ia) (hib : IsFundSpin Rb ib)
    (hoa : F₁.La (-1) * ia = LinearEquiv.neg F) (hob : F₁.La (-1) * ib = LinearEquiv.neg F)
    {c : spinGroup (quadPlus 4 F)} (hc : c ∈ R₁) (hcz : ∀ r ∈ R₁, c * r = r * c) (hc1 : c ≠ 1) :
    ∃ ua ∈ Ra, ∃ ub ∈ Rb, ∃ P ∈ fundD4 F, ∃ x ∈ P,
      (∀ r ∈ P, r * (ua * ub) = (ua * ub) * r) ∧
      (∀ ca ∈ Ra, (∀ r ∈ Ra, ca * r = r * ca) → ca ≠ 1 → ua * ua = ca) ∧
      (∀ cb ∈ Rb, (∀ r ∈ Rb, cb * r = r * cb) → cb ≠ 1 → ub * ub = cb) ∧
      (¬ ∀ r ∈ Ra, ua * r = r * ua) ∧ (¬ ∀ r ∈ Rb, ub * r = r * ub) ∧
      ua * ub ∉ Subgroup.center (spinGroup (quadPlus 4 F)) ∧
      (x * c * x⁻¹ * c⁻¹) ^ 4 = 1 ∧
      x * c * x⁻¹ * c⁻¹ ∉ Subgroup.center (spinGroup (quadPlus 4 F)) := by
  classical
  have h2 : (2 : F) ≠ 0 := hF.two_ne_zero
  unfold IsFundSpin at hia hib
  obtain ⟨F₃, hF₃⟩ := hF.exists_frame ha
  obtain ⟨Fb, hFb⟩ := hF.exists_frame hb
  have hia' : F₃.La (-1) = ia :=
    IsFundamental.involution_unique hF.odd (⟨F₃, hF₃, rfl⟩ : IsFundamental (quadPlus 4 F) _ _) hia
  have hib' : Fb.La (-1) = ib :=
    IsFundamental.involution_unique hF.odd (⟨Fb, hFb, rfl⟩ : IsFundamental (quadPlus 4 F) _ _) hib
  rw [← hia'] at hoa
  rw [← hib'] at hob
  have hbeq : Fb.La (-1) = F₃.La (-1) := mul_left_cancel (hob.trans hoa.symm)
  have hFb' : Rb.map (spinAction (quadPlus 4 F)) = F₃.swap.La.range := by
    rcases Frame.La_range_eq_or_eq_swap h2 hbeq with h | h
    · exact absurd (hF.eq_of_map_eq hb ha (hFb.trans (h.trans hF₃.symm))) hab.symm
    · exact hFb.trans h
  have hcent : ∀ A : SL(2, F), F₃.La (-1) * F₁.La A = F₁.La A * F₃.La (-1) := by
    intro A
    obtain ⟨r, hr, hrA⟩ : F₁.La A ∈ R₁.map (spinAction (quadPlus 4 F)) := hF₁ ▸ ⟨A, rfl⟩
    obtain ⟨s, hs, hsθ⟩ : F₃.La (-1) ∈ Ra.map (spinAction (quadPlus 4 F)) := hF₃ ▸ ⟨-1, rfl⟩
    rw [← hsθ, ← hrA, ← map_mul, ← map_mul, (ca1 r hr s hs).symm]
  have hne : F₃.La (-1) ≠ F₁.La (-1) := by
    intro h
    rw [h] at hoa
    exact one_ne_neg_of_frame h2 F₁ (by rw [← hoa, Frame.La_neg_one_mul_self])
  have horth := (Frame.orth_or_eq h2 (hcent (-1)) hcent).resolve_right hne
  have hθc := hF.theta_central h₁ hF₁ hc hcz hc1
  obtain ⟨u₃, hu₃, u₄, hu₄, P, hP, x, hxP, hθ3, hθ4, hn1, hneg, hcom, -, ht4, hnc⟩ :=
    exists_partner_spin hF.odd hF.perf h₁ F₁ F₃ hF₁ hF₃ hFb' horth hθc
  refine ⟨u₃, hu₃, u₄, hu₄, P, hP, x, hxP, hcom, ?_, ?_, ?_, ?_, ?_, ht4, hnc⟩
  · intro ca hca hz hc1'
    exact hF.sq_eq_of_central ha hF₃ hu₃ hθ3 slB_mul_slB hca hz hc1'
  · intro cb hcb hz hc1'
    obtain ⟨hFb3⟩ : Nonempty (OFrame (quadPlus 4 F)) := ⟨F₃.swap⟩
    exact hF.sq_eq_of_central hb hFb' hu₄ hθ4 slB_mul_slB hcb hz hc1'
  · intro hz
    obtain ⟨ca, hca, hz', hc1', -⟩ := hF.exists_central ha hF₃
    exact hF.not_central_of_sq ha hu₃ hca hz' hc1' (hF.sq_eq_of_central ha hF₃ hu₃ hθ3
      slB_mul_slB hca hz' hc1') hz
  · intro hz
    obtain ⟨cb, hcb, hz', hc1', -⟩ := hF.exists_central hb hFb'
    exact hF.not_central_of_sq hb hu₄ hcb hz' hc1' (hF.sq_eq_of_central hb hFb' hu₄ hθ4
      slB_mul_slB hcb hz' hc1') hz
  · intro hz
    have hmem : spinAction (quadPlus 4 F) (u₃ * u₄) ∈ elementaryGroup (quadPlus 4 F) := by
      rw [← range_spinAction_quadPlus (by norm_num)]
      exact ⟨_, rfl⟩
    let zz : ↥(elementaryGroup (quadPlus 4 F)) := ⟨_, hmem⟩
    have hzc : zz ∈ Subgroup.center ↥(elementaryGroup (quadPlus 4 F)) := by
      rw [Subgroup.mem_center_iff]
      intro u
      have hu : (u : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) ∈
          (spinAction (quadPlus 4 F)).range := by
        rw [range_spinAction_quadPlus (by norm_num)]
        exact u.2
      obtain ⟨y, hy⟩ := hu
      apply Subtype.ext
      show (u : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) *
        spinAction (quadPlus 4 F) (u₃ * u₄) =
          spinAction (quadPlus 4 F) (u₃ * u₄) *
            (u : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F))
      rw [← hy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y)]
    have hz2 : zz * zz = 1 := Subtype.ext (by
      show spinAction (quadPlus 4 F) (u₃ * u₄) * spinAction (quadPlus 4 F) (u₃ * u₄) = 1
      rw [map_mul, hθ3, hθ4]
      exact uB_mul_self' F₃)
    have hZ := CFSG.ClassicalInvolution.Models.Transfer.centerScalar_quadPlus (K := F)
      (n := 4) (by norm_num)
    rcases CFSG.ClassicalInvolution.Models.Transfer.eq_one_or_eq_neg_of_mem_center hZ hzc hz2 with
      h | h
    · exact hn1 (congrArg Subtype.val h)
    · exact hneg h

@[expose] def CliquePartner (t : StatedLieTag) {K : Type} [Group K] (D : UniversalRootDatum K)
    (R₂ R₃ R₄ : Subgroup K) (c : K) : Prop :=
  ∃ Ra Rb : Subgroup K, (Ra = R₂ ∨ Ra = R₃ ∨ Ra = R₄) ∧ (Rb = R₂ ∨ Rb = R₃ ∨ Rb = R₄) ∧
    Ra ≠ Rb ∧ ∃ ua ∈ Ra, ∃ ub ∈ Rb, ∃ P ∈ Generic.fundamentalSubgroups t D, ∃ x ∈ P,
      (∀ r ∈ P, r * (ua * ub) = (ua * ub) * r) ∧
      (∀ ca ∈ Ra, (∀ r ∈ Ra, ca * r = r * ca) → ca ≠ 1 → ua * ua = ca) ∧
      (∀ cb ∈ Rb, (∀ r ∈ Rb, cb * r = r * cb) → cb ≠ 1 → ub * ub = cb) ∧
      (¬ ∀ r ∈ Ra, ua * r = r * ua) ∧ (¬ ∀ r ∈ Rb, ub * r = r * ub) ∧
      ua * ub ∉ Subgroup.center K ∧
      (x * c * x⁻¹ * c⁻¹) ^ 4 = 1 ∧ x * c * x⁻¹ * c⁻¹ ∉ Subgroup.center K

theorem exists_clique_partner (hF : D4Facts F)
    {R₁ R₂ R₃ R₄ : Subgroup (spinGroup (quadPlus 4 F))}
    (h₁ : R₁ ∈ fundD4 F) (h₂ : R₂ ∈ fundD4 F) (h₃ : R₃ ∈ fundD4 F) (h₄ : R₄ ∈ fundD4 F)
    (h12 : R₁ ≠ R₂) (h13 : R₁ ≠ R₃) (h14 : R₁ ≠ R₄) (h23 : R₂ ≠ R₃) (h24 : R₂ ≠ R₄)
    (h34 : R₃ ≠ R₄) (c12 : Commutes R₁ R₂) (c13 : Commutes R₁ R₃) (c14 : Commutes R₁ R₄)
    {c : spinGroup (quadPlus 4 F)} (hc : c ∈ R₁) (hcz : ∀ r ∈ R₁, c * r = r * c) (hc1 : c ≠ 1) :
    CliquePartner .POmegaPlus (plusDatum 4 F (by norm_num)) R₂ R₃ R₄ c := by
  classical
  have h2 : (2 : F) ≠ 0 := hF.two_ne_zero
  obtain ⟨F₁, hF₁⟩ := hF.exists_frame h₁
  have hdich : ∀ {R : Subgroup (spinGroup (quadPlus 4 F))}, R ∈ fundD4 F → Commutes R₁ R →
      IsFundSpin R (F₁.La (-1)) ∨
        ∃ i, IsFundSpin R i ∧ F₁.La (-1) * i = LinearEquiv.neg F := by
    intro R hR hcomm
    obtain ⟨i, i', hi, hi', hdi⟩ := exists_inv_of_commutes hF.odd hF.single hF.long h₁ hR hcomm
    unfold IsFundSpin at hi
    have hi1 : F₁.La (-1) = i := IsFundamental.involution_unique hF.odd
      (⟨F₁, hF₁, rfl⟩ : IsFundamental (quadPlus 4 F) _ _) hi
    rcases hdi with h | h
    · left
      rw [hi1]
      exact h ▸ hi'
    · right
      exact ⟨i', hi', by rw [hi1]; exact h⟩
  have hsame : ∀ {R R' : Subgroup (spinGroup (quadPlus 4 F))}, R ∈ fundD4 F → R' ∈ fundD4 F →
      R ≠ R₁ → R' ≠ R₁ → R ≠ R' → IsFundSpin R (F₁.La (-1)) → IsFundSpin R' (F₁.La (-1)) →
      False := by
    intro R R' hR hR' hR1 hR'1 hRR' hi hi'
    obtain ⟨fr, hfr, hfi⟩ := hi
    obtain ⟨fr', hfr', hfi'⟩ := hi'
    have hne : ∀ {S : Subgroup (spinGroup (quadPlus 4 F))}, S ∈ fundD4 F → S ≠ R₁ →
        S.map (spinAction (quadPlus 4 F)) = F₁.La.range → False := fun hS hSR h =>
      hSR (hF.eq_of_map_eq hS h₁ (h.trans hF₁.symm))
    rcases Frame.La_range_eq_or_eq_swap h2 hfi.symm with e1 | e1
    · exact hne hR hR1 (hfr.trans e1)
    rcases Frame.La_range_eq_or_eq_swap h2 hfi'.symm with e2 | e2
    · exact hne hR' hR'1 (hfr'.trans e2)
    exact hRR' (hF.eq_of_map_eq hR hR' ((hfr.trans e1).trans (hfr'.trans e2).symm))
  have core : ∀ {Ra Rb : Subgroup (spinGroup (quadPlus 4 F))}, Ra ∈ fundD4 F → Rb ∈ fundD4 F →
      Ra ≠ Rb → Commutes R₁ Ra →
      (∃ i, IsFundSpin Ra i ∧ F₁.La (-1) * i = LinearEquiv.neg F) →
      (∃ i, IsFundSpin Rb i ∧ F₁.La (-1) * i = LinearEquiv.neg F) →
      ∃ ua ∈ Ra, ∃ ub ∈ Rb, ∃ P ∈ fundD4 F, ∃ x ∈ P,
        (∀ r ∈ P, r * (ua * ub) = (ua * ub) * r) ∧
        (∀ ca ∈ Ra, (∀ r ∈ Ra, ca * r = r * ca) → ca ≠ 1 → ua * ua = ca) ∧
        (∀ cb ∈ Rb, (∀ r ∈ Rb, cb * r = r * cb) → cb ≠ 1 → ub * ub = cb) ∧
        (¬ ∀ r ∈ Ra, ua * r = r * ua) ∧ (¬ ∀ r ∈ Rb, ub * r = r * ub) ∧
        ua * ub ∉ Subgroup.center (spinGroup (quadPlus 4 F)) ∧
        (x * c * x⁻¹ * c⁻¹) ^ 4 = 1 ∧
        x * c * x⁻¹ * c⁻¹ ∉ Subgroup.center (spinGroup (quadPlus 4 F)) := by
    rintro Ra Rb ha hb hab ca1 ⟨ia, hia, hoa⟩ ⟨ib, hib, hob⟩
    exact partner_of_opposite hF h₁ ha hb hab hF₁ ca1 hia hib hoa hob hc hcz hc1
  rcases hdich h₂ c12 with s2 | o2 <;> rcases hdich h₃ c13 with s3 | o3 <;>
    rcases hdich h₄ c14 with s4 | o4
  · exact (hsame h₂ h₃ h12.symm h13.symm h23 s2 s3).elim
  · exact (hsame h₂ h₃ h12.symm h13.symm h23 s2 s3).elim
  · exact (hsame h₂ h₄ h12.symm h14.symm h24 s2 s4).elim
  · exact ⟨R₃, R₄, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), h34, core h₃ h₄ h34 c13 o3 o4⟩
  · exact (hsame h₃ h₄ h13.symm h14.symm h34 s3 s4).elim
  · exact ⟨R₂, R₄, Or.inl rfl, Or.inr (Or.inr rfl), h24, core h₂ h₄ h24 c12 o2 o4⟩
  · exact ⟨R₂, R₃, Or.inl rfl, Or.inr (Or.inl rfl), h23, core h₂ h₃ h23 c12 o2 o3⟩
  · exact ⟨R₂, R₃, Or.inl rfl, Or.inr (Or.inl rfl), h23, core h₂ h₃ h23 c12 o2 o3⟩

end Partner

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem exists_clique_partner_of_eq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaPlus) (hn : n = 4) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₁ R₂ R₃ R₄ : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (h₁ : R₁ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (h₂ : R₂ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (h₃ : R₃ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (h₄ : R₄ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (h12 : R₁ ≠ R₂) (h13 : R₁ ≠ R₃) (h14 : R₁ ≠ R₄) (h23 : R₂ ≠ R₃) (h24 : R₂ ≠ R₄)
    (h34 : R₃ ≠ R₄) (c12 : Commutes R₁ R₂) (c13 : Commutes R₁ R₃) (c14 : Commutes R₁ R₄)
    {c : (Generic.modelUniv t n p e Fact.out).K} (hc : c ∈ R₁) (hcz : ∀ r ∈ R₁, c * r = r * c)
    (hc1 : c ≠ 1) :
    CliquePartner t (Generic.modelUniv t n p e Fact.out).D R₂ R₃ R₄ c := by
  subst ht hn he
  have hn3 : 3 ≤ 4 := by norm_num
  have hF := D4Facts.of_galoisField (p := p) (f := e) hp2 hq
  have hM : Generic.modelUniv .POmegaPlus 4 p e Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus 4 p e Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 p e Fact.out).trans (modelUniv_POmegaPlus hn3)
  have key : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ →
      ∀ R₁ R₂ R₃ R₄ : Subgroup M.K,
      R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D →
      R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D →
      R₃ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D →
      R₄ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D →
      R₁ ≠ R₂ → R₁ ≠ R₃ → R₁ ≠ R₄ → R₂ ≠ R₃ → R₂ ≠ R₄ → R₃ ≠ R₄ →
      Commutes R₁ R₂ → Commutes R₁ R₃ → Commutes R₁ R₄ → ∀ c : M.K, c ∈ R₁ →
      (∀ r ∈ R₁, c * r = r * c) → c ≠ 1 → CliquePartner .POmegaPlus M.D R₂ R₃ R₄ c := by
    intro M hM R₁ R₂ R₃ R₄ h₁ h₂ h₃ h₄ h12 h13 h14 h23 h24 h34 c12 c13 c14 c hc hcz hc1
    subst hM
    exact exists_clique_partner hF h₁ h₂ h₃ h₄ h12 h13 h14 h23 h24 h34 c12 c13 c14 hc hcz hc1
  exact key _ hM R₁ R₂ R₃ R₄ h₁ h₂ h₃ h₄ h12 h13 h14 h23 h24 h34 c12 c13 c14 c hc hcz hc1

end Model

end CFSG.ClassicalInvolution.RouteD.Exotic
