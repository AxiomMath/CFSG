module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourLift
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourPair
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.RouteD.NonClassical (d4Node d4Frame d4Node_mem)
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Spin

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem diagSL2_neg_one : diagSL2 (-1 : Fˣ) = (-1 : SL(2, F)) := by
  apply Subtype.ext
  rw [coe_diagSL2, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] noncomputable def cNode (F : Type) [Field F] (k : Fin 4) : spinGroup (quadPlus 4 F) :=
  rankOneD F (by norm_num : 3 ≤ 4) k (-1)

omit [Finite F] in
theorem spinAction_cNode (k : Fin 4) :
    spinAction (quadPlus 4 F) (cNode F k) = (d4Frame F k).La (-1) :=
  congrArg (fun φ => φ (-1 : SL(2, F)))
    (spinAction_comp_longSL2 (plusFrame 4 F (by norm_num)) (rootIdxD_ne 4 (by omega) k) true
      (rootSignD 4 k))

omit [Finite F] in
theorem cNode_eq_torusD (k : Fin 4) :
    cNode F k = torusD F (by norm_num : 3 ≤ 4) k (-1) := by
  rw [torusD_apply, cNode, diagSL2_neg_one]

omit [Finite F] in
theorem commute_cNode (j k : Fin 4) : cNode F j * cNode F k = cNode F k * cNode F j := by
  rw [cNode_eq_torusD, cNode_eq_torusD]
  exact commute_torusD F (by norm_num) j k (-1) (-1)

omit [Finite F] in
theorem cNode_mem (k : Fin 4) : cNode F k ∈ d4Node F k :=
  PlusCT.rankOneD_mem_rankOne (by norm_num) k (-1)

omit [Finite F] in
theorem cNode_central (k : Fin 4) : ∀ r ∈ d4Node F k, cNode F k * r = r * cNode F k := by
  intro r hr
  have hr' : r ∈ (rankOneD F (by norm_num : 3 ≤ 4) k).range := by
    rw [← PlusCT.rankOne_plusRootGroup]
    exact hr
  obtain ⟨M, rfl⟩ := hr'
  rw [cNode, ← map_mul, ← map_mul]
  congr 1
  exact (Subgroup.mem_center_iff.mp
    ((CFSG.ClassicalInvolution.mem_center_sl2_iff (-1 : SL(2, F))).mpr (Or.inr rfl)) M).symm

theorem cNode_ne_one (hodd : Odd (Nat.card F)) (k : Fin 4) : cNode F k ≠ 1 := by
  intro h
  have := spinAction_cNode (F := F) k
  rw [h, map_one] at this
  exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd
    ((d4Frame F k).La_injective (by rw [← this, map_one]))

theorem D4Facts.eq_cNode_of_central (hF : D4Facts F) (k : Fin 4) {c' : spinGroup (quadPlus 4 F)}
    (hc' : c' ∈ d4Node F k) (hz : ∀ r ∈ d4Node F k, c' * r = r * c') (h1 : c' ≠ 1) :
    c' = cNode F k := by
  have hθ := hF.theta_central (d4Node_mem k) (NonClassical.map_rankOne_d4 F k) hc' hz h1
  have hmem : c' * (cNode F k)⁻¹ ∈ d4Node F k :=
    (d4Node F k).mul_mem hc' ((d4Node F k).inv_mem (cNode_mem k))
  have h0 : spinAction (quadPlus 4 F) (c' * (cNode F k)⁻¹) = 1 := by
    rw [map_mul, map_inv, hθ, spinAction_cNode, mul_inv_cancel]
  exact mul_inv_eq_one.mp (spinAction_injOn_fund hF.odd (by norm_num) hF.single hF.perf hF.long
    hF.sl2 (d4Node_mem k) hmem h0)

omit [Finite F] in
theorem rankOneRoot_one_eq (k : Fin 4) :
    rankOneRoot (plusDatum 4 F (by norm_num)) 1 (Pi.single k 1) = d4Node F k := by
  ext y
  simp [NonClassical.d4Node, rankOne, rankOneRoot]

end Spin

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem exists_nodes_of_eq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaPlus) (hn : n = 4) (he : e = f) :
    ∃ (R : Fin 4 → Subgroup (Generic.modelUniv t n p e Fact.out).K)
      (c : Fin 4 → (Generic.modelUniv t n p e Fact.out).K),
      (∀ k, R k ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D) ∧
      (∀ k, c k ∈ R k) ∧ (∀ k, ∀ r ∈ R k, c k * r = r * c k) ∧ (∀ k, c k ≠ 1) ∧
      (∀ k, ∀ c' ∈ R k, (∀ r ∈ R k, c' * r = r * c') → c' ≠ 1 → c' = c k) ∧
      (∀ j k, c j * c k = c k * c j) ∧ (⨆ k, R k) = ⊤ := by
  subst ht hn he
  have hn3 : 3 ≤ 4 := by norm_num
  have hF := D4Facts.of_galoisField (p := p) (f := e) hp2 hq
  have hM : Generic.modelUniv .POmegaPlus 4 p e Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus 4 p e Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 p e Fact.out).trans (modelUniv_POmegaPlus hn3)
  have key : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ →
      ∃ (R : Fin 4 → Subgroup M.K) (c : Fin 4 → M.K),
        (∀ k, R k ∈ Generic.fundamentalSubgroups .POmegaPlus M.D) ∧
        (∀ k, c k ∈ R k) ∧ (∀ k, ∀ r ∈ R k, c k * r = r * c k) ∧ (∀ k, c k ≠ 1) ∧
        (∀ k, ∀ c' ∈ R k, (∀ r ∈ R k, c' * r = r * c') → c' ≠ 1 → c' = c k) ∧
        (∀ j k, c j * c k = c k * c j) ∧ (⨆ k, R k) = ⊤ := by
    intro M hM
    subst hM
    refine ⟨fun k => d4Node (GaloisField p e) k, fun k => cNode (GaloisField p e) k,
      fun k => d4Node_mem k, fun k => cNode_mem k, fun k => cNode_central k,
      fun k => cNode_ne_one hF.odd k, fun k c' hc' hz h1 => hF.eq_cNode_of_central k hc' hz h1,
      fun j k => commute_cNode j k, ?_⟩
    have := hF.gen 1
    simp only [rankOneRoot_one_eq] at this
    exact this
  exact key _ hM

end Model

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G}
  {z : G}

omit [IsSimpleGroup G] in
theorem exists_node_members (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f 4 .POmegaPlus 4 (conjClass K) z) {N₀ : Subgroup G}
    (hN₀ : N₀ ∈ conjClass K) :
    ∃ (Mk : Fin 4 → Subgroup G) (zk : Fin 4 → G),
      (∀ k, Mk k ∈ outerSet (conjClass K) N₀) ∧ (∀ k, IsClassicalMember p f (Mk k) (zk k)) ∧
      (∀ j k, zk j * zk k = zk k * zk j) ∧
      ∀ L ∈ outerSet (conjClass K) N₀, L ≤ ⨆ k, Mk k := by
  classical
  set Ω := conjClass K with hΩdef
  have hΩ : InClass p f Ω := S.inClass
  have hex : ExactMembers Ω := S.exact
  have hf : 0 < f := routeD_f_pos S
  obtain ⟨w, hw, hP1, D, i₁, hcard, ht, hr, hrest⟩ := exists_D4At S hloc hN₀
  have hout := outerSet_eq_compMembers S.odd hf S.five hΩ hex hw hN₀ hP1
    (single_class_of_mem hN₀) D ht hr hrest
  have hq4 : 4 ≤ p ^ f := by
    have := S.five
    omega
  have hperf := D.fundPerfect S.odd hq4
    (trialityD4_vacuous D (by decide : StatedLieTag.POmegaPlus ≠ .trialityD4) ht hrest) i₁
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h (by decide)
  have hsc := fundamentalSingleClass_of_ne D i₁ (by rw [ht]; decide) (by rw [ht]; decide)
  obtain ⟨R, c, hRf, hcR, hcz, hc1, huniq, hcomm, hgen⟩ :=
    exists_nodes_of_eq S.odd S.five ht hr hexp
  choose M hM using fun k => exists_corr_right hΩ D hsc (hRf k)
  have hMout : ∀ k, M k ∈ outerSet Ω N₀ := fun k => by
    rw [hout]
    exact ⟨(hM k).1, (hM k).2.2 ▸ Subgroup.map_le_range _ _⟩
  choose z' hz' using fun k => hΩ.classical (M k) (hM k).1.1
  have hzY : ∀ k, z' k ∈ locLayer Ω w := fun k => le_centralizingLayer (hM k).1 (hz' k).mem
  have hzc : ∀ k, D.hom i₁ (c k) = locMk Ω w ⟨z' k, hzY k⟩ := by
    intro k
    obtain ⟨c', hc'R, hc'z, hc'img, hc'1⟩ := exists_central_preimage hperf (hM k) (hz' k) (hzY k)
    rw [← hc'img, huniq k c' hc'R hc'z hc'1]
  refine ⟨M, z', hMout, hz', ?_, ?_⟩
  · intro j k
    have hsq : ∀ m, z' m * z' m = 1 := fun m => mul_self_of_isClassicalMember (hz' m)
    set Zj : ↥(locLayer Ω w) := ⟨z' j, hzY j⟩
    set Zk : ↥(locLayer Ω w) := ⟨z' k, hzY k⟩
    have hmk : locMk Ω w (Zj * Zk * Zj⁻¹ * Zk⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      show locMk Ω w ⟨z' j, hzY j⟩ * locMk Ω w ⟨z' k, hzY k⟩ * (locMk Ω w ⟨z' j, hzY j⟩)⁻¹ *
        (locMk Ω w ⟨z' k, hzY k⟩)⁻¹ = 1
      rw [← hzc j, ← hzc k, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
        hcomm j k]
      group
      exact map_one _
    have hO : Zj * Zk * Zj⁻¹ * Zk⁻¹ ∈ classicalInvolutionOddCore ↥(locLayer Ω w) :=
      (QuotientGroup.eq_one_iff _).mp hmk
    have hcent := hP1 hO
    have hZj : Zj * Zj = 1 := Subtype.ext (hsq j)
    have hZk : Zk * Zk = 1 := Subtype.ext (hsq k)
    have hZji : Zj⁻¹ = Zj := inv_eq_of_mul_eq_one_right hZj
    have hZki : Zk⁻¹ = Zk := inv_eq_of_mul_eq_one_right hZk
    set A : ↥(locLayer Ω w) := Zj * Zk * Zj⁻¹ * Zk⁻¹ with hA
    have hAA : A * A = 1 := by
      have h1 : Zj * A * Zj⁻¹ = A⁻¹ := by
        rw [hA, hZji, hZki]
        calc Zj * (Zj * Zk * Zj * Zk) * Zj = (Zj * Zj) * Zk * Zj * Zk * Zj := by group
          _ = Zk * Zj * Zk * Zj := by rw [hZj, one_mul]
          _ = (Zj * Zk * Zj * Zk)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hZji, hZki]
            group
      have h2 : Zj * A * Zj⁻¹ = A := by
        rw [Subgroup.mem_center_iff.mp hcent Zj]
        group
      rw [h2] at h1
      exact mul_eq_one_iff_eq_inv.mpr h1
    have hA1 := eq_one_of_mem_oddCore_of_sq hO hAA
    have hcomm' : Zj * Zk = Zk * Zj := by
      have h3 : (Zj * Zk) * (Zj * Zk) = 1 := by
        have h4 := hA1
        rw [hA, hZji, hZki] at h4
        simpa [mul_assoc] using h4
      calc Zj * Zk = (Zj * Zk)⁻¹ := eq_inv_of_mul_eq_one_left h3
        _ = Zk * Zj := by rw [mul_inv_rev, hZki, hZji]
    exact congrArg Subtype.val hcomm'
  · intro L hL
    exact le_iSup_of_model_generates hΩ hP1 M R hM hgen (hout ▸ hL)

end Members

end CFSG.ClassicalInvolution.RouteD.Exotic
