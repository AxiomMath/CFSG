module

public import CFSG.ClassicalInvolution.Asc77.AscBSD3

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (ModelFund)

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

theorem conjSub_inj {G : Type} [Group G] (g : G) {A B : Subgroup G}
    (h : conjSub g A = conjSub g B) : A = B := by
  have := congrArg (conjSub g⁻¹) h
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

variable {p f : ℕ} [Fact p.Prime]


theorem fund_eq_of_central_ratio_three {t : LTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) (ht : t = .PSL ∨ t = .PSU) (hn : n = 3)
    (hadm : StatedLieAdmissible t n p e) {R R' : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ ModelFund p t n e) (hR' : R' ∈ ModelFund p t n e)
    {r r' : (modelUniv t n p e Fact.out).K} (hr : IsInvIn R r) (hr' : IsInvIn R' r')
    (hc : r * r'⁻¹ ∈ Subgroup.center (modelUniv t n p e Fact.out).K) : R = R' := by
  subst hn
  rcases ht with rfl | rfl
  · exact fund_eq_of_central_ratio_psl_three hp2 hR hR' hr hr' hc
  · exact fund_eq_of_central_ratio_psu_three hp2 hq hadm hR hR' hr hr' hc

theorem bootNoM3Twin : BootNoM3Twin p f := by
  intro G _ _ _ K z hS D b hbtag hbrank
  by_contra hcard
  have hcard3 : 2 < D.card := by omega
  have hno := noFuzzyFrame hS
  let C := NDB.Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  have hbtag' : C.D.tag b = .PSL ∨ C.D.tag b = .PSU := hbtag
  have hbrank' : C.D.rank b = 3 := hbrank
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := fun h => by omega
  obtain ⟨j₀, hj₀, hK₀⟩ := C.exists_A1_of_K
  have hj₀b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  obtain ⟨e, hej, heb⟩ := Fin.exists_ne_and_ne_of_two_lt j₀ b hcard3
  obtain ⟨he, hall⟩ := nbar_eq_of_A1 C hno hb heb
  obtain ⟨me⟩ := exists_compMem C e
  have hme := hall me
  obtain ⟨hTcl, hTmod⟩ := classical_of_nbar_eq C he me hme
  have hTK : me.N ≠ C.K := twin_ne_K C hj₀ hK₀ hej he me hme
  obtain ⟨mb⟩ := exists_compMem C b
  obtain ⟨g, -, hg⟩ := exists_conj_of_compMem C mb
  have hKr : modOdd z C.K = (C.psi j₀).range := by rw [← hK₀, C.exactCore_K]
  obtain ⟨hK'tq, hK'cl, R₁, hR₁, himg₁, r₁, hr₁R, hm₁, hr₁⟩ :=
    exists_fund_conj_twin hno hb mb hg C.hK C.K_cl fun y hy =>
      nb_comm_of_range hj₀b mb (hKr ▸ hy)
  obtain ⟨hT'tq, hT'cl, R₂, hR₂, himg₂, r₂, hr₂R, hm₂, hr₂⟩ :=
    exists_fund_conj_twin hno hb mb hg me.hN.1 hTcl fun y hy =>
      nb_comm_of_range heb mb (hTmod ▸ hy)
  have hmsq : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 :=
    (isCentralInvolution_of_isClassicalMember hK'cl).sq
  have hm1 : g⁻¹ * z * g ≠ 1 := (isCentralInvolution_of_isClassicalMember hK'cl).ne_one
  have hi₁ := isInvIn_of_psi_eq hb hR₁ hr₁R hm₁ hmsq hm1 hr₁
  have hi₂ := isInvIn_of_psi_eq hb hR₂ hr₂R hm₂ hmsq hm1 hr₂
  have hcen : r₁ * r₂⁻¹ ∈ Subgroup.center (compModel C.D b).K := by
    refine C.psi_ker b ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hr₁, hr₂, mul_inv_cancel]
  have hexp : C.D.exp b = f := C.exp_eq b (fun h => by
    rcases hbtag' with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide))
  have hq : 5 ≤ p ^ C.D.exp b := by rw [hexp]; exact hS.five
  have hRR : R₁ = R₂ :=
    fund_eq_of_central_ratio_three hS.odd hq hbtag' hbrank' (C.D.admissible b) hR₁ hR₂ hi₁ hi₂
      hcen
  have hEq : conjSub g⁻¹ C.K = conjSub g⁻¹ me.N :=
    eq_of_fund_eq C.hz2 hK'tq hT'tq hK'cl hT'cl (by rw [himg₁, himg₂, hRR])
  exact hTK (conjSub_inj g⁻¹ hEq).symm

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
