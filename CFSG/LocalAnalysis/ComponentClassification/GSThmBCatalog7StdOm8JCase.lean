module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Cases
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Indep

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup Module
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

attribute [local instance] finite_linearEquiv

variable {H : Type} [Group H] [Finite H] {G : Subgroup H} [G.Normal] {K : Type} [Field K]
  [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {Θ : G ≃* projectiveDerived Q} {a b : H}

theorem j_caseA {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = r ^ e) (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K V = 8)
    (Da : InvData G Q Θ a) (Db : InvData G Q Θ b) (hnsb : ¬ IsSquare (Db.c : K)) (β : Kˣ)
    (hβ : (Da.c : K) = (β : K) ^ 2) (J : Subgroup H) (hJC : J ≤ centralizer ({a} : Set H))
    (hJG : J ≤ G) (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H))))
    (hb : b ∈ UnbalancedLayer.coreActionKernel J) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hJm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) (hpf : p ^ f = (r ^ e) ^ 2) :
    False := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hr.eq_two_or_odd'.resolve_left hr2).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hre : 3 ≤ r ^ e := by
    have h3 : 3 ≤ r := by
      have := hr.two_le
      omega
    exact le_trans h3 (Nat.le_self_pow (by omega) r)
  obtain ⟨W, W', ι, hcompl, hnd, hnd', hι⟩ := caseA_data hr hr2 he hK hQ hdim Da β hβ
  obtain ⟨M, hM, hMJ, hMε⟩ := corr_down Da ι J hJC hJG hJ
  subst hMJ
  obtain ⟨U, U', ψ, hcU, hndU, -, hψ, L, hL, hML⟩ :=
    left_normal_form Da ι hcompl hnd hnd' hι M hMε
  have hLq := (isComponent_of_pComponent hodd hndU hL).1
  obtain ⟨hJq, ⟨eJ⟩⟩ := quotient_of_left Da ψ M L hLq hML
  have hJZ := lieModel_center_of_pPrimeCore hJq hJm
  have hU3 : 3 ≤ finrank K U := by
    by_contra h
    exact CatalogueBOrthogonal.orthogonal_small_no_pComponent _ h2 hndU (by omega) 2 L hL
  have hmis : Blueprint.LieModel (L ⧸ center L) .PSL 2 r e → False := by
    intro h1
    have h3 := pow_eq_of_lieModel_psl_two hp hp2 hr hr2 hJZ
      (LieType.CurtisTits.lieModel_of_mulEquiv eJ.symm h1)
    rw [hpf] at h3
    nlinarith
  by_cases h3 : finrank K U = 3
  · exact hmis (pComponent_three hr hr2 he hK hndU h3 hL)
  by_cases h4s : finrank K U = 4 ∧
      ∃ S : Submodule K U, finrank K S = 2 ∧ ∀ x ∈ S, (Q.comp U.subtype) x = 0
  · exact hmis (pComponent_split_four hr hr2 he hK hndU h4s.1 h4s.2 hL)
  have hLc : L = commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)) := by
    rcases lt_or_ge (finrank K U) 5 with hlt | hge
    · have h4 : finrank K U = 4 := by omega
      exact (pComponent_nonsplit_four hr hr2 he hK hndU h4 (fun hS => h4s ⟨h4, hS⟩) hL).1
    · exact pComponent_five_le hodd hndU hge hL
  have hperf : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect hM)
  have hcent := commute_of_mem_coreActionKernel hJq hJm hb
  have hA := commute_of_centralizes Da Db M hperf (fun m hm => hcent _ (mem_map_of_mem _ hm))
  apply false_of_commuting ψ hψ hodd hndU hcU (by omega) Db.A.toLinearMap hnsb
    (fun v => Db.hsq v)
  intro h hh v
  obtain ⟨m, hm, hmh⟩ := exists_lift Da ψ M (by rw [hML, hLc]) h hh
  rw [← hmh, epsT_symm_val Da ψ m]
  exact hA m hm v

theorem j_caseB {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = r ^ e) (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K V = 8)
    (hnp : ¬ IsPlusType Q) (Da : InvData G Q Θ a) (hnsa : ¬ IsSquare (Da.c : K))
    (J : Subgroup H) (hJC : J ≤ centralizer ({a} : Set H)) (hJG : J ≤ G)
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H)))) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hJm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    (hpf : p ^ f = (r ^ e) ^ 2) : False := by
  have hre : 3 ≤ r ^ e := by
    have h3 : 3 ≤ r := by
      have := hr.two_le
      omega
    exact le_trans h3 (Nat.le_self_pow (by omega) r)
  obtain ⟨T, _, _, ι, hT⟩ := caseB_data hr hr2 he hK hQ hdim hnp Da hnsa
  obtain ⟨M, hM, hMJ, hMε⟩ := corr_down Da ι J hJC hJG hJ
  subst hMJ
  obtain ⟨hq, hLM⟩ := hT _ hMε
  obtain ⟨hqJ, ⟨eJ⟩⟩ := centerQuotient_equiv Da ι M hq
  have h3 := pow_eq_of_lieModel_psl_two hp hp2 hr hr2 (lieModel_center_of_pPrimeCore hqJ hJm)
    (LieType.CurtisTits.lieModel_of_mulEquiv eJ.symm hLM)
  have h4 : (r ^ e) ^ 2 = ((r ^ e) ^ 2) ^ 2 := by
    calc (r ^ e) ^ 2 = p ^ f := hpf.symm
      _ = r ^ (2 * (2 * e)) := h3
      _ = ((r ^ e) ^ 2) ^ 2 := by ring
  have h9 : 9 ≤ (r ^ e) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hre 2)
  nlinarith

theorem j_analysis {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = r ^ e) (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K V = 8)
    (hnp : ¬ IsPlusType Q) (Da : InvData G Q Θ a) (Db : InvData G Q Θ b)
    (hnsb : ¬ IsSquare (Db.c : K)) (J : Subgroup H) (hJC : J ≤ centralizer ({a} : Set H))
    (hJG : J ≤ G) (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H))))
    (hb : b ∈ UnbalancedLayer.coreActionKernel J) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hJm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) (hpf : p ^ f = (r ^ e) ^ 2) :
    False := by
  by_cases hsq : IsSquare (Da.c : K)
  · obtain ⟨β, hβ⟩ := hsq
    have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hβ
      exact Units.ne_zero _ hβ
    exact j_caseA hr hr2 he hK hQ hdim Da Db hnsb (Units.mk0 β hβ0)
      (by rw [Units.val_mk0, hβ, sq]) J hJC hJG hJ hb hp hp2 hJm hpf
  · exact j_caseB hr hr2 he hK hQ hdim hnp Da hsq J hJC hJG hJ hp hp2 hJm hpf

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
