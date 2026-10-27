module

public import CFSG.ClassicalInvolution.Asc77.AscBSD12

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSE

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.BSC.BSD
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


@[expose] def IsConjTwin (C : XCtx p f (𝒞 K) z) (b : Fin C.D.card) (m : G) (N : Subgroup G) :
    Prop :=
  N ∈ tqMembers (𝒞 K) z ∧ IsClassicalMember p f N m ∧
    ∃ R ∈ fundamentalSubgroups (C.D.tag b) (compModel C.D b).D,
      modOdd z (exactCore z N) = R.map (C.psi b) ∧
        ∃ r ∈ R, ∃ hm : m ∈ Subgroup.centralizer ({z} : Set G),
          C.psi b r = oddQuotMk z ⟨m, hm⟩

theorem exists_conj_twins_complete {C : XCtx p f (𝒞 K) z}
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2)) :
    ∃ (g : G) (N : {j : Fin C.D.card // j ≠ b} → Subgroup G), Function.Injective N ∧
      (∀ j, IsConjTwin C b (g⁻¹ * z * g) (N j)) ∧
      ∀ T ∈ 𝒞 K, IsClassicalMember p f T z → ∃ j, conjSub g⁻¹ T = N j := by
  obtain ⟨mb⟩ := exists_compMem C b
  obtain ⟨g, -, hg⟩ := exists_conj_of_compMem C mb
  let me : ∀ j : {j : Fin C.D.card // j ≠ b}, CompMem C j.1 := fun j =>
    Classical.choice (exists_compMem C j.1)
  have hA1 : ∀ j : {j : Fin C.D.card // j ≠ b}, C.D.tag j.1 = .PSL ∧ C.D.rank j.1 = 2 :=
    fun j => (nbar_eq_of_A1 C hno hb j.2).1
  have hnb : ∀ j : {j : Fin C.D.card // j ≠ b}, (me j).nbar = zbar z := fun j =>
    (nbar_eq_of_A1 C hno hb j.2).2 (me j)
  have hcl : ∀ j : {j : Fin C.D.card // j ≠ b}, IsClassicalMember p f (me j).N z ∧
      modOdd z (me j).N = (C.psi j.1).range := fun j =>
    classical_of_nbar_eq C (hA1 j) (me j) (hnb j)
  refine ⟨g, fun j => conjSub g⁻¹ (me j).N, ?_, fun j => ?_, ?_⟩
  · intro j j' hjj'
    by_contra hne
    have hne' : j.1 ≠ j'.1 := fun h => hne (Subtype.ext h)
    exact twin_ne_twin hne' (hA1 j) (hA1 j') (me j) (hnb j) (me j') (hnb j')
      (BSD.conjSub_inj g⁻¹ hjj')
  · obtain ⟨hT'tq, hT'cl, R, hR, himg, r, hrR, hm, hr⟩ :=
      exists_fund_conj_twin hno hb mb hg (me j).hN.1 (hcl j).1 fun y hy =>
        nb_comm_of_range j.2 mb ((hcl j).2 ▸ hy)
    exact ⟨hT'tq, hT'cl, R, hR, himg, r, hrR, hm, hr⟩
  · intro T hT hTz
    obtain ⟨j, hj, hjT⟩ := C.exists_A1_of_member hT hTz
    have hjb : j ≠ b := fun h => hb (h ▸ hj)
    refine ⟨⟨j, hjb⟩, ?_⟩
    have hTtq : T ∈ tqMembers (𝒞 K) z := mem_tqMembers_of_isClassicalMember hT hTz
    have hTe : exactCore z T = T :=
      exactCore_eq_self hTz.perfect (RouteD.le_centralizer_of_isClassicalMember hTz)
    have hMe : exactCore z (me ⟨j, hjb⟩).N = (me ⟨j, hjb⟩).N :=
      exactCore_eq_self (hcl ⟨j, hjb⟩).1.perfect
        (RouteD.le_centralizer_of_isClassicalMember (hcl ⟨j, hjb⟩).1)
    have hEq : T = (me ⟨j, hjb⟩).N :=
      BSD.eq_of_fund_eq C.hz2 hTtq (me ⟨j, hjb⟩).hN hTz (hcl ⟨j, hjb⟩).1
        (by rw [hTe, hMe, hjT, (hcl ⟨j, hjb⟩).2])
    rw [hEq]

theorem exists_conj_twins {C : XCtx p f (𝒞 K) z}
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2)) :
    ∃ (N : {j : Fin C.D.card // j ≠ b} → Subgroup G) (m : G), Function.Injective N ∧
      ∀ j, IsConjTwin C b m (N j) := by
  obtain ⟨g, N, hinj, hN, -⟩ := exists_conj_twins_complete hno hb
  exact ⟨N, g⁻¹ * z * g, hinj, hN⟩

namespace IsConjTwin

variable {C : XCtx p f (𝒞 K) z} {b : Fin C.D.card} {m : G} {N N' : Subgroup G}

theorem eq_of_fund_eq (h : IsConjTwin C b m N) (h' : IsConjTwin C b m N')
    {R R' : Subgroup (compModel C.D b).K}
    (hR : modOdd z (exactCore z N) = R.map (C.psi b))
    (hR' : modOdd z (exactCore z N') = R'.map (C.psi b)) (hRR : R = R') : N = N' :=
  BSD.eq_of_fund_eq C.hz2 h.1 h'.1 h.2.1 h'.2.1 (by rw [hR, hR', hRR])

end IsConjTwin

end CFSG.ClassicalInvolution.Asc77.BSC.BSE
