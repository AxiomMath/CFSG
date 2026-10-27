module

public import CFSG.GH74.Generic.BProg.B3.S1ThreeSplit
public import CFSG.GH74.Generic.Front.OuterModels
public import CFSG.GH74.Generic.BProg.B2.T3S1Abs
public import CFSG.GH74.Generic.S1.Exo.Glue
public import CFSG.GH74.Generic.S1.Exo.Q3Perf
public import CFSG.Milestones.OO_odd_order_solvable
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Three

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS1 CFSG.GH74.L5U5
open CFSG.GH74.Generic.S1 Subgroup
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem resCent_xa_eq_bot {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}
    (hc : Ctx21 G x K A a D J) (h3 : B1.PilotS1.QShape1Three (↥K ⧸ pPrimeCore 2 ↥K)) :
    resCent ({x, a} : Set G) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF3, ⟨eK⟩⟩ := h3
  have h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K) :=
    Or.inl ⟨F, inferInstance, inferInstance, by omega, ⟨eK⟩⟩
  obtain ⟨hxK, hAK, hxA, hCY⟩ := s1_basic hc h1
  have hax : a ≠ x := s1_a_ne_x hc h1
  have hx2 : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have ha2 : orderOf a = 2 := hc.obs.y_ord
  have haA : a ∈ A := hc.a_mem
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hc.src.2.1
  have hAsq : ∀ b ∈ A, b * b = 1 := fun b hb => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) b hb
  have hAcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc' =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨b, hb⟩ ⟨c, hc'⟩)
  have hxa_comm : x * a = a * x := hAcomm x hxA a haA
  have hax' : a ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxa_comm.symm
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  obtain ⟨z₀, hP⟩ := B1.PilotS1.grpS1_lin (F := F) (by omega)
  obtain ⟨-, -, -, hY, -, -⟩ := B1.PilotS1.shape1_data hc.hyp.gen4 hx2 hK eK hP h1
  have hKc : IsComponent (imgBar x K) := by
    obtain ⟨-, Kb, hKb, -, hmap, -⟩ := hK
    show IsComponent ((K.subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G)))))
    rw [hmap]
    exact hKb
  have hKn : (imgBar x K).Normal := normal_of_centralizer_le hKc hCY
  have haK : a ∈ K := hAK haA
  obtain ⟨hub, -, hub2⟩ := bar_facts hKC haK ha2
  have hubx : bar x a ≠ xbar x := by
    intro h
    apply hax
    refine B1.PilotS1.eq_of_proj_eq hax' hxC (hAcomm a haA x hxA) (hAsq a haA) (hAsq x hxA) ?_
    rw [← bar_of_mem hax']; exact h
  obtain ⟨Jb₁, Jb₂, hS⟩ := hY.split (bar x a) hub hub2 hubx
  obtain ⟨eKb⟩ := hat_equiv_imgBar hK
  have hsolv : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(imgBar x K)) := by
    have := CFSG.GH74.Generic.outer_solvable_statedSL4 (F := F)
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv (eKb.symm.trans eK).symm
  have hxbK : xbar x ∈ imgBar x K := by
    have h := (bar_facts hKC hxK hx2).1
    rw [bar_of_mem hxC] at h
    exact h
  have hCK : centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) ≤
      imgBar x K := fun w hw => by
    rcases hCY w hw with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxbK
  obtain ⟨e₁⟩ := hS.equiv₁
  obtain ⟨e₂⟩ := hS.equiv₂
  have hsl : Group.IsSolvable SL(2, F) := B1.PilotS1.isSolvable_sl2_three hF3
  have hJ₁s : Group.IsSolvable ↥Jb₁ :=
    Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective
  have hJ₂s : Group.IsSolvable ↥Jb₂ :=
    Group.isSolvable_of_isSolvable_injective (f := e₂.toMonoidHom) e₂.injective
  set Q : Subgroup G := resCent ({x, a} : Set G) with hQdef
  have hQperf : ⁅Q, Q⁆ = Q := resCent_perfect _
  have hQC : Q ≤ centralizer ({x, a} : Set G) := resCent_le _
  have hQx : Q ≤ centralizer ({x} : Set G) :=
    hQC.trans (Subgroup.centralizer_le (by simp))
  have hQa : Q ≤ centralizer ({a} : Set G) :=
    hQC.trans (Subgroup.centralizer_le (by simp))
  set Qb : Subgroup (CentralizerBar x) := (Q.subgroupOf (centralizer ({x} : Set G))).map (proj x)
    with hQbdef
  have hQ'perf : ⁅Q.subgroupOf (centralizer ({x} : Set G)), Q.subgroupOf (centralizer ({x} : Set G))⁆ =
      Q.subgroupOf (centralizer ({x} : Set G)) := by
    apply Subgroup.map_injective (centralizer ({x} : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hQx, hQperf]
  have hQbperf : ⁅Qb, Qb⁆ = Qb := by
    rw [hQbdef, ← Subgroup.map_commutator, hQ'perf]
  have hQbK : Qb ≤ imgBar x K := by
    have := hKn
    have h := CFSG.GH74.Generic.BProg.B2.T3S1.goodSub_le_sup_centralizer (X := CentralizerBar x)
      (K := imgBar x K) (T := False) hsolv (fun h => h.elim) Qb (Or.inl hQbperf)
    rwa [sup_eq_left.2 hCK] at h
  have hQbA : ∀ q ∈ Qb, q * bar x a = bar x a * q := by
    rintro _ ⟨q, hq, rfl⟩
    have hqa : (q : G) * a = a * (q : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hQa (Subgroup.mem_subgroupOf.1 hq))
    rw [bar_of_mem hax', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hqa
  have hQbJ : Qb ≤ Jb₁ ⊔ Jb₂ := by
    rw [← hQbperf]
    refine (Subgroup.commutator_le).2 fun g hg h hh => ?_
    exact hS.comm g (hQbK hg) h (hQbK hh) (hQbA g hg) (hQbA h hh)
  have hQbs : Group.IsSolvable ↥Qb :=
    CFSG.GH74.Generic.S1.Exo.isSolvable_of_le_sup_of_commute hS.commute hQbJ
  have hQb1 : Qb = ⊥ := by
    by_contra hne
    have : Nontrivial ↥Qb := (Subgroup.nontrivial_iff_ne_bot Qb).mpr hne
    have : Group.IsPerfect ↥Qb := Subgroup.isPerfect_iff.mpr hQbperf
    exact Group.IsPerfect.not_isSolvable ↥Qb hQbs
  have hQO : Q.subgroupOf (centralizer ({x} : Set G)) ≤ pPrimeCore 2 ↥(centralizer ({x} : Set G)) := by
    intro q hq
    have h1 : proj x q ∈ Qb := ⟨q, hq, rfl⟩
    rw [hQb1, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff q).1 h1
  have hQodd : Odd (Nat.card ↥Q) := by
    have hc1 : Nat.card ↥Q = Nat.card ↥(Q.subgroupOf (centralizer ({x} : Set G))) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQx).toEquiv).symm
    have hc2 : Nat.card ↥(Q.subgroupOf (centralizer ({x} : Set G))) ∣
        Nat.card ↥(pPrimeCore 2 ↥(centralizer ({x} : Set G))) := Subgroup.card_dvd_of_le hQO
    have hc3 : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥(centralizer ({x} : Set G)))) :=
      CFSG.pPrimeCore_coprime_card
    rw [hc1]
    exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right hc2 hc3)
  have hQs : Group.IsSolvable ↥Q := CFSG.Milestones.odd_order_solvable hQodd
  by_contra hne
  have : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.mpr hQperf
  exact Group.IsPerfect.not_isSolvable ↥Q hQs

theorem s1three_perfectFree {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}
    (hc : Ctx21 G x K A a D J) (h3 : B1.PilotS1.QShape1Three (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∀ P : Subgroup (CentralizerBar a), ⁅P, P⁆ = P →
      P ≤ centralizer ({bar a x} : Set (CentralizerBar a)) → P = ⊥ := by
  intro P hP hPc
  have h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K) := by
    obtain ⟨F, _, _, hF3, e⟩ := h3
    exact Or.inl ⟨F, inferInstance, inferInstance, by omega, e⟩
  obtain ⟨-, -, hxA, -⟩ := s1_basic hc h1
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hc.src.2.1
  have hxa_comm : x * a = a * x :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨x, hxA⟩ ⟨a, hc.a_mem⟩)
  have hxa : x ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxa_comm
  have hxx : x * x = 1 := by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) x hxA
  have hle := CFSG.GH74.Generic.S1.Exo.perfect_le_barSub_resCent hxa hxx hP
    (by rwa [bar_of_mem hxa] at hPc)
  rw [resCent_xa_eq_bot hc h3] at hle
  have hb : S45.barSub a (⊥ : Subgroup G) = ⊥ := by
    rw [S45.barSub, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hb] at hle
  exact le_bot_iff.1 hle

end S1Three

end CFSG.GH74.Generic.BProg.B3
