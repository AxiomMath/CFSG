module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.PCentralLayerGLA
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultCover
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open

theorem exists_isComponentOf_dvd_card_center {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C : Subgroup G} {z : G} (hzC : z ∈ C) (hcent : ∀ g ∈ C, g * z = z * g)
    (hzo : orderOf z = p) {P : Subgroup G} (hPC : P ≤ C)
    (hP : Nat.card P = p ^ (Nat.card C).factorization p)
    (hZ : ∀ c ∈ P, (∀ g ∈ P, c * g = g * c) → c ∈ Subgroup.zpowers z)
    (hO : GLAPPrimeCoreOf p C = ⊥) {J : Subgroup G} (hJ : CFSG.Open.IsComponentOf J C) :
    ∃ J' : Subgroup G, CFSG.Open.IsComponentOf J' C ∧ p ∣ Nat.card (Subgroup.center ↥J') := by
  have hJC : J ≤ C := hJ.1
  have hcomp : CFSG.Assembly.IsComponentOf J C := CFSG.Assembly.isComponentOf_iff_open.2 hJ
  have hK : CFSG.IsComponent (J.subgroupOf C) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJC).1 hcomp
  have hzo' : orderOf (⟨z, hzC⟩ : C) = p := (Subgroup.orderOf_mk z hzC).trans hzo
  have hzc : (⟨z, hzC⟩ : C) ∈ Subgroup.center C :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcent g g.2)
  have hP' : Nat.card (P.subgroupOf C) = p ^ (Nat.card C).factorization p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv).trans hP
  have hZ' : ∀ c ∈ P.subgroupOf C, (∀ g ∈ P.subgroupOf C, c * g = g * c) →
      c ∈ Subgroup.zpowers (⟨z, hzC⟩ : C) := by
    intro c hc hcomm
    have hcP : (c : G) ∈ P := hc
    have h1 := hZ (c : G) hcP fun g hg =>
      congrArg Subtype.val (hcomm ⟨g, hPC hg⟩ (show (⟨g, hPC hg⟩ : C) ∈ P.subgroupOf C from hg))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨K', hK', hdvd⟩ := PCentralLayer.exists_component_dvd_card_center hp hzo' hzc hP' hZ'
    (PCentralLayer.pPrimeCore_eq_bot_of_glaPPrimeCoreOf hO) hK
  have hle : K'.map C.subtype ≤ C := Subgroup.map_subtype_le K'
  refine ⟨K'.map C.subtype, CFSG.Assembly.isComponentOf_iff_open.1
    ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle).2
      (by
        have : (K'.map C.subtype).subgroupOf C = K' :=
          Subgroup.comap_map_eq_self_of_injective C.subtype_injective K'
        rwa [this])), ?_⟩
  have e := Subgroup.centerCongr (K'.equivMapOfInjective C.subtype C.subtype_injective)
  rwa [← Nat.card_congr e.toEquiv]

theorem nine_dvd_index_center {J : Type*} [Group J] [Finite J] (hJ : commutator J = ⊤)
    (h3 : 3 ∣ Nat.card (Subgroup.center J)) : 9 ∣ (Subgroup.center J).index := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center J) 3 h3
  have hu' : orderOf (u : J) = 3 := by rw [Subgroup.orderOf_coe]; exact hu
  have huc : (u : J) ∈ Subgroup.center J := u.2
  by_contra h9
  obtain ⟨P⟩ : Nonempty (Sylow 3 J) := inferInstance
  have hperf : Group.IsPerfect J := ⟨hJ⟩
  have hu3 : (u : J) ^ (3 ^ 1) = 1 := by rw [pow_one, ← hu']; exact pow_orderOf_eq_one _
  have hmem : (u : J) ∈ ⁅(P : Subgroup J), (P : Subgroup J)⁆ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult.central_mem_commutator_sylow hperf P huc ⟨1, hu3⟩
  let f : (P : Subgroup J) →* J ⧸ Subgroup.center J :=
    (QuotientGroup.mk' (Subgroup.center J)).comp (P : Subgroup J).subtype
  have hRp : IsPGroup 3 f.range := P.isPGroup'.of_surjective f.rangeRestrict
    f.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hRp.exists_card_eq
  have hkdvd : 3 ^ k ∣ (Subgroup.center J).index := by
    rw [Subgroup.index_eq_card, ← hk]
    exact Subgroup.card_subgroup_dvd_card f.range
  have hk1 : k ≤ 1 := by
    by_contra hk2
    exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hkdvd)
  haveI : IsCyclic f.range := by
    interval_cases k
    · haveI : Subsingleton f.range :=
        Finite.card_le_one_iff_subsingleton.1 (by rw [hk]; norm_num)
      infer_instance
    · exact isCyclic_of_prime_card (p := 3) (by simpa using hk)
  have hker : f.rangeRestrict.ker ≤ Subgroup.center (P : Subgroup J) := by
    intro x hx
    have hx1 : f x = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      simpa using this
    have hxc : (x : J) ∈ Subgroup.center J := by
      simpa [f, QuotientGroup.eq_one_iff] using hx1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 hxc (g : J)))
  have hcomm : ∀ a b : (P : Subgroup J), a * b = b * a := fun a b =>
    (commGroupOfCyclicCenterQuotient f.rangeRestrict hker).mul_comm a b
  have hPc : (P : Subgroup J) ≤ Subgroup.centralizer ((P : Subgroup J) : Set J) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hcomm ⟨y, hy⟩ ⟨x, hx⟩)
  have hbot : ⁅(P : Subgroup J), (P : Subgroup J)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 hPc
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hu'
  exact absurd hu' (by norm_num)

end CFSG.HardMathSupport.Dickson.I271
