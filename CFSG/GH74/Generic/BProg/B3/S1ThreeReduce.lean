module

public import CFSG.GH74.Generic.BProg.B3.S1ThreeSplit
public import CFSG.GH74.Generic.S1.Exo.Q3HReduce

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Three

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
open CFSG.GH74.GLS.C3.Layer1 Subgroup
open CFSG.GH74.Filter.ClassicalOdd (Q8)

section Abstract

variable {H : Type} [Group H] [Finite H]

theorem centralizes_of_bal {Jb : Subgroup H} (hJ : IsComponent Jb) (φ : Q8 →* H)
    (hbal : (∀ q, φ q ∈ pCore 2 H) ∨ ∃ N : Subgroup H, IsComponent N ∧ ∀ q, φ q ∈ N) :
    (∀ q, φ q ∈ Jb) ∨ ∀ q, ∀ j ∈ Jb, φ q * j = j * φ q := by
  rcases hbal with hO | ⟨N, hN, hNφ⟩
  · right
    intro q j hj
    have h1 := CFSG.GH74.Generic.S1.Exo.pCore_two_le_centralizer_layer (hO q)
    have hjL : j ∈ layer H := CFSG.LocalCores.component_le_layer hJ hj
    exact (Subgroup.mem_centralizer_iff.1 h1 j hjL).symm
  · by_cases hNJ : N = Jb
    · left
      intro q
      rw [← hNJ]
      exact hNφ q
    · right
      intro q j hj
      have hc := (CFSG.LocalCores.distinct_components_commute hN hJ).resolve_left hNJ
      have hle : N ≤ centralizer (Jb : Set H) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
      exact (Subgroup.mem_centralizer_iff.1 (hle (hNφ q)) j hj).symm

theorem q3_reduce {Jb : Subgroup H} (hJ : IsComponent Jb) {c : H} (hc : ∀ h : H, h * c = c * h)
    (φA φB : Q8 →* H)
    (hcy : ¬ ∀ j ∈ Jb, c * φB (QuaternionGroup.a 2) * j = j * (c * φB (QuaternionGroup.a 2)))
    (hbalA : (∀ q, φA q ∈ pCore 2 H) ∨ ∃ N : Subgroup H, IsComponent N ∧ ∀ q, φA q ∈ N)
    (hbalB : (∀ q, φB q ∈ pCore 2 H) ∨ ∃ N : Subgroup H, IsComponent N ∧ ∀ q, φB q ∈ N) :
    (∀ q, φB q ∈ Jb) ∧ ((∀ q, φA q ∈ Jb) ∨ ∀ q, ∀ j ∈ Jb, φA q * j = j * φA q) := by
  refine ⟨?_, centralizes_of_bal hJ φA hbalA⟩
  rcases centralizes_of_bal hJ φB hbalB with h | h
  · exact h
  · exfalso
    apply hcy
    intro j hj
    have h1 := h (QuaternionGroup.a 2) j hj
    calc c * φB (QuaternionGroup.a 2) * j = c * (φB (QuaternionGroup.a 2) * j) := mul_assoc _ _ _
      _ = c * (j * φB (QuaternionGroup.a 2)) := by rw [h1]
      _ = (c * j) * φB (QuaternionGroup.a 2) := (mul_assoc _ _ _).symm
      _ = (j * c) * φB (QuaternionGroup.a 2) := by rw [hc j]
      _ = j * (c * φB (QuaternionGroup.a 2)) := mul_assoc _ _ _

end Abstract

section Glue

variable {G : Type} [Group G]

theorem bar_self_central (a : G) : ∀ h : CentralizerBar a, h * bar a a = bar a a * h := by
  intro h
  have haC : a ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(centralizer ({a} : Set G))) h
  rw [bar_of_mem haC]
  show proj a g * proj a ⟨a, haC⟩ = proj a ⟨a, haC⟩ * proj a g
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)

theorem bar_mul_bar {a x : G} (haa : a * a = 1) (hxa : x * a = a * x) :
    bar a a * bar a (x * a) = bar a x := by
  have haC : a ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxC : x ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxa
  have hxaC : x * a ∈ centralizer ({a} : Set G) := Subgroup.mul_mem _ hxC haC
  rw [bar_of_mem haC, bar_of_mem hxaC, bar_of_mem hxC, ← map_mul]
  congr 1
  apply Subtype.ext
  show a * (x * a) = x
  rw [hxa, ← mul_assoc, haa, one_mul]

variable [Finite G]


theorem xbar_not_cent {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G} (hc : Ctx21 G x K A a D J)
    (h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ¬ ∀ j ∈ PumpCalc.bar a J, bar a x * j = j * bar a x := by
  intro h
  obtain ⟨-, -, hxA, -⟩ := s1_basic hc h1
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hc.src.2.1
  have hAcomm : x * a = a * x :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨x, hxA⟩ ⟨a, hc.a_mem⟩)
  have hxa : x ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hAcomm
  have hmem := ObsPump.mem_cSec_of_bar_comm hc.obs.comp hxa (by
    intro l hl
    have := h l hl
    rw [bar_of_mem hxa] at this
    exact this)
  rcases hc.cA_eq x hxA hmem with h2 | h2
  · have hx2 : orderOf x = 2 := hc.circ.1.1.1.1
    rw [h2, orderOf_one] at hx2
    omega
  · exact s1_a_ne_x hc h1 h2.symm

theorem s1three_reduce {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G} (hc : Ctx21 G x K A a D J)
    (h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) {φA φB : Q8 →* CentralizerBar a}
    (hd : S1ThreeData x a φA φB) :
    (∀ q, φB q ∈ PumpCalc.bar a J) ∧ ((∀ q, φA q ∈ PumpCalc.bar a J) ∨
      ∀ q, ∀ j ∈ PumpCalc.bar a J, φA q * j = j * φA q) := by
  obtain ⟨-, -, hxA, -⟩ := s1_basic hc h1
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hc.src.2.1
  have hAcomm : x * a = a * x :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨x, hxA⟩ ⟨a, hc.a_mem⟩)
  have ha2 : orderOf a = 2 := hc.obs.y_ord
  have haa : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rw [ha2, pow_two] at h
    exact h
  refine q3_reduce (PumpCalc.isComponent_bar hc.obs.comp) (bar_self_central a) φA φB ?_ hd.balA hd.balB
  rw [hd.zB, bar_mul_bar haa hAcomm]
  exact xbar_not_cent hc h1

end Glue

end S1Three

end CFSG.GH74.Generic.BProg.B3
