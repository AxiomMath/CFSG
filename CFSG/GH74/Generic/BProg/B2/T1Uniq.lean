module

public import CFSG.GH74.Generic.BProg.B2.Prop111
import CFSG.GH74.Generic.BProg.B2.Thm2Comp
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC2
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC3
import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14
public import CFSG.GH74.Generic.BProg.B2.Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

namespace T1Uniq

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

theorem mk_mem_centralizer_barIn {H : Subgroup G} (hHM : GLS.IsSubnormalIn H M) {y : G} (hyM : y ∈ M)
    (hy : y ∈ centralizerSection H (pPrimeCoreOf 2 H)) :
    QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨y, hyM⟩ : ↥M) ∈
      centralizer ((barIn M H : Subgroup (Mbar M)) : Set (Mbar M)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨h, hh, rfl⟩
  have hhH : (h : G) ∈ H := Subgroup.mem_subgroupOf.1 hh
  have hc : ⁅(h : G), y⁆ ∈ pPrimeCoreOf 2 M := Th2.pPrimeCoreOf_le_of_subnormal hHM (hy.2.2 _ hhH)
  obtain ⟨m, hm, hmeq⟩ := hc
  have hm' : m = ⁅h, (⟨y, hyM⟩ : ↥M)⁆ := Subtype.ext (by
    rw [show (m : G) = ⁅(h : G), y⁆ from hmeq]; simp [commutatorElement_def])
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⁅h, (⟨y, hyM⟩ : ↥M)⁆ = 1 := by
    rw [← hm']; exact (QuotientGroup.eq_one_iff _).2 hm
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem odd_orderOf_of_mk_eq_one {y : G} (hyM : y ∈ M)
    (h : QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨y, hyM⟩ : ↥M) = 1) : Odd (orderOf y) := by
  have hmem : (⟨y, hyM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
    Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have h1 : orderOf (⟨⟨y, hyM⟩, hmem⟩ : ↥(pPrimeCore 2 ↥M)) ∣ Nat.card ↥(pPrimeCore 2 ↥M) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨⟨y, hyM⟩, hmem⟩ : ↥(pPrimeCore 2 ↥M)) = orderOf y := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
  rw [h2] at h1
  exact hodd.of_dvd_nat h1

theorem eq_one_of_mem_sup_of_commute {Y : Type} [Group Y] {L₁ L₂ : Subgroup Y}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h1 : center ↥L₁ = ⊥) (h2 : center ↥L₂ = ⊥) {z : Y}
    (hz : z ∈ L₁ ⊔ L₂) (hzc : ∀ w ∈ L₁ ⊔ L₂, w * z = z * w) : z = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (Thm2AssemblyC3.mem_sup_iff hc).1 hz
  have ha1 : a = 1 := by
    have hmem : (⟨a, ha⟩ : ↥L₁) ∈ center ↥L₁ := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have e1 := hzc l (Subgroup.mem_sup_left l.2)
      have e2 := hc l l.2 b hb
      show (l : Y) * a = a * l
      have : (l : Y) * a * b = a * l * b := by
        calc (l : Y) * a * b = l * (a * b) := by group
          _ = a * b * l := e1
          _ = a * (b * l) := by group
          _ = a * (l * b) := by rw [e2]
          _ = a * l * b := by group
      exact mul_right_cancel this
    rw [h1, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hb1 : b = 1 := by
    have hmem : (⟨b, hb⟩ : ↥L₂) ∈ center ↥L₂ := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have e1 := hzc l (Subgroup.mem_sup_right l.2)
      have e2 := hc a ha l l.2
      show (l : Y) * b = b * l
      have : a * (l * b) = a * (b * l) := by
        calc a * (l * b) = (a * l) * b := by group
          _ = (l * a) * b := by rw [e2]
          _ = l * (a * b) := by group
          _ = a * b * l := e1
          _ = a * (b * l) := by group
      exact mul_left_cancel this
    rw [h2, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  rw [ha1, hb1, mul_one]

theorem preuniq_of_core
    (hs : Stage2Setup G x K A M P Q) {H : Subgroup G} (h1 : Stage2Concl1Core x K M Q H)
    (h2 : Stage2Concl2 M) :
    M ≠ ⊤ ∧ ∀ y ∈ M, orderOf y = 2 → y ∈ centralizerSection H (pPrimeCoreOf 2 H) →
      centralizer ({y} : Set G) ≤ M := by
  refine ⟨hs.maxM.1, fun y hyM hy2 hyC => ?_⟩
  have hbar := mk_mem_centralizer_barIn h1.H_min.2.1 hyM hyC
  rcases h1.H_tri with hc1 | ⟨hF, hsimple⟩ |
      ⟨hF, hx, L₁, L₂, hL₁, hL₂, hne, hs₁, hs₂, hsup, hconj, hall⟩
  ·
    have hX : y ∈ CMbar M K :=
      (Thm2Comp.mem_CMbar_iff h1.K_le ⟨y, hyM⟩).2 (by
        show _ ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M))
        rw [← hc1]; exact hbar)
    have hQ := isSylowOf_CMbar_of_c1 hs h1 hc1
    have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
    obtain ⟨c, hcX, hcQ⟩ := Stage2.Final.Thm6.L20.exists_mem_conj_into_sylow hQ hX hyy
    have hcM : c ∈ M := hcX.1
    have hy2' : orderOf (c * y * c⁻¹) = 2 := by
      rw [show c * y * c⁻¹ = (MulAut.conj c) y from rfl, MulEquiv.orderOf_eq]
      exact hy2
    have hCM := centralizer_le_M_of_mem_Q hs h1.K_le h1.Q_le h2 hcQ hy2'
    intro g hg
    have hg' : c * g * c⁻¹ ∈ centralizer ({c * y * c⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      calc c * g * c⁻¹ * (c * y * c⁻¹) = c * (g * y) * c⁻¹ := by group
        _ = c * (y * g) * c⁻¹ := by rw [hg]
        _ = c * y * c⁻¹ * (c * g * c⁻¹) := by group
    have h3 := hCM hg'
    have e : g = c⁻¹ * (c * g * c⁻¹) * c := by group
    rw [e]
    exact M.mul_mem (M.mul_mem (M.inv_mem hcM) h3) hcM
  ·
    exfalso
    have hnab := Thm2AssemblyC2.barIn_nonabelian_of_simple hs h1.K_le hF hsimple
    have hcen : center ↥(barIn M H) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥(barIn M H)) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        have ha : a ∈ center ↥(barIn M H) := by rw [h]; exact Subgroup.mem_top a
        exact hab ((Subgroup.mem_center_iff.1 ha b).symm)
    set ybar := QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨y, hyM⟩ : ↥M) with hybar
    have hyH : ybar ∈ barIn M H := by
      rw [hF]
      refine CFSG.centralizer_generalizedFitting_le (Mbar M) ?_
      rw [← hF]; exact hbar
    have hmem : (⟨ybar, hyH⟩ : ↥(barIn M H)) ∈ center ↥(barIn M H) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hbar w w.2)
    rw [hcen, Subgroup.mem_bot] at hmem
    have h1' : ybar = 1 := congrArg Subtype.val hmem
    have := odd_orderOf_of_mk_eq_one hyM h1'
    rw [hy2] at this
    exact absurd this (by decide)
  ·
    exfalso
    have hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
      intro a ha b hb
      have hle : L₁ ≤ centralizer (L₂ : Set (Mbar M)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1
          ((CFSG.LocalCores.distinct_components_commute hL₁ hL₂).resolve_left hne)
      exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm
    set ybar := QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨y, hyM⟩ : ↥M) with hybar
    have hyH : ybar ∈ barIn M H := by
      rw [hF]
      refine CFSG.centralizer_generalizedFitting_le (Mbar M) ?_
      rw [← hF]; exact hbar
    rw [hsup] at hyH hbar
    have h1' : ybar = 1 :=
      eq_one_of_mem_sup_of_commute hc (Thm2AssemblyC3.center_eq_bot_of_simple_quasisimple hL₁.1 hs₁)
        (Thm2AssemblyC3.center_eq_bot_of_simple_quasisimple hL₂.1 hs₂) hyH
        (fun w hw => Subgroup.mem_centralizer_iff.1 hbar w hw)
    have := odd_orderOf_of_mk_eq_one hyM h1'
    rw [hy2] at this
    exact absurd this (by decide)

end T1Uniq

end CFSG.GH74.Generic.BProg.B2
