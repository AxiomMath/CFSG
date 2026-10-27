module

public import CFSG.Quasithin.H13.A6S1372L76N3b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1357
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Oe2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative Matrix commutatorElement

namespace Setting4

open CFSG.Open

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem exists_O2L1_comm_not_mem_QH_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hNS : ¬ LieModel G .PSp 3 2 1) (hhat : ¬ IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    (hL1K : S.L1 ≤ K)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1) :
    ∃ o ∈ pCoreOf 2 S.L1, (S.cL1 hhat : G) * o * (S.cL1 hhat : G)⁻¹ * o⁻¹ ∉ pCoreOf 2 H := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSL
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  set g := S.cL1 hhat with hgdef
  have hgL1 : (g : G) ∈ S.L1 := S.cL1_mem hhat
  have hgX : (g : G) ∈ S.X1375 := by
    rw [S.X1375_of_not_hat hhat]
    exact hgL1
  have hg : S.frame.ρ g = swap 0 1 * swap 1 2 := S.cL1_rho hhat
  have hg3 : (g : G) ^ 3 = 1 := S.cL1_cube hhat
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : S.L1 ≤ H := hL1K.trans hKH
  have hgH : (g : G) ∈ H := hL1H hgL1
  have hF91 := S.hypF91_F4 hNS h13315 h1356two hH
  obtain ⟨a, P, v₂, ha, hP, hv₂, -, -, hP2, hPodd, hPv, -, ha2, hv⟩ :=
    S.exists_odd_config_of_F4 hH hK rfl h139 h37 h38 h13315 hgX hg
  have hmemK : ∀ (k : G) (hk : k ∈ K), A6Mod.secAct hHU hHV ⟨k, hKH hk⟩ ∈
      autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
    fun k hk => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩

  have hQ1 : ∀ (q : G) (hq : q ∈ pCoreOf 2 H), A6Mod.secAct hHU hHV ⟨q, pCoreOf_le 2 H hq⟩ = 1 := by
    intro q hq
    refine MulEquiv.ext fun w => ?_
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ w
    rw [A6Mod.secAct_secMk, MulAut.one_apply]
    apply secMk_eq_of_mem_V1
    rw [Setup.rho_apply_coe]
    exact KeyData.comm_QH_mem hF91 hq u.2

  have haY : a ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    rw [ha]
    exact hmemK g (hL1K hgL1)
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← map_pow]
    have : (⟨g, hgH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this, map_one]

  set O : Set (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :=
    {f | ∃ (o : G) (ho : o ∈ pCoreOf 2 S.L1),
      f = A6Mod.secAct hHU hHV ⟨o, hL1H (pCoreOf_le 2 S.L1 ho)⟩} with hOdef
  have hOY : O ⊆ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    rintro f ⟨o, ho, rfl⟩
    exact hmemK o (hL1K (pCoreOf_le 2 _ ho))
  have hOv : ∀ f ∈ O, f v₂ = v₂ ∧ f (a v₂) = a v₂ := by
    rintro f ⟨o, ho, rfl⟩
    rw [hv₂, ha, A6Mod.secAct_secMk, A6Mod.secAct_secMk, A6Mod.secAct_secMk]
    constructor
    · apply secMk_eq_of_mem_V1
      rw [Setup.rho_apply_coe]
      exact S.comm_O2L1_V3 ho S.v2_mem_V3
    · apply secMk_eq_of_mem_V1
      rw [Setup.rho_apply_coe, Setup.rho_apply_coe]
      exact S.comm_O2L1_V3 ho (S.conj_v2_mem_V3 hg)
  have hOa : ∀ f ∈ O, f * a = a * f := by
    rintro f ⟨o, ho, rfl⟩
    have hoH : o ∈ H := hL1H (pCoreOf_le 2 S.L1 ho)
    have h2 := hQ1 _ (hcon o ho)
    have e : (⟨(g : G) * o * (g : G)⁻¹ * o⁻¹, pCoreOf_le 2 H (hcon o ho)⟩ : ↥H) =
        ⁅(⟨g, hgH⟩ : ↥H), ⟨o, hoH⟩⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    rw [ha]
    exact h2.symm
  have hPn : ∀ p ∈ P, ∃ i : ℤ, ∃ f ∈ O, p * a * p⁻¹ = a ^ i * f := by
    rw [hP]
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T ⊓ K := ht
    have hx : (t : G) * g * (t : G)⁻¹ ∈ S.L1 :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 ht'.1) g).mp hgL1
    rw [ha]
    rcases S.L1_decomp hhat hx with h | h | h <;> try rw [← hgdef] at h
    · refine ⟨0, _, ⟨_, h, rfl⟩, ?_⟩
      rw [zpow_zero, one_mul, ← map_inv, ← map_mul, ← map_mul]
      rfl
    · refine ⟨-2, _, ⟨_, h, rfl⟩, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, ← map_zpow, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      group
    · refine ⟨-1, _, ⟨_, h, rfl⟩, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, ← map_zpow, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      group
  exact A6L76N3.false_of_natSL32 hF2 hπ haY ha3 hP2 hPodd hPv ha2 hv hOY hOv hOa hPn

end Setting4

end CFSG.Quasithin.H13.A6
