module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinLift
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Stmt
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.ModelFacts.Orth15SylowFrame
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
import CFSG.ClassicalInvolution.Balance.WeakFrameExistsBasic
public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Cases
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.Balance.WeakFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)
open scoped commutatorElement

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

section Basic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem XCtx.z_not_mem_map_fund (C : XCtx p f Ω z) (j : Fin C.D.card)
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) :
    oddQuotMk z ⟨z, XCtx.hzC z⟩ ∉ R.map (C.psi j) := by
  intro hmem
  have hzC := XCtx.hzC z
  obtain ⟨r, hrR, hr⟩ := hmem
  have hr1 : r = 1 := by
    refine CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p (C.D.tag j) (C.D.rank j)
      (C.D.exp j) (C.D.isFundTag j) (C.D.admissible j) hj R hR r hrR fun y => C.psi_ker j ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hr]
    have := oddQuotMk_central hzC (C.psi j y)
    calc oddQuotMk z ⟨z, hzC⟩ * C.psi j y * (oddQuotMk z ⟨z, hzC⟩)⁻¹ * (C.psi j y)⁻¹
        = (C.psi j y * oddQuotMk z ⟨z, hzC⟩) * (oddQuotMk z ⟨z, hzC⟩)⁻¹ * (C.psi j y)⁻¹ := by
          rw [this]
      _ = 1 := by group
  rw [hr1, map_one] at hr
  exact C.hKz.ne_one (congrArg Subtype.val
    (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) hr.symm))

namespace TwinShapeCtxCore

variable (C : TwinShapeCtxCore p f Ω z)

include C

theorem listed_not_A1 : ¬ (C.D.tag C.i₁ = .PSL ∧ C.D.rank C.i₁ = 2) := by
  rintro ⟨h1, h2⟩
  rcases C.listed with (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) | h
  · rw [h1] at h
    cases h
  · rw [h2] at h
    cases h
  all_goals (rw [h1] at h; cases h)

end TwinShapeCtxCore

namespace TwinShapeCtx

variable (C : TwinShapeCtx p f Ω z)

include C

theorem listed_not_A1 : ¬ (C.D.tag C.i₁ = .PSL ∧ C.D.rank C.i₁ = 2) := by
  rintro ⟨h1, h2⟩
  rcases C.listed with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · rw [h1] at h
    cases h
  · rw [h2] at h
    cases h
  all_goals (rw [h1] at h; cases h)

end TwinShapeCtx

end Basic

section FrameCore

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : TwinShapeCtxCore p f Ω z} (L : TwinLiftCore C)

namespace TwinLiftCore

theorem tbar_mem : oddQuotMk z ⟨L.t, L.ht⟩ ∈ (C.psi C.i₁).range := by
  have := oddQuotMk_mem_modOdd (C.involution_mem_exactCore L.hJ L.hJt) L.ht
  rw [L.hJimg] at this
  obtain ⟨r, -, hr⟩ := this
  exact ⟨r, hr⟩

theorem t_ne_z : L.t ≠ z := by
  intro h
  have hmem := oddQuotMk_mem_modOdd (C.involution_mem_exactCore L.hJ L.hJt) L.ht
  rw [L.hJimg] at hmem
  apply XCtx.z_not_mem_map_fund C.toXCtx C.i₁ C.listed_not_A1 L.hR₁
  have : (⟨L.t, L.ht⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = ⟨z, XCtx.hzC z⟩ :=
    Subtype.ext h
  rwa [this] at hmem

theorem T₁_ne_K₁ (S : C.Spec) : L.T₁ ≠ L.K₁ := fun h =>
  C.rng_ne S (by rw [← L.hK₁img, ← L.hT₁img, h])

theorem frameData (S : C.Spec) : TwinFrameData Ω L.K₁ L.T₁ z L.u L.J L.t where
  mem := L.hK₁
  hz := L.hK₁z
  hK' := ⟨L.hT₁, z, L.hK₁z, L.hT₁z⟩
  hne := L.T₁_ne_K₁ S
  hu := L.hu_mem
  hu2 := L.hu2
  hu1 := L.hu1
  huz := L.huz
  hJ := ⟨L.hJ.1, fun M hM => by
    obtain ⟨hMΩ, w, hwK, hwM⟩ := hM
    have hwz : w = z := (L.hK₁z.eq hwK).symm
    subst hwz
    have hne : L.J ≠ M := by
      intro hJM
      rw [← hJM] at hwM
      exact L.t_ne_z ((ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt).eq hwM)
    exact mem_omegaNbr_of_trivialOnQuot C.hp C.hq C.hΩ hMΩ hwM L.hJ.1 hne L.hJ.2⟩
  ht := ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt
  htu := L.hut

theorem B_le_centralizer :
    Subgroup.closure ({z, L.u, L.t} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  exacts [XCtx.hzC x, L.hu, L.ht]

theorem z_mem_B : z ∈ Subgroup.closure ({z, L.u, L.t} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem u_mem_B : L.u ∈ Subgroup.closure ({z, L.u, L.t} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem t_mem_B : L.t ∈ Subgroup.closure ({z, L.u, L.t} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem t_mem_exactLayer : L.t ∈ exactLayer Ω z :=
  exactCore_le_exactLayer L.hJ (C.involution_mem_exactCore L.hJ L.hJt)

theorem le_exactLayer_of_isClassicalMember {N : Subgroup G} (hNΩ : N ∈ Ω)
    (hN : IsClassicalMember p f N z) : N ≤ exactLayer Ω z := by
  have hKtq : N ∈ tqMembers Ω z :=
    ⟨hNΩ, mem_trivialOnQuot_of_le_centralizer (le_centralizer_of_isClassicalMember hN)⟩
  have h := exactCore_le_exactLayer hKtq
  rwa [exactCore_eq_self hN.perfect (le_centralizer_of_isClassicalMember hN)] at h

theorem u_mem_exactLayer : L.u ∈ exactLayer Ω z := by
  have hK := le_exactLayer_of_isClassicalMember L.hK₁
    (isClassicalMember_of_twin C.hΩ L.hK₁ L.hK₁z)
  have hT := le_exactLayer_of_isClassicalMember L.hT₁
    (isClassicalMember_of_twin C.hΩ L.hT₁ L.hT₁z)
  exact (sup_le hK hT) L.hu_mem

theorem B_le_exactLayer :
    Subgroup.closure ({z, L.u, L.t} : Set G) ≤ exactLayer Ω z := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact C.z_mem_exactLayer
  · exact L.u_mem_exactLayer
  · exact L.t_mem_exactLayer

theorem u_mem_normalizer
    (hset : TwinFrameSettingCore p f Ω L.K₁ L.T₁ L.J z L.u L.t) :
    L.u ∈ Subgroup.normalizer (L.J : Set G) := by
  obtain ⟨R, R', hRsyl, hR'syl, -, hRt, hR't, x, hx, y, hy, -, -, hxy⟩ :=
    hset.exists_sylow_frame
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt
  have hJK : L.J ≠ L.K₁ := by
    intro h
    rw [h] at hUt
    exact L.t_ne_z (hUt.eq L.hK₁z)
  have hJT : L.J ≠ L.T₁ := by
    intro h
    rw [h] at hUt
    exact L.t_ne_z (hUt.eq L.hT₁z)
  have hRN : R ≤ Subgroup.normalizer (L.J : Set G) :=
    C.hΩ.le_normalizer_of_le_centralizer C.hp C.hq L.hJ.1 L.hK₁ hJK hUt hRsyl.1 hRsyl.2.1
      (by
        have := C.hΩ.eight_le_of_mem_RSet C.hp (mem_RSet_of_isSylow2In L.hK₁ hRsyl)
        omega)
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hRt r hr))
  have hR'N : R' ≤ Subgroup.normalizer (L.J : Set G) :=
    C.hΩ.le_normalizer_of_le_centralizer C.hp C.hq L.hJ.1 L.hT₁ hJT hUt hR'syl.1 hR'syl.2.1
      (by
        have := C.hΩ.eight_le_of_mem_RSet C.hp (mem_RSet_of_isSylow2In L.hT₁ hR'syl)
        omega)
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hR't r hr))
  rw [← hxy]
  exact mul_mem (hRN hx) (hR'N hy)

theorem u_mem_trivialOnQuot
    (hset : TwinFrameSettingCore p f Ω L.K₁ L.T₁ L.J z L.u L.t) : L.u ∈ trivialOnQuot L.J := by
  have huN := L.u_mem_normalizer hset
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := C.hc2
  refine ⟨huN, fun w hw => ?_⟩
  obtain ⟨i, hi, n, hn, hwin⟩ := exactCore_cover L.hJt hc2 L.hJ.2 w hw
  have hiJ : i ∈ L.J := exactCore_le_left z L.J hi
  have hiC : i ∈ Subgroup.centralizer ({z} : Set G) := exactCore_le_centralizer z L.J hi
  have hconjE : L.u * z * L.u⁻¹ = z := conj_eq_of_mem_centralizer_singleton L.hu
  have hJfix : conjSub L.u L.J = L.J := mem_normalizer_iff_conjSub_eq.mp huN
  have hEfix : conjSub L.u (exactCore z L.J) = exactCore z L.J := by
    have := exactCore_conjSub L.u z L.J
    rw [hconjE, hJfix] at this
    exact this.symm
  have hA : L.u * i * L.u⁻¹ * i⁻¹ ∈ oddCoreIn L.J := by
    have h1 : L.u * i * L.u⁻¹ ∈ exactCore z L.J := by
      have := conj_mem_conjSub (n := L.u) hi
      rwa [hEfix] at this
    have hAE : L.u * i * L.u⁻¹ * i⁻¹ ∈ exactCore z L.J := mul_mem h1 (inv_mem hi)
    have hAC : L.u * i * L.u⁻¹ * i⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem (mul_mem (mul_mem L.hu hiC) (inv_mem L.hu)) (inv_mem hiC)
    have hmem : oddQuotMk z ⟨i, hiC⟩ ∈ (C.psi C.i₁).range := by
      have := oddQuotMk_mem_modOdd hi hiC
      rw [L.hJimg] at this
      obtain ⟨r, -, hr⟩ := this
      exact ⟨r, hr⟩
    have hcomm := L.hu_comm _ hmem
    have h1' : oddQuotMk z ⟨L.u * i * L.u⁻¹ * i⁻¹, hAC⟩ = 1 := by
      have e : (⟨L.u * i * L.u⁻¹ * i⁻¹, hAC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
          ⟨L.u, L.hu⟩ * ⟨i, hiC⟩ * ⟨L.u, L.hu⟩⁻¹ * ⟨i, hiC⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hOC : L.u * i * L.u⁻¹ * i⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
      ⟨_, oddQuotMk_eq_one_iff.mp h1', rfl⟩
    have h2 := inf_oddCoreIn_le (exactCore_le_centralizer z L.J) ⟨hAE, hOC⟩
    rw [oddCoreIn_exactCore L.hJt hc2 L.hJ.2] at h2
    exact h2.2
  have hQ : oddCoreIn L.J ≤ L.J := oddCoreIn_le L.J
  have hunq : L.u * n * L.u⁻¹ ∈ oddCoreIn L.J := conj_mem_oddCoreIn_of_mem_normalizer huN hn
  have hB : L.u * n * L.u⁻¹ * n⁻¹ ∈ oddCoreIn L.J := mul_mem hunq (inv_mem hn)
  have hiB : i * (L.u * n * L.u⁻¹ * n⁻¹) * i⁻¹ ∈ oddCoreIn L.J := conj_mem_oddCoreIn hiJ hB
  rw [hwin, commutatorElement_def]
  have e : L.u * (i * n) * L.u⁻¹ * (i * n)⁻¹ =
      (L.u * i * L.u⁻¹ * i⁻¹) * (i * (L.u * n * L.u⁻¹ * n⁻¹) * i⁻¹) := by group
  rw [e]
  exact mul_mem hA hiB

theorem B_le_trivialOnQuot
    (hset : TwinFrameSettingCore p f Ω L.K₁ L.T₁ L.J z L.u L.t) :
    Subgroup.closure ({z, L.u, L.t} : Set G) ≤ trivialOnQuot L.J := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact L.hJ.2
  · exact L.u_mem_trivialOnQuot hset
  · exact trivialOnQuot_of_isUniqueInvolution C.hp C.hq C.hΩ L.hJ.1
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt)

end TwinLiftCore

end FrameCore

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : TwinShapeCtx p f Ω z} (L : TwinLift C)

namespace TwinLift

theorem tbar_mem : oddQuotMk z ⟨L.t, L.ht⟩ ∈ (C.psi C.i₁).range := L.toCore.tbar_mem

theorem t_ne_z : L.t ≠ z := L.toCore.t_ne_z

theorem T₁_ne_K₁ (S : C.Spec) : L.T₁ ≠ L.K₁ := L.toCore.T₁_ne_K₁ S.toCore

theorem frameData (S : C.Spec) : TwinFrameData Ω L.K₁ L.T₁ z L.u L.J L.t :=
  L.toCore.frameData S.toCore

theorem B_le_centralizer :
    Subgroup.closure ({z, L.u, L.t} : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
  L.toCore.B_le_centralizer

theorem z_mem_B : z ∈ Subgroup.closure ({z, L.u, L.t} : Set G) := L.toCore.z_mem_B

theorem u_mem_B : L.u ∈ Subgroup.closure ({z, L.u, L.t} : Set G) := L.toCore.u_mem_B

theorem t_mem_B : L.t ∈ Subgroup.closure ({z, L.u, L.t} : Set G) := L.toCore.t_mem_B

theorem t_mem_exactLayer : L.t ∈ exactLayer Ω z := L.toCore.t_mem_exactLayer

theorem le_exactLayer_of_isClassicalMember {N : Subgroup G} (hNΩ : N ∈ Ω)
    (hN : IsClassicalMember p f N z) : N ≤ exactLayer Ω z := by
  have hKtq : N ∈ tqMembers Ω z :=
    ⟨hNΩ, mem_trivialOnQuot_of_le_centralizer (le_centralizer_of_isClassicalMember hN)⟩
  have h := exactCore_le_exactLayer hKtq
  rwa [exactCore_eq_self hN.perfect (le_centralizer_of_isClassicalMember hN)] at h

theorem u_mem_exactLayer : L.u ∈ exactLayer Ω z := L.toCore.u_mem_exactLayer

theorem B_le_exactLayer :
    Subgroup.closure ({z, L.u, L.t} : Set G) ≤ exactLayer Ω z := L.toCore.B_le_exactLayer

theorem u_mem_normalizer
    (hset : TwinFrameSetting p f Ω L.K₁ L.T₁ L.J z L.u L.t) :
    L.u ∈ Subgroup.normalizer (L.J : Set G) := L.toCore.u_mem_normalizer hset.toCore

theorem u_mem_trivialOnQuot
    (hset : TwinFrameSetting p f Ω L.K₁ L.T₁ L.J z L.u L.t) : L.u ∈ trivialOnQuot L.J :=
  L.toCore.u_mem_trivialOnQuot hset.toCore

theorem B_le_trivialOnQuot
    (hset : TwinFrameSetting p f Ω L.K₁ L.T₁ L.J z L.u L.t) :
    Subgroup.closure ({z, L.u, L.t} : Set G) ≤ trivialOnQuot L.J :=
  L.toCore.B_le_trivialOnQuot hset.toCore

end TwinLift

end Frame

end CFSG.ClassicalInvolution.Asc77
