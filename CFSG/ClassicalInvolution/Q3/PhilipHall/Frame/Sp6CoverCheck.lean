module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightRefute
public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverSpec
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Schreier.ClassSpec
public import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveQuat
public import CFSG.Sporadic.Mathieu.M12
public import Certificates.Certificate118002
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Q3.TL3Induct
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem cA_size : cA.size = 3 := rfl

theorem ySub_eq_closure :
    ySub = Subgroup.closure {g | ∃ i < 3, permOfArr 240 yS[i]! = g} :=
  ofArrays_originalSubgroup

theorem dP_mem {k : ℕ} (hk : k < 3) : dP k ∈ ySub := by
  rw [ySub_eq_closure]
  exact Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem card_ySub : Nat.card ySub = 2903040 := Certificates.certificate118002.1

theorem d_rep {k : ℕ} (hk : k < 3) :
    CFSG.Monster.B.Co2.Rep 240 yS[k]! (dP k) ∧
      CFSG.Monster.B.Co2.Rep 240 (invCand 240 yS[k]!) (dP k)⁻¹ :=
  have h := Certificates.certificate118002.2.1 k hk
  ⟨h, CFSG.KS.Raw.rep_invCand h⟩

theorem rep_data {a : Array ℕ} (ha : a ∈ [tA, iA, jA] ++ cA.toList) :
    CFSG.Monster.B.Co2.Rep 240 a (permOfArr 240 a) ∧
      CFSG.Monster.B.Co2.Rep 240 (invCand 240 a) (permOfArr 240 a)⁻¹ :=
  have h := Certificates.certificate118002.2.2.1 a ha
  ⟨h, CFSG.KS.Raw.rep_invCand h⟩

theorem t_data : CFSG.Monster.B.Co2.Rep 240 tA tP ∧
    CFSG.Monster.B.Co2.Rep 240 (invCand 240 tA) tP⁻¹ ∧ tP ∈ ySub :=
  ⟨(rep_data (a := tA) (by simp)).1, (rep_data (a := tA) (by simp)).2,
    Certificates.certificate118002.2.2.2.1⟩

theorem i_data : CFSG.Monster.B.Co2.Rep 240 iA iP ∧
    CFSG.Monster.B.Co2.Rep 240 (invCand 240 iA) iP⁻¹ ∧ iP ∈ ySub :=
  ⟨(rep_data (a := iA) (by simp)).1, (rep_data (a := iA) (by simp)).2,
    Certificates.certificate118002.2.2.2.2.1⟩

theorem j_data : CFSG.Monster.B.Co2.Rep 240 jA jP ∧
    CFSG.Monster.B.Co2.Rep 240 (invCand 240 jA) jP⁻¹ ∧ jP ∈ ySub :=
  ⟨(rep_data (a := jA) (by simp)).1, (rep_data (a := jA) (by simp)).2,
    Certificates.certificate118002.2.2.2.2.2.1⟩

theorem cA_mem_CSub {a : Array ℕ} (ha : a ∈ cA.toList) : permOfArr 240 a ∈ CSub :=
  Certificates.certificate118002.2.2.2.2.2.2.2.1 a ha

theorem c_data {a : Array ℕ} (ha : a ∈ cA.toList) : CFSG.Monster.B.Co2.Rep 240 a (permOfArr 240 a) ∧
    CFSG.Monster.B.Co2.Rep 240 (invCand 240 a) (permOfArr 240 a)⁻¹ ∧ permOfArr 240 a ∈ ySub :=
  ⟨(rep_data (a := a) (by simp [ha])).1, (rep_data (a := a) (by simp [ha])).2,
    (Subgroup.mem_inf.1 (cA_mem_CSub ha)).1⟩

theorem t_mul_t : tP * tP = 1 := Certificates.certificate118002.2.2.2.2.2.2.2.2.2.1

theorem t_ne_one : tP ≠ 1 := Certificates.certificate118002.2.2.2.2.2.2.2.2.2.2.1

theorem i_mul_i : iP * iP = tP := Certificates.certificate118002.2.2.2.2.2.2.2.2.2.2.2.1

theorem j_mul_j : jP * jP = tP := Certificates.certificate118002.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem j_i_j : jP * iP * jP⁻¹ = iP⁻¹ :=
  Certificates.certificate118002.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_CSub : Nat.card CSub = 4608 :=
  Certificates.certificate118002.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem conj_RSub : ∀ c ∈ CSub, ∀ r ∈ RSub, c * r * c⁻¹ ∈ RSub :=
  Certificates.certificate118002.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

noncomputable abbrev tY : ySub := ⟨tP, t_data.2.2⟩

noncomputable abbrev iY : ySub := ⟨iP, i_data.2.2⟩

noncomputable abbrev jY : ySub := ⟨jP, j_data.2.2⟩

noncomputable abbrev dY (k : ℕ) (hk : k < 3) : ySub := ⟨dP k, dP_mem hk⟩

theorem tY_mul_tY : tY * tY = 1 := Subtype.ext t_mul_t

theorem tY_ne_one : tY ≠ 1 := fun h => t_ne_one (congrArg Subtype.val h)

theorem eq_top_of_dY {K : Subgroup ySub} (hK : ∀ k (hk : k < 3), dY k hk ∈ K) : K = ⊤ := by
  have hle : ySub ≤ K.map ySub.subtype :=
    ySub_eq_closure.le.trans ((Subgroup.closure_le _).2 (by
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨dY k hk, hK k hk, rfl⟩))
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rw [show x = y from Subtype.ext hyx.symm]
  exact hy

theorem mem_centralizer_tY {x : ySub} :
    x ∈ Subgroup.centralizer ({tY} : Set ySub) ↔ (x : Equiv.Perm (Fin 240)) ∈ CSub := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨x.2, congrArg Subtype.val h⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext h

theorem mem_ySub_of_CSub {x : Equiv.Perm (Fin 240)} (hx : x ∈ CSub) : x ∈ ySub :=
  (Subgroup.mem_inf.1 hx).1

theorem card_centralizer_tY : Nat.card (Subgroup.centralizer ({tY} : Set ySub)) = 4608 := by
  have hmap : (Subgroup.centralizer ({tY} : Set ySub)).map ySub.subtype = CSub := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_centralizer_tY.1 hy
    · intro hx
      exact ⟨⟨x, mem_ySub_of_CSub hx⟩, mem_centralizer_tY.2 hx, rfl⟩
  rw [← card_CSub, ← hmap, Subgroup.card_map_of_injective ySub.subtype_injective]

theorem iY_sq : iY ^ 2 = tY := by rw [sq]; exact Subtype.ext i_mul_i

theorem jY_sq : jY ^ 2 = tY := by rw [sq]; exact Subtype.ext j_mul_j

theorem iY_pow_four : iY ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, iY_sq, sq, tY_mul_tY]

theorem jY_sq_eq : jY ^ 2 = iY ^ 2 := by rw [iY_sq, jY_sq]

theorem jij_Y : jY * iY * jY⁻¹ = iY⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_inv, Subgroup.coe_mul]
  exact j_i_j

theorem iY_sq_ne_one : iY ^ 2 ≠ 1 := by rw [iY_sq]; exact tY_ne_one

noncomputable abbrev qY : QuaternionGroup 2 →* ySub :=
  CFSG.EvenSporadicStandard.RuStd.S2.quatHom (n := 2) iY jY (by simpa using iY_pow_four) jY_sq_eq
    jij_Y

theorem qY_injective : Function.Injective qY :=
  CFSG.EvenSporadicStandard.RuStd.S2.quatHom_injective iY_pow_four iY_sq_ne_one jY_sq_eq jij_Y

noncomputable abbrev RY : Subgroup ySub := qY.range

noncomputable def eR : ↥RY ≃* QuaternionGroup 2 := (MonoidHom.ofInjective qY_injective).symm

theorem card_RY : Nat.card RY = 8 := by
  rw [Nat.card_congr eR.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem qY_a (k : ZMod (2 * 2)) : qY (QuaternionGroup.a k) = iY ^ k.val := rfl

theorem qY_xa (k : ZMod (2 * 2)) : qY (QuaternionGroup.xa k) = jY * iY ^ k.val := rfl

theorem iY_mem : iY ∈ RY :=
  ⟨QuaternionGroup.a 1, by rw [qY_a, show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]⟩

theorem jY_mem : jY ∈ RY := ⟨QuaternionGroup.xa 0, by rw [qY_xa]; simp⟩

theorem tY_mem : tY ∈ RY := ⟨QuaternionGroup.a 2, by rw [qY_a, ← iY_sq]; rfl⟩

theorem mem_RY_cases {r : ySub} (hr : r ∈ RY) : ∃ k : ℕ, r = iY ^ k ∨ r = jY * iY ^ k := by
  obtain ⟨q, rfl⟩ := hr
  cases q with
  | a k => exact ⟨k.val, Or.inl rfl⟩
  | xa k => exact ⟨k.val, Or.inr rfl⟩

theorem map_RY : RY.map ySub.subtype = RSub := by
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    have hi : iP ∈ RSub := Subgroup.subset_closure (by simp)
    have hj : jP ∈ RSub := Subgroup.subset_closure (by simp)
    obtain ⟨k, rfl | rfl⟩ := mem_RY_cases hr
    · simpa using Subgroup.pow_mem _ hi k
    · simpa using Subgroup.mul_mem _ hj (Subgroup.pow_mem _ hi k)
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨iY, iY_mem, rfl⟩
    · exact ⟨jY, jY_mem, rfl⟩

theorem conj_mem_RY {c : ySub} (hc : c ∈ Subgroup.centralizer ({tY} : Set ySub)) {r : ySub}
    (hr : r ∈ RY) : c * r * c⁻¹ ∈ RY := by
  have hrR : (r : Equiv.Perm (Fin 240)) ∈ RSub := map_RY ▸ ⟨r, hr, rfl⟩
  have hcr := conj_RSub _ (mem_centralizer_tY.1 hc) _ hrR
  rw [← map_RY] at hcr
  obtain ⟨r', hr', hr'eq⟩ := hcr
  have : c * r * c⁻¹ = r' := Subtype.ext (by simpa using hr'eq.symm)
  rw [this]
  exact hr'

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
