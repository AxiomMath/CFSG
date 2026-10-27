module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecXg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf3A
public import CFSG.ClassicalInvolution.Asc77.AscS24Cent
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.CGT.PushingUpLit.SolK.Basics
public import CFSG.CGT.PushingUpLit.BHS.Offender
public import CFSG.CGT.PushingUpLit.SolK.ModData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open scoped commutatorElement

section Twins

variable {Y : Type} [Group Y] [Finite Y]

theorem conjSub_mem_twinSet {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {L : Subgroup Y} {t : Y}
    (ht : IsUniqueInvolution L t) {d : Y} (hd : d ∈ Subgroup.centralizer ({t} : Set Y))
    {J : Subgroup Y} (hJ : J ∈ twinSet Ω L) : conjSub d J ∈ twinSet Ω L := by
  have hdz : d * t * d⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hd
    rw [hd, mul_inv_cancel_right]
  refine ⟨hΩ.conjInvariant d J hJ.1, t, ht, ?_⟩
  have := (TwinSecXg.isUniqueInvolution_of_mem_twinSet ht hJ).conj d
  rwa [hdz] at this

theorem le_rLayer_of_mem {Ω : Set (Subgroup Y)} {J : Subgroup Y} (hJ : J ∈ Ω) (h2 : IsPGroup 2 J)
    {a : Y} (hJa : J ≤ Subgroup.centralizer ({a} : Set Y)) : J ≤ rLayer Ω a :=
  Asc77.C22G.le_rLayer_of_le_centralizer (Q3.TC.mem_RSet_of_isPGroup hJ h2) hJa

theorem centralizes_twins_of_odd {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    {K K' K₃ K₄ : Subgroup Y} {t u₁ u₂ u₃ x : Y}
    (hd : A7T22.Hyp22G Ω K K' K₃ t u₁ u₂ u₃) (h41 : K₄ ≠ K) (h42 : K₄ ≠ K')
    (hV : ∀ J ∈ twinSet Ω K, J = K ∨ J = K' ∨ J = K₃ ∨ J = K₄) (hK₄ : K₄ ∈ twinSet Ω K)
    (h2g : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hq8 : ∀ J ∈ Ω, Nat.card ↥J = 8)
    (hxt : x ∈ Subgroup.centralizer ({t} : Set Y))
    (hxc : x ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y)) (hxodd : Odd (orderOf x))
    (hx3 : ∀ j ∈ K₃, x * j = j * x) (hx4 : ∀ j ∈ K₄, x * j = j * x) :
    ∀ J ∈ twinSet Ω K, ∀ j ∈ J, x * j = j * x := by
  have hzK₄ : IsUniqueInvolution K₄ t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hK₄
  have hKt : K ∈ twinSet Ω K := mem_twinSet_self hd.mem hd.hz
  have hc3 : conjSub x K₃ = K₃ := by
    ext y
    rw [mem_conjSub_iff]
    constructor
    · intro h
      have h1 := hx3 _ h
      have : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
      rw [this, h1]
      simpa using h
    · intro h
      have h1 := hx3 y h
      have : x⁻¹ * y * x = y := by
        calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
          _ = x⁻¹ * (x * y) := by rw [h1]
          _ = y := by group
      rwa [this]
  have hc4 : conjSub x K₄ = K₄ := by
    ext y
    rw [mem_conjSub_iff]
    constructor
    · intro h
      have h1 := hx4 _ h
      have : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
      rw [this, h1]
      simpa using h
    · intro h
      have h1 := hx4 y h
      have : x⁻¹ * y * x = y := by
        calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
          _ = x⁻¹ * (x * y) := by rw [h1]
          _ = y := by group
      rwa [this]
  have hperm : ∀ L ∈ ({K, K'} : Set (Subgroup Y)), conjSub x L = K ∨ conjSub x L = K' := by
    intro L hL
    have hLt : L ∈ twinSet Ω K := by
      rcases hL with rfl | rfl
      · exact hKt
      · exact hd.hK'
    have hmem := conjSub_mem_twinSet hΩ hd.hz hxt hLt
    rcases hV _ hmem with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have : L = K₃ := by
        calc L = conjSub x⁻¹ (conjSub x L) := (conjSub_inv_conjSub x L).symm
          _ = conjSub x⁻¹ K₃ := by rw [h]
          _ = K₃ := by
            calc conjSub x⁻¹ K₃ = conjSub x⁻¹ (conjSub x K₃) := by rw [hc3]
              _ = K₃ := conjSub_inv_conjSub x K₃
      rcases hL with rfl | rfl
      · exact hd.hK₃K this.symm
      · exact hd.hK₃K' this.symm
    · exfalso
      have : L = K₄ := by
        calc L = conjSub x⁻¹ (conjSub x L) := (conjSub_inv_conjSub x L).symm
          _ = conjSub x⁻¹ K₄ := by rw [h]
          _ = K₄ := by
            calc conjSub x⁻¹ K₄ = conjSub x⁻¹ (conjSub x K₄) := by rw [hc4]
              _ = K₄ := conjSub_inv_conjSub x K₄
      rcases hL with rfl | rfl
      · exact h41 this.symm
      · exact h42 this.symm
  obtain ⟨hxK, hxK'⟩ := conjSub_fix_of_odd (K := K) (K' := K') hd.hne.symm hxodd
    (hperm K (by simp)) (hperm K' (by simp))
  have hab : (x * u₁ * x⁻¹) * (x * u₂ * x⁻¹) = u₁ * u₂ := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hxc
    calc (x * u₁ * x⁻¹) * (x * u₂ * x⁻¹) = x * (u₁ * u₂) * x⁻¹ := by group
      _ = u₁ * u₂ := by rw [h1]; group
  have haK : x * u₁ * x⁻¹ ∈ K := by
    have := conj_mem_conjSub (n := x) hd.hu₁.1
    rwa [hxK] at this
  have hbK' : x * u₂ * x⁻¹ ∈ K' := by
    have := conj_mem_conjSub (n := x) hd.hu₂.1
    rwa [hxK'] at this
  have hinf : K ⊓ K' = Subgroup.zpowers t :=
    twin_inf_eq hΩ hd.mem hd.hK'.1 hd.hne.symm hd.hz hd.hzK' (h2g K hd.mem)
  have hmeet : u₁⁻¹ * (x * u₁ * x⁻¹) ∈ K ⊓ K' := by
    refine ⟨K.mul_mem (K.inv_mem hd.hu₁.1) haK, ?_⟩
    have : u₁⁻¹ * (x * u₁ * x⁻¹) = u₂ * (x * u₂ * x⁻¹)⁻¹ := by
      have h2 : x * u₁ * x⁻¹ = u₁ * u₂ * (x * u₂ * x⁻¹)⁻¹ := by
        calc x * u₁ * x⁻¹ = (x * u₁ * x⁻¹) * (x * u₂ * x⁻¹) * (x * u₂ * x⁻¹)⁻¹ := by group
          _ = u₁ * u₂ * (x * u₂ * x⁻¹)⁻¹ := by rw [hab]
      rw [h2]
      group
    rw [this]
    exact K'.mul_mem hd.hu₂.1 (K'.inv_mem hbK')
  rw [hinf] at hmeet
  have hu1fix : x * u₁ * x⁻¹ = u₁ := by
    refine conj_eq_of_odd_of_inv hxodd ?_
    rcases mem_zpowers_sq_eq_one hd.hz.sq hmeet with h | h
    · left
      calc x * u₁ * x⁻¹ = u₁ * (u₁⁻¹ * (x * u₁ * x⁻¹)) := by group
        _ = u₁ := by rw [h]; group
    · right
      calc x * u₁ * x⁻¹ = u₁ * (u₁⁻¹ * (x * u₁ * x⁻¹)) := by group
        _ = u₁ * t := by rw [h]
        _ = u₁ * (u₁ * u₁) := by rw [hd.sq₁]
        _ = u₁ * u₁ * u₁ := by group
        _ = u₁⁻¹ := by
          have h4 : u₁ * u₁ * u₁ * u₁ = 1 := by
            calc u₁ * u₁ * u₁ * u₁ = (u₁ * u₁) * (u₁ * u₁) := by group
              _ = t * t := by rw [hd.sq₁]
              _ = 1 := hd.hz.sq
          exact eq_inv_of_mul_eq_one_left h4
  have hu2fix : x * u₂ * x⁻¹ = u₂ := by
    have h1 : u₁ * (x * u₂ * x⁻¹) = u₁ * u₂ := by
      calc u₁ * (x * u₂ * x⁻¹) = (x * u₁ * x⁻¹) * (x * u₂ * x⁻¹) := by rw [hu1fix]
        _ = u₁ * u₂ := hab
    exact mul_left_cancel h1
  have hK8 := hq8 K hd.mem
  have hK'8 := hq8 K' hd.hK'.1
  have hcK : ∀ k ∈ K, x * k = k * x := fun k hk => by
    have := centralizes_of_odd_fix hK8 hd.hu₁.1 hd.hu₁.2 (fun k hk => by
      have := conj_mem_conjSub (n := x) hk
      rwa [hxK] at this) hxodd hu1fix k hk
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [this]
  have hcK' : ∀ k ∈ K', x * k = k * x := fun k hk => by
    have := centralizes_of_odd_fix hK'8 hd.hu₂.1 hd.hu₂.2 (fun k hk => by
      have := conj_mem_conjSub (n := x) hk
      rwa [hxK'] at this) hxodd hu2fix k hk
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [this]
  intro J hJ j hj
  rcases hV J hJ with rfl | rfl | rfl | rfl
  · exact hcK j hj
  · exact hcK' j hj
  · exact hx3 j hj
  · exact hx4 j hj

end Twins

section Layer


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem card_member_eq_eight (h : PerpHypS n Y R S t)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), Nat.card ↥J = 8 := by
  intro J hJ
  have hKS : IsSylow2In J J := ⟨le_rfl, h2g J hJ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨e⟩ := members_sylow_q8 h J hJ J hKS
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem members_le_centralizer (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    K₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) ∧ K₄ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
  obtain ⟨-, ⟨R₃, h3, c3⟩, ⟨R₄, h4', c4⟩⟩ := v3_layerBasics hStd hF
  have hd := hStd.datum
  exact ⟨(h3.2.2 K₃ le_rfl (h2g K₃ hd.hK₃.1) h3.1) ▸ c3, (h4'.2.2 K₄ le_rfl (h2g K₄ hF.1.1) h4'.1) ▸ c4⟩

theorem members_le_rLayer (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    K₃ ≤ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ∧
      K₄ ≤ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
  obtain ⟨h3, h4⟩ := members_le_centralizer hStd hF h2g
  have hd := hStd.datum
  exact ⟨le_rLayer_of_mem hd.hK₃.1 (h2g K₃ hd.hK₃.1) h3, le_rLayer_of_mem hF.1.1 (h2g K₄ hF.1.1) h4⟩

theorem oddCoreOf_rLayer_eq_bot (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J)
    (hodd : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    oddCoreOf (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = ⊥ := by
  classical
  have hd := hStd.datum
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hd.hyp
  have hq8 := card_member_eq_eight hStd.perp h2g
  have hV := TwinPerpV3.twinSet_four hStd hF
  obtain ⟨hK₃Cc, hK₄Cc⟩ := members_le_centralizer hStd hF h2g
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set c : Y := u₁ * u₂ with hc
  have hc1 : c ≠ 1 := hd.mul_ne_one
  set C : Subgroup Y := Subgroup.centralizer ({c} : Set Y) with hCdef
  set Ct : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hCtdef
  set Yu : Subgroup Y := rLayer Ω c with hYu
  set N : Subgroup Y := oddCoreOf Yu with hN
  have hNodd : Odd (Nat.card N) := Balance.odd_card_oddCoreIn Yu
  have hNYu : N ≤ Yu := oddCoreOf_le_self Yu
  have hYuC : Yu ≤ C := rLayer_le_centralizer Ω c
  have hYnorm : ∀ g ∈ C, conjSub g Yu = Yu := fun g hg => TwinMu.Pf3.conjSub_rLayer hΩ hg
  have hNnormYu : ∀ y ∈ Yu, ∀ x ∈ N, y * x * y⁻¹ ∈ N :=
    fun y hy x hx => Balance.conj_mem_oddCoreIn hy hx
  have hNC : N ≤ oddCoreOf C := TwinDisc.oddCoreOf_le_of_normalizes hYuC hYnorm
  have hNnormC : ∀ g ∈ C, conjSub g N = N := by
    intro g hg
    rw [hN, ← AscE184Sect.oddCoreOf_conjSub, hYnorm g hg]
  have hK₃Y : K₃ ≤ Yu :=
    le_rLayer_of_mem hd.hK₃.1 (h2g K₃ hd.hK₃.1) hK₃Cc
  have hK₄Y : K₄ ≤ Yu :=
    le_rLayer_of_mem hF.1.1 (h2g K₄ hF.1.1) hK₄Cc
  have hxt : ∀ x ∈ N, x * t = t * x := by
    intro x hx
    have h1 := Asc77.S24.mem_centralizer_oddCoreOf_of_alphaOf
      (A := Subgroup.closure ({c, t} : Set Y)) hα (a := c) (Subgroup.subset_closure (by simp)) hc1
      (b := t) (Subgroup.subset_closure (by simp))
    exact Subgroup.mem_centralizer_iff.mp h1 x (hNC hx)
  have hxCt : ∀ x ∈ N, x ∈ Ct := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hxt x hx)
  have hxC : ∀ x ∈ N, x ∈ C := fun x hx => hYuC (hNYu hx)
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 Ct) :=
    RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 Ct
  have hK₃Q : K₃ ≤ pCoreOf 2 Ct :=
    RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 (hd.subn K₃ hd.hK₃)
      (h2g K₃ hd.hK₃.1)
  have hK₄Q : K₄ ≤ pCoreOf 2 Ct :=
    RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 (hd.subn K₄ hF.1)
      (h2g K₄ hF.1.1)
  have hx3 : ∀ x ∈ N, ∀ j ∈ K₃, x * j = j * x := fun x hx =>
    comm_of_odd_of_le_two hNodd hQ2 hK₃Q hx
      (fun q hq => CGT.PushingUpLit.SolK.pCoreOf_normalized Ct (hxCt x hx) hq)
      (fun j hj n hn => hNnormYu j (hK₃Y hj) n hn)
  have hx4 : ∀ x ∈ N, ∀ j ∈ K₄, x * j = j * x := fun x hx =>
    comm_of_odd_of_le_two hNodd hQ2 hK₄Q hx
      (fun q hq => CGT.PushingUpLit.SolK.pCoreOf_normalized Ct (hxCt x hx) hq)
      (fun j hj n hn => hNnormYu j (hK₄Y hj) n hn)
  have hcent : ∀ x ∈ N, ∀ J ∈ twinSet Ω K, ∀ j ∈ J, x * j = j * x := fun x hx =>
    centralizes_twins_of_odd hΩ hd hF.2.1 hF.2.2.1 hV hF.1 h2g hq8 (hxCt x hx) (hxC x hx)
      (odd_orderOf_of_mem hNodd hx) (hx3 x hx) (hx4 x hx)
  set P : Subgroup Y := TwinSecXg.twinJoin Ω K with hP
  set C₁ : Subgroup Y := Ct ⊓ Subgroup.centralizer (P : Set Y) with hC₁
  have hKt : K ∈ twinSet Ω K := mem_twinSet_self hd.mem hd.hz
  have hle_P : ∀ J ∈ twinSet Ω K, J ≤ P := fun J hJ => le_iSup₂_of_le J hJ le_rfl
  have hNC₁ : N ≤ C₁ := by
    intro x hx
    refine ⟨hxCt x hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro p hp
    have hPle : P ≤ Subgroup.centralizer ({x} : Set Y) := by
      refine iSup₂_le fun J hJ j hj => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcent x hx J hJ j hj).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPle hp)
  have hC₁norm : ∀ g ∈ Ct, conjSub g C₁ = C₁ := by
    have hle : ∀ g ∈ Ct, conjSub g C₁ ≤ C₁ := by
      intro g hg y hy
      rw [mem_conjSub_iff] at hy
      have hgi : g⁻¹ ∈ Ct := Ct.inv_mem hg
      have hyCt : y ∈ Ct := by
        have : g * (g⁻¹ * y * g) * g⁻¹ ∈ Ct := Ct.mul_mem (Ct.mul_mem hg hy.1) hgi
        simpa [mul_assoc] using this
      refine ⟨hyCt, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro p hp
      have hp' : g⁻¹ * p * g ∈ P := by
        have := TwinSecXg.twinJoin_normalized hΩ hd.hz g⁻¹ hgi p hp
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hy.2 _ hp'
      calc p * y = g * ((g⁻¹ * p * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
        _ = y * p := by group
    intro g hg
    refine le_antisymm (hle g hg) ?_
    have h2 := conjSub_mono (n := g) (hle g⁻¹ (Ct.inv_mem hg))
    rwa [conjSub_conjSub_inv] at h2
  have hcP : c ∈ P := P.mul_mem (hle_P K hKt hd.hu₁.1) (hle_P K' hd.hK' hd.hu₂.1)
  have hC₁C : C₁ ≤ C := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hg.2 c hcP).symm
  have hNn : C₁ ≤ Subgroup.normalizer (N : Set Y) := fun g hg =>
    Asc77.mem_normalizer_iff_conjSub_eq.mpr (hNnormC g (hC₁C hg))
  have hNO : N ≤ oddCoreOf C₁ := Balance.le_oddCoreIn_of_normalizes hNC₁ hNn hNodd
  have hOle : oddCoreOf C₁ ≤ oddCoreOf Ct :=
    TwinDisc.oddCoreOf_le_of_normalizes inf_le_left hC₁norm
  have hOCt : oddCoreOf Ct = ⊥ := by
    show (classicalInvolutionOddCore ↥Ct).map Ct.subtype = ⊥
    rw [hodd]
    exact Subgroup.map_bot _
  exact le_antisymm ((hNO.trans hOle).trans hOCt.le) bot_le


end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6b
