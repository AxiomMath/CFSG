module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoEnd
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Alpha
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Conj
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Group

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp24

section Input

@[expose] def AlphaOddR (r n : ℕ) : Prop :=
  4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → TwinPerp.TwoTwins R →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W → ¬ TwinPerp.WCentralNontrivial W →
          ∀ g ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W, g * t * g⁻¹ ≠ t →
            Odd (Nat.card (alphaOf (Subgroup.closure ({t, g * t * g⁻¹} : Set Y))))

end Input

section Main

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem twoFrame_m_even (hr : 4 ≤ r) (h : PerpHypR r n Y R S t) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) {K K' : Subgroup Y}
    (D : Perp23.Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W K K' t) : Even D.m := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hquat : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ P : Subgroup Y, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rintro _ ⟨g', rfl⟩
    refine ⟨conjSub g' ((S : Subgroup R).map R.subtype), h.core.datum.sylow_core.conj g', ⟨?_⟩⟩
    exact (Subgroup.equivMapOfInjective _ (MulAut.conj g').toMonoidHom
      (MulAut.conj g').injective).symm.trans
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
        h.core.quat.some)
  have h16 := WTool.sylow16_of_quat hr hΩ hquat D.F.ρ.K D.F.ρ.hK D.F.ρ.R D.F.ρ.hRK
  have hcard : Nat.card D.F.ρ.R = 2 * Nat.card ↥(D.F.ρ.R ⊓ W) :=
    Q3CL.Thompson.D_card hΩ hW D.F.ρ.hR
  have hcard2 : Nat.card ↥(D.F.ρ.R ⊓ W) = 4 * D.m := by
    rw [← D.h₁, Nat.card_zpowers, D.o₁]
  rw [hcard2] at hcard
  obtain ⟨k, hk⟩ := D.F.ρ.hRK.2.1.exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e, rfl⟩ : ∃ e, k = e + 4 := ⟨k - 4, by omega⟩
  rw [pow_add] at hk
  generalize 2 ^ e = u at hk
  exact ⟨u, by omega⟩

theorem frame_ju (h : PerpHypR r n Y R S t) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hnc : ¬ TwinPerp.WCentralNontrivial W) {K' : Subgroup Y}
    (D : Perp23.Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t) :
    D.F.j = D.b * D.b'⁻¹ := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have cx : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W :=
    Q3CL.T8.ctxOf h.partIHypG hW
  have hwc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := WTool.comm_of_mem_wSet hΩ hW
  have h1 := D.u_mul_e hwc
  rw [D.e_eq_one hΩ hW cx hnc, mul_one] at h1
  exact h1.symm

theorem frame_frattini (hr : 4 ≤ r) (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hnc : ¬ TwinPerp.WCentralNontrivial W) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R)
    (D : Perp23.Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t) :
    ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      ∃ o ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y)),
        ∃ n ∈ Subgroup.centralizer ({t} : Set Y),
          n ∈ Subgroup.normalizer (Subgroup.closure ({t, D.F.j} : Set Y) : Set Y) ∧ c = o * n := by
  classical
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hwc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := WTool.comm_of_mem_wSet hΩ hW
  have hz : IsUniqueInvolution (tightCore R) t := D.hzK
  have hz2 : t * t = 1 := hz.sq
  have hj2 : D.F.j * D.F.j = 1 := D.j_sq
  have htj : t * D.F.j = D.F.j * t := hwc t D.t_mem_W D.F.j D.j_mem_W
  have hju := frame_ju h hW hnc D
  obtain ⟨m', hm'⟩ := twoFrame_m_even hr h hW D
  have hx₁K : D.x₁ ∈ tightCore R := by
    have := D.F.ρ.hRK.1 D.x₁_mem_R
    rwa [D.hρK] at this
  have hx₂K' : D.x₂ ∈ K' := by
    have := D.F.ρ'.hRK.1 D.x₂_mem_R
    rwa [D.hρ'K] at this
  have hb : D.b = D.x₁ ^ m' * D.x₁ ^ m' := by
    show D.x₁ ^ D.m = _
    rw [hm', pow_add]
  have hb' : D.b' = D.x₂ ^ m' * D.x₂ ^ m' := by
    show D.x₂ ^ D.m = _
    rw [hm', pow_add]
  set j := D.F.j with hjdef
  set E : Subgroup Y := Subgroup.closure ({t, j} : Set Y) with hEdef
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  have hEsq : ∀ x ∈ E, x * x = 1 := closure_pair_sq hz2 hj2 htj
  have hEp : IsPGroup 2 E := isPGroup_two_of_sq hEsq
  have htE : t ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hjC : j ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr htj.symm
  have hEC : E ≤ C := by
    rw [hEdef, Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]; exact htC
    · rw [Set.mem_singleton_iff.mp hx]; exact hjC
  have hct : ∀ c ∈ C, c * t * c⁻¹ = t := fun c hc => by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * t * c⁻¹ = t * c * c⁻¹ := by rw [this]
      _ = t := by group
  have hcj : ∀ c ∈ C, c * j * c⁻¹ ∈ E ⊔ oddCoreIn C := by
    intro c hc
    have := conj_mem_sup h h2 hK' hne (Subgroup.pow_mem _ hx₁K m') (Subgroup.pow_mem _ hx₂K' m')
      hb hb' D.b_sq D.b'_sq hc
    rw [← hju] at this
    exact this
  have hEO : ∀ c ∈ C, ∀ x ∈ E, c * x * c⁻¹ ∈ E ⊔ oddCoreIn C := by
    intro c hc
    have hle : E ≤ (E ⊔ oddCoreIn C).comap (MulAut.conj c).toMonoidHom := by
      rw [hEdef, Subgroup.closure_le]
      rintro x (hx | hx)
      · rw [hx]
        show c * t * c⁻¹ ∈ E ⊔ oddCoreIn C
        rw [hct c hc]
        exact Subgroup.mem_sup_left htE
      · rw [Set.mem_singleton_iff.mp hx]
        exact hcj c hc
    intro x hx
    simpa using hle hx
  have hOn : ∀ c ∈ C, ∀ x ∈ oddCoreIn C, c * x * c⁻¹ ∈ oddCoreIn C :=
    fun c hc x hx => conj_mem_oddCoreIn hc hx
  exact fun c hc =>
    exists_mul_normalizer_of_le hEC (oddCoreIn_le C) hOn hEO (odd_card_oddCoreIn C) hEp hc

theorem twinPerp24R_of_two23 (hr : 4 ≤ r) (hTwo : Perp23.Two23R r n) (hA : AlphaOddR r n) :
    TwinPerp24R r n := by
  intro Y _ _ R S t h h2 W hW htW hS4 hnc
  exfalso
  classical
  obtain ⟨K', hK', hne, ⟨D⟩⟩ := Perp23.Two.exists_twoFrame h h2 hW htW hS4
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have cx : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W :=
    Q3CL.T8.ctxOf h.partIHypG hW
  have hwc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := WTool.comm_of_mem_wSet hΩ hW
  have hz : IsUniqueInvolution (tightCore R) t := D.hzK
  have hz2 : t * t = 1 := hz.sq
  have hz1 : t ≠ 1 := hz.ne_one
  have hj2 : D.F.j * D.F.j = 1 := D.j_sq
  have hj1 : D.F.j ≠ 1 := D.F.hj.ne_one
  have htj : t * D.F.j = D.F.j * t := hwc t D.t_mem_W D.F.j D.j_mem_W
  have hsM : D.F.ρ₃.r ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W := D.s_mem_mgrp
  have hst : D.F.ρ₃.r * t * D.F.ρ₃.r⁻¹ = t * D.F.j := D.s_t hwc
  have hsne : D.F.ρ₃.r * t * D.F.ρ₃.r⁻¹ ≠ t := by
    rw [hst]
    intro h1
    exact hj1 (mul_eq_left.mp h1)
  have hgen := hTwo Y R S t h h2 W hW htW hS4 _ hsM hsne
  have hα := hA hr Y R S t h h2 W hW htW hS4 hnc _ hsM hsne
  rw [hst, closure_pair_mul hz2] at hα
  have hsN : D.F.ρ₃.r ∈ Subgroup.normalizer
      (Subgroup.closure ({t, D.F.j} : Set Y) : Set Y) := D.mgrp_le_normalizer hΩ hW cx hsM
  have hfac := frame_frattini hr h h2 hW hnc hK' hne D
  set j := D.F.j with hjdef
  set s := D.F.ρ₃.r with hsdef
  set E : Subgroup Y := Subgroup.closure ({t, j} : Set Y) with hEdef
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  have hEsq : ∀ x ∈ E, x * x = 1 := closure_pair_sq hz2 hj2 htj
  have hEp : IsPGroup 2 E := isPGroup_two_of_sq hEsq
  have htE : t ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hjC : j ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr htj.symm
  have hEC : E ≤ C := by
    rw [hEdef, Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]; exact htC
    · rw [Set.mem_singleton_iff.mp hx]; exact hjC
  have hCα : C ≤ Subgroup.normalizer (alphaOf E : Set Y) :=
    le_normalizer_alphaOf hEp htE hz1 hEC hfac
  have hsα : s ∈ Subgroup.normalizer (alphaOf E : Set Y) := mem_normalizer_alphaOf hsN
  have hCv : ∀ x ∈ Subgroup.centralizer ({s * t * s⁻¹} : Set Y), s⁻¹ * x * s ∈ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc s⁻¹ * x * s * t = s⁻¹ * (x * (s * t * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * t * s⁻¹) * x) * s := by rw [hx]
      _ = t * (s⁻¹ * x * s) := by group
  have hCvα : Subgroup.centralizer ({s * t * s⁻¹} : Set Y) ≤
      Subgroup.normalizer (alphaOf E : Set Y) := by
    intro x hx
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hsα (hCα (hCv x hx)))
      (Subgroup.inv_mem _ hsα)
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at h2
  have htop : Subgroup.normalizer (alphaOf E : Set Y) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hgen]
    exact sup_le hCvα hCα
  have hαn : (alphaOf E).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hαbot : alphaOf E = ⊥ := by
    have hle : alphaOf E ≤ classicalInvolutionOddCore Y := le_sSup ⟨hαn, hα⟩
    rw [h.core.oddFree] at hle
    exact le_bot_iff.mp hle
  have hCN : C ≤ Subgroup.normalizer (E : Set Y) :=
    le_normalizer_of_alphaOf_eq_bot htE hz1 hαbot hfac
  have hCvN : Subgroup.centralizer ({s * t * s⁻¹} : Set Y) ≤
      Subgroup.normalizer (E : Set Y) := by
    intro x hx
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hsN (hCN (hCv x hx)))
      (Subgroup.inv_mem _ hsN)
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at h2
  have hEtop : Subgroup.normalizer (E : Set Y) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hgen]
    exact sup_le hCvN hCN
  have hEnormal : E.Normal := Subgroup.normalizer_eq_top_iff.mp hEtop
  haveI := h.core.simple
  exact not_tightInO2_of_fstar h.core.nonab hz1 ⟨E, hEnormal, hEp, htE⟩

theorem twinPerp24R_of_alphaOdd (hr : 4 ≤ r) (hE : TwinThmER r n) (h233 : TwinPerp233R r n)
    (hA : AlphaOddR r n) : TwinPerp24R r n :=
  twinPerp24R_of_two23 hr (Perp23.two23R_of_thmE hr hE h233) hA

end Main

end Perp24

end CFSG.CGT.PushingUpLit.SolKNA.R4
