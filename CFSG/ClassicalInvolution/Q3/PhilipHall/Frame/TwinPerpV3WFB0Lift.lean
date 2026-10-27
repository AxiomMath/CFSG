module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93WO2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section B0Lift




variable {n : ℕ}

theorem eq_of_mk_eq_of_odd {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (hodd : ∀ o ∈ N, Odd (orderOf o)) {v w : X} (hv : v * v = 1) (hw : w * w = 1)
    (hcent : ∀ o ∈ N, o * w = w * o)
    (h : (QuotientGroup.mk v : X ⧸ N) = QuotientGroup.mk w) : v = w := by
  have hN : w⁻¹ * v ∈ N := QuotientGroup.eq.mp h.symm
  set o := w⁻¹ * v with ho
  have hvo : v = w * o := by rw [ho]; group
  have hco := hcent o hN
  have ho2 : o * o = 1 := by
    have h1 : (w * o) * (w * o) = 1 := by rw [← hvo]; exact hv
    have h2 : (w * o) * (w * o) = (w * w) * (o * o) := by
      calc (w * o) * (w * o) = w * (o * w) * o := by group
        _ = w * (w * o) * o := by rw [hco]
        _ = (w * w) * (o * o) := by group
    rw [h2, hw, one_mul] at h1
    exact h1
  have hdvd : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
  have h1 : orderOf o = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact h1
    · exfalso
      have := hodd o hN
      rw [h1] at this
      exact absurd this (by decide)
  have : o = 1 := orderOf_eq_one_iff.mp h1
  rw [hvo, this, mul_one]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem lift_conj_involution (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    {J : Subgroup G} {t : G} (hJ : J ∈ Q3NL.tqMembers3 Ω u) (ht : IsUniqueInvolution J t)
    (hcent : ∀ m ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G)), m * t = t * m)
    {y : G} (hyC : y ∈ Subgroup.centralizer ({u} : Set G))
    (hst : t * (y * t * y⁻¹) = (y * t * y⁻¹) * t) (hne : y * t * y⁻¹ ≠ t)
    (z₀ j : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u))
    (hz₀ : IsUniqueInvolution (TwinDisc.secImg Ω u J) z₀)
    (hKlein : ∀ J' ∈ TwinDisc.secFam Ω u, ∀ z' : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u),
      IsUniqueInvolution J' z' → z' = z₀ ∨ z' = j ∨ z' = z₀ * j) :
    ∀ c ∈ Subgroup.centralizer ({u} : Set G),
      c * t * c⁻¹ = t ∨ c * t * c⁻¹ = y * t * y⁻¹ ∨ c * t * c⁻¹ = t * (y * t * y⁻¹) := by
  classical
  haveI := Pf93.normal_coreHull hΩ hc2
  have key : ∀ c ∈ (Subgroup.centralizer ({u} : Set G)), ∃ v : ↥(coreHull Ω u), ((v : ↥(Subgroup.centralizer ({u} : Set G))) : G) = c * t * c⁻¹ ∧
      IsUniqueInvolution (TwinDisc.secImg Ω u (conjSub c J)) (QuotientGroup.mk v : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) := by
    intro c hc
    obtain ⟨hxC, hxX, hinv⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2
      (Q3NL.conjSub_mem_tqMembers3 hΩ.conjInvariant hc hJ) (ht.conj c)
    exact ⟨⟨⟨_, hxC⟩, hxX⟩, rfl, hinv⟩
  obtain ⟨htC, htX, htinv⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hJ ht
  set tX : ↥(coreHull Ω u) := ⟨⟨t, htC⟩, htX⟩ with htXdef
  have hz₀eq : z₀ = QuotientGroup.mk tX := hz₀.eq htinv
  obtain ⟨sX, hsXv, hsXinv⟩ := key y hyC
  have htX2 : tX * tX = 1 := Subtype.ext (Subtype.ext ht.sq)
  have hsq : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
    calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [ht.sq]; group
  have hsX2 : sX * sX = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show ((sX : ↥(Subgroup.centralizer ({u} : Set G))) : G) * ((sX : ↥(Subgroup.centralizer ({u} : Set G))) : G) = 1
    rw [hsXv]
    exact hsq
  have htsX : tX * sX = sX * tX := by
    apply Subtype.ext
    apply Subtype.ext
    show t * ((sX : ↥(Subgroup.centralizer ({u} : Set G))) : G) = ((sX : ↥(Subgroup.centralizer ({u} : Set G))) : G) * t
    rw [hsXv]
    exact hst
  have hodd : ∀ o ∈ (classicalInvolutionOddCore ↥(coreHull Ω u)), Odd (orderOf o) := fun o ho => Q3T.odd_orderOf_of_mem_oddCore ho
  have hcentT : ∀ o ∈ (classicalInvolutionOddCore ↥(coreHull Ω u)), o * tX = tX * o := by
    intro o ho
    apply Subtype.ext
    apply Subtype.ext
    exact hcent _ (TwinDisc.oddCore_coreHull_le hΩ hc2 ho)
  have hcentS : ∀ o ∈ (classicalInvolutionOddCore ↥(coreHull Ω u)), o * sX = sX * o := by
    intro o ho
    have ho' := Pf93.conjNormal_mem_oddCore hΩ hc2 (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({u} : Set G)))⁻¹ ho
    have h1 := hcent _ (TwinDisc.oddCore_coreHull_le hΩ hc2 ho')
    rw [MulAut.conjNormal_apply] at h1
    apply Subtype.ext
    apply Subtype.ext
    show ((o : ↥(Subgroup.centralizer ({u} : Set G))) : G) * ((sX : ↥(Subgroup.centralizer ({u} : Set G))) : G) = ((sX : ↥(Subgroup.centralizer ({u} : Set G))) : G) * ((o : ↥(Subgroup.centralizer ({u} : Set G))) : G)
    rw [hsXv]
    have h2 : (y⁻¹ * ((o : ↥(Subgroup.centralizer ({u} : Set G))) : G) * y) * t = t * (y⁻¹ * ((o : ↥(Subgroup.centralizer ({u} : Set G))) : G) * y) := by
      simpa using h1
    calc ((o : ↥(Subgroup.centralizer ({u} : Set G))) : G) * (y * t * y⁻¹) = y * ((y⁻¹ * ((o : ↥(Subgroup.centralizer ({u} : Set G))) : G) * y) * t) * y⁻¹ := by group
      _ = y * (t * (y⁻¹ * ((o : ↥(Subgroup.centralizer ({u} : Set G))) : G) * y)) * y⁻¹ := by rw [h2]
      _ = (y * t * y⁻¹) * ((o : ↥(Subgroup.centralizer ({u} : Set G))) : G) := by group
  rw [hz₀eq] at hKlein
  have hz0sq : (QuotientGroup.mk tX : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) *
      QuotientGroup.mk tX = 1 := by
    rw [← hz₀eq]
    exact hz₀.sq
  have hsne : (QuotientGroup.mk sX : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) ≠
      QuotientGroup.mk tX := by
    intro h
    have hN : tX⁻¹ * sX ∈ classicalInvolutionOddCore ↥(coreHull Ω u) := QuotientGroup.eq.mp h.symm
    have hodd' := hodd _ hN
    have hval : (((tX⁻¹ * sX : ↥(coreHull Ω u)) : ↥(Subgroup.centralizer ({u} : Set G))) : G) =
        t * (y * t * y⁻¹) := by
      show ((tX : ↥(Subgroup.centralizer ({u} : Set G))) : G)⁻¹ *
        ((sX : ↥(Subgroup.centralizer ({u} : Set G))) : G) = _
      rw [hsXv]
      show t⁻¹ * (y * t * y⁻¹) = _
      rw [inv_eq_of_mul_eq_one_right ht.sq]
    have hne1 : tX⁻¹ * sX ≠ 1 := by
      intro h1
      have h2 : (((tX⁻¹ * sX : ↥(coreHull Ω u)) : ↥(Subgroup.centralizer ({u} : Set G))) : G) = 1 := by
        rw [h1]; rfl
      rw [hval] at h2
      apply hne
      calc y * t * y⁻¹ = t⁻¹ * (t * (y * t * y⁻¹)) := by group
        _ = t⁻¹ := by rw [h2, mul_one]
        _ = t := inv_eq_of_mul_eq_one_right ht.sq
    have hsq2 : (tX⁻¹ * sX) ^ 2 = 1 := by
      have : tX⁻¹ = tX := inv_eq_of_mul_eq_one_right htX2
      rw [this, pow_two]
      calc tX * sX * (tX * sX) = tX * (sX * tX) * sX := by group
        _ = tX * (tX * sX) * sX := by rw [htsX]
        _ = (tX * tX) * (sX * sX) := by group
        _ = 1 := by rw [htX2, hsX2, one_mul]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : orderOf (tX⁻¹ * sX) = 2 := orderOf_eq_prime hsq2 hne1
    rw [h2] at hodd'
    exact absurd hodd' (by decide)
  have hmem : ∀ J' ∈ TwinDisc.secFam Ω u,
      ∀ z' : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u),
      IsUniqueInvolution J' z' →
      z' = QuotientGroup.mk tX ∨ z' = QuotientGroup.mk sX ∨
        z' = QuotientGroup.mk tX * QuotientGroup.mk sX := by
    intro J' hJ' z' hz'
    have hK' := hKlein J' hJ' z' hz'
    have hKs := hKlein _ (TwinDisc.secImg_mem_secFam
      (Q3NL.conjSub_mem_tqMembers3 hΩ.conjInvariant hyC hJ)) _ hsXinv
    rcases hKs with h | h | h
    · exact absurd h hsne
    · rcases hK' with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl (h'.trans h.symm))
      · exact Or.inr (Or.inr (by rw [h', ← h]))
    · rcases hK' with h' | h' | h'
      · exact Or.inl h'
      · refine Or.inr (Or.inr ?_)
        rw [h', h]
        calc j = (QuotientGroup.mk tX * QuotientGroup.mk tX) * j := by rw [hz0sq, one_mul]
          _ = QuotientGroup.mk tX * (QuotientGroup.mk tX * j) := mul_assoc _ _ _
      · exact Or.inr (Or.inl (h'.trans h.symm))
  intro c hc
  obtain ⟨vX, hvXv, hvXinv⟩ := key c hc
  have hvX2 : vX * vX = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show ((vX : ↥(Subgroup.centralizer ({u} : Set G))) : G) * ((vX : ↥(Subgroup.centralizer ({u} : Set G))) : G) = 1
    rw [hvXv]
    calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht.sq]; group
  have hts2 : (tX * sX) * (tX * sX) = 1 := by
    calc tX * sX * (tX * sX) = tX * (sX * tX) * sX := by group
      _ = tX * (tX * sX) * sX := by rw [htsX]
      _ = (tX * tX) * (sX * sX) := by group
      _ = 1 := by rw [htX2, hsX2, one_mul]
  rcases hmem _ (TwinDisc.secImg_mem_secFam (Q3NL.conjSub_mem_tqMembers3 hΩ.conjInvariant hc hJ)) _ hvXinv
    with h | h | h
  · have := eq_of_mk_eq_of_odd (classicalInvolutionOddCore ↥(coreHull Ω u)) hodd hvX2 htX2 hcentT h
    left
    rw [← hvXv, this]
  · have := eq_of_mk_eq_of_odd (classicalInvolutionOddCore ↥(coreHull Ω u)) hodd hvX2 hsX2 hcentS h
    right; left
    rw [← hvXv, this, hsXv]
  · have hcentTS : ∀ o ∈ (classicalInvolutionOddCore ↥(coreHull Ω u)), o * (tX * sX) = (tX * sX) * o := by
      intro o ho
      calc o * (tX * sX) = (o * tX) * sX := by group
        _ = (tX * o) * sX := by rw [hcentT o ho]
        _ = tX * (o * sX) := by group
        _ = tX * (sX * o) := by rw [hcentS o ho]
        _ = (tX * sX) * o := by group
    have h' : (QuotientGroup.mk vX : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) = QuotientGroup.mk (tX * sX) := by
      rw [h, QuotientGroup.mk_mul]
    have := eq_of_mk_eq_of_odd (classicalInvolutionOddCore ↥(coreHull Ω u)) hodd hvX2 hts2 hcentTS h'
    right; right
    rw [← hvXv, this]
    show ((tX : ↥(Subgroup.centralizer ({u} : Set G))) : G) * ((sX : ↥(Subgroup.centralizer ({u} : Set G))) : G) = _
    rw [hsXv]

end B0Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
