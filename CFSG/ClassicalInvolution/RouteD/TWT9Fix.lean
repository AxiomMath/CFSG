module

public import CFSG.ClassicalInvolution.RouteD.TWT8Fix
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusNodesImg
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.Models.TwistedPairs
open QuadraticMap

set_option linter.unusedSectionVars false

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}



theorem pattern_td4 (c : TCtx p f .POmegaMinus 4 Ω K z) {β : Subgroup G} {t : G}
    (htz : t * z * t⁻¹ = z) {J₁ : Subgroup G} (hJ₁Ω : J₁ ∈ Ω) (hKJ₁ : Commutes K J₁)
    (hβJ₁ : ∃ W, LinearBlockStandardPair (GaloisField p f) W β J₁)
    {x : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)}
    {α : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ≃*
      spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)}
    {g₀ : Vm 4 (GaloisField p f) ≃ₗ[GaloisField p f] Vm 4 (GaloisField p f)}
    {ε : GaloisField p f}
    (hn2 : locImg Ω z J₁ =
      ((rootSL2 (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2))
    (hconj : ∀ y v, spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) (α y) (g₀ v) =
      g₀ (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) y v))
    (hε : ε * ε = 1)
    (hscal : ∀ y,
      polar (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
        (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) x
        ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
          true)) y = 0 →
      polar (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
        (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) x
        ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
          false)) y = 0 →
      g₀ y = ε • y) :
    PartnerPatternMinus p f 4 Ω K β t := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hirr := minusCoeffs_irr p f
  have hF4 : 4 ≤ Nat.card (GaloisField p f) := c.h4
  have hQ : (polarBilin (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 4 (GaloisField p f) hirr
  obtain ⟨j, hjK, hjperf, hjY, hjΩ, hjc, hjp, hjtw, hjimg⟩ :=
    exists_nodes_typeTwistedD_img (m := 4) (by omega) (spinMinus6Generated_galois c.hp2)
      (spinMinus6_noCover_galois c.hp2 c.hq) c
  obtain ⟨y', hy'⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y' : G) ∈ locLayer Ω z := y'.2
  have hyz : (y' : G) * z * (y' : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hlocmk : locMk Ω z y' = c.d.ψ x := hy'
  let ψ' : ↥(spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
    (minusCoeffs p f).2)) →* locQuot Ω z := c.d.ψ
  set F₀ : HypFrame (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
    (4 - 1) := (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame with hF₀
  have hg : spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have hRfix : ∀ a : Fin (4 - 1), 1 ≤ a.val → ∀ r ∈ (rankOne (minusDatum 4 hirr).rootGroup
      a).map (MulAut.conj x).toMonoidHom, α r = r := by
    intro a ha
    have hperf : ⁅(rankOne (minusDatum 4 hirr).rootGroup a).map (MulAut.conj x).toMonoidHom,
        (rankOne (minusDatum 4 hirr).rootGroup a).map (MulAut.conj x).toMonoidHom⁆ =
        (rankOne (minusDatum 4 hirr).rootGroup a).map (MulAut.conj x).toMonoidHom := by
      rw [← Subgroup.map_commutator]
      exact congrArg (Subgroup.map _) (Subgroup.isPerfect_iff.mp (perfect_of_le_commutator
        (TWT8.rankOne_minus_perfect hirr hF4 a)))
    refine eq_of_fixed_of_perfect (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) (ker_spinAction_le_center _) α (MulAut.conj g₀) (fun y => ?_) hperf ?_
    · refine LinearEquiv.ext fun v => ?_
      show spinAction _ (α y) v = g₀ (spinAction _ y (g₀⁻¹ v))
      have e1 : g₀ (g₀⁻¹ v) = v := by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl
      have := hconj y (g₀⁻¹ v)
      rw [e1] at this
      exact this
    · rintro _ ⟨s, hs, rfl⟩
      have hshs : (MulAut.conj x).toMonoidHom s = x * s * x⁻¹ := rfl
      have hhO : spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) ((MulAut.conj x).toMonoidHom s) ∈
          TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField p f)
            (minusCoeffs p f).1 (minusCoeffs p f).2) :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ _ v
      have hfixv : ∀ r, spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) ((MulAut.conj x).toMonoidHom s)
          (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
            (minusCoeffs p f).2) x (F₀.vec ⟨0, by omega⟩ r)) =
          spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) x
            (F₀.vec ⟨0, by omega⟩ r) := by
        intro r
        rw [hshs, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          ← LinearEquiv.mul_apply (spinAction _ x⁻¹), ← map_mul, inv_mul_cancel, map_one]
        show spinAction _ x (spinAction _ s (F₀.vec ⟨0, by omega⟩ r)) = _
        exact congrArg (spinAction _ x) (TWT8.rankOne_fix_vec_zero_minus hirr (by omega)
          (by omega : 0 < a.val) hs r)
      have hcomm := commute_of_scalar_on_perp hQ (imgPair F₀ ⟨0, by omega⟩ hg) hg₀O hhO hε
        (fun y hy => hscal y (HypPair.mem_perp.mp hy).1 (HypPair.mem_perp.mp hy).2)
        (fun q hq => by
          obtain ⟨a₁, b₁, rfl⟩ := (mem_hypPlane_iff _).mp hq
          rw [map_add, map_smul, map_smul]
          exact congrArg₂ (· + ·) (congrArg (a₁ • ·) (hfixv true))
            (congrArg (b₁ • ·) (hfixv false)))
      show g₀ * spinAction _ _ * g₀⁻¹ = _
      rw [hcomm]
      group
  have hfix : ∀ a : Fin (4 - 1), 1 ≤ a.val → ∀ u ∈ locImg Ω z (conjSub (y' : G) (j a)),
      locAut hΩ.conjInvariant htz u = u := by
    intro a ha u hu
    rw [locImg_conjSub_layer (j a) y', hjimg a] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨s, hs, rfl⟩ : ∃ s : ↥(spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)), s ∈ rankOne (minusDatum 4 hirr).rootGroup a ∧ c.d.ψ s = v :=
      Subgroup.mem_map.mp hv
    rw [hlocmk]
    have hαs : α (x * s * x⁻¹) = x * s * x⁻¹ := hRfix a ha _ ⟨s, hs, rfl⟩
    have hu1 : (MulAut.conj (c.d.ψ x)).toMonoidHom (c.d.ψ s) = c.d.ψ (x * s * x⁻¹) := by
      change (MulAut.conj (ψ' x)).toMonoidHom (ψ' s) = ψ' (x * s * x⁻¹)
      simp [map_mul, map_inv]
    rw [hu1, ← hαθ, hαs]
  have hn2z : J₁ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hJ₁Ω c.hz.mem (commutes_symm hKJ₁)
  have hr0 : rankOne (minusDatum 4 hirr).rootGroup (⟨0, by norm_num⟩ : Fin (4 - 1)) =
      rootSL2 (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 0 1 (by omega)
        (by omega) (by omega) true false :=
    rankOne_minusDatum_of_lt hirr (k := ⟨0, by norm_num⟩) (by norm_num)
  have hpair0 : ∀ a : Fin (4 - 1), a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub (y' : G) (j a)) := by
    intro a ha
    have ha0 : a = (⟨0, by norm_num⟩ : Fin (4 - 1)) := Fin.ext ha
    rw [ha0]
    have hmemy : conjSub (y' : G) (j ⟨0, by norm_num⟩) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y' : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j ⟨0, by norm_num⟩, mem_centralizingMembers_of_commutes (hjΩ _ (by simp)) c.hz.mem
        (commutes_symm (hjK _)), rfl⟩
    have heq : conjSub (y' : G) (j ⟨0, by norm_num⟩) = J₁ := by
      refine c.eq_of_locImg_eq hmemy hn2z ?_
      rw [locImg_conjSub_layer (j ⟨0, by norm_num⟩) y', hjimg ⟨0, by norm_num⟩, hn2, hlocmk, hr0]
      change Subgroup.map (MulAut.conj (ψ' x)).toMonoidHom (Subgroup.map ψ' _) =
        Subgroup.map ψ' (Subgroup.map (MulAut.conj x).toMonoidHom _)
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext s
      simp [map_mul, map_inv]
    rw [heq]
    exact hβJ₁
  exact PartnerPatternMinus.of_locAut c hjK hjperf hjY hjΩ hjc hjp hjtw hy htz hfix hpair0

end Group

end CFSG.ClassicalInvolution.RouteD.TWT9
