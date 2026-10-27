module

public import CFSG.ClassicalInvolution.RouteD.TWEB4Fix
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.TWE.B6
open QuadraticMap
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)

set_option linter.unusedSectionVars false

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


theorem pattern_b3 (c : TCtx p f .POmegaOdd 3 Ω K z) {β : Subgroup G} {t : G}
    (htz : t * z * t⁻¹ = z) {N₀ : Subgroup G} (hN₀Ω : N₀ ∈ Ω) (hKN : Commutes K N₀)
    (hβN : ∃ W, LinearBlockStandardPair (GaloisField p f) W β N₀)
    {x : spinGroup (quadOdd 3 (GaloisField p f))}
    {α : spinGroup (quadOdd 3 (GaloisField p f)) ≃* spinGroup (quadOdd 3 (GaloisField p f))}
    {g₀ : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)} {ε : GaloisField p f}
    (hn2 : locImg Ω z N₀ =
      ((rootSL2 (oddFrame 3 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)))
    (hconj : ∀ y v, spinAction (quadOdd 3 (GaloisField p f)) (α y) (g₀ v) =
      g₀ (spinAction (quadOdd 3 (GaloisField p f)) y v))
    (hε : ε * ε = 1)
    (hscal : ∀ y,
      polar (quadOdd 3 (GaloisField p f)) (spinAction (quadOdd 3 (GaloisField p f)) x
        ((oddFrame 3 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ true)) y = 0 →
      polar (quadOdd 3 (GaloisField p f)) (spinAction (quadOdd 3 (GaloisField p f)) x
        ((oddFrame 3 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ false)) y = 0 →
      g₀ y = ε • y) :
    PartnerPatternBPair p f 3 Ω K β t := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hm3 : 3 ≤ 3 := by norm_num
  have hF4 : 4 ≤ Nat.card (GaloisField p f) := c.h4
  have hQ : (polarBilin (quadOdd 3 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 3 (GaloisField p f) h2
  obtain ⟨j, hjmem, hjY, hjperf, hjK, hjc, hjp, hjsp, hjimg⟩ := TCtx.exists_nodes_odd_full hm3 c
  obtain ⟨y', hy'⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y' : G) ∈ locLayer Ω z := y'.2
  have hyz : (y' : G) * z * (y' : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hlocmk : locMk Ω z y' = c.d.ψ x := hy'
  let ψ' : ↥(spinGroup (quadOdd 3 (GaloisField p f))) →* locQuot Ω z := c.d.ψ
  set F₀ : HypFrame (quadOdd 3 (GaloisField p f)) 3 := (oddFrame 3 (GaloisField p f)).toHypFrame
    with hF₀
  have hg : spinAction (quadOdd 3 (GaloisField p f)) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have hSperf : ∀ a : Fin 3, rankOne (oddDatum 3 (GaloisField p f)).rootGroup a ≤
      ⁅rankOne (oddDatum 3 (GaloisField p f)).rootGroup a,
        rankOne (oddDatum 3 (GaloisField p f)).rootGroup a⁆ := by
    intro a
    by_cases ha : a.val + 1 < 3
    · exact c.hY.perfR _ (rankOne_mem_fundamentalSubgroups_oddDatum hm3 ha)
    · obtain ⟨Wm, hWm⟩ := symplecticPair_oddDatum (F := GaloisField p f) hF4 h2 hm3
      have ha5 : a = (⟨2, by norm_num⟩ : Fin 3) :=
        Fin.ext (by have := a.isLt; show a.val = 2; omega)
      rw [ha5]
      exact (symplecticBlockPair_perfect hF4 hWm.pair).2
  have hRfix : ∀ a : Fin 3, 1 ≤ a.val → ∀ r ∈ (rankOne (oddDatum 3 (GaloisField p f)).rootGroup
      a).map (MulAut.conj x).toMonoidHom, α r = r := by
    intro a ha
    have hperf : ⁅(rankOne (oddDatum 3 (GaloisField p f)).rootGroup a).map
        (MulAut.conj x).toMonoidHom, (rankOne (oddDatum 3 (GaloisField p f)).rootGroup a).map
        (MulAut.conj x).toMonoidHom⁆ = (rankOne (oddDatum 3 (GaloisField p f)).rootGroup a).map
        (MulAut.conj x).toMonoidHom := by
      rw [← Subgroup.map_commutator]
      exact congrArg (Subgroup.map _) (Subgroup.isPerfect_iff.mp (perfect_of_le_commutator
        (hSperf a)))
    refine eq_of_fixed_of_perfect (spinAction (quadOdd 3 (GaloisField p f)))
      (ker_spinAction_le_center _) α (MulAut.conj g₀) (fun y => ?_) hperf ?_
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
      have hhO : spinAction (quadOdd 3 (GaloisField p f)) ((MulAut.conj x).toMonoidHom s) ∈
          TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)) :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ _ v
      have hfixv : ∀ r, spinAction (quadOdd 3 (GaloisField p f)) ((MulAut.conj x).toMonoidHom s)
          (spinAction (quadOdd 3 (GaloisField p f)) x (F₀.vec ⟨0, by omega⟩ r)) =
          spinAction (quadOdd 3 (GaloisField p f)) x (F₀.vec ⟨0, by omega⟩ r) := by
        intro r
        rw [hshs, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          ← LinearEquiv.mul_apply (spinAction _ x⁻¹), ← map_mul, inv_mul_cancel, map_one]
        show spinAction _ x (spinAction _ s (F₀.vec ⟨0, by omega⟩ r)) = _
        rw [rankOne_fix_vec_zero (by omega) (by omega : 0 < a.val) hs r]
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
  have hfix : ∀ a : Fin 3, 1 ≤ a.val → ∀ u ∈ locImg Ω z (conjSub (y' : G) (j a)),
      locAut hΩ.conjInvariant htz u = u := by
    intro a ha u hu
    rw [locImg_conjSub_layer (j a) y', hjimg a] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨s, hs, rfl⟩ : ∃ s : ↥(spinGroup (quadOdd 3 (GaloisField p f))),
        s ∈ rankOne (oddDatum 3 (GaloisField p f)).rootGroup a ∧ c.d.ψ s = v :=
      Subgroup.mem_map.mp hv
    rw [hlocmk]
    have hαs : α (x * s * x⁻¹) = x * s * x⁻¹ := hRfix a ha _ ⟨s, hs, rfl⟩
    have hu1 : (MulAut.conj (c.d.ψ x)).toMonoidHom (c.d.ψ s) = c.d.ψ (x * s * x⁻¹) := by
      change (MulAut.conj (ψ' x)).toMonoidHom (ψ' s) = ψ' (x * s * x⁻¹)
      simp [map_mul, map_inv]
    rw [hu1, ← hαθ, hαs]
  have hn2z : N₀ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN₀Ω c.hz.mem (commutes_symm hKN)
  have hr0 : rankOne (modelUniv .POmegaOdd 3 p f Fact.out).D.rootGroup (⟨0, by norm_num⟩ : Fin 3) =
      rootSL2 (oddFrame 3 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false :=
    rankOne_oddDatum_of_lt (K := GaloisField p f) (k := ⟨0, by norm_num⟩) (by norm_num)
  have hpair0 : ∀ a : Fin 3, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub (y' : G) (j a)) := by
    intro a ha
    have ha0 : a = (⟨0, by norm_num⟩ : Fin 3) := Fin.ext ha
    rw [ha0]
    have hmemy : conjSub (y' : G) (j ⟨0, by norm_num⟩) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y' : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j ⟨0, by norm_num⟩, (hjmem ⟨0, by norm_num⟩ (by norm_num)).1, rfl⟩
    have heq : conjSub (y' : G) (j ⟨0, by norm_num⟩) = N₀ := by
      refine c.eq_of_locImg_eq hmemy hn2z ?_
      rw [locImg_conjSub_layer (j ⟨0, by norm_num⟩) y', hjimg ⟨0, by norm_num⟩, hn2, hlocmk, hr0]
      change Subgroup.map (MulAut.conj (ψ' x)).toMonoidHom (Subgroup.map ψ' _) =
        Subgroup.map ψ' (Subgroup.map (MulAut.conj x).toMonoidHom _)
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext s
      simp [map_mul, map_inv]
    rw [heq]
    exact hβN
  exact PartnerPatternBPair.of_locAut hΩ c.hP1 (j := j) (fun a ha => (hjmem a ha).1.1) hjY hjK
    hjperf c.locLayer_le_normalizer hjc hjp hjsp hy htz hfix hpair0


end Group

end CFSG.ClassicalInvolution.RouteD.TWE.B3
