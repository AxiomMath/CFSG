module

public import CFSG.ClassicalInvolution.RouteD.TWED6Scalar
public import CFSG.ClassicalInvolution.RouteD.TypeDChain
public import CFSG.ClassicalInvolution.RouteD.TypeDAdapt
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.D6

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TWE.B6 CFSG.LieType.CurtisTits
open QuadraticMap

set_option linter.unusedSectionVars false

section Model

variable {n : ℕ} {K : Type} [Field K]

theorem rankOne_fix_vec_zero_plus (hn : 3 ≤ n) {a : Fin n} (ha : 0 < a.val)
    {s : spinGroup (quadPlus n K)} (hs : s ∈ rankOne (plusDatum n K hn).rootGroup a) (r : Bool) :
    spinAction (quadPlus n K) s ((plusFrame n K hn).vec ⟨0, by omega⟩ r) =
      (plusFrame n K hn).vec ⟨0, by omega⟩ r := by
  let Stab : Subgroup (spinGroup (quadPlus n K)) :=
    { carrier := {g | ∀ r, spinAction (quadPlus n K) g ((plusFrame n K hn).vec ⟨0, by omega⟩ r) =
        (plusFrame n K hn).vec ⟨0, by omega⟩ r}
      mul_mem' := fun {g h} hg hh r => by
        rw [map_mul, LinearEquiv.mul_apply, hh r, hg r]
      one_mem' := fun r => by simp
      inv_mem' := fun {g} hg r => by
        calc spinAction (quadPlus n K) g⁻¹ ((plusFrame n K hn).vec ⟨0, by omega⟩ r)
            = spinAction (quadPlus n K) g⁻¹ (spinAction (quadPlus n K) g
                ((plusFrame n K hn).vec ⟨0, by omega⟩ r)) := by rw [hg r]
          _ = (plusFrame n K hn).vec ⟨0, by omega⟩ r := by
            rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            rfl }
  have hi : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD n a := fun h => by
    have h1 := congrArg Fin.val h
    by_cases hk : a.val + 1 < n
    · simp [rootIdxD, hk] at h1
      omega
    · simp [rootIdxD, hk] at h1
      have := a.isLt
      omega
  have hj : (⟨0, by omega⟩ : Fin n) ≠ rootIdxD' n a := fun h => by
    have h1 := congrArg Fin.val h
    have h2 := val_rootIdxD' n (by omega) a
    simp at h1
    omega
  have hle : rankOne (plusDatum n K hn).rootGroup a ≤ Stab := by
    rw [show rankOne (plusDatum n K hn).rootGroup a = (rankOneD K hn a).range from
      PlusCT.rankOne_plusRootGroup hn a]
    show ((plusFrame n K hn).longSL2 (rootIdxD_ne n (by omega) a) true (rootSignD n a)).range ≤
      Stab
    rw [longSL2_range_eq_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩ r
      obtain ⟨c', rfl⟩ := Multiplicative.ofAdd.surjective c
      exact (plusFrame n K hn).spinAction_longRoot_vec_of_ne _ true (rootSignD n a) c' hi hj r
    · rintro _ ⟨c, rfl⟩ r
      obtain ⟨c', rfl⟩ := Multiplicative.ofAdd.surjective c
      exact (plusFrame n K hn).spinAction_longRoot_vec_of_ne _ (!rootSignD n a) (!true) c' hj hi r
  exact hle hs r

end Model

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


local macro "d6_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem pattern_plus_six (c : TCtx p f .POmegaPlus 6 Ω K z) {β : Subgroup G} {t : G}
    (htz : t * z * t⁻¹ = z) {M : Subgroup G}
    (nd : DNodes p f 6 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {x : spinGroup (quadPlus 6 (GaloisField p f))}
    {α : spinGroup (quadPlus 6 (GaloisField p f)) ≃* spinGroup (quadPlus 6 (GaloisField p f))}
    {g₀ : (Fin 6 ⊕ Fin 6 → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 6 ⊕ Fin 6 → GaloisField p f)}
    (hn2 : locImg Ω z (nd.J ⟨2, by omega⟩) =
      ((rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField p f)))
    (hconj : ∀ y v, spinAction (quadPlus 6 (GaloisField p f)) (α y) (g₀ v) =
      g₀ (spinAction (quadPlus 6 (GaloisField p f)) y v))
    (hscal : ∀ y,
      polar (quadPlus 6 (GaloisField p f)) (spinAction (quadPlus 6 (GaloisField p f)) x
        ((plusFrame 6 (GaloisField p f) (by norm_num)).vec ⟨0, by omega⟩ true)) y = 0 →
      polar (quadPlus 6 (GaloisField p f)) (spinAction (quadPlus 6 (GaloisField p f)) x
        ((plusFrame 6 (GaloisField p f) (by norm_num)).vec ⟨0, by omega⟩ false)) y = 0 →
      g₀ y = y) :
    PartnerPatternD p f 6 Ω K β t := by
  classical
  have hΩ := c.hΩ
  have hm3 : 3 ≤ 6 := by norm_num
  have hQ : (polarBilin (quadPlus 6 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadPlus 6 (GaloisField p f)
  obtain ⟨j, hjmem, hjimg, hjK, hjc, hjp⟩ :=
    TCtx.exists_nodes_plus' (by norm_num : 4 ≤ 6) c (Equiv.refl _) (fun _ _ => rfl)
  obtain ⟨y', hy'⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y' : G) ∈ locLayer Ω z := y'.2
  have hyz : (y' : G) * z * (y' : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hlocmk : locMk Ω z y' = c.d.ψ x := hy'
  let ψ' : ↥(spinGroup (quadPlus 6 (GaloisField p f))) →* locQuot Ω z := c.d.ψ
  set F₀ : HypFrame (quadPlus 6 (GaloisField p f)) 6 := plusFrame 6 (GaloisField p f) hm3
    with hF₀
  have hg : spinAction (quadPlus 6 (GaloisField p f)) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField p f)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have hSperf : ∀ a : Fin 6, rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup a ≤
      ⁅rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup a,
        rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup a⁆ := fun a =>
    c.hY.perfR _ (rankOne_mem_fundamentalSubgroups_plusDatum hm3 a)
  have hRfix : ∀ a : Fin 6, 1 ≤ a.val → ∀ r ∈ (rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup
      a).map (MulAut.conj x).toMonoidHom, α r = r := by
    intro a ha
    have hperf : ⁅(rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup a).map
        (MulAut.conj x).toMonoidHom, (rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup a).map
        (MulAut.conj x).toMonoidHom⁆ = (rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup
          a).map (MulAut.conj x).toMonoidHom := by
      rw [← Subgroup.map_commutator]
      exact congrArg (Subgroup.map _) (Subgroup.isPerfect_iff.mp (perfect_of_le_commutator
        (hSperf a)))
    refine eq_of_fixed_of_perfect (spinAction (quadPlus 6 (GaloisField p f)))
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
      have hhO : spinAction (quadPlus 6 (GaloisField p f)) ((MulAut.conj x).toMonoidHom s) ∈
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField p f)) :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ _ v
      have hfixv : ∀ r, spinAction (quadPlus 6 (GaloisField p f)) ((MulAut.conj x).toMonoidHom s)
          (spinAction (quadPlus 6 (GaloisField p f)) x (F₀.vec ⟨0, by omega⟩ r)) =
          spinAction (quadPlus 6 (GaloisField p f)) x (F₀.vec ⟨0, by omega⟩ r) := by
        intro r
        rw [hshs, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          ← LinearEquiv.mul_apply (spinAction _ x⁻¹), ← map_mul, inv_mul_cancel, map_one]
        show spinAction _ x (spinAction _ s (F₀.vec ⟨0, by omega⟩ r)) = _
        rw [rankOne_fix_vec_zero_plus hm3 (by omega : 0 < a.val) hs r]
      have hcomm := commute_of_scalar_on_perp hQ (imgPair F₀ ⟨0, by omega⟩ hg) hg₀O hhO
        (ε := 1) (one_mul 1)
        (fun y hy => by
          rw [one_smul]
          exact hscal y (HypPair.mem_perp.mp hy).1 (HypPair.mem_perp.mp hy).2)
        (fun q hq => by
          obtain ⟨a₁, b₁, rfl⟩ := (mem_hypPlane_iff _).mp hq
          rw [map_add, map_smul, map_smul]
          exact congrArg₂ (· + ·) (congrArg (a₁ • ·) (hfixv true))
            (congrArg (b₁ • ·) (hfixv false)))
      show g₀ * spinAction _ _ * g₀⁻¹ = _
      rw [hcomm]
      group
  have hfix : ∀ a : Fin 6, 1 ≤ a.val → ∀ u ∈ locImg Ω z (conjSub (y' : G) (j a)),
      locAut hΩ.conjInvariant htz u = u := by
    intro a ha u hu
    rw [locImg_conjSub_layer (j a) y', hjimg a] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨s, hs, rfl⟩ : ∃ s : ↥(spinGroup (quadPlus 6 (GaloisField p f))),
        s ∈ rankOne (plusDatum 6 (GaloisField p f) hm3).rootGroup a ∧ c.d.ψ s = v :=
      Subgroup.mem_map.mp hv
    rw [hlocmk]
    have hαs : α (x * s * x⁻¹) = x * s * x⁻¹ := hRfix a ha _ ⟨s, hs, rfl⟩
    have hu1 : (MulAut.conj (c.d.ψ x)).toMonoidHom (c.d.ψ s) = c.d.ψ (x * s * x⁻¹) := by
      change (MulAut.conj (ψ' x)).toMonoidHom (ψ' s) = ψ' (x * s * x⁻¹)
      simp [map_mul, map_inv]
    rw [hu1, ← hαθ, hαs]
  have hKJ2 : Commutes K (nd.J ⟨2, by omega⟩) := by
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by d6_idx)) (by d6_idx)
  have hn2z : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem (commutes_symm hKJ2)
  have hr0 : rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup
      (⟨0, by norm_num⟩ : Fin 6) =
      rootSL2 (plusFrame 6 (GaloisField p f) hm3) 0 1 (by omega) (by omega) (by omega)
        true false :=
    rankOne_plusDatum_of_lt (K := GaloisField p f) (m := 6) hm3 (k := ⟨0, by norm_num⟩)
      (by norm_num)
  have hpair0 : ∀ a : Fin 6, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub (y' : G) (j a)) := by
    intro a ha
    have ha0 : a = (⟨0, by norm_num⟩ : Fin 6) := Fin.ext ha
    rw [ha0]
    have hmemy : conjSub (y' : G) (j (⟨0, by norm_num⟩ : Fin 6)) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y' : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j (⟨0, by norm_num⟩ : Fin 6), (hjmem (⟨0, by norm_num⟩ : Fin 6)).1, rfl⟩
    have heq : conjSub (y' : G) (j (⟨0, by norm_num⟩ : Fin 6)) = nd.J ⟨2, by omega⟩ := by
      refine c.eq_of_locImg_eq hmemy hn2z ?_
      rw [locImg_conjSub_layer (j (⟨0, by norm_num⟩ : Fin 6)) y',
        hjimg (⟨0, by norm_num⟩ : Fin 6), hn2, hlocmk, hr0]
      change Subgroup.map (MulAut.conj (ψ' x)).toMonoidHom (Subgroup.map ψ' _) =
        Subgroup.map ψ' (Subgroup.map (MulAut.conj x).toMonoidHom _)
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext s
      simp [map_mul, map_inv]
    rw [heq]
    obtain ⟨W, hW⟩ := nd.pair_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by d6_idx)
    rw [h1] at hW
    exact ⟨W, hW⟩
  exact PartnerPatternD.of_locAut c (j := j) (fun a => (hjmem a).1) hjK hjc hjp hy htz hfix hpair0

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.D6
