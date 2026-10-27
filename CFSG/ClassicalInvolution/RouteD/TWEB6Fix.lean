module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Scalar
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakChain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.CurtisTits
open QuadraticMap
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)

set_option linter.unusedSectionVars false

section Model

variable {n : ℕ} {K : Type} [Field K]

theorem rankOne_fix_vec_zero (hn : 0 < n) {a : Fin n} (ha : 0 < a.val)
    {s : spinGroup (quadOdd n K)} (hs : s ∈ rankOne (oddDatum n K).rootGroup a) (r : Bool) :
    spinAction (quadOdd n K) s ((oddFrame n K).vec ⟨0, hn⟩ r) =
      (oddFrame n K).vec ⟨0, hn⟩ r := by
  let Stab : Subgroup (spinGroup (quadOdd n K)) :=
    { carrier := {g | ∀ r, spinAction (quadOdd n K) g ((oddFrame n K).vec ⟨0, hn⟩ r) =
        (oddFrame n K).vec ⟨0, hn⟩ r}
      mul_mem' := fun {g h} hg hh r => by
        rw [map_mul, LinearEquiv.mul_apply, hh r, hg r]
      one_mem' := fun r => by simp
      inv_mem' := fun {g} hg r => by
        calc spinAction (quadOdd n K) g⁻¹ ((oddFrame n K).vec ⟨0, hn⟩ r)
            = spinAction (quadOdd n K) g⁻¹ (spinAction (quadOdd n K) g
                ((oddFrame n K).vec ⟨0, hn⟩ r)) := by rw [hg r]
          _ = (oddFrame n K).vec ⟨0, hn⟩ r := by
            rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            rfl }
  have hne : (⟨0, hn⟩ : Fin n) ≠ a := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have hle : rankOne (oddDatum n K).rootGroup a ≤ Stab := by
    show oddRootGroup n K (Pi.single a 1) ⊔ oddRootGroup n K (-Pi.single a 1) ≤ Stab
    refine sup_le ?_ ?_
    · rw [oddRootGroup_single]
      rintro _ ⟨c, rfl⟩ r
      obtain ⟨c', rfl⟩ := Multiplicative.ofAdd.surjective c
      by_cases hk : a.val + 1 < n
      · have hkk : a ≠ ⟨a.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
        rw [rootB_of_lt K hk rfl hkk]
        exact (oddFrame n K).spinAction_longRoot_vec_of_ne hkk true false c' hne
          (fun h => by have := congrArg Fin.val h; simp at this) r
      · rw [rootB_of_not_lt K hk]
        exact (oddFrame n K).spinAction_shortRoot_vec_of_ne a true c' hne r
    · rw [oddRootGroup_neg_single]
      rintro _ ⟨c, rfl⟩ r
      obtain ⟨c', rfl⟩ := Multiplicative.ofAdd.surjective c
      by_cases hk : a.val + 1 < n
      · have hkk : (⟨a.val + 1, hk⟩ : Fin n) ≠ a := Fin.ne_of_val_ne (by simp)
        rw [negRootB_of_lt K hk rfl hkk]
        exact (oddFrame n K).spinAction_longRoot_vec_of_ne hkk true false c'
          (fun h => by have := congrArg Fin.val h; simp at this)
          hne r
      · rw [negRootB_of_not_lt K hk]
        exact (oddFrame n K).spinAction_shortRoot_vec_of_ne a false _ hne r
  exact hle hs r

end Model

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


local macro "b6_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem pattern_six (c : TCtx p f .POmegaOdd 6 Ω K z) {β : Subgroup G} {t : G}
    (htz : t * z * t⁻¹ = z) {M : Subgroup G}
    (nd : DNodes p f 6 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {x : spinGroup (quadOdd 6 (GaloisField p f))}
    {α : spinGroup (quadOdd 6 (GaloisField p f)) ≃* spinGroup (quadOdd 6 (GaloisField p f))}
    {g₀ : (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f)} {ε : GaloisField p f}
    (hn2 : locImg Ω z (nd.J ⟨2, by omega⟩) =
      ((rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 6 (GaloisField p f)))
    (hconj : ∀ y v, spinAction (quadOdd 6 (GaloisField p f)) (α y) (g₀ v) =
      g₀ (spinAction (quadOdd 6 (GaloisField p f)) y v))
    (hε : ε * ε = 1)
    (hscal : ∀ y,
      polar (quadOdd 6 (GaloisField p f)) (spinAction (quadOdd 6 (GaloisField p f)) x
        ((oddFrame 6 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ true)) y = 0 →
      polar (quadOdd 6 (GaloisField p f)) (spinAction (quadOdd 6 (GaloisField p f)) x
        ((oddFrame 6 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ false)) y = 0 →
      g₀ y = ε • y) :
    PartnerPatternBPair p f 6 Ω K β t := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hm3 : 3 ≤ 6 := by norm_num
  have hF4 : 4 ≤ Nat.card (GaloisField p f) := c.h4
  have hQ : (polarBilin (quadOdd 6 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 6 (GaloisField p f) h2
  obtain ⟨j, hjmem, hjY, hjperf, hjK, hjc, hjp, hjsp, hjimg⟩ := TCtx.exists_nodes_odd_full hm3 c
  obtain ⟨y', hy'⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y' : G) ∈ locLayer Ω z := y'.2
  have hyz : (y' : G) * z * (y' : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hlocmk : locMk Ω z y' = c.d.ψ x := hy'
  let ψ' : ↥(spinGroup (quadOdd 6 (GaloisField p f))) →* locQuot Ω z := c.d.ψ
  set F₀ : HypFrame (quadOdd 6 (GaloisField p f)) 6 := (oddFrame 6 (GaloisField p f)).toHypFrame
    with hF₀
  have hg : spinAction (quadOdd 6 (GaloisField p f)) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd 6 (GaloisField p f)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have hSperf : ∀ a : Fin 6, rankOne (oddDatum 6 (GaloisField p f)).rootGroup a ≤
      ⁅rankOne (oddDatum 6 (GaloisField p f)).rootGroup a,
        rankOne (oddDatum 6 (GaloisField p f)).rootGroup a⁆ := by
    intro a
    by_cases ha : a.val + 1 < 6
    · exact c.hY.perfR _ (rankOne_mem_fundamentalSubgroups_oddDatum hm3 ha)
    · obtain ⟨Wm, hWm⟩ := symplecticPair_oddDatum (F := GaloisField p f) hF4 h2 hm3
      have ha5 : a = (⟨5, by norm_num⟩ : Fin 6) :=
        Fin.ext (by have := a.isLt; show a.val = 5; omega)
      rw [ha5]
      exact (symplecticBlockPair_perfect hF4 hWm.pair).2
  have hRfix : ∀ a : Fin 6, 1 ≤ a.val → ∀ r ∈ (rankOne (oddDatum 6 (GaloisField p f)).rootGroup
      a).map (MulAut.conj x).toMonoidHom, α r = r := by
    intro a ha
    have hperf : ⁅(rankOne (oddDatum 6 (GaloisField p f)).rootGroup a).map
        (MulAut.conj x).toMonoidHom, (rankOne (oddDatum 6 (GaloisField p f)).rootGroup a).map
        (MulAut.conj x).toMonoidHom⁆ = (rankOne (oddDatum 6 (GaloisField p f)).rootGroup a).map
        (MulAut.conj x).toMonoidHom := by
      rw [← Subgroup.map_commutator]
      exact congrArg (Subgroup.map _) (Subgroup.isPerfect_iff.mp (perfect_of_le_commutator
        (hSperf a)))
    refine eq_of_fixed_of_perfect (spinAction (quadOdd 6 (GaloisField p f)))
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
      have hhO : spinAction (quadOdd 6 (GaloisField p f)) ((MulAut.conj x).toMonoidHom s) ∈
          TauCeti.QuadraticMap.orthogonalGroup (quadOdd 6 (GaloisField p f)) :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ _ v
      have hfixv : ∀ r, spinAction (quadOdd 6 (GaloisField p f)) ((MulAut.conj x).toMonoidHom s)
          (spinAction (quadOdd 6 (GaloisField p f)) x (F₀.vec ⟨0, by omega⟩ r)) =
          spinAction (quadOdd 6 (GaloisField p f)) x (F₀.vec ⟨0, by omega⟩ r) := by
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
  have hfix : ∀ a : Fin 6, 1 ≤ a.val → ∀ u ∈ locImg Ω z (conjSub (y' : G) (j a)),
      locAut hΩ.conjInvariant htz u = u := by
    intro a ha u hu
    rw [locImg_conjSub_layer (j a) y', hjimg a] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨s, hs, rfl⟩ : ∃ s : ↥(spinGroup (quadOdd 6 (GaloisField p f))),
        s ∈ rankOne (oddDatum 6 (GaloisField p f)).rootGroup a ∧ c.d.ψ s = v :=
      Subgroup.mem_map.mp hv
    rw [hlocmk]
    have hαs : α (x * s * x⁻¹) = x * s * x⁻¹ := hRfix a ha _ ⟨s, hs, rfl⟩
    have hu1 : (MulAut.conj (c.d.ψ x)).toMonoidHom (c.d.ψ s) = c.d.ψ (x * s * x⁻¹) := by
      change (MulAut.conj (ψ' x)).toMonoidHom (ψ' s) = ψ' (x * s * x⁻¹)
      simp [map_mul, map_inv]
    rw [hu1, ← hαθ, hαs]
  have hKJ2 : Commutes K (nd.J ⟨2, by omega⟩) := by
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by b6_idx)) (by b6_idx)
  have hn2z : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem (commutes_symm hKJ2)
  have hr0 : rankOne (modelUniv .POmegaOdd 6 p f Fact.out).D.rootGroup (⟨0, by norm_num⟩ : Fin 6) =
      rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false :=
    rankOne_oddDatum_of_lt (K := GaloisField p f) (k := ⟨0, by norm_num⟩) (by norm_num)
  have hpair0 : ∀ a : Fin 6, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub (y' : G) (j a)) := by
    intro a ha
    have ha0 : a = (⟨0, by norm_num⟩ : Fin 6) := Fin.ext ha
    rw [ha0]
    have hmemy : conjSub (y' : G) (j ⟨0, by norm_num⟩) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y' : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j ⟨0, by norm_num⟩, (hjmem ⟨0, by norm_num⟩ (by norm_num)).1, rfl⟩
    have heq : conjSub (y' : G) (j ⟨0, by norm_num⟩) = nd.J ⟨2, by omega⟩ := by
      refine c.eq_of_locImg_eq hmemy hn2z ?_
      rw [locImg_conjSub_layer (j ⟨0, by norm_num⟩) y', hjimg ⟨0, by norm_num⟩, hn2, hlocmk, hr0]
      change Subgroup.map (MulAut.conj (ψ' x)).toMonoidHom (Subgroup.map ψ' _) =
        Subgroup.map ψ' (Subgroup.map (MulAut.conj x).toMonoidHom _)
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext s
      simp [map_mul, map_inv]
    rw [heq]
    obtain ⟨W, hW⟩ := nd.pair_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by b6_idx)
    rw [h1] at hW
    exact ⟨W, hW⟩
  exact PartnerPatternBPair.of_locAut hΩ c.hP1 (j := j) (fun a ha => (hjmem a ha).1.1) hjY hjK
    hjperf c.locLayer_le_normalizer hjc hjp hjsp hy htz hfix hpair0

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.B6
