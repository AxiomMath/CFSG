module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBExtra
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

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open scoped MatrixGroups

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_dnodes_extra_leaf_odd_ge5 {m : ℕ} (hm : 5 ≤ m) (c : TCtx p f .POmegaOdd m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes p f m Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β ∧
      ∃ N₁ : Subgroup G, N₁ ∈ Ω ∧ Commutes K N₁ ∧ Commutes β N₁ ∧ Commutes M N₁ ∧
        (∀ a (h : a < m), a + 3 < m → Commutes (nd.J ⟨a, h⟩) N₁) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨m - 3, by omega⟩) N₁) ∧
        N₁ ≠ nd.J ⟨m - 2, by omega⟩ ∧ N₁ ≠ nd.J ⟨m - 1, by omega⟩ := by
  classical
  have hm3 : 3 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hq4 : 4 ≤ p ^ f := by have := c.hq; omega
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hMΩ
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hxM
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hKL := IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaOdd m p f Fact.out).K) RK Rβ :=
    modelAdj_of_adj cx hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hF := orthFacts_odd c.hp2 hm4 c.hq
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  have cq := centralQuot_odd (m := m) (f := f) c.hp2 hm3 c.hq
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hQ : (quadOdd m (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadOdd m (GaloisField p f) h2)
  let F₀ : HypFrame (quadOdd m (GaloisField p f)) m := (oddFrame m (GaloisField p f)).toHypFrame
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair_gen c.hp2 c.hq hQ hm4 F₀ hdim cq hRK hRβ hadj hlinR
  let a0 : Fin m := ⟨0, by omega⟩
  let a1 : Fin m := ⟨1, by omega⟩
  have hRfund : ∀ k, dNode hm3 F₀ x₀ k ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd m p f Fact.out).D := by
    intro k
    by_cases h : k.val + 1 < m
    · rw [dNode_lt hm3 F₀ x₀ k h]
      exact rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ _ _ x₀
    · rw [dNode_last hm3 F₀ x₀ k h]
      exact rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ _ _ x₀
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes (fun k => dNode hm3 F₀ x₀ k) hRfund
    (fun a b => edgeD m a b) (fun a b hab h1 h2' => commutes_dNode hm3 F₀ x₀ hab h1 h2')
    (fun a b h => stdPair_dNode_odd hm3 x₀ h)
  have hR0 : dNode hm3 F₀ x₀ a0 = RK := by
    rw [dNode_lt hm3 F₀ x₀ a0 (by show 0 + 1 < m; omega)]
    exact hx0.symm
  have hR1 : dNode hm3 F₀ x₀ a1 = Rβ := by
    rw [dNode_lt hm3 F₀ x₀ a1 (by show 1 + 1 < m; omega)]
    exact hx1.symm
  have hex : ∀ a, ∃ w, IsClassicalMember p f (j a) w := fun a =>
    c.hΩ.classical _ (hj a).1.1
  choose w hw using hex
  let nd : DNodes p f m Ω M :=
    { J := j
      w := w
      mem := fun a => (hj a).1.1
      cl := hw
      commK := hjM
      comm := hjc
      pair := hjp }
  let kk : Fin m := ⟨m - 2 + 1, by omega⟩
  let s₀ : spinGroup (quadOdd m (GaloisField p f)) :=
    (oddFrame m (GaloisField p f)).shortRoot kk true (Multiplicative.ofAdd 1)
  let s' : spinGroup (quadOdd m (GaloisField p f)) := x₀ * s₀ * x₀⁻¹
  have hs'x : s' * x₀ = x₀ * s₀ := by simp only [s']; group
  let bn : Fin m := ⟨m - 2, by omega⟩
  let R₁ := conjSub s' (dNode hm3 F₀ x₀ bn)
  have hR₁ : R₁ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D :=
    conjSub_mem_fundamentalSubgroups (hRfund bn) s'
  obtain ⟨N₁, hN₁x, hN₁M, -, hN₁R⟩ := cx.exists_member_of_fund hR₁
  have hconjT : ∀ a : Fin m, a.val + 2 < m →
      conjSub s' (dNode hm3 F₀ x₀ a) = dNode hm3 F₀ x₀ a := by
    intro a ha
    have ha1 : a.val + 1 < m := by omega
    have hT : conjSub s₀ (rootSL2 F₀ a.val (a.val + 1) a.isLt ha1 (by omega) true false) =
        rootSL2 F₀ a.val (a.val + 1) a.isLt ha1 (by omega) true false :=
      conjSub_eq_of_mem_of_commutes (Subgroup.mem_zpowers s₀)
        (commutes_zpowers_shortRoot_rootSL2 kk a.isLt ha1 (by omega)
          (by simp only [kk]; omega) (by simp only [kk]; omega) true false true 1)
    rw [dNode_lt hm3 F₀ x₀ a ha1]
    show conjSub s' (conjSub x₀ _) = conjSub x₀ _
    rw [← conjSub_mul, hs'x, conjSub_mul, hT]
  have hR₁eq : R₁ = conjSub x₀ (conjSub s₀
      (rootSL2 F₀ (m - 2) (m - 2 + 1) (by omega) (by omega) (by omega) true false)) := by
    show conjSub s' (dNode hm3 F₀ x₀ bn) = _
    rw [dNode_lt hm3 F₀ x₀ bn (by show m - 2 + 1 < m; omega)]
    show conjSub s' (conjSub x₀ _) = _
    rw [← conjSub_mul, hs'x, conjSub_mul]
  obtain ⟨hne1, hne2⟩ := conjSub_short_ne_rootSL2 c.hodd (oddFrame m (GaloisField p f))
    (a := m - 2) (b := m - 2 + 1) (by omega) (by omega) (by omega)
  have hinjc : ∀ A B : Subgroup (spinGroup (quadOdd m (GaloisField p f))),
      conjSub x₀ A = conjSub x₀ B → A = B := by
    intro A B e
    have := congrArg (conjSub x₀⁻¹) e
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hbn : dNode hm3 F₀ x₀ bn = conjSub x₀
      (rootSL2 F₀ (m - 2) (m - 2 + 1) (by omega) (by omega) (by omega) true false) :=
    dNode_lt hm3 F₀ x₀ bn (by show m - 2 + 1 < m; omega)
  let fn : Fin m := ⟨m - 1, by omega⟩
  have hfn : dNode hm3 F₀ x₀ fn = conjSub x₀
      (rootSL2 F₀ (m - 2) (m - 2 + 1) (by omega) (by omega) (by omega) true true) :=
    dNode_last hm3 F₀ x₀ fn (by show ¬ m - 1 + 1 < m; omega)
  have hR₁b : R₁ ≠ dNode hm3 F₀ x₀ bn := by
    intro e
    rw [hR₁eq, hbn] at e
    exact hne1 (hinjc _ _ e)
  have hR₁f : R₁ ≠ dNode hm3 F₀ x₀ fn := by
    intro e
    rw [hR₁eq, hfn] at e
    exact hne2 (hinjc _ _ e)
  have hmodelc : ∀ a : Fin m, a.val + 3 < m → Commutes (dNode hm3 F₀ x₀ a) R₁ := by
    intro a ha
    have h1 : Commutes (dNode hm3 F₀ x₀ a) (dNode hm3 F₀ x₀ bn) :=
      commutes_dNode hm3 F₀ x₀ (fin_ne_of_val_ne (by simp only [bn]; omega))
        (by intro h; unfold edgeD at h; simp only [bn] at h; omega)
        (by intro h; unfold edgeD at h; simp only [bn] at h; omega)
    have h2 := h1.conjSub s'
    rwa [hconjT a (by omega)] at h2
  have hN₁Ω : N₁ ∈ Ω := hN₁x.1
  have hN₁K : Commutes K N₁ := (cx.commutes_iff_fund hKx hN₁x hRK hKR hN₁R).mpr (by
    rw [← hR0]
    exact hmodelc a0 (by show 0 + 3 < m; omega))
  have hN₁β : Commutes β N₁ := (cx.commutes_iff_fund hβx hN₁x hRβ hβR hN₁R).mpr (by
    rw [← hR1]
    exact hmodelc a1 (by show 1 + 3 < m; omega))
  have hN₁Mc : Commutes M N₁ := cx.commutes_K_of_ne hN₁x hN₁M
  have hN₁c : ∀ a (h : a < m), a + 3 < m → Commutes (nd.J ⟨a, h⟩) N₁ :=
    fun a h ha =>
      (cx.commutes_iff_fund (hj ⟨a, h⟩).1 hN₁x (hRfund ⟨a, h⟩) (hj ⟨a, h⟩).2.2.2 hN₁R).mpr
        (hmodelc ⟨a, h⟩ ha)
  obtain ⟨W₁, hW₁⟩ : ∃ W, LinearBlockStandardPair (GaloisField p f) W
      (dNode hm3 F₀ x₀ ⟨m - 3, by omega⟩) (dNode hm3 F₀ x₀ bn) :=
    stdPair_dNode_odd hm3 x₀ (a := ⟨m - 3, by omega⟩) (b := bn)
      (Or.inl ⟨by show m - 3 + 1 = m - 2; omega, by show m - 2 + 1 < m; omega⟩)
  have hW₂ : LinearBlockStandardPair (GaloisField p f) _
      (conjSub s' (dNode hm3 F₀ x₀ ⟨m - 3, by omega⟩)) R₁ :=
    CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ s'
  rw [hconjT ⟨m - 3, by omega⟩ (by show m - 3 + 2 < m; omega)] at hW₂
  have hN₁adj : ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨m - 3, by omega⟩) N₁ :=
    cx.stdPair_of_fund (hj ⟨m - 3, by omega⟩).1 hN₁x hW₂ (hj ⟨m - 3, by omega⟩).2.2.2 hN₁R
  have hperf : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)),
      ⁅R, R⁆ = R := cq.perf
  have hN₁2 : N₁ ≠ nd.J ⟨m - 2, by omega⟩ := by
    intro e
    have hloc : locImg Ω xM N₁ = locImg Ω xM (j ⟨m - 2, by omega⟩) := by
      rw [show N₁ = j ⟨m - 2, by omega⟩ from e]
    rw [hN₁R, (hj ⟨m - 2, by omega⟩).2.2.2] at hloc
    exact hR₁b (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect cx.d.ψ
      cx.d.ker_le (hperf _ hR₁) (hperf _ (hRfund bn)) hloc)
  have hN₁1 : N₁ ≠ nd.J ⟨m - 1, by omega⟩ := by
    intro e
    have hloc : locImg Ω xM N₁ = locImg Ω xM (j ⟨m - 1, by omega⟩) := by
      rw [show N₁ = j ⟨m - 1, by omega⟩ from e]
    rw [hN₁R, (hj ⟨m - 1, by omega⟩).2.2.2] at hloc
    exact hR₁f (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect cx.d.ψ
      cx.d.ker_le (hperf _ hR₁) (hperf _ (hRfund fn)) hloc)
  refine ⟨nd, ?_, ?_, N₁, hN₁Ω, hN₁K, hN₁β, hN₁Mc, hN₁c, hN₁adj, hN₁2, hN₁1⟩
  · exact cx.eq_of_locImg_eq (hj a0).1 hKx (by rw [(hj a0).2.2.2, hR0, hKR])
  · exact cx.eq_of_locImg_eq (hj a1).1 hβx (by rw [(hj a1).2.2.2, hR1, hβR])

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
