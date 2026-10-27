module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Rec
public import CFSG.ClassicalInvolution.RouteD.TWEB6Twin
public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerBasic
public import CFSG.ClassicalInvolution.RouteD.TwinYSetup
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
open QuadraticMap
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt)
open CFSG.ClassicalInvolution.RouteD.Exotic (commutes_of_commutator_mem_center)

set_option linter.unusedSectionVars false

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {m : ℕ}

theorem imgPair_orth (F₀ : HypFrame Q m) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {i j : Fin m} (hij : i ≠ j) :
    (imgPair F₀ i hg).Orth (imgPair F₀ j hg) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show polar Q (g (F₀.vec i true)) (g (F₀.vec j true)) = 0
    rw [polar_map_of_mem hg]
    exact F₀.polar_vec_of_ne hij true true
  · show polar Q (g (F₀.vec i true)) (g (F₀.vec j false)) = 0
    rw [polar_map_of_mem hg]
    exact F₀.polar_vec_of_ne hij true false
  · show polar Q (g (F₀.vec i false)) (g (F₀.vec j true)) = 0
    rw [polar_map_of_mem hg]
    exact F₀.polar_vec_of_ne hij false true
  · show polar Q (g (F₀.vec i false)) (g (F₀.vec j false)) = 0
    rw [polar_map_of_mem hg]
    exact F₀.polar_vec_of_ne hij false false

theorem negSpace_rootSL2 (hodd : Odd (Nat.card K)) (F₀ : HypFrame Q m) {a b : ℕ} (ha : a < m)
    (hb : b < m) (hab : a ≠ b) (s t : Bool) (x : spinGroup Q)
    (hg : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (hL : IsFundamental Q L i)
    (hLeq : L = ((rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom).map
      (spinAction Q)) :
    negSpace i = hypPlane (imgPair F₀ ⟨a, ha⟩ hg) ⊔ hypPlane (imgPair F₀ ⟨b, hb⟩ hg) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hex : ∀ (j : Fin m) (u : Bool), ∃ P : HypPair Q, P.e = spinAction Q x (F₀.vec j u) ∧
      P.f = spinAction Q x (F₀.vec j (!u)) ∧ hypPlane P = hypPlane (imgPair F₀ j hg) := by
    intro j u
    cases u
    · exact ⟨swapPair (imgPair F₀ j hg), rfl, rfl, hypPlane_swapPair _⟩
    · exact ⟨imgPair F₀ j hg, rfl, rfl, rfl⟩
  obtain ⟨P, hPe, hPf, hPpl⟩ := hex ⟨a, ha⟩ s
  obtain ⟨P', hP'e, hP'f, hP'pl⟩ := hex ⟨b, hb⟩ t
  have hPP' : P.Orth P' := orth_of_polar_hypPlane (by
    rw [hPpl, hP'pl]
    exact polar_hypPlane_of_orth (imgPair_orth F₀ hg (fun h => hab (congrArg Fin.val h))))
  have hrange := La_range_eq_of_pairs F₀ ha hb hab s t x hPP' ⟨hPe, hPf⟩ ⟨hP'e, hP'f⟩
  have hLF : L = (mkFrame P P' hPP').La.range := hLeq.trans hrange.symm
  have hi : i = (mkFrame P P' hPP').La (-1) :=
    IsFundamental.involution_unique hodd hL (hLF ▸ IsFundamental.of_frame (mkFrame P P' hPP'))
  rw [hi, negSpace_La_neg_one h2, frame_span_eq]
  show hypPlane P ⊔ hypPlane P' = _
  rw [hPpl, hP'pl]

theorem commute_of_fixed {X : Type} [Group X] (θ : spinGroup Q →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup Q)) (σ : X ≃* X)
    (α : spinGroup Q ≃* spinGroup Q) (hαθ : ∀ y, θ (α y) = σ (θ y)) {R : Subgroup (spinGroup Q)}
    (hR : ⁅R, R⁆ = R) (hfix : ∀ r ∈ R, σ (θ r) = θ r) {g₀ : V ≃ₗ[K] V}
    (hconj : ∀ y v, spinAction Q (α y) (g₀ v) = g₀ (spinAction Q y v)) :
    ∀ l ∈ R.map (spinAction Q), g₀ * l = l * g₀ := by
  rintro _ ⟨r, hr, rfl⟩
  have hαr : α r = r := eq_of_fixed_of_perfect θ hker α σ hαθ hR hfix r hr
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hconj r v, hαr]

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

theorem scalar_six (c : TCtx p f .POmegaOdd 6 Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z)
    {M : Subgroup G} (hMz : M ∈ centralizingMembers Ω {z}) (nd : DNodes p f 6 Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {Rz : ℕ → Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K}
    {RzM : Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K}
    {x : spinGroup (quadOdd 6 (GaloisField p f))} {tM : Bool}
    {α : spinGroup (quadOdd 6 (GaloisField p f)) ≃* spinGroup (quadOdd 6 (GaloisField p f))}
    {g₀ : (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f)}
    (hRz : ∀ a (h : a < 6), 2 ≤ a →
      Rz a ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 6 p f Fact.out).D ∧
        locImg Ω z (nd.J ⟨a, h⟩) = (Rz a).map c.d.ψ)
    (hRzM : RzM ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 6 p f Fact.out).D ∧
      locImg Ω z M = RzM.map c.d.ψ)
    (hxR : ∀ a (ha : a ≤ 2), Rz (a + 2) = ((rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame a
      (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom))
    (hxM : RzM = ((rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame 4 5 (by omega) (by omega)
      (by omega) true tM).map (MulAut.conj x).toMonoidHom))
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 6 (GaloisField p f)))
    (hg₀2 : g₀ * g₀ = 1)
    (hconj : ∀ y v, spinAction (quadOdd 6 (GaloisField p f)) (α y) (g₀ v) =
      g₀ (spinAction (quadOdd 6 (GaloisField p f)) y v))
    {N₁ N₂ : Subgroup G} (hN₁Ω : N₁ ∈ Ω) (hN₂Ω : N₂ ∈ Ω)
    (hN₁c : ∀ a : Fin 6, a.val < 4 → Commutes N₁ (nd.J a))
    (hN₂c : ∀ a : Fin 6, a.val < 4 → Commutes N₂ (nd.J a))
    (hN₁4 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨4, by omega⟩) N₁)
    (hN₂4 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨4, by omega⟩) N₂)
    (hN₁₂ : ¬ Commutes N₁ N₂) (hne₁₂ : N₁ ≠ N₂)
    {J' : Subgroup G} {w : G} (e' : TwinElt M J' w) (hwM : IsClassicalMember p f M w)
    (hwJ' : IsClassicalMember p f J' w) (hJ'z : J' ∈ centralizingMembers Ω {z})
    (hJ'L : IsLayerMember c J') (hMJ' : M ≠ J')
    (hN₁u : ∀ n ∈ N₁, n * e'.u = e'.u * n) (hN₂u : ∀ n ∈ N₂, n * e'.u = e'.u * n) :
    ∃ ε : GaloisField p f, (ε = 1 ∨ ε = -1) ∧ ∀ y,
      polar (quadOdd 6 (GaloisField p f)) (spinAction (quadOdd 6 (GaloisField p f)) x
        ((oddFrame 6 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ true)) y = 0 →
      polar (quadOdd 6 (GaloisField p f)) (spinAction (quadOdd 6 (GaloisField p f)) x
        ((oddFrame 6 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ false)) y = 0 →
      g₀ y = ε • y := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := c.hodd
  have cq := centralQuot_odd (m := 6) c.hp2 (by norm_num : 3 ≤ 6) c.hq
  have hQ : (polarBilin (quadOdd 6 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 6 (GaloisField p f) h2
  have hdim13 : Module.finrank (GaloisField p f) (Fin 6 ⊕ Fin 6 ⊕ Unit → GaloisField p f) = 13 := by
    rw [finrank_odd]
  set F₀ : HypFrame (quadOdd 6 (GaloisField p f)) 6 := (oddFrame 6 (GaloisField p f)).toHypFrame
    with hF₀
  have hg : spinAction (quadOdd 6 (GaloisField p f)) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd 6 (GaloisField p f)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  let pr : ℕ → HypPair (quadOdd 6 (GaloisField p f)) := fun k =>
    if h : k < 6 then imgPair F₀ ⟨k, h⟩ hg else imgPair F₀ ⟨0, by omega⟩ hg
  have hprk : ∀ k (hk : k < 6), pr k = imgPair F₀ ⟨k, hk⟩ hg := fun k hk => by simp [pr, hk]
  have horth : ∀ a b, a < 6 → b < 6 → a ≠ b → (pr a).Orth (pr b) := fun a b ha hb hab => by
    rw [hprk a ha, hprk b hb]
    exact imgPair_orth F₀ hg (fun h => hab (congrArg Fin.val h))
  have hLf : ∀ a (h : a ≤ 2), ∃ i, IsFundamental (quadOdd 6 (GaloisField p f))
      ((Rz (a + 2)).map (spinAction (quadOdd 6 (GaloisField p f)))) i ∧
      negSpace i = hypPlane (pr a) ⊔ hypPlane (pr (a + 1)) := by
    intro a h
    obtain ⟨i, hi⟩ := cq.map_mem _ (hRz (a + 2) (by omega) (by omega)).1
    refine ⟨i, hi, ?_⟩
    rw [hprk a (by omega), hprk (a + 1) (by omega)]
    exact negSpace_rootSL2 hodd F₀ (by omega : a < 6) (by omega : a + 1 < 6) (by omega) true false
      x hg hi (by rw [hxR a h])
  obtain ⟨i₀, h₀, n₀⟩ := hLf 0 (by norm_num)
  obtain ⟨i₁, h₁, n₁⟩ := hLf 1 (by norm_num)
  obtain ⟨i₂, h₂', n₂⟩ := hLf 2 (by norm_num)
  obtain ⟨iM, hM', nM⟩ : ∃ iM, IsFundamental (quadOdd 6 (GaloisField p f))
      (RzM.map (spinAction (quadOdd 6 (GaloisField p f)))) iM ∧
      negSpace iM = hypPlane (pr 4) ⊔ hypPlane (pr 5) := by
    obtain ⟨i, hi⟩ := cq.map_mem _ hRzM.1
    refine ⟨i, hi, ?_⟩
    rw [hprk 4 (by omega), hprk 5 (by omega)]
    exact negSpace_rootSL2 hodd F₀ (by omega : 4 < 6) (by omega : 5 < 6) (by omega) true tM x hg hi
      (by rw [hxM])
  have hKJ : ∀ a (h : a < 6), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by b6_idx)) (by b6_idx)
  have hmemz : ∀ a (h : a < 6), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hβJ : ∀ a (h : a < 6), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by b6_idx)) (by b6_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hcentJ : ∀ a (h : a < 6), 3 ≤ a → nd.J ⟨a, h⟩ ≤ Subgroup.centralizer ({t} : Set G) :=
    fun a h ha n hn => Subgroup.mem_centralizer_singleton_iff.mpr (hβJ a h ha t ht.mem n hn).symm
  have hcentM : M ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm
  have hcentN : ∀ {N : Subgroup G}, (∀ a : Fin 6, a.val < 4 → Commutes N (nd.J a)) →
      N ≤ Subgroup.centralizer ({t} : Set G) := fun hNc n hn => by
    have := hNc ⟨1, by omega⟩ (by norm_num)
    rw [h1] at this
    exact Subgroup.mem_centralizer_singleton_iff.mpr (this n hn t ht.mem)
  have hfixL : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K},
      L ∈ centralizingMembers Ω {z} → locImg Ω z L = R.map c.d.ψ →
      L ≤ Subgroup.centralizer ({t} : Set G) →
      ∀ r ∈ R, locAut hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r :=
    fun hL hLR hLt r hr => (locAut_fixed_iff hΩ c.hP1 htz hL).mp hLt _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  have hcommg : ∀ {R : Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K},
      R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 6 (GaloisField p f)) →
      (∀ r ∈ R, locAut hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r) →
      ∀ l ∈ R.map (spinAction (quadOdd 6 (GaloisField p f))), g₀ * l = l * g₀ :=
    fun hR hfix => commute_of_fixed c.d.ψ c.d.ker_le (locAut hΩ.conjInvariant htz) α hαθ
      (cq.perf _ hR) hfix hconj
  have f₁ := hcommg (hRz 3 (by omega) (by omega)).1
    (hfixL (hmemz 3 (by omega) (by omega)) (hRz 3 (by omega) (by omega)).2
      (hcentJ 3 (by omega) (by omega)))
  have f₂ := hcommg (hRz 4 (by omega) (by omega)).1
    (hfixL (hmemz 4 (by omega) (by omega)) (hRz 4 (by omega) (by omega)).2
      (hcentJ 4 (by omega) (by omega)))
  have fM := hcommg hRzM.1 (hfixL hMz hRzM.2 hcentM)
  have hbr : ∀ {N : Subgroup G}, N ∈ Ω → (∀ a : Fin 6, a.val < 4 → Commutes N (nd.J a)) →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨4, by omega⟩) N) →
      N ∈ centralizingMembers Ω {z} ∧ ∃ RN ∈ fundamentalSubgroups .POmegaOdd
        (modelUniv .POmegaOdd 6 p f Fact.out).D, locImg Ω z N = RN.map c.d.ψ := by
    intro N hNΩ hNc ⟨W4, hW4⟩
    have hNz : N ∈ centralizingMembers Ω {z} := by
      have := hNc ⟨0, by omega⟩ (by norm_num)
      rw [h0] at this
      exact mem_centralizingMembers_of_commutes hNΩ c.hz.mem this
    have hn4N : ¬ Commutes N (nd.J ⟨4, by omega⟩) := fun h =>
      not_commutes_of_linearBlockStandardPair hW4 (commutes_symm h)
    have hN4ne : N ≠ nd.J ⟨4, by omega⟩ := fun h => ne_of_linearBlockStandardPair hW4 h.symm
    exact ⟨hNz, (IsLayerMember.of_not_commutes c hNz (hmemz 4 (by omega) (by omega)) hN4ne
      hn4N).exists_fund⟩
  obtain ⟨hN₁z, RN₁, hRN₁, hN₁R⟩ := hbr hN₁Ω hN₁c hN₁4
  obtain ⟨hN₂z, RN₂, hRN₂, hN₂R⟩ := hbr hN₂Ω hN₂c hN₂4
  obtain ⟨s₁, hS₁⟩ := cq.map_mem _ hRN₁
  obtain ⟨s₂, hS₂⟩ := cq.map_mem _ hRN₂
  have hbrel : ∀ {N : Subgroup G} {RN : Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K},
      N ∈ centralizingMembers Ω {z} →
      RN ∈ fundamentalSubgroups .POmegaOdd (oddDatum 6 (GaloisField p f)) →
      locImg Ω z N = RN.map c.d.ψ → (∀ a : Fin 6, a.val < 4 → Commutes N (nd.J a)) →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨4, by omega⟩) N) →
      Commutes (RN.map (spinAction (quadOdd 6 (GaloisField p f))))
        ((Rz 2).map (spinAction (quadOdd 6 (GaloisField p f)))) ∧
      Commutes (RN.map (spinAction (quadOdd 6 (GaloisField p f))))
        ((Rz 3).map (spinAction (quadOdd 6 (GaloisField p f)))) ∧
      ¬ Commutes (RN.map (spinAction (quadOdd 6 (GaloisField p f))))
        ((Rz 4).map (spinAction (quadOdd 6 (GaloisField p f)))) := by
    intro N RN hNz hRN hNR hNc ⟨W4, hW4⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (cq.commutes_iff hRN).mpr ((c.commutes_iff_fund hNz (hmemz 2 (by omega) (by omega))
        hRN hNR (hRz 2 (by omega) (by omega)).2).mp (hNc ⟨2, by omega⟩ (by norm_num)))
    · exact (cq.commutes_iff hRN).mpr ((c.commutes_iff_fund hNz (hmemz 3 (by omega) (by omega))
        hRN hNR (hRz 3 (by omega) (by omega)).2).mp (hNc ⟨3, by omega⟩ (by norm_num)))
    · intro h
      have := (c.commutes_iff_fund hNz (hmemz 4 (by omega) (by omega)) hRN hNR
        (hRz 4 (by omega) (by omega)).2).mpr ((cq.commutes_iff hRN).mp h)
      exact not_commutes_of_linearBlockStandardPair hW4 (commutes_symm this)
  obtain ⟨c₁, c₁', d₁⟩ := hbrel hN₁z hRN₁ hN₁R hN₁c hN₁4
  obtain ⟨c₂, c₂', d₂⟩ := hbrel hN₂z hRN₂ hN₂R hN₂c hN₂4
  have hSne : RN₁.map (spinAction (quadOdd 6 (GaloisField p f))) ≠
      RN₂.map (spinAction (quadOdd 6 (GaloisField p f))) := fun e =>
    hne₁₂ (c.eq_of_locImg_eq hN₁z hN₂z (by rw [hN₁R, hN₂R, cq.map_inj hRN₁ hRN₂ e]))
  have hSnc : ¬ Commutes (RN₁.map (spinAction (quadOdd 6 (GaloisField p f))))
      (RN₂.map (spinAction (quadOdd 6 (GaloisField p f)))) := fun h =>
    hN₁₂ ((c.commutes_iff_fund hN₁z hN₂z hRN₁ hN₁R hN₂R).mpr ((cq.commutes_iff hRN₁).mp h))
  have hne : negSpace s₁ ≠ negSpace s₂ := negSpace_ne_of_not_commutes hodd hS₁ hS₂ hSne hSnc
  have fS₁ := hcommg hRN₁ (hfixL hN₁z hN₁R (hcentN hN₁c))
  have fS₂ := hcommg hRN₂ (hfixL hN₂z hN₂R (hcentN hN₂c))
  obtain ⟨RJ, hRJ, hJR⟩ := hJ'L.exists_fund
  have hYM : M ≤ locLayer Ω z := le_centralizingLayer hMz
  have hYJ : J' ≤ locLayer Ω z := le_centralizingLayer hJ'z
  have hwY : w ∈ locLayer Ω z := hYM hwM.mem
  obtain ⟨r, hr, hψr⟩ := exists_involution_of_fund c hMz hRzM.1 hRzM.2 hwM
  obtain ⟨r', hr', hψr'⟩ := exists_involution_of_fund c hJ'z hRJ hJR hwJ'
  have hlcongr : ∀ {y y' : G} (hy : y ∈ locLayer Ω z) (hy' : y' ∈ locLayer Ω z), y = y' →
      locElt Ω z y hy = locElt Ω z y' hy' := by
    intro y y' hy hy' h
    subst h
    rfl
  have hcentral : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K}
      {y : (modelUniv .POmegaOdd 6 p f Fact.out).K}, (∀ k ∈ L, w * k = k * w) →
      locImg Ω z L = R.map c.d.ψ → R ≤ ⁅R, R⁆ → c.d.ψ y = locElt Ω z w hwY →
      ∀ s ∈ R, y * s = s * y := by
    intro L R y hzL hLR hRp hy
    refine commutes_of_commutator_mem_center hRp fun s hs => c.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hy]
    have hsL : c.d.ψ s ∈ locImg Ω z L := hLR ▸ Subgroup.mem_map_of_mem _ hs
    obtain ⟨k, hk, hks⟩ := hsL
    rw [← hks]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    show locMk Ω z ⟨w, hwY⟩ * locMk Ω z k = locMk Ω z k * locMk Ω z ⟨w, hwY⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hzL k (Subgroup.mem_subgroupOf.mp hk)
  have hr1 : r ≠ 1 := fun h => by
    have := hr.2
    rw [h, orderOf_one] at this
    omega
  have hr'1 : r' ≠ 1 := fun h => by
    have := hr'.2
    rw [h, orderOf_one] at this
    omega
  have hsame : r * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd 6 p f Fact.out).K :=
    c.d.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψr, hψr', mul_inv_cancel])
  have haM : locElt Ω z e'.a (hYM e'.mem_a) ∈ locImg Ω z M := locElt_mem_locImg hYM e'.mem_a
  rw [hRzM.2] at haM
  obtain ⟨ã, hãR, hψã⟩ := haM
  have haJ : locElt Ω z e'.a' (hYJ e'.mem_a') ∈ locImg Ω z J' := locElt_mem_locImg hYJ e'.mem_a'
  rw [hJR] at haJ
  obtain ⟨ã', hã'R, hψã'⟩ := haJ
  have hsq : ã * ã * r⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd 6 p f Fact.out).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã, hψr, locElt_mul,
        hlcongr _ hwY e'.mul_self_a, mul_inv_cancel])
  have hsq' : ã' * ã' * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd 6 p f Fact.out).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã', hψr', locElt_mul,
        hlcongr _ hwY e'.mul_self_a', mul_inv_cancel])
  have hne_RJ : RzM ≠ RJ := fun h =>
    hMJ' (c.eq_of_locImg_eq hMz hJ'z (by rw [hRzM.2, hJR, h]))
  obtain ⟨g', iM', hiM', hg'eq, hg'O, hg'2, hg'fix, hg'dim, hg'le, hg'pos⟩ := exists_twin_inv
    c.hp2 c.hq hRzM.1 hRJ hne_RJ hr.1
    (hcentral hwM.isCentralInvolution.central hRzM.2 (c.hY.perfR _ hRzM.1) hψr) hr1 hr'.1
    (hcentral hwJ'.isCentralInvolution.central hJR (c.hY.perfR _ hRJ) hψr') hr'1 hsame hãR hã'R
    hsq hsq'
  have hiMeq : iM' = iM := IsFundamental.involution_unique hodd hiM' hM'
  subst hiMeq
  have hψu : c.d.ψ (ã * ã') = locElt Ω z (e'.a * e'.a')
      ((locLayer Ω z).mul_mem (hYM e'.mem_a) (hYJ e'.mem_a')) := by
    rw [map_mul, hψã, hψã', locElt_mul]
  have hgS : ∀ {N : Subgroup G} {RN : Subgroup (modelUniv .POmegaOdd 6 p f Fact.out).K},
      (∀ n ∈ N, n * e'.u = e'.u * n) → locImg Ω z N = RN.map c.d.ψ → RN ≤ ⁅RN, RN⁆ →
      ∀ l ∈ RN.map (spinAction (quadOdd 6 (GaloisField p f))), g' * l = l * g' := by
    intro N RN hNu hNR hRp
    have hcomm : ∀ s ∈ RN, ã * ã' * s = s * (ã * ã') := by
      refine commutes_of_commutator_mem_center hRp fun s hs => c.d.ker_le ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hψu]
      have hsL : c.d.ψ s ∈ locImg Ω z N := hNR ▸ Subgroup.mem_map_of_mem _ hs
      obtain ⟨k, hk, hks⟩ := hsL
      rw [← hks]
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      show locMk Ω z ⟨e'.a * e'.a', _⟩ * locMk Ω z k = locMk Ω z k * locMk Ω z ⟨e'.a * e'.a', _⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (hNu k (Subgroup.mem_subgroupOf.mp hk)).symm
    rintro _ ⟨s, hs, rfl⟩
    rw [hg'eq, ← map_mul, ← map_mul]
    exact congrArg (spinAction (quadOdd 6 (GaloisField p f))) (hcomm s hs)
  have hS₁g' := hgS hN₁u hN₁R (c.hY.perfR _ hRN₁)
  have hS₂g' := hgS hN₂u hN₂R (c.hY.perfR _ hRN₂)
  obtain ⟨ε, hε, hscal⟩ := g0_scalar hodd hQ hdim13 pr horth h₀ h₁ h₂' hM' hS₁ hS₂ n₀ n₁ n₂ nM
    c₁ c₁' c₂ c₂' d₁ d₂ hne hg₀O hg₀2 f₁ f₂ fM fS₁ fS₂ hg'O hg'2 hS₁g' hS₂g' hg'fix hg'dim hg'le
    hg'pos
  refine ⟨ε, hε, fun y hy1 hy2 => hscal y ?_⟩
  rw [hprk 0 (by omega)]
  exact HypPair.mem_perp.mpr ⟨hy1, hy2⟩

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.B6
