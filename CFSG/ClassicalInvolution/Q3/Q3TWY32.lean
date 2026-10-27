module

public import CFSG.ClassicalInvolution.Q3.Q3TWY31
public import CFSG.ClassicalInvolution.Q3.Q3TWY21
public import CFSG.ClassicalInvolution.Q3.Q3TWY12
public import CFSG.ClassicalInvolution.RouteD.TWEB6Scalar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Timmesfeld
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


section Scalar

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {M : Subgroup G}

theorem scalar_odd3 {u : ℕ} (c : TCtx3 .POmegaOdd (u + 5) Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z) (hMz : M ∈ centralizingMembers Ω {z})
    (nd : DNodes3 (u + 5) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {Rz : ℕ → Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    {RzM : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    (hch : LayerChain3 c nd Rz RzM) {x : spinGroup (quadOdd (u + 5) 𝔽₃)} {tM : Bool}
    {α : spinGroup (quadOdd (u + 5) 𝔽₃) ≃* spinGroup (quadOdd (u + 5) 𝔽₃)}
    {g₀ : (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃] (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃)}
    (hxR : ∀ a (ha : a ≤ u + 1), Rz (a + 2) = ((rootSL2 (oddFrame (u + 5) 𝔽₃).toHypFrame a
      (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom))
    (hxM : RzM = ((rootSL2 (oddFrame (u + 5) 𝔽₃).toHypFrame (u + 3) (u + 4) (by omega)
      (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom))
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd (u + 5) 𝔽₃)) (hg₀2 : g₀ * g₀ = 1)
    (hconj : ∀ y v, spinAction (quadOdd (u + 5) 𝔽₃) (α y) (g₀ v) =
      g₀ (spinAction (quadOdd (u + 5) 𝔽₃) y v))
    {N₁ N₂ : Subgroup G} (hN₁Ω : N₁ ∈ Ω) (hN₂Ω : N₂ ∈ Ω)
    (hN₁c : ∀ a : Fin (u + 5), a.val < u + 3 → Commutes N₁ (nd.J a))
    (hN₂c : ∀ a : Fin (u + 5), a.val < u + 3 → Commutes N₂ (nd.J a))
    (hN₁4 : ∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 3, by omega⟩) N₁)
    (hN₂4 : ∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 3, by omega⟩) N₂)
    (hN₁₂ : ¬ Commutes N₁ N₂) (hne₁₂ : N₁ ≠ N₂)
    {J' : Subgroup G} {w : G} (e' : TwinElt M J' w) (hwM : IsClassicalMember3 M w)
    (hwJ' : IsClassicalMember3 J' w) (hJ'z : J' ∈ centralizingMembers Ω {z}) (hMJ' : M ≠ J')
    (hJ'K : J' ≠ K) (hJ'Q : ¬ locImg Ω z J' ≤ c.d.Q₁)
    (hN₁u : ∀ n ∈ N₁, n * e'.u = e'.u * n) (hN₂u : ∀ n ∈ N₂, n * e'.u = e'.u * n) :
    ∃ ε : 𝔽₃, ε * ε = 1 ∧ ∀ y,
      polar (quadOdd (u + 5) 𝔽₃) (spinAction (quadOdd (u + 5) 𝔽₃) x
        ((oddFrame (u + 5) 𝔽₃).toHypFrame.vec ⟨0, by omega⟩ true)) y = 0 →
      polar (quadOdd (u + 5) 𝔽₃) (spinAction (quadOdd (u + 5) 𝔽₃) x
        ((oddFrame (u + 5) 𝔽₃).toHypFrame.vec ⟨0, by omega⟩ false)) y = 0 →
      g₀ y = ε • y := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have cq := centralQuot3_odd (m := u + 5) (by omega)
  have hQ : (polarBilin (quadOdd (u + 5) 𝔽₃)).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd (u + 5) 𝔽₃ h2
  have hdimV : Module.finrank 𝔽₃ (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃) = 2 * (u + 1) + 9 := by
    rw [finrank_odd]
    omega
  set F₀ : HypFrame (quadOdd (u + 5) 𝔽₃) (u + 5) := (oddFrame (u + 5) 𝔽₃).toHypFrame with hF₀
  have hg : spinAction (quadOdd (u + 5) 𝔽₃) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd (u + 5) 𝔽₃) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  let pr : ℕ → HypPair (quadOdd (u + 5) 𝔽₃) := fun k =>
    if h : k < u + 5 then imgPair F₀ ⟨k, h⟩ hg else imgPair F₀ ⟨0, by omega⟩ hg
  have hprk : ∀ k (hk : k < u + 5), pr k = imgPair F₀ ⟨k, hk⟩ hg := fun k hk => by
    simp [pr, hk]
  have horth : ∀ a b, a < u + 1 + 4 → b < u + 1 + 4 → a ≠ b → (pr a).Orth (pr b) :=
    fun a b ha hb hab => by
      rw [hprk a (by omega), hprk b (by omega)]
      exact imgPair_orth F₀ hg (fun h => hab (congrArg Fin.val h))
  have hex : ∀ a, ∃ i', a ≤ u + 1 → IsFundamental (quadOdd (u + 5) 𝔽₃)
      ((Rz (a + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃))) i' := fun a => by
    by_cases ha : a ≤ u + 1
    · obtain ⟨i', hi'⟩ := cq.map_mem _ (hch.fund (a + 2) (by omega) (by omega))
      exact ⟨i', fun _ => hi'⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  have nL : ∀ a ≤ u + 1, negSpace (i a) = hypPlane (pr a) ⊔ hypPlane (pr (a + 1)) := by
    intro a ha
    rw [hprk a (by omega), hprk (a + 1) (by omega)]
    exact negSpace_rootSL2 hodd F₀ (by omega : a < u + 5) (by omega : a + 1 < u + 5) (by omega)
      true false x hg (hi a ha) (by rw [hxR a ha])
  obtain ⟨iM, hM', nM⟩ : ∃ iM, IsFundamental (quadOdd (u + 5) 𝔽₃)
      (RzM.map (spinAction (quadOdd (u + 5) 𝔽₃))) iM ∧
      negSpace iM = hypPlane (pr (u + 3)) ⊔ hypPlane (pr (u + 4)) := by
    obtain ⟨i', hi'⟩ := cq.map_mem _ hch.fundM
    refine ⟨i', hi', ?_⟩
    rw [hprk (u + 3) (by omega), hprk (u + 4) (by omega)]
    exact negSpace_rootSL2 hodd F₀ (by omega : u + 3 < u + 5) (by omega : u + 4 < u + 5)
      (by omega) true tM x hg hi' (by rw [hxM])
  let θ : spinGroup (quadOdd (u + 5) 𝔽₃) →* locQuot Ω z := c.d.ψ
  let σ := locAut c.hΩ.conjInvariant htz
  have hfixσ : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadOdd (u + 5) 𝔽₃))},
      L ∈ centralizingMembers Ω {z} → locImg Ω z L = R.map θ → Commutes β L →
      ∀ r ∈ R, σ (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 htz hL).mp
      (fun n hn => Subgroup.mem_centralizer_singleton_iff.mpr (hβL t ht.mem n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  have hcommg : ∀ {R : Subgroup (spinGroup (quadOdd (u + 5) 𝔽₃))},
      R ∈ fundamentalSubgroups .POmegaOdd (oddDatum (u + 5) 𝔽₃) →
      (∀ r ∈ R, σ (θ r) = θ r) →
      ∀ l ∈ R.map (spinAction (quadOdd (u + 5) 𝔽₃)), g₀ * l = l * g₀ :=
    fun hR hfix => commute_of_fixed3 θ c.d.ker_le c.ker_cop σ α hαθ (cq.pow3 _ hR) hfix hconj
  have hMβ : Commutes β M := by
    have := nd.commK ⟨1, by omega⟩
    rw [h1] at this
    exact commutes_symm this
  have f : ∀ a, 1 ≤ a → a ≤ u + 1 →
      ∀ l ∈ (Rz (a + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃)), g₀ * l = l * g₀ :=
    fun a ha1 ha2 => hcommg (hch.fund (a + 2) (by omega) (by omega))
      (hfixσ (node_mem_z3 c nd h0 (a := a + 2) (by omega) (by omega))
        (hch.img (a + 2) (by omega) (by omega))
        (node_commutes_β3 nd h1 (a := a + 2) (by omega) (by omega)))
  have fM := hcommg hch.fundM (hfixσ hMz hch.imgM hMβ)
  have hbr : ∀ {N : Subgroup G}, N ∈ Ω → (∀ a : Fin (u + 5), a.val < u + 3 →
      Commutes N (nd.J a)) → (∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 3, by omega⟩) N) →
      N ∈ centralizingMembers Ω {z} ∧ ∃ RN ∈ fundamentalSubgroups .POmegaOdd
        (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).D, locImg Ω z N = RN.map c.d.ψ := by
    intro N hNΩ hNc ⟨W4, hW4⟩
    have hNz : N ∈ centralizingMembers Ω {z} := by
      have := hNc ⟨0, by omega⟩ (by show 0 < u + 3; omega)
      rw [h0] at this
      exact mem_centralizingMembers_of_commutes hNΩ c.hz.mem this
    have hn4N : ¬ Commutes N (nd.J ⟨u + 3, by omega⟩) := fun h =>
      not_commutes_of_linearBlockStandardPair hW4 (commutes_symm h)
    have hN4ne : N ≠ nd.J ⟨u + 3, by omega⟩ := fun h =>
      ne_of_linearBlockStandardPair hW4 h.symm
    obtain ⟨hNK, hNQ⟩ := c.ne_and_not_le_Q₁3 hNz
      (node_mem_z3 c nd h0 (a := u + 3) (by omega) (by omega)) hN4ne hn4N
    exact ⟨hNz, c.exists_fund_of_ne hNz hNK hNQ⟩
  obtain ⟨hN₁z, RN₁, hRN₁, hN₁R⟩ := hbr hN₁Ω hN₁c hN₁4
  obtain ⟨hN₂z, RN₂, hRN₂, hN₂R⟩ := hbr hN₂Ω hN₂c hN₂4
  obtain ⟨s₁, hS₁⟩ := cq.map_mem _ hRN₁
  obtain ⟨s₂, hS₂⟩ := cq.map_mem _ hRN₂
  have hcommβ : ∀ {N : Subgroup G}, (∀ a : Fin (u + 5), a.val < u + 3 → Commutes N (nd.J a)) →
      Commutes β N := by
    intro N hNc
    have := hNc ⟨1, by omega⟩ (by show 1 < u + 3; omega)
    rw [h1] at this
    exact commutes_symm this
  have fS₁ := hcommg hRN₁ (hfixσ hN₁z hN₁R (hcommβ hN₁c))
  have fS₂ := hcommg hRN₂ (hfixσ hN₂z hN₂R (hcommβ hN₂c))
  have hSne : RN₁.map (spinAction (quadOdd (u + 5) 𝔽₃)) ≠
      RN₂.map (spinAction (quadOdd (u + 5) 𝔽₃)) := fun e =>
    hne₁₂ (c.eq_of_locImg_eq hN₁z hN₂z (by rw [hN₁R, hN₂R, cq.map_inj hRN₁ hRN₂ e]))
  have hSnc : ¬ Commutes (RN₁.map (spinAction (quadOdd (u + 5) 𝔽₃)))
      (RN₂.map (spinAction (quadOdd (u + 5) 𝔽₃))) := fun h =>
    hN₁₂ ((c.commutes_iff_fund hN₁z hN₂z hRN₁ hN₁R hN₂R).mpr ((cq.commutes_iff hRN₁).mp h))
  have hne : negSpace s₁ ≠ negSpace s₂ := negSpace_ne_of_not_commutes hodd hS₁ hS₂ hSne hSnc
  have hnc4 : ∀ {N : Subgroup G} {RN : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1
      Nat.prime_three).K}, N ∈ centralizingMembers Ω {z} →
      RN ∈ fundamentalSubgroups .POmegaOdd (oddDatum (u + 5) 𝔽₃) →
      locImg Ω z N = RN.map c.d.ψ →
      (∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 3, by omega⟩) N) →
      ¬ Commutes (RN.map (spinAction (quadOdd (u + 5) 𝔽₃)))
        ((Rz (u + 1 + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃))) := by
    intro N RN hNz hRN hNR ⟨W4, hW4⟩ h
    exact not_commutes_of_linearBlockStandardPair hW4 (commutes_symm
      ((c.commutes_iff_fund hNz (node_mem_z3 c nd h0 (a := u + 3) (by omega) (by omega)) hRN hNR
        (hch.img (u + 3) (by omega) (by omega))).mpr ((cq.commutes_iff hRN).mp h)))
  have hcN : ∀ {N : Subgroup G} {RN : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1
      Nat.prime_three).K}, N ∈ centralizingMembers Ω {z} →
      RN ∈ fundamentalSubgroups .POmegaOdd (oddDatum (u + 5) 𝔽₃) →
      locImg Ω z N = RN.map c.d.ψ →
      (∀ a : Fin (u + 5), a.val < u + 3 → Commutes N (nd.J a)) →
      ∀ a < u + 1, Commutes (RN.map (spinAction (quadOdd (u + 5) 𝔽₃)))
        ((Rz (a + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃))) := by
    intro N RN hNz hRN hNR hNc a ha
    exact (cq.commutes_iff hRN).mpr ((c.commutes_iff_fund hNz
      (node_mem_z3 c nd h0 (a := a + 2) (by omega) (by omega)) hRN hNR
      (hch.img (a + 2) (by omega) (by omega))).mp
        (hNc ⟨a + 2, by omega⟩ (by show a + 2 < u + 3; omega)))
  have horth' : ∀ a b, a < u + 1 + 1 → b < u + 1 + 1 → a ≠ b → (pr a).Orth (pr b) :=
    fun a b ha hb hab => horth a b (by omega) (by omega) hab
  have oS₁ := orth_bridge3 c ht htz nd h0 h1 hch hαθ hg₀O hg₀2 hconj horth' hi nL hS₁
    (hcN hN₁z hRN₁ hN₁R hN₁c) fS₁
  have oS₂ := orth_bridge3 c ht htz nd h0 h1 hch hαθ hg₀O hg₀2 hconj horth' hi nL hS₂
    (hcN hN₂z hRN₂ hN₂R hN₂c) fS₂
  obtain ⟨RJ, hRJ, hJR⟩ := c.exists_fund_of_ne hJ'z hJ'K hJ'Q
  obtain ⟨FM, g', J₁, hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, -, -, -, -, hg'comm⟩ :=
    twin_datum_odd3 (by omega) c hMz hJ'z hwM hwJ' e' hMJ' hch.fundM hch.imgM hRJ hJR
  have hM'' : IsFundamental (quadOdd (u + 5) 𝔽₃) FM.La.range (FM.La (-1)) :=
    IsFundamental.of_frame FM
  rw [← hFM] at hM''
  have hniM : negSpace iM = FM.span := by
    rw [IsFundamental.involution_unique hodd hM' hM'', negSpace_La_neg_one h2]
  have hS₁g' := hg'comm hN₁u hN₁R (c.hY.pow3 _ hRN₁)
  have hS₂g' := hg'comm hN₂u hN₂R (c.hY.pow3 _ hRN₂)
  obtain ⟨ε, hε, hscal⟩ := g0_scalar_gen hodd hQ (s := u + 1) (by omega) hdimV pr horth
    (L := fun a => (Rz (a + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃))) hi hM' hS₁ hS₂ nL nM
    oS₁ oS₂ (hnc4 hN₁z hRN₁ hN₁R hN₁4) (hnc4 hN₂z hRN₂ hN₂R hN₂4) hne hg₀O hg₀2 f fM fS₁ fS₂
    hg'O hg'2 hS₁g' hS₂g' (fun y hy => hg'fix y (fun w hw => hy w (by rw [hniM]; exact hw)))
    hg'dim (by rw [hniM]; exact hg'le)
  refine ⟨ε, by rcases hε with rfl | rfl <;> norm_num, fun y hy1 hy2 => hscal y ?_⟩
  rw [hprk 0 (by omega)]
  exact HypPair.mem_perp.mpr ⟨hy1, hy2⟩

end Scalar

end CFSG.ClassicalInvolution.Q3.Q3TWY
