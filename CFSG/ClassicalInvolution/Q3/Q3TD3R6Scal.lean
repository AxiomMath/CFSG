module

public import CFSG.ClassicalInvolution.Q3.Q3TD3R6Rec
public import CFSG.ClassicalInvolution.RouteD.TWED6Scalar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.Timmesfeld CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.RouteD.TWE.B6 CFSG.ClassicalInvolution.RouteD.TWE.D6
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (plus_hspan)
open scoped MatrixGroups


section Model

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  {Q : QuadraticForm (GaloisField 3 1) V}

theorem commute_spin_of_fixed3 {X : Type} [Group X] (θ : spinGroup Q →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup Q)) (hcop : ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z)
    (σ : X ≃* X) (α : spinGroup Q ≃* spinGroup Q) (hαθ : ∀ y, θ (α y) = σ (θ y))
    {R : Subgroup (spinGroup Q)} (hR : Pow3 R) (hfix : ∀ r ∈ R, σ (θ r) = θ r)
    {g₀ : V ≃ₗ[GaloisField 3 1] V}
    (hconj : ∀ y v, spinAction Q (α y) (g₀ v) = g₀ (spinAction Q y v)) :
    ∀ l ∈ R.map (spinAction Q), g₀ * l = l * g₀ := by
  rintro _ ⟨r, hr, rfl⟩
  have hαr : α r = r := eq_of_fixed_of_pow3 θ hker hcop α σ hαθ hR hfix r hr
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hconj r v, hαr]

end Model

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

local macro "d6_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem scalar_plus_six3 (c : TCtx3 .POmegaPlus 6 Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z)
    {M : Subgroup G} (hMz : M ∈ centralizingMembers Ω {z}) (nd : DNodes3 6 Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {Rz : ℕ → Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K}
    {RzM RN : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K}
    {x : spinGroup (quadPlus 6 (GaloisField 3 1))} {tM : Bool}
    {α : spinGroup (quadPlus 6 (GaloisField 3 1)) ≃* spinGroup (quadPlus 6 (GaloisField 3 1))}
    {g₀ : (Fin 6 ⊕ Fin 6 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 6 ⊕ Fin 6 → GaloisField 3 1)}
    (hRz : ∀ a (h : a < 6), 2 ≤ a →
      Rz a ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D ∧
        locImg Ω z (nd.J ⟨a, h⟩) = (Rz a).map c.d.ψ)
    (hRzM : RzM ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D ∧
      locImg Ω z M = RzM.map c.d.ψ)
    {N : Subgroup G} (hNz : N ∈ centralizingMembers Ω {z})
    (hRN : RN ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D ∧
      locImg Ω z N = RN.map c.d.ψ)
    (hxR : ∀ a (ha : a ≤ 2), Rz (a + 2) = ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) a
      (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom))
    (hxM : RzM = ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 4 5 (by omega) (by omega)
      (by omega) true tM).map (MulAut.conj x).toMonoidHom))
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField 3 1)))
    (hg₀2 : g₀ * g₀ = 1)
    (hconj : ∀ y v, spinAction (quadPlus 6 (GaloisField 3 1)) (α y) (g₀ v) =
      g₀ (spinAction (quadPlus 6 (GaloisField 3 1)) y v))
    (hfixv : ∀ a : Fin 6, 1 ≤ a.val → a.val ≤ 3 → ∀ s,
      g₀ (spinAction (quadPlus 6 (GaloisField 3 1)) x
        ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec a s)) =
      spinAction (quadPlus 6 (GaloisField 3 1)) x
        ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec a s))
    (hNc : ∀ a : Fin 6, a.val < 3 → Commutes N (nd.J a))
    (hN4 : ¬ Commutes N (nd.J ⟨4, by omega⟩)) (hN5 : ¬ Commutes N (nd.J ⟨5, by omega⟩)) :
    ∀ y, polar (quadPlus 6 (GaloisField 3 1)) (spinAction (quadPlus 6 (GaloisField 3 1)) x
        ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec ⟨0, by omega⟩ true)) y = 0 →
      polar (quadPlus 6 (GaloisField 3 1)) (spinAction (quadPlus 6 (GaloisField 3 1)) x
        ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec ⟨0, by omega⟩ false)) y = 0 →
      g₀ y = y := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have cq := centralQuot3_plus (m := 6) (by norm_num : 4 ≤ 6)
  have hQ : (polarBilin (quadPlus 6 (GaloisField 3 1))).Nondegenerate :=
    nondegenerate_polarBilin_quadPlus 6 (GaloisField 3 1)
  set F₀ := plusFrame 6 (GaloisField 3 1) (by norm_num) with hF₀
  have hg : spinAction (quadPlus 6 (GaloisField 3 1)) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField 3 1)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  let pr : ℕ → HypPair (quadPlus 6 (GaloisField 3 1)) := fun k =>
    if h : k < 6 then imgPair F₀ ⟨k, h⟩ hg else imgPair F₀ ⟨0, by omega⟩ hg
  have hprk : ∀ k (hk : k < 6), pr k = imgPair F₀ ⟨k, hk⟩ hg := fun k hk => by simp [pr, hk]
  have horth : ∀ a b, a < 6 → b < 6 → a ≠ b → (pr a).Orth (pr b) := fun a b ha hb hab => by
    rw [hprk a ha, hprk b hb]
    exact imgPair_orth F₀ hg (fun h => hab (congrArg Fin.val h))
  have hsp : ∀ y, (∀ a < 6, polar (quadPlus 6 (GaloisField 3 1)) y (pr a).e = 0 ∧
      polar (quadPlus 6 (GaloisField 3 1)) y (pr a).f = 0) → y = 0 := by
    intro y hy
    have h0 : spinAction (quadPlus 6 (GaloisField 3 1)) x⁻¹ y = 0 := by
      refine plus_hspan (F := GaloisField 3 1) (by norm_num) _ fun a r => ?_
      have h := hy a.val a.isLt
      have e1 : polar (quadPlus 6 (GaloisField 3 1)) y (imgPair F₀ a hg).e =
          polar (quadPlus 6 (GaloisField 3 1)) y (spinAction _ x (F₀.vec a true)) := rfl
      have hinv : y = spinAction (quadPlus 6 (GaloisField 3 1)) x
          (spinAction (quadPlus 6 (GaloisField 3 1)) x⁻¹ y) := by
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      have key : ∀ r', polar (quadPlus 6 (GaloisField 3 1))
          (spinAction (quadPlus 6 (GaloisField 3 1)) x⁻¹ y) (F₀.vec a r') =
          polar (quadPlus 6 (GaloisField 3 1)) y (spinAction (quadPlus 6 (GaloisField 3 1)) x
            (F₀.vec a r')) := by
        intro r'
        conv_rhs => rw [hinv]
        exact (polar_map_of_mem hg _ _).symm
      rw [key]
      rw [hprk a.val a.isLt] at h
      cases r
      · exact h.2
      · exact h.1
    have := (spinAction (quadPlus 6 (GaloisField 3 1)) x⁻¹).injective
      (h0.trans (map_zero _).symm)
    exact this
  have hLf : ∀ a (h : a ≤ 2), ∃ i, IsFundamental (quadPlus 6 (GaloisField 3 1))
      ((Rz (a + 2)).map (spinAction (quadPlus 6 (GaloisField 3 1)))) i ∧
      negSpace i = hypPlane (pr a) ⊔ hypPlane (pr (a + 1)) := by
    intro a h
    obtain ⟨i, hi⟩ := cq.map_mem _ (hRz (a + 2) (by omega) (by omega)).1
    refine ⟨i, hi, ?_⟩
    rw [hprk a (by omega), hprk (a + 1) (by omega)]
    exact negSpace_rootSL2 hodd F₀ (by omega : a < 6) (by omega : a + 1 < 6) (by omega) true false
      x hg hi (by rw [hxR a h])
  obtain ⟨i₀, h₀, n₀⟩ := hLf 0 (by norm_num)
  obtain ⟨i₂, h₂', n₂⟩ := hLf 2 (by norm_num)
  obtain ⟨iM, hM', nM⟩ : ∃ iM, IsFundamental (quadPlus 6 (GaloisField 3 1))
      (RzM.map (spinAction (quadPlus 6 (GaloisField 3 1)))) iM ∧
      negSpace iM = hypPlane (pr 4) ⊔ hypPlane (pr 5) := by
    obtain ⟨i, hi⟩ := cq.map_mem _ hRzM.1
    refine ⟨i, hi, ?_⟩
    rw [hprk 4 (by omega), hprk 5 (by omega)]
    exact negSpace_rootSL2 hodd F₀ (by omega : 4 < 6) (by omega : 5 < 6) (by omega) true tM x hg hi
      (by rw [hxM])
  obtain ⟨iN, hN'⟩ := cq.map_mem _ hRN.1
  have hKJ : ∀ a (h : a < 6), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne3 (by d6_idx)) (by d6_idx)
  have hmemz : ∀ a (h : a < 6), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hn45 : Commutes (nd.J ⟨4, by omega⟩) (nd.J ⟨5, by omega⟩) :=
    nd.commutes_of_not_adj (fin_ne_of_val_ne3 (by d6_idx)) (by d6_idx)
  have hN4ne : N ≠ nd.J ⟨4, by omega⟩ := fun h => hN5 (h ▸ hn45)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hcentM : M ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm
  have hcentN : N ≤ Subgroup.centralizer ({t} : Set G) := fun n hn => by
    have := hNc ⟨1, by omega⟩ (by norm_num)
    rw [h1] at this
    exact Subgroup.mem_centralizer_singleton_iff.mpr (this n hn t ht.mem)
  have hfixL : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K},
      L ∈ centralizingMembers Ω {z} → locImg Ω z L = R.map c.d.ψ →
      L ≤ Subgroup.centralizer ({t} : Set G) →
      ∀ r ∈ R, locAut hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r :=
    fun hL hLR hLt r hr => (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hL).mp hLt _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  have hcommg : ∀ {R : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K},
      R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)) →
      (∀ r ∈ R, locAut hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r) →
      ∀ l ∈ R.map (spinAction (quadPlus 6 (GaloisField 3 1))), g₀ * l = l * g₀ :=
    fun hR hfix => commute_spin_of_fixed3 c.d.ψ c.d.ker_le c.ker_cop
      (locAut hΩ.conjInvariant htz) α hαθ (cq.pow3 _ hR) hfix hconj
  have fM := hcommg hRzM.1 (hfixL hMz hRzM.2 hcentM)
  have fN := hcommg hRN.1 (hfixL hNz hRN.2 hcentN)
  obtain ⟨εM, hεM, hsM⟩ := sign_of_commute h2 hM' hg₀O hg₀2 fM
  obtain ⟨εN, hεN, hsN⟩ := sign_of_commute h2 hN' hg₀O hg₀2 fN
  have hfix2 : ∀ w ∈ negSpace i₂, g₀ w = w := by
    intro w hw
    rw [n₂] at hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
    have hpl : ∀ (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3), ∀ u ∈ hypPlane (pr k), g₀ u = u := by
      intro k hk hk3 u hu
      obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff _).mp hu
      have hk6 : k < 6 := by omega
      have h := hfixv ⟨k, hk6⟩ hk hk3
      rw [map_add, map_smul, map_smul]
      have e1 : g₀ (pr k).e = (pr k).e := by
        rw [hprk k hk6]
        exact h true
      have e2 : g₀ (pr k).f = (pr k).f := by
        rw [hprk k hk6]
        exact h false
      rw [e1, e2]
    rw [map_add, hpl 2 (by omega) (by omega) u hu, hpl 3 (by omega) (by omega) v hv]
  have hRf' : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), Rz a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) (by norm_num)) := fun a ha ha2 => (hRz a ha ha2).1
  have hc₀ : Commutes (RN.map (spinAction (quadPlus 6 (GaloisField 3 1))))
      ((Rz (0 + 2)).map (spinAction (quadPlus 6 (GaloisField 3 1)))) :=
    (cq.commutes_iff hRN.1).mpr ((c.commutes_iff_fund hNz (hmemz 2 (by omega) (by omega)) hRN.1
      hRN.2 (hRz 2 (by omega) (by omega)).2).mp (hNc ⟨2, by omega⟩ (by norm_num)))
  have hnc4 : ¬ Commutes (RN.map (spinAction (quadPlus 6 (GaloisField 3 1))))
      ((Rz (2 + 2)).map (spinAction (quadPlus 6 (GaloisField 3 1)))) := fun h =>
    hN4 ((c.commutes_iff_fund hNz (hmemz 4 (by omega) (by omega)) hRN.1 hRN.2
      (hRz 4 (by omega) (by omega)).2).mpr ((cq.commutes_iff hRN.1).mp h))
  have hne42 : RN.map (spinAction (quadPlus 6 (GaloisField 3 1))) ≠
      (Rz (2 + 2)).map (spinAction (quadPlus 6 (GaloisField 3 1))) := fun e =>
    hN4ne (c.eq_of_locImg_eq hNz (hmemz 4 (by omega) (by omega)) (by
      rw [hRN.2, (hRz 4 (by omega) (by omega)).2,
        cq.map_inj hRN.1 (hRf' 4 (by omega) (by omega)) e]))
  obtain ⟨u, hu, w, hw, hpuw⟩ := exists_polar_ne_of_not_commutes h2 hN' h₂' hnc4
  have hεN1 : εN = 1 := by
    have := sign_mul_eq_one hg₀O (hsN u hu) (show g₀ w = (1 : GaloisField 3 1) • w by
      rw [one_smul]; exact hfix2 w hw) hpuw
    rwa [mul_one] at this
  have hnM : ¬ Commutes (RN.map (spinAction (quadPlus 6 (GaloisField 3 1))))
      (RzM.map (spinAction (quadPlus 6 (GaloisField 3 1)))) := fun h =>
    hnc4 (commutes_of_commutes_two hodd horth hsp h₀ h₂' hM' hN' n₀ n₂ nM hne42 hc₀ h)
  obtain ⟨u', hu', w', hw', hpuw'⟩ := exists_polar_ne_of_not_commutes h2 hN' hM' hnM
  have hεM1 : εM = 1 := by
    have := sign_mul_eq_one hg₀O (hsN u' hu') (hsM w' hw') hpuw'
    rwa [hεN1, one_mul] at this
  have hfixall : ∀ a, 1 ≤ a → a < 6 →
      g₀ (pr a).e = (pr a).e ∧ g₀ (pr a).f = (pr a).f := by
    intro a ha1 ha6
    by_cases ha3 : a ≤ 3
    · have h := hfixv ⟨a, ha6⟩ ha1 ha3
      rw [hprk a ha6]
      exact ⟨h true, h false⟩
    · have hle : hypPlane (pr a) ≤ negSpace iM := by
        rw [nM]
        have : a = 4 ∨ a = 5 := by omega
        rcases this with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      refine ⟨?_, ?_⟩
      · rw [hsM _ (hle (e_mem_hypPlane _)), hεM1, one_smul]
      · rw [hsM _ (hle (f_mem_hypPlane _)), hεM1, one_smul]
  intro y hy1 hy2
  have key := g_eq_id_on_perp horth hsp (by norm_num) hg₀O hg₀2 hfixall y
  rw [hprk 0 (by omega)] at key
  exact key hy1 hy2

end Group

end CFSG.ClassicalInvolution.Q3.Q3TD
