module

public import CFSG.RankThree.Lattice.SteinbergBIGenCells
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

section Coords

variable {τ : Tag} {k : Type} [Field k]

@[expose] def coordTuple (Δ : Finset (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → kˣ) :
    Fin τ.rank → kˣ :=
  fun i => ∏ β ∈ Δ, c β ^ corootPair β (Pi.single i 1)

theorem coordTuple_congr {Δ : Finset (Fin τ.rank → ℤ)} {c c' : (Fin τ.rank → ℤ) → kˣ}
    (h : ∀ β ∈ Δ, c β = c' β) : coordTuple Δ c = coordTuple Δ c' :=
  funext fun _ => Finset.prod_congr rfl fun β hβ => by rw [h β hβ]

@[expose] def coordHom (Δ : Finset (Fin τ.rank → ℤ)) :
    ((Fin τ.rank → ℤ) → kˣ) →* (Fin τ.rank → kˣ) where
  toFun := coordTuple Δ
  map_one' := funext fun _ => by simp [coordTuple]
  map_mul' c c' := funext fun _ => by
    simp only [coordTuple, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem coordHom_apply (Δ : Finset (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → kˣ) :
    coordHom Δ c = coordTuple Δ c :=
  rfl

theorem coordTuple_eq_prod (Δ : Finset (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → kˣ) :
    coordTuple Δ c = ∏ β ∈ Δ, fun i => c β ^ corootPair β (Pi.single i 1) := by
  funext i
  rw [Finset.prod_apply]
  rfl

theorem rootDiagUnit_list_prod {ι : Type*} (l : List ι) (a : ι → Fin τ.rank → kˣ) :
    rootDiagUnit τ (l.map a).prod = (l.map fun j => rootDiagUnit τ (a j)).prod := by
  have h := map_list_prod (rootDiagUnitHom τ k) (l.map a)
  rw [List.map_map] at h
  exact h

theorem map_HSL_units {K K' : Type*} [Field K] [Field K'] (f : K →+* K') (t : Kˣ) :
    Matrix.SpecialLinearGroup.map f (HSL t) = HSL (Units.map f.toMonoidHom t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_HSL]

end Coords

section Datum


variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]

open Classical in
theorem rootDiagUnit_coordTuple_orbit_mem (D : GenFixedRootDatum τ p₀ k M)
    (Δ : Finset (Fin τ.rank → ℤ)) (hΔ : (Δ : Set (Fin τ.rank → ℤ)) = D.simpleRootsJ)
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (c : (Fin τ.rank → ℤ) → kˣ)
    (hc : ∀ j, c (D.orbitVec O (j + 1)) = c (D.orbitVec O j) ^ D.q) :
    rootDiagUnit τ (coordTuple Δ fun γ => if γ ∈ O then c γ else 1) ∈ D.orbitGroup := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, c (D.orbitVec O 0) = s := ⟨_, rfl⟩
  have hpow : ∀ j, c (D.orbitVec O j) = s ^ D.q ^ j := by
    intro j
    induction j with
    | zero => rw [hs, pow_zero, pow_one]
    | succ j ih => rw [hc, ih, ← pow_mul, ← pow_succ]
  have hsfix : s ^ D.q ^ GenFixedRootDatum.orbitCard O = s := by
    rw [← hpow, D.orbitVec_orbitCard hO, hs]
  have hmem : (s : k) ∈ D.orbitField O := by
    rw [D.mem_orbitField, ← Units.val_pow_eq_pow_val, hsfix]
  have hne : (⟨(s : k), hmem⟩ : D.orbitField O) ≠ 0 := fun h =>
    s.ne_zero (congrArg Subtype.val h)
  let u : (D.orbitField O)ˣ := Units.mk0 ⟨(s : k), hmem⟩ hne
  have hu : ∀ j, Units.map (iterateFrobenius k p₀ (D.e * j)).toMonoidHom
      (Units.map (D.orbitField O).subtype.toMonoidHom u) = s ^ D.q ^ j := fun j =>
    Units.ext (by simp [u, iterateFrobenius_def, GenFixedRootDatum.q, ← pow_mul])
  have hfac : ∀ j, D.orbitFactor O j (HSL u) =
      rootDiagUnit τ (fun i => c (D.orbitVec O j) ^ corootPair (D.orbitVec O j) (Pi.single i 1)) := by
    intro j
    rw [GenFixedRootDatum.orbitFactor_apply, map_HSL_units, map_HSL_units, hu j,
      rootSL2_HSL_eq (D.isRoot_orbitVec hO j), hpow j]
  have hmap : D.orbitMap O (HSL u) =
      rootDiagUnit τ (∏ j ∈ Finset.range (GenFixedRootDatum.orbitCard O),
        fun i => c (D.orbitVec O j) ^ corootPair (D.orbitVec O j) (Pi.single i 1)) := by
    simp only [GenFixedRootDatum.orbitMap_eq_prod, hfac]
    rw [← rootDiagUnit_list_prod, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  have hcoord : coordTuple Δ (fun γ => if γ ∈ O then c γ else 1) =
      ∏ j ∈ Finset.range (GenFixedRootDatum.orbitCard O),
        fun i => c (D.orbitVec O j) ^ corootPair (D.orbitVec O j) (Pi.single i 1) := by
    rw [coordTuple_eq_prod]
    have e1 : (∏ β ∈ Δ, fun i => (if β ∈ O then c β else 1) ^ corootPair β (Pi.single i 1)) =
        ∏ β ∈ Δ.filter (· ∈ O), fun i => c β ^ corootPair β (Pi.single i 1) := by
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun β _ => ?_
      split_ifs with h
      · rfl
      · funext i
        simp
    rw [e1]
    symm
    refine Finset.prod_nbij (D.orbitVec O) (fun j _ => ?_) (fun i hi j hj h => ?_)
      (fun γ hγ => ?_) (fun j _ => rfl)
    · have h1 := D.orbitVec_mem hO j
      refine Finset.mem_filter.2 ⟨?_, h1⟩
      rw [← Finset.mem_coe, hΔ]
      exact D.subset_simpleRootsJ_of_mem_orbits hO h1
    · exact D.orbitVec_injOn hO (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
    · obtain ⟨-, hγO⟩ := Finset.mem_filter.1 hγ
      obtain ⟨j, hj, e⟩ := D.exists_orbitVec_eq hO hγO
      exact ⟨j, Finset.mem_range.2 hj, e⟩
  rw [hcoord, ← hmap]
  exact D.orbitMap_mem_orbitGroup hO _

theorem fixedTorus_le_orbitGroupC_of_coords (D : GenFixedRootDatum τ p₀ k M)
    (Δ : Finset (Fin τ.rank → ℤ)) (hΔ : (Δ : Set (Fin τ.rank → ℤ)) = D.simpleRootsJ)
    (hcoord : ∀ t ∈ D.torusJ, ∃ c : (Fin τ.rank → ℤ) → kˣ, t = rootDiagUnit τ (coordTuple Δ c))
    (hinj : ∀ c c' : (Fin τ.rank → ℤ) → kˣ,
      rootDiagUnit τ (coordTuple Δ c) = rootDiagUnit τ (coordTuple Δ c') → ∀ β ∈ Δ, c β = c' β) :
    D.fixedTorus ≤ D.orbitGroupC := by
  classical
  intro t ht
  obtain ⟨htJ, htF⟩ := Subgroup.mem_inf.1 ht
  rw [Subgroup.mem_subgroupOf] at htJ
  have htF' : D.F t = t := htF
  obtain ⟨c, hc⟩ := hcoord _ htJ
  have hΔmem : ∀ β ∈ Δ, β ∈ D.simpleRootsJ := fun β hβ => by
    rw [← hΔ]
    exact hβ
  have hroot : ∀ β ∈ Δ, IsRoot τ β := fun β hβ =>
    (D.mem_kernelRoots_of_mem_simpleRootsJ (hΔmem β hβ)).1
  have hθ : ∀ β ∈ Δ, ∃ β' ∈ Δ, D.θ (toReal β) = toReal β' := by
    intro β hβ
    obtain ⟨β', hβ', e⟩ := D.mapsTo_simpleRootsJ ⟨β, hΔmem β hβ, rfl⟩
    refine ⟨β', ?_, e.symm⟩
    rw [← Finset.mem_coe, hΔ]
    exact hβ'
  choose! σ hσΔ hσθ using hθ
  have hσinj : Set.InjOn σ (Δ : Set (Fin τ.rank → ℤ)) := by
    intro β hβ β' hβ' h
    apply toReal_injective
    apply D.theta_injective
    rw [hσθ β hβ, hσθ β' hβ', h]
  have hbij : Set.BijOn σ (Δ : Set (Fin τ.rank → ℤ)) Δ :=
    (Δ.finite_toSet.injOn_iff_bijOn_of_mapsTo fun β hβ => hσΔ β hβ).1 hσinj
  let mk : (Fin τ.rank → kˣ) →* adjointGroup τ k :=
    (rootDiagUnitHom τ k).codRestrict (adjointGroup τ k) fun a =>
      rootDiagUnit_mem_adjointGroup_of_isAlgClosed a
  have hmk : ∀ a, ((mk a : adjointGroup τ k) : ModGL τ k) = rootDiagUnit τ a := fun _ => rfl
  let g₀ : (Fin τ.rank → ℤ) → Fin τ.rank → kˣ := fun β i => c β ^ corootPair β (Pi.single i 1)
  let g₁ : (Fin τ.rank → ℤ) → Fin τ.rank → kˣ := fun β i =>
    (c β ^ D.q) ^ corootPair (σ β) (Pi.single i 1)
  have ht : t = mk ((Δ.toList.map g₀).prod) := by
    apply Subtype.ext
    rw [hmk, Finset.prod_map_toList, hc, coordTuple_eq_prod]
  have hF1 : ∀ β ∈ Δ, D.F (mk (g₀ β)) = mk (g₁ β) := by
    intro β hβ
    apply Subtype.ext
    have h1 : ((mk (g₀ β) : adjointGroup τ k) : ModGL τ k) = rootSL2 τ k β (HSL (c β)) := by
      rw [hmk, rootSL2_HSL_eq (hroot β hβ)]
    have hu : Units.map (iterateFrobenius k p₀ D.e).toMonoidHom (c β) = c β ^ D.q :=
      Units.ext (by simp [iterateFrobenius_def, GenFixedRootDatum.q])
    rw [D.map_rootSL2 β (hΔmem β hβ).1 (σ β) (hσθ β hβ) (HSL (c β)) _ h1, map_HSL_units, hu,
      rootSL2_HSL_eq (hroot _ (hσΔ β hβ)), hmk]
  have hFt : D.F t = mk ((Δ.toList.map g₁).prod) := by
    rw [ht]
    simp only [map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun β hβ => hF1 β (Finset.mem_toList.1 hβ)
  let c' : (Fin τ.rank → ℤ) → kˣ := fun γ => c (Function.invFunOn σ (Δ : Set _) γ) ^ D.q
  have hc'σ : ∀ β ∈ Δ, c' (σ β) = c β ^ D.q := fun β hβ => by
    show c (Function.invFunOn σ (Δ : Set _) (σ β)) ^ D.q = c β ^ D.q
    rw [hσinj.leftInvOn_invFunOn hβ]
  have hY : (∏ β ∈ Δ, g₁ β) = coordTuple Δ c' := by
    rw [coordTuple_eq_prod]
    refine Finset.prod_nbij σ (fun β hβ => hσΔ β hβ) hσinj hbij.surjOn fun β hβ => ?_
    funext i
    show (c β ^ D.q) ^ corootPair (σ β) (Pi.single i 1) =
      c' (σ β) ^ corootPair (σ β) (Pi.single i 1)
    rw [hc'σ β hβ]
  have hfix : ∀ β ∈ Δ, c (σ β) = c β ^ D.q := by
    have e1 : ((D.F t : adjointGroup τ k) : ModGL τ k) = rootDiagUnit τ (coordTuple Δ c') := by
      rw [hFt, hmk, Finset.prod_map_toList, hY]
    have e2 : ((D.F t : adjointGroup τ k) : ModGL τ k) = rootDiagUnit τ (coordTuple Δ c) := by
      rw [htF', hc]
    have h := hinj c' c (e1.symm.trans e2)
    intro β hβ
    rw [← h (σ β) (hσΔ β hβ), hc'σ β hβ]
  have hstep : ∀ O ∈ D.orbits, ∀ j, c (D.orbitVec O (j + 1)) = c (D.orbitVec O j) ^ D.q := by
    intro O hO j
    have hjΔ : D.orbitVec O j ∈ Δ := by
      rw [← Finset.mem_coe, hΔ]
      exact D.subset_simpleRootsJ_of_mem_orbits hO (D.orbitVec_mem hO j)
    have e : σ (D.orbitVec O j) = D.orbitVec O (j + 1) := by
      apply toReal_injective
      rw [← hσθ _ hjΔ, D.theta_orbitVec hO j]
    rw [← e, hfix _ hjΔ]
  show (t : ModGL τ k) ∈ D.orbitGroup
  rw [hc]
  let R : Finset (Set (Fin τ.rank → ℤ)) := Δ.image fun β => thetaOrbit D.θ β
  have hR : ∀ O ∈ R, O ∈ D.orbits := by
    intro O hO
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hO
    exact ⟨β, hΔmem β hβ, rfl⟩
  let cO : Set (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → kˣ := fun O γ => if γ ∈ O then c γ else 1
  have hdec : ∀ γ ∈ Δ, (∏ O ∈ R, cO O) γ = c γ := by
    intro γ hγ
    rw [Finset.prod_apply, Finset.prod_eq_single_of_mem (thetaOrbit D.θ γ)
      (Finset.mem_image_of_mem _ hγ)]
    · show (if γ ∈ thetaOrbit D.θ γ then c γ else 1) = c γ
      rw [if_pos ⟨0, by simp⟩]
    · intro O hO hne
      show (if γ ∈ O then c γ else 1) = 1
      rw [if_neg]
      intro hγO
      exact hne (D.eq_thetaOrbit_of_mem_orbits (hR O hO) hγO)
  have hmemP : ∀ O ∈ R, coordHom Δ (cO O) ∈ D.orbitGroup.comap (rootDiagUnitHom τ k) := by
    intro O hO
    rw [Subgroup.mem_comap, coordHom_apply]
    exact rootDiagUnit_coordTuple_orbit_mem D Δ hΔ (hR O hO) c (hstep O (hR O hO))
  have hprod := Subgroup.prod_mem (D.orbitGroup.comap (rootDiagUnitHom τ k)) hmemP
  rw [← map_prod, coordHom_apply, coordTuple_congr hdec, Subgroup.mem_comap] at hprod
  exact hprod

end Datum

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
