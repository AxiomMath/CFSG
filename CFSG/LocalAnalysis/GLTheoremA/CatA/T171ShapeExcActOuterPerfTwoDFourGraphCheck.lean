module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171D4GraphLists

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut TauCeti

variable {n : ℕ}

@[expose] def dGraphCheck (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) : Bool :=
  closedB M (orbitIter M 30) && M a b == 0 && orthOK M a b (orbitIter M 30) &&
    reachOK M a b (orbitIter M 30) 30 && adjOK M a b

theorem dGraphCheck_spec {M : Matrix (Fin n) (Fin n) ℤ} {a b : Fin n}
    (h : dGraphCheck M a b = true) :
    closedB M (orbitIter M 30) = true ∧ M a b = 0 ∧ orthOK M a b (orbitIter M 30) = true ∧
      reachOK M a b (orbitIter M 30) 30 = true ∧ adjOK M a b = true := by
  simpa [dGraphCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem isGraphTwist_of_dGraphCheck
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2) (e : simpleRoots Ψ ≃ Fin n)
    {M : Matrix (Fin n) (Fin n) ℤ}
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ))
    {a b : Fin n} (hab : a ≠ b) (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hσ : ∀ j, δ (e.symm j) = e.symm (Equiv.swap a b j))
    (hchk : dGraphCheck M a b = true) : IsGraphTwist Ψ δ := by
  obtain ⟨hcl, hMab, horth, hreach, hadj⟩ := dGraphCheck_spec hchk
  have himg := image_rootLift_orbit hΨ e he
  have hlift : ∀ x : Fin n → ℤ, δ (rootLift e x) =
      rootLift e (fun j => x (Equiv.swap a b j)) := fun x => by
    rw [map_rootLift δ e hσ x, Equiv.symm_swap]
  have hmem : ∀ γ ∈ Ψ, ∃ x, IsOrbitRoot M x ∧ rootLift e x = γ := by
    intro γ hγ
    rw [← himg] at hγ
    exact hγ
  refine ⟨fun γ hγ => ?_, fun γ hγ hne => ?_, fun γ hγ => ?_, fun β hβ hfix => ?_⟩
  · obtain ⟨x, -, rfl⟩ := hmem γ hγ
    rw [hlift, hlift]
    simp only [Equiv.swap_apply_self]
  · obtain ⟨x, hx, rfl⟩ := hmem γ hγ
    rw [hlift] at hne ⊢
    have hne' : (fun j => x (Equiv.swap a b j)) ≠ x := fun h => hne (by rw [h])
    rw [iform_rootLift hsl e he]
    exact form_swap_eq_zero_of_orthOK horth (ofFn_mem_of_closedB hcl hx) hne'
  · obtain ⟨x, hx, rfl⟩ := hmem γ hγ
    have hfr := isFoldReach_of_reachOK hreach (ofFn_mem_of_closedB hcl hx)
    obtain ⟨w, hw, j, hj⟩ := exists_smul_of_isFoldReach hsl e he hab δ hσ hMab hfr
    refine ⟨w⁻¹, inv_mem hw, ?_⟩
    rw [hj, inv_smul_smul]
    exact (e.symm j).2
  · set i := e ⟨β, hβ⟩ with hi
    have hβi : (e.symm i : Fin τ.rank → ℤ) = β := by rw [hi, Equiv.symm_apply_apply]
    have hia : i ≠ a := by
      rintro rfl
      have h := hσ i
      rw [Equiv.swap_apply_left, hβi, hfix] at h
      exact hab (e.symm.injective (Subtype.ext (hβi.trans h)))
    have hib : i ≠ b := by
      rintro rfl
      have h := hσ i
      rw [Equiv.swap_apply_right, hβi, hfix] at h
      exact hab (e.symm.injective (Subtype.ext (hβi.trans h).symm))
    obtain ⟨j, hja, hjb, hM⟩ := exists_adj_of_adjOK hadj hia hib
    refine ⟨e.symm j, (e.symm j).2, by rw [hσ, Equiv.swap_apply_of_ne_of_ne hja hjb], ?_⟩
    have h := iform_rootLift hsl e he (Pi.single i 1) (Pi.single j 1)
    rw [rootLift_single, rootLift_single, hβi] at h
    rw [h]
    simp [Pi.single_apply, hM]

@[expose] def d4Fun : Fin 4 → Fin 4 → ℤ := fun i j => CartanMatrix.D 4 i j

theorem d4_perm_cases {f : Fin 4 → Fin 4}
    (hM : ∀ i j, d4Fun (f i) (f j) = d4Fun i j) (h2 : ∀ i, f (f i) = i) :
    (∀ i, f i = i) ∨ (∀ i, f i = Equiv.swap 0 2 i) ∨
      (∀ i, f i = Equiv.swap 0 3 i) ∨ (∀ i, f i = Equiv.swap 2 3 i) := by
  decide +kernel +revert

theorem dGraphCheck_D4_zero_two :
    dGraphCheck (CartanMatrix.D 4) (0 : Fin 4) (2 : Fin 4) = true := by
  rw [dGraphCheck, D4K.orbitIter_D4, D4K.closedB_oD4, reachOK, D4K.foldIter_D4_02]
  decide +kernel

theorem dGraphCheck_D4_zero_three :
    dGraphCheck (CartanMatrix.D 4) (0 : Fin 4) (3 : Fin 4) = true := by
  rw [dGraphCheck, D4K.orbitIter_D4, D4K.closedB_oD4, reachOK, D4K.foldIter_D4_03]
  decide +kernel

theorem dGraphCheck_D4_two_three :
    dGraphCheck (CartanMatrix.D 4) (2 : Fin 4) (3 : Fin 4) = true := by
  rw [dGraphCheck, D4K.orbitIter_D4, D4K.closedB_oD4, reachOK, D4K.foldIter_D4_23]
  decide +kernel

theorem exists_fixed_adj_of_d4_swap
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hsl : ∀ beta ∈ simpleRoots Ψ, iform beta beta = 2)
    (e : simpleRoots Ψ ≃ Fin 4)
    (he : ∀ beta gamma : simpleRoots Ψ,
      corootPair (beta : Fin τ.rank → ℤ) gamma = CartanMatrix.D 4 (e beta) (e gamma))
    (delta : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    {sigma : Equiv.Perm (Fin 4)}
    (hSigma : ∀ j, delta (e.symm j) = e.symm (sigma j))
    (hCartan : ∀ i j, d4Fun (sigma i) (sigma j) = d4Fun i j)
    (hInvol : ∀ j, sigma (sigma j) = j) :
    ∀ beta ∈ simpleRoots Ψ, delta beta ≠ beta →
      ∃ beta' ∈ simpleRoots Ψ, delta beta' = beta' ∧ iform beta beta' = -1 := by
  have hFork : sigma 1 = 1 := by
    have h := d4_perm_cases hCartan hInvol
    rcases h with h | h | h | h
    · exact h 1
    · simpa only [show Equiv.swap (0 : Fin 4) 2 1 = 1 from by decide] using h 1
    · simpa only [show Equiv.swap (0 : Fin 4) 3 1 = 1 from by decide] using h 1
    · simpa only [show Equiv.swap (2 : Fin 4) 3 1 = 1 from by decide] using h 1
  intro beta hb hMove
  let j : Fin 4 := e ⟨beta, hb⟩
  have hBeta : (e.symm j : Fin τ.rank → ℤ) = beta := by simp [j]
  have hj : j ≠ 1 := by
    intro h
    apply hMove
    rw [← hBeta, hSigma, h, hFork]
  refine ⟨e.symm 1, (e.symm 1).2, ?_, ?_⟩
  · rw [hSigma, hFork]
  · have hAdj : CartanMatrix.D 4 j (1 : Fin 4) = -1 := by
      have hAll : ∀ k : Fin 4, k ≠ 1 → CartanMatrix.D 4 k 1 = -1 := by decide +kernel
      exact hAll j hj
    have hPair := he ⟨beta, hb⟩ (e.symm 1)
    change corootPair beta (e.symm 1) = CartanMatrix.D 4 j (e (e.symm 1)) at hPair
    rw [Equiv.apply_symm_apply, hAdj, corootPair, hsl beta hb] at hPair
    omega


@[expose] def d4_graph_perm (j : Fin 6) : Fin 4 → Fin 4 :=
  ![![0,1,2,3], ![2,1,0,3], ![3,1,2,0], ![0,1,3,2], ![2,1,3,0], ![3,1,0,2]] j

@[expose] def d4_graph_roots : List (List ℤ) :=
  [[-1,-2,-1,-1],
    [-1,-1,-1,-1],
    [-1,-1,-1,0],
    [-1,-1,0,-1],
    [-1,-1,0,0],
    [-1,0,0,0],
    [0,-1,-1,-1],
    [0,-1,-1,0],
    [0,-1,0,-1],
    [0,-1,0,0],
    [0,0,-1,0],
    [0,0,0,-1],
    [0,0,0,1],
    [0,0,1,0],
    [0,1,0,0],
    [0,1,0,1],
    [0,1,1,0],
    [0,1,1,1],
    [1,0,0,0],
    [1,1,0,0],
    [1,1,0,1],
    [1,1,1,0],
    [1,1,1,1],
    [1,2,1,1]]

theorem d4_graph_roots_members_mem_orbit : ∀ l ∈ d4_graph_roots,
    l ∈ orbitIter (CartanMatrix.D 4) 5 := by
  have hAll : ∀ i : Fin d4_graph_roots.length,
      d4_graph_roots[i] ∈ orbitIter (CartanMatrix.D 4) 5 := by
    decide +kernel
  intro l hl
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hl
  have hi' : d4_graph_roots[i] = l := hi
  exact hi' ▸ hAll i

theorem d4_graph_perm_values_cases :
    ∀ a b c d : Fin 4,
      (∀ i j : Fin 4, CFSG.LocalAnalysis.GLTheoremA.T171Sh.d4Fun (![a,b,c,d] i) (![a,b,c,d] j) =
        CFSG.LocalAnalysis.GLTheoremA.T171Sh.d4Fun i j) →
      ∃ k : Fin 6, ∀ i : Fin 4, ![a,b,c,d] i = d4_graph_perm k i := by
  decide +kernel

theorem d4_graph_perm_cases {sigma : Fin 4 → Fin 4}
    (hSigma : ∀ i j, CartanMatrix.D 4 (sigma i) (sigma j) = CartanMatrix.D 4 i j) :
    ∃ k : Fin 6, ∀ i, sigma i = d4_graph_perm k i := by
  have hs : sigma = ![sigma 0,sigma 1,sigma 2,sigma 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hs] at hSigma ⊢
  exact d4_graph_perm_values_cases _ _ _ _ hSigma

theorem d4_graph_root_six_cases_check (j : Fin 6) :
      ∀ k : Fin d4_graph_roots.length,
      let x : Fin 4 → ℤ := ofList d4_graph_roots[k]
      let p : (Fin 4 → ℤ) → (Fin 4 → ℤ) := fun y i => y (d4_graph_perm j i)
      ((∀ i, p x i = x i) ∨
        ((∀ i, p (p x) i = x i) ∧ (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * p x j) = 0) ∨
        ((∀ i, p (p (p x)) i = x i) ∧
          (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * p x j) = 0 ∧
          (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * p (p x) j) = 0 ∧
          (∑ i, ∑ j, p x i * CartanMatrix.D 4 i j * p (p x) j) = 0)) ∧
      ∃ k' : Fin d4_graph_roots.length,
        (∀ i, ofList d4_graph_roots[k'] (d4_graph_perm j i) =
          ofList (n := 4) d4_graph_roots[k'] i) ∧
        (∑ i, ∑ j, x i * CartanMatrix.D 4 i j *
          ofList d4_graph_roots[k'] j) = -1 := by
  decide +kernel +revert

theorem d4_graph_root_cases_check (sigma : Equiv.Perm (Fin 4))
    (hSigma : ∀ i j, CartanMatrix.D 4 (sigma i) (sigma j) = CartanMatrix.D 4 i j) :
      ∀ k : Fin d4_graph_roots.length,
      let x : Fin 4 → ℤ := ofList d4_graph_roots[k]
      let p : (Fin 4 → ℤ) → (Fin 4 → ℤ) := fun y i => y (sigma i)
      ((∀ i, p x i = x i) ∨
        ((∀ i, p (p x) i = x i) ∧ (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * p x j) = 0) ∨
        ((∀ i, p (p (p x)) i = x i) ∧
          (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * p x j) = 0 ∧
          (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * p (p x) j) = 0 ∧
          (∑ i, ∑ j, p x i * CartanMatrix.D 4 i j * p (p x) j) = 0)) ∧
      ∃ k' : Fin d4_graph_roots.length,
        (∀ i, ofList d4_graph_roots[k'] (sigma i) =
          ofList (n := 4) d4_graph_roots[k'] i) ∧
        (∑ i, ∑ j, x i * CartanMatrix.D 4 i j *
          ofList d4_graph_roots[k'] j) = -1 := by
  obtain ⟨j,hj⟩ := d4_graph_perm_cases hSigma
  have h := d4_graph_root_six_cases_check j
  have hs : (sigma : Fin 4 → Fin 4) = d4_graph_perm j := funext hj
  rw [← hs] at h
  exact h

theorem d4_graph_root_cases_list (sigma : Equiv.Perm (Fin 4))
    (hSigma : ∀ i j, CartanMatrix.D 4 (sigma i) (sigma j) = CartanMatrix.D 4 i j) :
      ∀ l ∈ d4_graph_roots,
      let x : Fin 4 → ℤ := ofList l
      let p : (Fin 4 → ℤ) → (Fin 4 → ℤ) := fun y i => y (sigma i)
      ((∀ i, p x i = x i) ∨
        ((∀ i, p (p x) i = x i) ∧ (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * p x j) = 0) ∨
        ((∀ i, p (p (p x)) i = x i) ∧
          (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * p x j) = 0 ∧
          (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * p (p x) j) = 0 ∧
          (∑ i, ∑ j, p x i * CartanMatrix.D 4 i j * p (p x) j) = 0)) ∧
      ∃ k ∈ d4_graph_roots,
        (∀ i, ofList k (sigma i) = ofList (n := 4) k i) ∧
        (∑ i, ∑ j, x i * CartanMatrix.D 4 i j * ofList k j) = -1 := by
  intro l hl
  obtain ⟨idx,hidx⟩ := List.mem_iff_get.mp hl
  have h := d4_graph_root_cases_check sigma hSigma idx
  have hget : d4_graph_roots[idx] = l := hidx
  dsimp only at h
  simp only [hget] at h
  rcases h with ⟨hp,j,hfix,hform⟩
  exact ⟨hp, d4_graph_roots[j],List.getElem_mem j.isLt,hfix,hform⟩

theorem d4_graph_root_list_closed : closedB (CartanMatrix.D 4) d4_graph_roots = true := by
  decide +kernel


end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
