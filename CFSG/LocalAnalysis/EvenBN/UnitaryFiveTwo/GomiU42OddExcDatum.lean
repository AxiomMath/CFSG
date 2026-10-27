module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcFix
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcNeigh
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcToral
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedComponentPrimes
public import CFSG.LocalAnalysis.SteinbergCAOddResidualInner

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem gomi_iform_eq_sum_single {τ : Tag} (u γ : Fin τ.rank → ℤ) :
    iform u γ = ∑ j, γ j * iform u (Pi.single j 1) := by
  classical
  have h : ∀ j, iform u (Pi.single j 1 : Fin τ.rank → ℤ) = ∑ i, u i * τ.symmetrizedCartan i j := by
    intro j
    simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  calc iform u γ = ∑ i, ∑ j, u i * τ.symmetrizedCartan i j * γ j := rfl
    _ = ∑ j, ∑ i, u i * τ.symmetrizedCartan i j * γ j := Finset.sum_comm
    _ = ∑ j, γ j * ∑ i, u i * τ.symmetrizedCartan i j := Finset.sum_congr rfl fun j _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ j, γ j * iform u (Pi.single j 1) := Finset.sum_congr rfl fun j _ => by rw [h j]

theorem gomi_rootChar_neg_one_zpow {τ : Tag} {K : Type} [Field K] (c γ : Fin τ.rank → ℤ) :
    rootChar (fun i => (-1 : Kˣ) ^ c i) γ = (-1 : Kˣ) ^ ∑ i, c i * γ i := by
  classical
  unfold rootChar
  rw [← gomi_prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [← zpow_mul]

section Datum

variable
  {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem gomi_orbitMap_neg_one_comm (hτ : τ = .E6 ∨ τ = .E7) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits)
    (heven : ∀ j, j < orbitCard O → ∀ γ ∈ D.roots, Even (iform (D.orbitVec O j) γ)) :
    ∀ g ∈ rootSpan τ k D.roots, g * D.orbitMap O (-1) = D.orbitMap O (-1) * g := by
  classical
  have hf : ∀ j, D.orbitFactor O j (-1) = rootDiagUnit τ
      (fun i => (-1 : kˣ) ^ corootPair (D.orbitVec O j) (Pi.single i 1)) := by
    intro j
    rw [D.orbitFactor_apply, CFSG.ClassicalInvolution.ModelFacts.map_neg_one_sl2,
      CFSG.ClassicalInvolution.ModelFacts.map_neg_one_sl2,
      ← CFSG.ClassicalInvolution.ModelFacts.HSL_neg_one_eq]
    exact CFSG.ClassicalInvolution.ModelFacts.rootSL2_neg_one_eq_rootDiagUnit
      (D.isRoot_orbitVec hO j) fun i => rfl
  have hcp : ∀ j (i : Fin τ.rank), corootPair (D.orbitVec O j) (Pi.single i 1) =
      iform (D.orbitVec O j) (Pi.single i 1) := fun j i =>
    CFSG.LocalAnalysis.SteinbergCA.corootPair_eq_iform_E67 hτ (D.isRoot_orbitVec hO j) _
  have hfac : ∀ j, j < orbitCard O → ∀ g ∈ rootSpan τ k D.roots,
      g * D.orbitFactor O j (-1) = D.orbitFactor O j (-1) * g := by
    intro j hj g hg
    set b : Fin τ.rank → kˣ := fun i => (-1 : kˣ) ^ iform (D.orbitVec O j) (Pi.single i 1) with hb
    have hb' : D.orbitFactor O j (-1) = rootDiagUnit τ b := by
      rw [hf j]
      simp only [hcp, hb]
    have hker : D.roots ⊆ rootCharKernel b := fun γ hγ => by
      refine ⟨isRoot_of_mem_unionRoots hγ, ?_⟩
      have h1 := gomi_rootChar_neg_one_zpow (K := k)
        (fun i => iform (D.orbitVec O j) (Pi.single i 1)) γ
      change rootChar (fun i => (-1 : kˣ) ^ iform (D.orbitVec O j) (Pi.single i 1)) γ = 1
      rw [h1]
      have h2 : ∑ i, iform (D.orbitVec O j) (Pi.single i 1) * γ i =
          iform (D.orbitVec O j) γ := by
        rw [gomi_iform_eq_sum_single (D.orbitVec O j) γ]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [h2]
      exact (heven j hj γ hγ).neg_one_zpow
    have hmono : rootSpan τ k D.roots ≤ rootSpan τ k (rootCharKernel b) :=
      iSup₂_le fun α hα => le_iSup₂_of_le α (hker hα) le_rfl
    have htc : rootSpan τ k (rootCharKernel b) ≤ toralCentralizer τ k b :=
      rootSpan_rootCharKernel_le_toralCentralizer b
    have hcen : toralCentralizer τ k b ≤
        Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ k)) := inf_le_right
    have := Subgroup.mem_centralizer_singleton_iff.1 (hcen (htc (hmono hg)))
    rw [hb']
    exact this
  rw [D.orbitMap_eq_prod]
  intro g hg
  have hc : Commute g
      ((List.map (fun j => D.orbitFactor O j (-1)) (List.range (orbitCard O))).prod) :=
    Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hfac j (List.mem_range.1 hj) g hg
  exact hc.eq

end Datum

theorem gomi_neigh_dichotomy {τ : Tag} (b : Fin τ.rank → Bool)
    (h : gomiNeighOK τ b = true) {α : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots (maskChar b)) (hpos : 0 < height α) :
    (∀ γ ∈ kernelRoots (maskChar b), 0 < height γ → γ ≠ α → iform α γ = 0) ∨
      ∃ T : Finset (Fin τ.rank → ℤ), 4 ≤ T.card ∧ ∀ γ ∈ T, γ ∈ kernelRoots (maskChar b) ∧
        0 < height γ ∧ γ ≠ α ∧ iform α γ ≠ 0 := by
  classical
  have hαr := mem_kernelRoots_maskChar.1 hα
  have hmem : List.ofFn α ∈ τ.artifactRoots := isRoot_iff_mem_artifactRoots.1 hαr.1
  have hvec : ∀ v : Fin τ.rank → ℤ, (gomiRootVec (List.ofFn v) : Fin τ.rank → ℤ) = v :=
    fun v => by funext i; simp [gomiRootVec]
  have hht : ∀ v : Fin τ.rank → ℤ, ∑ i : Fin τ.rank, gomiRootVec (List.ofFn v) i = height v :=
    fun v => by simp only [hvec]; rfl
  set a := List.ofFn α with ha
  set Lf : List (List ℤ) := (τ.artifactRoots).filter fun g => g != a &&
    decide (0 < ∑ i : Fin τ.rank, gomiRootVec g i) &&
    decide (Even (maskPairing b (gomiRootVec g : Fin τ.rank → ℤ))) &&
    decide (iform (τ := τ) (gomiRootVec a) (gomiRootVec g) ≠ 0) with hLf
  have hLfl : gomiNeighCount τ b a = Lf.length := rfl
  have hcnt : Lf.length = 0 ∨ 4 ≤ Lf.length := by
    have h1 := List.all_eq_true.1 h a hmem
    have hp : decide (0 < ∑ i : Fin τ.rank, gomiRootVec a i) = true := by
      simp only [decide_eq_true_eq, ha, hht]
      exact hpos
    have he : decide (Even (maskPairing b (gomiRootVec a : Fin τ.rank → ℤ))) = true := by
      simp only [decide_eq_true_eq, ha, hvec]
      exact hαr.2
    rw [hp, he] at h1
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h1
    rw [hLfl] at h1
    exact h1
  have hmemLf : ∀ g ∈ Lf, g ∈ τ.artifactRoots ∧ g ≠ a ∧
      0 < ∑ i : Fin τ.rank, gomiRootVec g i ∧
      Even (maskPairing b (gomiRootVec g : Fin τ.rank → ℤ)) ∧
      iform (τ := τ) (gomiRootVec a) (gomiRootVec g) ≠ 0 := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := List.mem_filter.1 hg
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hg2
    exact ⟨hg1, hg2.1.1.1, hg2.1.1.2, hg2.1.2, hg2.2⟩
  rcases hcnt with h0 | h4
  · left
    intro γ hγ hγpos hγne
    by_contra hne
    have hγr := mem_kernelRoots_maskChar.1 hγ
    have hγmem : List.ofFn γ ∈ τ.artifactRoots := isRoot_iff_mem_artifactRoots.1 hγr.1
    have : List.ofFn γ ∈ Lf := by
      rw [hLf, List.mem_filter]
      refine ⟨hγmem, ?_⟩
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, hht, hvec]
      refine ⟨⟨⟨fun hh => hγne (List.ofFn_injective hh), hγpos⟩, hγr.2⟩, ?_⟩
      rw [ha, hvec]
      exact hne
    have := List.length_pos_of_mem this
    omega
  · right
    refine ⟨(Lf.map fun g => (gomiRootVec g : Fin τ.rank → ℤ)).toFinset, ?_, ?_⟩
    · have hnd : Lf.Nodup := (nodup_artifactRoots τ).filter _
      have hlen : ∀ g ∈ Lf, g.length = τ.rank := fun g hg =>
        length_of_mem_artifactRoots (hmemLf g hg).1
      have hnd2 : (Lf.map fun g => (gomiRootVec g : Fin τ.rank → ℤ)).Nodup := by
        refine hnd.map_on fun g hg g' hg' hgg' => ?_
        rw [← gomi_ofFn_rootVec (hlen g hg), ← gomi_ofFn_rootVec (hlen g' hg'), hgg']
      rw [List.toFinset_card_of_nodup hnd2, List.length_map]
      exact h4
    · intro γ hγ
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hγ)
      obtain ⟨hg1, hg2, hg3, hg4, hg5⟩ := hmemLf g hg
      have hglen := length_of_mem_artifactRoots hg1
      have hgv : List.ofFn (gomiRootVec g : Fin τ.rank → ℤ) = g := gomi_ofFn_rootVec hglen
      refine ⟨mem_kernelRoots_maskChar.2 ⟨isRoot_iff_mem_artifactRoots.2 (by rw [hgv]; exact hg1),
        hg4⟩, hg3, ?_, ?_⟩
      · intro hh
        apply hg2
        rw [← hgv, hh, ha]
      · rw [ha, hvec] at hg5
        exact hg5

theorem gomi_neigh_dichotomy' {τ : Tag} {b : Fin τ.rank → Bool}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    (hχ : χ = maskChar b) (h : gomiNeighOK τ b = true) {α : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots χ) (hpos : 0 < height α) :
    (∀ γ ∈ kernelRoots χ, 0 < height γ → γ ≠ α → iform α γ = 0) ∨
      ∃ T : Finset (Fin τ.rank → ℤ), 4 ≤ T.card ∧ ∀ γ ∈ T, γ ∈ kernelRoots χ ∧
        0 < height γ ∧ γ ≠ α ∧ iform α γ ≠ 0 := by
  subst hχ
  exact gomi_neigh_dichotomy b h hα hpos

theorem gomi_not_pow_five_dvd_25920 {n : ℕ} (hn : Odd n) (hn1 : 1 < n) : ¬ n ^ 5 ∣ 25920 := by
  intro h
  have hle : n ^ 5 ≤ 25920 := Nat.le_of_dvd (by norm_num) h
  have hn8 : n ≤ 7 := by
    by_contra h8
    have : 8 ^ 5 ≤ n ^ 5 := Nat.pow_le_pow_left (not_le.1 h8) 5
    omega
  interval_cases n <;> first | exact absurd hn (by decide) | exact absurd h (by decide)

section Main

variable
  {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem gomi_false_of_isPComponent_totalFixedGroup (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hτ : τ = .E6 ∨ τ = .E7) {m : ℕ} (hDχ : D.χ = ToralSign.signMaskChar τ m)
    (hnb : gomiNeighOK τ (ToralSign.natBits m) = true)
    (horb : ∀ (J' : Set.range D.classOrbit) (O : Set (Fin τ.rank → ℤ)),
      O ∈ (D.withOrbit J').orbits → orbitCard O ≤ 2)
    (hX : Finite D.totalFixedGroup) {J₀ : Subgroup (adjointGroup τ k)}
    (hJ₀X : J₀ ≤ D.totalFixedGroup)
    (hJ₀c : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup))
    (hJ₀s : IsSimpleGroup J₀) (hJ₀nab : ∃ a b : J₀, a * b ≠ b * a)
    (hcard : Nat.card J₀ = 25920) : False := by
  classical
  have hcomp : CFSG.IsComponent (J₀.subgroupOf D.totalFixedGroup) := by
    obtain ⟨-, -, hsub, -, -⟩ := hJ₀c
    refine ⟨?_, hsub⟩
    have : IsSimpleGroup (J₀.subgroupOf D.totalFixedGroup) :=
      (Subgroup.subgroupOfEquivOfLe hJ₀X).isSimpleGroup
    exact CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (by
      obtain ⟨a, b, hab⟩ := hJ₀nab
      refine ⟨(Subgroup.subgroupOfEquivOfLe hJ₀X).symm a,
        (Subgroup.subgroupOfEquivOfLe hJ₀X).symm b, fun h' => hab ?_⟩
      apply (Subgroup.subgroupOfEquivOfLe hJ₀X).symm.injective
      exact (MulEquiv.map_mul _ a b).trans (h'.trans (MulEquiv.map_mul _ b a).symm)) |>.1
  obtain ⟨J', ⟨O, hO⟩, hJ₀eq⟩ := D.exists_eq_orbitGroupC_of_isComponent hX hJ₀X hcomp
  set D' := D.withOrbit J' with hD'
  have hχ : D'.χ = maskChar (ToralSign.natBits m) := hDχ
  have hP1 : D'.q ^ D'.posRootsJ.ncard ∣ 25920 := by
    have h1 := gomi_pow_dvd_card_orbitGroupC D'
    rw [← hJ₀eq, hcard] at h1
    exact h1
  have hN : D'.posRootsJ.ncard ≤ 4 := by
    by_contra hN
    have hN5 : 5 ≤ D'.posRootsJ.ncard := by omega
    have hq : D'.q = p ^ D'.e := rfl
    have h5 : p ^ 5 ∣ 25920 := by
      have : p ^ 5 ∣ D'.q ^ D'.posRootsJ.ncard := by
        rw [hq, ← pow_mul]
        exact pow_dvd_pow p (by have := D'.one_le_e; nlinarith)
      exact this.trans hP1
    exact gomi_not_pow_five_dvd_25920 ((Fact.out : p.Prime).odd_of_ne_two D.odd)
      (Fact.out : p.Prime).one_lt h5
  have hfin : D'.posRootsJ.Finite := D'.finite_roots.subset fun α hα => hα.1
  have hort : ∀ α ∈ D'.posRootsJ, ∀ γ ∈ D'.posRootsJ, γ ≠ α → iform α γ = 0 := by
    intro α hα γ hγ hne
    have hαK : α ∈ kernelRoots D'.χ := hα.1.1
    rcases gomi_neigh_dichotomy' hχ hnb hαK hα.2 with h | ⟨T, hT, hTmem⟩
    · exact h γ hγ.1.1 hγ.2 hne
    · exfalso
      have hsub : insert α (↑T : Set (Fin τ.rank → ℤ)) ⊆ D'.posRootsJ := by
        intro γ' hγ'
        rcases hγ' with rfl | hγ'T
        · exact hα
        · obtain ⟨hγ'K, hγ'pos, -, hγ'ne⟩ := hTmem γ' hγ'T
          refine ⟨⟨hγ'K, ?_⟩, hγ'pos⟩
          have hcls := mk_eq_of_iform_ne_zero (χ := D'.χ) (α := ⟨α, hαK⟩) (β := ⟨γ', hγ'K⟩)
            hγ'ne
          rw [← hcls]
          exact hα.1.2
      have h1 := Set.ncard_le_ncard hsub hfin
      have hnot : α ∉ (↑T : Set (Fin τ.rank → ℤ)) := fun hαT =>
        (hTmem α hαT).2.2.1 rfl
      rw [Set.ncard_insert_of_notMem hnot T.finite_toSet, Set.ncard_coe_finset] at h1
      omega
  have hself : ∀ j, iform (D'.orbitVec O j) (D'.orbitVec O j) = 2 := by
    intro j
    obtain ⟨i, hi⟩ := iform_self_of_isRoot (D'.isRoot_orbitVec hO j)
    have h1 : τ.symmetrizer i i = 1 := by rcases hτ with rfl | rfl <;> fin_cases i <;> rfl
    rw [hi, h1, mul_one]
  have heven : ∀ j, j < orbitCard O → ∀ γ ∈ D'.roots,
      Even (iform (D'.orbitVec O j) γ) := by
    intro j hj γ hγ
    have hv : D'.orbitVec O j ∈ D'.posRootsJ :=
      D'.mem_posRootsJ_of_mem_orbits hO (D'.orbitVec_mem hO j)
    rcases mem_posRoots_or_mem_negRoots_unionRoots hγ with hγp | hγn
    · by_cases he : γ = D'.orbitVec O j
      · rw [he, hself]
        exact even_two
      · rw [hort _ hv γ hγp he]
        exact ⟨0, by simp⟩
    · have hγ' : -γ ∈ D'.posRootsJ := hγn
      have hneg : iform (D'.orbitVec O j) γ = -iform (D'.orbitVec O j) (-γ) := by
        have := iform_smul_right (-1 : ℤ) (D'.orbitVec O j) (-γ)
        rw [neg_one_smul, neg_neg] at this
        rw [this]
        ring
      rw [hneg]
      by_cases he : -γ = D'.orbitVec O j
      · rw [he, hself]
        exact (even_two).neg
      · rw [hort _ hv (-γ) hγ' he]
        simp
  have hcomm := gomi_orbitMap_neg_one_comm D' hτ hO heven
  let φ : SL2 (D'.orbitField O) →* adjointGroup τ k :=
    (D'.orbitMapHom hO).codRestrict _ (fun A => D'.orbitMap_mem_adjointGroup O A)
  have hφ : ∀ A, ((φ A : adjointGroup τ k) : ModGL τ k) = D'.orbitMap O A := fun A => rfl
  have hφJ : φ (-1) ∈ J₀ := by
    rw [hJ₀eq]
    exact D'.mk_mem_orbitGroupC (D'.orbitMap_mem_orbitGroup hO _)
  have hz1 : φ (-1) ≠ 1 := fun h => by
    apply CFSG.LocalAnalysis.SteinbergCA.orbitMap_neg_one_ne_one D' hτ hO (horb J' O hO)
    rw [← hφ, h]
    rfl
  have hcent : (⟨φ (-1), hφJ⟩ : J₀) ∈ Subgroup.center J₀ := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : ((g : adjointGroup τ k) : ModGL τ k) ∈ D'.rootSpanJ := by
      have h1 : (g : adjointGroup τ k) ∈ D'.fixedGroup := D'.orbitGroupC_le_fixedGroup (hJ₀eq ▸ g.2)
      exact (Subgroup.mem_inf.1 h1).1
    have := hcomm _ hg
    apply Subtype.ext
    apply Subtype.ext
    show ((g : adjointGroup τ k) : ModGL τ k) * ((φ (-1) : adjointGroup τ k) : ModGL τ k) =
      ((φ (-1) : adjointGroup τ k) : ModGL τ k) * ((g : adjointGroup τ k) : ModGL τ k)
    rw [hφ]
    exact this
  haveI := hJ₀s
  have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hJ₀nab).2
  rw [hZ, Subgroup.mem_bot] at hcent
  exact hz1 (congrArg (fun x : J₀ => (x : adjointGroup τ k)) hcent)

end Main

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
