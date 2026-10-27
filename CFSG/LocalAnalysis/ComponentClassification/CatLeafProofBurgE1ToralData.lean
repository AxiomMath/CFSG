module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Toral
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4SignOrbit

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem sum_zsmul_mem_addClosure {V : Type*} [AddCommGroup V] {s : Set V}
    (l : List (V × ℤ)) (h : ∀ x ∈ l, x.1 ∈ s) :
    (l.map fun x => x.2 • x.1).sum ∈ AddSubgroup.closure s := by
  induction l with
  | nil => exact zero_mem _
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons]
    exact add_mem (zsmul_mem (AddSubgroup.subset_closure (h x List.mem_cons_self)) _)
      (ih fun y hy => h y (List.mem_cons_of_mem x hy))

theorem pPrimeCore_toralCentralizer_bits_eq_bot
    [Finite K] (hK : ringChar K ≠ 2) (m : Fin τ.rank → Bool)
    (d1 d2 : Fin τ.rank → List ((Fin τ.rank → ℤ) × ℤ))
    (hd : ∀ j, ∀ x ∈ d1 j ++ d2 j,
      x.1 ∈ rootFinset τ ∧ maskChar m (Multiplicative.ofAdd x.1) = 1)
    (h1 : ∀ j, ((d1 j).map fun x => x.2 • x.1).sum = (2 : ℤ) • Pi.single j 1)
    (h2 : ∀ i j, 2 * τ.cartan i j =
      ((d2 i).map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum) :
    pPrimeCore 2 (toralCentralizer τ K (bitsTuple m)) = ⊥ := by
  have hb : ∀ i, bitsTuple (K := K) m i = 1 ∨ bitsTuple (K := K) m i = -1 := bitsTuple_mem m
  have hker := rootCharKernel_eq_kernelRoots hK hb
  rw [signTupleBits_bitsTuple hK] at hker
  have hmem : ∀ j, ∀ x ∈ d1 j ++ d2 j, x.1 ∈ rootCharKernel (bitsTuple (K := K) m) := by
    intro j x hx
    rw [hker]
    exact ⟨mem_rootFinset.1 (hd j x hx).1, (hd j x hx).2⟩
  refine pPrimeCore_toralCentralizer_eq_bot hK hb (fun j => ?_) (fun i t => ?_)
  · rw [← h1 j]
    exact sum_zsmul_mem_addClosure _ fun x hx => hmem j x (List.mem_append_left _ hx)
  · refine sq_torusElt_mem_of_coroots (fun w k hwk t => ?_) (fun γ hγ => hγ.1) i (d2 i)
      (fun x hx => hmem i x (List.mem_append_right _ hx)) (h2 i) t
    rw [hker] at hwk ⊢
    have h3 := componentTorus_le_componentRootSpan K (maskChar m) ⟦⟨_, hwk⟩⟧
      (canonicalRep_conj_torusElt_mem (K := K) (χ := maskChar m) (i := ⟦⟨_, hwk⟩⟧) ⟨hwk, rfl⟩ t)
    exact (biSup_mono (fun γ hγ => hγ.1) : componentRootSpan K (maskChar m) ⟦⟨_, hwk⟩⟧ ≤
      rootSpan τ K (kernelRoots (maskChar m))) h3

theorem pPrimeCore_toralCentralizer_of_orbitCheck
    (hK2 : ringChar K ≠ 2) {reps : List (List Bool)} {entries : List (List Bool × ℕ × List ℕ)}
    (hcert : OrbitCheck τ reps entries)
    (hreps : ∀ ρ < reps.length, listMask (τ := τ) (reps.getD ρ []) ≠ (fun _ => false) →
      pPrimeCore 2 (toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ [])))) = ⊥)
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    pPrimeCore 2 (toralCentralizer τ K b) = ⊥ := by
  obtain ⟨ρ, hρ, w, hw, hmap⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 hcert hb
  by_cases h0 : listMask (τ := τ) (reps.getD ρ []) = fun _ => false
  · refine absurd (eq_one_of_rootChar_smul_eq_one (w := w) fun v => ?_) hb1
    rw [hw v]
    congr 1
    funext i
    change (if listMask (τ := τ) (reps.getD ρ []) i then (-1 : Kˣ) else 1) = 1
    rw [h0]
    rfl
  · let e : toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ []))) ≃*
        toralCentralizer τ K b :=
      ((toralCentralizer τ K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    have h := pPrimeCore_map_iso 2 e
    rw [hreps ρ hρ h0, Subgroup.map_bot] at h
    exact h.symm

@[expose] def g2BurgData1 : Fin (Tag.rank .G2) → List ((Fin (Tag.rank .G2) → ℤ) × ℤ) :=
  ![[(![2, 3], 1), (![0, 1], -3)], [(![0, 1], 2)]]

@[expose] def g2BurgData2 : Fin (Tag.rank .G2) → List ((Fin (Tag.rank .G2) → ℤ) × ℤ) :=
  ![[(![2, 3], 1), (![0, 1], -1)], [(![0, 1], 2)]]

theorem g2BurgData_check :
    (∀ j, ∀ x ∈ g2BurgData1 j ++ g2BurgData2 j, x.1 ∈ rootFinset .G2 ∧
      maskChar (listMask (τ := .G2) [true, false]) (Multiplicative.ofAdd x.1) = 1) ∧
    (∀ j, ((g2BurgData1 j).map fun x => x.2 • x.1).sum = (2 : ℤ) • Pi.single j 1) ∧
    (∀ i j, 2 * Tag.G2.cartan i j =
      ((g2BurgData2 i).map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum) := by
  decide +kernel

theorem pPrimeCore_toralCentralizer_G2
    [Finite K] (hK : ringChar K ≠ 2) {b : Fin (Tag.rank .G2) → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    pPrimeCore 2 (toralCentralizer .G2 K b) = ⊥ := by
  refine pPrimeCore_toralCentralizer_of_orbitCheck hK g2SignOrbit_check (fun ρ hρ hne => ?_) hb hb1
  have hlen : g2SignReps.length = 2 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · obtain ⟨hd, h1, h2⟩ := g2BurgData_check
    exact pPrimeCore_toralCentralizer_bits_eq_bot hK _ g2BurgData1 g2BurgData2 hd h1 h2

@[expose] def f4BurgDataC1 : Fin (Tag.rank .F4) → List ((Fin (Tag.rank .F4) → ℤ) × ℤ) :=
  ![[(![2, 3, 4, 2], 1), (![0, 1, 0, 0], -3), (![0, 0, 1, 0], -4), (![0, 0, 0, 1], -2)],
    [(![0, 1, 0, 0], 2)], [(![0, 0, 1, 0], 2)], [(![0, 0, 0, 1], 2)]]

@[expose] def f4BurgDataC2 : Fin (Tag.rank .F4) → List ((Fin (Tag.rank .F4) → ℤ) × ℤ) :=
  ![[(![2, 3, 4, 2], 1), (![0, 1, 0, 0], -3), (![0, 0, 1, 0], -2), (![0, 0, 0, 1], -1)],
    [(![0, 1, 0, 0], 2)], [(![0, 0, 1, 0], 2)], [(![0, 0, 0, 1], 2)]]

@[expose] def f4BurgDataB1 : Fin (Tag.rank .F4) → List ((Fin (Tag.rank .F4) → ℤ) × ℤ) :=
  ![[(![1, 0, 0, 0], 2)], [(![0, 1, 0, 0], 2)], [(![0, 0, 1, 0], 2)],
    [(![2, 3, 4, 2], 1), (![1, 0, 0, 0], -2), (![0, 1, 0, 0], -3), (![0, 0, 1, 0], -4)]]

@[expose] def f4BurgDataB2 : Fin (Tag.rank .F4) → List ((Fin (Tag.rank .F4) → ℤ) × ℤ) :=
  ![[(![1, 0, 0, 0], 2)], [(![0, 1, 0, 0], 2)], [(![0, 0, 1, 0], 2)],
    [(![2, 3, 4, 2], 2), (![1, 0, 0, 0], -4), (![0, 1, 0, 0], -6), (![0, 0, 1, 0], -4)]]

theorem f4BurgDataC_check :
    (∀ j, ∀ x ∈ f4BurgDataC1 j ++ f4BurgDataC2 j, x.1 ∈ rootFinset .F4 ∧
      maskChar (listMask (τ := .F4) [true, false, false, false])
        (Multiplicative.ofAdd x.1) = 1) ∧
    (∀ j, ((f4BurgDataC1 j).map fun x => x.2 • x.1).sum = (2 : ℤ) • Pi.single j 1) ∧
    (∀ i j, 2 * Tag.F4.cartan i j =
      ((f4BurgDataC2 i).map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum) := by
  decide +kernel

theorem f4BurgDataB_check :
    (∀ j, ∀ x ∈ f4BurgDataB1 j ++ f4BurgDataB2 j, x.1 ∈ rootFinset .F4 ∧
      maskChar (listMask (τ := .F4) [false, false, false, true])
        (Multiplicative.ofAdd x.1) = 1) ∧
    (∀ j, ((f4BurgDataB1 j).map fun x => x.2 • x.1).sum = (2 : ℤ) • Pi.single j 1) ∧
    (∀ i j, 2 * Tag.F4.cartan i j =
      ((f4BurgDataB2 i).map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum) := by
  decide +kernel

theorem pPrimeCore_toralCentralizer_F4
    [Finite K] (hK : ringChar K ≠ 2) {b : Fin (Tag.rank .F4) → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    pPrimeCore 2 (toralCentralizer .F4 K b) = ⊥ := by
  refine pPrimeCore_toralCentralizer_of_orbitCheck hK f4SignOrbitB4_check
    (fun ρ hρ hne => ?_) hb hb1
  have hlen : f4SignRepsB4.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · obtain ⟨hd, h1, h2⟩ := f4BurgDataC_check
    exact pPrimeCore_toralCentralizer_bits_eq_bot hK _ f4BurgDataC1 f4BurgDataC2 hd h1 h2
  · obtain ⟨hd, h1, h2⟩ := f4BurgDataB_check
    exact pPrimeCore_toralCentralizer_bits_eq_bot hK _ f4BurgDataB1 f4BurgDataB2 hd h1 h2

@[expose] def e8BurgDataD : Fin (Tag.rank .E8) → List ((Fin (Tag.rank .E8) → ℤ) × ℤ) :=
  ![[(![2, 3, 4, 6, 5, 4, 3, 2], 1), (![0, 1, 0, 0, 0, 0, 0, 0], -3),
      (![0, 0, 1, 0, 0, 0, 0, 0], -4), (![0, 0, 0, 1, 0, 0, 0, 0], -6),
      (![0, 0, 0, 0, 1, 0, 0, 0], -5), (![0, 0, 0, 0, 0, 1, 0, 0], -4),
      (![0, 0, 0, 0, 0, 0, 1, 0], -3), (![0, 0, 0, 0, 0, 0, 0, 1], -2)],
    [(![0, 1, 0, 0, 0, 0, 0, 0], 2)], [(![0, 0, 1, 0, 0, 0, 0, 0], 2)],
    [(![0, 0, 0, 1, 0, 0, 0, 0], 2)], [(![0, 0, 0, 0, 1, 0, 0, 0], 2)],
    [(![0, 0, 0, 0, 0, 1, 0, 0], 2)], [(![0, 0, 0, 0, 0, 0, 1, 0], 2)],
    [(![0, 0, 0, 0, 0, 0, 0, 1], 2)]]

@[expose] def e8BurgDataA : Fin (Tag.rank .E8) → List ((Fin (Tag.rank .E8) → ℤ) × ℤ) :=
  ![[(![1, 1, 1, 1, 0, 0, 0, 0], 3), (![1, 3, 3, 5, 4, 3, 2, 1], -1),
      (![0, 0, 0, 1, 0, 0, 0, 0], 2), (![0, 0, 0, 0, 1, 0, 0, 0], 4),
      (![0, 0, 0, 0, 0, 1, 0, 0], 3), (![0, 0, 0, 0, 0, 0, 1, 0], 2),
      (![0, 0, 0, 0, 0, 0, 0, 1], 1)],
    [(![1, 3, 3, 5, 4, 3, 2, 1], 1), (![1, 1, 1, 1, 0, 0, 0, 0], -1),
      (![0, 0, 1, 0, 0, 0, 0, 0], -2), (![0, 0, 0, 1, 0, 0, 0, 0], -4),
      (![0, 0, 0, 0, 1, 0, 0, 0], -4), (![0, 0, 0, 0, 0, 1, 0, 0], -3),
      (![0, 0, 0, 0, 0, 0, 1, 0], -2), (![0, 0, 0, 0, 0, 0, 0, 1], -1)],
    [(![0, 0, 1, 0, 0, 0, 0, 0], 2)], [(![0, 0, 0, 1, 0, 0, 0, 0], 2)],
    [(![0, 0, 0, 0, 1, 0, 0, 0], 2)], [(![0, 0, 0, 0, 0, 1, 0, 0], 2)],
    [(![0, 0, 0, 0, 0, 0, 1, 0], 2)], [(![0, 0, 0, 0, 0, 0, 0, 1], 2)]]

theorem e8BurgDataD_check :
    (∀ j, ∀ x ∈ e8BurgDataD j ++ e8BurgDataD j, x.1 ∈ rootFinset .E8 ∧
      maskChar (listMask (τ := .E8) [true, false, false, false, false, false, false, false])
        (Multiplicative.ofAdd x.1) = 1) ∧
    (∀ j, ((e8BurgDataD j).map fun x => x.2 • x.1).sum = (2 : ℤ) • Pi.single j 1) ∧
    (∀ i j, 2 * Tag.E8.cartan i j =
      ((e8BurgDataD i).map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum) := by
  decide +kernel

theorem e8BurgDataA_check :
    (∀ j, ∀ x ∈ e8BurgDataA j ++ e8BurgDataA j, x.1 ∈ rootFinset .E8 ∧
      maskChar (listMask (τ := .E8) [true, true, false, false, false, false, false, false])
        (Multiplicative.ofAdd x.1) = 1) ∧
    (∀ j, ((e8BurgDataA j).map fun x => x.2 • x.1).sum = (2 : ℤ) • Pi.single j 1) ∧
    (∀ i j, 2 * Tag.E8.cartan i j =
      ((e8BurgDataA i).map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum) := by
  decide +kernel

theorem pPrimeCore_toralCentralizer_E8
    [Finite K] (hK : ringChar K ≠ 2) {b : Fin (Tag.rank .E8) → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    pPrimeCore 2 (toralCentralizer .E8 K b) = ⊥ := by
  refine pPrimeCore_toralCentralizer_of_orbitCheck hK e8SignOrbit_check
    (fun ρ hρ hne => ?_) hb hb1
  have hlen : e8SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · obtain ⟨hd, h1, h2⟩ := e8BurgDataD_check
    exact pPrimeCore_toralCentralizer_bits_eq_bot hK _ e8BurgDataD e8BurgDataD hd h1 h2
  · obtain ⟨hd, h1, h2⟩ := e8BurgDataA_check
    exact pPrimeCore_toralCentralizer_bits_eq_bot hK _ e8BurgDataA e8BurgDataA hd h1 h2

end CFSG.ComponentClassification.CatLeafProof
