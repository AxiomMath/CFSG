module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureCentralizer
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureGeneration

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

def rangePurePair {G : Type} [Group G] {ι : Type*} [DecidableEq ι]
    (R : Finset ι → Subgroup G) (i j : ι) : Subgroup G :=
  ⁅Subgroup.centralizer ((R {i} ⊓ R {j} : Subgroup G) : Set G) ⊓ R {i, j},
    Subgroup.centralizer ((R {i} ⊓ R {j} : Subgroup G) : Set G) ⊓ R {i, j}⁆

private theorem exists_ne_two (i j : Fin 4) : ∃ l : Fin 4, l ≠ i ∧ l ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem exists_ne_three (i j k : Fin 4) :
    ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

private theorem centralizer_map_inf_map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) (X Y : Subgroup G) :
    Subgroup.centralizer ((X.map φ : Subgroup H) : Set H) ⊓ Y.map φ =
      (Subgroup.centralizer (X : Set G) ⊓ Y).map φ := by
  ext h
  constructor
  · intro hh
    rw [Subgroup.mem_inf] at hh
    obtain ⟨hc, hy⟩ := hh
    obtain ⟨y, hyY, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, hyY⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : (φ x : H) ∈ (X.map φ : Subgroup H) := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hc) (φ x) hx'
    exact hφ (by rw [map_mul, map_mul]; exact hcomm)
  · intro hh
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyC, hyY⟩ := hy
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_map.mpr ⟨y, hyY, rfl⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hz
    have hxy : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hyC) x hxX
    rw [← map_mul, ← map_mul, hxy]

variable {G : Type} [Group G] {a : Fin 4 → (normOmega E 3 →* G)}
  {R : Finset (Fin 4) → Subgroup G}

private theorem hR_singleton (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty →
      S.card ≤ 2 → (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {i l : Fin 4} {i' : Fin 3} (hi' : l.succAbove i' = i) :
    (normBlock E 3 {i'}).map (a l) = R {i} := by
  simpa only [Finset.image_singleton, hi'] using
    hR l {i'} (Finset.singleton_nonempty i') (by simp)

private theorem hR_pair (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty →
      S.card ≤ 2 → (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {i j l : Fin 4} {i' j' : Fin 3} (hi' : l.succAbove i' = i)
    (hj' : l.succAbove j' = j) :
    (normBlock E 3 {i', j'}).map (a l) = R {i, j} := by
  simpa only [Finset.image_insert, Finset.image_singleton, hi', hj'] using
    hR l {i', j'} (Finset.insert_nonempty i' {j'}) Finset.card_le_two

theorem inf_eq_map_normBlock_empty
    (ha : ∀ i, Function.Injective (a i))
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {i j l : Fin 4} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    R {i} ⊓ R {j} = (normBlock E 3 ∅).map (a l) := by
  obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq hil
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hjl
  have hij' : i' ≠ j' := by
    intro h
    exact hij (by rw [← hi', ← hj', h])
  have h1 : (normBlock E 3 {i'}).map (a l) = R {i} := hR_singleton (E := E) hR hi'
  have h2 : (normBlock E 3 {j'}).map (a l) = R {j} := hR_singleton (E := E) hR hj'
  rw [← h1, ← h2, ← Subgroup.map_inf_eq (normBlock E 3 {i'}) (normBlock E 3 {j'})
    (a l) (ha l), normBlock_singleton_inf_singleton E hij']

theorem rangePurePair_eq_map (hq : 4 ≤ Nat.card F)
    (ha : ∀ i, Function.Injective (a i))
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {i j l : Fin 4} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {i' j' : Fin 3} (hi' : l.succAbove i' = i) (hj' : l.succAbove j' = j) :
    rangePurePair R i j = (normPureBlock E 3 {i', j'}).map (a l) := by
  have hij' : i' ≠ j' := by
    intro h
    exact hij (by rw [← hi', ← hj', h])
  have hInf : R {i} ⊓ R {j} = (normBlock E 3 ∅).map (a l) :=
    inf_eq_map_normBlock_empty (E := E) ha hR hij hil hjl
  have hPair : (normBlock E 3 {i', j'}).map (a l) = R {i, j} := hR_pair (E := E) hR hi' hj'
  calc
    rangePurePair R i j =
        ⁅Subgroup.centralizer ((normBlock E 3 ∅).map (a l) : Set G) ⊓
            (normBlock E 3 {i', j'}).map (a l),
          Subgroup.centralizer ((normBlock E 3 ∅).map (a l) : Set G) ⊓
            (normBlock E 3 {i', j'}).map (a l)⁆ := by
      unfold rangePurePair
      rw [hInf, hPair]
    _ = ⁅(Subgroup.centralizer (normBlock E 3 ∅ : Set (normOmega E 3)) ⊓
            normBlock E 3 {i', j'}).map (a l),
          (Subgroup.centralizer (normBlock E 3 ∅ : Set (normOmega E 3)) ⊓
            normBlock E 3 {i', j'}).map (a l)⁆ := by
      rw [centralizer_map_inf_map (a l) (ha l) (normBlock E 3 ∅) (normBlock E 3 {i', j'})]
    _ = (⁅Subgroup.centralizer (normBlock E 3 ∅ : Set (normOmega E 3)) ⊓
            normBlock E 3 {i', j'},
          Subgroup.centralizer (normBlock E 3 ∅ : Set (normOmega E 3)) ⊓
            normBlock E 3 {i', j'}⁆).map (a l) :=
      (Subgroup.map_commutator _ _ (a l)).symm
    _ = (normPureBlock E 3 {i', j'}).map (a l) := by
      rw [commutator_centralizer_normBlock_empty_inf_pair E hq hij']

theorem commute_of_mem_rangePurePair_of_mem_singleton (hq : 4 ≤ Nat.card F)
    (ha : ∀ i, Function.Injective (a i))
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {x y : G}
    (hx : x ∈ rangePurePair R i j) (hy : y ∈ R {k}) : Commute x y := by
  obtain ⟨l, hli, hlj, hlk⟩ := exists_ne_three i j k
  have hil : i ≠ l := fun h => hli h.symm
  have hjl : j ≠ l := fun h => hlj h.symm
  have hkl : k ≠ l := fun h => hlk h.symm
  obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq hil
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hjl
  obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hkl
  have hx' : x ∈ (normPureBlock E 3 {i', j'}).map (a l) := by
    rw [← rangePurePair_eq_map (E := E) hq ha hR hij hil hjl hi' hj']
    exact hx
  have hy' : y ∈ (normBlock E 3 {k'}).map (a l) := by
    simpa only [← hR_singleton (E := E) hR hk'] using hy
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx'
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy'
  have hik' : i' ≠ k' := by
    intro h
    exact hik (by rw [← hi', ← hk', h])
  have hjk' : j' ≠ k' := by
    intro h
    exact hjk (by rw [← hj', ← hk', h])
  have hdisj : Disjoint ({i', j'} : Finset (Fin 3)) {k'} := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hik'.symm, hjk'.symm⟩
  exact (commute_of_mem_normPureBlock_of_mem_normBlock (E := E) hdisj hx₀ hy₀).map (a l)

theorem commute_of_mem_rangePurePair_of_mem_pair (hq : 4 ≤ Nat.card F)
    (ha : ∀ i, Function.Injective (a i))
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) {x y : G} (hx : x ∈ rangePurePair R i j)
    (hy : y ∈ R {k, l}) : Commute x y := by
  obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hik.symm
  obtain ⟨l', hl'⟩ := Fin.exists_succAbove_eq hil.symm
  have hkl' : k' ≠ l' := by
    intro h
    exact hkl (by rw [← hk', ← hl', h])
  have hK : (normBlock E 3 {k'}).map (a i) = R {k} := hR_singleton (E := E) hR hk'
  have hL : (normBlock E 3 {l'}).map (a i) = R {l} := hR_singleton (E := E) hR hl'
  have hKL : (normBlock E 3 {k', l'}).map (a i) = R {k, l} := hR_pair (E := E) hR hk' hl'
  have hsup : R {k, l} = R {k} ⊔ R {l} := by
    rw [← hKL, ← hK, ← hL, ← Subgroup.map_sup,
      normBlock_singleton_sup_singleton E k' l']
  have hk_le : R {k} ≤ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_mem_rangePurePair_of_mem_singleton (E := E) hq ha hR hij hik hjk hx hz).eq.symm
  have hl_le : R {l} ≤ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_mem_rangePurePair_of_mem_singleton (E := E) hq ha hR hij hil hjl hx hz).eq.symm
  have hyC : y ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [hsup] at hy
    exact sup_le hk_le hl_le hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm

theorem sup_rangePurePair_eq (hq : 4 ≤ Nat.card F)
    (ha : ∀ i, Function.Injective (a i))
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {i j : Fin 4} (hij : i ≠ j) :
    R {i} ⊔ rangePurePair R i j = R {i, j} := by
  obtain ⟨l, hli, hlj⟩ := exists_ne_two i j
  have hil : i ≠ l := fun h => hli h.symm
  have hjl : j ≠ l := fun h => hlj h.symm
  obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq hil
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hjl
  have hij' : i' ≠ j' := by
    intro h
    exact hij (by rw [← hi', ← hj', h])
  have hI : (normBlock E 3 {i'}).map (a l) = R {i} := hR_singleton (E := E) hR hi'
  have hP : rangePurePair R i j = (normPureBlock E 3 {i', j'}).map (a l) :=
    rangePurePair_eq_map (E := E) hq ha hR hij hil hjl hi' hj'
  have hB : (normBlock E 3 {i', j'}).map (a l) = R {i, j} := hR_pair (E := E) hR hi' hj'
  rw [hP, ← hI, ← hB, ← Subgroup.map_sup,
    normBlock_singleton_sup_normPureBlock_pair E (by omega) (by norm_num) i' j']

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
