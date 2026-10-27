module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NodeTab

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CoxeterSystem
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc


theorem distinct_of_codes {N : ℕ} {tab : List (List N6)} (hlen : tab.length = N) {v : List ℤ} {f : ℕ}
    (h : strictB (msortR f (tab.map fun w => codeL (w.foldr reflectL6 v))) = true) :
    ∀ i i' : Fin N, i ≠ i' →
      (tab.getD i []).foldr reflectL6 v ≠ (tab.getD i' []).foldr reflectL6 v := by
  intro i i' hne he
  have hnd := nodup_of_strictB_R h
  have hi : (i : ℕ) < tab.length := by rw [hlen]; exact i.isLt
  have hi' : (i' : ℕ) < tab.length := by rw [hlen]; exact i'.isLt
  have e1 : (tab.map fun w => codeL (w.foldr reflectL6 v))[(i : ℕ)]'(by simpa using hi) =
      (tab.map fun w => codeL (w.foldr reflectL6 v))[(i' : ℕ)]'(by simpa using hi') := by
    simp only [List.getElem_map]
    have h1 : tab[(i : ℕ)] = tab.getD i [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    have h2 : tab[(i' : ℕ)] = tab.getD i' [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
    rw [h1, h2, he]
  have := (List.Nodup.getElem_inj_iff hnd).1 e1
  exact hne (Fin.ext this)

theorem prim_of_contentL {s : N6} (T : NodeTab s)
    (h : ∀ i : Fin T.A, contentL ((T.wTab.getD i []).foldr refEL (List.ofFn (alphaF s))) = 1) :
    ∀ i : Fin T.A, ∀ d : ℕ, (∀ c, (d : ℤ) ∣ famB s T.wW i c) → d = 1 := by
  intro i d hd
  have h1 : d ∣ contentL ((T.wTab.getD i []).foldr refEL (List.ofFn (alphaF s))) := by
    refine dvd_contentL d _ fun z hz => ?_
    rw [← T.ofFn_famB, List.mem_ofFn] at hz
    obtain ⟨c, rfl⟩ := hz
    exact hd c
  rw [h i] at h1
  exact Nat.dvd_one.1 h1


structure TransTab where
  N : ℕ
  wTab : List (List N6)
  v : List ℤ
  A : List N6
  hvlen : v.length = Tag.rank .E6
  hmov : ∀ j : N6, reflectL6 j v ≠ v → j ∈ A
  hdist : ∀ i i' : Fin N, i ≠ i' →
    (wTab.getD i []).foldr reflectL6 v ≠ (wTab.getD i' []).foldr reflectL6 v

structure CopyTab (s : N6) where
  B : ℕ
  uTab : List (List N6)
  v : List ℤ
  A : List N6
  hvlen : v.length = Tag.rank .E6
  hmov : ∀ j : N6, reflectL6 j v ≠ v → j ∈ A
  hU2 : ∀ j : Fin B, (uTab.getD j []).foldr reflectL6 (List.ofFn (Pi.single s (1 : ℤ) : N6 → ℤ)) =
    List.ofFn (Pi.single s (1 : ℤ) : N6 → ℤ)
  hdist : ∀ j j' : Fin B, j ≠ j' →
    (uTab.getD j []).foldr reflectL6 v ≠ (uTab.getD j' []).foldr reflectL6 v

@[expose] def vecOf (v : List ℤ) : N6 → ℤ := fun i => v.getD i 0

theorem ofFn_vecOf {v : List ℤ} (h : v.length = Tag.rank .E6) : List.ofFn (vecOf v) = v := by
  refine List.ext_getElem (by simp [h]) fun n h1 h2 => ?_
  simp [vecOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

namespace TransTab

variable (Tr : TransTab)

theorem hmov' (j : N6) (hj : reflect Tag.E6 j (vecOf Tr.v) ≠ vecOf Tr.v) : j ∈ Tr.A := by
  apply Tr.hmov
  intro h
  apply hj
  apply List.ofFn_injective
  rw [ofFn_reflect6, ofFn_vecOf Tr.hvlen]
  exact h

theorem hdist' (i i' : Fin Tr.N) (h : i ≠ i') :
    (coxeterSystem Tag.E6).wordProd (Tr.wTab.getD i []) • vecOf Tr.v ≠
      (coxeterSystem Tag.E6).wordProd (Tr.wTab.getD i' []) • vecOf Tr.v := by
  intro he
  apply Tr.hdist i i' h
  rw [wordProd_smul_foldr, wordProd_smul_foldr] at he
  have := congrArg List.ofFn he
  rwa [ofFn_foldr_reflect6, ofFn_foldr_reflect6, ofFn_vecOf Tr.hvlen] at this

end TransTab

namespace CopyTab

variable {s : N6} (Cp : CopyTab s)

theorem hmov' (j : N6) (hj : reflect Tag.E6 j (vecOf Cp.v) ≠ vecOf Cp.v) : j ∈ Cp.A := by
  apply Cp.hmov
  intro h
  apply hj
  apply List.ofFn_injective
  rw [ofFn_reflect6, ofFn_vecOf Cp.hvlen]
  exact h

theorem hdist' (i i' : Fin Cp.B) (h : i ≠ i') :
    (coxeterSystem Tag.E6).wordProd (Cp.uTab.getD i []) • vecOf Cp.v ≠
      (coxeterSystem Tag.E6).wordProd (Cp.uTab.getD i' []) • vecOf Cp.v := by
  intro he
  apply Cp.hdist i i' h
  rw [wordProd_smul_foldr, wordProd_smul_foldr] at he
  have := congrArg List.ofFn he
  rwa [ofFn_foldr_reflect6, ofFn_foldr_reflect6, ofFn_vecOf Cp.hvlen] at this

theorem hfix (j : Fin Cp.B) :
    (coxeterSystem Tag.E6).wordProd (Cp.uTab.getD j []) • (Pi.single s 1 : N6 → ℤ) = Pi.single s 1 := by
  rw [wordProd_smul_foldr]
  apply List.ofFn_injective
  rw [ofFn_foldr_reflect6]
  exact Cp.hU2 j

end CopyTab

section Bounds

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem TransTab.bound [Module.Finite k V] (Tr : TransTab)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hA : ∀ j ∈ Tr.A, j ∉ J) :
    Tr.N ≤ Module.finrank k V :=
  card_le_finrank_support hρ ht (v := vecOf Tr.v) (fun j hj => hA j (Tr.hmov' j hj))
    (fun i => (coxeterSystem Tag.E6).wordProd (Tr.wTab.getD i [])) Tr.hdist'

theorem CopyTab.bound [Module.Finite k V] {s : N6} (Cp : CopyTab s) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k ↥(e6Data_valid.minGroup K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hs : s ∉ J) (hA : ∀ j ∈ Cp.A, j ∉ J)
    {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (e6Data_valid.hm K s z) ^ (2 ^ g) = χ (e6Data_valid.hm K s z)) :
    Cp.B * 2 ^ (n / g) ≤ Module.finrank k V :=
  copies_finrank hn hK hρ ht hs hg hgn hper
    (fun j => (coxeterSystem Tag.E6).wordProd (Cp.uTab.getD j [])) Cp.hfix
    (linearIndependent_translates_support hρ ht (v := vecOf Cp.v)
      (fun j hj => hA j (Cp.hmov' j hj)) _ Cp.hdist')

theorem twenty_pow_ge {t : ℕ} (h : 4 ≤ t) : 78 * t + 2 ≤ 20 * 2 ^ t := by
  induction t, h using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem dead_bound [Module.Finite k V] {s : N6} (Tr : TransTab) (Cp : CopyTab s)
    (hN : 158 ≤ Tr.N) (hN3 : 236 ≤ Tr.N ∨ 30 ≤ Cp.B) (hB : 20 ≤ Cp.B) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k ↥(e6Data_valid.minGroup K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hs : s ∉ J) (hAT : ∀ j ∈ Tr.A, j ∉ J)
    (hAC : ∀ j ∈ Cp.A, j ∉ J) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (e6Data_valid.hm K s z) ^ (2 ^ g) = χ (e6Data_valid.hm K s z)) :
    (n / g = 1 → 79 ≤ Module.finrank k V) ∧ (2 ≤ n / g → 78 * (n / g) + 2 ≤ Module.finrank k V) := by
  have h1 := Tr.bound hρ ht hAT
  have h2 := Cp.bound hn hK hρ ht hs hAC hg hgn hper
  refine ⟨fun ht1 => by omega, fun ht2 => ?_⟩
  by_cases h4 : 4 ≤ n / g
  · have := twenty_pow_ge h4
    have h5 : 20 * 2 ^ (n / g) ≤ Cp.B * 2 ^ (n / g) := Nat.mul_le_mul_right _ hB
    omega
  · have h3 : n / g = 2 ∨ n / g = 3 := by omega
    rcases h3 with h3 | h3
    · rw [h3]; omega
    · rw [h3] at h2 ⊢
      rcases hN3 with h | h
      · omega
      · have : 30 * 2 ^ 3 ≤ Cp.B * 2 ^ 3 := Nat.mul_le_mul_right _ h
        omega

end Bounds


end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
