module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.EvenSporadicStandard.HypOne

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.SmallOddCore (tp rep_tp rep_invT enum_spec forall₂_tablePerm
  mem_map_tablePerm length_le_ncard_of_nodup permOK nodup_of_hkeysDistinct)

@[expose] def hashIndex (n : ℕ) (L : Array Table) : Std.HashMap UInt64 ℕ :=
  (List.range L.size).foldl (fun m i => m.insert (hkey n L[i]!) i) ∅

@[expose] def memTH (n : ℕ) (L : Array Table) (idx : Std.HashMap UInt64 ℕ) (x : Table) : Bool :=
  match idx[hkey n x]? with
  | some i => decide (i < L.size) && tblEq n x L[i]!
  | none => false

@[expose] def closedOKH (n : ℕ) (gens L : Array Table) : Bool :=
  let idx := hashIndex n L
  L.all fun x => gens.all fun g => memTH n L idx (compT n x g)

theorem memT_of_memTH {n : ℕ} {L : Array Table} {idx : Std.HashMap UInt64 ℕ} {x : Table}
    (h : memTH n L idx x = true) : memT n L x = true := by
  unfold memTH at h
  split at h
  · rename_i i _
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [memT, Array.any_eq_true]
    refine ⟨i, h.1, ?_⟩
    rw [← getElem!_pos L i h.1]
    exact h.2
  · exact absurd h Bool.false_ne_true

theorem closedOK_of_closedOKH {n : ℕ} {gens L : Array Table}
    (h : closedOKH n gens L = true) : closedOK n gens L = true := by
  unfold closedOKH at h
  rw [Array.all_eq_true] at h
  rw [closedOK, Array.all_eq_true]
  intro k hk
  have h1 := h k hk
  rw [Array.all_eq_true] at h1 ⊢
  intro l hl
  exact memT_of_memTH (h1 l hl)

@[expose] def fiveConjOK (n cap : ℕ) (cg cgInv : Array Table) (s : Table) : Bool :=
  let q := conjClosureH n cg cgInv s cap
  decide (5 ≤ q.1.size) && conjTreeOK n cg cgInv s q.1 q.2.1 q.2.2 && hkeysDistinct n q.1.toList

@[expose] def sylowFourOK (n capS capC : ℕ) (memK : Table → Bool) (cg sg : Array Table)
    (sylowOrder : ℕ) : Bool :=
  let cgInv := cg.map (invT n)
  let syl := mulClosureH n sg capS
  cg.all (fun x => permOK n x && invOK n x (invT n x) && memK x) &&
    sg.all (fun x => permOK n x && invOK n x (invT n x) && memK x) &&
    mulTreeOK n sg syl.1 syl.2.1 syl.2.2 && closedOKH n (sg ++ sg.map (invT n)) syl.1 &&
    hkeysDistinct n syl.1.toList && syl.1.size == sylowOrder &&
    syl.1.all (fun s => !ordTest n 4 s || fiveConjOK n capC cg cgInv s)

theorem exists_conj_mem_of_card_pow_four {M : Type*} [Group M] [Finite M] {R S : Subgroup M}
    (hSR : S ≤ R) (hS : Nat.card S = 2 ^ (Nat.card R).factorization 2) {t : M} (ht : t ∈ R)
    (ht4 : t ^ 4 = 1) : ∃ x ∈ R, x⁻¹ * t * x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 R := Sylow.ofCard (S.subgroupOf R) (by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv)
  have htR2 : IsPGroup 2 (zpowers (⟨t, ht⟩ : R)) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf t ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one ht4)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hm])
  obtain ⟨T, hT⟩ := htR2.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq R S' T
  refine ⟨x, x.2, ?_⟩
  have htT : (⟨t, ht⟩ : R) ∈ (T : Subgroup R) := hT (mem_zpowers _)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htT
  obtain ⟨s, hs, hst⟩ := htT
  have hsS : (s : M) ∈ S := by
    have : s ∈ S.subgroupOf R := by
      rwa [show ((S' : Subgroup R)) = S.subgroupOf R from Sylow.coe_ofCard _ _] at hs
    exact mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨t, ht⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

theorem fourClassesLarge_of_sylowFourOK {n : ℕ} (hn : n < 2 ^ 32)
    {K : Subgroup (Equiv.Perm (Fin n))} {memK : Table → Bool}
    (hmem : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → memK T = true → g ∈ K)
    {capS capC : ℕ} {cg sg : Array Table} {sylowOrder : ℕ}
    (hsyl : sylowOrder = 2 ^ (Nat.card K).factorization 2)
    (h : sylowFourOK n capS capC memK cg sg sylowOrder = true) : FourClassesLarge K := by
  simp only [sylowFourOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hcg, hsg⟩, htree⟩, hclosed⟩, hdist⟩, hsize⟩, hall⟩ := h
  rw [Array.all_eq_true'] at hcg hsg hall
  simp only [Bool.and_eq_true] at hcg hsg
  have hsgA : ∀ x ∈ sg, permOK n x = true := fun x hx => (hsg x hx).1.1
  have hsginv : ∀ x ∈ sg, invOK n x (invT n x) = true := fun x hx => (hsg x hx).1.2
  obtain ⟨-, hcov, hcard⟩ := enum_spec hn hsgA hsginv htree (closedOK_of_closedOKH hclosed) hdist
  set S := closure (tp n '' {x | x ∈ sg})
  have hSK : S ≤ K := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hmem x _ (rep_tp (hsgA x hx)) (hsg x hx).2
  have hScard : Nat.card S = 2 ^ (Nat.card K).factorization 2 := by rw [hcard, hsize, hsyl]
  have hcgK : ∀ l < cg.size, Rep n cg[l]! (tp n cg[l]!) ∧
      Rep n (cg.map (invT n))[l]! (tp n cg[l]!)⁻¹ ∧ tp n cg[l]! ∈ K := by
    intro l hl
    have hmemcg := CFSG.Sporadic.SmallOddCore.getElem!_mem_array hl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcg _ hmemcg
    have hc := rep_tp h1
    refine ⟨hc, ?_, hmem _ _ hc h3⟩
    rw [getElem!_pos (cg.map (invT n)) l (by simpa using hl), Array.getElem_map,
      ← getElem!_pos cg l hl]
    exact rep_invT hc h2
  intro x hx4 hx2
  have hx4' : (x : Equiv.Perm (Fin n)) ^ 4 = 1 := by
    rw [← SubgroupClass.coe_pow, hx4, OneMemClass.coe_one]
  have hx2' : (x : Equiv.Perm (Fin n)) ^ 2 ≠ 1 := fun h' => hx2 (Subtype.ext (by
    rw [SubgroupClass.coe_pow, h', OneMemClass.coe_one]))
  have hord4 : orderOf (x : Equiv.Perm (Fin n)) = 4 := orderOf_eq_four hx4' hx2'
  obtain ⟨c, hcK, hcS⟩ := exists_conj_mem_of_card_pow_four hSK hScard x.2 hx4'
  set s := c⁻¹ * (x : Equiv.Perm (Fin n)) * c with hs
  have hs4 : orderOf s = 4 := by
    have : s = (MulAut.conj c⁻¹) (x : Equiv.Perm (Fin n)) := by simp [hs]
    rw [this, MulEquiv.orderOf_eq, hord4]
  obtain ⟨k, hk, hkrep⟩ := hcov s hcS
  have hkmem := CFSG.Sporadic.SmallOddCore.getElem!_mem_array hk
  have h5 := hall _ hkmem
  have hordT : ordTest n 4 (mulClosureH n sg capS).1[k]! = true :=
    (ordTest_iff perm_faithful hkrep (by norm_num)).2 hs4
  rw [hordT, Bool.not_true, Bool.false_or] at h5
  simp only [fiveConjOK, Bool.and_eq_true, decide_eq_true_eq] at h5
  obtain ⟨⟨hq5, hqtree⟩, hqdist⟩ := h5
  set q := conjClosureH n cg (cg.map (invT n)) (mulClosureH n sg capS).1[k]! capC
  have hspec := conjTreeOK_spec K hcgK hkrep hqtree
  have hqrep : ∀ j < q.1.size, Rep n q.1[j]! (tablePerm n q.1[j]!) := by
    intro j hj
    obtain ⟨d, -, hrep⟩ := hspec j hj
    rw [tablePerm_eq hrep]
    exact hrep
  have hqnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hqrep) hqdist
  have hle : q.1.size ≤ (conjClass K s).ncard := by
    have := length_le_ncard_of_nodup hqnodup (S := conjClass K s) fun y hy => by
      obtain ⟨j, hj, rfl⟩ := mem_map_tablePerm hqrep hy
      obtain ⟨d, hd, hrep⟩ := hspec j hj
      rw [tablePerm_eq hrep]
      exact ⟨d, hd, rfl⟩
    rwa [List.length_map, Array.length_toList] at this
  have hcls : conjClass K s = conjClass K (x : Equiv.Perm (Fin n)) := by
    have := conjClass_conj K (inv_mem hcK) (x : Equiv.Perm (Fin n))
    rwa [inv_inv] at this
  rw [card_conj_eq_ncard, ← hcls]
  exact hq5.trans hle

end CFSG.EvenSporadicStandard.HypOne
