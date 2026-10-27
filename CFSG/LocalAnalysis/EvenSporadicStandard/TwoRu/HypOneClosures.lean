module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover

variable {n : ℕ}

@[expose] def FourSet (K : Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n)) :=
  {x | x ∈ K ∧ x ^ 4 = 1 ∧ x ^ 2 ≠ 1}

theorem ncard_fourSet (K : Subgroup (Equiv.Perm (Fin n))) :
    (FourSet K).ncard = Nat.card {g : K // (g : Equiv.Perm (Fin n)) ^ 4 = 1 ∧
      (g : Equiv.Perm (Fin n)) ^ 2 ≠ 1} := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      invFun := fun g => ⟨g.1, g.1.2, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem conj_mem_fourSet {K : Subgroup (Equiv.Perm (Fin n))} {c x : Equiv.Perm (Fin n)}
    (hc : c ∈ K) (hx : x ∈ FourSet K) : c * x * c⁻¹ ∈ FourSet K := by
  obtain ⟨hxK, hx4, hx2⟩ := hx
  refine ⟨K.mul_mem (K.mul_mem hc hxK) (K.inv_mem hc), ?_, ?_⟩
  · rw [conj_pow, hx4]
    group
  · rw [conj_pow]
    intro h
    apply hx2
    have h' := congrArg (fun g => c⁻¹ * g * c) h
    simpa [mul_assoc] using h'

theorem fourClassesLarge_of_closures (K : Subgroup (Equiv.Perm (Fin n)))
    {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ K)
    {reps : List Table} (hreps : ∀ r ∈ reps, ∃ g ∈ K, Rep n r g) {cap N : ℕ}
    (hN : (FourSet K).ncard = N) (hok : fourClosuresOK n gens gensInv reps cap N = true) :
    FourClassesLarge K := by
  classical
  simp only [fourClosuresOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hok
  obtain ⟨⟨⟨htree, hdist⟩, hsum⟩, hord⟩ := hok
  choose! gr hgrK hgrep using hreps
  have hgr : ∀ r ∈ reps, gr r ∈ FourSet K := by
    intro r hr
    have ho : orderOf (gr r) = 4 :=
      (ordTest_iff perm_faithful (hgrep r hr) (by norm_num)).1 (hord r hr)
    refine ⟨hgrK r hr, ?_, fun h => ?_⟩
    · rw [← ho]
      exact pow_orderOf_eq_one _
    · have := orderOf_dvd_of_pow_eq_one h
      rw [ho] at this
      omega
  set cl := reps.map fun r => (r, conjClosure n gens gensInv r cap) with hcl
  have hclr : ∀ c ∈ cl, ∃ r ∈ reps, c = (r, conjClosure n gens gensInv r cap) := by
    intro c hc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
    exact ⟨r, hr, rfl⟩
  have hclm : ∀ r ∈ reps, (r, conjClosure n gens gensInv r cap) ∈ cl := fun r hr =>
    List.mem_map.2 ⟨r, hr, rfl⟩
  have hconj : ∀ r ∈ reps, ∀ T ∈ (conjClosure n gens gensInv r cap).1.toList,
      ∃ d ∈ K, Rep n T (d * gr r * d⁻¹) := by
    intro r hr T hT
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hk
    obtain ⟨d, hd, hrepd⟩ := conjTreeOK_spec K hg (hgrep r hr) (htree _ (hclm r hr)).1 k hk
    refine ⟨d, hd, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos _ k hk] at hrepd
  set U := cl.flatMap fun c => c.2.1.toList with hU
  have hUrep : ∀ T ∈ U, ∃ x ∈ FourSet K, Rep n T x := by
    intro T hT
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    obtain ⟨r, hr, rfl⟩ := hclr c hc
    obtain ⟨d, hd, hrep⟩ := hconj r hr T hT
    exact ⟨_, conj_mem_fourSet hd (hgr r hr), hrep⟩
  have hUf : List.Forall₂ (Rep n) U (U.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨x, -, hrep⟩ := hUrep T hT
    rw [tablePerm_eq hrep]
    exact hrep
  have hnodup : (U.map (tablePerm n)).Nodup := nodup_of_keysDistinct hUf hdist
  have hfin : (FourSet K).Finite := Set.toFinite _
  have hsub : (U.map (tablePerm n)).toFinset ⊆ hfin.toFinset := by
    intro y hy
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
    obtain ⟨x, hx, hrep⟩ := hUrep T hT
    rw [tablePerm_eq hrep]
    exact hfin.mem_toFinset.2 hx
  have hcard : hfin.toFinset.card ≤ (U.map (tablePerm n)).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup, List.length_map, hU, List.length_flatMap,
      ← Set.ncard_eq_toFinset_card _ hfin, hN, ← hsum]
    simp
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro x hx4 hx2
  have hx : (x : Equiv.Perm (Fin n)) ∈ FourSet K :=
    ⟨x.2, by rw [← SubgroupClass.coe_pow, hx4, OneMemClass.coe_one], fun h => hx2 (Subtype.ext (by
      rw [SubgroupClass.coe_pow, h, OneMemClass.coe_one]))⟩
  have hxU : (x : Equiv.Perm (Fin n)) ∈ (U.map (tablePerm n)).toFinset := by
    rw [heq]
    exact hfin.mem_toFinset.2 hx
  obtain ⟨T, hT, hTx⟩ := List.mem_map.1 (List.mem_toFinset.1 hxU)
  obtain ⟨c, hc, hTc⟩ := List.mem_flatMap.1 hT
  obtain ⟨r, hr, rfl⟩ := hclr c hc
  obtain ⟨d, hd, hrepd⟩ := hconj r hr T hTc
  have hxd : (x : Equiv.Perm (Fin n)) = d * gr r * d⁻¹ := by
    rw [← hTx, tablePerm_eq hrepd]
  have hE : ((conjClosure n gens gensInv r cap).1.toList.map (tablePerm n)).Nodup := by
    have h1 : (U.map (tablePerm n)).Nodup := hnodup
    rw [hU, List.map_flatMap] at h1
    exact (List.nodup_flatMap.1 h1).1 _ (hclm r hr)
  have hEsub : ∀ y ∈ (conjClosure n gens gensInv r cap).1.toList.map (tablePerm n),
      y ∈ conjClass K (gr r) := by
    intro y hy
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hy
    obtain ⟨d', hd', hrep'⟩ := hconj r hr T' hT'
    exact ⟨d', hd', tablePerm_eq hrep'⟩
  have hle : (conjClosure n gens gensInv r cap).1.size ≤ (conjClass K (gr r)).ncard := by
    have hlen : ((conjClosure n gens gensInv r cap).1.toList.map (tablePerm n)).length =
        (conjClosure n gens gensInv r cap).1.size := by simp
    rw [← hlen, ← List.toFinset_card_of_nodup hE, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun y hy => hEsub y (List.mem_toFinset.1 hy))
      (conjClass_finite K (gr r))
  rw [card_conj_eq_ncard, hxd, conjClass_conj K hd]
  exact (htree _ (hclm r hr)).2.trans hle

@[expose] def letterG (gg : ℕ → Equiv.Perm (Fin n)) (z : ℤ) : Equiv.Perm (Fin n) :=
  if 0 < z then gg (z.toNat - 1) else (gg ((-z).toNat - 1))⁻¹

theorem wordG_mem {K : Subgroup (Equiv.Perm (Fin n))} (gg : ℤ → Equiv.Perm (Fin n))
    {w : List ℤ} (h : ∀ z ∈ w, gg z ∈ K) : wordG gg w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons z w ih =>
    rw [wordG, List.map_cons, List.prod_cons]
    exact K.mul_mem (h z List.mem_cons_self) (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem rep_wordTables (hn : n < 2 ^ 32) (K : Subgroup (Equiv.Perm (Fin n)))
    {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ K)
    {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ gens.size) :
    ∃ g ∈ K, Rep n (wordT n (letterTab gens gensInv) w) g := by
  have hl : ∀ z ∈ w, Rep n (letterTab gens gensInv z) (letterG gg z) ∧ letterG gg z ∈ K := by
    intro z hz
    obtain ⟨hz0, hzs⟩ := hw z hz
    by_cases hpos : 0 < z
    · obtain ⟨h1, -, h3⟩ := hg (z.toNat - 1) (by omega)
      simp only [letterTab, letterG, hpos, ite_true]
      exact ⟨h1, h3⟩
    · obtain ⟨-, h2, h3⟩ := hg ((-z).toNat - 1) (by omega)
      simp only [letterTab, letterG, hpos, ite_false]
      exact ⟨h2, K.inv_mem h3⟩
  exact ⟨wordG (letterG gg) w, wordG_mem _ fun z hz => (hl z hz).2,
    Rep.wordT hn w fun z hz => (hl z hz).1⟩

end CFSG.EvenSporadicStandard.TwoRu.HypOne
