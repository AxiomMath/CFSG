module

public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative

public section

namespace CFSG.ComponentClassification.J2Cover

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Certificates.ChainArrays

variable {n : ℕ}

theorem toTable_eq_arrTable {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n t g) : toTable g = arrTable n t := by
  unfold toTable arrTable
  congr 1
  funext i
  rw [h i]

theorem rep_arrTable (hn : n < 2 ^ 32) {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n t g) : CFSG.Sporadic.Th.Rep n (arrTable n t) g := by
  rw [← toTable_eq_arrTable h]
  exact rep_toTable hn g

theorem card_fixed_eq_fixedCount {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n t g) : Nat.card {i : Fin n // g i = i} = fixedCount n t := by
  rw [fixedCount, List.countP_eq_length_filter]
  refine card_eq_length _ Fin.val Fin.val_injective _ (List.nodup_range.filter _) fun b => ?_
  simp only [List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨hb, hfix⟩
    refine ⟨⟨b, hb⟩, Fin.ext ?_, rfl⟩
    rw [← h ⟨b, hb⟩]
    exact hfix
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, ?_⟩
    rw [h a, ha]

theorem isInvA_of_invoList {t : Array ℕ} (h : invoList n t = true) : isInvA n t t = true := by
  rw [isInvA, allLt_iff]
  intro i hi
  exact List.all_eq_true.1 h i (List.mem_range.2 hi)

theorem eqA_idA_of_movesList {t : Array ℕ} (h : movesList n t = true) :
    eqA n t (idA n) = false := by
  obtain ⟨i, hi, hne⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  rw [Bool.eq_false_iff]
  intro he
  have := allLt_spec he hi
  rw [beq_iff_eq, idA_get hi] at this
  rw [bne_iff_ne] at hne
  exact hne this

theorem levelTables_eq {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) : levelTables Q = chainTables n S base := by
  have hsz : (rawLevels n S base).size = Q.baseCount := by
    rw [ChainArrays.chainLevels_size, hA.base_size]
  have hlev : ∀ i : Fin Q.baseCount,
      (levelTransversals Q i).map toTable =
        (List.range (lev n S base i).pts.size).map fun k => arrTable n (lev n S base i).tr[k]! := by
    intro i
    have hkeys : (Q.orbitSearch i).keys =
        (List.range (lev n S base i).pts.size).map (levPts Q S base i) := by
      rw [SchreierOrbitState.keys, hA.orbitSearch_eq hF i.2]
      simp [List.map_map, Function.comp_def]
    rw [levelTransversals, hkeys, List.map_map, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk' : k < (lev n S base i).pts.size := List.mem_range.1 hk
    simp only [Function.comp_apply]
    rw [hA.transversal_of_lt hF i.2 hk', Option.getD_some,
      toTable_eq_arrTable (hA.rep_levT hF i.2 hk')]
  rw [levelTables, chainTables, List.map_map]
  apply List.ext_getElem
  · simp [hsz]
  · intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_finRange]
    exact hlev ⟨i, h1⟩

section Arrays

variable {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ} {hk : k ≤ S.size} {base : List (Fin n)}
  {hb : base.Nodup} {W : Array (List ℤ)} {chunks : ℕ}

theorem ofArrays_chainArrays
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray W chunks = true) :
    ChainArrays (RawSchreierDatum.ofArrays n hn S k hk base hb W) (S.extract 0 k) S
      (base.map Fin.val).toArray W :=
  chainArrays_ofArrays (chainCheckFacts h).strong_inv

theorem ofArrays_valid (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray W chunks = true) :
    ValidSchreier (RawSchreierDatum.ofArrays n hn S k hk base hb W) :=
  (validSchreier_of_chainOK (ofArrays_chainArrays h) hc h).1

theorem ofArrays_card (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray W chunks = true) :
    Nat.card (RawSchreierDatum.ofArrays n hn S k hk base hb W).originalSubgroup =
      (rawOrbitSizes n S (base.map Fin.val).toArray).prod :=
  card_originalSubgroup_of_chainOK (ofArrays_chainArrays h) hc h

theorem ofArrays_mem_iff (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray W chunks = true)
    {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hG : CFSG.Monster.B.Co2.Rep n g G) :
    siftA n (rawLevels n S (base.map Fin.val).toArray) (base.map Fin.val).toArray 0 g = true ↔
      G ∈ (RawSchreierDatum.ofArrays n hn S k hk base hb W).originalSubgroup :=
  siftA_iff_mem_originalSubgroup (ofArrays_chainArrays h) hc h hG

theorem ofArrays_levelTables
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray W chunks = true) :
    levelTables (RawSchreierDatum.ofArrays n hn S k hk base hb W) =
      chainTables n S (base.map Fin.val).toArray :=
  levelTables_eq (ofArrays_chainArrays h) (chainCheckFacts h)

theorem ofArrays_originalSubgroup :
    (RawSchreierDatum.ofArrays n hn S k hk base hb W).originalSubgroup =
      Subgroup.closure {g | ∃ i < k, permOfArr n S[i]! = g} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  exact RawSchreierDatum.mem_ofArrays_original

theorem rep_permOfArr_of_chainOK
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray W chunks = true) {j : ℕ}
    (hj : j < S.size) : CFSG.Monster.B.Co2.Rep n S[j]! (permOfArr n S[j]!) :=
  (rep_permOfArr ((chainCheckFacts h).strong_inv j hj)).1

end Arrays

end CFSG.ComponentClassification.J2Cover
