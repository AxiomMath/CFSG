module

public import CFSG.Certificates.Kernel.SporSch.ChainKCount
public import CFSG.Certificates.Kernel.SporSch.ConjClosureSpec

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Monster.B.Mathieu CFSG.KS.SporSch.ChainCls CFSG.KS.SporSch.ClsSpec
open CFSG.Sporadic.SmallOddCore

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
include hQ

theorem prep_gens {g : Nat} (hg : g < gens.length) :
    PRep n w (PS g) (gens.getD g 1) ∧ PRep n w (PSI g) (gens.getD g 1)⁻¹ := by
  have h1 := prep_of_imageList (hQ.2.2.2.1 g hg)
  have hk := kS_eq hQ
  have h2 := prep_PS (binds_of hQ) (chainK_perm hQ) (j := g) (by omega)
  have e := prep_unique h2.1 h1
  rw [e] at h2
  exact ⟨h1, h2.2⟩

theorem inv_facts {LB CJ RP : Nat → Nat} {c j : Nat}
    (h : clsInvK n w (mask w) (n * w) (pidn n w) LR TR k PS PSI gens.length LB CJ RP c
      (ordK LR k) j = true) :
    LB j < c ∧ j ≤ RP (LB j) ∧ ∀ g < gens.length, CJ (gens.length * j + g) < ordK LR k ∧
      LB (CJ (gens.length * j + g)) = LB j ∧
      elemP n w LR TR k (CJ (gens.length * j + g)) =
        gens.getD g 1 * elemP n w LR TR k j * (gens.getD g 1)⁻¹ := by
  unfold clsInvK at h
  simp only [Orb.strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, allN_iff,
    Nat.add_eq, Nat.mul_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun g hg => ?_⟩
  obtain ⟨h4, h5, h6⟩ := h3 g hg
  have h32 := chainK_h32 hQ
  have hP := prep_gens hQ hg
  have hr := prep_pcomp h32 hP.1 (prep_pcomp h32 (prep_elemK hQ j) hP.2)
  rw [← Nat.eq_of_beq_eq_true h6] at hr
  refine ⟨h4, Nat.eq_of_beq_eq_true h5, ?_⟩
  rw [prep_unique (prep_elemK hQ _) hr, mul_assoc]

theorem rep_facts {LB RP SZ ZC : Nat → Nat} {l : Nat}
    (h : clsRepK n w (mask w) (n * w) (pidn n w) LR TR k LB RP SZ ZC (ordK LR k) l = true) :
    LB (RP l) = l ∧ RP l < ordK LR k ∧ (l ≠ 0 → RP l < RP (l - 1)) ∧
      SZ l * ZC l = ordK LR k ∧
      (List.range (ordK LR k)).countP (fun j => Nat.beq (LB j) l) = SZ l ∧
      (List.range (ordK LR k)).countP (fun j => decide (elemP n w LR TR k j *
        elemP n w LR TR k (RP l) = elemP n w LR TR k (RP l) * elemP n w LR TR k j)) = ZC l := by
  unfold clsRepK at h
  simp only [Orb.strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, h2, fun hl => ?_, Nat.eq_of_beq_eq_true h4, ?_, ?_⟩
  · rw [bIf_eq] at h3
    simpa [hl] using h3
  · rw [← Nat.eq_of_beq_eq_true h5, cntRK_eq, List.range_eq_range']
  · rw [← Nat.eq_of_beq_eq_true h6, commCntK, cntRK_eq, ← List.range_eq_range']
    apply List.countP_congr
    intro j hj
    have hjN := List.mem_range.1 hj
    have hG : ∀ i < [elemP n w LR TR k (RP l)].length,
        PRep n w ((fun _ => elemK n w (mask w) (n * w) (pidn n w) LR TR k (RP l)) i)
          ([elemP n w LR TR k (RP l)].getD i 1) := fun i hi => by
      have : i = 0 := by simpa using hi
      subst this
      exact prep_elemK hQ _
    have e := commGK_eq hQ hG j
    simp only [List.length_singleton, List.all_cons, List.all_nil, Bool.and_true] at e
    simp only [bIf_eq, Orb.strictB_eq, Nat.blt_eq, hjN, ↓reduceIte, e]

theorem ordK_pos : 0 < ordK LR k := by
  rw [ordK_eq]
  exact List.prod_pos fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    exact rcnt_pos hQ (List.mem_range.1 hi)

theorem of_blocks {f : Nat → Bool} {L NB : Nat} (hL : ordK LR k ≤ NB * L)
    (h : ∀ s < NB, allBlk (s * L) f L = true) : ∀ j < ordK LR k, f j = true := by
  intro j hj
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, Nat.mul_zero] at hL
      have := ordK_pos hQ
      omega
    · exact h0
  have hb := h (j / L) ((Nat.div_lt_iff_lt_mul hLpos).2 (by omega))
  rw [allBlk_eq, List.all_eq_true] at hb
  have := hb (j % L) (List.mem_range.2 (Nat.mod_lt j hLpos))
  rwa [Nat.div_add_mod' j L] at this

variable (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
include hn hbs

theorem mem_group_iff (z : Equiv.Perm (Fin n)) :
    z ∈ (certificate hn gens words bv hbs).originalSubgroup ↔
      ∃ j < ordK LR k, elemP n w LR TR k j = z := by
  rw [← mem_elemP_iff hQ hn hbs, List.mem_map]
  simp only [List.mem_range]

theorem elemP_inj {j j' : Nat} (hj : j < ordK LR k) (hj' : j' < ordK LR k)
    (e : elemP n w LR TR k j = elemP n w LR TR k j') : j = j' :=
  List.inj_on_of_nodup_map (elemP_nodup hQ hn hbs) (List.mem_range.2 hj) (List.mem_range.2 hj') e

theorem card_group :
    Nat.card (certificate hn gens words bv hbs).originalSubgroup = ordK LR k := by
  rw [← RawSchreierDatum.orderCertificate_eq_card _ (chainK_valid hQ hn hbs),
    (chainK_check hn hbs hQ).2]

theorem ncard_elems (p : Nat → Bool) :
    {z | ∃ j < ordK LR k, p j = true ∧ elemP n w LR TR k j = z}.ncard =
      (List.range (ordK LR k)).countP p := by
  classical
  have e : {z | ∃ j < ordK LR k, p j = true ∧ elemP n w LR TR k j = z} =
      ↑((((List.range (ordK LR k)).filter p).map (elemP n w LR TR k)).toFinset) := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map, List.mem_filter,
      List.mem_range]
    constructor
    · rintro ⟨j, hj, hp, rfl⟩
      exact ⟨j, ⟨hj, hp⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hp⟩, rfl⟩
      exact ⟨j, hj, hp, rfl⟩
  have hnd : (((List.range (ordK LR k)).filter p).map (elemP n w LR TR k)).Nodup :=
    (elemP_nodup hQ hn hbs).sublist (List.filter_sublist.map _)
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map,
    List.countP_eq_length_filter]

end Chain

section Classes

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup) {LB CJ RP SZ ZC : Nat → Nat} {c : Nat}
  (hinv : ∀ j < ordK LR k, clsInvK n w (mask w) (n * w) (pidn n w) LR TR k PS PSI gens.length LB
    CJ RP c (ordK LR k) j = true)
  (hrep : ∀ l < c, clsRepK n w (mask w) (n * w) (pidn n w) LR TR k LB RP SZ ZC (ordK LR k) l = true)
include hQ hn hbs hinv hrep

@[expose] def labSet (n w : Nat) (LR TR : Nat → Nat) (k : Nat) (LB : Nat → Nat) (l : Nat) :
    Set (Equiv.Perm (Fin n)) :=
  {z | ∃ j < ordK LR k, LB j = l ∧ elemP n w LR TR k j = z}

omit hinv in
theorem ncard_labSet {l : Nat} (hl : l < c) : (labSet n w LR TR k LB l).ncard = SZ l := by
  have h := ncard_elems hQ hn hbs (fun j => Nat.beq (LB j) l)
  rw [(rep_facts hQ (hrep l hl)).2.2.2.2.1] at h
  rw [← h, labSet]
  congr 1
  ext z
  constructor <;> rintro ⟨j, hj, h1, h2⟩ <;> exact ⟨j, hj, by simpa using h1, h2⟩

theorem labSet_eq {l : Nat} (hl : l < c) :
    CFSG.Sporadic.SmallOddCore.conjClass (certificate hn gens words bv hbs).originalSubgroup (elemP n w LR TR k (RP l)) =
      labSet n w LR TR k LB l := by
  set G := (certificate hn gens words bv hbs).originalSubgroup with hGdef
  set x := elemP n w LR TR k (RP l)
  obtain ⟨hr1, hr2, -, hr4, -, hr6⟩ := rep_facts hQ (hrep l hl)
  have hx : x ∈ labSet n w LR TR k LB l := ⟨RP l, hr2, hr1, rfl⟩
  have hcl : ∀ g ∈ {g | g ∈ gens}, ∀ z ∈ labSet n w LR TR k LB l,
      g * z * g⁻¹ ∈ labSet n w LR TR k LB l := by
    rintro g hg z ⟨j, hj, hjl, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨-, -, h3⟩ := inv_facts hQ (hinv j hj)
    obtain ⟨ht, htl, hte⟩ := h3 i hi
    rw [List.getD_eq_getElem _ _ hi] at hte
    exact ⟨_, ht, htl.trans hjl, hte⟩
  have hsub : CFSG.Sporadic.SmallOddCore.conjClass G x ⊆ labSet n w LR TR k LB l := by
    rintro z ⟨h, hh, rfl⟩
    rw [hGdef, certificate_originalSubgroup] at hh
    exact conj_closed hcl h hh x hx
  have hcent : Nat.card ↥(G ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n)))) = ZC l := by
    rw [← hr6, ← ncard_elems hQ hn hbs, ← Nat.card_coe_set_eq]
    congr 2
    ext z
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      mem_group_iff hQ hn hbs]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hc⟩
      exact ⟨j, hj, decide_eq_true hc, rfl⟩
    · rintro ⟨j, hj, hc, rfl⟩
      exact ⟨⟨j, hj, rfl⟩, of_decide_eq_true hc⟩
  have hcard := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card G x
  rw [hcent, card_group hQ hn hbs, ← hr4] at hcard
  have hZ : 0 < ZC l := by
    rcases Nat.eq_zero_or_pos (ZC l) with h0 | h0
    · rw [h0, Nat.mul_zero] at hr4
      have := ordK_pos hQ
      omega
    · exact h0
  have hsz : (CFSG.Sporadic.SmallOddCore.conjClass G x).ncard = SZ l := Nat.eq_of_mul_eq_mul_right hZ hcard
  have hfin : (labSet n w LR TR k LB l).Finite := Set.toFinite _
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_labSet hQ hn hbs hrep hl, hsz]) hfin

theorem conjClass_elem {j : Nat} (hj : j < ordK LR k) :
    CFSG.Sporadic.SmallOddCore.conjClass (certificate hn gens words bv hbs).originalSubgroup (elemP n w LR TR k j) =
      labSet n w LR TR k LB (LB j) := by
  have hl := (inv_facts hQ (hinv j hj)).1
  rw [← labSet_eq hQ hn hbs hinv hrep hl]
  have hm : elemP n w LR TR k j ∈ CFSG.Sporadic.SmallOddCore.conjClass (certificate hn gens words bv hbs).originalSubgroup
      (elemP n w LR TR k (RP (LB j))) := by
    rw [labSet_eq hQ hn hbs hinv hrep hl]
    exact ⟨j, hj, rfl, rfl⟩
  ext z
  exact ⟨fun h => conjClass_trans h hm, fun h => conjClass_trans h (conjClass_symm hm)⟩

theorem mem_conjClass_elem_iff {j j' : Nat} (hj : j < ordK LR k) (hj' : j' < ordK LR k) :
    elemP n w LR TR k j' ∈ CFSG.Sporadic.SmallOddCore.conjClass (certificate hn gens words bv hbs).originalSubgroup
      (elemP n w LR TR k j) ↔ LB j' = LB j := by
  rw [conjClass_elem hQ hn hbs hinv hrep hj]
  constructor
  · rintro ⟨j'', hj'', hl, e⟩
    rw [← elemP_inj hQ hn hbs hj'' hj' e]
    exact hl
  · intro h
    exact ⟨j', hj', h, rfl⟩

omit hn hbs hinv in
theorem RP_anti {l₁ l₂ : Nat} (h : l₁ < l₂) (h₂ : l₂ < c) : RP l₂ < RP l₁ := by
  induction l₂ with
  | zero => omega
  | succ l ih =>
    have h1 := (rep_facts hQ (hrep (l + 1) h₂)).2.2.1 (by omega)
    simp only [Nat.add_sub_cancel] at h1
    rcases Nat.lt_or_ge l₁ l with h3 | h3
    · exact h1.trans (ih h3 (by omega))
    · have : l₁ = l := by omega
      subst this
      exact h1

end Classes

theorem chainK_classes' (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
    {LB CJ RP SZ ZC : Nat → Nat} {c cap L NB : Nat} (hL : ordK LR k ≤ NB * L)
    (hinv : ∀ s < NB, allBlk (s * L) (fun j => bIf(Nat.blt j (ordK LR k),
      clsInvK n w (mask w) (n * w) (pidn n w) LR TR k PS PSI gens.length LB CJ RP c
        (ordK LR k) j, true)) L = true)
    (hrep : ∀ l < c, clsRepK n w (mask w) (n * w) (pidn n w) LR TR k LB RP SZ ZC
      (ordK LR k) l = true)
    (hcap : ∀ l < c, SZ l ≤ cap) :
    classOK n (gens.map toTable).toArray (gens.map fun g => toTable g⁻¹).toArray
        (allTables (certificate hn gens words bv hbs)) cap = true ∧
      (classes n (gens.map toTable).toArray (gens.map fun g => toTable g⁻¹).toArray
        (allTables (certificate hn gens words bv hbs)) cap).map (fun c => c.2.1.size) =
        (List.range c).map SZ ∧
      (classes n (gens.map toTable).toArray (gens.map fun g => toTable g⁻¹).toArray
        (allTables (certificate hn gens words bv hbs)) cap).map
          (fun c => (allTables (certificate hn gens words bv hbs)).countP (commT n c.1)) =
        (List.range c).map ZC := by
  classical
  set N := ordK LR k with hNdef
  set e := elemP n w LR TR k with hedef
  have hinv' : ∀ j < N, clsInvK n w (mask w) (n * w) (pidn n w) LR TR k PS PSI gens.length LB
      CJ RP c N j = true := fun j hj => by
    have := of_blocks hQ hL hinv j hj
    simpa [bIf_eq, Nat.blt_eq, hj] using this
  set gT := (gens.map toTable).toArray
  set gI := (gens.map fun g => toTable g⁻¹).toArray
  set gg : Nat → Equiv.Perm (Fin n) := fun l => gens.getD l 1
  have h32 := chainK_h32 hQ
  have hg : ∀ l < gT.size, Rep n gT[l]! (gg l) ∧ Rep n gI[l]! (gg l)⁻¹ := by
    intro l hl
    have hl' : l < gens.length := by simpa [gT] using hl
    have hl2 : l < gI.size := by simpa [gI] using hl'
    have e1 : gT[l]! = toTable gens[l] := by rw [getElem!_pos gT l hl]; simp [gT]
    have e2 : gI[l]! = toTable gens[l]⁻¹ := by rw [getElem!_pos gI l hl2]; simp [gI]
    have e3 : gg l = gens[l] := List.getD_eq_getElem _ _ hl'
    rw [e1, e2, e3]
    exact ⟨rep_toTable h32 _, rep_toTable h32 _⟩
  have hK : genK gT gg = (certificate hn gens words bv hbs).originalSubgroup := by
    have hset : {g | ∃ l < gT.size, gg l = g} = {g | g ∈ gens} := by
      ext g
      simp only [gT, gg, List.size_toArray, List.length_map, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨l, hl, rfl⟩
        rw [List.getD_eq_getElem _ _ hl]
        exact List.getElem_mem hl
      · intro hg
        obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
        exact ⟨l, hl, List.getD_eq_getElem _ _ hl⟩
    rw [certificate_originalSubgroup, genK, hset]
  set xs := ((List.range N).map e).reverse with hxsdef
  have hX : List.Forall₂ (Rep n) (allTables (certificate hn gens words bv hbs)) xs := forall₂_allTables_elem hQ hn hbs
  have hlen : (allTables (certificate hn gens words bv hbs)).length = N := by rw [hX.length_eq]; simp [xs]
  have hxs : ∀ p < N, xs.getD p 1 = e (N - 1 - p) := fun p hp => by
    rw [List.getD_eq_getElem _ _ (by simpa [xs] using hp)]
    simp only [xs, List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map,
      List.length_range]
  have hcap' : ∀ y ∈ xs, (CFSG.Sporadic.SmallOddCore.conjClass (genK gT gg) y).ncard ≤ cap := by
    intro y hy
    rw [List.mem_reverse, List.mem_map] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' := List.mem_range.1 hj
    have hl := (inv_facts hQ (hinv' j hj')).1
    rw [hK, conjClass_elem hQ hn hbs hinv' hrep hj', ncard_labSet hQ hn hbs hrep hl]
    exact hcap _ hl
  have hnd : xs.Nodup := List.nodup_reverse.2 (elemP_nodup hQ hn hbs)
  have hmem : ∀ z, z ∈ xs ↔ z ∈ genK gT gg := fun z => by
    rw [hK, List.mem_reverse]
    exact mem_elemP_iff hQ hn hbs z
  obtain ⟨hok, hsz⟩ := classes_spec hg hX hcap' hnd hmem
  have hR := findReps_spec hg hX hcap'
  have hFirst : ∀ p < N, (First (genK gT gg) xs p ↔ RP (LB (N - 1 - p)) = N - 1 - p) := by
    intro p hp
    have hmemc : ∀ p' < p, (xs.getD p' 1 ∈ CFSG.Sporadic.SmallOddCore.conjClass (genK gT gg)
        (xs.getD p 1) ↔ LB (N - 1 - p') = LB (N - 1 - p)) := fun p' hp' => by
      rw [hK, hxs p' (by omega), hxs p hp]
      exact mem_conjClass_elem_iff hQ hn hbs hinv' hrep (by omega) (by omega)
    unfold First
    constructor
    · intro hF
      obtain ⟨-, hjr, -⟩ := inv_facts hQ (hinv' (N - 1 - p) (by omega))
      have hl := (inv_facts hQ (hinv' (N - 1 - p) (by omega))).1
      obtain ⟨hr1, hr2, -⟩ := rep_facts hQ (hrep _ hl)
      by_contra hne
      have hp' : N - 1 - RP (LB (N - 1 - p)) < p := by omega
      apply hF _ hp'
      rw [hmemc _ hp']
      have : N - 1 - (N - 1 - RP (LB (N - 1 - p))) = RP (LB (N - 1 - p)) := by omega
      rw [this, hr1]
    · intro hr p' hp' hm
      rw [hmemc p' hp'] at hm
      have h2 := (inv_facts hQ (hinv' (N - 1 - p') (by omega))).2.1
      rw [hm, hr] at h2
      omega
  have hreps : findReps n gT gI (allTables (certificate hn gens words bv hbs)) cap = (List.range c).map fun l => N - 1 - RP l := by
    rw [hR, hlen]
    apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
    · exact List.pairwise_lt_range.filter _
    · rw [List.pairwise_map]
      refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab => ?_
      have hb' := List.mem_range.1 hb
      have h1 := RP_anti hQ hrep hab hb'
      have h2 := (rep_facts hQ (hrep a (List.mem_range.1 ha))).2.1
      omega
    · intro p
      rw [List.mem_filter, List.mem_range, List.mem_map, decide_eq_true_eq]
      constructor
      · rintro ⟨hp, hF⟩
        have hl := (inv_facts hQ (hinv' (N - 1 - p) (by omega))).1
        refine ⟨LB (N - 1 - p), List.mem_range.2 hl, ?_⟩
        rw [(hFirst p hp).1 hF]
        omega
      · rintro ⟨l, hl, rfl⟩
        have hl' := List.mem_range.1 hl
        obtain ⟨hr1, hr2, -⟩ := rep_facts hQ (hrep l hl')
        refine ⟨by omega, (hFirst _ (by omega)).2 ?_⟩
        have : N - 1 - (N - 1 - RP l) = RP l := by omega
        rw [this, hr1]
  refine ⟨hok, ?_, ?_⟩
  · rw [hsz, hreps, List.map_map]
    apply List.map_congr_left
    intro l hl
    have hl' := List.mem_range.1 hl
    have hr2 := (rep_facts hQ (hrep l hl')).2.1
    simp only [Function.comp_apply]
    rw [hxs _ (by omega), show N - 1 - (N - 1 - RP l) = RP l by omega, hK,
      labSet_eq hQ hn hbs hinv' hrep hl', ncard_labSet hQ hn hbs hrep hl']
  · rw [classes, hreps, List.map_map, List.map_map]
    apply List.map_congr_left
    intro l hl
    have hl' := List.mem_range.1 hl
    obtain ⟨-, hr2, -, -, -, hr6⟩ := rep_facts hQ (hrep l hl')
    have hrep' := rep_get hX (p := N - 1 - RP l) (by omega)
    rw [hxs _ (by omega), show N - 1 - (N - 1 - RP l) = RP l by omega] at hrep'
    simp only [Function.comp_apply]
    rw [countP_allTables hQ hn hbs
      (q := fun x => decide (e (RP l) * x = x * e (RP l))) fun X x hX' => commT_eq hrep' hX', ← hr6]
    apply List.countP_congr
    intro j _
    simp only [decide_eq_true_eq, hedef]
    exact eq_comm

end CFSG.KS.SporSch.MOC

end
