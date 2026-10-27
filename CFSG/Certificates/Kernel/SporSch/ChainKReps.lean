module

public import Certificates.Data.Kernel.SporSch.MathieuCls
public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
public import CFSG.Certificates.Kernel.SporSch.ConjClosureSpec

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu CFSG.KS.SporSch.ClsSpec
open CFSG.Sporadic.SmallOddCore

variable {n w : Nat}

theorem fld_packL (w : Nat) : ∀ l : List Nat, (∀ x ∈ l, x < 2 ^ w) →
    PF.Fld w (packL w l) (fun i => l.getD i 0)
  | [], _ => PF.fld_congr (PF.fld_zero w) (fun i => by simp)
  | x :: l, h => by
    have e : packL w (x :: l) = x ||| (packL w l <<< (w * 1)) := by
      rw [Nat.mul_one]
      rfl
    rw [e]
    refine PF.fld_congr (PF.fld_or (PF.fld_one (h x List.mem_cons_self))
      (PF.fld_shl 1 (fld_packL w l fun y hy => h y (List.mem_cons_of_mem x hy)))) fun i => ?_
    rcases i with _ | i
    · simp
    · simp

theorem prep_packL {g : Equiv.Perm (Fin n)} (hw : n + 1 < 2 ^ w) :
    PRep n w (packL w (imageList g)) g ∧ packL w (imageList g) >>> (n * w) = 0 := by
  have hl : ∀ x ∈ imageList g, x < 2 ^ w := by
    intro x hx
    simp only [imageList, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Nat.lt_trans (g i).2 (by omega)
  have hF := fld_packL w _ hl
  refine ⟨fun x => ?_, PF.shr_zero_of_fld (PF.w_pos hw) hF fun i hi => ?_⟩
  · rw [PF.pg_of_fld hF (by
      rw [List.getD_eq_getElem _ _ (by simp [imageList])]
      exact hl _ (List.getElem_mem _))]
    rw [List.getD_eq_getElem _ _ (by simp [imageList])]
    simp [imageList]
  · rw [List.getD_eq_default _ _ (by simpa [imageList] using hi)]

theorem prep_conjK {G Gi X : Nat} {g x : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hG : PRep n w G g) (hGi : PRep n w Gi g⁻¹) (hX : PRep n w X x) :
    PRep n w (conjK n w (mask w) G Gi X) (g * x * g⁻¹) := by
  rw [mul_assoc]
  exact prep_pcomp hn hG (prep_pcomp hn hX hGi)

theorem conjK_shr {G Gi X : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) :
    conjK n w (mask w) G Gi X >>> (n * w) = 0 :=
  PF.pcomp_shr _ _ hn hw

@[expose] noncomputable def cycF (w : Nat) (Z i : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih p c => strictN (pg w (mask w) Z p) (fun q => nIf(Nat.beq q i, c, ih q (Nat.succ c))))

theorem cycLen_eq (n w Z i : Nat) : cycLen n w (mask w) Z i = cycF w Z i n i 1 := rfl

theorem cycF_succ (w Z i t p c : Nat) :
    cycF w Z i (t + 1) p c =
      if pg w (mask w) Z p = i then c else cycF w Z i t (pg w (mask w) Z p) (c + 1) := by
  change strictN (pg w (mask w) Z p) (fun q => nIf(Nat.beq q i, c, cycF w Z i t q (Nat.succ c)))
    = _
  rw [Orb.strictN_eq, Orb.nIf_eq, beq_dec]
  simp

theorem pow_apply_succ (z : Equiv.Perm (Fin n)) (b : Nat) (x : Fin n) :
    (z ^ (b + 1)) x = z ((z ^ b) x) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

theorem cycF_spec {Z : Nat} {z : Equiv.Perm (Fin n)} (hZ : PRep n w Z z) (x : Fin n) :
    ∀ t c, 1 ≤ c → (∀ b, 0 < b → b < c → (z ^ b) x ≠ x) →
      Function.minimalPeriod z x ≤ c - 1 + t →
      cycF w Z x t ((z ^ (c - 1)) x).val c = Function.minimalPeriod z x := by
  have hper : x ∈ Function.periodicPts z := by
    refine ⟨orderOf z, orderOf_pos z, ?_⟩
    change z^[orderOf z] x = x
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  have hmp := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hfix : (z ^ Function.minimalPeriod z x) x = x := by
    have := Function.isPeriodicPt_minimalPeriod z x
    rwa [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow] at this
  have hne : ∀ b, 0 < b → b < Function.minimalPeriod z x → (z ^ b) x ≠ x := by
    intro b hb hbm e
    refine Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega) hbm ?_
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow]
    exact e
  intro t
  induction t with
  | zero =>
    intro c hc hb hle
    exfalso
    rcases Nat.lt_or_ge (Function.minimalPeriod z x) c with h | h
    · exact hb _ hmp h hfix
    · omega
  | succ t ih =>
    intro c hc hb hle
    rw [cycF_succ, hZ ((z ^ (c - 1)) x)]
    have e : (z ((z ^ (c - 1)) x)) = (z ^ c) x := by
      rw [← pow_apply_succ, Nat.sub_add_cancel hc]
    rw [e]
    by_cases hc' : ((z ^ c) x).val = x.val
    · simp only [hc', ↓reduceIte]
      have hx : (z ^ c) x = x := Fin.ext hc'
      rcases Nat.lt_trichotomy c (Function.minimalPeriod z x) with h | h | h
      · exact absurd hx (hne c (by omega) h)
      · exact h
      · exact absurd hfix (hb _ hmp h)
    · simp only [hc', ↓reduceIte]
      have := ih (c + 1) (by omega) (fun b hb0 hbc => by
        rcases Nat.lt_or_ge b c with h | h
        · exact hb b hb0 h
        · have : b = c := by omega
          subst this
          exact fun e => hc' (congrArg Fin.val e)) (by omega)
      simpa using this

theorem cycLen_spec {Z : Nat} {z : Equiv.Perm (Fin n)} (hZ : PRep n w Z z) (x : Fin n) :
    cycLen n w (mask w) Z x = Function.minimalPeriod z x := by
  rw [cycLen_eq]
  have := cycF_spec hZ x n 1 le_rfl (fun b hb hb1 => absurd hb1 (by omega)) (by
    have := Function.minimalPeriod_le_card (f := z) (x := x)
    simpa using this)
  simpa using this

theorem foldr_lcm_dvd (f : Nat → Nat) (m : Nat) :
    ∀ l : List Nat, l.foldr (fun i s => Nat.lcm s (f i)) 1 ∣ m ↔ ∀ i ∈ l, f i ∣ m
  | [] => by simp
  | i :: l => by
    rw [List.foldr_cons, Nat.lcm_dvd_iff, foldr_lcm_dvd f m l]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem orderOf_of_ordC {Z : Nat} {z : Equiv.Perm (Fin n)} (hZ : PRep n w Z z) :
    orderOf z = ordC n w (mask w) Z := by
  have e : ordC n w (mask w) Z =
      (List.range n).foldr (fun i s => Nat.lcm s (cycLen n w (mask w) Z i)) 1 := foldN_eq _ _ _
  have hpow : ∀ m, z ^ m = 1 ↔ ordC n w (mask w) Z ∣ m := by
    intro m
    rw [e, foldr_lcm_dvd]
    constructor
    · intro h i hi
      have hi' := List.mem_range.1 hi
      have := cycLen_spec hZ ⟨i, hi'⟩
      simp only at this
      rw [this, ← Function.isPeriodicPt_iff_minimalPeriod_dvd, Function.IsPeriodicPt,
        Function.IsFixedPt, ← Equiv.Perm.coe_pow, h]
      rfl
    · intro h
      ext x
      have := h x.val (List.mem_range.2 x.2)
      rw [cycLen_spec hZ x, ← Function.isPeriodicPt_iff_minimalPeriod_dvd, Function.IsPeriodicPt,
        Function.IsFixedPt, ← Equiv.Perm.coe_pow] at this
      rw [this]
      rfl
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((hpow _).2 dvd_rfl))
    ((hpow _).1 (pow_orderOf_eq_one z))

theorem clsHdK_facts {mx cap : Nat} {d : ClsD} (h : clsHdK n w (mask w) mx cap d = true) :
    0 < d.c ∧ d.c ≤ cap ∧ d.r < d.c ∧ d.ST d.r = d.R ∧ ordC n w (mask w) d.R = mx := by
  unfold clsHdK at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_dec, decide_eq_true_eq] at h
  exact h

theorem clsElemK_facts {A Ai B Bi : Nat} {d : ClsD} {k : Nat} (hk : k < d.c)
    (h : clsElemK n w (mask w) (n * w) A Ai B Bi d k = true) :
    (k + 1 < d.c → d.ST k < d.ST (k + 1)) ∧ d.ST k >>> (n * w) = 0 ∧
      d.IA k < d.c ∧ conjK n w (mask w) A Ai (d.ST k) = d.ST (d.IA k) ∧
      d.IB k < d.c ∧ conjK n w (mask w) B Bi (d.ST k) = d.ST (d.IB k) ∧
      (k ≠ d.r → d.PA k < d.c ∧ d.DP (d.PA k) < d.DP k ∧
        d.ST k = if d.LB k = 0 then conjK n w (mask w) A Ai (d.ST (d.PA k))
          else conjK n w (mask w) B Bi (d.ST (d.PA k))) := by
  unfold clsElemK at h
  simp only [bAnd_eq, Orb.strictB_eq] at h
  simp only [Orb.bIf_eq, Orb.nIf_eq, Nat.blt_eq, hk, ↓reduceIte, Bool.and_eq_true, beq_dec,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun hk1 => by simpa [hk1] using h1, by simpa using h2, h3, h4, h5, h6, fun hr => ?_⟩
  simp only [hr, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h7
  obtain ⟨h8, h9, h10⟩ := h7
  exact ⟨Nat.blt_eq.mp h8, Nat.blt_eq.mp h9, h10⟩

theorem notInK_spec {d : ClsD} {x : Nat} (h : notInK d x = true) : ∀ k < d.c, d.ST k ≠ x := by
  unfold notInK at h
  generalize d.c = c at h
  induction c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | succ c ih =>
    change bAnd(bIf(Nat.beq (d.ST c) x, false, true), Nat.rec (motive := fun _ => Bool) true
      (fun k ih => bAnd(bIf(Nat.beq (d.ST k) x, false, true), ih)) c) = true at h
    rw [bAnd_eq, Bool.and_eq_true, Orb.bIf_eq, beq_dec] at h
    intro k hk
    rcases Nat.lt_or_ge k c with hkc | hkc
    · exact ih h.2 k hkc
    · have : k = c := by omega
      subst this
      intro e
      simp [e] at h

theorem lt_of_consec {c : Nat} {ST : Nat → Nat} (h : ∀ k, k + 1 < c → ST k < ST (k + 1)) :
    ∀ i j, i < j → j < c → ST i < ST j := by
  intro i j hij hj
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero _)
  | succ j ih =>
    rcases Nat.lt_or_ge i j with h' | h'
    · exact Nat.lt_trans (ih h' (by omega)) (h j hj)
    · have : i = j := by omega
      subst this
      exact h i hj

section Datum

variable {gA gB : Equiv.Perm (Fin n)} {A Ai B Bi : Nat} (hn : n < 2 ^ 32)
  (pA : PRep n w A gA) (pAi : PRep n w Ai gA⁻¹) (pB : PRep n w B gB) (pBi : PRep n w Bi gB⁻¹)
  {mx cap : Nat} {d : ClsD} (hd : clsHdK n w (mask w) mx cap d = true)
  (he : ∀ k < d.c, clsElemK n w (mask w) (n * w) A Ai B Bi d k = true)
  {r : Equiv.Perm (Fin n)} (pR : PRep n w d.R r)
include hn pA pAi pB pBi hd he pR

theorem entry_mem_class :
    ∀ k < d.c, ∃ z ∈ CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r, PRep n w (d.ST k) z := by
  set K := Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))
  obtain ⟨-, -, hr, hST, -⟩ := clsHdK_facts hd
  have hAK : gA ∈ K := Subgroup.subset_closure (by simp)
  have hBK : gB ∈ K := Subgroup.subset_closure (by simp)
  suffices H : ∀ m, ∀ k < d.c, d.DP k = m → ∃ z ∈ CFSG.Sporadic.SmallOddCore.conjClass K r,
      PRep n w (d.ST k) z from fun k hk => H _ k hk rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk hm
    by_cases hkr : k = d.r
    · subst hkr
      refine ⟨r, ⟨1, K.one_mem, by simp⟩, ?_⟩
      rw [hST]
      exact pR
    · obtain ⟨-, -, -, -, -, -, h7⟩ := clsElemK_facts hk (he k hk)
      obtain ⟨hp, hdp, hx⟩ := h7 hkr
      obtain ⟨z, hz, pz⟩ := ih _ (hm ▸ hdp) _ hp rfl
      rw [hx]
      split
      · exact ⟨gA * z * gA⁻¹, conj_mem_conjClass hAK hz, prep_conjK hn pA pAi pz⟩
      · exact ⟨gB * z * gB⁻¹, conj_mem_conjClass hBK hz, prep_conjK hn pB pBi pz⟩

theorem mem_class_iff (z : Equiv.Perm (Fin n)) :
    z ∈ CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r ↔
      ∃ k < d.c, PRep n w (d.ST k) z := by
  obtain ⟨-, -, hr, hST, -⟩ := clsHdK_facts hd
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine conj_closed (S := {z | ∃ k < d.c, PRep n w (d.ST k) z}) ?_ g hg r
      ⟨d.r, hr, by rw [hST]; exact pR⟩
    rintro g' hg' z ⟨k, hk, pz⟩
    obtain ⟨-, -, h3, h4, h5, h6, -⟩ := clsElemK_facts hk (he k hk)
    rcases hg' with rfl | hg'
    · exact ⟨_, h3, by rw [← h4]; exact prep_conjK hn pA pAi pz⟩
    · rw [Set.mem_singleton_iff] at hg'
      subst hg'
      exact ⟨_, h5, by rw [← h6]; exact prep_conjK hn pB pBi pz⟩
  · rintro ⟨k, hk, pz⟩
    obtain ⟨z', hz', pz'⟩ := entry_mem_class hn pA pAi pB pBi hd he pR k hk
    rw [prep_unique pz pz']
    exact hz'

theorem ncard_class (hw : 0 < w) :
    (CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r).ncard = d.c := by
  have hE := entry_mem_class hn pA pAi pB pBi hd he pR
  refine Set.ncard_eq_of_bijective (fun k hk => Classical.choose (hE k hk))
    (fun z hz => ?_) (fun k hk => (Classical.choose_spec (hE k hk)).1) (fun i j hi hj e => ?_)
  · obtain ⟨k, hk, pz⟩ := (mem_class_iff hn pA pAi pB pBi hd he pR z).1 hz
    exact ⟨k, hk, prep_unique (Classical.choose_spec (hE k hk)).2 pz⟩
  · have p1 := (Classical.choose_spec (hE i hi)).2
    have p2 := (Classical.choose_spec (hE j hj)).2
    rw [e] at p1
    have s1 := (clsElemK_facts hi (he i hi)).2.1
    have s2 := (clsElemK_facts hj (he j hj)).2.1
    have eq : d.ST i = d.ST j := PF.eq_of_fields hw s1 s2 fun t ht => by
      rw [p1 ⟨t, ht⟩, p2 ⟨t, ht⟩]
    have hinc := lt_of_consec (c := d.c) (ST := d.ST) fun k hk =>
      (clsElemK_facts (by omega) (he k (by omega))).1 hk
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd eq (Nat.ne_of_lt (hinc i j h hj))
    · exact h
    · exact absurd eq (Nat.ne_of_gt (hinc j i h hi))

end Datum

theorem genK_pair (gA gB : Equiv.Perm (Fin n)) :
    genK (pairTables gA gB) (fun l => if l = 0 then gA else gB) =
      Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) := by
  unfold genK
  congr 1
  ext g
  simp only [pairTables, List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd,
    Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases l with _ | l
    · simp
    · simp
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩

theorem rep_pair (hn : n < 2 ^ 32) (gA gB : Equiv.Perm (Fin n)) :
    ∀ l < (pairTables gA gB).size,
      Rep n (pairTables gA gB)[l]! ((fun l => if l = 0 then gA else gB) l) ∧
        Rep n (pairTables gA⁻¹ gB⁻¹)[l]! ((fun l => if l = 0 then gA else gB) l)⁻¹ := by
  intro l hl
  simp only [pairTables, List.size_toArray, List.length_cons, List.length_nil] at hl
  rcases l with _ | _ | l
  · exact ⟨rep_toTable hn gA, rep_toTable hn gA⁻¹⟩
  · exact ⟨rep_toTable hn gB, rep_toTable hn gB⁻¹⟩
  · omega

theorem reps_of_classes {gA gB : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32) {mx cap : Nat}
    {reps : List (Equiv.Perm (Fin n))} {sz : Nat → Nat}
    (hcls : ∀ j (hj : j < reps.length), (CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) reps[j]).ncard = sz j ∧
        sz j ≤ cap ∧ orderOf reps[j] = mx)
    (hdisj : ∀ i j (hi : i < reps.length) (hj : j < reps.length), i < j →
      reps[j] ∉ CFSG.Sporadic.SmallOddCore.conjClass
        (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) reps[i])
    (hmx : 0 < mx) {X : List Table} (hX : X.length = ((List.range reps.length).map sz).sum) :
    repsOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) X (reps.map toTable) cap = true ∧
      repSizes n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable) cap =
        (List.range reps.length).map sz ∧
      (reps.map toTable).all (ordTest n mx) = true := by
  set gens := pairTables gA gB
  set gensInv := pairTables gA⁻¹ gB⁻¹
  set gg : Nat → Equiv.Perm (Fin n) := fun l => if l = 0 then gA else gB
  have hgK := genK_pair gA gB
  have hg := rep_pair hn gA gB
  set cc := fun r : Equiv.Perm (Fin n) => conjClosure n gens gensInv (toTable r) cap
  have hcap : ∀ j (hj : j < reps.length),
      (CFSG.Sporadic.SmallOddCore.conjClass (genK gens gg) reps[j]).ncard ≤ cap := by
    intro j hj
    rw [hgK, (hcls j hj).1]
    exact (hcls j hj).2.1
  have hspec := fun j (hj : j < reps.length) =>
    conjClosure_spec hg (rep_toTable hn reps[j]) (hcap j hj)
  have hsizes : (reps.map toTable).map (fun r => (conjClosure n gens gensInv r cap).1.size) =
      (List.range reps.length).map sz := by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    have hj : j < reps.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [conjClosure_size hg (rep_toTable hn reps[j]) (hcap j hj), hgK, (hcls j hj).1]
  have hidx : ∀ r ∈ reps, ∃ j, ∃ hj : j < reps.length, reps[j] = r := fun r hr =>
    List.mem_iff_getElem.1 hr
  refine ⟨?_, hsizes, ?_⟩
  · unfold repsOK
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro c hc
      simp only [List.map_map, List.mem_map, Function.comp_apply] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      obtain ⟨j, hj, rfl⟩ := hidx r hr
      exact (hspec j hj).1
    · apply keysDistinct_of
      rw [List.map_flatMap, List.flatMap_map, List.flatMap_map, List.nodup_flatMap]
      refine ⟨fun r hr => ?_, List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_⟩
      · obtain ⟨j, hj, rfl⟩ := hidx r hr
        exact (hspec j hj).2.1
      · intro a ha hb
        simp only [List.mem_map] at ha hb
        obtain ⟨t, ht, rfl⟩ := ha
        obtain ⟨t', ht', e⟩ := hb
        obtain ⟨z, hz, pz⟩ := (hspec i hi).2.2.1 t ht
        obtain ⟨z', hz', pz'⟩ := (hspec j hj).2.2.1 t' ht'
        have ezz := eq_of_key pz' pz e
        rw [hgK] at hz hz'
        rw [ezz] at hz'
        exact hdisj i j hi hj hij (conjClass_trans (conjClass_symm hz') hz)
    · rw [hX, ← hsizes, List.map_map]
      rfl
  · rw [List.all_eq_true]
    intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    obtain ⟨j, hj, rfl⟩ := hidx r hr
    rw [ordTest_iff perm_faithful (rep_toTable hn _) hmx]
    exact (hcls j hj).2.2

theorem range_map_getD {α : Type*} {CL : List α} {d0 : α} (f : α → Nat) {L : Nat}
    (hL : L = CL.length) : (List.range L).map (fun j => f (CL.getD j d0)) = CL.map f := by
  subst hL
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h2)]

theorem reps_of_data {gA gB : Equiv.Perm (Fin n)} {A Ai B Bi : Nat} (hn : n < 2 ^ 32)
    (hw : 0 < w) (pA : PRep n w A gA) (pAi : PRep n w Ai gA⁻¹) (pB : PRep n w B gB)
    (pBi : PRep n w Bi gB⁻¹) {mx cap : Nat} {d0 : ClsD} {CL : List ClsD}
    (hcls : ∀ j < CL.length, clsHdK n w (mask w) mx cap (CL.getD j d0) = true ∧
      (∀ k < (CL.getD j d0).c, clsElemK n w (mask w) (n * w) A Ai B Bi (CL.getD j d0) k = true) ∧
      ∀ i < j, notInK (CL.getD i d0) (CL.getD j d0).R = true)
    {reps : List (Equiv.Perm (Fin n))}
    (hR : reps.length = CL.length ∧ ∀ j < CL.length, PRep n w (CL.getD j d0).R (reps.getD j 1))
    (hmx : 0 < mx) {X : List Table} (hX : X.length = (CL.map ClsD.c).sum) :
    repsOK n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) X (reps.map toTable) cap = true ∧
      repSizes n (pairTables gA gB) (pairTables gA⁻¹ gB⁻¹) (reps.map toTable) cap =
        CL.map ClsD.c ∧
      (reps.map toTable).all (ordTest n mx) = true := by
  have hRj : ∀ j (hj : j < reps.length), PRep n w (CL.getD j d0).R reps[j] := fun j hj => by
    rw [← List.getD_eq_getElem _ 1 hj]
    exact hR.2 j (hR.1 ▸ hj)
  have hmap := range_map_getD (d0 := d0) ClsD.c hR.1
  rw [← hmap] at hX ⊢
  refine reps_of_classes hn (sz := fun j => (CL.getD j d0).c) (fun j hj => ?_)
    (fun i j hi hj hij hrj => ?_) hmx hX
  · obtain ⟨hd, he, -⟩ := hcls j (hR.1 ▸ hj)
    have hf := clsHdK_facts hd
    exact ⟨ncard_class hn pA pAi pB pBi hd he (hRj j hj) hw, hf.2.1,
      (orderOf_of_ordC (hRj j hj)).trans hf.2.2.2.2⟩
  · obtain ⟨hdi, hei, -⟩ := hcls i (hR.1 ▸ hi)
    obtain ⟨hdj, hej, hnot⟩ := hcls j (hR.1 ▸ hj)
    obtain ⟨k, hk, pk⟩ := (mem_class_iff hn pA pAi pB pBi hdi hei (hRj i hi) _).1 hrj
    have hfj := clsHdK_facts hdj
    have sR : (CL.getD j d0).R >>> (n * w) = 0 := by
      rw [← hfj.2.2.2.1]
      exact (clsElemK_facts hfj.2.2.1 (hej _ hfj.2.2.1)).2.1
    have sk := (clsElemK_facts hk (hei k hk)).2.1
    have eq : (CL.getD i d0).ST k = (CL.getD j d0).R :=
      PF.eq_of_fields hw sk sR fun t ht => by rw [pk ⟨t, ht⟩, hRj j hj ⟨t, ht⟩]
    exact notInK_spec (hnot i hij) k hk eq

@[expose] noncomputable def wsVal (mx my : Nat) (ws : List (List Nat × Nat))
    (x y : Equiv.Perm (Fin n)) : Bool :=
  ws.all fun p => decide (p.2 = 0) || decide (orderOf (wordElts x y mx my p.1).prod = p.2)

theorem wordsTest_eq_val {X Y : Table} {x y : Equiv.Perm (Fin n)} (hX : Rep n X x)
    (hY : Rep n Y y) (mx my : Nat) (ws : List (List Nat × Nat)) :
    wordsTest n mx my ws X Y = wsVal mx my ws x y := by
  unfold wordsTest wsVal
  congr 1
  funext p
  exact ordW_eq (forall₂_wordTbls hX hY mx my p.1) p.2

theorem repsTotal_eq {gens gensInv : Array Table} {reps : List (Equiv.Perm (Fin n))}
    {Y : List Table} {cap : Nat} {rel : Table → Table → Bool} {L : Nat} {c N : Nat → Nat}
    (hlen : reps.length = L)
    (hs : ∀ j (hj : j < reps.length), (conjClosure n gens gensInv (toTable reps[j]) cap).1.size =
      c j)
    (hN : ∀ j (hj : j < reps.length), Y.countP (rel (toTable reps[j])) = N j) :
    repsTotal n gens gensInv (reps.map toTable) Y cap rel =
      ((List.range L).map fun j => c j * N j).sum := by
  unfold repsTotal
  congr 1
  apply List.ext_getElem (by simp [hlen])
  intro j h1 h2
  have hj : j < reps.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [hs j hj, hN j hj]

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem countP_orderTables_words {mx my : Nat} (hmy : 0 < my) (ws : List (List Nat × Nat))
    (r : Equiv.Perm (Fin n)) :
    (orderTables (certificate hn gens words bv hbs) my).countP
        (wordsTest n mx my ws (toTable r)) =
      ((enumeration (certificate hn gens words bv hbs)).map (1 * ·)).countP
        (fun y => decide (orderOf y = my) && wsVal mx my ws r y) := by
  have h32 := chainK_h32 hQ
  rw [countP_forall₂ (f := wordsTest n mx my ws (toTable r)) (q := wsVal mx my ws r)
    (fun T y hT => wordsTest_eq_val (rep_toTable h32 r) hT mx my ws)
    (forall₂_orderTables h32 _ hmy), List.countP_reverse, List.countP_filter]
  simp only [one_mul, List.map_id']
  congr 1
  funext y
  rw [Bool.and_comm]

omit hn hbs in
theorem wordP_eq {R : Nat} {r : Equiv.Perm (Fin n)} (pR : PRep n w R r) {mx my : Nat}
    (hmy : 0 < my) (ws : List (List Nat × Nat)) :
    ∀ P x, PRep n w P x → P >>> (n * w) = 0 →
      bAnd(ordIs n w (mask w) (pidn n w) P (Nat.sub my (nat_lit 1)),
        wordOrdK n w (mask w) (pidn n w) mx my ws R P) =
      (decide (orderOf x = my) && wsVal mx my ws r x) := by
  intro P x hP sP
  have hsz := chainK_szOK hQ
  have h32 := chainK_h32 hQ
  rw [bAnd_eq]
  congr 1
  · exact ordIs_eq hsz hP sP hmy
  · rw [wordOrdK_eq ws hsz pR hP, wordsTest_eq_val (rep_toTable h32 r) (rep_toTable h32 x)]

theorem countWord' {R : Nat} {r : Equiv.Perm (Fin n)} (pR : PRep n w R r) {mx my : Nat}
    (hmy : 0 < my) (ws : List (List Nat × Nat)) (hk : 0 < k) {CS : List Nat}
    (hCS : CS.length = rcnt (LR 0))
    (hc : ∀ k₀ < rcnt (LR 0), cntWordK n w (mask w) (n * w) (pidn n w) LR TR k mx my ws R k₀ =
      CS.getD k₀ 0) :
    (orderTables (certificate hn gens words bv hbs) my).countP
        (wordsTest n mx my ws (toTable r)) = CS.sum := by
  have h32 := chainK_h32 hQ
  rw [countP_orderTables_words hQ hn hbs hmy ws r, countP_coset1 hQ hn hbs hk]
  refine sum_range_getD hCS fun k₀ hk₀ => ?_
  rw [← hc k₀ hk₀]
  obtain ⟨t0, s0⟩ := tr_facts hQ hk hk₀
  have e1 : cntWordK n w (mask w) (n * w) (pidn n w) LR TR k mx my ws R k₀ =
      enumFrom n w (mask w) (n * w) LR TR (fun y => bAnd(ordIs n w (mask w) (pidn n w) y
          (Nat.sub my (nat_lit 1)), wordOrdK n w (mask w) (pidn n w) mx my ws R y))
        (k - 1) 1 (TR (roff n (n * w) (LR 0) + k₀)) 0 := by
    unfold cntWordK
    rw [Orb.strictN_eq]
    rfl
  rw [e1, enumFrom_spec hQ (wordP_eq hQ pR hmy ws) (k - 1) 1 (by omega) _
    (1 * trP n w LR TR 0 k₀) 0 (by rw [one_mul]; exact t0) s0, Nat.zero_add]

theorem countWord2' {R : Nat} {r : Equiv.Perm (Fin n)} (pR : PRep n w R r) {mx my : Nat}
    (hmy : 0 < my) (ws : List (List Nat × Nat)) (hk : 2 ≤ k) {CS : List (List Nat)}
    (hc : Cnt2 LR CS (cntWord2K n w (mask w) (n * w) (pidn n w) LR TR k mx my ws R)) :
    (orderTables (certificate hn gens words bv hbs) my).countP
        (wordsTest n mx my ws (toTable r)) = (CS.map List.sum).sum := by
  have h32 := chainK_h32 hQ
  have hw := PF.w_pos hQ.2.1
  rw [countP_orderTables_words hQ hn hbs hmy ws r, countP_coset2 hQ hn hbs hk, ← sum_counts2 hc]
  congr 1
  apply List.map_congr_left
  intro k₀ hk₀
  congr 1
  apply List.map_congr_left
  intro k₁ hk₁
  obtain ⟨t0, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hk₀)
  obtain ⟨t1, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hk₁)
  have e1 : cntWord2K n w (mask w) (n * w) (pidn n w) LR TR k mx my ws R k₀ k₁ =
      enumFrom n w (mask w) (n * w) LR TR (fun y => bAnd(ordIs n w (mask w) (pidn n w) y
          (Nat.sub my (nat_lit 1)), wordOrdK n w (mask w) (pidn n w) mx my ws R y))
        (k - 2) 2 (pcomp n w (mask w) (pcomp n w (mask w) (pidn n w)
          (TR (roff n (n * w) (LR 0) + k₀))) (TR (roff n (n * w) (LR 1) + k₁))) 0 := by
    unfold cntWord2K start2
    rw [Orb.strictN_eq, Orb.strictN_eq]
    rfl
  rw [e1, enumFrom_spec hQ (wordP_eq hQ pR hmy ws) (k - 2) 2 (by omega) _ _ 0
    (prep_pcomp h32 (prep_pcomp h32 (prep_pidn (chainK_n24 hQ) hQ.2.1) t0) t1)
    (PF.pcomp_shr _ _ h32 hw), Nat.zero_add]

end Chain

end CFSG.KS.SporSch.MOC

end
