module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWCheck
public import Certificates.Kernel.Census.Pg.FactsBase
public import CFSG.Sporadic.Schreier.PairChain
public import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

theorem baseArr_facts : ∀ k < 6, baseArr[k]! < 128 ∧ baseArr[k]! ≠ 0 ∧ baseArr[k]! ≠ tC := by
  decide

theorem invC_unique_base :
    ∀ m < 6, ∀ u < 128, mulC baseArr[m]! u = 0 → u = invC baseArr[m]! := by
  decide +kernel

theorem comm_base_central : ∀ k < 6, ∀ j < k,
    commC baseArr[k]! baseArr[j]! = 0 ∨ commC baseArr[k]! baseArr[j]! = tC := by
  decide

theorem tC_ne_zero : tC ≠ 0 := by decide

theorem tC_lt : tC < 128 := by decide

section Table

theorem mulC_lt {a b : ℕ} (ha : a < 128) (hb : b < 128) : mulC a b < 128 := by
  have h := CertificateChecks.KernelPg.table_ok'
  simp only [tableCheck, Bool.and_eq_true] at h
  exact of_decide_eq_true
    (List.all_eq_true.1 (List.all_eq_true.1 h.1.1.1.1.1.1 a (List.mem_range.2 ha))
      b (List.mem_range.2 hb))

theorem mulC_row {a : ℕ} (ha : a < 128) :
    mulC 0 a = a ∧ mulC a 0 = a ∧ mulC a (invC a) = 0 ∧ mulC (invC a) a = 0 ∧
      invC a < 128 ∧ (mulC a a = 0 ∨ mulC a a = tC) := by
  have h := CertificateChecks.KernelPg.table_ok'
  simp only [tableCheck, Bool.and_eq_true] at h
  have h2 : (mulC 0 a == a && mulC a 0 == a && mulC a (invC a) == 0 &&
      mulC (invC a) a == 0 && decide (invC a < 128) &&
      (mulC a a == 0 || mulC a a == tC)) = true :=
    List.all_eq_true.1 h.1.1.1.1.1.2 a (List.mem_range.2 ha)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true] at h2
  exact ⟨h2.1.1.1.1.1, h2.1.1.1.1.2, h2.1.1.1.2, h2.1.1.2, h2.1.2, h2.2⟩

theorem mulC_zero_left {a : ℕ} (ha : a < 128) : mulC 0 a = a := (mulC_row ha).1

theorem invC_lt {a : ℕ} (ha : a < 128) : invC a < 128 := (mulC_row ha).2.2.2.2.1

theorem mulC_invC {a : ℕ} (ha : a < 128) : mulC a (invC a) = 0 := (mulC_row ha).2.2.1

theorem mulC_self_mem {a : ℕ} (ha : a < 128) : mulC a a = 0 ∨ mulC a a = tC :=
  (mulC_row ha).2.2.2.2.2

theorem center_of_comm {c : ℕ} (hc : c < 128) (h : ∀ d < 128, mulC c d = mulC d c) :
    c = 0 ∨ c = tC := by
  have h3 := CertificateChecks.KernelPg.table_ok'
  simp only [tableCheck, Bool.and_eq_true] at h3
  have hall : ((List.range 128).all fun d => mulC c d == mulC d c) = true :=
    List.all_eq_true.2 fun d hd => beq_iff_eq.2 (h d (List.mem_range.1 hd))
  have h4 : (!((List.range 128).all fun d => mulC c d == mulC d c) || c == 0 || c == tC) = true :=
    List.all_eq_true.1 h3.1.1.1.1.2 c (List.mem_range.2 hc)
  rw [hall] at h4
  simpa only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] using h4

theorem tC_comm {d : ℕ} (hd : d < 128) : mulC tC d = mulC d tC := by
  have h4 := CertificateChecks.KernelPg.table_ok'
  simp only [tableCheck, Bool.and_eq_true] at h4
  exact beq_iff_eq.1 (List.all_eq_true.1 h4.1.1.1.2 d (List.mem_range.2 hd))

theorem tC_sq : mulC tC tC = 0 := by
  have h4 := CertificateChecks.KernelPg.table_ok'
  simp only [tableCheck, Bool.and_eq_true] at h4
  exact beq_iff_eq.1 h4.1.1.2

theorem mulF_val (a b : Fin 128) : ((mulF a b : Fin 128) : ℕ) = mulC a b :=
  Nat.mod_eq_of_lt (mulC_lt a.2 b.2)

end Table

@[expose] def permVal (π : Equiv.Perm (Fin 128)) (a : ℕ) : ℕ :=
  if h : a < 128 then ((π ⟨a, h⟩ : Fin 128) : ℕ) else a

theorem permVal_eq (π : Equiv.Perm (Fin 128)) {a : ℕ} (ha : a < 128) :
    permVal π a = ((π ⟨a, ha⟩ : Fin 128) : ℕ) :=
  dite_eq_left ha

theorem permVal_lt (π : Equiv.Perm (Fin 128)) {a : ℕ} (ha : a < 128) : permVal π a < 128 := by
  rw [permVal_eq π ha]
  exact (π ⟨a, ha⟩).isLt

theorem permVal_inj (π : Equiv.Perm (Fin 128)) {a b : ℕ} (ha : a < 128) (hb : b < 128)
    (h : permVal π a = permVal π b) : a = b := by
  rw [permVal_eq π ha, permVal_eq π hb] at h
  exact congrArg Fin.val (π.injective (Fin.ext h))

theorem permVal_surj (π : Equiv.Perm (Fin 128)) {d : ℕ} (hd : d < 128) :
    ∃ e, ∃ _ : e < 128, permVal π e = d := by
  refine ⟨((π.symm ⟨d, hd⟩ : Fin 128) : ℕ), (π.symm ⟨d, hd⟩).isLt, ?_⟩
  rw [permVal_eq π (π.symm ⟨d, hd⟩).isLt]
  simp

section Aut

theorem sgsArr_size : sgsArr.size = 36 := by decide

theorem permVal_mul {π : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC) {a b : ℕ} (ha : a < 128)
    (hb : b < 128) : permVal π (mulC a b) = mulC (permVal π a) (permVal π b) := by
  have hab : mulC a b < 128 := mulC_lt ha hb
  have hm : (⟨mulC a b, hab⟩ : Fin 128) = mulF ⟨a, ha⟩ ⟨b, hb⟩ :=
    Fin.ext ((mulF_val ⟨a, ha⟩ ⟨b, hb⟩).symm)
  have hπ' : ∀ x y : Fin 128, π (mulF x y) = mulF (π x) (π y) := hπ
  rw [permVal_eq π hab, hm, hπ' ⟨a, ha⟩ ⟨b, hb⟩, mulF_val, permVal_eq π ha, permVal_eq π hb]

theorem permVal_zero {π : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC) : permVal π 0 = 0 := by
  have h0le : (0 : ℕ) < 128 := by norm_num
  have hx := permVal_lt π h0le
  have h0 : permVal π 0 = mulC (permVal π 0) (permVal π 0) := by
    have h := permVal_mul hπ h0le h0le
    rwa [mulC_zero_left h0le] at h
  rcases mulC_self_mem hx with h1 | h1
  · exact h0.trans h1
  · exfalso
    have hx' : permVal π 0 = tC := h0.trans h1
    rw [hx', tC_sq] at h1
    exact tC_ne_zero h1.symm

theorem permVal_tC {π : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC) : permVal π tC = tC := by
  have hcen : ∀ d < 128, mulC (permVal π tC) d = mulC d (permVal π tC) := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := permVal_surj π hd
    have h1 := permVal_mul hπ tC_lt he
    have h2 := permVal_mul hπ he tC_lt
    rw [← h1, ← h2, tC_comm he]
  rcases center_of_comm (permVal_lt π tC_lt) hcen with h | h
  · exact absurd (permVal_inj π tC_lt (by norm_num) (h.trans (permVal_zero hπ).symm)) tC_ne_zero
  · exact h

theorem permVal_fix {π : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC) {x : ℕ}
    (h : x = 0 ∨ x = tC) : permVal π x = x := by
  rcases h with rfl | rfl
  · exact permVal_zero hπ
  · exact permVal_tC hπ

theorem sgs_mul {i : ℕ} (hi : i < sgsArr.size) :
    ∀ a < 128, ∀ b < 128, (sgsArr[i]!)[mulC a b]! = mulC (sgsArr[i]!)[a]! (sgsArr[i]!)[b]! := by
  have h := CertificateChecks.KernelPg.aut_ok'
  simp only [autCheck, Array.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  rw [getElem!_pos sgsArr i hi]
  exact (h i hi).1.2

theorem permOfArr_mem_autC {i : ℕ} (hi : i < sgsArr.size) :
    permOfArr 128 sgsArr[i]! ∈ AutC := by
  have hinv := (chainCheckFacts CertificateChecks.KernelPg.chain_zero).strong_inv i hi
  have hrep : ∀ x : Fin 128, (sgsArr[i]!)[(x : ℕ)]! = permOfArr 128 sgsArr[i]! x :=
    (rep_permOfArr hinv).1
  have hmul := sgs_mul hi
  intro a b
  apply Fin.ext
  simp only [mulF_val, ← hrep]
  exact hmul a a.2 b b.2

theorem genCheck_facts : genElems[0]! = 0 ∧ (∀ j < 128, genElems[j]! < 128) ∧
    (∀ c < 128, ∃ j < 128, genElems[j]! = c) ∧
    (∀ j' < 127, genPar[j' + 1]! < j' + 1 ∧ genGen[j' + 1]! < 6 ∧
      mulC genElems[genPar[j' + 1]!]! baseArr[genGen[j' + 1]!]! = genElems[j' + 1]!) := by
  have h := CertificateChecks.KernelPg.gen_ok'
  simp only [genCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩ := h
  refine ⟨h5, fun j hj => ?_, fun c hc => ?_, fun j' hj' => ?_⟩
  · have := List.all_eq_true.1 h6 j (List.mem_range.2 hj)
    exact of_decide_eq_true this
  · obtain ⟨j, hj, hjc⟩ := List.any_eq_true.1 (List.all_eq_true.1 h7 c (List.mem_range.2 hc))
    exact ⟨j, List.mem_range.1 hj, beq_iff_eq.1 hjc⟩
  · have := List.all_eq_true.1 h8 j' (List.mem_range.2 hj')
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

theorem genElems_fix {π : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC)
    (hbase : ∀ g < 6, permVal π baseArr[g]! = baseArr[g]!) :
    ∀ j < 128, permVal π genElems[j]! = genElems[j]! := by
  obtain ⟨h0, hlt, -, hstep⟩ := genCheck_facts
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases j with _ | j'
    · rw [h0]
      exact permVal_zero hπ
    · obtain ⟨hp, hg, heq⟩ := hstep j' (by omega)
      rw [← heq, permVal_mul hπ (hlt _ (by omega)) (baseArr_facts _ hg).1, ih _ hp (by omega),
        hbase _ hg]

theorem fixed_all {π : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC)
    (hfix : ∀ j < 6, ∀ x : Fin 128, (x : ℕ) = baseArr[j]! → π x = x) : π = 1 := by
  have hbase : ∀ g < 6, permVal π baseArr[g]! = baseArr[g]! := by
    intro g hg
    rw [permVal_eq π (baseArr_facts g hg).1, hfix g hg ⟨baseArr[g]!, (baseArr_facts g hg).1⟩ rfl]
  have hall : ∀ x : Fin 128, π x = x := by
    intro x
    obtain ⟨j, hj, hjx⟩ := genCheck_facts.2.2.1 x.val x.isLt
    have h1 := genElems_fix hπ hbase j hj
    rw [hjx, permVal_eq π x.isLt] at h1
    exact Fin.ext h1
  exact Equiv.ext fun x => by rw [Equiv.Perm.one_apply]; exact hall x

theorem permVal_comm {π : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC) {c d : ℕ} (hc : c < 128)
    (hd : d < 128) (hdfix : permVal π d = d) (hrowc : ∀ u < 128, mulC c u = 0 → u = invC c)
    (hrowd : ∀ u < 128, mulC d u = 0 → u = invC d) (hcd : commC c d = 0 ∨ commC c d = tC) :
    commC (permVal π c) d = commC c d := by
  have hinvc : invC (permVal π c) = permVal π (invC c) := by
    obtain ⟨y, hy, hyv⟩ := permVal_surj π (invC_lt (permVal_lt π hc))
    have h1 : permVal π (mulC c y) = permVal π 0 := by
      rw [permVal_mul hπ hc hy, hyv, mulC_invC (permVal_lt π hc), permVal_zero hπ]
    have h2 : mulC c y = 0 := permVal_inj π (mulC_lt hc hy) (by norm_num) h1
    rw [← hyv, hrowc y hy h2]
  have hinvd : permVal π (invC d) = invC d := by
    have h1 : mulC d (permVal π (invC d)) = 0 := by
      have h := permVal_mul hπ hd (invC_lt hd)
      rw [mulC_invC hd, permVal_zero hπ, hdfix] at h
      exact h.symm
    exact hrowd _ (permVal_lt π (invC_lt hd)) h1
  have hX : mulC (permVal π c) d = permVal π (mulC c d) := by
    rw [permVal_mul hπ hc hd, hdfix]
  have hY : mulC (invC (permVal π c)) (invC d) = permVal π (mulC (invC c) (invC d)) := by
    rw [hinvc, permVal_mul hπ (invC_lt hc) (invC_lt hd), hinvd]
  have hcd' : mulC (mulC c d) (mulC (invC c) (invC d)) = 0 ∨
      mulC (mulC c d) (mulC (invC c) (invC d)) = tC := hcd
  unfold commC
  rw [hX, hY, ← permVal_mul hπ (mulC_lt hc hd) (mulC_lt (invC_lt hc) (invC_lt hd))]
  exact permVal_fix hπ (by
    rcases hcd' with h | h
    · exact Or.inl h
    · exact Or.inr h)

theorem cand_mem {π : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC) {k : ℕ} (hk : k < 6)
    (hfix : ∀ j < k, permVal π baseArr[j]! = baseArr[j]!) :
    permVal π baseArr[k]! ∈ candSet k := by
  obtain ⟨hlt, hne0, hneT⟩ := baseArr_facts k hk
  unfold candSet
  rw [List.mem_filter]
  refine ⟨List.mem_range.2 (permVal_lt π hlt), ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact fun h => hne0 (permVal_inj π hlt (by norm_num) (h.trans (permVal_zero hπ).symm))
  · exact fun h => hneT (permVal_inj π hlt tC_lt (h.trans (permVal_tC hπ).symm))
  · have h := permVal_mul hπ hlt hlt
    have h' := permVal_fix hπ (mulC_self_mem hlt)
    exact h.symm.trans (h' : _)
  · intro j hj
    exact permVal_comm hπ hlt (baseArr_facts j (by omega)).1 (hfix j hj)
      (fun u hu h => invC_unique_base k hk u hu h)
      (fun u hu h => invC_unique_base j (by omega) u hu h) (comm_base_central k hk j hj)

end Aut

theorem card_le_prod_cands {X : Type*} (n : ℕ) :
    ∀ (K : Type) [Group K] [Finite K] [MulAction K X] (b : ℕ → X) (cand : ℕ → Finset X),
      (∀ m < n, ∀ g : K, (∀ j < m, g • b j = b j) → g • b m ∈ cand m) →
      (∀ g : K, (∀ j < n, g • b j = b j) → g = 1) →
      Nat.card K ≤ ∏ m ∈ Finset.range n, (cand m).card := by
  induction n with
  | zero =>
    intro K _ _ _ b cand _ h1
    rw [Finset.prod_range_zero]
    have hsub : Subsingleton K := ⟨fun x y => by
      rw [h1 x fun j hj => absurd hj (Nat.not_lt_zero j),
        h1 y fun j hj => absurd hj (Nat.not_lt_zero j)]⟩
    exact Finite.card_le_one_iff_subsingleton.2 hsub
  | succ n ih =>
    intro K _ _ _ b cand h0 h1
    have hcard : Nat.card K = Nat.card (MulAction.orbit K (b 0)) *
        Nat.card (MulAction.stabilizer K (b 0)) := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K (b 0))).symm
    have horb : Nat.card (MulAction.orbit K (b 0)) ≤ (cand 0).card := by
      have hsub : MulAction.orbit K (b 0) ⊆ ((cand 0 : Finset X) : Set X) := by
        rintro _ ⟨g, rfl⟩
        exact h0 0 (Nat.succ_pos n) g fun j hj => absurd hj (Nat.not_lt_zero j)
      calc Nat.card (MulAction.orbit K (b 0)) ≤ Nat.card ((cand 0 : Finset X) : Set X) :=
            Nat.card_mono (Finset.finite_toSet _) hsub
        _ = (cand 0).card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hA : ∀ m < n, ∀ g : ↥(MulAction.stabilizer K (b 0)),
        (∀ j < m, g • b (j + 1) = b (j + 1)) → g • b (m + 1) ∈ cand (m + 1) := by
      intro m hm g hg
      refine h0 (m + 1) (by omega) (g : K) fun j hj => ?_
      cases j with
      | zero => exact MulAction.mem_stabilizer_iff.1 g.2
      | succ i => exact hg i (by omega)
    have hB : ∀ g : ↥(MulAction.stabilizer K (b 0)),
        (∀ j < n, g • b (j + 1) = b (j + 1)) → g = 1 := by
      intro g hg
      apply Subtype.ext
      refine h1 (g : K) fun j hj => ?_
      cases j with
      | zero => exact MulAction.mem_stabilizer_iff.1 g.2
      | succ i => exact hg i (by omega)
    have hH := ih (MulAction.stabilizer K (b 0)) (fun i => b (i + 1))
      (fun i => cand (i + 1)) hA hB
    rw [hcard, Finset.prod_range_succ']
    calc Nat.card (MulAction.orbit K (b 0)) * Nat.card (MulAction.stabilizer K (b 0))
        ≤ (cand 0).card * ∏ m ∈ Finset.range n, (cand (m + 1)).card :=
          Nat.mul_le_mul horb hH
      _ = (∏ m ∈ Finset.range n, (cand (m + 1)).card) * (cand 0).card := mul_comm _ _

@[expose] def bF (j : ℕ) : Fin 128 := ⟨baseArr[j]! % 128, Nat.mod_lt _ (by norm_num)⟩

theorem bF_eq {j : ℕ} (hj : j < 6) : bF j = ⟨baseArr[j]!, (baseArr_facts j hj).1⟩ :=
  Fin.ext (Nat.mod_eq_of_lt (baseArr_facts j hj).1)

theorem bF_val {j : ℕ} (hj : j < 6) : ((bF j : Fin 128) : ℕ) = baseArr[j]! :=
  Nat.mod_eq_of_lt (baseArr_facts j hj).1

@[expose] def candF (k : ℕ) : Finset (Fin 128) :=
  Finset.univ.filter fun x : Fin 128 => (x : ℕ) ∈ candSet k

theorem card_candF (k : ℕ) : (candF k).card = (candSet k).length := by
  have hnd : (candSet k).Nodup := by
    unfold candSet
    exact (List.nodup_range).filter _
  have hmap : (candF k).map Fin.valEmbedding = (candSet k).toFinset := by
    ext y
    simp only [candF, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, List.mem_toFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      have hy128 : y < 128 := List.mem_range.1 (List.mem_of_mem_filter hy)
      exact ⟨⟨y, hy128⟩, hy, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, List.toFinset_card_of_nodup hnd]

theorem permVal_bF (π : Equiv.Perm (Fin 128)) {j : ℕ} (hj : j < 6) :
    permVal π baseArr[j]! = ((π (bF j) : Fin 128) : ℕ) := by
  rw [permVal_eq π (baseArr_facts j hj).1, bF_eq hj]

theorem finsetProd_range_eq_listProd (n : ℕ) (f : ℕ → ℕ) :
    ∏ m ∈ Finset.range n, f m = ((List.range n).map f).prod := by
  rw [Finset.prod_eq_multiset_prod, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.prod_coe]

theorem candSet_eq_candSetG : candSet = CFSG.KC.W16Pg.candSetG mulC := rfl

theorem candG_prod (mul : ℕ → ℕ → ℕ) (h : CFSG.KC.W16Pg.candG mul = true) :
    ((List.range 6).map fun k => (CFSG.KC.W16Pg.candSetG mul k).length).prod = 3317760 := by
  unfold CFSG.KC.W16Pg.candG at h
  simpa only [beq_iff_eq] using h

theorem candSet_prod :
    ∏ m ∈ Finset.range 6, (candSet m).length = 3317760 := by
  rw [candSet_eq_candSetG, CFSG.KC.W16Pg.mulC_eq CertificateChecks.KernelPg.bindE,
    finsetProd_range_eq_listProd]
  exact candG_prod _ CertificateChecks.KernelPg.cand_ok

theorem card_autC_le : Nat.card AutC ≤ 3317760 := by
  have hstep : ∀ m < 6, ∀ g : ↥AutC, (∀ j < m, g • bF j = bF j) → g • bF m ∈ candF m := by
    intro m hm g hg
    have hfix : ∀ j < m, permVal (g : Equiv.Perm (Fin 128)) baseArr[j]! = baseArr[j]! := by
      intro j hj
      have h1 : (g : Equiv.Perm (Fin 128)) (bF j) = bF j := hg j hj
      rw [permVal_bF _ (by omega : j < 6), h1, bF_val (by omega : j < 6)]
    have hmem := cand_mem g.2 hm hfix
    rw [permVal_bF _ hm] at hmem
    rw [candF, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmem⟩
  have hfinal : ∀ g : ↥AutC, (∀ j < 6, g • bF j = bF j) → g = 1 := by
    intro g hg
    apply Subtype.ext
    show (g : Equiv.Perm (Fin 128)) = 1
    apply fixed_all g.2
    intro j hj x hx
    have hxb : x = bF j := Fin.ext (hx.trans (bF_val hj).symm)
    rw [hxb]
    exact hg j hj
  have hbound := card_le_prod_cands (X := Fin 128) 6 (↥AutC) bF candF hstep hfinal
  have hprod : ∏ m ∈ Finset.range 6, (candF m).card = 3317760 := by
    rw [Finset.prod_congr rfl fun m _ => card_candF m]
    exact candSet_prod
  rw [hprod] at hbound
  exact hbound

end CFSG.EvenSporadicStandard.Fin76b.W16
