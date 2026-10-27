module

public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.PairClassCover
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Certificate2219
public import Certificates.Certificate2220
public import Certificates.Certificate4081
public import Certificates.Certificate2218

public noncomputable section

namespace CFSG.QuasithinUnique.Id2519.UHS

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

abbrev PP : Subgroup (Equiv.Perm (Fin 3850)) := hsChain.originalSubgroup

@[expose] def hsC : Equiv.Perm (Fin 3850) := (hsGen 0 * hsGen 1 * hsGen 1) ^ 5

theorem hsC_mem : hsC ∈ PP :=
  pow_mem (mul_mem (mul_mem (hsGen_mem 0 (by norm_num)) (hsGen_mem 1 (by norm_num)))
    (hsGen_mem 1 (by norm_num))) 5

theorem repW_hswC : RepW 3850 PairHS.wC hsC := by
  have hp := repW_patW repW_hswA repW_hswB [false, true, true]
  have e : ([false, true, true].map fun b => if b then hsGen 1 else hsGen 0).prod =
      hsGen 0 * hsGen 1 * hsGen 1 := by
    simp [mul_assoc]
  rw [e] at hp
  have h5 := RepW.flatten (List.Forall₂.cons hp (List.Forall₂.cons hp (List.Forall₂.cons hp
    (List.Forall₂.cons hp (List.Forall₂.cons hp List.Forall₂.nil)))))
  have e5 : [hsGen 0 * hsGen 1 * hsGen 1, hsGen 0 * hsGen 1 * hsGen 1,
      hsGen 0 * hsGen 1 * hsGen 1, hsGen 0 * hsGen 1 * hsGen 1,
      hsGen 0 * hsGen 1 * hsGen 1].reverse.prod = hsC := by
    simp only [hsC, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.prod_cons, List.prod_nil, mul_one, pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e5] at h5
  exact h5

theorem orderOf_hsGen_zero : orderOf (hsGen 0) = 2 := hs_word_orders.1

theorem cl_eq : PairHS.cl = [(PairHS.wA, PairHS.closureOf PairHS.wA),
    (PairHS.wC, PairHS.closureOf PairHS.wC)] :=
  rfl

theorem orderOf_hsC : orderOf hsC = 2 := by
  have h := PairHS.classes.1
  rw [cl_eq] at h
  exact (ordB_iff hs_baseFaithful hs_bs_lt repW_hswC hsC_mem (by norm_num)).1
    (h (PairHS.wC, PairHS.closureOf PairHS.wC) (List.mem_cons_of_mem _ List.mem_cons_self))

@[expose] def hsInvols : List (Equiv.Perm (Fin 3850)) :=
  (enumeration hsChain).filter fun h => decide (orderOf h = 2)

theorem mem_hsInvols {x : Equiv.Perm (Fin 3850)} : x ∈ hsInvols ↔ x ∈ PP ∧ orderOf x = 2 := by
  rw [hsInvols, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff hsChain hsChain_valid.1]

theorem hsInvols_nodup : hsInvols.Nodup :=
  (enumeration_nodup hsChain hsChain_valid.1).filter _

theorem hs_card_order' (m : ℕ) (hm : 0 < m) :
    Nat.card {x : PP // orderOf (x : Equiv.Perm (Fin 3850)) = m} =
      PairHS.parCount (ordPred PairHS.bs m) PairHS.blocks := by
  rw [← hs_card_order m hm, ← card_orderOf_coe]

theorem hsInvols_length : hsInvols.length = 21175 := by
  have h1 := card_subtype_eq_countP PP (enumeration hsChain)
    (enumeration_nodup hsChain hsChain_valid.1) (mem_enumeration_iff hsChain hsChain_valid.1)
    (fun y => orderOf y = 2)
  rw [List.countP_eq_length_filter] at h1
  have h2 := hs_card_order' 2 (by norm_num)
  rw [PairHS.count_two] at h2
  rw [hsInvols, ← h1]
  exact h2

theorem cl_sizes : (PairHS.closureOf PairHS.wA).1.size = 5775 ∧
    (PairHS.closureOf PairHS.wC).1.size = 15400 := by
  have h : PairHS.cl.map (fun c => c.2.1.size) = [5775, 15400] :=
    Certificates.certificate4081
  rw [cl_eq] at h
  simpa only [List.map_cons, List.map_nil, List.cons.injEq, and_true] using h

@[expose] def hsE1 : List (Equiv.Perm (Fin 3850)) :=
  (PairHS.closureOf PairHS.wA).1.toList.map (nfElt 3850 hsStrongArrs PairHS.baseArr)

@[expose] def hsE2 : List (Equiv.Perm (Fin 3850)) :=
  (PairHS.closureOf PairHS.wC).1.toList.map (nfElt 3850 hsStrongArrs PairHS.baseArr)

theorem hsE1_length : hsE1.length = 5775 := by
  rw [hsE1, List.length_map, Array.length_toList, cl_sizes.1]

theorem hsE2_length : hsE2.length = 15400 := by
  rw [hsE2, List.length_map, Array.length_toList, cl_sizes.2]

theorem hs_entries_perm : (hsE1 ++ hsE2).Perm hsInvols := by
  obtain ⟨-, hok, hkeys, hsize⟩ := PairHS.classes
  have hclosed : ∀ c ∈ PP, ∀ x ∈ hsInvols, c * x * c⁻¹ ∈ hsInvols := by
    intro c hc x hx
    obtain ⟨hxP, hxo⟩ := mem_hsInvols.1 hx
    rw [mem_hsInvols]
    exact ⟨mul_mem (mul_mem hc hxP) (inv_mem hc),
      (MulEquiv.orderOf_eq (MulAut.conj c) x).trans hxo⟩
  have h1 : ∀ c ∈ PairHS.cl, ∃ x ∈ hsInvols, RepW 3850 c.1 x ∧ x ∈ PP := by
    intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨hsGen 0, mem_hsInvols.2 ⟨hsGen_mem 0 (by norm_num), orderOf_hsGen_zero⟩, repW_hswA,
        hsGen_mem 0 (by norm_num)⟩
    · exact ⟨hsC, mem_hsInvols.2 ⟨hsC_mem, orderOf_hsC⟩, repW_hswC, hsC_mem⟩
  have h4 : (PairHS.cl.map fun c => c.2.1.size).sum = hsInvols.length := by
    rw [hsize, hsInvols_length]
  have h := closureEntries_perm hsChainArrays (chainCheckFacts PairHS.chain_check.1)
    hsChain_valid.1 hs_baseFaithful hs_bs_lt hs_gens hsInvols hclosed PairHS.cl h1 hok hkeys h4
  rw [cl_eq] at h
  simpa only [hsE1, hsE2, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_append] using h

theorem hsE_nodup : (hsE1 ++ hsE2).Nodup :=
  hs_entries_perm.nodup_iff.2 hsInvols_nodup

theorem hs_closure_conj {w : List (Array ℕ)} {x₀ : Equiv.Perm (Fin 3850)}
    (hw : RepW 3850 w x₀) (hx₀ : x₀ ∈ PP)
    (h : closureOK PairHS.levels PairHS.bs PairHS.gens PairHS.gensInv w (PairHS.closureOf w).1
      (PairHS.closureOf w).2.1 (PairHS.closureOf w).2.2 = true) :
    ∀ e ∈ (PairHS.closureOf w).1.toList.map (nfElt 3850 hsStrongArrs PairHS.baseArr),
      ∃ d ∈ PP, e = d * x₀ * d⁻¹ := by
  intro e he
  obtain ⟨nf, hnf, rfl⟩ := List.mem_map.1 he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hnf
  rw [Array.length_toList] at hk
  have := closureOK_spec hsChainArrays (chainCheckFacts PairHS.chain_check.1) hsChain_valid.1
    hs_baseFaithful hs_bs_lt hs_gens hw hx₀ h k hk
  rw [getElem!_pos _ k hk] at this
  obtain ⟨-, d, hd, hde⟩ := this
  exact ⟨d, hd, by simpa [Array.getElem_toList] using hde⟩

theorem hsE1_conj : ∀ e ∈ hsE1, ∃ d ∈ PP, e = d * hsGen 0 * d⁻¹ := by
  have h := PairHS.classes.2.1
  rw [cl_eq] at h
  exact hs_closure_conj repW_hswA (hsGen_mem 0 (by norm_num))
    (h (PairHS.wA, PairHS.closureOf PairHS.wA) List.mem_cons_self)

theorem hsE2_conj : ∀ e ∈ hsE2, ∃ d ∈ PP, e = d * hsC * d⁻¹ := by
  have h := PairHS.classes.2.1
  rw [cl_eq] at h
  exact hs_closure_conj repW_hswC hsC_mem
    (h (PairHS.wC, PairHS.closureOf PairHS.wC) (List.mem_cons_of_mem _ List.mem_cons_self))

theorem hs_invol_cover {x : Equiv.Perm (Fin 3850)} (hx : x ∈ PP) (hxo : orderOf x = 2) :
    x ∈ hsE1 ∨ x ∈ hsE2 :=
  List.mem_append.1 (hs_entries_perm.mem_iff.2 (mem_hsInvols.2 ⟨hx, hxo⟩))

theorem orderOf_conj_perm {c x : Equiv.Perm (Fin 3850)} : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem hsC_not_conj {d : Equiv.Perm (Fin 3850)} (hd : d ∈ PP) : hsC ≠ d * hsGen 0 * d⁻¹ := by
  intro hdc
  set a : PP := ⟨hsGen 0, hsGen_mem 0 (by norm_num)⟩ with ha
  have hcls : conjugatesOf a = {x : PP | orderOf x = 2} := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp (show IsConj a x from hx)
      have h2 : orderOf x = 2 := by
        rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
        exact orderOf_hsGen_zero
      exact h2
    · intro hx
      have hxo : orderOf (x : Equiv.Perm (Fin 3850)) = 2 := by
        rw [Subgroup.orderOf_coe]; exact hx
      show IsConj a x
      rw [isConj_iff]
      rcases hs_invol_cover x.2 hxo with h | h
      · obtain ⟨c, hc, hce⟩ := hsE1_conj _ h
        refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ha]
        exact hce.symm
      · obtain ⟨c, hc, hce⟩ := hsE2_conj _ h
        refine ⟨⟨c * d, mul_mem hc hd⟩, Subtype.ext ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ha]
        rw [hce, hdc]
        group
  have hidx := Subgroup.index_centralizer_eq_ncard a
  have hncard : (conjugatesOf a).ncard = 21175 := by
    rw [hcls, ← Nat.card_coe_set_eq]
    have h1 := hs_card_order 2 (by norm_num)
    rw [PairHS.count_two] at h1
    exact h1
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({a} : Set PP))
  rw [hidx, hncard] at hmul
  have hP : Nat.card PP = 44352000 := by
    have := card_hsP
    rw [hsP_eq_original] at this
    exact this
  rw [hP] at hmul
  omega

theorem hs_conj_a0_iff {x : Equiv.Perm (Fin 3850)} (hx : x ∈ PP) :
    (∃ d ∈ PP, x = d * hsGen 0 * d⁻¹) ↔ x ∈ hsE1 := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases hs_invol_cover hx (by rw [orderOf_conj_perm, orderOf_hsGen_zero]) with h | h
    · exact h
    · obtain ⟨d', hd', he⟩ := hsE2_conj _ h
      exfalso
      refine hsC_not_conj (mul_mem (inv_mem hd') hd) ?_
      have : hsC = d'⁻¹ * (d * hsGen 0 * d⁻¹) * d' := by rw [he]; group
      rw [this]
      group
  · exact hsE1_conj x

theorem hs_conj_c_iff {x : Equiv.Perm (Fin 3850)} (hx : x ∈ PP) :
    (∃ d ∈ PP, x = d * hsC * d⁻¹) ↔ x ∈ hsE2 := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases hs_invol_cover hx (by rw [orderOf_conj_perm, orderOf_hsC]) with h | h
    · obtain ⟨d', hd', he⟩ := hsE1_conj _ h
      exfalso
      refine hsC_not_conj (mul_mem (inv_mem hd) hd') ?_
      have : hsC = d⁻¹ * (d' * hsGen 0 * d'⁻¹) * d := by rw [← he]; group
      rw [this]
      group
    · exact h
  · exact hsE2_conj x

theorem hsE1_mem : ∀ e ∈ hsE1, e ∈ PP := fun e he => by
  obtain ⟨d, hd, rfl⟩ := hsE1_conj e he
  exact mul_mem (mul_mem hd (hsGen_mem 0 (by norm_num))) (inv_mem hd)

theorem hsE2_mem : ∀ e ∈ hsE2, e ∈ PP := fun e he => by
  obtain ⟨d, hd, rfl⟩ := hsE2_conj e he
  exact mul_mem (mul_mem hd hsC_mem) (inv_mem hd)

theorem ncard_list_pre (L : List (Equiv.Perm (Fin 3850))) (hL : L.Nodup) (hsub : ∀ e ∈ L, e ∈ PP) :
    ({x : PP | (x : Equiv.Perm (Fin 3850)) ∈ L} : Set PP).ncard = L.length := by
  have h1 : ({x : PP | (x : Equiv.Perm (Fin 3850)) ∈ L} : Set PP) =
      (Subtype.val : PP → Equiv.Perm (Fin 3850)) ⁻¹' (L.toFinset : Set (Equiv.Perm (Fin 3850))) := by
    ext x
    simp
  rw [h1, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hL]
  intro y hy
  exact ⟨⟨y, hsub y (by simpa using hy)⟩, rfl⟩

theorem card_PP : Nat.card PP = 44352000 := by
  have := card_hsP
  rwa [hsP_eq_original] at this

theorem card_centralizer_a0 :
    Nat.card (Subgroup.centralizer ({(⟨hsGen 0, hsGen_mem 0 (by norm_num)⟩ : PP)} : Set PP)) =
      7680 := by
  set a : PP := ⟨hsGen 0, hsGen_mem 0 (by norm_num)⟩ with ha
  have hcls : conjugatesOf a = {x : PP | (x : Equiv.Perm (Fin 3850)) ∈ hsE1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp (show IsConj a x from hx)
      exact (hs_conj_a0_iff x.2).1 ⟨c, c.2, by rw [← hc]; simp [ha]⟩
    · intro hx
      obtain ⟨d, hd, hdx⟩ := (hs_conj_a0_iff x.2).2 hx
      show IsConj a x
      rw [isConj_iff]
      exact ⟨⟨d, hd⟩, Subtype.ext (by simp [ha, hdx])⟩
  have hnd : hsE1.Nodup := (List.nodup_append.1 hsE_nodup).1
  have hidx := Subgroup.index_centralizer_eq_ncard a
  rw [hcls, ncard_list_pre hsE1 hnd hsE1_mem, hsE1_length] at hidx
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({a} : Set PP))
  rw [hidx, card_PP] at hmul
  omega

theorem card_centralizer_c :
    Nat.card (Subgroup.centralizer ({(⟨hsC, hsC_mem⟩ : PP)} : Set PP)) = 2880 := by
  set a : PP := ⟨hsC, hsC_mem⟩ with ha
  have hcls : conjugatesOf a = {x : PP | (x : Equiv.Perm (Fin 3850)) ∈ hsE2} := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp (show IsConj a x from hx)
      exact (hs_conj_c_iff x.2).1 ⟨c, c.2, by rw [← hc]; simp [ha]⟩
    · intro hx
      obtain ⟨d, hd, hdx⟩ := (hs_conj_c_iff x.2).2 hx
      show IsConj a x
      rw [isConj_iff]
      exact ⟨⟨d, hd⟩, Subtype.ext (by simp [ha, hdx])⟩
  have hnd : hsE2.Nodup := (List.nodup_append.1 hsE_nodup).2.1
  have hidx := Subgroup.index_centralizer_eq_ncard a
  rw [hcls, ncard_list_pre hsE2 hnd hsE2_mem, hsE2_length] at hidx
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({a} : Set PP))
  rw [hidx, card_PP] at hmul
  omega

end CFSG.QuasithinUnique.Id2519.UHS
