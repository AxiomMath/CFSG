module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineJTwoSylow
public import Certificates.Certificate3966
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup Equiv
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

section Tables

variable {n : ℕ}

theorem card_support_eq_movedCount {T : Table} {g : Perm (Fin n)} (hT : Rep n T g) :
    g.support.card = movedCount n T := by
  classical
  have h1 : g.support.card = ∑ i : Fin n, if ap T i.val ≠ i.val then 1 else 0 := by
    rw [Equiv.Perm.support, Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hT i.val i.isLt
    rw [idx_of_lt _ i.isLt] at this
    simp only [Equiv.Perm.smul_def, Fin.eta] at this
    simp only [this, ne_eq, Fin.val_inj]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => if ap T i ≠ i then 1 else 0), ← Finset.card_filter,
    movedCount, List.countP_eq_length_filter]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  congr 1

theorem invoOK_of_mul_self {T : Table} {g : Perm (Fin n)} (hT : Rep n T g) (h : g * g = 1) :
    invoOK n T = true := by
  rw [invoOK, allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hT i hi, hT _ (idx_lt g hi), ← idx_mul, h, idx_one]

end Tables

section Exponent

variable {G : Type*} [Group G]

theorem mul_comm_of_exp_two {W : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1) {v w : G} (hv : v ∈ W)
    (hw : w ∈ W) : v * w = w * v := by
  have h1 : v * w * (v * w) = 1 := hW2 _ (W.mul_mem hv hw)
  have h2 : v * w * (w * v) = 1 := by
    rw [mul_assoc, ← mul_assoc w w v, hW2 w hw, one_mul, hW2 v hv]
  calc v * w = v * w * (v * w * (w * v)) := by rw [h2, mul_one]
    _ = v * w * (v * w) * (w * v) := (mul_assoc (v * w) (v * w) (w * v)).symm
    _ = w * v := by rw [h1, one_mul]

theorem card_le_length_of_forall (W : Subgroup G) {α : Type*} (L : List α) (f : α → G)
    (h : ∀ v ∈ W, ∃ y ∈ L, v = f y) : Nat.card W ≤ L.length := by
  classical
  have hsub : (W : Set G) ⊆ ((L.map f).toFinset : Set G) := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := h v hv
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨y, hy, rfl⟩
  calc Nat.card W = (W : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ((L.map f).toFinset : Set G).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (L.map f).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (L.map f).length := List.toFinset_card_le _
    _ = L.length := List.length_map _

theorem forall_mem_of_card_le {W : Subgroup G} [Finite W] {α : Type*} {L : List α} (f : α → G)
    (hL : L.length ≤ Nat.card W) (h : ∀ v ∈ W, ∃ y ∈ L, v = f y) : ∀ y ∈ L, f y ∈ W := by
  classical
  have hsub : (W : Set G) ⊆ ((L.map f).toFinset : Set G) := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := h v hv
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨y, hy, rfl⟩
  have hle : ((L.map f).toFinset : Set G).ncard ≤ (W : Set G).ncard := by
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    calc (L.map f).toFinset.card ≤ (L.map f).length := List.toFinset_card_le _
      _ = L.length := List.length_map _
      _ ≤ Nat.card W := hL
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Finset.finite_toSet _)
  intro y hy
  have hmem : f y ∈ ((L.map f).toFinset : Set G) := by
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨y, hy, rfl⟩
  rw [← heq] at hmem
  exact hmem

theorem forall_or_forall_of_union {W : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1) {A B : G → Prop}
    (hA : ∀ a b, A a → A b → A (a * b)) (hB : ∀ a b, B a → B b → B (a * b))
    (h : ∀ w ∈ W, A w ∨ B w) : (∀ w ∈ W, A w) ∨ (∀ w ∈ W, B w) := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨a, ha, hAa⟩, ⟨b, hb, hBb⟩⟩ := hne
  have hBa : B a := (h a ha).resolve_left hAa
  have hAb : A b := (h b hb).resolve_right hBb
  rcases h (a * b) (W.mul_mem ha hb) with hab | hab
  · apply hAa
    have := hA _ _ hab hAb
    rwa [mul_assoc, hW2 b hb, mul_one] at this
  · apply hBb
    have := hB _ _ hBa hab
    rwa [← mul_assoc, hW2 a ha, one_mul] at this

end Exponent

structure TableEnum (n : ℕ) (S P : Subgroup (Perm (Fin n))) (sift : Table → Bool)
    (E : Array Table) : Prop where
  lt : n < 2 ^ 32
  rep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!)
  cov : ∀ x ∈ S, ∃ k < E.size, Rep n E[k]! x
  sift : ∀ (T : Table) (g : Perm (Fin n)), Rep n T g → (sift T = true ↔ g ∈ P)

section Enum

variable {n : ℕ} {S P : Subgroup (Perm (Fin n))} {sift : Table → Bool} {E : Array Table}

theorem mul_mem_of_idxClosedOK (hD : TableEnum n S P sift E) {I : List ℕ}
    (h : idxClosedOK n E I = true) :
    (∀ y ∈ I, y < E.size) ∧ ∀ y ∈ I, ∀ z ∈ I, ∃ t ∈ I,
      tablePerm n E[y]! * tablePerm n E[z]! = tablePerm n E[t]! := by
  simp only [idxClosedOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨hlt, hcl⟩ := h
  refine ⟨hlt, fun y hy z hz => ?_⟩
  obtain ⟨t, ht, he⟩ := hcl y hy z hz
  exact ⟨t, ht, (tblEq_iff_eq (Rep.compT (hD.rep y (hlt y hy)) (hD.rep z (hlt z hz)))
    (hD.rep t (hlt t ht))).1 he⟩

theorem mem_union_of_eaCountOK (hD : TableEnum n S P sift E) {I₁ I₂ : List ℕ}
    (hcount : eaCountOK n sift E I₁ I₂ = true) {W : Subgroup (Perm (Fin n))} (hWS : W ≤ S)
    (hWP : W ≤ P) (hW16 : Nat.card W = 16) (hW2 : ∀ w ∈ W, w * w = 1) :
    ∀ w ∈ W, ∃ y, (y ∈ I₁ ∨ y ∈ I₂) ∧ w = tablePerm n E[y]! := by
  intro w hw
  obtain ⟨i, hi, hiw⟩ := hD.cov w (hWS hw)
  by_cases hmem : i ∈ I₁ ∨ i ∈ I₂
  · exact ⟨i, hmem, (tablePerm_eq hiw).symm⟩
  exfalso
  rw [not_or] at hmem
  simp only [eaCountOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hcount
  have hc1 : I₁.contains i = false := by simpa using hmem.1
  have hc2 : I₂.contains i = false := by simpa using hmem.2
  have hs : sift E[i]! = true := (hD.sift _ _ hiw).2 (hWP hw)
  have hinv : invoOK n E[i]! = true := invoOK_of_mul_self hiw (hW2 w hw)
  have hlen : (centInvolIdx n sift E i).length < 16 := by
    rcases hcount i hi with (((h | h) | h) | h) | h
    · rw [hc1] at h; exact Bool.noConfusion h
    · rw [hc2] at h; exact Bool.noConfusion h
    · rw [hs] at h; exact Bool.noConfusion h
    · rw [hinv] at h; exact Bool.noConfusion h
    · exact h
  have hle : Nat.card W ≤ (centInvolIdx n sift E i).length := by
    refine card_le_length_of_forall W _ (fun y => tablePerm n E[y]!) fun v hv => ?_
    obtain ⟨y, hy, hyv⟩ := hD.cov v (hWS hv)
    refine ⟨y, ?_, (tablePerm_eq hyv).symm⟩
    simp only [centInvolIdx, List.mem_filter, List.mem_range, Bool.and_eq_true]
    exact ⟨hy, ⟨(hD.sift _ _ hyv).2 (hWP hv), invoOK_of_mul_self hyv (hW2 v hv)⟩,
      (commTT_iff hyv hiw).2 (mul_comm_of_exp_two hW2 hv hw)⟩
  omega

theorem eq_listed_of_checks (hD : TableEnum n S P sift E) {I₁ I₂ : List ℕ}
    (hl₁ : I₁.length = 16) (hl₂ : I₂.length = 16)
    (hc₁ : idxClosedOK n E I₁ = true) (hc₂ : idxClosedOK n E I₂ = true)
    (hcount : eaCountOK n sift E I₁ I₂ = true) {W : Subgroup (Perm (Fin n))} (hWS : W ≤ S)
    (hWP : W ≤ P) (hW16 : Nat.card W = 16) (hW2 : ∀ w ∈ W, w * w = 1) :
    ∃ I ∈ [I₁, I₂], (∀ y ∈ I, y < E.size) ∧ (∀ w ∈ W, ∃ y ∈ I, w = tablePerm n E[y]!) ∧
      ∀ y ∈ I, tablePerm n E[y]! ∈ W := by
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW16]; norm_num)
  have hU := mem_union_of_eaCountOK hD hcount hWS hWP hW16 hW2
  obtain ⟨hlt₁, hcl₁⟩ := mul_mem_of_idxClosedOK hD hc₁
  obtain ⟨hlt₂, hcl₂⟩ := mul_mem_of_idxClosedOK hD hc₂
  have hor := forall_or_forall_of_union hW2 (A := fun g => ∃ y ∈ I₁, g = tablePerm n E[y]!)
    (B := fun g => ∃ y ∈ I₂, g = tablePerm n E[y]!)
    (by
      rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
      obtain ⟨t, ht, he⟩ := hcl₁ y hy z hz
      exact ⟨t, ht, he⟩)
    (by
      rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
      obtain ⟨t, ht, he⟩ := hcl₂ y hy z hz
      exact ⟨t, ht, he⟩)
    (by
      intro w hw
      obtain ⟨y, hy | hy, hyw⟩ := hU w hw
      · exact Or.inl ⟨y, hy, hyw⟩
      · exact Or.inr ⟨y, hy, hyw⟩)
  rcases hor with h | h
  · exact ⟨I₁, List.mem_cons_self, hlt₁, h,
      forall_mem_of_card_le _ (by rw [hl₁, hW16]) h⟩
  · exact ⟨I₂, List.mem_cons_of_mem _ List.mem_cons_self, hlt₂, h,
      forall_mem_of_card_le _ (by rw [hl₂, hW16]) h⟩

theorem supportInput_of_checks (hD : TableEnum n S P sift E) {I₁ I₂ : List ℕ}
    (hl₁ : I₁.length = 16) (hl₂ : I₂.length = 16)
    (hc₁ : idxClosedOK n E I₁ = true) (hc₂ : idxClosedOK n E I₂ = true)
    (hcount : eaCountOK n sift E I₁ I₂ = true) (hsupp : eaSupportOK n sift E I₁ I₂ = true)
    {x : Perm (Fin n)} (hxS : x ∈ S) (hxP : x ∉ P) (hxx : x * x = 1)
    {W : Subgroup (Perm (Fin n))} (hWS : W ≤ S) (hWP : W ≤ P) (hW16 : Nat.card W = 16)
    (hW2 : ∀ w ∈ W, w * w = 1) (hWx : ∀ w ∈ W, x * w * x⁻¹ ∈ W) :
    ∃ a ∈ W, ∃ b ∈ W, a * x = x * a ∧ b * x = x * b ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a.support.card ≠ b.support.card := by
  obtain ⟨I, hI, hlt, hWI, hIW⟩ :=
    eq_listed_of_checks hD hl₁ hl₂ hc₁ hc₂ hcount hWS hWP hW16 hW2
  obtain ⟨m, hm, hmx⟩ := hD.cov x hxS
  have hsm : sift E[m]! = false := by
    cases hs : sift E[m]!
    · rfl
    · exact absurd ((hD.sift _ _ hmx).1 hs) hxP
  have hx1 : x ≠ 1 := fun h1 => hxP (h1 ▸ P.one_mem)
  have hinv : involOK n E[m]! = true :=
    involOK_of_orderOf hD.lt hmx (orderOf_eq_prime (by rw [sq]; exact hxx) hx1)
  simp only [eaSupportOK, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hsupp
  have hnorm : idxNormOK n E m I = true := by
    simp only [idxNormOK, List.all_eq_true, List.any_eq_true]
    intro y hy
    obtain ⟨t, ht, hte⟩ := hWI _ (hWx _ (hIW y hy))
    refine ⟨t, ht, (tblEq_iff_eq (Rep.compT hmx (hD.rep y (hlt y hy)))
      (Rep.compT (hD.rep t (hlt t ht)) hmx)).2 ?_⟩
    rw [← hte]
    group
  have h2 : twoSupportsOK n E m I = true := by
    rcases hsupp m hm with (h | h) | h
    · rw [hsm] at h; exact Bool.noConfusion h
    · rw [hinv] at h; exact Bool.noConfusion h
    · rcases h I hI with h | h
      · rw [hnorm] at h; exact Bool.noConfusion h
      · exact h
  simp only [twoSupportsOK, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at h2
  obtain ⟨a, ha, b, hb, ⟨⟨⟨hca, hcb⟩, ha1⟩, hb1⟩, hab⟩ := h2
  have hra := hD.rep a (hlt a ha)
  have hrb := hD.rep b (hlt b hb)
  refine ⟨_, hIW a ha, _, hIW b hb, (commTT_iff hra hmx).1 hca, (commTT_iff hrb hmx).1 hcb,
    fun h1 => ?_, fun h1 => ?_, ?_⟩
  · rw [(tblEq_idT_iff hD.lt hra).2 h1] at ha1
    exact Bool.noConfusion ha1
  · rw [(tblEq_idT_iff hD.lt hrb).2 h1] at hb1
    exact Bool.noConfusion hb1
  · rw [card_support_eq_movedCount hra, card_support_eq_movedCount hrb]
    exact hab

end Enum

theorem sylowOK_of_centDataOK {n NP cap : ℕ} {pg pgInv : Array Table} {sift : Table → Bool}
    {u : Table} {sylowGens : List Table} {sylowOrder : ℕ} {rows : List ClassRow}
    (h : centDataOK n NP cap pg pgInv sift u sylowGens sylowOrder rows = true) :
    sylowOK n cap pg pgInv sift u sylowGens sylowOrder = true := by
  simp only [centDataOK, Bool.and_eq_true] at h
  exact h.1.1

theorem enum_of_sylowOK {n cap : ℕ} (hn : n < 2 ^ 32) {pg pgInv : Array Table}
    {sift : Table → Bool} {u : Table} {sylowGens : List Table} {sylowOrder : ℕ}
    (h : sylowOK n cap pg pgInv sift u sylowGens sylowOrder = true) :
    (∀ k < (mulClosureH n sylowGens.toArray cap).1.size,
        Rep n (mulClosureH n sylowGens.toArray cap).1[k]!
          (tablePerm n (mulClosureH n sylowGens.toArray cap).1[k]!) ∧
        tablePerm n (mulClosureH n sylowGens.toArray cap).1[k]! ∈
          closure (tp n '' {x | x ∈ sylowGens.toArray})) ∧
      ∀ x ∈ closure (tp n '' {x | x ∈ sylowGens.toArray}),
        ∃ k < (mulClosureH n sylowGens.toArray cap).1.size,
          Rep n (mulClosureH n sylowGens.toArray cap).1[k]! x := by
  simp only [sylowOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hsg⟩, htree⟩, hclosed⟩, hdist⟩, -⟩ := h
  rw [Array.all_eq_true'] at hsg
  simp only [Bool.and_eq_true] at hsg
  obtain ⟨h1, h2, -⟩ := enum_spec hn (fun x hx => (hsg x hx).1.1) (fun x hx => (hsg x hx).1.2)
    htree hclosed hdist
  exact ⟨h1, h2⟩

theorem j2EAClosedOne_check :
    idxClosedOK 315 j2SylEnum j2EAIdxOne = true :=
  Certificates.certificate3966.1

theorem j2EAClosedTwo_check :
    idxClosedOK 315 j2SylEnum j2EAIdxTwo = true :=
  Certificates.certificate3966.2.1

theorem j2EACount_check :
    eaCountOK 315 j2Sift j2SylEnum j2EAIdxOne j2EAIdxTwo = true :=
  Certificates.certificate3966.2.2.1

theorem j2EASupport_check :
    eaSupportOK 315 j2Sift j2SylEnum j2EAIdxOne j2EAIdxTwo = true :=
  Certificates.certificate3966.2.2.2

section J2

theorem j2SylEnum_tableEnum : TableEnum 315 j2S j2P j2Sift j2SylEnum := by
  obtain ⟨h1, h2⟩ := enum_of_sylowOK (by norm_num) (sylowOK_of_centDataOK j2_centDataOK)
  exact ⟨by norm_num, fun k hk => (h1 k hk).1, h2, j2_groupData.sift⟩

theorem j2SylowSupportInput_of_cert : J2SylowSupportInput := by
  intro x hxS hxP hxx W hWS hWP hW16 hW2 hWx
  exact supportInput_of_checks j2SylEnum_tableEnum (by rfl) (by rfl) j2EAClosedOne_check
    j2EAClosedTwo_check j2EACount_check j2EASupport_check hxS hxP hxx hWS hWP hW16 hW2 hWx

end J2

end CFSG.SeitzReduction.SporadicRefine
