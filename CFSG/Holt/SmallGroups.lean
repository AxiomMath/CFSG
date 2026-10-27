module

public import CFSG.Permutation.BurnsideSchur.PrimeDegree
public import Certificates.Certificate21301
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.Holt.SmallGroups

open Equiv Equiv.Perm MulAction

theorem exists_finRotate_mem_map_conj {M : Subgroup (Perm (Fin 7))} (h7 : 7 ∣ Nat.card M) :
    ∃ σ : Perm (Fin 7), finRotate 7 ∈ M.map (MulAut.conj σ).toMonoidHom := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 7 h7
  rw [← Subgroup.orderOf_coe] at hc
  have hcyc : (c : Perm (Fin 7)).IsCycle :=
    isCycle_of_prime_order'' (by norm_num) (by simpa using hc)
  have htype : (c : Perm (Fin 7)).cycleType = (finRotate 7).cycleType := by
    rw [hcyc.cycleType, ← hcyc.orderOf, hc]
    exact (cycleType_finRotate (n := 5)).symm
  obtain ⟨σ, hσ⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr htype)
  exact ⟨σ, c, c.2, by simpa [MulAut.conj_apply] using hσ⟩

theorem forty_two_dvd_card_zmod {M : Subgroup (Perm (ZMod 7))}
    (hT : ∀ c : ZMod 7, Equiv.addRight c ∈ M) {g : Perm (ZMod 7)} (hg : g ∈ M) (hg1 : g ≠ 1)
    {x y : ZMod 7} (hxy : x ≠ y) (hx : g x = x) (hy : g y = y) : 42 ∣ Nat.card M := by
  obtain ⟨e⟩ : Nonempty (Fin 2 ↪ ZMod 7) := ⟨⟨![0, 1], by decide⟩⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h2 : IsMultiplyPretransitive M (ZMod 7) 2 := by
    by_contra h2
    obtain ⟨a, -, b, hab⟩ :=
      CFSG.BurnsideSchur.exists_affine_of_not_isMultiplyPretransitive hT h2 (σ := g) hg
    have h1 : a * x + b = x := (hab x).symm.trans hx
    have h1' : a * y + b = y := (hab y).symm.trans hy
    have ha : a = 1 := by
      have hm : (a - 1) * (x - y) = 0 := by linear_combination h1 - h1'
      rcases mul_eq_zero.mp hm with h | h
      · linear_combination h
      · exact absurd (sub_eq_zero.mp h) hxy
    have hb : b = 0 := by
      rw [ha, one_mul] at h1
      linear_combination h1
    exact hg1 (Equiv.ext fun z => by rw [hab z, ha, hb, one_mul, add_zero]; rfl)
  have horb : orbit M e = Set.univ := Set.eq_univ_of_forall fun f => by
    obtain ⟨g, hg⟩ := @exists_smul_eq M _ _ h2 e f
    exact ⟨g, hg⟩
  have hcard : (orbit M e).ncard = 42 := by
    rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
    simp
  have hdvd := Subgroup.index_dvd_card (stabilizer M e)
  rw [index_stabilizer] at hdvd
  convert hdvd using 1
  exact hcard.symm

theorem card_le_factorial_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) : Nat.card G ≤ H.index.factorial := by
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  calc Nat.card G ≤ Nat.card (Perm (G ⧸ H)) := Nat.card_le_card_of_injective _ hinj
    _ = H.index.factorial := by rw [Nat.card_perm, Subgroup.index_eq_card]

section Regular

variable {G α : Type*} [Group G] [MulAction G α]

theorem isMultiplyPretransitive_of_exists_smul_eq {n : ℕ} (x₀ : Fin n ↪ α)
    (h : ∀ x : Fin n ↪ α, ∃ g : G, g • x₀ = x) : IsMultiplyPretransitive G α n :=
  ⟨fun x y => by
    obtain ⟨g, rfl⟩ := h x
    obtain ⟨g', rfl⟩ := h y
    exact ⟨g' * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩⟩

theorem eq_one_of_smul_eq_self [Finite G] [Finite α] {n : ℕ} (h : IsMultiplyPretransitive G α n)
    (hcard : Nat.card G = Nat.card (Fin n ↪ α)) {g : G} {x : Fin n ↪ α} (hg : g • x = x) :
    g = 1 := by
  have horb : orbit G x = Set.univ := Set.eq_univ_of_forall fun y => by
    obtain ⟨k, hk⟩ := @exists_smul_eq G _ _ h x y
    exact ⟨k, hk⟩
  have h1 := Subgroup.card_mul_index (stabilizer G x)
  rw [index_stabilizer, horb, Set.ncard_univ, ← hcard] at h1
  have hst : stabilizer G x = ⊥ := Subgroup.card_eq_one.mp
    (Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [one_mul]; exact h1))
  have hmem : g ∈ stabilizer G x := hg
  rwa [hst, Subgroup.mem_bot] at hmem

end Regular

section M11

open CFSG.Sporadic.Mathieu CFSG.Adapters.RankTwoModelTransports

theorem m11_four_check : Native.check 11 m11Data4 = true :=
  Certificates.certificate21301

theorem nativeM11_hyp4 :
    Hyp CFSG.Blueprint.NativeSporadic.M11 m11Data4 m11a m11b where
  lt := by norm_num
  gen := closure_pair_eq_top m11_eq _ _
  repA := by
    rw [show m11Data4.tA = Native.m11Data.tA from rfl]
    exact rep_m11a
  repB := by
    rw [show m11Data4.tB = Native.m11Data.tB from rfl]
    exact rep_m11b
  cert := m11_four_check

theorem m11_le_alternatingGroup : CFSG.Open.M11 ≤ alternatingGroup (Fin 11) := by
  rw [catalogueM11_eq_closure, Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_alternatingGroup] <;> decide

theorem card_m11 : Nat.card CFSG.Open.M11 = 7920 := by
  have hinj : Function.Injective (MulAut.conj m11Conj).toMonoidHom :=
    (MulAut.conj m11Conj).injective
  rw [← nativeM11_map_conj, Subgroup.card_map_of_injective hinj, card_eq nativeM11_hyp4]
  rfl

@[expose] def m11Base : Fin 4 ↪ Fin 11 := ⟨![0, 1, 2, 3], by decide⟩

theorem nativeM11_isMultiplyPretransitive :
    IsMultiplyPretransitive CFSG.Blueprint.NativeSporadic.M11 (Fin 11) 4 := by
  refine isMultiplyPretransitive_of_exists_smul_eq m11Base fun x => ?_
  have hx : ∀ i j : Fin 4, i ≠ j → x i ≠ x j := fun i j h => x.injective.ne h
  obtain ⟨g, h0, h1, h2, h3⟩ := exists_smul_eq_four nativeM11_hyp4 (by decide) (by norm_num)
    (x 0) (x 1) (x 2) (x 3) (hx 0 1 (by decide)) (hx 0 2 (by decide)) (hx 0 3 (by decide))
    (hx 1 2 (by decide)) (hx 1 3 (by decide)) (hx 2 3 (by decide))
  refine ⟨g, Function.Embedding.ext fun i => ?_⟩
  fin_cases i
  exacts [h0, h1, h2, h3]

theorem m11_isMultiplyPretransitive_four :
    IsMultiplyPretransitive CFSG.Open.M11 (Fin 11) 4 := by
  refine isMultiplyPretransitive_of_exists_smul_eq m11Base fun x => ?_
  obtain ⟨h, hh⟩ := @exists_smul_eq _ _ _ nativeM11_isMultiplyPretransitive
    (m11Base.trans m11Conj.symm.toEmbedding) (x.trans m11Conj.symm.toEmbedding)
  have hmem : m11Conj * (h : Perm (Fin 11)) * m11Conj⁻¹ ∈ CFSG.Open.M11 := by
    rw [← nativeM11_map_conj]
    exact ⟨h, h.2, rfl⟩
  refine ⟨⟨_, hmem⟩, Function.Embedding.ext fun i => ?_⟩
  have hi := congrArg (fun e : Fin 4 ↪ Fin 11 => e i) hh
  simp only [Function.Embedding.smul_apply, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, Subgroup.smul_def, Perm.smul_def] at hi
  rw [Function.Embedding.smul_apply, Subgroup.mk_smul, Perm.smul_def, Perm.mul_apply,
    Perm.mul_apply, Perm.inv_def, hi, Equiv.apply_symm_apply]

theorem m11_isMultiplyPretransitive_three :
    IsMultiplyPretransitive CFSG.Open.M11 (Fin 11) 3 := by
  have := m11_isMultiplyPretransitive_four
  exact isMultiplyPretransitive_of_le (n := 4) (by norm_num) (by simp)

theorem eq_one_of_mem_m11_of_fix {g : Perm (Fin 11)}
    (hg : g ∈ CFSG.Open.M11) (y : Fin 4 ↪ Fin 11) (hy : ∀ i, g (y i) = y i) : g = 1 := by
  have hcard : Nat.card CFSG.Open.M11 = Nat.card (Fin 4 ↪ Fin 11) := by
    rw [card_m11, Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
    rfl
  have := eq_one_of_smul_eq_self m11_isMultiplyPretransitive_four hcard (g := ⟨g, hg⟩) (x := y)
    (Function.Embedding.ext hy)
  exact congrArg Subtype.val this

@[expose] def m11Stab (a b c : Fin 11) : Subgroup (Perm (Fin 11)) :=
  CFSG.Open.M11 ⊓ fixingSubgroup (Perm (Fin 11)) {a, b, c}

theorem mem_m11Stab {a b c : Fin 11} {g : Perm (Fin 11)} :
    g ∈ m11Stab a b c ↔ g ∈ CFSG.Open.M11 ∧ g a = a ∧ g b = b ∧ g c = c := by
  simp [m11Stab, mem_fixingSubgroup_iff, Perm.smul_def]

@[expose] def tripleEmb {a b c : Fin 11} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fin 3 ↪ Fin 11 :=
  ⟨![a, b, c], fun i j h => by
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

@[expose] def quadEmb {a b c d : Fin 11} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ Fin 11 :=
  ⟨![a, b, c, d], fun i j h => by
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

variable {a b c : Fin 11}

theorem eq_one_of_mem_m11Stab (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {r : Perm (Fin 11)}
    (hr : r ∈ m11Stab a b c) {x : Fin 11} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hx : r x = x) : r = 1 := by
  obtain ⟨hrM, ha, hb, hc⟩ := mem_m11Stab.mp hr
  refine eq_one_of_mem_m11_of_fix hrM (quadEmb hab hac (Ne.symm hxa) hbc (Ne.symm hxb)
    (Ne.symm hxc)) fun i => ?_
  fin_cases i
  exacts [ha, hb, hc, hx]

theorem m11_word_mem {g : Perm (Fin 11)}
    (hg : g ∈ Subgroup.closure ({m11CatC, m11CatD} : Set (Perm (Fin 11)))) :
    g ∈ CFSG.Open.M11 := by
  rwa [catalogueM11_eq_closure]

@[expose] def m11i : Perm (Fin 11) := List.formPerm [3, 8, 9, 10] * List.formPerm [4, 5, 7, 6]

@[expose] def m11j : Perm (Fin 11) := List.formPerm [3, 5, 9, 6] * List.formPerm [4, 10, 7, 8]

@[expose] def m11z : Perm (Fin 11) := m11i * m11i

@[expose] def m11StabList : List (Perm (Fin 11)) :=
  [1, m11i, m11i * m11i, m11i * m11i * m11i, m11j, m11i * m11j, m11i * m11i * m11j,
    m11i * m11i * m11i * m11j]

theorem m11i_eq : m11i = [m11CatD, m11CatD, m11CatC, m11CatD, m11CatC, m11CatC, m11CatC,
    m11CatC, m11CatC, m11CatD, m11CatC].prod := by
  decide +kernel

theorem m11j_eq : m11j = [m11CatC, m11CatC, m11CatC, m11CatD, m11CatD, m11CatC, m11CatD,
    m11CatC, m11CatD, m11CatC, m11CatC, m11CatD, m11CatC].prod := by
  decide +kernel

theorem m11Stab_check :
    (m11StabList.all fun r => decide (r 0 = 0 ∧ r 1 = 1 ∧ r 2 = 2)) &&
    ((List.finRange 11).all fun y =>
      decide (y = 0 ∨ y = 1 ∨ y = 2) || m11StabList.any fun r => decide (r 3 = y)) &&
    (m11StabList.all fun r => !decide (r * r = 1) || decide (r = 1) || decide (r = m11z)) &&
    (m11StabList.all fun r => decide (r * m11z = m11z * r)) &&
    decide (m11z ≠ 1 ∧ m11z * m11z = 1 ∧ m11z ∈ m11StabList) = true := by
  decide +kernel

theorem list_prod_mem_m11 {l : List (Perm (Fin 11))}
    (hl : (l.all fun y => decide (y = m11CatC) || decide (y = m11CatD)) = true) :
    l.prod ∈ CFSG.Open.M11 := by
  refine CFSG.Open.M11.list_prod_mem fun x hx => m11_word_mem (Subgroup.subset_closure ?_)
  have h := List.all_eq_true.mp hl x hx
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

theorem m11i_mem : m11i ∈ CFSG.Open.M11 := by
  rw [m11i_eq]
  exact list_prod_mem_m11 (by decide +kernel)

theorem m11j_mem : m11j ∈ CFSG.Open.M11 := by
  rw [m11j_eq]
  exact list_prod_mem_m11 (by decide +kernel)

theorem m11StabList_mem : ∀ r ∈ m11StabList, r ∈ m11Stab 0 1 2 := by
  have h := m11Stab_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have hM : ∀ r ∈ m11StabList, r ∈ CFSG.Open.M11 := by
    have hm := fun {x y : Perm (Fin 11)} => @Subgroup.mul_mem _ _ CFSG.Open.M11 x y
    have hi := m11i_mem
    have hj := m11j_mem
    simp only [m11StabList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    exact ⟨CFSG.Open.M11.one_mem, hi, hm hi hi, hm (hm hi hi) hi, hj, hm hi hj, hm (hm hi hi) hj,
      hm (hm (hm hi hi) hi) hj⟩
  exact fun r hr => mem_m11Stab.mpr ⟨hM r hr, h.1.1.1.1 r hr⟩

theorem mem_m11StabList {r : Perm (Fin 11)} (hr : r ∈ m11Stab 0 1 2) : r ∈ m11StabList := by
  have h := m11Stab_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    List.any_eq_true] at h
  obtain ⟨-, h0, h1, h2⟩ := mem_m11Stab.mp hr
  have h3 : ¬ (r 3 = 0 ∨ r 3 = 1 ∨ r 3 = 2) := by
    rintro (h | h | h)
    · exact absurd (r.injective (h.trans h0.symm)) (by decide)
    · exact absurd (r.injective (h.trans h1.symm)) (by decide)
    · exact absurd (r.injective (h.trans h2.symm)) (by decide)
  obtain ⟨l, hl, hl3⟩ := (h.1.1.1.2 (r 3) (List.mem_finRange _)).resolve_left h3
  have hlr : l⁻¹ * r ∈ m11Stab 0 1 2 :=
    (m11Stab 0 1 2).mul_mem ((m11Stab 0 1 2).inv_mem (m11StabList_mem l hl)) hr
  have hfix : (l⁻¹ * r) 3 = 3 := by rw [Perm.mul_apply, ← hl3, Perm.inv_eq_iff_eq]
  have hone := eq_one_of_mem_m11Stab (by decide) (by decide) (by decide) hlr (by decide)
    (by decide) (by decide) hfix
  rw [inv_mul_eq_one] at hone
  exact hone ▸ hl

theorem m11z_facts : m11z ∈ m11Stab 0 1 2 ∧ m11z ≠ 1 ∧ m11z * m11z = 1 ∧
    (∀ r ∈ m11Stab 0 1 2, r * r = 1 → r = 1 ∨ r = m11z) ∧
    ∀ r ∈ m11Stab 0 1 2, r * m11z = m11z * r := by
  have h := m11Stab_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨-, hinv⟩, hcomm⟩, hz1, hzz, hzL⟩ := h
  refine ⟨m11StabList_mem _ hzL, hz1, hzz, fun r hr hrr => ?_, fun r hr =>
    hcomm r (mem_m11StabList hr)⟩
  rcases hinv r (mem_m11StabList hr) with (h | h) | h
  · exact absurd hrr h
  · exact Or.inl h
  · exact Or.inr h

theorem exists_mem_m11_apply_eq (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g ∈ CFSG.Open.M11, g 0 = a ∧ g 1 = b ∧ g 2 = c := by
  obtain ⟨g, hg⟩ := @exists_smul_eq _ _ _ m11_isMultiplyPretransitive_three
    (tripleEmb (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide))
    (tripleEmb hab hac hbc)
  have hgi := fun i => congrArg (fun e : Fin 3 ↪ Fin 11 => e i) hg
  exact ⟨g, g.2, hgi 0, hgi 1, hgi 2⟩

theorem exists_central_involution_m11Stab (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ z ∈ m11Stab a b c, z ≠ 1 ∧ z * z = 1 ∧ (∀ r ∈ m11Stab a b c, r * r = 1 → r = 1 ∨ r = z) ∧
      ∀ r ∈ m11Stab a b c, r * z = z * r := by
  obtain ⟨g, hgM, hg0, hg1, hg2⟩ := exists_mem_m11_apply_eq hab hac hbc
  obtain ⟨hz, hz1, hzz, hzu, hzc⟩ := m11z_facts
  have hginv : ∀ {p q : Fin 11}, g p = q → g⁻¹ q = p := fun h => by rw [← h, Perm.inv_eq_iff_eq]
  have hconj : ∀ r ∈ m11Stab a b c, g⁻¹ * r * g ∈ m11Stab 0 1 2 := fun r hr => by
    obtain ⟨hrM, ha, hb, hc⟩ := mem_m11Stab.mp hr
    refine mem_m11Stab.mpr ⟨CFSG.Open.M11.mul_mem (CFSG.Open.M11.mul_mem
      (CFSG.Open.M11.inv_mem hgM) hrM) hgM, ?_, ?_, ?_⟩ <;>
      simp only [Perm.mul_apply, hg0, hg1, hg2, ha, hb, hc, hginv hg0, hginv hg1, hginv hg2]
  have hconj' : ∀ r ∈ m11Stab 0 1 2, g * r * g⁻¹ ∈ m11Stab a b c := fun r hr => by
    obtain ⟨hrM, h0, h1, h2⟩ := mem_m11Stab.mp hr
    refine mem_m11Stab.mpr ⟨CFSG.Open.M11.mul_mem (CFSG.Open.M11.mul_mem hgM hrM)
      (CFSG.Open.M11.inv_mem hgM), ?_, ?_, ?_⟩ <;>
      simp only [Perm.mul_apply, hginv hg0, hginv hg1, hginv hg2, h0, h1, h2, hg0, hg1, hg2]
  have hback : ∀ r, r = g * (g⁻¹ * r * g) * g⁻¹ := fun r => by group
  refine ⟨g * m11z * g⁻¹, hconj' _ hz, fun h => hz1 ?_, ?_, fun r hr hrr => ?_, fun r hr => ?_⟩
  · calc m11z = g⁻¹ * (g * m11z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · calc g * m11z * g⁻¹ * (g * m11z * g⁻¹) = g * (m11z * m11z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  · have hrr' : g⁻¹ * r * g * (g⁻¹ * r * g) = 1 := by
      calc g⁻¹ * r * g * (g⁻¹ * r * g) = g⁻¹ * (r * r) * g := by group
        _ = 1 := by rw [hrr]; group
    rcases hzu _ (hconj r hr) hrr' with h | h
    · left
      rw [hback r, h]
      group
    · right
      rw [hback r, h]
  · have h := hzc _ (hconj r hr)
    calc r * (g * m11z * g⁻¹) = g * (g⁻¹ * r * g * m11z) * g⁻¹ := by group
      _ = g * (m11z * (g⁻¹ * r * g)) * g⁻¹ := by rw [h]
      _ = g * m11z * g⁻¹ * r := by group

end M11

end CFSG.Holt.SmallGroups
