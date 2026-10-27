module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11Check
public import CFSG.Sporadic.Schreier.M11

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

section M11

@[expose] def M11Pair (x y : NativeSporadic.M11) : Prop :=
  orderOf x = 2 ∧ orderOf y = 4 ∧ orderOf (x * y) = 11 ∧
    orderOf (x * y * (x * (y * y)) * (x * (y * (y * y)))) = 3

theorem m11_pair_card
    : Nat.card {p : NativeSporadic.M11 × NativeSporadic.M11 //
    M11Pair p.1 p.2} = 7920 := by
  rw [← m11_pair_count]
  refine card_eq_length _
    (fun p : NativeSporadic.M11 × NativeSporadic.M11 =>
      ((p.1 : Equiv.Perm (Fin 11)), (p.2 : Equiv.Perm (Fin 11))))
    (fun p q h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))) _
    (((m11Elements_nodup.filter _).product (m11Elements_nodup.filter _)).filter _) ?_
  rintro ⟨g, h⟩
  simp only [List.mem_filter, List.mem_product, mem_m11Elements, Bool.and_eq_true,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hg, hg2⟩, hh, hh4⟩, hgh, hgw⟩
    exact ⟨(⟨g, hg⟩, ⟨h, hh⟩), ⟨(m11_orderOf_eq_iff _ (by norm_num)).2 hg2,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hh4,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hgh,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hgw⟩, rfl, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy, hxw⟩, rfl, rfl⟩
    exact ⟨⟨⟨x.2, (m11_orderOf_eq_iff x (by norm_num)).1 hx⟩, y.2,
      (m11_orderOf_eq_iff y (by norm_num)).1 hy⟩,
      (m11_orderOf_eq_iff (x * y) (by norm_num)).1 hxy,
      (m11_orderOf_eq_iff _ (by norm_num)).1 hxw⟩

theorem m11_pair_ab : M11Pair m11a m11b := by
  obtain ⟨h1, h2, h3, h4⟩ := m11_orders_ab
  exact ⟨(m11_orderOf_eq_iff _ (by norm_num)).2 h1, (m11_orderOf_eq_iff _ (by norm_num)).2 h2,
    (m11_orderOf_eq_iff _ (by norm_num)).2 h3, (m11_orderOf_eq_iff _ (by norm_num)).2 h4⟩

theorem m11_autInner
    : ∀ φ : NativeSporadic.M11 ≃* NativeSporadic.M11,
    ∃ s : NativeSporadic.M11, ∀ x, φ x = s * x * s⁻¹ := by
  refine autInner_of_card_pairs m11_center_eq_bot m11_closure_eq_top M11Pair ?_ ?_
  · intro φ
    obtain ⟨h1, h2, h3, h4⟩ := m11_pair_ab
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq]; exact h1
    · rw [MulEquiv.orderOf_eq]; exact h2
    · rw [← map_mul, MulEquiv.orderOf_eq]; exact h3
    · simp only [← map_mul]
      rw [MulEquiv.orderOf_eq]; exact h4
  · rw [m11_pair_card, m11_card]

theorem m11_mem_invs
    {w : NativeSporadic.M11} (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    (w : Equiv.Perm (Fin 11)) ∈ m11Invs := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  rw [m11Invs, List.mem_filter]
  exact ⟨(mem_m11Elements _).2 w.2, (m11_orderOf_eq_iff w (by norm_num)).1 hord⟩

theorem m11_elemAbelian_le :
    ∀ B : Subgroup NativeSporadic.M11, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 2 := by
  refine card_le_two_pow_of_no_indep 2 ?_
  rintro ⟨l, hl, hlen⟩
  match l, hlen, hl with
  | [x, y, z], _, hl =>
    obtain ⟨hx2, hy2, hz2, hx1, hy1, hz1, hxy, hxz, hyz, hxy', hxz', hxyz, hyz'⟩ :=
      indepList_three hl
    have h1 := List.all_eq_true.1 m11_no_indep_triple _ (m11_mem_invs hx2 hx1)
    have h2 := List.all_eq_true.1 h1 _ (m11_mem_invs hy2 hy1)
    have hxyb : (((x : Equiv.Perm (Fin 11)) * (y : Equiv.Perm (Fin 11))) ==
        ((y : Equiv.Perm (Fin 11)) * (x : Equiv.Perm (Fin 11)))) = true := by
      simpa using congrArg Subtype.val hxy
    simp only [hxyb, Bool.not_true, Bool.false_or] at h2
    have h3 := List.all_eq_true.1 h2 _ (m11_mem_invs hz2 hz1)
    have hxzb : (((x : Equiv.Perm (Fin 11)) * (z : Equiv.Perm (Fin 11))) ==
        ((z : Equiv.Perm (Fin 11)) * (x : Equiv.Perm (Fin 11)))) = true := by
      simpa using congrArg Subtype.val hxz
    have hyzb : (((y : Equiv.Perm (Fin 11)) * (z : Equiv.Perm (Fin 11))) ==
        ((z : Equiv.Perm (Fin 11)) * (y : Equiv.Perm (Fin 11)))) = true := by
      simpa using congrArg Subtype.val hyz
    simp only [hxzb, hyzb, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      beq_iff_eq] at h3
    rcases h3 with ((h | h) | h) | h
    · exact hxz' (Subtype.ext h)
    · exact hxy' (Subtype.ext h)
    · exact hxyz (Subtype.ext h)
    · exact hyz' (Subtype.ext h)

theorem m11_exists_conj
    {t : NativeSporadic.M11} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ h : NativeSporadic.M11, h * m11a * h⁻¹ = t := by
  have hmem := m11_mem_invs ht2 ht1
  have := List.all_eq_true.1 m11_conj_class _ hmem
  obtain ⟨h0, hh0, heq⟩ := List.mem_map.1 (List.elem_iff.1 this)
  exact ⟨⟨h0, (mem_m11Elements h0).1 hh0⟩, Subtype.ext heq⟩

theorem m11_gen :
    ∀ t : NativeSporadic.M11, t * t = 1 → t ≠ 1 →
    ∃ cs : List NativeSporadic.M11, cs.length = 3 ∧
      Subgroup.closure {x | ∃ c ∈ cs, x = c * t * c⁻¹} = ⊤ := by
  intro t ht2 ht1
  obtain ⟨hmemG, hwa, hwb⟩ := m11_gen_check
  have hmem : ∀ i, m11G i ∈ m11Invs := fun i => by
    have := List.all_eq_true.1 hmemG i (List.mem_finRange i)
    exact List.elem_iff.1 this
  have hg : ∀ i, m11G i ∈ NativeSporadic.M11 := fun i =>
    (mem_m11Elements _).1 (List.mem_filter.1 (hmem i)).1
  have hgo : ∀ i, orderOf (⟨m11G i, hg i⟩ : NativeSporadic.M11) = 2 := fun i => by
    rw [m11_orderOf_eq_iff _ (by norm_num)]
    exact (List.mem_filter.1 (hmem i)).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g : Fin 3 → NativeSporadic.M11 := fun i => ⟨m11G i, hg i⟩
  have hg2 : ∀ i, g i * g i = 1 := fun i => by
    have := pow_orderOf_eq_one (g i)
    rwa [hgo i, sq] at this
  have hg1 : ∀ i, g i ≠ 1 := fun i h => by
    have := hgo i
    change orderOf (g i) = 2 at this
    rw [h, orderOf_one] at this
    omega
  choose c hc using fun i => m11_exists_conj (hg2 i) (hg1 i)
  have h0 : Subgroup.closure {x : NativeSporadic.M11 | ∃ c' ∈ [c 0, c 1, c 2],
      x = c' * m11a * c'⁻¹} = ⊤ := by
    have hset : {x : NativeSporadic.M11 | ∃ c' ∈ [c 0, c 1, c 2], x = c' * m11a * c'⁻¹} =
        Set.range g := by
      ext x
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq,
        Set.mem_range]
      constructor
      · rintro ⟨c', hc' | hc' | hc', rfl⟩
        · exact ⟨0, by rw [← hc 0, hc']⟩
        · exact ⟨1, by rw [← hc 1, hc']⟩
        · exact ⟨2, by rw [← hc 2, hc']⟩
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact ⟨c 0, Or.inl rfl, (hc 0).symm⟩
        · exact ⟨c 1, Or.inr (Or.inl rfl), (hc 1).symm⟩
        · exact ⟨c 2, Or.inr (Or.inr rfl), (hc 2).symm⟩
    rw [hset]
    have hgmem : ∀ i, g i ∈ Subgroup.closure (Set.range g) := fun i =>
      Subgroup.subset_closure ⟨i, rfl⟩
    have ha : m11a ∈ Subgroup.closure (Set.range g) := by
      have : (m11WordA.map g).prod = m11a := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_list_prod, List.map_map]
        exact hwa
      rw [← this]
      exact Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        exact hgmem i
    have hb : m11b ∈ Subgroup.closure (Set.range g) := by
      have : (m11WordB.map g).prod = m11b := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_list_prod, List.map_map]
        exact hwb
      rw [← this]
      exact Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        exact hgmem i
    rw [eq_top_iff, ← m11_closure_eq_top, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  obtain ⟨h, hh⟩ := m11_exists_conj ht2 ht1
  exact exists_generating_conjugates_of_conj [c 0, c 1, c 2] h0 hh

theorem m11_weight_le
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (e : CQ L ≃* NativeSporadic.Carrier .M11)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E) :
    4 * (Nat.card E * Nat.card (fixV E)) ≤ Nat.card W := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hL : L ≠ ⊥ := ne_bot_of_isQuasisimple hq
  have e' : CQ L ≃* NativeSporadic.M11 := e
  have hrank := rank_of_generation hW hq.1 hirr hL e' (k := 3) (ρ := 4) (p := 11) (by norm_num)
    (by rw [m11_card]; norm_num) (by norm_num [orderOf_two_zmod_11])
    (fun t ht2 ht1 => m11_gen t ht2 ht1)
  have h := exclusion_of_autInner_le hW hq.1 hirr hE hEne hEel e' m11_autInner (r := 2) (ρ := 4)
    (by norm_num) m11_elemAbelian_le hrank
  simpa using h

theorem sporadicExclusion_M11
    : SporadicExclusion .M11 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  have h := m11_weight_le hW hq hirr e hE hEne hEel
  have hpos : 0 < Nat.card E * Nat.card (fixV E) := Nat.mul_pos Nat.card_pos Nat.card_pos
  omega

end M11

end CFSG.QuasithinUnique.Setup.X1
