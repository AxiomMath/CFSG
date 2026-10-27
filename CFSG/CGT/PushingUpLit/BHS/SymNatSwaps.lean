module

public import CFSG.CGT.PushingUpLit.BHS.SymNatWeight

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6

section Perm

variable {α : Type*} [DecidableEq α]

theorem eq_swap_of_isSwap_apply_ne {t : Equiv.Perm α} (ht : t.IsSwap) {x : α} (hx : t x ≠ x) :
    t = Equiv.swap x (t x) := by
  obtain ⟨a, b, hab, rfl⟩ := ht
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left]
  · by_cases hxb : x = b
    · subst hxb
      rw [Equiv.swap_apply_right, Equiv.swap_comm]
    · exact absurd (Equiv.swap_apply_of_ne_of_ne hxa hxb) hx

theorem apply_eq_of_commute_swap {t t' : Equiv.Perm α} (ht : t.IsSwap) (ht' : t'.IsSwap)
    (hcomm : t * t' = t' * t) (hne : t ≠ t') {x : α} (hx : t x ≠ x) : t' x = x := by
  by_contra hx'
  have e1 := eq_swap_of_isSwap_apply_ne ht hx
  have e2 := eq_swap_of_isSwap_apply_ne ht' hx'
  by_cases hyz : t x = t' x
  · apply hne
    calc t = Equiv.swap x (t x) := e1
      _ = Equiv.swap x (t' x) := by rw [hyz]
      _ = t' := e2.symm
  · have h1 : t (t' x) = t' x :=
      calc t (t' x) = Equiv.swap x (t x) (t' x) := congrArg (fun σ => σ (t' x)) e1
        _ = t' x := Equiv.swap_apply_of_ne_of_ne hx' fun h => hyz h.symm
    have h2 : t' (t x) = t x :=
      calc t' (t x) = Equiv.swap x (t' x) (t x) := congrArg (fun σ => σ (t x)) e2
        _ = t x := Equiv.swap_apply_of_ne_of_ne hx hyz
    have h3 : t (t' x) = t' (t x) := by
      have := congrArg (fun σ : Equiv.Perm α => σ x) hcomm
      simpa only [Equiv.Perm.mul_apply] using this
    exact hyz (h1.symm.trans (h3.trans h2)).symm

omit [DecidableEq α] in
theorem apply_eq_of_mem_closure {S : Set (Equiv.Perm α)} {x : α} (h : ∀ s ∈ S, s x = x)
    {a : Equiv.Perm α} (ha : a ∈ Subgroup.closure S) : a x = x := by
  have hle : Subgroup.closure S ≤ MulAction.stabilizer (Equiv.Perm α) x :=
    (Subgroup.closure_le _).2 fun s hs => MulAction.mem_stabilizer_iff.2 (h s hs)
  exact MulAction.mem_stabilizer_iff.1 (hle ha)

end Perm

theorem closure_comm {G : Type*} [Group G] {T : Set G} (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t)
    {x y : G} (hx : x ∈ Subgroup.closure T) (hy : y ∈ Subgroup.closure T) : x * y = y * x := by
  have := Subgroup.isMulCommutative_closure (k := T) fun a ha b hb _ => hc a ha b hb
  exact setLike_mul_comm hx hy

variable {n : ℕ}

theorem sq_eq_one_of_isSwap {t : Equiv.Perm (Fin n)} (ht : t.IsSwap) : t ^ 2 = 1 := by
  have := pow_orderOf_eq_one t
  rwa [ht.orderOf] at this

theorem sq_eq_one_of_mem_closure {T : Set (Equiv.Perm (Fin n))} (hT : ∀ t ∈ T, t.IsSwap)
    (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) {a : Equiv.Perm (Fin n)}
    (ha : a ∈ Subgroup.closure T) : a ^ 2 = 1 := by
  induction ha using Subgroup.closure_induction with
  | mem t ht => exact sq_eq_one_of_isSwap (hT t ht)
  | one => exact one_pow 2
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := closure_comm hc ha hb
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem two_pow_ncard_le_card_closure {T : Set (Equiv.Perm (Fin n))} (hfin : T.Finite)
    (hT : ∀ t ∈ T, t.IsSwap) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) :
    2 ^ T.ncard ≤ Nat.card (Subgroup.closure T) := by
  revert hT hc
  induction T, hfin using Set.Finite.induction_on with
  | empty =>
    intro _ _
    simp
  | @insert a S haS hS ih =>
    intro hT hc
    have hTS : ∀ t ∈ S, t.IsSwap := fun t ht => hT t (Set.mem_insert_of_mem a ht)
    have hcS : ∀ t ∈ S, ∀ t' ∈ S, t * t' = t' * t := fun t ht t' ht' =>
      hc t (Set.mem_insert_of_mem a ht) t' (Set.mem_insert_of_mem a ht')
    have ih' := ih hTS hcS
    have haSw : a.IsSwap := hT a (Set.mem_insert a S)
    have hclos : Subgroup.closure (insert a S) = Subgroup.closure S ⊔ Subgroup.zpowers a := by
      rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure, sup_comm]
    obtain ⟨x, hx⟩ : ∃ x, a x ≠ x := by
      obtain ⟨x, y, hxy, rfl⟩ := haSw
      exact ⟨x, by rw [Equiv.swap_apply_left]; exact hxy.symm⟩
    have hfixS : ∀ s ∈ S, s x = x := fun s hs =>
      apply_eq_of_commute_swap haSw (hTS s hs)
        (hc a (Set.mem_insert a S) s (Set.mem_insert_of_mem a hs))
        (fun h => haS (h ▸ hs)) hx
    have haX : a ∉ Subgroup.closure S := fun h => hx (apply_eq_of_mem_closure hfixS h)
    have hcomm : ∀ u ∈ Subgroup.closure S, ∀ w ∈ Subgroup.zpowers a, u * w = w * u := by
      intro u hu w hw
      have hu' : u ∈ Subgroup.closure (insert a S) := by
        rw [hclos]
        exact Subgroup.mem_sup_left hu
      have hw' : w ∈ Subgroup.closure (insert a S) := by
        rw [hclos]
        exact Subgroup.mem_sup_right hw
      exact closure_comm hc hu' hw'
    have hcard := card_sup_mul_card_inf' hcomm
    have hinf : Subgroup.closure S ⊓ Subgroup.zpowers a = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      obtain ⟨hgS, k, hk⟩ := (Subgroup.mem_inf.1 hg).imp_right Subgroup.mem_zpowers_iff.1
      rw [Subgroup.mem_bot]
      have ha2 : a ^ 2 = 1 := sq_eq_one_of_isSwap haSw
      have hk' : g = 1 ∨ g = a := by
        rw [← hk]
        have h1 : a ^ k = a ^ (k % 2) := by
          conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
          have h2 : a ^ (2 : ℤ) = 1 := by exact_mod_cast ha2
          rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
        have h3 : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rcases h3 with h | h
        · left
          rw [h1, h, zpow_zero]
        · right
          rw [h1, h, zpow_one]
      rcases hk' with h | h
      · exact h
      · exact absurd (h ▸ hgS) haX
    have hY : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers, haSw.orderOf]
    rw [hinf, Subgroup.card_bot, mul_one, hY] at hcard
    rw [Set.ncard_insert_of_notMem haS hS, hclos, hcard, pow_succ]
    exact Nat.mul_le_mul_right 2 ih'

@[expose] def stabFun (f : Fin n → ZMod 2) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {a | ∀ i, f (a i) = f i}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb i => by rw [Equiv.Perm.mul_apply, ha, hb]
  inv_mem' := fun {a} ha i => by
    have := ha (a⁻¹ i)
    rw [perm_apply_inv_self] at this
    exact this.symm

theorem mem_stabFun {f : Fin n → ZMod 2} {a : Equiv.Perm (Fin n)} :
    a ∈ stabFun f ↔ ∀ i, f (a i) = f i := Iff.rfl

theorem mem_fixV_map_closure_iff {T : Set (Equiv.Perm (Fin n))} {v : ↥(coreMod n)} :
    v ∈ fixV ((Subgroup.closure T).map (coreAct n)) ↔
      ∀ t ∈ T, ∀ i, vcoord v (t i) = vcoord v i := by
  rw [mem_fixV_map_iff]
  constructor
  · intro h t ht i
    exact h t (Subgroup.subset_closure ht) i
  · intro h a ha i
    have hle : Subgroup.closure T ≤ stabFun (vcoord v) :=
      (Subgroup.closure_le _).2 fun t ht i => h t ht i
    exact hle ha i

theorem mem_fixV_map_zpowers_iff {t : Equiv.Perm (Fin n)} {v : ↥(coreMod n)} :
    v ∈ fixV ((Subgroup.zpowers t).map (coreAct n)) ↔ ∀ i, vcoord v (t i) = vcoord v i := by
  rw [Subgroup.zpowers_eq_closure, mem_fixV_map_closure_iff]
  simp

@[expose] def swapForm (x y : Fin n) : ↥(coreMod n) →* Multiplicative (ZMod 2) where
  toFun v := Multiplicative.ofAdd (vcoord v x + vcoord v y)
  map_one' := by
    show Multiplicative.ofAdd (vcoord (1 : ↥(coreMod n)) x + vcoord (1 : ↥(coreMod n)) y) = 1
    rw [vcoord_one, vcoord_one, add_zero]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (vcoord (a * b) x + vcoord (a * b) y) =
      Multiplicative.ofAdd (vcoord a x + vcoord a y) *
        Multiplicative.ofAdd (vcoord b x + vcoord b y)
    rw [vcoord_mul, vcoord_mul, ← ofAdd_add]
    congr 1
    abel

theorem swapForm_eq_one_iff {x y : Fin n} {v : ↥(coreMod n)} :
    swapForm x y v = 1 ↔ vcoord v x = vcoord v y := by
  show Multiplicative.ofAdd (vcoord v x + vcoord v y) = 1 ↔ _
  rw [ofAdd_eq_one, CharTwo.add_eq_zero]

theorem index_le_two_of_form {V : Type*} [CommGroup V] [Finite V] (S : Subgroup V)
    (φ : V →* Multiplicative (ZMod 2)) (h : ∀ v, v ∈ S ↔ φ v = 1) : S.index ≤ 2 := by
  have hS : S = φ.ker := Subgroup.ext fun v => (h v).trans MonoidHom.mem_ker.symm
  rw [hS, Subgroup.index_ker]
  calc Nat.card φ.range ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
    _ = 2 := (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)

theorem index_fixV_swap_le_two {t : Equiv.Perm (Fin n)} (ht : t.IsSwap) :
    (fixV ((Subgroup.zpowers t).map (coreAct n))).index ≤ 2 := by
  obtain ⟨x, y, hxy, rfl⟩ := ht
  refine index_le_two_of_form _ (swapForm x y) fun v => ?_
  refine mem_fixV_map_zpowers_iff.trans (Iff.trans ?_ swapForm_eq_one_iff.symm)
  constructor
  · intro h
    have := h x
    rw [Equiv.swap_apply_left] at this
    exact this.symm
  · intro h i
    by_cases hix : i = x
    · rw [hix, Equiv.swap_apply_left, h]
    · by_cases hiy : i = y
      · rw [hiy, Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hix hiy]

theorem fixV_map_closure_eq_iInf (T : Set (Equiv.Perm (Fin n))) :
    fixV ((Subgroup.closure T).map (coreAct n)) =
      ⨅ t : T, fixV ((Subgroup.zpowers (t : Equiv.Perm (Fin n))).map (coreAct n)) := by
  ext v
  rw [Subgroup.mem_iInf, mem_fixV_map_closure_iff]
  constructor
  · intro h t
    rw [mem_fixV_map_zpowers_iff]
    exact h t t.2
  · intro h t ht
    exact mem_fixV_map_zpowers_iff.1 (h ⟨t, ht⟩)

theorem card_le_two_pow_mul_card_fixV (T : Set (Equiv.Perm (Fin n)))
    (hT : ∀ t ∈ T, t.IsSwap) :
    Nat.card (coreMod n) ≤
      2 ^ Nat.card T * Nat.card (fixV ((Subgroup.closure T).map (coreAct n))) := by
  have : Fintype T := Fintype.ofFinite T
  have h1 := B1.card_eq_index_mul ((Subgroup.closure T).map (coreAct n))
  have h2 : (fixV ((Subgroup.closure T).map (coreAct n))).index ≤ 2 ^ Nat.card T := by
    rw [fixV_map_closure_eq_iInf]
    calc (⨅ t : T, fixV ((Subgroup.zpowers (t : Equiv.Perm (Fin n))).map (coreAct n))).index
        ≤ ∏ t : T, (fixV ((Subgroup.zpowers (t : Equiv.Perm (Fin n))).map (coreAct n))).index :=
          Subgroup.index_iInf_le _
      _ ≤ ∏ _t : T, 2 :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) fun t _ =>
            index_fixV_swap_le_two (hT t t.2)
      _ = 2 ^ Nat.card T := by
          rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  calc Nat.card (coreMod n)
      = (fixV ((Subgroup.closure T).map (coreAct n))).index *
          Nat.card (fixV ((Subgroup.closure T).map (coreAct n))) := h1
    _ ≤ 2 ^ Nat.card T * Nat.card (fixV ((Subgroup.closure T).map (coreAct n))) :=
        Nat.mul_le_mul_right _ h2

theorem weight_map_le (hn : Odd n) (h3 : 3 ≤ n) {B : Subgroup (Equiv.Perm (Fin n))}
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card (B.map (coreAct n)) * Nat.card (fixV (B.map (coreAct n))) ≤ Nat.card (coreMod n) := by
  have h1 : Nat.card (B.map (coreAct n)) = Nat.card B :=
    Subgroup.card_map_of_injective (coreAct_injective h3)
  rw [h1]
  exact weight_le hn hc

theorem card_le_weight_map_closure (h3 : 3 ≤ n) {T : Set (Equiv.Perm (Fin n))}
    (hT : ∀ t ∈ T, t.IsSwap) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) :
    Nat.card (coreMod n) ≤ Nat.card ((Subgroup.closure T).map (coreAct n)) *
      Nat.card (fixV ((Subgroup.closure T).map (coreAct n))) := by
  have h1 : Nat.card ((Subgroup.closure T).map (coreAct n)) = Nat.card (Subgroup.closure T) :=
    Subgroup.card_map_of_injective (coreAct_injective h3)
  have h2 := two_pow_ncard_le_card_closure (Set.toFinite T) hT hc
  have h4 := card_le_two_pow_mul_card_fixV T hT
  rw [Nat.card_coe_set_eq] at h4
  rw [h1]
  exact h4.trans (Nat.mul_le_mul_right _ h2)

theorem ne_bot_of_mem_ne_one {G : Type*} [Group G] {X : Subgroup G} {a : G} (ha : a ∈ X)
    (h1 : a ≠ 1) : X ≠ ⊥ := fun h => h1 (Subgroup.mem_bot.1 (h ▸ ha))

theorem sym_swaps_offender (n : ℕ) (hn : Odd n) {T : Set (Equiv.Perm (Fin n))}
    (hT : ∀ t ∈ T, t.IsSwap) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) (hne : T.Nonempty) :
    IsFFStarOffender (⊤ : Subgroup (MulAut (coreMod n)))
      ((Subgroup.closure T).map (coreAct n)) := by
  obtain ⟨t₀, ht₀⟩ := hne
  have h3 : 3 ≤ n := by
    obtain ⟨x, y, hxy, -⟩ := hT t₀ ht₀
    have : Nontrivial (Fin n) := ⟨x, y, hxy⟩
    have h2 : 2 ≤ n := Fin.nontrivial_iff_two_le.1 this
    obtain ⟨k, hk⟩ := hn
    omega
  have hinj := coreAct_injective h3
  have hAc : ∀ a ∈ Subgroup.closure T, ∀ b ∈ Subgroup.closure T, a * b = b * a :=
    fun a ha b hb => closure_comm hc ha hb
  refine ⟨le_top, ?_, ⟨?_, ?_⟩, ?_⟩
  · have hne1 : coreAct n t₀ ≠ 1 := fun h => by
      have ht1 : t₀ = 1 := hinj (h.trans (map_one _).symm)
      obtain ⟨x, y, hxy, rfl⟩ := hT t₀ ht₀
      have := congrArg (fun σ : Equiv.Perm (Fin n) => σ x) ht1
      simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at this
      exact hxy this.symm
    exact ne_bot_of_mem_ne_one (Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ht₀)) hne1
  · intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    calc coreAct n a₀ * coreAct n b₀ = coreAct n (a₀ * b₀) := (map_mul _ _ _).symm
      _ = coreAct n (b₀ * a₀) := by rw [hAc a₀ ha₀ b₀ hb₀]
      _ = coreAct n b₀ * coreAct n a₀ := map_mul _ _ _
  · intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    calc coreAct n a₀ ^ 2 = coreAct n (a₀ ^ 2) := (map_pow _ _ _).symm
      _ = coreAct n 1 := by rw [sq_eq_one_of_mem_closure hT hc ha₀]
      _ = 1 := map_one _
  · intro B hB
    have hrange : B ≤ (coreAct n).range := hB.trans (Subgroup.map_le_range _ _)
    obtain ⟨B₀, rfl⟩ : ∃ B₀ : Subgroup (Equiv.Perm (Fin n)), B = B₀.map (coreAct n) :=
      ⟨B.comap (coreAct n), (Subgroup.map_comap_eq_self hrange).symm⟩
    have hB₀ : B₀ ≤ Subgroup.closure T := (Subgroup.map_le_map_iff_of_injective hinj).1 hB
    exact (weight_map_le hn h3 fun a ha b hb => hAc a (hB₀ ha) b (hB₀ hb)).trans
      (card_le_weight_map_closure h3 hT hc)

end CFSG.CGT.PushingUpLit.BHS
