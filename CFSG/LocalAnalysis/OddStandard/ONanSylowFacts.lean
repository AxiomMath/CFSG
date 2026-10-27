module

public import CFSG.LocalAnalysis.OddStandard.ONanSylowPres
public import CFSG.LocalAnalysis.OddStandard.ONanSylowTools
public import Certificates.Data.ONanF2Facts
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE

theorem f2Check_parts (h : f2Check = true) :
    factCentre ∧ factClasses ∧ factNonV ∧ factSub ∧ factMax ∧ factQR ∧ factCent ∧ factDerived ∧
      factOrders ∧ factCV ∧ factW := by
  simp only [f2Check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Model

theorem mem_center_of_gens {x : AlpE} (hx : ∀ i : Fin 5, gen i * x = x * gen i) :
    x ∈ Subgroup.center AlpE := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure (Set.range gen) := by
    rw [closure_range_gen]
    exact Subgroup.mem_top g
  have hle : Subgroup.closure (Set.range gen) ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hx i
  have := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  exact this

theorem mem_center_iff_E (h : f2Check = true) (x : AlpE) :
    x ∈ Subgroup.center AlpE ↔ x = 1 ∨ x = zc := by
  obtain ⟨⟨hz, hc⟩, -⟩ := f2Check_parts h
  constructor
  · intro hx
    refine hc x fun i => ?_
    exact (Subgroup.mem_center_iff.1 hx (gen i))
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact mem_center_of_gens hz

theorem mem_allE (x : AlpE) : x ∈ allE := by
  obtain ⟨d, a, b, c⟩ := x
  refine List.mem_flatMap.2 ⟨d, List.mem_finRange d, ?_⟩
  refine List.mem_flatMap.2 ⟨a, List.mem_finRange a, ?_⟩
  refine List.mem_flatMap.2 ⟨b, List.mem_finRange b, ?_⟩
  exact List.mem_map.2 ⟨c, List.mem_finRange c, rfl⟩

theorem closure_genE : Subgroup.closure {g | g ∈ genE} = ⊤ := by
  have : {g | g ∈ genE} = Set.range gen := by
    ext g
    simp only [genE, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [this, closure_range_gen]

theorem invEL_getD (i : Fin 7) : invEL.getD i 1 = invE i := by
  fin_cases i <;> simp [invEL]

theorem exists_conj_invE (h : f2Check = true) {u : AlpE} (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ i : Fin 7, ∃ c : AlpE, c⁻¹ * invE i * c = u := by
  obtain ⟨-, ⟨-, hcov, hcl, -, -, -⟩, -⟩ := f2Check_parts h
  have hmem : u ∈ allInvs := by
    simp only [allInvs, List.mem_filter, decide_eq_true_eq]
    exact ⟨mem_allE u, hu, hu1⟩
  obtain ⟨i, hi⟩ := hcov u hmem
  obtain ⟨c, -, hc⟩ := (ClassOK.mem_iff (hcl i) u).1 hi
  exact ⟨i, c, hc⟩

theorem conj_invE_eq (h : f2Check = true) {i j : Fin 7} {c : AlpE}
    (hc : c⁻¹ * invE i * c = invE j) : i = j := by
  obtain ⟨-, ⟨-, -, hcl, hpw, -, -⟩, -⟩ := f2Check_parts h
  by_contra hij
  apply hpw i j hij (invE j)
  · exact (ClassOK.mem_iff (hcl i) (invE j)).2 ⟨c, by rw [closure_genE]; exact mem_top c, hc⟩
  · exact (ClassOK.mem_iff (hcl j) (invE j)).2 ⟨1, one_mem _, by simp⟩

theorem invE_sq (h : f2Check = true) (i : Fin 7) : invE i * invE i = 1 ∧ invE i ≠ 1 :=
  (f2Check_parts h).2.1.1 i

theorem card_centralizer_invE (h : f2Check = true) (i : Fin 7) :
    Nat.card (Subgroup.centralizer ({invE i} : Set AlpE)) = ![512, 256, 128, 32, 16, 32, 32] i := by
  obtain ⟨-, ⟨-, -, -, -, -, hcent⟩, -⟩ := f2Check_parts h
  have h1 := hcent i
  rw [invEL_getD] at h1
  have e : Subgroup.centralizer ({invE i} : Set AlpE) ≃ {g : AlpE // g * invE i = invE i * g} :=
    Equiv.subtypeEquivRight fun g => by
      rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h1

theorem mul_d (x y : AlpE) : (x * y).d = dmul x.d y.d := rfl

theorem inv_d (x : AlpE) : (x⁻¹).d = dinv x.d := rfl

@[expose] def Vsub : Subgroup AlpE where
  carrier := {x | x.d = 0}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [mul_d, hx, hy]
    rfl
  one_mem' := rfl
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [inv_d, hx]
    rfl

theorem mem_Vsub {x : AlpE} : x ∈ Vsub ↔ x.d = 0 := Iff.rfl

theorem closure_genVE : Subgroup.closure {g | g ∈ genVE} = Vsub := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [genVE, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> exact rfl
  · intro x hx
    have hg : ∀ g ∈ genVE, g ∈ Subgroup.closure {g | g ∈ genVE} := fun g hg =>
      Subgroup.subset_closure hg
    have h0 : gen 0 ∈ Subgroup.closure {g | g ∈ genVE} := hg _ (by simp [genVE])
    have h1 : gen 1 ∈ Subgroup.closure {g | g ∈ genVE} := hg _ (by simp [genVE])
    have h2 : gen 2 ∈ Subgroup.closure {g | g ∈ genVE} := hg _ (by simp [genVE])
    obtain ⟨d, a, b, c⟩ := x
    have hd : d = 0 := hx
    subst hd
    rw [tr_eq]
    exact mul_mem (mul_mem (pow_mem h0 _) (pow_mem h1 _)) (pow_mem h2 _)

theorem card_Vsub : Nat.card Vsub = 64 := by
  have e : Vsub ≃ ZMod 4 × ZMod 4 × ZMod 4 :=
    { toFun := fun x => (x.1.v0, x.1.v1, x.1.v2)
      invFun := fun p => ⟨⟨0, p.1, p.2.1, p.2.2⟩, rfl⟩
      left_inv := fun x => by
        obtain ⟨⟨d, a, b, c⟩, hx⟩ := x
        have hd : d = 0 := hx
        subst hd
        rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e]
  simp [ZMod.card]

instance : Vsub.Normal := ⟨fun x hx g => by
  show (g * x * g⁻¹).d = 0
  have hx' : x.d = 0 := hx
  rw [mul_d, mul_d, inv_d, hx']
  revert g
  decide +kernel⟩

theorem card_centralizer_le (h : f2Check = true) {x : AlpE} (hx : x.d ≠ 0) :
    Nat.card (Subgroup.centralizer ({x} : Set AlpE)) ≤ 32 := by
  obtain ⟨-, -, hnv, -⟩ := f2Check_parts h
  have h1 := hnv x hx
  have e : Subgroup.centralizer ({x} : Set AlpE) ≃ {g : AlpE // g * x = x * g} :=
    Equiv.subtypeEquivRight fun g => by
      rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h1

theorem abelian_le_Vsub (h : f2Check = true) {H : Subgroup AlpE}
    (hab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hcard : 32 < Nat.card H) : H ≤ Vsub := by
  intro x hx
  by_contra hxV
  have hd : x.d ≠ 0 := hxV
  have hle : H ≤ Subgroup.centralizer ({x} : Set AlpE) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hab y hy x hx
  have := Subgroup.card_le_of_le hle
  have := card_centralizer_le h hd
  omega

noncomputable def equivVsub : Vsub ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) :=
  { toFun := fun x => Multiplicative.ofAdd (x.1.v0, x.1.v1, x.1.v2)
    invFun := fun p => ⟨⟨0, (Multiplicative.toAdd p).1, (Multiplicative.toAdd p).2.1,
      (Multiplicative.toAdd p).2.2⟩, rfl⟩
    left_inv := fun x => by
      obtain ⟨⟨d, a, b, c⟩, hx⟩ := x
      have hd : d = 0 := hx
      subst hd
      rfl
    right_inv := fun p => rfl
    map_mul' := fun x y => by
      obtain ⟨⟨d, a, b, c⟩, hx⟩ := x
      obtain ⟨⟨d', a', b', c'⟩, hy⟩ := y
      have hd : d = 0 := hx
      have hd' : d' = 0 := hy
      subst hd hd'
      have hm : ∀ i : Fin 3, act 0 i ⟨0, a', b', c'⟩ = ![a', b', c'] i := by
        intro i
        fin_cases i <;> simp [act, me_zero]
      show Multiplicative.ofAdd (a + act 0 0 ⟨0, a', b', c'⟩ + ck 0 0,
        b + act 0 1 ⟨0, a', b', c'⟩, c + act 0 2 ⟨0, a', b', c'⟩ + ck 0 0) = _
      rw [hm 0, hm 1, hm 2, ck_zero_left]
      show _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
      rw [← ofAdd_add]
      congr 1
      simp }

abbrev subE (gens : List AlpE) : Subgroup AlpE := Subgroup.closure {g | g ∈ gens}

theorem sub_facts (h : f2Check = true) :
    SubOK genV0E ballV0 32 ∧ SubOK genPdE ballPd 64 ∧ SubOK genCommE ballComm 64 ∧
    SubOK genVE ballV 64 ∧ SubOK genWE ballW 8 ∧ SubOK genVtE ballVt 128 ∧
    SubOK genQE ballQ 32 ∧ SubOK genRE ballR 16 ∧
    (∀ i : Fin 7, SubOK (genMaxE i) (ballMaxL.getD i []) 256) ∧
    (∀ i : Fin 3, SubOK (genCentE i) (ballCentL.getD i []) 32) :=
  (f2Check_parts h).2.2.2.1

theorem card_subE_W (h : f2Check = true) : Nat.card (subE genWE) = 8 :=
  SubOK.card_closure (sub_facts h).2.2.2.2.1

theorem card_subE_Q (h : f2Check = true) : Nat.card (subE genQE) = 32 :=
  SubOK.card_closure (sub_facts h).2.2.2.2.2.2.1

theorem card_subE_R (h : f2Check = true) : Nat.card (subE genRE) = 16 :=
  SubOK.card_closure (sub_facts h).2.2.2.2.2.2.2.1

theorem card_subE_max (h : f2Check = true) (i : Fin 7) : Nat.card (subE (genMaxE i)) = 256 :=
  SubOK.card_closure ((sub_facts h).2.2.2.2.2.2.2.2.1 i)

theorem mem_subE_max_iff (h : f2Check = true) (i : Fin 7) (x : AlpE) :
    x ∈ subE (genMaxE i) ↔ x ∈ ballMaxL.getD i [] :=
  SubOK.mem_closure_iff ((sub_facts h).2.2.2.2.2.2.2.2.1 i) x

theorem mem_subE_cent_iff (h : f2Check = true) (i : Fin 3) (x : AlpE) :
    x ∈ subE (genCentE i) ↔ x ∈ ballCentL.getD i [] :=
  SubOK.mem_closure_iff ((sub_facts h).2.2.2.2.2.2.2.2.2 i) x

theorem mem_class_iff (h : f2Check = true) (j : Fin 7) (x : AlpE) :
    x ∈ classLists.getD j [] ↔ ∃ c : AlpE, c⁻¹ * invE j * c = x := by
  obtain ⟨-, ⟨-, -, hcl, -, -, -⟩, -⟩ := f2Check_parts h
  rw [ClassOK.mem_iff (hcl j) x]
  constructor
  · rintro ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [closure_genE]; exact mem_top c, hc⟩

theorem max_table (h : f2Check = true) (i j : Fin 7) :
    (∃ u ∈ subE (genMaxE i), ∃ c : AlpE, c⁻¹ * invE j * c = u) ↔ maxTable i j = true := by
  obtain ⟨-, -, -, -, hmax, -⟩ := f2Check_parts h
  rw [← hmax i j]
  constructor
  · rintro ⟨u, hu, hc⟩
    exact ⟨u, (mem_subE_max_iff h i u).1 hu, (mem_class_iff h j u).2 hc⟩
  · rintro ⟨u, hu, hc⟩
    exact ⟨u, (mem_subE_max_iff h i u).2 hu, (mem_class_iff h j u).1 hc⟩

theorem mem_subE_Q_iff (h : f2Check = true) (x : AlpE) : x ∈ subE genQE ↔ x ∈ ballQ :=
  SubOK.mem_closure_iff (sub_facts h).2.2.2.2.2.2.1 x

theorem mem_subE_R_iff (h : f2Check = true) (x : AlpE) : x ∈ subE genRE ↔ x ∈ ballR :=
  SubOK.mem_closure_iff (sub_facts h).2.2.2.2.2.2.2.1 x

theorem involutions_Q (h' : f2Check = true) {u : AlpE} (hu : u ∈ subE genQE) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) :
    (∃ c : AlpE, c⁻¹ * invE 1 * c = u) ∨ (∃ c : AlpE, c⁻¹ * invE 2 * c = u) ∨
      (∃ c : AlpE, c⁻¹ * invE 4 * c = u) := by
  obtain ⟨-, -, -, -, -, ⟨-, -, h3, -⟩, -⟩ := f2Check_parts h'
  rcases h3 u ((mem_subE_Q_iff h' u).1 hu) hu2 hu1 with h | h | h
  · exact Or.inl ((mem_class_iff h' 1 u).1 h)
  · exact Or.inr (Or.inl ((mem_class_iff h' 2 u).1 h))
  · exact Or.inr (Or.inr ((mem_class_iff h' 4 u).1 h))

theorem involution_R (h : f2Check = true) {x : AlpE} (hx : x ∈ subE genRE) (hx2 : x * x = 1) :
    x = 1 ∨ x = zc := by
  obtain ⟨-, -, -, -, -, ⟨-, -, -, h4⟩, -⟩ := f2Check_parts h
  exact h4 x ((mem_subE_R_iff h x).1 hx) hx2

theorem centralizer_invE_eq (h : f2Check = true) (i : Fin 3) :
    Subgroup.centralizer ({invE (![3, 5, 6] i)} : Set AlpE) = subE (genCentE i) := by
  obtain ⟨-, -, -, -, -, -, ⟨h1, -, -, -, -⟩, -⟩ := f2Check_parts h
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, mem_subE_cent_iff h i g, ← h1 i g]

theorem card_list_filter {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup) (p : α → Prop)
    [DecidablePred p] :
    Nat.card {x : α // x ∈ L ∧ p x} = (L.filter fun x => decide (p x)).length := by
  have e : {x : α // x ∈ L ∧ p x} ≃ {x : α // x ∈ (L.filter fun x => decide (p x)).toFinset} :=
    Equiv.subtypeEquivRight fun x => by simp
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (hL.filter _)]

theorem card_involutions_cent (h : f2Check = true) (i : Fin 3) (j : Fin 7) :
    Nat.card {u : AlpE // u ∈ subE (genCentE i) ∧ u * u = 1 ∧ u ≠ 1 ∧
      ∃ c : AlpE, c⁻¹ * invE j * c = u} = centCount i j := by
  obtain ⟨-, -, -, -, -, -, ⟨-, h2, -, -, -⟩, -⟩ := f2Check_parts h
  have hnd := ((sub_facts h).2.2.2.2.2.2.2.2.2 i).2.2.1
  have h3 := h2 i j
  rw [← h3, ← card_list_filter _ hnd]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
  simp only [mem_subE_cent_iff h i u, mem_class_iff h j u]

theorem centralizer_special (h : f2Check = true) :
    Subgroup.centralizer ({gen 1 ^ 2} : Set AlpE) = subE genVtE ∧
    Subgroup.centralizer ({gen 0 * gen 2} : Set AlpE) = subE (genMaxE 0) ∧
    Subgroup.centralizer ({xE} : Set AlpE) = subE (genMaxE 1) := by
  obtain ⟨-, -, -, -, -, -, ⟨-, -, h3, h4, h5⟩, -⟩ := f2Check_parts h
  refine ⟨?_, ?_, ?_⟩
  · ext g
    rw [Subgroup.mem_centralizer_singleton_iff,
      SubOK.mem_closure_iff (sub_facts h).2.2.2.2.2.1 g, ← h3 g]
  · ext g
    have e : g ∈ subE (genMaxE 0) ↔ g ∈ ballMaxL.getD 0 [] := mem_subE_max_iff h 0 g
    rw [Subgroup.mem_centralizer_singleton_iff, e, ← h4 g]
  · ext g
    have e : g ∈ subE (genMaxE 1) ↔ g ∈ ballMaxL.getD 1 [] := mem_subE_max_iff h 1 g
    rw [Subgroup.mem_centralizer_singleton_iff, e, ← h5 g]

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

instance : Fact (IsPGroup 2 AlpE) := ⟨isPGroup⟩

instance : Finite AlpE := Finite.of_fintype AlpE

theorem pow_four_of_mem_V (h : f2Check = true) {x : AlpE} (hx : x.d = 0) : x ^ 4 = 1 :=
  (f2Check_parts h).2.2.2.2.2.2.2.2.1.1 x hx

theorem orderOf_of_d_odd (h : f2Check = true) {x : AlpE} (hx : x.d = 1 ∨ x.d = 3) :
    orderOf x = 16 := by
  obtain ⟨h1, h2⟩ := (f2Check_parts h).2.2.2.2.2.2.2.2.1.2.1 x hx
  have := orderOf_eq_prime_pow (p := 2) (n := 3) (x := x) (by simpa using h2) (by simpa using h1)
  simpa using this

theorem sq_of_order_four_d246 (h : f2Check = true) {x : AlpE}
    (hx : x.d = 2 ∨ x.d = 4 ∨ x.d = 6) (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) : x ^ 2 = zc :=
  (f2Check_parts h).2.2.2.2.2.2.2.2.1.2.2.2.1 x hx h4 h2

theorem sq_of_order_four_d5 (h : f2Check = true) {x : AlpE} (hx : x.d = 5) (h4 : x ^ 4 = 1)
    (h2 : x ^ 2 ≠ 1) : x ^ 2 = gen 0 ^ 2 * gen 1 ^ 2 :=
  (f2Check_parts h).2.2.2.2.2.2.2.2.1.2.2.2.2.1 x hx h4 h2

theorem sq_of_order_four_d7 (h : f2Check = true) {x : AlpE} (hx : x.d = 7) (h4 : x ^ 4 = 1)
    (h2 : x ^ 2 ≠ 1) : x ^ 2 = gen 1 ^ 2 * gen 2 ^ 2 :=
  (f2Check_parts h).2.2.2.2.2.2.2.2.1.2.2.2.2.2 x hx h4 h2

theorem mem_subE_W_iff (h : f2Check = true) (x : AlpE) : x ∈ subE genWE ↔ x ∈ ballW :=
  SubOK.mem_closure_iff (sub_facts h).2.2.2.2.1 x

theorem W_facts (h : f2Check = true) :
    (∀ x : AlpE, x.d = 0 → (x * x = 1 ↔ x ∈ subE genWE)) ∧
    (∀ g : AlpE, (∀ w ∈ subE genWE, g * w = w * g) ↔ g.d = 0) ∧
    (∀ g : AlpE, (∀ v ∈ Vsub, g * v = v * g) ↔ g.d = 0) ∧
    (∀ g : AlpE, ∀ w ∈ subE genWE, g * w * g⁻¹ ∈ subE genWE) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := f2Check_parts h
  refine ⟨fun x hx => ?_, fun g => ?_, fun g => ?_, fun g w hw => ?_⟩
  · rw [mem_subE_W_iff h]
    exact h1 x hx
  · rw [commute_closure_iff genWE]
    exact h2 g
  · have hc := commute_closure_iff genVE g
    rw [closure_genVE] at hc
    rw [hc]
    exact h3 g
  · rw [mem_subE_W_iff h] at hw ⊢
    exact h4 g w hw

end Model

end CFSG.OddStandard.ONanRec
