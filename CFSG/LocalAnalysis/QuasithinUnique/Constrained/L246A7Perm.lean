module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

set_option maxRecDepth 100000

namespace CFSG.QuasithinUnique.L246A7

open Equiv
open scoped Pointwise

@[expose] def pact (σ : Perm (Fin 7)) (x : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 := fun i => x (σ⁻¹ i)

theorem pact_one (x : Fin 7 → ZMod 2) : pact 1 x = x := rfl

theorem pact_mul (σ τ : Perm (Fin 7)) (x : Fin 7 → ZMod 2) :
    pact (σ * τ) x = pact σ (pact τ x) := by
  funext i
  simp [pact, mul_inv_rev]

theorem pact_add (σ : Perm (Fin 7)) (x y : Fin 7 → ZMod 2) :
    pact σ (x + y) = pact σ x + pact σ y := by
  funext i
  simp [pact]

theorem pact_mem (σ : Perm (Fin 7)) {x : Fin 7 → ZMod 2}
    (hx : x ∈ CFSG.QuasithinUnique.evenWeight 7) : pact σ x ∈ CFSG.QuasithinUnique.evenWeight 7 := by
  have h : ∑ i, x i = 0 := hx
  show ∑ i, x (σ⁻¹ i) = 0
  rw [Equiv.sum_comp σ⁻¹ x]
  exact h

@[expose] def vact (σ : Perm (Fin 7)) (w : CFSG.QuasithinUnique.evenWeight 7) :
    CFSG.QuasithinUnique.evenWeight 7 :=
  ⟨pact σ w.1, pact_mem σ w.2⟩

theorem vact_one (w : CFSG.QuasithinUnique.evenWeight 7) : vact 1 w = w := rfl

theorem vact_mul (σ τ : Perm (Fin 7)) (w : CFSG.QuasithinUnique.evenWeight 7) :
    vact (σ * τ) w = vact σ (vact τ w) :=
  Subtype.ext (pact_mul σ τ w.1)

theorem vact_add (σ : Perm (Fin 7)) (x y : CFSG.QuasithinUnique.evenWeight 7) :
    vact σ (x + y) = vact σ x + vact σ y :=
  Subtype.ext (pact_add σ x.1 y.1)

theorem vact_zero (σ : Perm (Fin 7)) : vact σ 0 = 0 :=
  Subtype.ext (by funext i; simp [vact, pact])

@[expose] def vactHom (σ : Perm (Fin 7)) :
    CFSG.QuasithinUnique.evenWeight 7 →+ CFSG.QuasithinUnique.evenWeight 7 where
  toFun := vact σ
  map_zero' := vact_zero σ
  map_add' := vact_add σ

theorem vactHom_surjective (σ : Perm (Fin 7)) : Function.Surjective (vactHom σ) := by
  intro w
  refine ⟨vact σ⁻¹ w, ?_⟩
  show vact σ (vact σ⁻¹ w) = w
  rw [← vact_mul, mul_inv_cancel, vact_one]

theorem vactHom_injective (σ : Perm (Fin 7)) : Function.Injective (vactHom σ) := by
  intro w w' h
  have h' : vact σ w = vact σ w' := h
  have := congrArg (vact σ⁻¹) h'
  rwa [← vact_mul, ← vact_mul, inv_mul_cancel, vact_one, vact_one] at this

@[expose] def g1 : Perm (Fin 7) := c[0, 1, 2, 3] * swap 4 5

@[expose] def g2 : Perm (Fin 7) := swap 0 2 * swap 4 5

theorem g1_sign : Perm.sign g1 = 1 := by decide +kernel

theorem g2_sign : Perm.sign g2 = 1 := by decide +kernel

theorem g1_fix6 : g1 6 = 6 := by decide +kernel

theorem g2_fix6 : g2 6 = 6 := by decide +kernel

theorem g1_fix : ∀ x : Fin 7, g1 x = x → x = 6 := by decide +kernel

theorem g1_cyc : ∀ x : Fin 7, x.val < 4 →
    x ≠ g1 x ∧ x ≠ g1 (g1 x) ∧ g1 x ≠ g1 (g1 x) := by decide +kernel

theorem g1_pow_four : g1 ^ 4 = 1 := by decide +kernel

theorem g1_orderOf : orderOf g1 = 4 := by
  apply (orderOf_eq_iff (n := 4) (by norm_num)).mpr
  refine ⟨g1_pow_four, ?_⟩
  intro m hm0 hm4
  interval_cases m <;> decide +kernel

theorem g2_sq : g2 ^ 2 = 1 := by decide +kernel

theorem g2_rel : g2 * g1 * g2⁻¹ = g1⁻¹ := by decide +kernel

theorem g12_ne : g1 * g2 ≠ g2 * g1 := by decide +kernel

@[expose] def Pstd : Subgroup (Perm (Fin 7)) := Subgroup.zpowers g1 ⊔ Subgroup.zpowers g2

theorem g1_mem : g1 ∈ Pstd := Subgroup.mem_sup_left (Subgroup.mem_zpowers g1)

theorem g2_mem : g2 ∈ Pstd := Subgroup.mem_sup_right (Subgroup.mem_zpowers g2)

theorem Pstd_le_alt : Pstd ≤ alternatingGroup (Fin 7) := by
  refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
  · exact Perm.mem_alternatingGroup.2 g1_sign
  · exact Perm.mem_alternatingGroup.2 g2_sign

@[expose] def S6 : Subgroup (Perm (Fin 7)) where
  carrier := {σ | σ 6 = 6}
  one_mem' := rfl
  mul_mem' := fun {a b} ha hb => by
    have ha' : a 6 = 6 := ha
    have hb' : b 6 = 6 := hb
    show a (b 6) = 6
    rw [hb', ha']
  inv_mem' := fun {a} ha => by
    have : a⁻¹ 6 = a⁻¹ (a 6) := by rw [ha]
    simpa using this

@[expose] def S45 : Subgroup (Perm (Fin 7)) where
  carrier := {σ | (σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4)}
  one_mem' := Or.inl ⟨rfl, rfl⟩
  mul_mem' := by
    rintro a b (⟨h1, h2⟩ | ⟨h1, h2⟩) (⟨h3, h4⟩ | ⟨h3, h4⟩) <;> simp [Perm.mul_apply, h1, h2, h3, h4]
  inv_mem' := by
    rintro a (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      constructor
      · have : a⁻¹ 4 = a⁻¹ (a 4) := by rw [h1]
        simpa using this
      · have : a⁻¹ 5 = a⁻¹ (a 5) := by rw [h2]
        simpa using this
    · right
      constructor
      · have : a⁻¹ 4 = a⁻¹ (a 5) := by rw [h2]
        simpa using this
      · have : a⁻¹ 5 = a⁻¹ (a 4) := by rw [h1]
        simpa using this

theorem Pstd_le_S6 : Pstd ≤ S6 := by
  refine sup_le (Subgroup.zpowers_le.2 g1_fix6) (Subgroup.zpowers_le.2 g2_fix6)

theorem Pstd_le_S45 : Pstd ≤ S45 := by
  refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
  · exact Or.inr ⟨by decide +kernel, by decide +kernel⟩
  · exact Or.inr ⟨by decide +kernel, by decide +kernel⟩

theorem card_Pstd : Nat.card Pstd = 8 := by
  let ρ' : Pstd := ⟨g1, g1_mem⟩
  let σ' : Pstd := ⟨g2, g2_mem⟩
  have hgen : ⊤ = Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ' := by
    have hmap : Subgroup.map Pstd.subtype ⊤ =
        Subgroup.map Pstd.subtype (Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ') := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    exact (Subgroup.map_injective (f := Pstd.subtype) Subtype.coe_injective) hmap
  have hσ2 : σ' ^ 2 = 1 := by
    apply Subtype.ext
    simpa [σ'] using g2_sq
  have hrel : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := by
    apply Subtype.ext
    simpa [σ', ρ'] using g2_rel
  have hord : orderOf ρ' = 4 := by
    rw [← Subgroup.orderOf_coe ρ']
    exact g1_orderOf
  rcases CFSG.GorensteinWalter.isCyclic_or_dihedral_of_generators ρ' σ' hgen hσ2 hrel with
    hcyc | hdih
  · exfalso
    have hcomm : ρ' * σ' = σ' * ρ' := IsMulCommutative.is_comm.comm ρ' σ'
    have hc : g1 * g2 = g2 * g1 := congrArg (fun x : Pstd => (x : Perm (Fin 7))) hcomm
    exact g12_ne hc
  · obtain ⟨e⟩ := hdih
    rw [hord] at e
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem Pstd_fix6 {a : Perm (Fin 7)} (ha : a ∈ Pstd) : a 6 = 6 := Pstd_le_S6 ha

theorem normalizer_Pstd {τ : Perm (Fin 7)} (h' : ∀ a ∈ Pstd, τ⁻¹ * a * τ ∈ Pstd) :
    τ 6 = 6 ∧ ((τ 4 = 4 ∧ τ 5 = 5) ∨ (τ 4 = 5 ∧ τ 5 = 4)) := by
  have h6 : τ 6 = 6 := by
    apply g1_fix
    have hb : (τ⁻¹ * g1 * τ) 6 = 6 := Pstd_fix6 (h' g1 g1_mem)
    have h2 : τ⁻¹ (g1 (τ 6)) = 6 := hb
    have h3 := congrArg τ h2
    simpa using h3
  have horb : ∀ g ∈ Pstd, ∀ y : Fin 7, (y = 4 ∨ y = 5) → g (τ y) = τ 4 ∨ g (τ y) = τ 5 := by
    intro g hg y hy
    have hb := Pstd_le_S45 (h' g hg)
    have hgy : g (τ y) = τ ((τ⁻¹ * g * τ) y) := by simp [Perm.mul_apply]
    rw [hgy]
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with rfl | rfl <;> simp [h1, h2]
  have key : ∀ y : Fin 7, (y = 4 ∨ y = 5) → τ y = 4 ∨ τ y = 5 := by
    intro y hy
    by_contra hcon
    push Not at hcon
    obtain ⟨hc4, hc5⟩ := hcon
    have hy6 : τ y ≠ 6 := by
      intro h
      have : τ y = τ 6 := by rw [h, h6]
      rcases hy with rfl | rfl <;> exact absurd (τ.injective this) (by decide)
    have hlt : (τ y).val < 4 := by
      have h7 := (τ y).isLt
      have h46 : (τ y).val ≠ 4 := fun h => hc4 (Fin.ext h)
      have h56 : (τ y).val ≠ 5 := fun h => hc5 (Fin.ext h)
      have h66 : (τ y).val ≠ 6 := fun h => hy6 (Fin.ext h)
      omega
    obtain ⟨d1, d2, d3⟩ := g1_cyc (τ y) hlt
    have m0 := horb 1 (Subgroup.one_mem _) y hy
    have m1 := horb g1 g1_mem y hy
    have m2 := horb (g1 * g1) (Subgroup.mul_mem _ g1_mem g1_mem) y hy
    simp only [Perm.mul_apply, Perm.coe_one, id_eq] at m0 m1 m2
    rcases m0 with h0 | h0 <;> rcases m1 with h1 | h1 <;> rcases m2 with h2 | h2 <;>
      first
      | exact d1 (h0.trans h1.symm)
      | exact d2 (h0.trans h2.symm)
      | exact d3 (h1.trans h2.symm)
  have k4 := key 4 (Or.inl rfl)
  have k5 := key 5 (Or.inr rfl)
  refine ⟨h6, ?_⟩
  rcases k4 with h4 | h4 <;> rcases k5 with h5 | h5
  · exact absurd (τ.injective (h4.trans h5.symm)) (by decide)
  · exact Or.inl ⟨h4, h5⟩
  · exact Or.inr ⟨h4, h5⟩
  · exact absurd (τ.injective (h4.trans h5.symm)) (by decide)

@[expose] def cc : Perm (Fin 7) := c[4, 5, 6]

theorem cc_sign : Perm.sign cc = 1 := by decide +kernel

theorem cc_pow_three : cc ^ 3 = 1 := by decide +kernel

theorem cc_apply6 : cc 6 = 4 := by decide +kernel

theorem cc_ne_one : cc ≠ 1 := by decide +kernel

theorem cc_mem_alt : cc ∈ alternatingGroup (Fin 7) := Perm.mem_alternatingGroup.2 cc_sign

theorem cc_fix_of_lt : ∀ i : Fin 7, i.val < 4 → cc i = i := by decide +kernel

theorem conj_cc_of_pres : ∀ τ : Perm (Fin 7), τ 6 = 6 →
    ((τ 4 = 4 ∧ τ 5 = 5) ∨ (τ 4 = 5 ∧ τ 5 = 4)) →
      τ * cc * τ⁻¹ = cc ∨ τ * cc * τ⁻¹ = cc⁻¹ := by decide +kernel

@[expose] def ccA : alternatingGroup (Fin 7) := ⟨cc, cc_mem_alt⟩

@[expose] def S6A : Subgroup (alternatingGroup (Fin 7)) :=
  S6.subgroupOf (alternatingGroup (Fin 7))

theorem mem_S6A {a : alternatingGroup (Fin 7)} : a ∈ S6A ↔ (a : Perm (Fin 7)) 6 = 6 := Iff.rfl

theorem S6A_sup_zpowers_ccA : S6A ⊔ Subgroup.zpowers ccA = ⊤ := by
  have hcoatom : IsCoatom (MulAction.stabilizer (alternatingGroup (Fin 7)) ({6} : Set (Fin 7))) :=
    alternatingGroup.isCoatom_stabilizer_singleton (α := Fin 7) (by simp [Nat.card_eq_fintype_card])
      (Set.singleton_nonempty 6) Set.subsingleton_singleton
  rw [MulAction.stabilizer_singleton] at hcoatom
  have hS : MulAction.stabilizer (alternatingGroup (Fin 7)) (6 : Fin 7) = S6A := by
    ext a
    rw [MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  rw [hS] at hcoatom
  by_contra hne
  have hlt : S6A < S6A ⊔ Subgroup.zpowers ccA := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    have hmem : ccA ∈ S6A := h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers ccA)
    have : cc 6 = 6 := hmem
    rw [cc_apply6] at this
    exact absurd this (by decide)
  exact hne (hcoatom.2 _ hlt)

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_PstdA : Nat.card (Pstd.subgroupOf (alternatingGroup (Fin 7))) = 8 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Pstd_le_alt).toEquiv]
  exact card_Pstd

@[expose] noncomputable def PstdSylow : Sylow 2 (alternatingGroup (Fin 7)) :=
  have hp : IsPGroup 2 (Pstd.subgroupOf (alternatingGroup (Fin 7))) :=
    IsPGroup.of_card (p := 2) (n := 3) (by rw [card_PstdA]; norm_num)
  hp.toSylow (by
    have h := Subgroup.index_mul_card (Pstd.subgroupOf (alternatingGroup (Fin 7)))
    rw [card_PstdA, card_alt7] at h
    have : (Pstd.subgroupOf (alternatingGroup (Fin 7))).index = 315 := by omega
    rw [this]
    decide)

theorem exists_conj_Pstd (P : Sylow 2 (alternatingGroup (Fin 7))) :
    ∃ σ : alternatingGroup (Fin 7),
      (P : Subgroup (alternatingGroup (Fin 7))).map (MulAut.conj σ).toMonoidHom =
        Pstd.subgroupOf (alternatingGroup (Fin 7)) := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) P PstdSylow
  refine ⟨σ, ?_⟩
  have h := congrArg (fun Q : Sylow 2 (alternatingGroup (Fin 7)) =>
    (Q : Subgroup (alternatingGroup (Fin 7)))) hσ
  simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, PstdSylow] at h
  exact h

@[expose] def pts6 : Finset (Fin 7) := Finset.univ.erase 6

theorem card_pts6 : Fintype.card ↥pts6 = 6 := by
  rw [Fintype.card_coe]
  simp [pts6]

abbrev T6 : Type := alternatingGroup ↥pts6

theorem isSimpleGroup_T6 : IsSimpleGroup T6 :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, card_pts6]; norm_num)

@[expose] def jA : T6 →* alternatingGroup (Fin 7) := alternatingGroup.ofSubtype pts6

theorem jA_injective : Function.Injective jA := alternatingGroup.ofSubtype_injective

theorem mem_range_jA {a : alternatingGroup (Fin 7)} :
    a ∈ jA.range ↔ (a : Perm (Fin 7)) 6 = 6 := by
  constructor
  · rintro ⟨x, rfl⟩
    show ((alternatingGroup.ofSubtype pts6 x : alternatingGroup (Fin 7)) : Perm (Fin 7)) 6 = 6
    rw [alternatingGroup.coe_ofSubtype]
    exact Perm.ofSubtype_apply_of_not_mem _ (by simp [pts6])
  · intro h6
    have hmem : ∀ i : Fin 7, (a : Perm (Fin 7)) i ∈ pts6 ↔ i ∈ pts6 := by
      intro i
      simp only [pts6, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hi hi'
        apply hi
        rw [hi', h6]
      · intro hi hi'
        apply hi
        apply (a : Perm (Fin 7)).injective
        rw [hi', h6]
    have hsupp : ∀ x, (a : Perm (Fin 7)) x ≠ x → x ∈ pts6 := by
      intro x hx
      simp only [pts6, Finset.mem_erase, Finset.mem_univ, and_true]
      intro hx6
      apply hx
      rw [hx6, h6]
    let f : Perm ↥pts6 := (a : Perm (Fin 7)).subtypePerm hmem
    have hf : Perm.ofSubtype f = (a : Perm (Fin 7)) := Perm.ofSubtype_subtypePerm hmem hsupp
    have hfs : f ∈ alternatingGroup ↥pts6 := by
      rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype, hf]
      exact Perm.mem_alternatingGroup.1 a.2
    refine ⟨⟨f, hfs⟩, ?_⟩
    apply Subtype.ext
    show ((alternatingGroup.ofSubtype pts6 ⟨f, hfs⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) = _
    rw [alternatingGroup.coe_ofSubtype]
    exact hf

theorem isSimpleGroup_range_jA : IsSimpleGroup ↥jA.range := by
  have := isSimpleGroup_T6
  exact (MonoidHom.ofInjective jA_injective).symm.isSimpleGroup

@[expose] def ChiOrder (t : ℕ) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ t = 2 ^ n * (4 ^ n - 1)) ∨ ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ t = m.factorial / 2

theorem not_chiOrder_360 : ¬ ChiOrder 360 := by
  rintro (⟨n, hn, h⟩ | ⟨m, hm, hm3, h⟩)
  · by_cases hn2 : n = 2
    · subst hn2
      norm_num at h
    · have hn3 : 3 ≤ n := by omega
      have h1 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      have h2 : 4 ^ 3 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      have h3 : 63 ≤ 4 ^ n - 1 := by omega
      have h4 : 8 * 63 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul (by omega) h3
      omega
  · by_cases hm7 : 7 ≤ m
    · have h1 : Nat.factorial 7 ≤ Nat.factorial m := Nat.factorial_le hm7
      have h2 : (5040 : ℕ) ≤ Nat.factorial m := by simpa [Nat.factorial] using h1
      omega
    · push Not at hm7
      obtain ⟨k, rfl⟩ := hm
      have hk : k < 3 := by omega
      interval_cases k
      · omega
      · simp [Nat.factorial] at h
      · simp [Nat.factorial] at h

theorem mem_evenWeight_iff (x : Fin 7 → ZMod 2) :
    x ∈ CFSG.QuasithinUnique.evenWeight 7 ↔ ∑ i, x i = 0 := Iff.rfl

theorem support_of_norm {x : Fin 7 → ZMod 2} (h : x + pact cc x + pact (cc * cc) x = 0) :
    ∀ i : Fin 7, i.val < 4 → x i = 0 := by
  intro i hi
  have hcc : cc⁻¹ i = i := by
    rw [Perm.inv_eq_iff_eq]
    exact (cc_fix_of_lt i hi).symm
  have h1 := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply, pact, mul_inv_rev, Perm.mul_apply, hcc] at h1
  have h2 : x i + x i + x i = x i := by
    have : (2 : ZMod 2) = 0 := by decide
    calc x i + x i + x i = 2 * x i + x i := by ring
      _ = x i := by rw [this]; ring
  rw [h2] at h1
  exact h1

theorem eq_of_support {x x' : Fin 7 → ZMod 2} (hx : ∑ i, x i = 0) (hx' : ∑ i, x' i = 0)
    (h0 : ∀ i : Fin 7, i.val < 4 → x i = 0) (h0' : ∀ i : Fin 7, i.val < 4 → x' i = 0)
    (h4 : x 4 = x' 4) (h5 : x 5 = x' 5) : x = x' := by
  have h6 : x 6 = x' 6 := by
    have e : ∀ z : Fin 7 → ZMod 2, (∀ i : Fin 7, i.val < 4 → z i = 0) → ∑ i, z i = 0 →
        z 6 = z 4 + z 5 := by
      intro z hz hs
      rw [Fin.sum_univ_seven] at hs
      have e0 := hz 0 (by decide)
      have e1 := hz 1 (by decide)
      have e2 := hz 2 (by decide)
      have e3 := hz 3 (by decide)
      rw [e0, e1, e2, e3] at hs
      have key : ∀ a b c : ZMod 2, 0 + 0 + 0 + 0 + a + b + c = 0 → c = a + b := by decide
      exact key _ _ _ hs
    rw [e x h0 hx, e x' h0' hx', h4, h5]
  funext i
  fin_cases i
  · exact (h0 0 (by decide)).trans (h0' 0 (by decide)).symm
  · exact (h0 1 (by decide)).trans (h0' 1 (by decide)).symm
  · exact (h0 2 (by decide)).trans (h0' 2 (by decide)).symm
  · exact (h0 3 (by decide)).trans (h0' 3 (by decide)).symm
  · exact h4
  · exact h5
  · exact h6

@[expose] def w0 : Fin 7 → ZMod 2 := ![1, 0, 0, 0, 1, 1, 1]

theorem w0_mem : w0 ∈ CFSG.QuasithinUnique.evenWeight 7 := by
  rw [mem_evenWeight_iff]
  decide +kernel

theorem w0_twice_ne :
    ((w0 + pact g1 w0) + pact g1 (w0 + pact g1 w0)) 0 ≠ 0 := by decide +kernel

end CFSG.QuasithinUnique.L246A7
