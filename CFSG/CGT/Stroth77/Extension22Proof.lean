module

public import CFSG.CGT.Stroth77.Extension22
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

namespace StrothTypeData

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)}

theorem comm_t100 (D : StrothTypeData B (StrothTypeIndex.t100 m)) (x y : B) :
    x * y = y * x := by
  apply Additive.ofMul.injective
  apply D.e.injective
  simp only [ofMul_mul, map_add, add_comm]

theorem card_t100 (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Nat.card B = 2 ^ (3 * m + 2) := by
  have h := D.card
  have h0 : (StrothTypeIndex.t100 m).k 0 = m := rfl
  have h1 : (StrothTypeIndex.t100 m).k 1 = m + 1 := rfl
  have h2 : (StrothTypeIndex.t100 m).k 2 = m + 1 := rfl
  rw [h0, h1, h2] at h
  rw [show m + (m + 1) + (m + 1) = 3 * m + 2 by ring] at h
  exact h

theorem closure_c_a_b (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S) = B := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact D.c.2
    · exact D.a.2
    · exact D.b.2
  · intro x hx
    let xB : B := ⟨x, hx⟩
    let y : Torus (StrothTypeIndex.t100 m).k := D.e (Additive.ofMul xB)
    choose z hz using fun i : Fin 3 => ZMod.intCast_surjective (y i)
    have hc : D.e (Additive.ofMul D.c) = gen (StrothTypeIndex.t100 m).k 0 := by
      simp [StrothTypeData.c, Torus.c, gen, ofMul_toMul]
    have ha : D.e (Additive.ofMul D.a) = gen (StrothTypeIndex.t100 m).k 1 := by
      simp [StrothTypeData.a, Torus.a, gen, ofMul_toMul]
    have hb : D.e (Additive.ofMul D.b) = gen (StrothTypeIndex.t100 m).k 2 := by
      simp [StrothTypeData.b, Torus.b, gen, ofMul_toMul]
    have hy : y = z 0 • gen (StrothTypeIndex.t100 m).k 0 +
        z 1 • gen (StrothTypeIndex.t100 m).k 1 + z 2 • gen (StrothTypeIndex.t100 m).k 2 := by
      funext i
      fin_cases i <;>
        simp [gen, Pi.single_eq_same, Pi.single_eq_of_ne, hz, Pi.add_apply, Pi.smul_apply]
    have hx' : xB = D.c ^ (z 0) * D.a ^ (z 1) * D.b ^ (z 2) := by
      apply Additive.ofMul.injective
      apply D.e.injective
      rw [show D.e (Additive.ofMul xB) = y from rfl, hy]
      simp only [ofMul_mul, ofMul_zpow, map_add, map_zsmul]
      rw [hc, ha, hb]
    have hx'' : x = (D.c : S) ^ (z 0) * (D.a : S) ^ (z 1) * (D.b : S) ^ (z 2) := by
      simpa using congrArg (fun z : B => (z : S)) hx'
    rw [hx'']
    let cl : Subgroup S := Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S)
    have hc : (D.c : S) ∈ cl := Subgroup.subset_closure (by simp)
    have ha : (D.a : S) ∈ cl := Subgroup.subset_closure (by simp)
    have hb : (D.b : S) ∈ cl := Subgroup.subset_closure (by simp)
    exact cl.mul_mem (cl.mul_mem (cl.zpow_mem hc _) (cl.zpow_mem ha _)) (cl.zpow_mem hb _)

end StrothTypeData

section RelIndexTwo

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)}

theorem index_two_of_relIndex (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) :
    (B.subgroupOf C).index = 2 := by
  have hcard : Nat.card (B.subgroupOf C) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  have hmul : Nat.card (B.subgroupOf C) * (B.subgroupOf C).index = Nat.card C :=
    Subgroup.card_mul_index (B.subgroupOf C)
  rw [hcard, hrel, mul_comm 2 (Nat.card B)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

theorem lt_of_relIndex (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) : B < C := by
  refine lt_of_le_of_ne hBC ?_
  intro hEq
  rw [← hEq] at hrel
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hlt : Nat.card B < Nat.card B :=
    calc Nat.card B < 2 * Nat.card B := lt_mul_of_one_lt_left hpos (by norm_num : 1 < 2)
      _ = Nat.card B := hrel.symm
  exact (lt_irrefl _ hlt).elim

theorem comm_of_le_centralizer (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (x y : C) : x * y = y * x := by
  let H : Subgroup C := B.subgroupOf C
  have hindex : H.index = 2 := index_two_of_relIndex hBC hrel
  haveI : H.Normal := Subgroup.normal_of_index_eq_two hindex
  have hcard : Nat.card (C ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card, hindex]
  haveI : IsCyclic (C ⧸ H) :=
    isCyclic_of_card_dvd_prime (p := 2) (by simpa [hcard])
  have hker : (QuotientGroup.mk' H).ker ≤ Subgroup.center C := by
    rw [QuotientGroup.ker_mk']
    intro b hb
    rw [Subgroup.mem_center_iff]
    intro g
    have hbB : (b : S) ∈ B := Subgroup.mem_subgroupOf.mp hb
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hC g.2) (b : S) hbB).symm
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' H) hker x y

noncomputable def torusHomOfGens {A : Type*} [AddCommGroup A] (k : Fin 3 → ℕ)
    (x : (i : Fin 3) → A) (hx : ∀ i, (2 ^ k i) • x i = 0) : Torus k →+ A :=
  Finset.univ.sum fun i : Fin 3 =>
    (ZMod.lift (2 ^ k i) ⟨zmultiplesHom A (x i), by rw [zmultiplesHom_apply, natCast_zsmul]; exact hx i⟩).comp
      (Pi.evalAddMonoidHom (fun i => ZMod (2 ^ k i)) i)

theorem torusHomOfGens_gen {A : Type*} [AddCommGroup A] {k : Fin 3 → ℕ}
    (x : (i : Fin 3) → A) (hx : ∀ i, (2 ^ k i) • x i = 0) (j : Fin 3) :
    torusHomOfGens k x hx (gen k j) = x j := by
  rw [torusHomOfGens, AddMonoidHom.finset_sum_apply]
  rw [Finset.sum_eq_single j]
  · simp only [AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, gen, Pi.single_eq_same]
    simpa [zmultiplesHom_apply, one_zsmul] using
      (ZMod.lift_coe (2 ^ k j) (f := ⟨zmultiplesHom A (x j), _⟩) (1 : ℤ))
  · intro i _ hij
    simp [gen, Pi.single_eq_of_ne hij, ZMod.lift_coe, zmultiplesHom_apply]
  · intro h
    simp at h

theorem sq_mem_of_index_two {x : C} (hindex : (B.subgroupOf C).index = 2) :
    ((x : S) * (x : S)) ∈ B := by
  have h : x ^ 2 ∈ B.subgroupOf C := Subgroup.sq_mem_of_index_two hindex x
  rw [pow_two] at h
  simpa [Subgroup.mem_subgroupOf] using h

theorem mem_or_exists_mul_of_index_two {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hindex : (B.subgroupOf C).index = 2) {x : S} (hxC : x ∈ C) :
    x ∈ B ∨ ∃ b ∈ B, x = d * b := by
  by_cases hx : x ∈ B
  · exact Or.inl hx
  · right
    let dC : C := ⟨d, hdC⟩
    let xC : C := ⟨x, hxC⟩
    have hdH : dC ∉ B.subgroupOf C := by simpa [Subgroup.mem_subgroupOf] using hdB
    have hxH : xC ∉ B.subgroupOf C := by simpa [Subgroup.mem_subgroupOf] using hx
    have h : dC⁻¹ * xC ∈ B.subgroupOf C := by
      rw [Subgroup.mul_mem_iff_of_index_two hindex]
      constructor
      · intro hd
        exact (hdH (inv_mem_iff.mp hd)).elim
      · intro hx'
        exact (hxH hx').elim
    refine ⟨dC⁻¹ * xC, ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using h
    · simp only [Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_inv_cancel_left]

theorem closure_eq_of_sq (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S)) :
    Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S) = C := by
  let K : Subgroup S := Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S)
  have hdK : d ∈ K := Subgroup.subset_closure (by simp)
  have haK : (D.a : S) ∈ K := Subgroup.subset_closure (by simp)
  have hbK : (D.b : S) ∈ K := Subgroup.subset_closure (by simp)
  have hcK : (D.c : S) ∈ K := by
    rw [← hd2]
    exact K.mul_mem hdK hdK
  have hBK : B ≤ K := by
    rw [← D.closure_c_a_b, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hcK
    · exact haK
    · exact hbK
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hdC
    · exact hBC D.a.2
    · exact hBC D.b.2
  · intro x hxC
    have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
    rcases mem_or_exists_mul_of_index_two hdC hdB hindex hxC with hxB | ⟨b, hbB, rfl⟩
    · exact hBK hxB
    · exact K.mul_mem hdK (hBK hbB)

theorem n_t100 (m : ℕ) : (StrothTypeIndex.t100 m).n = m + 1 := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t100 m)) 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons] at h
  have hk : (StrothTypeIndex.t100 m).k 1 = m + 1 := rfl
  rw [hk] at h
  exact h.symm

theorem m_t100 (m : ℕ) : (StrothTypeIndex.t100 m).m = m := by
  have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t100 m)) 0
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons] at h
  have hk : (StrothTypeIndex.t100 m).k 0 = m := rfl
  rw [hk] at h
  exact h.symm

structure TorusBasisEquiv (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (d : S) (hdC : d ∈ C) where
  e : Additive C ≃+ Torus (Type300.k (m + 1))
  e_d : e (Additive.ofMul ⟨d, hdC⟩) = gen (Type300.k (m + 1)) 0
  e_a : e (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen (Type300.k (m + 1)) 1
  e_b : e (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen (Type300.k (m + 1)) 2

noncomputable def addEquivOfSq (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S)) :
    TorusBasisEquiv D hBC d hdC := by
  letI : CommGroup C := { mul_comm := comm_of_le_centralizer D hBC hC hrel }
  let k3 : Fin 3 → ℕ := Type300.k (m + 1)
  let dC : C := ⟨d, hdC⟩
  let aC : C := ⟨D.a, hBC D.a.2⟩
  let bC : C := ⟨D.b, hBC D.b.2⟩
  let x : (i : Fin 3) → Additive C := ![Additive.ofMul dC, Additive.ofMul aC, Additive.ofMul bC]
  have hd2C : dC ^ 2 = ⟨D.c, hBC D.c.2⟩ := by
    apply Subtype.ext
    simp [dC, pow_two, hd2]
  have hcOrder : orderOf (⟨D.c, hBC D.c.2⟩ : C) = 2 ^ m := by
    rw [show (⟨D.c, hBC D.c.2⟩ : C) = Subgroup.inclusion hBC D.c from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.c,
      D.orderOf_c, m_t100]
  have hcC : (⟨D.c, hBC D.c.2⟩ : C) ^ (2 ^ m) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hcOrder]
  have hdN : dC ^ (2 ^ (m + 1)) = 1 := by
    rw [show 2 ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ'], pow_mul, hd2C, hcC]
  have haOrder : orderOf aC = 2 ^ (m + 1) := by
    rw [show aC = Subgroup.inclusion hBC D.a from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.a,
      D.orderOf_a, n_t100]
  have hbOrder : orderOf bC = 2 ^ (m + 1) := by
    rw [show bC = Subgroup.inclusion hBC D.b from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.b,
      D.orderOf_b, n_t100]
  have haN : aC ^ (2 ^ (m + 1)) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, haOrder]
  have hbN : bC ^ (2 ^ (m + 1)) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hbOrder]
  have hx : ∀ i, (2 ^ k3 i) • x i = 0 := by
    intro i
    fin_cases i
    · change (2 ^ k3 0) • Additive.ofMul dC = 0
      rw [show k3 0 = m + 1 by simp [k3, Type300.k], ← ofMul_pow, hdN]
      simp
    · change (2 ^ k3 1) • Additive.ofMul aC = 0
      rw [show k3 1 = m + 1 by simp [k3, Type300.k], ← ofMul_pow, haN]
      simp
    · change (2 ^ k3 2) • Additive.ofMul bC = 0
      rw [show k3 2 = m + 1 by simp [k3, Type300.k], ← ofMul_pow, hbN]
      simp
  let f : Torus k3 →+ Additive C := torusHomOfGens k3 x hx
  have hfgen : ∀ i : Fin 3, f (gen k3 i) = x i := fun i => torusHomOfGens_gen x hx i
  have hsurj : Function.Surjective f := by
    have hK : f.range.toSubgroup' = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro z
      have hle : Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S) ≤
          f.range.toSubgroup'.map C.subtype := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · refine Subgroup.mem_map.mpr ⟨dC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx0 : x 0 = Additive.ofMul dC := rfl
          rw [← hx0, ← hfgen 0]
          exact ⟨gen k3 0, rfl⟩
        · refine Subgroup.mem_map.mpr ⟨aC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx1 : x 1 = Additive.ofMul aC := rfl
          rw [← hx1, ← hfgen 1]
          exact ⟨gen k3 1, rfl⟩
        · refine Subgroup.mem_map.mpr ⟨bC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx2 : x 2 = Additive.ofMul bC := rfl
          rw [← hx2, ← hfgen 2]
          exact ⟨gen k3 2, rfl⟩
      have hC : C ≤ f.range.toSubgroup'.map C.subtype :=
        calc C = Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S) :=
              (closure_eq_of_sq D hBC hrel hdC hdB hd2).symm
          _ ≤ f.range.toSubgroup'.map C.subtype := hle
      have hz : (z : S) ∈ f.range.toSubgroup'.map C.subtype := hC z.2
      rcases Subgroup.mem_map.mp hz with ⟨k, hk, hks⟩
      have hkz : k = z := Subtype.ext hks
      simpa [hkz] using hk
    have hrange : f.range = ⊤ := by
      apply AddSubgroup.toSubgroup'.injective
      simpa using hK
    exact AddMonoidHom.range_eq_top.mp hrange
  have hcardT : Nat.card (Torus k3) = 2 ^ (3 * (m + 1)) := by
    rw [natCard_torus]
    congr 1
    simp [k3, Type300.k]
    ring
  have hcardC : Nat.card C = 2 ^ (3 * (m + 1)) := by
    rw [hrel, D.card_t100]
    rw [show 2 * 2 ^ (3 * m + 2) = 2 ^ (3 * (m + 1)) by
      rw [show 3 * (m + 1) = 3 * m + 2 + 1 by ring, pow_succ]; ring]
  have heq : Nat.card (Torus k3) = Nat.card (Additive C) := by
    rw [hcardT, ← Nat.card_congr Additive.ofMul, hcardC]
  have hbij : Function.Bijective f :=
    hsurj.bijective_of_nat_card_le (le_of_eq heq)
  let e : Additive C ≃+ Torus k3 := (AddEquiv.ofBijective f hbij).symm
  have ed : e (Additive.ofMul ⟨d, hdC⟩) = gen k3 0 := by
    show (AddEquiv.ofBijective f hbij).symm (Additive.ofMul ⟨d, hdC⟩) = gen k3 0
    rw [show Additive.ofMul ⟨d, hdC⟩ = x 0 from rfl, ← hfgen 0]
    exact AddEquiv.symm_apply_apply _ _
  have ea : e (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen k3 1 := by
    show (AddEquiv.ofBijective f hbij).symm (Additive.ofMul ⟨D.a, hBC D.a.2⟩) = gen k3 1
    rw [show Additive.ofMul ⟨D.a, hBC D.a.2⟩ = x 1 from rfl, ← hfgen 1]
    exact AddEquiv.symm_apply_apply _ _
  have eb : e (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen k3 2 := by
    show (AddEquiv.ofBijective f hbij).symm (Additive.ofMul ⟨D.b, hBC D.b.2⟩) = gen k3 2
    rw [show Additive.ofMul ⟨D.b, hBC D.b.2⟩ = x 2 from rfl, ← hfgen 2]
    exact AddEquiv.symm_apply_apply _ _
  exact ⟨e, ed, ea, eb⟩

section ConjCheck

@[expose] def conjAddHom {g : S} (hg : g ∈ Subgroup.normalizer C) :
    Additive C →+ Additive C where
  toFun x := Additive.ofMul (conjBy hg (Additive.toMul x))
  map_zero' := by simp [conjBy]
  map_add' x y := by
    rw [toMul_add, ← ofMul_mul]
    congr 1
    apply Subtype.ext
    simp [conjBy, mul_assoc]

theorem conj_eq_of_generator_images {k : Fin 3 → ℕ} {g : S}
    (hg : g ∈ Subgroup.normalizer C) (E : Additive C ≃+ Torus k) (φ : Torus k →+ Torus k)
    {xd xa xb : C}
    (hxd : E (Additive.ofMul xd) = gen k 0) (ha0 : E (Additive.ofMul xa) = gen k 1)
    (hb0 : E (Additive.ofMul xb) = gen k 2)
    (hd : E (Additive.ofMul (conjBy hg xd)) = φ (gen k 0))
    (ha : E (Additive.ofMul (conjBy hg xa)) = φ (gen k 1))
    (hb : E (Additive.ofMul (conjBy hg xb)) = φ (gen k 2))
    (x : C) : E (Additive.ofMul (conjBy hg x)) = φ (E (Additive.ofMul x)) := by
  let Φ : Torus k →+ Torus k := E.toAddMonoidHom.comp ((conjAddHom hg).comp E.symm.toAddMonoidHom)
  have hΦ : Φ = φ := by
    apply torus_hom_ext
    intro j z
    rw [show Pi.single j z = z • gen k j by
      funext i
      by_cases h : i = j
      · subst h
        simp [gen, Pi.single_eq_same, zsmul_eq_mul]
      · simp [gen, Pi.single_eq_of_ne h]]
    rw [map_zsmul, map_zsmul]
    congr 1
    fin_cases j
    · show Φ (gen k 0) = φ (gen k 0)
      have hx : E.symm (gen k 0) = Additive.ofMul xd := by
        rw [← hxd, AddEquiv.symm_apply_apply]
      have hΦgen : Φ (gen k 0) = E (Additive.ofMul (conjBy hg xd)) := by
        show E (Additive.ofMul (conjBy hg (Additive.toMul (E.symm (gen k 0))))) =
          E (Additive.ofMul (conjBy hg xd))
        rw [hx, toMul_ofMul]
      rw [hΦgen]
      exact hd
    · show Φ (gen k 1) = φ (gen k 1)
      have hx : E.symm (gen k 1) = Additive.ofMul xa := by
        rw [← ha0, AddEquiv.symm_apply_apply]
      have hΦgen : Φ (gen k 1) = E (Additive.ofMul (conjBy hg xa)) := by
        show E (Additive.ofMul (conjBy hg (Additive.toMul (E.symm (gen k 1))))) =
          E (Additive.ofMul (conjBy hg xa))
        rw [hx, toMul_ofMul]
      rw [hΦgen]
      exact ha
    · show Φ (gen k 2) = φ (gen k 2)
      have hx : E.symm (gen k 2) = Additive.ofMul xb := by
        rw [← hb0, AddEquiv.symm_apply_apply]
      have hΦgen : Φ (gen k 2) = E (Additive.ofMul (conjBy hg xb)) := by
        show E (Additive.ofMul (conjBy hg (Additive.toMul (E.symm (gen k 2))))) =
          E (Additive.ofMul (conjBy hg xb))
        rw [hx, toMul_ofMul]
      rw [hΦgen]
      exact hb
  have hx := DFunLike.congr_fun hΦ (E (Additive.ofMul x))
  rw [← hx]
  change E (Additive.ofMul (conjBy hg x)) =
    E (Additive.ofMul (conjBy hg (Additive.toMul (E.symm (E (Additive.ofMul x))))))
  rw [AddEquiv.symm_apply_apply, toMul_ofMul]

end ConjCheck

@[expose]
def basisElems (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C) {d : S}
    (hdC : d ∈ C) : Fin 3 → C :=
  ![⟨d, hdC⟩, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩]

theorem hasStrothType_t300_of_generator_images
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (E : TorusBasisEquiv D hBC d hdC)
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems D hBC hdC j))) =
      (Type300.action (m + 1)).φuv (gen (Type300.k (m + 1)) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems D hBC hdC j))) =
      (Type300.action (m + 1)).φt (gen (Type300.k (m + 1)) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems D hBC hdC j))) =
      (Type300.action (m + 1)).φu (gen (Type300.k (m + 1)) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems D hBC hdC j))) =
      (Type300.action (m + 1)).φρ (gen (Type300.k (m + 1)) j)) :
    HasStrothType C (StrothTypeIndex.t300 (m + 1)) := by
  let xd : C := ⟨d, hdC⟩
  let xa : C := ⟨D.a, hBC D.a.2⟩
  let xb : C := ⟨D.b, hBC D.b.2⟩
  have hxd : E.e (Additive.ofMul xd) = gen (Type300.k (m + 1)) 0 := E.e_d
  have hxa : E.e (Additive.ofMul xa) = gen (Type300.k (m + 1)) 1 := E.e_a
  have hxb : E.e (Additive.ofMul xb) = gen (Type300.k (m + 1)) 2 := E.e_b
  refine ⟨⟨E.e, D.uv, D.t, D.u, D.ρ, D.uv_sq, D.t_sq, D.uv_comm_t, D.rho_cube, D.u_sq,
    D.u_rho, D.uv_rho, D.t_rho, D.uv_comm_u, D.t_u, hL D.uv_mem_L, hL D.t_mem_L,
    hL D.u_mem_L, hL D.ρ_mem_L,
    conj_eq_of_generator_images (hL D.uv_mem_L) E.e
      (Type300.action (m + 1)).φuv hxd hxa hxb (huv 0) (huv 1) (huv 2),
    conj_eq_of_generator_images (hL D.t_mem_L) E.e
      (Type300.action (m + 1)).φt hxd hxa hxb (ht 0) (ht 1) (ht 2),
    conj_eq_of_generator_images (hL D.u_mem_L) E.e
      (Type300.action (m + 1)).φu hxd hxa hxb (hu 0) (hu 1) (hu 2),
    conj_eq_of_generator_images (hL D.ρ_mem_L) E.e
      (Type300.action (m + 1)).φρ hxd hxa hxb (hρ 0) (hρ 1) (hρ 2)⟩⟩
theorem hasStrothType_t310_of_generator_images
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
    (E : TorusBasisEquiv D hBC d hdC)
    (huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems D hBC hdC j))) =
      (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) j))
    (ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems D hBC hdC j))) =
      (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) j))
    (hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems D hBC hdC j))) =
      (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) j))
    (hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems D hBC hdC j))) =
      (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) j)) :
    HasStrothType C (StrothTypeIndex.t310 (m + 1) (by omega)) := by
  let xd : C := ⟨d, hdC⟩
  let xa : C := ⟨D.a, hBC D.a.2⟩
  let xb : C := ⟨D.b, hBC D.b.2⟩
  have hxd : E.e (Additive.ofMul xd) = gen (Type310.k (m + 1)) 0 := E.e_d
  have hxa : E.e (Additive.ofMul xa) = gen (Type310.k (m + 1)) 1 := E.e_a
  have hxb : E.e (Additive.ofMul xb) = gen (Type310.k (m + 1)) 2 := E.e_b
  refine ⟨⟨E.e, D.uv, D.t, D.u, D.ρ, D.uv_sq, D.t_sq, D.uv_comm_t, D.rho_cube, D.u_sq,
    D.u_rho, D.uv_rho, D.t_rho, D.uv_comm_u, D.t_u, hL D.uv_mem_L, hL D.t_mem_L,
    hL D.u_mem_L, hL D.ρ_mem_L,
    conj_eq_of_generator_images (hL D.uv_mem_L) E.e
      (Type310.action (m + 1) (by omega)).φuv hxd hxa hxb (huv 0) (huv 1) (huv 2),
    conj_eq_of_generator_images (hL D.t_mem_L) E.e
      (Type310.action (m + 1) (by omega)).φt hxd hxa hxb (ht 0) (ht 1) (ht 2),
    conj_eq_of_generator_images (hL D.u_mem_L) E.e
      (Type310.action (m + 1) (by omega)).φu hxd hxa hxb (hu 0) (hu 1) (hu 2),
    conj_eq_of_generator_images (hL D.ρ_mem_L) E.e
      (Type310.action (m + 1) (by omega)).φρ hxd hxa hxb (hρ 0) (hρ 1) (hρ 2)⟩⟩
end RelIndexTwo

end CFSG.CGT.Stroth77
