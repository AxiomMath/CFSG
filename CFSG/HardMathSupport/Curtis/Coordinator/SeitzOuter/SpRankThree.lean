module

public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.LieType.SeitzGeneration.SpBlockPlanes
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCSpFull (coprime_card_ker_proj)
open scoped MatrixGroups

theorem card_sup_zpowers_of_comm {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    {c : G} (hcH : ∀ h ∈ H, Commute h c) (hc : orderOf c = p) (hind : c ∉ H) :
    Nat.card ↥(H ⊔ Subgroup.zpowers c) = Nat.card H * p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcz : Nat.card ↥(Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, hc]
  have hinf : H ⊓ Subgroup.zpowers c = ⊥ := by
    have : Fact (Nat.card ↥(Subgroup.zpowers c)).Prime := ⟨by rw [hcz]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((H ⊓ Subgroup.zpowers c).subgroupOf (Subgroup.zpowers c)) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      apply hind
      have hcc : (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ∈
          (H ⊓ Subgroup.zpowers c).subgroupOf (Subgroup.zpowers c) := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hcc).1
  have hcomm : ∀ x ∈ H, ∀ y ∈ Subgroup.zpowers c, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (hcH x hx).zpow_right m
  let φ : H × Subgroup.zpowers c →* G :=
    MonoidHom.noncommCoprod H.subtype (Subgroup.zpowers c).subtype
      fun x y => hcomm x x.2 y y.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := hxy
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hmem : (x : G) ∈ H ⊓ Subgroup.zpowers c :=
      ⟨x.2, by rw [hx]; exact (Subgroup.zpowers c).inv_mem y.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hy : (y : G) = 1 := inv_eq_one.1 (hx.symm.trans hmem)
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy)
  have hrange : φ.range = H ⊔ Subgroup.zpowers c := by
    have h1 : φ.range = H.subtype.range ⊔ (Subgroup.zpowers c).subtype.range :=
      MonoidHom.noncommCoprod_range _ _ _
    rw [h1, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hcz]

theorem card_closure_three {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {a b c : G}
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : orderOf a = p) (hb : orderOf b = p) (hc : orderOf c = p)
    (hind : b ∉ Subgroup.zpowers a) (hind' : c ∉ Subgroup.closure ({a, b} : Set G)) :
    Nat.card ↥(Subgroup.closure ({a, b, c} : Set G)) = p ^ 3 := by
  have hH : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = p ^ 2 :=
    card_closure_pair' hp hab ha hb hind
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      rw [Set.mem_singleton_iff.1 hg]
      exact hac.symm.eq
    · refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      rw [Set.mem_singleton_iff.1 hg]
      exact hbc.symm.eq
  have hcH : ∀ h ∈ Subgroup.closure ({a, b} : Set G), Commute h c := by
    intro h hh
    exact (Subgroup.mem_centralizer_iff.1 (hle hh) c (Set.mem_singleton c)).symm
  have hsup := card_sup_zpowers_of_comm hp hcH hc hind'
  have hset : Subgroup.closure ({a, b, c} : Set G) =
      Subgroup.closure ({a, b} : Set G) ⊔ Subgroup.zpowers c := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp : x ∈ ({x, b} : Set G)))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp : x ∈ ({a, x} : Set G)))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine sup_le (Subgroup.closure_mono ?_)
        (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
      intro x hx
      rcases hx with rfl | rfl <;> simp
  rw [hset, hsup, hH]
  ring

theorem isElemAbelian_closure_three {G : Type*} [Group G] {p : ℕ} {a b c : G}
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hc : c ^ p = 1) :
    IsElemAbelian p (Subgroup.closure ({a, b, c} : Set G)) := by
  refine isElemAbelian_closure_of_comm ?_ ?_
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
      | exact Commute.refl _
      | exact hab
      | exact hab.symm
      | exact hac
      | exact hac.symm
      | exact hbc
      | exact hbc.symm
  · intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption

theorem exists_sl2_order_three (k : Type) [Field k] : ∃ A : SL(2, k), orderOf A = 3 := by
  let A : SL(2, k) := ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩
  refine ⟨A, ?_⟩
  have hM : (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) k) ^ 3 = 1 := by
    rw [pow_succ, pow_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have h3 : A ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hM
  have hne : A ≠ 1 := by
    intro h
    have h01 := congrArg (fun X : SL(2, k) => (X : Matrix (Fin 2) (Fin 2) k) 0 1) h
    simp [A] at h01
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 hne

section Model

variable {r : ℕ} {k : Type} [Field k]

theorem exists_three_block_elemAbelian (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime) (A : SL(2, k))
    (hA : orderOf A = p) :
    ∃ E : Subgroup (StatedSp r k), IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  let k₀ : Fin r := ⟨0, by omega⟩
  let k₁ : Fin r := ⟨1, by omega⟩
  let l : Fin r := ⟨2, by omega⟩
  have hk : k₀ ≠ k₁ := fun h => by simpa [k₀, k₁] using congrArg Fin.val h
  have hl₀ : l ≠ k₀ := fun h => by simpa [l, k₀] using congrArg Fin.val h
  have hl₁ : l ≠ k₁ := fun h => by simpa [l, k₁] using congrArg Fin.val h
  set a : StatedSp r k := longBlock k r k₀ A with ha
  set b : StatedSp r k := longBlock k r k₁ A with hb
  set c : StatedSp r k := longBlock k r l A with hc
  have hA1 : A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact hp.one_lt.ne hA
  have ha1 : a ≠ 1 := fun h => hA1 (longBlock_injective k₀ (by rw [map_one]; exact h))
  have hb1 : b ≠ 1 := fun h => hA1 (longBlock_injective k₁ (by rw [map_one]; exact h))
  have hab : Commute a b := commute_longBlock hk A A
  have hac : Commute a c := commute_longBlock hl₀.symm A A
  have hbc : Commute b c := commute_longBlock hl₁.symm A A
  have hao : orderOf a = p := by
    rw [ha, orderOf_injective (longBlock k r k₀) (longBlock_injective k₀) A, hA]
  have hbo : orderOf b = p := by
    rw [hb, orderOf_injective (longBlock k r k₁) (longBlock_injective k₁) A, hA]
  have hco : orderOf c = p := by
    rw [hc, orderOf_injective (longBlock k r l) (longBlock_injective l) A, hA]
  have hc1 : c ≠ 1 := fun h => hA1 (longBlock_injective l (by rw [map_one]; exact h))
  have hind : b ∉ Subgroup.zpowers a := by
    intro hmem
    have hdisj : Disjoint (coords k₀) (coords k₁) := Set.disjoint_left.2 fun x h0 h1 => by
      rcases mem_coords.1 h0 with rfl | rfl <;> rcases mem_coords.1 h1 with h | h <;>
        first | exact hk (Sum.inl_injective h) | exact hk (Sum.inr_injective h) | cases h
    have h0 : b ∈ suppGroup (K := k) (coords k₀) := by
      have : Subgroup.zpowers a ≤ suppGroup (coords k₀) :=
        Subgroup.zpowers_le.2 ((mem_suppGroup).2 (isSupp_longBlock k₀ A))
      exact this hmem
    exact hb1 (eq_one_of_isSupp_disjoint hdisj h0 (isSupp_longBlock k₁ A))
  have hsub : Subgroup.closure ({a, b} : Set (StatedSp r k)) ≤
      suppGroup (coords k₀ ∪ coords k₁) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact suppGroup_mono Set.subset_union_left
        ((mem_suppGroup).2 (isSupp_longBlock k₀ A))
    · exact suppGroup_mono Set.subset_union_right
        ((mem_suppGroup).2 (isSupp_longBlock k₁ A))
  have hind' : c ∉ Subgroup.closure ({a, b} : Set (StatedSp r k)) := by
    intro hmem
    have hdisj : Disjoint (coords k₀ ∪ coords k₁) (coords l) := by
      rw [Set.disjoint_left]
      intro x hx hxl
      rcases mem_coords.1 hxl with rfl | rfl <;> rcases hx with hx | hx <;>
        rcases mem_coords.1 hx with h | h <;>
        first
        | exact hl₀ (Sum.inl_injective h)
        | exact hl₁ (Sum.inl_injective h)
        | exact hl₀ (Sum.inr_injective h)
        | exact hl₁ (Sum.inr_injective h)
        | cases h
    have h0 : c ∈ suppGroup (K := k) (coords k₀ ∪ coords k₁) := hsub hmem
    exact hc1 (eq_one_of_isSupp_disjoint hdisj (mem_suppGroup.1 h0)
      (isSupp_longBlock l A))
  refine ⟨Subgroup.closure ({a, b, c} : Set (StatedSp r k)), ?_,
    card_closure_three hp hab hac hbc hao hbo hco hind hind'⟩
  refine isElemAbelian_closure_three hab hac hbc ?_ ?_ ?_
  · rw [← hao]; exact pow_orderOf_eq_one _
  · rw [← hbo]; exact pow_orderOf_eq_one _
  · rw [← hco]; exact pow_orderOf_eq_one _

end Model

theorem not_rankLE2_three_projectiveSp {r : ℕ} (hr : 3 ≤ r) {k : Type} [Field k] [Finite k]
    (hk : ¬ 3 ∣ Nat.card k) : ¬ RankLE2 3 (StatedProj (StatedSp r k)) := by
  intro hrank
  obtain ⟨A, hA⟩ := exists_sl2_order_three k
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨E, hE, hc⟩ := exists_three_block_elemAbelian hr hp A hA
  have hker : Nat.Coprime (Nat.card (proj r k).ker) 3 :=
    coprime_card_ker_proj (r := r) (K := k) (by omega) hp (by norm_num)
  have hEker : ∀ x ∈ E, proj r k x = 1 → x = 1 := by
    intro x hx hπ
    have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hE.2 x hx)
    have h2 : orderOf x ∣ Nat.card (proj r k).ker := by
      let y : (proj r k).ker := ⟨x, hπ⟩
      calc orderOf x = orderOf y := Subgroup.orderOf_coe y
        _ ∣ Nat.card (proj r k).ker := orderOf_dvd_natCard y
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hker h2 h1)
  have hinj : Function.Injective ((proj r k).comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h
    exact Subtype.ext (hEker x hx (by simpa using h))
  have hF : IsElemAbelian 3 (E.map (proj r k)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE _
  have hcard : Nat.card (E.map (proj r k)) = 3 ^ 3 := by
    have hrange : ((proj r k).comp E.subtype).range = E.map (proj r k) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← hc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hle := hrank _ hF
  rw [hcard] at hle
  norm_num at hle

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

end
