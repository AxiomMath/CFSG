module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T2
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Bridge
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Matrix Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Solv

theorem isSolvable_sup_of_commute {Y : Type} [Group Y] {A B : Subgroup Y}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) [Group.IsSolvable ↥A] [Group.IsSolvable ↥B] :
    Group.IsSolvable ↥(A ⊔ B) := by
  let Φ : ↥A × ↥B →* Y :=
    { toFun := fun p => (p.1 : Y) * (p.2 : Y)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        have := hcomm (q.1 : Y) q.1.2 (p.2 : Y) p.2.2
        calc (p.1 : Y) * q.1 * ((p.2 : Y) * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
          _ = p.1 * (p.2 * q.1) * q.2 := by rw [← this]
          _ = p.1 * p.2 * (q.1 * q.2) := by group }
  have hrange : Φ.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right b.2)
    · refine sup_le (fun a ha => ⟨(⟨a, ha⟩, 1), by simp [Φ]⟩) (fun b hb => ⟨(1, ⟨b, hb⟩), by simp [Φ]⟩)
  have hmem : ∀ p : ↥A × ↥B, Φ p ∈ A ⊔ B := fun p =>
    Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
  let Ψ : ↥A × ↥B →* ↥(A ⊔ B) := Φ.codRestrict (A ⊔ B) hmem
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨y, hy⟩
    have : y ∈ Φ.range := by rw [hrange]; exact hy
    obtain ⟨p, hp⟩ := this
    exact ⟨p, Subtype.ext hp⟩
  exact Group.isSolvable_of_surjective hsurj

theorem isSolvable_quaternion_two : Group.IsSolvable (QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (QuaternionGroup 2) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have := hp.isNilpotent
  infer_instance

theorem solvable_centralizer_of_m12 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hdata : Stage1Data G z S Kind.m12) : Group.IsSolvable ↥(centralizer ({z} : Set G)) := by
  cases hdata with
  | m12 h =>
    obtain ⟨A, B, hAB, ⟨eA⟩, ⟨eB⟩, -⟩ := h.W_shape
    obtain ⟨hWn, ⟨eQ⟩⟩ := h.quot
    have : Group.IsSolvable (QuaternionGroup 2) := isSolvable_quaternion_two
    have hAs : Group.IsSolvable ↥A :=
      Group.isSolvable_of_isSolvable_injective (f := eA.toMonoidHom) eA.injective
    have hBs : Group.IsSolvable ↥B :=
      Group.isSolvable_of_isSolvable_injective (f := eB.toMonoidHom) eB.injective
    have hW : Group.IsSolvable ↥(WBar z) := by
      rw [← hAB.1]
      exact isSolvable_sup_of_commute hAB.2.1
    have := hWn
    have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    have hQ : Group.IsSolvable (CentralizerBar z ⧸ WBar z) :=
      Group.isSolvable_of_isSolvable_injective (f := eQ.toMonoidHom) eQ.injective
    have := hW
    have hCbar : Group.IsSolvable (CentralizerBar z) :=
      Group.isSolvable_of_ker_le_range (WBar z).subtype (QuotientGroup.mk' (WBar z))
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
    have := hCbar
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Final.Thm4.pPrimeCore_solvable (X := ↥(centralizer ({z} : Set G)))
    exact Group.isSolvable_of_ker_le_range (pPrimeCore 2 ↥(centralizer ({z} : Set G))).subtype
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Solv

section Lift

theorem odd_card_center_of_no_central_involution {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hnoc : ∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) :
    Odd (Nat.card ↥(center ↥J)) := by
  by_contra hne
  have heven : Even (Nat.card ↥(center ↥J)) := Nat.not_odd_iff_even.mp hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥J)) 2 heven.two_dvd
  set c' : ↥J := (c : ↥J) with hc'
  set g : G := (c' : G) with hg
  have hog : orderOf g = 2 := by
    rw [hg, Subgroup.orderOf_coe, hc', Subgroup.orderOf_coe, hc]
  have hg2 : g * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [hog, pow_two] at this
    exact this
  have hgJ : g ∈ J := c'.2
  have hgc : ∀ x ∈ J, g * x = x * g := by
    intro x hx
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨x, hx⟩)
    simpa [hg, hc', Subgroup.coe_mul] using this.symm
  have := hnoc g hgJ hgc hg2
  rw [this, orderOf_one] at hog
  omega

theorem exists_finset_card_four' {F : Type} [Field F] [Finite F] (h : 4 ≤ Nat.card F) :
    ∃ s : Finset F, s.card = 4 := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h)
  exact ⟨s, hs⟩

theorem exists_perfect_lift_of_lieModel {G : Type} [Group G] [Finite G] {z : G} {J : Subgroup G}
    (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hnoc : ∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 2 ≤ n) (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 p n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ n ∧
      ∃ Y : Subgroup ↥J, Y ≤ centralizer ({(⟨z, hzJ⟩ : ↥J)} : Set ↥J) ∧ Group.IsPerfect ↥Y ∧
        ∃ φ : ↥Y →* SpecialLinearGroup (Fin 2) F, Function.Surjective φ ∧
          ∀ a : ↥Y, φ a = 1 → (a : ↥J) ∈ center ↥J := by
  obtain ⟨F, iF, fF, hFcard, ⟨ι⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  have hFodd : Odd (Nat.card F) := by
    rw [hFcard]
    exact (hp.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  have hz2 : (⟨z, hzJ⟩ : ↥J) * ⟨z, hzJ⟩ = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one z
    rw [hz, pow_two] at this
    exact this
  have hz1 : (⟨z, hzJ⟩ : ↥J) ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at hz
    omega
  obtain ⟨Y, hYC, hYperf, φ, hφs, hφk⟩ :=
    exists_perfect_lift_centralizer (odd_card_center_of_no_central_involution hnoc) hFodd
      (exists_finset_card_four' h4) ι hz2 hz1
  exact ⟨F, iF, fF, hFcard, Y, hYC, hYperf, φ, hφs, hφk⟩

end Lift

section M12

theorem false_of_m12 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hdata : Stage1Data G z S Kind.m12) (hz : orderOf z = 2) {J : Subgroup G} (hzJ : z ∈ J)
    (hnoc : ∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 2 ≤ n) (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 p n) : False := by
  have hsolv := solvable_centralizer_of_m12 hdata
  obtain ⟨F, iF, fF, hFcard, Y, hYC, hYperf, φ, hφs, -⟩ :=
    exists_perfect_lift_of_lieModel hzJ hz hnoc hp hp2 hn hLie
  have h4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  have hSLnt : Nontrivial (SpecialLinearGroup (Fin 2) F) :=
    CFSG.LocalCores.isQuasisimple_nontrivial (CFSG.RankThree.Classical.isQuasisimple_SL2
      (exists_finset_card_four' h4))
  have hYnt : Nontrivial ↥Y := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (SpecialLinearGroup (Fin 2) F)
    obtain ⟨a', rfl⟩ := hφs a
    obtain ⟨b', rfl⟩ := hφs b
    exact ⟨a', b', fun h => hab (by rw [h])⟩
  have hmem : ∀ y : ↥Y, ((y : ↥J) : G) ∈ centralizer ({z} : Set G) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hYC y.2)
    exact congrArg Subtype.val this
  let f : ↥Y →* ↥(centralizer ({z} : Set G)) :=
    ((J.subtype.comp Y.subtype).codRestrict (centralizer ({z} : Set G)) hmem)
  have hfinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hYs : Group.IsSolvable ↥Y := Group.isSolvable_of_isSolvable_injective hfinj
  have := hYperf
  exact Group.IsPerfect.not_isSolvable ↥Y inferInstance

end M12

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
