module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
public import CFSG.GroupTheory.HuppertProduct.Quotient
import CFSG.GroupTheory.HuppertProduct.CommutatorClosure
import CFSG.GroupTheory.HuppertProduct.NilpotentAbsorption
import CFSG.GroupTheory.HuppertProduct.RelIndexHom
import CFSG.GroupTheory.HuppertProduct.ProductIndex
import CFSG.GroupTheory.HuppertProduct.SmallQuotient
import CFSG.GroupTheory.HuppertProduct.PGroupMho
import CFSG.GroupTheory.HuppertProduct.RankBound

public section

open scoped commutatorElement

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace KHupOdd

open CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

theorem pow_mul_eq_of_commute {x y : G} (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    y ^ n * x = ⁅y, x⁆ ^ n * x * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hyx : y * x = ⁅y, x⁆ * x * y := by rw [commutatorElement_def]; group
    have hcy : ⁅y, x⁆ ^ n * y = y * ⁅y, x⁆ ^ n := (hy.pow_left n).eq
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (⁅y, x⁆ ^ n * x * y ^ n) := by rw [ih]
      _ = (y * ⁅y, x⁆ ^ n) * x * y ^ n := by simp only [mul_assoc]
      _ = (⁅y, x⁆ ^ n * y) * x * y ^ n := by rw [hcy]
      _ = ⁅y, x⁆ ^ n * (y * x) * y ^ n := by simp only [mul_assoc]
      _ = ⁅y, x⁆ ^ n * (⁅y, x⁆ * x * y) * y ^ n := by rw [hyx]
      _ = ⁅y, x⁆ ^ (n + 1) * x * y ^ (n + 1) := by
        rw [pow_succ ⁅y, x⁆ n, pow_succ' y n]; simp only [mul_assoc]

theorem mul_pow_of_commute {x y : G} (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    (x * y) ^ n = ⁅y, x⁆ ^ n.choose 2 * x ^ n * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : y ^ n * x = ⁅y, x⁆ ^ n * x * y ^ n := pow_mul_eq_of_commute hy n
    have h2 : x ^ n * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * x ^ n := ((hx.pow_pow n n).eq).symm
    have hc : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = ⁅y, x⁆ ^ n.choose 2 * x ^ n * y ^ n * (x * y) := by rw [ih]
      _ = ⁅y, x⁆ ^ n.choose 2 * x ^ n * (y ^ n * x) * y := by simp only [mul_assoc]
      _ = ⁅y, x⁆ ^ n.choose 2 * x ^ n * (⁅y, x⁆ ^ n * x * y ^ n) * y := by rw [h1]
      _ = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * ⁅y, x⁆ ^ n) * x * y ^ n * y := by
        simp only [mul_assoc]
      _ = ⁅y, x⁆ ^ n.choose 2 * (⁅y, x⁆ ^ n * x ^ n) * x * y ^ n * y := by rw [h2]
      _ = ⁅y, x⁆ ^ (n + 1).choose 2 * x ^ (n + 1) * y ^ (n + 1) := by
        rw [hc, pow_add, pow_succ x n, pow_succ y n]; simp only [mul_assoc]

theorem mul_pow_prime_of_commute {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y : G}
    (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (hc : ⁅y, x⁆ ^ p = 1) :
    (x * y) ^ p = x ^ p * y ^ p := by
  have h3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (by norm_num : (2 : ℕ) ≠ 0) h3
  rw [mul_pow_of_commute hx hy p, hk, pow_mul, hc, one_pow, one_mul]

theorem commutator_pow_eq_one {Γ : Type*} [Group Γ] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x g : Γ} (hd : ⁅g, x⁆ ^ p = 1) (hx : Commute ⁅x, ⁅g, x⁆⁆ x)
    (hdd : Commute ⁅x, ⁅g, x⁆⁆ ⁅g, x⁆) : ⁅x ^ p, g⁆ = 1 := by
  set d := ⁅g, x⁆ with hd_def
  set e := ⁅x, d⁆ with he_def
  have h1 : g * x * g⁻¹ = d * x := by
    rw [hd_def, commutatorElement_def]
    group
  have h3 : e ^ p = 1 := by
    rw [he_def, Commute.commutatorElement_pow_right hdd.symm p, hd, commutatorElement_one_right]
  have h2 : (d * x) ^ p = d ^ p * x ^ p :=
    mul_pow_prime_of_commute hp hp2 (x := d) (y := x) hdd hx h3
  have h4 : g * x ^ p * g⁻¹ = x ^ p := by
    have : g * x ^ p * g⁻¹ = (g * x * g⁻¹) ^ p := by
      simp [conj_pow]
    rw [this, h1, h2, hd]
    simp
  rw [commutatorElement_def]
  calc x ^ p * g * (x ^ p)⁻¹ * g⁻¹ = x ^ p * (g * x ^ p * g⁻¹)⁻¹ := by group
    _ = 1 := by rw [h4]; simp

theorem pow_commutator_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H K : Subgroup G}
    (hK : H ≤ Subgroup.normalizer (K : Set G)) {x g : G} (hx : x ∈ H) (hg : g ∈ H)
    (hd : ⁅g, x⁆ ^ p ∈ K) (hc : ∀ h ∈ H, ⁅⁅x, ⁅g, x⁆⁆, h⁆ ∈ K) : ⁅x ^ p, g⁆ ∈ K := by
  obtain ⟨Γ, _, π, -, hπ⟩ := exists_quotient hK
  let x' : H := ⟨x, hx⟩
  let g' : H := ⟨g, hg⟩
  have hdH : ⁅g, x⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)) (H.inv_mem hx)
  let d' : H := ⟨⁅g, x⁆, hdH⟩
  have hd' : d' = ⁅g', x'⁆ := rfl
  have hdp : π d' ^ p = 1 := by
    rw [← map_pow]
    exact (hπ _).2 (by simpa [d'] using hd)
  have hcx : ∀ h : H, ⁅π ⁅x', d'⁆, π h⁆ = 1 := by
    intro h
    rw [← map_commutatorElement]
    exact (hπ _).2 (by simpa [x', d', commutatorElement_def] using hc h h.2)
  have key : ⁅π x' ^ p, π g'⁆ = 1 := by
    refine commutator_pow_eq_one hp hp2 (x := π x') (g := π g') ?_ ?_ ?_
    · rw [← map_commutatorElement, ← hd']
      exact hdp
    · rw [← map_commutatorElement, ← map_commutatorElement, ← hd']
      exact commutatorElement_eq_one_iff_commute.1 (hcx x')
    · rw [← map_commutatorElement, ← map_commutatorElement, ← hd']
      exact commutatorElement_eq_one_iff_commute.1 (hcx d')
  have : π ⁅x' ^ p, g'⁆ = 1 := by
    rw [map_commutatorElement, map_pow]
    exact key
  simpa [x', g', commutatorElement_def] using (hπ _).1 this

theorem commutator_mho_le_mho_mho_odd [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Subgroup G} (hH : IsPGroup p H) (hcomm : ⁅H, H⁆ ≤ GroupTheory.HuppertProduct.mho H p) :
    ⁅GroupTheory.HuppertProduct.mho H p, H⁆ ≤ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent H := hH.isNilpotent
  have hMH : GroupTheory.HuppertProduct.mho H p ≤ H := mho_le H p
  have hQH : GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p ≤ H := (mho_le _ p).trans hMH
  have hQn : H ≤ Subgroup.normalizer ((GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p : Subgroup G) : Set G) :=
    le_normalizer_mho_mho H p p
  have hLn : H ≤ Subgroup.normalizer ((⁅⁅GroupTheory.HuppertProduct.mho H p, H⁆, H⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right ⁅GroupTheory.HuppertProduct.mho H p, H⁆ H
  have hKn : H ≤ Subgroup.normalizer
      ((GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p ⊔ ⁅⁅GroupTheory.HuppertProduct.mho H p, H⁆, H⁆ : Subgroup G) : Set G) :=
    le_normalizer_sup hQn hLn
  have step1 : ∀ x ∈ H, ∀ g ∈ H, ⁅x ^ p, g⁆ ∈ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p ⊔ ⁅⁅GroupTheory.HuppertProduct.mho H p, H⁆, H⁆ := by
    intro x hx g hg
    have hdM : ⁅g, x⁆ ∈ GroupTheory.HuppertProduct.mho H p := hcomm (Subgroup.commutator_mem_commutator hg hx)
    refine pow_commutator_mem hp hp2 hKn hx hg ?_ ?_
    · exact Subgroup.mem_sup_left (pow_mem_mho hdM)
    · intro h hh
      have hL : ⁅x, ⁅g, x⁆⁆ ∈ ⁅GroupTheory.HuppertProduct.mho H p, H⁆ := by
        rw [← commutatorElement_inv]
        exact (⁅GroupTheory.HuppertProduct.mho H p, H⁆).inv_mem (Subgroup.commutator_mem_commutator hdM hx)
      exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hL hh)
  have step2 : ⁅GroupTheory.HuppertProduct.mho H p, H⁆ ≤ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p ⊔ ⁅⁅GroupTheory.HuppertProduct.mho H p, H⁆, H⁆ :=
    commutator_mho_le hKn step1
  exact le_of_le_sup_commutator inferInstance hQH hQn
    (Subgroup.commutator_le_of_le hMH le_rfl) step2

theorem pow_mul_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hcomm : ⁅H, H⁆ ≤ GroupTheory.HuppertProduct.mho H p) (hpow : ⁅GroupTheory.HuppertProduct.mho H p, H⁆ ≤ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p) {x y : G} (hx : x ∈ H)
    (hy : y ∈ H) : (x ^ p * y ^ p)⁻¹ * (x * y) ^ p ∈ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p := by
  obtain ⟨Γ, _, π, -, hπ⟩ := exists_quotient (le_normalizer_mho_mho H p p)
  have hdM : ⁅y, x⁆ ∈ GroupTheory.HuppertProduct.mho H p := hcomm (Subgroup.commutator_mem_commutator hy hx)
  have hdH : ⁅y, x⁆ ∈ H := mho_le H p hdM
  let x' : H := ⟨x, hx⟩
  let y' : H := ⟨y, hy⟩
  let c' : H := ⟨⁅y, x⁆, hdH⟩
  have hc' : c' = ⁅y', x'⁆ := rfl
  have hcp : π c' ^ p = 1 := by
    rw [← map_pow]
    exact (hπ _).2 (by simpa [c'] using pow_mem_mho (n := p) hdM)
  have hcen : ∀ h : H, ⁅π c', π h⁆ = 1 := by
    intro h
    rw [← map_commutatorElement]
    refine (hπ _).2 ?_
    have : ⁅⁅y, x⁆, (h : G)⁆ ∈ ⁅GroupTheory.HuppertProduct.mho H p, H⁆ := Subgroup.commutator_mem_commutator hdM h.2
    simpa [c', commutatorElement_def] using hpow this
  have key := mul_pow_prime_of_commute hp hp2 (x := π x') (y := π y')
    (commutatorElement_eq_one_iff_commute.1 (by simpa [← map_commutatorElement, hc'] using hcen x'))
    (commutatorElement_eq_one_iff_commute.1 (by simpa [← map_commutatorElement, hc'] using hcen y'))
    (by rw [← map_commutatorElement, ← hc']; exact hcp)
  have : π ((x' ^ p * y' ^ p)⁻¹ * (x' * y') ^ p) = 1 := by
    simp only [map_mul, map_inv, map_pow]
    rw [key]
    simp
  simpa [x', y'] using (hπ _).1 this

theorem exists_pow_hom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hcomm : ⁅H, H⁆ ≤ GroupTheory.HuppertProduct.mho H p) (hpow : ⁅GroupTheory.HuppertProduct.mho H p, H⁆ ≤ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p) :
    ∃ φ : H →* (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p),
      ∀ (x : H) (m : GroupTheory.HuppertProduct.mho H p), (m : G) = (x : G) ^ p →
        φ x = (m : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)) := by
  let c : H → GroupTheory.HuppertProduct.mho H p := fun x => ⟨(x : G) ^ p, pow_mem_mho x.2⟩
  have hmul : ∀ x y : H,
      ((c (x * y) : GroupTheory.HuppertProduct.mho H p) : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)) =
        ((c x : GroupTheory.HuppertProduct.mho H p) : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)) *
          ((c y : GroupTheory.HuppertProduct.mho H p) : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)) := by
    intro x y
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).inv_mem (pow_mul_mem hp hp2 hcomm hpow x.2 y.2)
    rw [mul_inv_rev, inv_inv] at h
    exact h
  have hone : ((c 1 : GroupTheory.HuppertProduct.mho H p) : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show ((1 : H) : G) ^ p ∈ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p
    rw [Subgroup.coe_one, one_pow]
    exact one_mem _
  let φ : H →* (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p) :=
    { toFun := fun x => ((c x : GroupTheory.HuppertProduct.mho H p) : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p))
      map_one' := hone
      map_mul' := fun x y => hmul x y }
  refine ⟨φ, fun x m hm => ?_⟩
  have hcm : c x = m := Subtype.ext hm.symm
  calc φ x = ((c x : GroupTheory.HuppertProduct.mho H p) : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)) := rfl
    _ = ((m : GroupTheory.HuppertProduct.mho H p) : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)) := by rw [hcm]

theorem pow_hom_surjective {p : ℕ} {H : Subgroup G}
    {φ : H →* (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)}
    (hφ : ∀ (x : H) (m : GroupTheory.HuppertProduct.mho H p), (m : G) = (x : G) ^ p →
      φ x = (m : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p))) :
    Function.Surjective φ := by
  have hS : GroupTheory.HuppertProduct.mho H p ≤ ((φ.range).comap
      (QuotientGroup.mk' ((GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)))).map (GroupTheory.HuppertProduct.mho H p).subtype := by
    refine mho_le_of_forall fun x hx => ?_
    refine Subgroup.mem_map.2 ⟨⟨(x : G) ^ p, pow_mem_mho hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact MonoidHom.mem_range.2 ⟨⟨x, hx⟩, hφ ⟨x, hx⟩ ⟨(x : G) ^ p, pow_mem_mho hx⟩ rfl⟩
  have key : ∀ m : GroupTheory.HuppertProduct.mho H p,
      ((m : (GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p))) ∈ φ.range := by
    intro m
    obtain ⟨t, ht, htm⟩ := Subgroup.mem_map.1 (hS m.2)
    have htm' : t = m := Subtype.ext htm
    rw [htm'] at ht
    exact Subgroup.mem_comap.1 ht
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  exact MonoidHom.mem_range.1 (key m)

theorem relIndex_mul_le_odd [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H E : Subgroup G}
    (hcomm : ⁅H, H⁆ ≤ GroupTheory.HuppertProduct.mho H p) (hpow : ⁅GroupTheory.HuppertProduct.mho H p, H⁆ ≤ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p) (hEH : E ≤ H)
    (hEp : ∀ e ∈ E, e ^ p = 1) :
    (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) * (GroupTheory.HuppertProduct.mho H p).relIndex E ≤ (GroupTheory.HuppertProduct.mho H p).relIndex H := by
  obtain ⟨φ, hφ⟩ := exists_pow_hom hp hp2 hcomm hpow
  have hsurj := pow_hom_surjective hφ
  have hker : ∀ x : H, (x : G) ^ p ∈ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p → φ x = 1 := by
    intro x hx
    rw [hφ x ⟨(x : G) ^ p, pow_mem_mho x.2⟩ rfl, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hx
  have h := card_mul_relIndex_le φ hsurj (mho_le H p) hEH
    (fun x hx => hker x (pow_mem_mho hx))
    (fun x hx => hker x (by rw [hEp x hx]; exact one_mem _))
  have hcard : Nat.card ((GroupTheory.HuppertProduct.mho H p) ⧸ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).subgroupOf (GroupTheory.HuppertProduct.mho H p)) =
      (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) :=
    (Subgroup.index_eq_card _).symm
  rwa [hcard] at h

theorem relIndex_mho_mho_le_odd [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hcomm : ⁅H, H⁆ ≤ GroupTheory.HuppertProduct.mho H p) (hpow : ⁅GroupTheory.HuppertProduct.mho H p, H⁆ ≤ GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p) :
    (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) ≤ (GroupTheory.HuppertProduct.mho H p).relIndex H := by
  have h := relIndex_mul_le_odd hp hp2 hcomm hpow (bot_le : (⊥ : Subgroup G) ≤ H)
    (fun e he => by rw [(Subgroup.mem_bot.1 he)]; exact one_pow p)
  rwa [Subgroup.relIndex_bot_right, mul_one] at h

theorem card_le_of_isCyclic [Finite G] {p : ℕ} (hp : 0 < p) {S F : Subgroup G} (hS : IsCyclic S)
    (hFS : F ≤ S) (hF : ∀ e ∈ F, e ^ p = 1) : Nat.card F ≤ p := by
  haveI : IsCyclic (F.subgroupOf S) := Subgroup.isCyclic _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F.subgroupOf S)
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have := hF (((g : S)) : G) (Subgroup.mem_subgroupOf.1 g.2)
    simpa using this
  have hcard : Nat.card (F.subgroupOf S) = orderOf g :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have h3 : orderOf g ≤ p := Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one hgp)
  have hFS' : Nat.card F = Nat.card (F.subgroupOf S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFS).toEquiv.symm
  omega

theorem relIndex_mho_mho_le_sq [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {H : Subgroup G}
    (hH : IsPGroup p H) (h : (GroupTheory.HuppertProduct.mho H p).relIndex H ≤ p ^ 2) :
    (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) ≤ p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hcomm : ⁅H, H⁆ ≤ GroupTheory.HuppertProduct.mho H p := commutator_le_mho_of_relIndex_le (p := p) h
  exact (relIndex_mho_mho_le_odd hp hp2 hcomm
    (commutator_mho_le_mho_mho_odd hp hp2 hH hcomm)).trans h

theorem card_ne_pow_three_of_relIndex_mho_le [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {H E : Subgroup G} (hH : IsPGroup p H) (hidx : (GroupTheory.HuppertProduct.mho H p).relIndex H ≤ p ^ 2) (hEH : E ≤ H)
    (hEp : ∀ e ∈ E, e ^ p = 1) : Nat.card E ≠ p ^ 3 := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have main : ∀ n : ℕ, ∀ (H E : Subgroup G), Nat.card H = n → IsPGroup p H →
      (GroupTheory.HuppertProduct.mho H p).relIndex H ≤ p ^ 2 → E ≤ H → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≠ p ^ 3 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H E hn hH hidx hEH hEp
      by_cases hbot : H = ⊥
      · subst hbot
        have hE : E = ⊥ := le_bot_iff.1 hEH
        subst hE
        rw [Subgroup.card_bot]
        have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp1
        omega
      have hMH : GroupTheory.HuppertProduct.mho H p ≤ H := mho_le H p
      have hMne : GroupTheory.HuppertProduct.mho H p ≠ H := fun h => hbot (eq_bot_of_mho_eq_self hH h)
      have hcard : Nat.card (GroupTheory.HuppertProduct.mho H p) < n :=
        hn ▸ Subgroup.card_lt_of_lt (lt_of_le_of_ne hMH hMne)
      have hMp : IsPGroup p (GroupTheory.HuppertProduct.mho H p) := hH.to_le hMH
      have hMidx : (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) ≤ p ^ 2 :=
        relIndex_mho_mho_le_sq hp2 hH hidx
      by_cases hEM : E ≤ GroupTheory.HuppertProduct.mho H p
      · exact ih _ hcard (GroupTheory.HuppertProduct.mho H p) E rfl hMp hMidx hEM hEp
      · intro hE
        have hcomm : ⁅H, H⁆ ≤ GroupTheory.HuppertProduct.mho H p := commutator_le_mho_of_relIndex_le (p := p) hidx
        have hpow := commutator_mho_le_mho_mho_odd hp hp2 hH hcomm
        have hab : (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) * (GroupTheory.HuppertProduct.mho H p).relIndex E ≤ p ^ 2 :=
          (relIndex_mul_le_odd hp hp2 hcomm hpow hEH hEp).trans hidx
        have hb : p ≤ (GroupTheory.HuppertProduct.mho H p).relIndex E := le_relIndex_of_not_le (hH.to_le hEH) hEM
        have hbc : (GroupTheory.HuppertProduct.mho H p).relIndex E * Nat.card ((GroupTheory.HuppertProduct.mho H p ⊓ E : Subgroup G)) = Nat.card E :=
          Subgroup.relIndex_mul_card _ _
        have ha1 : 0 < (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        have ha : (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) ≤ p := by
          have h1 : (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) * p ≤ p * p :=
            calc (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) * p
                ≤ (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) * (GroupTheory.HuppertProduct.mho H p).relIndex E :=
                  Nat.mul_le_mul_left _ hb
              _ ≤ p ^ 2 := hab
              _ = p * p := sq p
          exact Nat.le_of_mul_le_mul_right h1 hp.pos
        have hMcyc : IsCyclic (GroupTheory.HuppertProduct.mho H p) := isCyclic_of_relIndex_mho_le hMp ha
        have hcle : Nat.card ((GroupTheory.HuppertProduct.mho H p ⊓ E : Subgroup G)) ≤ p :=
          card_le_of_isCyclic hp.pos hMcyc inf_le_left (fun e he => hEp e he.2)
        rw [hE] at hbc
        have hb2 : p ^ 2 ≤ (GroupTheory.HuppertProduct.mho H p).relIndex E := by
          have h1 : p ^ 2 * p ≤ (GroupTheory.HuppertProduct.mho H p).relIndex E * p :=
            calc p ^ 2 * p = p ^ 3 := by ring
              _ = (GroupTheory.HuppertProduct.mho H p).relIndex E * Nat.card ((GroupTheory.HuppertProduct.mho H p ⊓ E : Subgroup G)) := hbc.symm
              _ ≤ (GroupTheory.HuppertProduct.mho H p).relIndex E * p := Nat.mul_le_mul_left _ hcle
          exact Nat.le_of_mul_le_mul_right h1 hp.pos
        have hbpos : 0 < (GroupTheory.HuppertProduct.mho H p).relIndex E := lt_of_lt_of_le (pow_pos hp.pos 2) hb2
        have ha_eq : (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) = 1 := by
          have h1 : (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) * (GroupTheory.HuppertProduct.mho H p).relIndex E ≤
              1 * (GroupTheory.HuppertProduct.mho H p).relIndex E :=
            calc (GroupTheory.HuppertProduct.mho (GroupTheory.HuppertProduct.mho H p) p).relIndex (GroupTheory.HuppertProduct.mho H p) * (GroupTheory.HuppertProduct.mho H p).relIndex E ≤ p ^ 2 := hab
              _ ≤ (GroupTheory.HuppertProduct.mho H p).relIndex E := hb2
              _ = 1 * (GroupTheory.HuppertProduct.mho H p).relIndex E := (one_mul _).symm
          exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hbpos) ha1
        have hMbot : GroupTheory.HuppertProduct.mho H p = ⊥ :=
          eq_bot_of_mho_eq_self hMp
            (le_antisymm (mho_le _ p) (Subgroup.relIndex_eq_one.1 ha_eq))
        have hc1 : Nat.card ((GroupTheory.HuppertProduct.mho H p ⊓ E : Subgroup G)) = 1 := by
          rw [hMbot, bot_inf_eq]
          exact Subgroup.card_bot
        rw [hc1, mul_one] at hbc
        rw [ha_eq] at hab
        have h23 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
        omega
  exact main _ H E rfl hH hidx hEH hEp

theorem card_ne_pow_three_of_product [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {W A B E : Subgroup G} (hW : IsPGroup p W) (hA : A ≤ W) (hB : B ≤ W) (hAc : IsCyclic A)
    (hBc : IsCyclic B) (hprod : ∀ w ∈ W, ∃ a ∈ A, ∃ b ∈ B, w = a * b) (hEW : E ≤ W)
    (hEp : ∀ e ∈ E, e ^ p = 1) : Nat.card E ≠ p ^ 3 :=
  card_ne_pow_three_of_relIndex_mho_le hp2 hW
    (relIndex_mho_le_of_mul_cyclic (p := p) (Fact.out : p.Prime).pos hA hB hAc hBc hprod) hEW hEp

end KHupOdd

theorem kHupAt_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KHupAt p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro X _ _ W A B hW hA hB hAc hBc hprod
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E hEW hE
  by_contra hlt
  have hlt : p ^ 2 < Nat.card E := not_le.mp hlt
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hp3 : p ^ 3 ∣ Nat.card E := by
    rw [hn] at hlt ⊢
    have h2n : 2 < n := by
      by_contra h
      have h' : n ≤ 2 := not_lt.mp h
      have : p ^ n ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos h'
      omega
    exact pow_dvd_pow p h2n
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hp3
  have hle : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
  have hE'card : Nat.card (K.map E.subtype) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  exact KHupOdd.card_ne_pow_three_of_product hp2 hW hA hB hAc hBc hprod (hle.trans hEW)
    (fun x hx => hE.2 x (hle hx)) hE'card

end CFSG.LocalAnalysis.RankThreeUC.S15
