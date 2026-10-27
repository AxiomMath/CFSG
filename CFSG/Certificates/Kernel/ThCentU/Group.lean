module

public import CFSG.Certificates.Kernel.ThCentU.Sound
public import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.ThCentU

open Finset

variable {G : Type*} [Group G]

@[expose] def phiG (r : ℕ → G) (e : ℕ → ℕ) : G := ((List.range 5).map fun i => r i ^ e i).prod

@[expose] def subR (r : ℕ → G) : Subgroup G := Subgroup.closure {x | ∃ i < 5, r i = x}

@[expose] noncomputable def row5 (a j : ℕ) : ℕ → ℕ := fun i => dig3 a (5 * j + i)

theorem mem_subR (r : ℕ → G) {i : ℕ} (hi : i < 5) : r i ∈ subR r :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem list_range_five : List.range 5 = [0, 1, 2, 3, 4] := by decide

theorem phiG_congr (r : ℕ → G) {e f : ℕ → ℕ} (h : ∀ i < 5, e i = f i) : phiG r e = phiG r f := by
  simp only [phiG, list_range_five, List.map_cons, List.map_nil]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num)]

theorem phiG_mem (r : ℕ → G) (e : ℕ → ℕ) : phiG r e ∈ subR r := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.pow_mem _ (mem_subR r (List.mem_range.1 hi)) _

theorem conj_phiG (r : ℕ → G) (g : G) (e : ℕ → ℕ) :
    g * phiG r e * g⁻¹ = ((List.range 5).map fun i => (g * r i * g⁻¹) ^ e i).prod := by
  have := map_list_prod (MulAut.conj g) ((List.range 5).map fun i => r i ^ e i)
  simp only [MulAut.conj_apply, List.map_map] at this
  rw [phiG, this]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp [conj_pow]

theorem list_map_prod5 {M : Type*} [CommGroup M] (ι : M → G) (h1 : ι 1 = 1)
    (hm : ∀ x y, ι (x * y) = ι x * ι y) (hp : ∀ x (n : ℕ), ι (x ^ n) = ι x ^ n) (x : ℕ → M)
    (e : ℕ → ℕ) :
    ((List.range 5).map fun i => ι (x i) ^ e i).prod = ι (∏ i ∈ range 5, x i ^ e i) := by
  simp only [list_range_five, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    prod_range_succ, prod_range_zero, hm, hp, h1, one_mul, mul_one, mul_assoc]

section Comm

variable (r : ℕ → G) (hc : ∀ i < 5, ∀ j < 5, r i * r j = r j * r i)
  (h3 : ∀ i < 5, r i ^ 3 = 1)
include hc

theorem subR_comm : ∀ x ∈ {x | ∃ i < 5, r i = x}, ∀ y ∈ {x | ∃ i < 5, r i = x},
    x * y = y * x := by
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  exact hc i hi j hj

theorem subR_pairwise : {x | ∃ i < 5, r i = x}.Pairwise Commute :=
  fun x hx y hy _ => subR_comm r hc x hx y hy

theorem subR_mul_comm (x y : subR r) : x * y = y * x := by
  let inst : CommGroup (subR r) := Subgroup.closureCommGroupOfComm (subR_pairwise r hc)
  exact inst.mul_comm x y

include h3

theorem phiG_lin (f : ℕ → ℕ → ℕ) (a : ℕ → ℕ) :
    ((List.range 5).map fun i => phiG r (f i) ^ a i).prod =
      phiG r (fun m => (∑ i ∈ range 5, a i * f i m) % 3) := by
  let inst : CommGroup (subR r) := Subgroup.closureCommGroupOfComm (subR_pairwise r hc)
  let ι : subR r → G := Subtype.val
  have h1 : ι 1 = 1 := rfl
  have hm : ∀ x y : subR r, ι (x * y) = ι x * ι y := fun _ _ => rfl
  have hp : ∀ (x : subR r) (n : ℕ), ι (x ^ n) = ι x ^ n := fun _ _ => rfl
  let ρ : ℕ → subR r := fun i => if h : i < 5 then ⟨r i, mem_subR r h⟩ else 1
  have hρ : ∀ i < 5, ι (ρ i) = r i := fun i hi => by
    simp only [ρ, dif_pos hi]
    rfl
  have hφ : ∀ e, phiG r e = ι (∏ i ∈ range 5, ρ i ^ e i) := by
    intro e
    refine Eq.trans ?_ (list_map_prod5 ι h1 hm hp ρ e)
    simp only [phiG, list_range_five, List.map_cons, List.map_nil]
    rw [hρ 0 (by norm_num), hρ 1 (by norm_num), hρ 2 (by norm_num), hρ 3 (by norm_num),
      hρ 4 (by norm_num)]
  simp only [hφ]
  refine (list_map_prod5 ι h1 hm hp (fun i => ∏ m ∈ range 5, ρ m ^ f i m) a).trans ?_
  congr 1
  have hmod : ∀ m ∈ range 5, ∀ n : ℕ, ρ m ^ n = ρ m ^ (n % 3) := by
    intro m hm n
    have h3' : ρ m ^ 3 = 1 := Subtype.ext (by
      have e := hρ m (mem_range.1 hm)
      change ((ρ m ^ 3 : subR r) : G) = 1
      rw [Subgroup.coe_pow]
      change (ι (ρ m)) ^ 3 = 1
      rw [e, h3 m (mem_range.1 hm)])
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h3', one_pow, one_mul]
  calc ∏ i ∈ range 5, (∏ m ∈ range 5, ρ m ^ f i m) ^ a i
      = ∏ i ∈ range 5, ∏ m ∈ range 5, ρ m ^ (f i m * a i) := prod_congr rfl fun i _ => by
        rw [← prod_pow]
        exact prod_congr rfl fun m _ => (pow_mul _ _ _).symm
    _ = ∏ m ∈ range 5, ∏ i ∈ range 5, ρ m ^ (f i m * a i) := prod_comm
    _ = ∏ m ∈ range 5, ρ m ^ (∑ i ∈ range 5, a i * f i m) := prod_congr rfl fun m _ => by
        rw [prod_pow_eq_pow_sum]
        congr 1
        exact sum_congr rfl fun i _ => Nat.mul_comm _ _
    _ = ∏ m ∈ range 5, ρ m ^ ((∑ i ∈ range 5, a i * f i m) % 3) :=
        prod_congr rfl fun m hm => hmod m hm _

end Comm

theorem phiG_inj_of (r : ℕ → G)
    (hK : ∀ x < 243, ∀ y < 243, phiG r (dig3 x) = phiG r (dig3 y) → x = y) {e f : ℕ → ℕ}
    (he : ∀ i < 5, e i < 3) (hf : ∀ i < 5, f i < 3) (h : phiG r e = phiG r f) :
    ∀ i < 5, e i = f i := by
  have key : ∀ g : ℕ → ℕ, (∀ i < 5, g i < 3) →
      g 0 + 3 * g 1 + 9 * g 2 + 27 * g 3 + 81 * g 4 < 243 ∧
        ∀ i < 5, dig3 (g 0 + 3 * g 1 + 9 * g 2 + 27 * g 3 + 81 * g 4) i = g i := by
    intro g hg
    have := hg 0 (by norm_num)
    have := hg 1 (by norm_num)
    have := hg 2 (by norm_num)
    have := hg 3 (by norm_num)
    have := hg 4 (by norm_num)
    refine ⟨by omega, fun i hi => ?_⟩
    interval_cases i <;> simp only [dig3_eq] <;> norm_num <;> omega
  obtain ⟨hx, dx⟩ := key e he
  obtain ⟨hy, dy⟩ := key f hf
  have e1 := phiG_congr r dx
  have e2 := phiG_congr r dy
  have := hK _ hx _ hy (by rw [e1, e2, h])
  intro i hi
  rw [← dx i hi, ← dy i hi, this]

variable [Finite G]

theorem centU_facts (u : G) (h r : ℕ → G) (GC E PA : ℕ → ℕ)
    (hR : ∀ i < 5, r i ∈ Subgroup.closure {x | ∃ l < 2, h l = x})
    (h3 : ∀ i < 5, r i ^ 3 = 1) (hc : ∀ i < 5, ∀ j < 5, r i * r j = r j * r i)
    (hA : ∀ l < 2, ∀ j < 5, h l * r j = phiG r (row5 (GC l) j) * h l)
    (hK : ∀ x < 243, ∀ y < 243, phiG r (dig3 x) = phiG r (dig3 y) → x = y)
    (hT : ∀ k < 720, node5 GC 2 E PA k = true) (hD : ∀ k < 720, ∀ m < 720, E k = E m → k = m)
    (hu : ∀ l < 2, u * h l = h l * u)
    (hle : Nat.card (Subgroup.centralizer ({u} : Set G)) ≤ 174960) :
    Nat.card (Subgroup.centralizer ({u} : Set G)) = 174960 ∧
      Subgroup.centralizer ({u} : Set G) = Subgroup.closure {x | ∃ l < 2, h l = x} ∧
      subR r ≤ Subgroup.centralizer ({u} : Set G) ∧
      (∀ x ∈ Subgroup.centralizer ({u} : Set G), ∀ y ∈ subR r, x * y * x⁻¹ ∈ subR r) ∧
      Nat.card (subR r) = 3 ^ 5 ∧
      ∀ x ∈ Subgroup.centralizer ({u} : Set G), (∀ y ∈ subR r, x * y = y * x) → x ∈ subR r := by
  set H := Subgroup.closure {x | ∃ l < 2, h l = x} with hH
  set C := Subgroup.centralizer ({u} : Set G)
  set R := subR r
  have hRH : R ≤ H := (Subgroup.closure_le H).2 fun _ ⟨i, hi, e⟩ => e ▸ hR i hi
  have hHC : H ≤ C := (Subgroup.closure_le C).2 fun _ ⟨l, hl, e⟩ => e ▸
    Subgroup.mem_centralizer_singleton_iff.2 (hu l hl).symm
  have hhH : ∀ l < 2, h l ∈ H := fun l hl => Subgroup.subset_closure ⟨l, hl, rfl⟩
  have hAc : ∀ l < 2, ∀ j < 5, h l * r j * (h l)⁻¹ = phiG r (row5 (GC l) j) := fun l hl j hj =>
    mul_inv_eq_of_eq_mul (hA l hl j hj)
  have htree : ∀ k < 720, E k < 3 ^ 25 ∧
      ∃ g ∈ H, ∀ j < 5, g * r j * g⁻¹ = phiG r (row5 (E k) j) := by
    refine tree_ind hT (fun z => z < 3 ^ 25 ∧ ∃ g ∈ H, ∀ j < 5, g * r j * g⁻¹ = phiG r (row5 z j))
      ?_ ?_
    · intro z hz
      obtain ⟨hlt, hd⟩ := one5_spec hz
      refine ⟨hlt, 1, H.one_mem, fun j hj => ?_⟩
      rw [one_mul, inv_one, mul_one]
      have e : ∀ i < 5, row5 z j i = if i = j then 1 else 0 := by
        intro i hi
        rw [row5, hd _ (by omega)]
        have e1 : (5 * j + i) / 5 = j := by omega
        have e2 : (5 * j + i) % 5 = i := by omega
        rw [e1, e2]
        by_cases hij : i = j
        · rw [if_pos hij.symm, if_pos hij]
        · rw [if_neg (Ne.symm hij), if_neg hij]
      rw [phiG_congr r e]
      simp only [phiG, list_range_five, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil]
      interval_cases j <;> simp
    · intro z a l hl ⟨_, g, hg, hga⟩ hz
      obtain ⟨hlt, hd⟩ := prod5_spec hz
      refine ⟨hlt, h l * g, H.mul_mem (hhH l hl) hg, fun j hj => ?_⟩
      have e1 : h l * g * r j * (h l * g)⁻¹ = h l * (g * r j * g⁻¹) * (h l)⁻¹ := by group
      rw [e1, hga j hj, conj_phiG]
      have e2 : ∀ i ∈ List.range 5, (h l * r i * (h l)⁻¹) ^ row5 a j i =
          phiG r (row5 (GC l) i) ^ row5 a j i := fun i hi => by
        rw [hAc l hl i (List.mem_range.1 hi)]
      rw [List.map_congr_left e2, phiG_lin r hc h3]
      refine phiG_congr r fun m hm => ?_
      rw [row5, hd _ (by omega), dot5_eq]
      have e3 : (5 * j + m) / 5 = j := by omega
      have e4 : (5 * j + m) % 5 = m := by omega
      rw [e3, e4]
      rfl
  choose! hEl g hgH hgE using htree
  set K : Subgroup ↥H := (Subgroup.centralizer (R : Set G)).subgroupOf H
  have hdist : ∀ k < 720, ∀ m < 720, (g k)⁻¹ * g m ∈ Subgroup.centralizer (R : Set G) → k = m := by
    intro k hk m hm hkm
    have hrow : ∀ j < 5, phiG r (row5 (E k) j) = phiG r (row5 (E m) j) := by
      intro j hj
      rw [← hgE k hk j hj, ← hgE m hm j hj]
      have hc' := Subgroup.mem_centralizer_iff.1 hkm (r j) (mem_subR r hj)
      have : g m * r j * (g m)⁻¹ = g k * ((g k)⁻¹ * g m * r j) * (g m)⁻¹ := by group
      rw [this, ← hc']
      group
    refine hD k hk m hm (eq_of_dig3 (n := 25) (hEl k hk) (hEl m hm) fun q hq => ?_)
    have := phiG_inj_of r hK (fun i _ => dig3_lt _ _) (fun i _ => dig3_lt _ _)
      (hrow (q / 5) (by omega)) (q % 5) (Nat.mod_lt _ (by norm_num))
    have e : dig3 (E k) (5 * (q / 5) + q % 5) = dig3 (E m) (5 * (q / 5) + q % 5) := this
    rwa [show 5 * (q / 5) + q % 5 = q by omega] at e
  have hidx : 720 ≤ K.index := by
    let F : Fin 720 → ↥H ⧸ K := fun k => (⟨g k, hgH k k.isLt⟩ : ↥H)
    have hF : Function.Injective F := by
      intro a b hab
      have := QuotientGroup.eq.1 hab
      exact Fin.ext (hdist a a.isLt b b.isLt this)
    have := Nat.card_le_card_of_injective F hF
    rw [Nat.card_eq_fintype_card (α := Fin 720), Fintype.card_fin] at this
    exact this
  have hR243 : 243 ≤ Nat.card R := by
    let F : Fin 243 → R := fun x => ⟨phiG r (dig3 x), phiG_mem r _⟩
    have hF : Function.Injective F := fun a b hab =>
      Fin.ext (hK a a.isLt b b.isLt (congrArg Subtype.val hab))
    simpa using Nat.card_le_card_of_injective F hF
  have hRK : R.subgroupOf H ≤ K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (subR_mul_comm r hc ⟨y, hy⟩ ⟨(x : G), hx⟩)
  have hRc : Nat.card (R.subgroupOf H) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hKR : Nat.card (R.subgroupOf H) ≤ Nat.card K := Subgroup.card_le_of_le hRK
  have hcard := Subgroup.card_mul_index K
  have hHle : Nat.card H ≤ 174960 := (Subgroup.card_le_of_le hHC).trans hle
  have hK243 : Nat.card K = 243 := by
    have h1 : Nat.card K * 720 ≤ Nat.card K * K.index := Nat.mul_le_mul_left _ hidx
    have h2 : Nat.card K * K.index ≤ 174960 := hcard ▸ hHle
    omega
  have hHcard : Nat.card H = 174960 := by
    have h1 : 243 * 720 ≤ 243 * K.index := Nat.mul_le_mul_left _ hidx
    rw [hK243] at hcard
    omega
  have hHeq : H = C := Subgroup.eq_of_le_of_card_ge hHC (by omega)
  have hRKeq : R.subgroupOf H = K := Subgroup.eq_of_le_of_card_ge hRK (by omega)
  have hRcard : Nat.card R = 243 := by omega
  have hnorm : ∀ l < 2, ∀ y ∈ R, h l * y * (h l)⁻¹ ∈ R := by
    intro l hl y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      rw [hAc l hl j hj]
      exact phiG_mem r _
    | one => simpa using R.one_mem
    | mul y z _ _ hy hz =>
      have : h l * (y * z) * (h l)⁻¹ = (h l * y * (h l)⁻¹) * (h l * z * (h l)⁻¹) := by group
      rw [this]
      exact R.mul_mem hy hz
    | inv y _ hy =>
      have : h l * y⁻¹ * (h l)⁻¹ = (h l * y * (h l)⁻¹)⁻¹ := by group
      rw [this]
      exact R.inv_mem hy
  have hnormH : H ≤ Subgroup.normalizer (R : Set G) := by
    refine (Subgroup.closure_le _).2 fun x ⟨l, hl, e⟩ => ?_
    subst e
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hnorm l hl y hy, fun hy => ?_⟩
    let f : R → R := fun z => ⟨h l * z * (h l)⁻¹, hnorm l hl z z.2⟩
    have hf : Function.Injective f := fun a b hab => Subtype.ext (by
      have e : h l * (a : G) * (h l)⁻¹ = h l * b * (h l)⁻¹ := congrArg Subtype.val hab
      simpa using e)
    obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hy⟩
    have := congrArg Subtype.val hz
    simp only [f] at this
    have : (z : G) = y := by simpa using this
    exact this ▸ z.2
  refine ⟨by rw [← hHeq, hHcard], hHeq.symm, hRH.trans hHC, fun x hx y hy => ?_,
    by rw [hRcard]; norm_num, fun x hx hxR => ?_⟩
  · rw [← hHeq] at hx
    exact (Subgroup.mem_normalizer_iff.1 (hnormH hx) y).1 hy
  · rw [← hHeq] at hx
    have hxK : (⟨x, hx⟩ : ↥H) ∈ K := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_centralizer_iff.2 fun y hy => (hxR y hy).symm
    rw [← hRKeq, Subgroup.mem_subgroupOf] at hxK
    exact hxK

end CFSG.KC.ThCentU

end
