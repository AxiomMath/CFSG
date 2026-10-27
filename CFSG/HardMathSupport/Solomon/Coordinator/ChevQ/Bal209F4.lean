module

public import CFSG.HardMathSupport.Dickson.Bal207.Corr
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace Bal209F4Aux

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

@[expose] def IsF4TwoIndex : TauCeti.LieTypeIndex → Prop
  | .F4 q => IsTwoPow q 1
  | _ => False

@[expose] def InnerAt {X : Type*} [Group X] (K : Subgroup X) (a : X) : Prop :=
  ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)

@[expose] def F4LocalOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K A : Subgroup X),
    CFSG.Open.IsComponentOf K ⊤ → IsLieQuot ↥K IsF4EightIndex →
      A ≤ Subgroup.normalizer (K : Set X) → CFSG.Open.IsElemAbelian 3 A →
        IsCompLocallyBalanced 3 1 A K

@[expose] def F4Fixed : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (a : X),
    CFSG.Open.IsComponentOf K ⊤ → IsLieQuot ↥K IsF4EightIndex →
      a ∈ Subgroup.normalizer (K : Set X) → a ^ 3 = 1 → ¬ InnerAt K a →
        IsSimpleGroup ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ∧
          CFSG.Open.IsQuasisimple ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ∧
          3 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ∧
          IsLieQuot ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) IsF4TwoIndex

@[expose] def F4InnerEx : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ (K B : Subgroup X), CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B →
      B ≤ Subgroup.normalizer (K : Set X) → GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B →
        IsLieQuot ↥K IsF4EightIndex →
          ∃ y ∈ B, InnerAt K y ∧ y ∉ Subgroup.centralizer (K : Set X)

section Glue

variable {X : Type} [Group X]

theorem innerAt_iff {K : Subgroup X} {a : X} :
    InnerAt K a ↔ ∃ k ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set X), a = k * c :=
  ⟨fun ⟨k, hk, hc⟩ => ⟨k, hk, k⁻¹ * a, hc, by group⟩,
    fun ⟨k, hk, c, hc, h⟩ => ⟨k, hk, by rw [h, inv_mul_cancel_left]; exact hc⟩⟩

@[expose] def innerSub (K : Subgroup X) : Subgroup X where
  carrier := {a | InnerAt K a}
  one_mem' := innerAt_iff.2 ⟨1, K.one_mem, 1, Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨k, hk, c, hc, rfl⟩ := innerAt_iff.1 ha
    obtain ⟨k', hk', c', hc', rfl⟩ := innerAt_iff.1 hb
    refine innerAt_iff.2 ⟨k * k', K.mul_mem hk hk', c * c', Subgroup.mul_mem _ hc hc', ?_⟩
    have hcm : c * k' = k' * c := (Subgroup.mem_centralizer_iff.1 hc k' hk').symm
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc c k', hcm, mul_assoc]
  inv_mem' := by
    intro a ha
    obtain ⟨k, hk, c, hc, rfl⟩ := innerAt_iff.1 ha
    have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.1 hc k hk
    refine innerAt_iff.2 ⟨k⁻¹, K.inv_mem hk, c⁻¹, Subgroup.inv_mem _ hc, ?_⟩
    rw [hkc, mul_inv_rev]

theorem mem_innerSub {K : Subgroup X} {a : X} : a ∈ innerSub K ↔ InnerAt K a := Iff.rfl

theorem mem_of_zpow_mem {H : Subgroup X} {g : X} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {j : ℤ}
    (hj : ¬ (3 : ℤ) ∣ j) (h : g ^ j ∈ H) : g ∈ H := by
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hjj : (j * j) % (orderOf g : ℤ) = 1 := by
    rw [hord]
    have h3 : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases h3 with h3 | h3 <;> simp [Int.mul_emod, h3]
  have hgg : g ^ (j * j) = g := by
    rw [← zpow_mod_orderOf, hjj, zpow_one]
  have : g = (g ^ j) ^ j := by rw [← zpow_mul, hgg]
  rw [this]
  exact H.zpow_mem h j

@[expose] def pairSub {x y : X} (hxy : Commute x y) : Subgroup X where
  carrier := {g | ∃ i j : ℤ, g = x ^ i * y ^ j}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    refine ⟨i + k, j + l, ?_⟩
    have h1 : y ^ j * x ^ k = x ^ k * y ^ j := ((hxy.zpow_zpow k j).eq).symm
    calc x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by group
      _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by rw [h1]
      _ = x ^ (i + k) * y ^ (j + l) := by simp only [zpow_add, mul_assoc]
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨-i, -j, ?_⟩
    have h1 : y ^ (-j) * x ^ (-i) = x ^ (-i) * y ^ (-j) := ((hxy.zpow_zpow (-i) (-j)).eq).symm
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact h1

theorem pairSub_le {B : Subgroup X} {x y : X} (hxy : Commute x y) (hxB : x ∈ B) (hyB : y ∈ B) :
    pairSub hxy ≤ B := by
  rintro g ⟨i, j, rfl⟩
  exact B.mul_mem (B.zpow_mem hxB i) (B.zpow_mem hyB j)

theorem isElemAbelian_pairSub {B : Subgroup X} {x y : X} (hxy : Commute x y)
    (hB : CFSG.Open.IsElemAbelian 3 B) (hxB : x ∈ B) (hyB : y ∈ B) :
    CFSG.Open.IsElemAbelian 3 (pairSub hxy) :=
  CFSG.Open.IsElemAbelian.mono hB (pairSub_le hxy hxB hyB)

theorem mem_pairSub {x y : X} {hxy : Commute x y} {g : X} :
    g ∈ pairSub hxy ↔ ∃ i j : ℤ, g = x ^ i * y ^ j := Iff.rfl

theorem not_isCyclic_pairSub {K B : Subgroup X} {x y : X} (hxy : Commute x y)
    (hB : CFSG.Open.IsElemAbelian 3 B) (hxB : x ∈ B) (hyB : y ∈ B) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxI : x ∉ innerSub K) (hyI : y ∈ innerSub K) :
    ¬ IsCyclic ↥(pairSub hxy) := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hxA : x ∈ pairSub hxy := mem_pairSub.2 ⟨1, 0, by simp⟩
  have hyA : y ∈ pairSub hxy := mem_pairSub.2 ⟨0, 1, by simp⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hxA⟩)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hyA⟩)
  have hxm : x = (g : X) ^ m := by
    have := congrArg Subtype.val hm
    simpa using this.symm
  have hyn : y = (g : X) ^ n := by
    have := congrArg Subtype.val hn
    simpa using this.symm
  have hGB : (g : X) ∈ B := pairSub_le hxy hxB hyB g.2
  have hG3 : (g : X) ^ 3 = 1 := hB.2 _ hGB
  have hG3z : (g : X) ^ (3 : ℤ) = 1 := by simpa using hG3
  have hG1 : (g : X) ≠ 1 := by
    intro h
    rw [h, one_zpow] at hxm
    exact hx1 hxm
  have hn3 : ¬ (3 : ℤ) ∣ n := by
    rintro ⟨k, rfl⟩
    apply hy1
    rw [hyn, zpow_mul, hG3z, one_zpow]
  have hGy : (g : X) ∈ Subgroup.zpowers y :=
    mem_of_zpow_mem hG3 hG1 hn3 (by rw [← hyn]; exact Subgroup.mem_zpowers y)
  have hxy' : x ∈ Subgroup.zpowers y := by
    rw [hxm]
    exact Subgroup.zpow_mem _ hGy m
  exact hxI (Subgroup.zpowers_le.2 hyI hxy')

theorem eq_one_of_mem_pairSub_centralizer {K : Subgroup X} {x y : X} (hxy : Commute x y)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxI : x ∉ innerSub K) (hyI : y ∈ innerSub K)
    (hyC : y ∉ Subgroup.centralizer (K : Set X)) {a : X} (ha : a ∈ pairSub hxy)
    (haC : a ∈ Subgroup.centralizer (K : Set X)) : a = 1 := by
  obtain ⟨i, j, rfl⟩ := mem_pairSub.1 ha
  have hx1 : x ≠ 1 := fun h => hxI (h ▸ (innerSub K).one_mem)
  have hy1 : y ≠ 1 := fun h => hyC (h ▸ (Subgroup.centralizer (K : Set X)).one_mem)
  have hxi : x ^ i ∈ innerSub K := by
    have h1 : x ^ i * y ^ j ∈ innerSub K :=
      mem_innerSub.2 (innerAt_iff.2 ⟨1, K.one_mem, x ^ i * y ^ j, haC, by simp⟩)
    have h2 : y ^ j ∈ innerSub K := (innerSub K).zpow_mem hyI j
    have h3 := (innerSub K).mul_mem h1 ((innerSub K).inv_mem h2)
    simpa using h3
  have hi3 : (3 : ℤ) ∣ i := by
    by_contra hi
    exact hxI (mem_of_zpow_mem hx3 hx1 hi hxi)
  obtain ⟨k, rfl⟩ := hi3
  have hx3z : x ^ (3 : ℤ) = 1 := by simpa using hx3
  have hx3k : x ^ (3 * k) = 1 := by rw [zpow_mul, hx3z, one_zpow]
  rw [hx3k, one_mul] at haC ⊢
  have hj3 : (3 : ℤ) ∣ j := by
    by_contra hj
    exact hyC (mem_of_zpow_mem hy3 hy1 hj haC)
  obtain ⟨l, rfl⟩ := hj3
  have hy3z : y ^ (3 : ℤ) = 1 := by simpa using hy3
  rw [zpow_mul, hy3z, one_zpow]

end Glue

section Transfer

variable {X : Type} [Group X]

theorem commute_of_elemAbelian {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 3 E) {g h : X}
    (hg : g ∈ E) (hh : h ∈ E) : Commute g h := by
  have := hE.1.is_comm.comm (⟨g, hg⟩ : E) ⟨h, hh⟩
  exact congrArg Subtype.val this

theorem isLieQuot_mono {Y : Type*} [Group Y] {P Q : TauCeti.LieTypeIndex → Prop}
    (h : IsLieQuot Y P) (hPQ : ∀ d, P d → Q d) : IsLieQuot Y Q := by
  obtain ⟨d, hd, hφ⟩ := h
  exact ⟨d, hPQ d.1 hd, hφ⟩

theorem isLieQuot_mulEquiv {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    {P : TauCeti.LieTypeIndex → Prop} (h : IsLieQuot Y P) : IsLieQuot Z P := by
  obtain ⟨d, hd, ⟨φ⟩⟩ := h
  exact ⟨d, hd, ⟨(QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Z) e
    (Subgroup.map_center_eq e)).symm.trans φ⟩⟩

theorem isF4Two_bal (d : TauCeti.LieTypeIndex) (hd : IsF4TwoIndex d) : Bal207Index 3 d := by
  cases d <;> simp_all [IsF4TwoIndex, Bal207Index]

theorem le_centralizer_of_elemAbelian {B : Subgroup X} {a : X} (hB : CFSG.Open.IsElemAbelian 3 B)
    (ha : a ∈ B) : B ≤ Subgroup.centralizer ({a} : Set X) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.1 hh]
  exact commute_of_elemAbelian hB ha hb

theorem isSCp_subgroupOf {B C : Subgroup X} (hBC : B ≤ C) (hB : IsSCp 3 ⊤ B) :
    IsSCp 3 ⊤ (B.subgroupOf C) := by
  have hBel := hB.2.1
  refine ⟨le_top, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact commute_of_elemAbelian hBel ((Subgroup.mem_subgroupOf).1 a.2)
      ((Subgroup.mem_subgroupOf).1 b.2)
  · apply Subtype.ext
    simpa using hBel.2 _ ((Subgroup.mem_subgroupOf).1 hx)
  · intro E _ hE hBE
    have hcomm : ∀ u ∈ E.map C.subtype, ∀ v ∈ E.map C.subtype, u * v = v * u := by
      intro u hu v hv
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hv
      exact congrArg Subtype.val (commute_of_elemAbelian hE ha hb)
    have hE' : CFSG.Open.IsElemAbelian 3 (E.map C.subtype) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, fun u hu => ?_⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
      rw [← map_pow, hE.2 a ha, map_one]
    have hBE' : B ≤ E.map C.subtype := by
      intro b hb
      have hbC : b ∈ C := hBC hb
      have hmem : (⟨b, hbC⟩ : ↥C) ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.2 hb
      exact Subgroup.mem_map.2 ⟨⟨b, hbC⟩, hBE hmem, rfl⟩
    have hEq : E.map C.subtype = B := hB.2.2 _ le_top hE' hBE'
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (x : X) ∈ E.map C.subtype := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      rw [hEq] at hx'
      exact hx'
    · intro hx
      have hx' : (x : X) ∈ E.map C.subtype := by rw [hEq]; exact hx
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx'
      have : a = x := Subtype.ext hax
      rw [← this]
      exact ha

theorem mem_normalizer_inf_centralizer {K : Subgroup X} {x w : X}
    (hwN : w ∈ Subgroup.normalizer (K : Set X)) (hxN : x ∈ Subgroup.normalizer (K : Set X))
    (hwx : ⁅w, x⁆ ∈ Subgroup.centralizer (K : Set X)) :
    w ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({x} : Set X) : Subgroup X) : Set X) := by
  have hc : ⁅w, x⁆⁻¹ ∈ Subgroup.centralizer (K : Set X) := inv_mem hwx
  set d : X := w⁻¹ * ⁅w, x⁆⁻¹ * w with hddef
  have hd : d ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : w * k * w⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hwN k).1 hk
    have h1 := Subgroup.mem_centralizer_iff.1 hc _ hk'
    calc k * d = w⁻¹ * ((w * k * w⁻¹) * ⁅w, x⁆⁻¹) * w := by rw [hddef]; group
      _ = w⁻¹ * (⁅w, x⁆⁻¹ * (w * k * w⁻¹)) * w := by rw [h1]
      _ = d * k := by rw [hddef]; group
  have hxw : w * (d * x) = x * w := by
    rw [hddef, commutatorElement_def]
    group
  have hkey : ∀ g ∈ K, x * (w * g * w⁻¹) * x⁻¹ = w * (x * g * x⁻¹) * w⁻¹ := by
    intro g hg
    have hxgx : x * g * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hxN g).1 hg
    have hdk : d * (x * g * x⁻¹) = (x * g * x⁻¹) * d :=
      (Subgroup.mem_centralizer_iff.1 hd _ hxgx).symm
    calc x * (w * g * w⁻¹) * x⁻¹ = (w * (d * x)) * g * (w * (d * x))⁻¹ := by rw [hxw]; group
      _ = w * (d * (x * g * x⁻¹) * d⁻¹) * w⁻¹ := by group
      _ = w * (x * g * x⁻¹) * w⁻¹ := by rw [hdk]; group
  rw [Subgroup.mem_normalizer_iff]
  intro g
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  constructor
  · rintro ⟨hgK, hgC⟩
    have hgC' : x * g = g * x := Subgroup.mem_centralizer_iff.1 hgC x (Set.mem_singleton x)
    have h2 : x * g * x⁻¹ = g := by rw [hgC']; group
    have h1 := hkey g hgK
    rw [h2] at h1
    refine ⟨(Subgroup.mem_normalizer_iff.1 hwN g).1 hgK, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
    rw [Set.mem_singleton_iff.1 hh]
    calc x * (w * g * w⁻¹) = (x * (w * g * w⁻¹) * x⁻¹) * x := by group
      _ = (w * g * w⁻¹) * x := by rw [h1]
  · rintro ⟨hwK, hwC⟩
    have gK : g ∈ K := (Subgroup.mem_normalizer_iff.1 hwN g).2 hwK
    have hwx' : x * (w * g * w⁻¹) = (w * g * w⁻¹) * x :=
      Subgroup.mem_centralizer_iff.1 hwC x (Set.mem_singleton x)
    have hconj : x * (w * g * w⁻¹) * x⁻¹ = w * g * w⁻¹ := by rw [hwx']; group
    have hA : w * (x * g * x⁻¹) * w⁻¹ = w * g * w⁻¹ := (hkey g gK).symm.trans hconj
    have hA' : x * g * x⁻¹ = g := mul_left_cancel (mul_right_cancel hA)
    have hgC' : x * g = g * x := by
      calc x * g = (x * g * x⁻¹) * x := by group
        _ = g * x := by rw [hA']
    exact ⟨gK, Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]; exact hgC')⟩

theorem exists_ne_one_of_isQuasisimple {G : Type*} [Group G]
    (h : CFSG.Open.IsQuasisimple G) : ∃ g : G, g ≠ 1 := by
  obtain ⟨-, hs⟩ := h
  haveI := hs
  obtain ⟨q, hq⟩ := exists_ne (1 : G ⧸ Subgroup.center G)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨g, fun hg => hq (by rw [hg]; rfl)⟩

theorem eq_of_glaPComponent {H J : Subgroup X} (hHs : IsSimpleGroup ↥H)
    (hJ : GLAPComponent 3 H J) : J = H := by
  obtain ⟨-, hsub, hIC, -⟩ := hJ
  have hne : J ≠ ⊥ := by
    intro hb
    obtain ⟨⟨g, hgL⟩, hg1⟩ := exists_ne_one_of_isQuasisimple hIC.2.2
    rw [hb, Subgroup.bot_subgroupOf, Subgroup.map_bot, Subgroup.mem_bot] at hgL
    exact hg1 (Subtype.ext hgL)
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub hHs with h | h
  · exact absurd h hne
  · exact h

theorem sLOB_of_bal207 [Finite X] (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) (hKG : CFSG.Open.IsKGroup X) {K B : Subgroup X} {a : X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hBSC : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (ha : a ∈ B)
    (hHq : CFSG.Open.IsQuasisimple ↥(K ⊓ Subgroup.centralizer ({a} : Set X)))
    (hHL : IsLieQuot ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) IsF4TwoIndex) :
    IsStronglyLocallyOneBalanced 3 B a (K ⊓ Subgroup.centralizer ({a} : Set X)) := by
  have hBel : CFSG.Open.IsElemAbelian 3 B := hBSC.2.1
  have hBC : B ≤ Subgroup.centralizer ({a} : Set X) := le_centralizer_of_elemAbelian hBel ha
  have hBH : ∀ b ∈ B, b ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X) := fun b hb =>
    mem_normalizer_inf_centralizer (hBN hb) (hBN ha) (by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (commute_of_elemAbelian hBel hb ha)]
      exact Subgroup.one_mem _)
  set C := Subgroup.centralizer ({a} : Set X) with hCdef
  set H := K ⊓ C with hHdef
  have hHC : H ≤ C := inf_le_right
  have hsubH : CFSG.Open.IsSubnormal H C := by
    have h1 := CFSG.Open.IsSubnormal.inf hK.2.1 C
    rwa [top_inf_eq] at h1
  have hsub' : CFSG.Open.IsSubnormal (H.subgroupOf C) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib ((CFSG.Open.IsSubnormal.iff_subgroupOf hHC).1 hsubH)
  have hq' : CFSG.Open.IsQuasisimple ↥(H.subgroupOf C) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHC) hHq
  have hcomp : CFSG.Open.IsComponentOf (H.subgroupOf C) ⊤ := ⟨le_top, hsub', hq'⟩
  have hSC' : IsSCp 3 ⊤ (B.subgroupOf C) := isSCp_subgroupOf hBC hBSC
  have hBN' : B.subgroupOf C ≤
      Subgroup.normalizer (((H.subgroupOf C : Subgroup ↥C)) : Set ↥C) := by
    intro b' hb'
    have hbB : (b' : X) ∈ B := Subgroup.mem_subgroupOf.1 hb'
    have hN := Subgroup.mem_normalizer_iff.1 (hBH _ hbB)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hLie : IsLieQuot ↥(H.subgroupOf C) IsF4TwoIndex :=
    isLieQuot_mulEquiv (Subgroup.subgroupOfEquivOfLe hHC).symm hHL
  have hbal := CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr.of_index h207 (hKG.subgroup C) Nat.prime_three (by decide) hcomp hSC'
    hBN' (fun d hd => ⟨isF4Two_bal d hd, by cases d <;> simp_all [IsF4TwoIndex, CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex]⟩)
    hLie
  intro S hS hcop hBS
  have hSC : S ≤ C := fun s hs => (Subgroup.mem_inf.1 (hS hs)).2
  have hS'N : S.subgroupOf C ≤
      Subgroup.normalizer (((H.subgroupOf C : Subgroup ↥C)) : Set ↥C) := by
    intro s' hs'
    have hsS : (s' : X) ∈ S := Subgroup.mem_subgroupOf.1 hs'
    have hsN : (s' : X) ∈ Subgroup.normalizer (H : Set X) := (Subgroup.mem_inf.1 (hS hsS)).1
    have hN := Subgroup.mem_normalizer_iff.1 hsN
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hcard : Nat.Coprime 3 (Nat.card (S.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]
    exact hcop
  have hB'N' : B.subgroupOf C ⊓
      Subgroup.normalizer (((H.subgroupOf C : Subgroup ↥C)) : Set ↥C) ≤
      Subgroup.normalizer (((S.subgroupOf C : Subgroup ↥C)) : Set ↥C) := by
    intro b' hb'
    have hb'B : b' ∈ B.subgroupOf C := (Subgroup.mem_inf.1 hb').1
    have hbB : (b' : X) ∈ B := Subgroup.mem_subgroupOf.1 hb'B
    have hbS : (b' : X) ∈ Subgroup.normalizer (S : Set X) :=
      hBS (Subgroup.mem_inf.2 ⟨hbB, hBH _ hbB⟩)
    have hN := Subgroup.mem_normalizer_iff.1 hbS
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hcent := hbal (S.subgroupOf C) hS'N hcard hB'N'
  refine Subgroup.commutator_le.2 (fun h hh s hs => ?_)
  have hcomm : h * s = s * h := by
    have hsC : (⟨s, hSC hs⟩ : ↥C) ∈ S.subgroupOf C := Subgroup.mem_subgroupOf.2 hs
    have hhC : (⟨h, hHC hh⟩ : ↥C) ∈ H.subgroupOf C := Subgroup.mem_subgroupOf.2 hh
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hcent hsC) _ hhC)
  rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
  exact Subgroup.one_mem _

end Transfer

end Bal209F4Aux

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
