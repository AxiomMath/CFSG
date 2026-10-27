module

import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG
public import CFSG.Walter.Bender1970.S3.Setup

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

section FourGroup

variable {G : Type*} [Group G] {A : Subgroup G}

theorem mul_self_eq_one (hA : IsElemAbelian 2 A) {x : G} (hx : x ∈ A) : x * x = 1 := by
  rw [← sq]
  exact hA.2 x hx

theorem comm (hA : IsElemAbelian 2 A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  CFSG.Open.IsElemAbelian.comm hA hx hy

theorem mem_four [Finite G] (hA : IsElemAbelian 2 A) (h4 : Nat.card A = 4) {a b x : G}
    (ha : a ∈ A) (hb : b ∈ A) (hx : x ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  have hab1 : a * b ≠ 1 := fun h => hab (by
    have := mul_self_eq_one hA ha
    calc a = a * (a * b) := by rw [h, mul_one]
      _ = b := by rw [← mul_assoc, this, one_mul])
  have haba : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habb : a * b ≠ b := fun h => ha1 (by simpa using h)
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hx1, hxa, hxb, hxab⟩ := hne
  have hsub : (({1, a, b, a * b, x} : Finset G) : Set G) ⊆ A := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact A.one_mem
    · exact ha
    · exact hb
    · exact A.mul_mem ha hb
    · exact hx
  have hcard : ({1, a, b, a * b, x} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using Ne.symm hxab
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm habb, Ne.symm hxb⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, Ne.symm haba, Ne.symm hxa⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hab1, Ne.symm hx1⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq] at hle
  change 5 ≤ Nat.card A at hle
  omega

end FourGroup

section Normalizer

variable {G : Type*} [Group G] {A : Subgroup G}

theorem conj_mem {n : G} (hn : n ∈ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A) :
    n * x * n⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp hn x).mp hx

theorem conj_ne_one {n x : G} (hx : x ≠ 1) : n * x * n⁻¹ ≠ 1 := fun h =>
  hx (by
    calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group)

theorem conj_injective {n x y : G} (h : n * x * n⁻¹ = n * y * n⁻¹) : x = y := by
  calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
    _ = n⁻¹ * (n * y * n⁻¹) * n := by rw [h]
    _ = y := by group

theorem mem_centralizer_of_forall {n : G} (h : ∀ x ∈ A, n * x * n⁻¹ = x) :
    n ∈ Subgroup.centralizer (A : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun x hx => by
    calc x * n = n * x * n⁻¹ * n := by rw [h x hx]
      _ = n * x := by group

theorem conj_eq_of_mem_centralizer {n : G} (hn : n ∈ Subgroup.centralizer (A : Set G)) {x : G}
    (hx : x ∈ A) : n * x * n⁻¹ = x := by
  rw [← Subgroup.mem_centralizer_iff.mp hn x hx, mul_inv_cancel_right]

end Normalizer

section Index

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem mem_centralizer_of_conj_eq (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {n : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hna : n * a * n⁻¹ = a) : n ∈ Subgroup.centralizer (A : Set G) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  by_contra hnc
  obtain ⟨b, hb, hnb⟩ : ∃ b ∈ A, n * b * n⁻¹ ≠ b := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hnc (mem_centralizer_of_forall h)
  have hA := hset.elem
  have hb1 : b ≠ 1 := fun h => hnb (by rw [h]; group)
  have hab : a ≠ b := fun h => hnb (h ▸ hna)
  have hcab : n * b * n⁻¹ = a * b := by
    rcases mem_four hA h4 ha hb (conj_mem hn hb) ha1 hb1 hab with h | h | h | h
    · exact absurd h (conj_ne_one hb1)
    · exact absurd (conj_injective (h.trans hna.symm)) (Ne.symm hab)
    · exact absurd h hnb
    · exact h
  have hcab' : n * (a * b) * n⁻¹ = b := by
    calc n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
      _ = a * (a * b) := by rw [hna, hcab]
      _ = b := by rw [← mul_assoc, mul_self_eq_one hA ha, one_mul]
  have hb' : b ≠ a * b := fun h => ha1 (by simpa using h.symm)
  let f : Subgroup.normalizer (A : Set G) →* ℤˣ :=
    Equiv.Perm.sign.comp ((MulAut.toPerm A).comp A.normalizerMonoidHom)
  have hperm : MulAut.toPerm A (A.normalizerMonoidHom ⟨n, hn⟩) =
      Equiv.swap ⟨b, hb⟩ ⟨a * b, A.mul_mem ha hb⟩ := by
    ext ⟨x, hx⟩
    change n * x * n⁻¹ = _
    rw [Equiv.swap_apply_def]
    have hab1 : a * b ≠ 1 := fun h => hab
      ((mul_eq_one_iff_eq_inv.mp h).trans (inv_eq_of_mul_eq_one_right (mul_self_eq_one hA hb)))
    rcases mem_four hA h4 ha hb hx ha1 hb1 hab with rfl | rfl | rfl | rfl
    · rw [ite_eq_right (fun h => hb1 (congrArg Subtype.val h).symm),
        ite_eq_right (fun h => hab1 (congrArg Subtype.val h).symm)]
      group
    · rw [ite_eq_right (fun h => hab (congrArg Subtype.val h)),
        ite_eq_right (fun h => hb1 (by simpa using (congrArg Subtype.val h).symm))]
      exact hna
    · rw [ite_eq_left rfl]
      exact hcab
    · rw [ite_eq_right (fun h => hb' (congrArg Subtype.val h).symm), ite_eq_left rfl]
      exact hcab'
  have hfn : f ⟨n, hn⟩ = -1 := by
    change Equiv.Perm.sign (MulAut.toPerm A (A.normalizerMonoidHom ⟨n, hn⟩)) = -1
    rw [hperm]
    exact Equiv.Perm.sign_swap (fun h => hb' (congrArg Subtype.val h))
  have hrange : f.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact f.range.one_mem
    · exact ⟨_, hfn⟩
  have hidx : f.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  refine hset.noIndexTwo (f.ker.map (Subgroup.normalizer (A : Set G)).subtype)
    (Subgroup.map_subtype_le _) ?_
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  exact hidx

theorem conj_conj_eq_mul (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {n : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) (hnc : n ∉ Subgroup.centralizer (A : Set G))
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    n * a * n⁻¹ ≠ a ∧ n * (n * a * n⁻¹) * n⁻¹ = a * (n * a * n⁻¹) := by
  have hA := hset.elem
  have hca : n * a * n⁻¹ ≠ a := fun h => hnc (mem_centralizer_of_conj_eq hset h4 hn ha ha1 h)
  refine ⟨hca, ?_⟩
  set c := n * a * n⁻¹ with hc
  have hcA : c ∈ A := conj_mem hn ha
  have hc1 : c ≠ 1 := conj_ne_one ha1
  rcases mem_four hA h4 ha hcA (conj_mem hn hcA) ha1 hc1 (Ne.symm hca) with h | h | h | h
  · exact absurd h (conj_ne_one hc1)
  · exfalso
    refine hnc (mem_centralizer_of_conj_eq hset h4 hn (A.mul_mem ha hcA) ?_ ?_)
    · intro h'
      exact hca (by
        calc c = a * (a * c) := by rw [← mul_assoc, mul_self_eq_one hA ha, one_mul]
          _ = a := by rw [h', mul_one])
    · calc n * (a * c) * n⁻¹ = (n * a * n⁻¹) * (n * c * n⁻¹) := by group
        _ = c * a := by rw [← hc, h]
        _ = a * c := comm hA hcA ha
  · exact absurd (conj_injective (h.trans hc)) hca
  · exact h

theorem pow_three_mem_centralizer (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {n : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) : n ^ 3 ∈ Subgroup.centralizer (A : Set G) := by
  by_cases hnc : n ∈ Subgroup.centralizer (A : Set G)
  · exact Subgroup.pow_mem _ hnc 3
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hset.ne_bot (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx))
  have hA := hset.elem
  obtain ⟨hca, hcc⟩ := conj_conj_eq_mul hset h4 hn hnc haA ha1
  obtain ⟨c, hc⟩ : ∃ c, n * a * n⁻¹ = c := ⟨_, rfl⟩
  rw [hc] at hca hcc
  have hcA : c ∈ A := hc ▸ conj_mem hn haA
  refine mem_centralizer_of_conj_eq hset h4 (Subgroup.pow_mem _ hn 3) haA ha1 ?_
  have e1 : n ^ 3 * a * (n ^ 3)⁻¹ = n * (n * (n * a * n⁻¹) * n⁻¹) * n⁻¹ := by
    rw [pow_three]; group
  have e2 : n * (a * c) * n⁻¹ = (n * a * n⁻¹) * (n * c * n⁻¹) := by group
  rw [e1, hc, hcc, e2, hc, hcc, ← mul_assoc, comm hA hcA haA, mul_assoc,
    mul_self_eq_one hA hcA, mul_one]

theorem mem_centralizer_of_pow_two (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {n : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) {k : ℕ} (hk : n ^ (2 ^ k) = 1) :
    n ∈ Subgroup.centralizer (A : Set G) := by
  let φ : Subgroup.normalizer (A : Set G) →* Equiv.Perm A :=
    (MulAut.toPerm A).comp A.normalizerMonoidHom
  have h3 : φ ⟨n, hn⟩ ^ 3 = 1 := by
    rw [← map_pow]
    ext ⟨x, hx⟩
    exact conj_eq_of_mem_centralizer (pow_three_mem_centralizer hset h4 hn) hx
  have h2 : φ ⟨n, hn⟩ ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨n, hn⟩ : Subgroup.normalizer (A : Set G)) ^ (2 ^ k) = 1 := Subtype.ext hk
    rw [this, map_one]
  have h1 : φ ⟨n, hn⟩ = 1 :=
    (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_right k (by norm_num))).mp ⟨h3, h2⟩
  refine mem_centralizer_of_forall fun x hx => ?_
  have := congrArg (fun σ : Equiv.Perm A => ((σ ⟨x, hx⟩ : A) : G)) h1
  exact this

theorem exists_mem_ne_one (hset : GoldSetting G S A) : ∃ a ∈ A, a ≠ 1 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact hset.ne_bot (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx))

theorem exists_not_mem_centralizer (hset : GoldSetting G S A) (h4 : Nat.card A = 4) :
    ∃ n ∈ Subgroup.normalizer (A : Set G), n ∉ Subgroup.centralizer (A : Set G) := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hset
  have hle : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
  have hN : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := fun n hn =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hle (h n hn))
  rcases hset.irreducible _ hle hN with h1 | h1
  · exact ha1 (Subgroup.zpowers_eq_bot.mp h1)
  · have h2 : Nat.card A = 2 := by
      rw [← h1, Nat.card_zpowers, orderOf_eq_prime (hset.elem.2 a ha) ha1]
    omega

theorem exists_conj_eq (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (A : Set G), n * a * n⁻¹ = b := by
  obtain ⟨x, hx, hxc⟩ := exists_not_mem_centralizer hset h4
  obtain ⟨hca, hcc⟩ := conj_conj_eq_mul hset h4 hx hxc ha ha1
  rcases mem_four hset.elem h4 ha (conj_mem hx ha) hb ha1 (conj_ne_one ha1) (Ne.symm hca) with
    h | h | h | h
  · exact absurd h hb1
  · exact ⟨1, Subgroup.one_mem _, by rw [h]; group⟩
  · exact ⟨x, hx, h.symm⟩
  · refine ⟨x * x, Subgroup.mul_mem _ hx hx, ?_⟩
    rw [h, ← hcc]
    group

theorem normalizer_le (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {X : Subgroup G}
    (hCX : Subgroup.centralizer (A : Set G) ≤ X) {x : G} (hxX : x ∈ X)
    (hx : x ∈ Subgroup.normalizer (A : Set G)) (hxc : x ∉ Subgroup.centralizer (A : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ X := by
  intro m hm
  obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hset
  obtain ⟨hca, hcc⟩ := conj_conj_eq_mul hset h4 hx hxc ha ha1
  have hfix : ∀ y ∈ X, y⁻¹ * m ∈ Subgroup.normalizer (A : Set G) →
      (y⁻¹ * m) * a * (y⁻¹ * m)⁻¹ = a → m ∈ X := fun y hy hyN hya => by
    have := hCX (mem_centralizer_of_conj_eq hset h4 hyN ha ha1 hya)
    simpa using X.mul_mem hy this
  have hxN : x⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hx
  rcases mem_four hset.elem h4 ha (conj_mem hx ha) (conj_mem hm ha) ha1 (conj_ne_one ha1)
    (Ne.symm hca) with h | h | h | h
  · exact absurd h (conj_ne_one ha1)
  · exact hfix 1 X.one_mem (by simpa using hm) (by simpa using h)
  · refine hfix x hxX (Subgroup.mul_mem _ hxN hm) ?_
    calc x⁻¹ * m * a * (x⁻¹ * m)⁻¹ = x⁻¹ * (m * a * m⁻¹) * x := by group
      _ = a := by rw [h]; group
  · refine hfix (x * x) (X.mul_mem hxX hxX) ?_ ?_
    · rw [mul_inv_rev]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hxN) hm
    · calc (x * x)⁻¹ * m * a * ((x * x)⁻¹ * m)⁻¹ = x⁻¹ * (x⁻¹ * (m * a * m⁻¹) * x) * x := by
            simp only [mul_inv_rev, inv_inv, mul_assoc]
        _ = a := by rw [h, ← hcc]; group

theorem le_normalizer (hset : GoldSetting G S A) :
    (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hset.le).mp
    (normal_subgroupOf_of_stronglyClosed hset.le hset.closed)

theorem le_centralizer (hset : GoldSetting G S A) (h4 : Nat.card A = 4) :
    (S : Subgroup G) ≤ Subgroup.centralizer (A : Set G) := fun s hs => by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
  exact mem_centralizer_of_pow_two hset h4 (le_normalizer hset hs)
    (by simpa using congrArg Subtype.val hk)

theorem pGroup_le_centralizer (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {R : Subgroup G}
    (hR : IsPGroup 2 R) (hAR : A ≤ R) : R ≤ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hRQ, hQ⟩ := stronglyClosed_of_le_pGroup S hset.closed hR hAR
  have hQN : (Q : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hAR.trans hRQ)).mp
      (normal_subgroupOf_of_stronglyClosed (hAR.trans hRQ) hQ)
  intro r hr
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  exact mem_centralizer_of_pow_two hset h4 (hQN (hRQ hr)) (by simpa using congrArg Subtype.val hk)

theorem sstar_of_le (hset : GoldSetting G S A) {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H) :
    IsSStarIn H A := by
  obtain ⟨g, hle, hs⟩ := hset.sstar H hH
  have hAH' : A ⊓ H = A := inf_eq_left.mpr hAH
  rw [hAH'] at hle
  have heq : conjSub g A = A :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])).symm
  rwa [heq, hAH'] at hs

theorem false_of_centralizer_le (hset : GoldSetting G S A) {X : Subgroup G} (hX : X ≠ ⊤)
    (h : ∀ b ∈ A, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ X) : False := by
  apply hX
  rw [eq_top_iff, ← hset.gen]
  exact iSup_le fun b => h b.1 b.2.1 b.2.2

theorem false_of_normalizer_le (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {X : Subgroup G}
    (hX : X ≠ ⊤) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hCX : Subgroup.centralizer ({a} : Set G) ≤ X)
    (hNX : Subgroup.normalizer (A : Set G) ≤ X) : False := by
  refine false_of_centralizer_le hset hX fun b hb hb1 => ?_
  obtain ⟨n, hn, rfl⟩ := exists_conj_eq hset h4 ha hb ha1 hb1
  rw [← Walter.map_conj_centralizer_singleton]
  rintro _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact X.mul_mem (X.mul_mem (hNX hn) (hCX hy)) (X.inv_mem (hNX hn))

theorem centralizer_ne_top (hset : GoldSetting G S A) {a : G} (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
  intro h
  have := hset.isSimpleGroup
  have hZ := PropHSetup.center_eq_bot hset.nonabelian
  have haZ : a ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (h ▸ Subgroup.mem_top g)
  rw [hZ] at haZ
  exact ha1 (Subgroup.mem_bot.mp haZ)

theorem le_centralizer_singleton (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G}
    (ha : a ∈ A) : (S : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) :=
  (le_centralizer hset h4).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))

theorem le_of_mem_benderM (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A)
    {H : Subgroup G} (hH : H ∈ Walter.benderM a) : (S : Subgroup G) ≤ H :=
  (le_centralizer_singleton hset h4 ha).trans (Walter.centralizer_le_of_mem_benderM hH)

theorem sstar_of_mem_benderM (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G}
    (ha : a ∈ A) {H : Subgroup G} (hH : H ∈ Walter.benderM a) : IsSStarIn H A :=
  sstar_of_le hset (Walter.ne_top_of_mem_benderM hH)
    (hset.le.trans (le_of_mem_benderM hset h4 ha hH))

end Index

end CFSG.Goldschmidt.Sec8
