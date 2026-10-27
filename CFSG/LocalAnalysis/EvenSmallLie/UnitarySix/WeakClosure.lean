module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Transfer
public import CFSG.LocalAnalysis.EvenSmallLie.StandardForm
public import CFSG.LocalAnalysis.EvenSmallLie.FoursGroup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix

open Subgroup CFSG.Quasithin
open SolomonWong (mul_comm_of_sq_eq_one card_conjSubgroup conjSubgroup_sq)

variable {G : Type*} [Group G]

theorem exists_normalizer_conj_eq {E : Subgroup G} {t : G}
    (hEc : ∀ b ∈ E, ∀ c ∈ E, b * c = c * b)
    (hsyl : ∀ g : G, conjSubgroup E g ≤ centralizer {t} →
      ∃ h ∈ centralizer {t}, conjSubgroup E g = conjSubgroup E h)
    {g : G} (hg : g⁻¹ * t * g ∈ E) :
    ∃ n ∈ normalizer (E : Set G), g⁻¹ * t * g = n⁻¹ * t * n := by
  have hle : conjSubgroup E g⁻¹ ≤ centralizer {t} := by
    intro y hy
    rw [mem_conjSubgroup_iff, inv_inv] at hy
    have hc := hEc _ hy _ hg
    rw [mem_centralizer_singleton_iff]
    calc y * t = g * ((g⁻¹ * y * g) * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
      _ = t * y := by group
  obtain ⟨h, hh, heq⟩ := hsyl g⁻¹ hle
  have hN : g⁻¹ * h⁻¹ ∈ normalizer (E : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, heq,
      conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  refine ⟨(g⁻¹ * h⁻¹)⁻¹, inv_mem hN, ?_⟩
  have hht : h * t = t * h := mem_centralizer_singleton_iff.1 hh
  calc g⁻¹ * t * g = g⁻¹ * (h⁻¹ * (h * t)) * g := by group
    _ = g⁻¹ * (h⁻¹ * (t * h)) * g := by rw [hht]
    _ = (g⁻¹ * h⁻¹)⁻¹⁻¹ * t * (g⁻¹ * h⁻¹)⁻¹ := by group

theorem conjSubgroup_le_of_rank [Finite G] {t : G} {L F E : Subgroup G} {r : ℕ}
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) (hEcard : Nat.card E = 2 ^ r)
    (hrank : ∀ τ ∈ centralizer {t}, orderOf τ = 2 → τ ∉ F → ∀ B : Subgroup G,
      B ≤ centralizer {t} ⊓ centralizer {τ} → (∀ b ∈ B, b ^ 2 = 1) → Nat.card B < 2 ^ r)
    (hinv : ∀ y ∈ F, y ^ 2 = 1 → y ∈ L) {g : G} (hg : conjSubgroup E g ≤ centralizer {t}) :
    conjSubgroup E g ≤ L := by
  intro y hy
  have hy2 := conjSubgroup_sq hE2 g y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact L.one_mem
  have hord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  by_contra hyL
  have hyF : y ∉ F := fun h => hyL (hinv y h hy2)
  have hle : conjSubgroup E g ≤ centralizer {t} ⊓ centralizer {y} := by
    refine le_inf hg fun z hz => mem_centralizer_singleton_iff.2 ?_
    exact mul_comm_of_sq_eq_one (conjSubgroup_sq hE2 g) hz hy
  have h := hrank y (hg hy) hord hyF _ hle (conjSubgroup_sq hE2 g)
  rw [card_conjSubgroup, hEcard] at h
  exact lt_irrefl _ h

theorem exists_eq_mul_of_conj {L H E : Subgroup G}
    (hcl : ∀ h ∈ H, ∃ l ∈ L, conjSubgroup E h = conjSubgroup E l) {h : G} (hh : h ∈ H) :
    ∃ l ∈ L, ∃ n ∈ normalizer (E : Set G), h = l * n := by
  obtain ⟨l, hl, heq⟩ := hcl h⁻¹ (inv_mem hh)
  have hN : h⁻¹ * l⁻¹ ∈ normalizer (E : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, heq,
      conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  refine ⟨l⁻¹, inv_mem hl, (h⁻¹ * l⁻¹)⁻¹, inv_mem hN, by group⟩

theorem relIndex_eq_of_forall_eq_mul {N L H : Subgroup G} (hLH : L ≤ H)
    (hmul : ∀ h ∈ H, ∃ l ∈ L, ∃ n ∈ N, h = l * n) : N.relIndex H = N.relIndex L := by
  have hstab : ∀ K : Subgroup G,
      MulAction.stabilizer K ((1 : G) : G ⧸ N) = N.subgroupOf K := by
    intro K
    ext k
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, Subgroup.smul_def,
      CFSG.Monster.B.Recog.TransferExtremal.smul_coe_eq_iff_conj_mem]
    simp
  have horb : MulAction.orbit H ((1 : G) : G ⧸ N) = MulAction.orbit L ((1 : G) : G ⧸ N) := by
    ext q
    constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩
      obtain ⟨l, hl, n, hn, rfl⟩ := hmul h hh
      refine ⟨⟨l, hl⟩, ?_⟩
      show (l : G) • ((1 : G) : G ⧸ N) = (l * n) • ((1 : G) : G ⧸ N)
      rw [mul_smul]
      congr 1
      rw [eq_comm, CFSG.Monster.B.Recog.TransferExtremal.smul_coe_eq_iff_conj_mem]
      simpa using hn
    · rintro ⟨⟨l, hl⟩, rfl⟩
      exact ⟨⟨l, hLH hl⟩, rfl⟩
  rw [relIndex, relIndex, ← hstab, ← hstab, MulAction.index_stabilizer,
    MulAction.index_stabilizer, horb]

theorem exists_conj_mem_of_odd_relIndex [Finite G] {N H : Subgroup G}
    (hodd : Odd (N.relIndex H)) {y : G} (hy : y ∈ H) (hy2 : y ^ 2 = 1) :
    ∃ h ∈ H, h⁻¹ * y * h ∈ N := by
  have hcong := CFSG.Monster.B.Recog.card_modEq_card_fixedBy
    (α := H ⧸ N.subgroupOf H) (t := (⟨y, hy⟩ : H)) (Subtype.ext (by simpa using hy2))
  have hne : Nat.card (MulAction.fixedBy (H ⧸ N.subgroupOf H) (⟨y, hy⟩ : H)) ≠ 0 := by
    intro h0
    rw [h0] at hcong
    have h2 : 2 ∣ Nat.card (H ⧸ N.subgroupOf H) := Nat.modEq_zero_iff_dvd.1 hcong
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  obtain ⟨⟨q, hq⟩⟩ := (Nat.card_ne_zero.1 hne).1
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 := (CFSG.Monster.B.Recog.TransferExtremal.smul_coe_eq_iff_conj_mem
    (N.subgroupOf H) ⟨y, hy⟩ h).1 hq
  rw [mem_subgroupOf] at h1
  exact ⟨h, h.2, by simpa using h1⟩

theorem mem_of_odd_orderOf {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) {y : G} (hy : y ∈ M)
    (hodd : Odd (orderOf y)) : y ∈ M₁ := by
  obtain ⟨k, hk⟩ := hodd
  have hsq := SolomonWong.mul_self_mem_of_relIndex_two hM₁ hy
  have e : y = (y * y) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e]
  exact pow_mem hsq _

theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  index_ne_zero_of_finite

theorem card_ne_two_of_nonabelian [Finite G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Nat.card G ≠ 2 := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : IsCyclic G := isCyclic_of_prime_card h
  obtain ⟨a, b, hab⟩ := hnonab
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 (hg a)
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 (hg b)
  exact hab (zpow_mul_comm g i j)

structure DavisSolomonFacts (G : Type*) [Group G] (t : G) (L E : Subgroup G) : Prop where
  le_centralizer : L ≤ centralizer {t}
  centralizer_le : centralizer {t} ≤ normalizer (L : Set G)
  E_le : E ≤ L
  E_sq : ∀ e ∈ E, e ^ 2 = 1
  card_E : Nat.card E = 2 ^ 10
  rank : ∀ τ ∈ centralizer {t}, orderOf τ = 2 → τ ∉ L ⊔ centralizer (L : Set G) →
    ∀ B : Subgroup G, B ≤ centralizer {t} ⊓ centralizer {τ} → (∀ b ∈ B, b ^ 2 = 1) →
      Nat.card B ≤ 2 ^ 8
  inv : ∀ y ∈ L ⊔ centralizer (L : Set G), y ^ 2 = 1 → y ∈ L
  conj_class : ∀ B : Subgroup G, B ≤ L → (∀ b ∈ B, b ^ 2 = 1) → Nat.card B = 2 ^ 10 →
    ∃ l ∈ L, B = conjSubgroup E l
  fuse : ∀ s ∈ L, orderOf s = 2 → ∃ l ∈ L, l⁻¹ * s * l ∈ E
  gen : normalizer (E : Set G) ⊓ L ≤
    E ⊔ closure {y | y ∈ normalizer (E : Set G) ⊓ L ∧ Odd (orderOf y)}
  odd_index : Odd ((normalizer (E : Set G)).relIndex L)
  unique : ∀ B : Subgroup G, B ≤ normalizer (E : Set G) ⊓ L → (∀ b ∈ B, b ^ 2 = 1) →
    Nat.card B = 2 ^ 10 → B = E
  outer : (L ⊔ centralizer (L : Set G)).relIndex (centralizer {t}) ≤ 2

namespace DavisSolomonFacts

variable {t : G} {L E : Subgroup G}

theorem E_comm (D : DavisSolomonFacts G t L E) : ∀ b ∈ E, ∀ c ∈ E, b * c = c * b :=
  fun _ hb _ hc => mul_comm_of_sq_eq_one D.E_sq hb hc

theorem conjSubgroup_le [Finite G] (D : DavisSolomonFacts G t L E) {g : G}
    (hg : conjSubgroup E g ≤ centralizer {t}) : conjSubgroup E g ≤ L :=
  conjSubgroup_le_of_rank D.E_sq D.card_E (fun τ hτ h2 hF B hB hB2 =>
    (D.rank τ hτ h2 hF B hB hB2).trans_lt (by norm_num)) D.inv hg

theorem sylowType [Finite G] (D : DavisSolomonFacts G t L E) (g : G)
    (hg : conjSubgroup E g ≤ centralizer {t}) :
    ∃ h ∈ centralizer {t}, conjSubgroup E g = conjSubgroup E h := by
  obtain ⟨l, hl, heq⟩ := D.conj_class _ (D.conjSubgroup_le hg) (conjSubgroup_sq D.E_sq g)
    (by rw [card_conjSubgroup, D.card_E])
  exact ⟨l, D.le_centralizer hl, heq⟩

theorem fusion [Finite G] (D : DavisSolomonFacts G t L E) {g : G} (hg : g⁻¹ * t * g ∈ E) :
    ∃ n ∈ normalizer (E : Set G), g⁻¹ * t * g = n⁻¹ * t * n :=
  exists_normalizer_conj_eq D.E_comm D.sylowType hg

theorem exists_eq_mul (D : DavisSolomonFacts G t L E) {h : G} (hh : h ∈ centralizer {t}) :
    ∃ l ∈ L, ∃ n ∈ normalizer (E : Set G), h = l * n := by
  refine exists_eq_mul_of_conj (fun h hh => ?_) hh
  have hEh : conjSubgroup E h ≤ L := by
    have h1 : conjSubgroup E h ≤ conjSubgroup L h := map_mono D.E_le
    rwa [conjSubgroup_eq_iff_mem_normalizer.2 (D.centralizer_le hh)] at h1
  exact D.conj_class _ hEh (conjSubgroup_sq D.E_sq h) (by rw [card_conjSubgroup, D.card_E])

open SolomonWong in
theorem exists_normalizer_conj_ne [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (D : DavisSolomonFacts G t L E) (ht : orderOf t = 2) :
    ∃ n ∈ normalizer (E : Set G), n⁻¹ * t * n ≠ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  set N := normalizer (E : Set G)
  set F := L ⊔ centralizer (L : Set G)
  have hNH : N ≤ centralizer {t} := fun n hn => by
    rw [mem_centralizer_singleton_iff]
    calc n * t = n * (n⁻¹ * t * n) := by rw [hcon n hn]
      _ = t * n := by group
  have hG2 : ∀ K : Subgroup G, K.index ≠ 2 :=
    index_ne_two_of_isSimpleGroup (card_ne_two_of_nonabelian hnonab)
  have hwc : ∀ g : G, conjSubgroup E g ≤ N → conjSubgroup E g = E := fun g hg =>
    D.unique _ (le_inf hg (D.conjSubgroup_le (hg.trans hNH))) (conjSubgroup_sq D.E_sq g)
      (by rw [card_conjSubgroup, D.card_E])
  have hsyl : ∀ g : G, conjSubgroup E g ≤ N → ∃ m ∈ N, conjSubgroup E g = conjSubgroup E m :=
    fun g hg => ⟨1, one_mem _, by rw [hwc g hg, conjSubgroup_one]⟩
  have hno2 : ∀ M₁ : Subgroup G, M₁ ≤ N → M₁.relIndex N ≠ 2 := by
    intro M₁ hM₁N
    refine relIndex_ne_two_of_rank hG2 D.E_sq hsyl (fun M₁ hM₁N hM₁ hEM₁ B hBN hBsq hnle => ?_)
      hM₁N
    rw [D.card_E]
    obtain ⟨τ, hτB, hτM₁⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
    have hτ2 := hBsq τ hτB
    have hτ1 : τ ≠ 1 := fun h => hτM₁ (h ▸ M₁.one_mem)
    by_cases hτF : τ ∈ F
    ·
      exfalso
      apply hτM₁
      have hτNL : τ ∈ N ⊓ L := ⟨hBN hτB, D.inv τ hτF hτ2⟩
      refine sup_le hEM₁ ((closure_le _).2 fun y hy => ?_) (D.gen hτNL)
      exact mem_of_odd_orderOf hM₁ hy.1.1 hy.2
    ·
      have hBle : B ≤ centralizer {t} ⊓ centralizer {τ} := by
        refine le_inf (hBN.trans hNH) fun b hb => mem_centralizer_singleton_iff.2 ?_
        exact mul_comm_of_sq_eq_one hBsq hb hτB
      have h8 := D.rank τ (hNH (hBN hτB)) (orderOf_eq_prime hτ2 hτ1) hτF B hBle hBsq
      omega
  have hNF : N ≤ F := by
    have hle : F.relIndex N ≤ 2 :=
      (relIndex_le_of_le_right hNH (relIndex_ne_zero_of_finite _ _)).trans D.outer
    have hne0 : F.relIndex N ≠ 0 := relIndex_ne_zero_of_finite _ _
    have hne2 : F.relIndex N ≠ 2 := by
      have := hno2 (F ⊓ N) inf_le_right
      rwa [inf_relIndex_right] at this
    exact relIndex_eq_one.1 (by omega)
  have hstep4 : ∀ g : G, g⁻¹ * t * g ∈ N → g⁻¹ * t * g = t := by
    intro g hg
    have hs2 : (g⁻¹ * t * g) ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, orderOf_conj_eq, ht]
    have hsL := D.inv _ (hNF hg) hs2
    obtain ⟨l, hl, hlE⟩ := D.fuse _ hsL (by rw [orderOf_conj_eq, ht])
    have e : l⁻¹ * (g⁻¹ * t * g) * l = (g * l)⁻¹ * t * (g * l) := by group
    rw [e] at hlE
    obtain ⟨n, hn, hgn⟩ := D.fusion hlE
    rw [hcon n hn] at hgn
    have hlt : l * t = t * l := mem_centralizer_singleton_iff.1 (D.le_centralizer hl)
    calc g⁻¹ * t * g = l * ((g * l)⁻¹ * t * (g * l)) * l⁻¹ := by group
      _ = l * t * l⁻¹ := by rw [hgn]
      _ = t := by rw [hlt, mul_inv_cancel_right]
  have hodd : Odd (N.relIndex (centralizer {t})) := by
    rw [relIndex_eq_of_forall_eq_mul D.le_centralizer fun h hh => D.exists_eq_mul hh]
    exact D.odd_index
  refine false_of_isolated_involution hnonab ht fun y hy hconj => ?_
  obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
  have hy2 : (c * t * c⁻¹) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    have := orderOf_conj_eq c⁻¹ t
    rw [inv_inv] at this
    rw [this, ht]
  obtain ⟨h, hh, hhN⟩ := exists_conj_mem_of_odd_relIndex hodd hy hy2
  have e : h⁻¹ * (c * t * c⁻¹) * h = (c⁻¹ * h)⁻¹ * t * (c⁻¹ * h) := by group
  rw [e] at hhN
  have h1 := hstep4 _ hhN
  have hht : h * t = t * h := mem_centralizer_singleton_iff.1 hh
  calc c * t * c⁻¹ = h * ((c⁻¹ * h)⁻¹ * t * (c⁻¹ * h)) * h⁻¹ := by group
    _ = h * t * h⁻¹ := by rw [h1]
    _ = t := by rw [hht, mul_inv_cancel_right]

open CFSG.ComponentClassification.M12Cover.CyclicKernel in
theorem centralizer_eq_zpowers [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (D : DavisSolomonFacts G t L E) (ht : orderOf t = 2)
    (hCc : IsCyclic (centralizer (L : Set G))) (hC2 : IsPGroup 2 (centralizer (L : Set G)))
    (htC : t ∈ centralizer (L : Set G))
    (hCE : centralizer (E : Set G) ≤ E ⊔ centralizer (L : Set G)) :
    centralizer (L : Set G) = zpowers t := by
  have hzC : zpowers t ≤ centralizer (L : Set G) := zpowers_le.2 htC
  by_contra hne
  have hcard : 2 < Nat.card (centralizer (L : Set G)) := by
    by_contra hle
    push Not at hle
    exact hne (eq_of_le_of_card_ge hzC (by rw [Nat.card_zpowers, ht]; exact hle)).symm
  obtain ⟨a, haC, ha4⟩ := exists_orderOf_eq_four_of_isCyclic hCc hC2 hcard
  have ha2 : a ^ 2 = t := eq_of_orderOf_eq_two_of_isCyclic hCc (pow_mem haC 2) htC
    (by rw [orderOf_pow_of_dvd two_ne_zero (by rw [ha4]; norm_num), ha4]) ht
  obtain ⟨n, hn, hnt⟩ := D.exists_normalizer_conj_ne hnonab ht
  apply hnt
  have haE : ∀ e ∈ E, e * a = a * e := fun e he => mem_centralizer_iff.1 haC e (D.E_le he)
  have hnaE : n⁻¹ * a * n ∈ centralizer (E : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    have hne' : n * e * n⁻¹ ∈ E := (mem_normalizer_iff.1 hn e).1 he
    have hc := haE _ hne'
    calc e * (n⁻¹ * a * n) = n⁻¹ * ((n * e * n⁻¹) * a) * n := by group
      _ = n⁻¹ * (a * (n * e * n⁻¹)) * n := by rw [hc]
      _ = n⁻¹ * a * n * e := by group
  obtain ⟨e, he, c, hc, hec⟩ := exists_mul_of_mem_sup_of_commute
    (fun e he c hc => mem_centralizer_iff.1 hc e (D.E_le he)) (hCE hnaE)
  have hcomm : e * c = c * e := mem_centralizer_iff.1 hc e (D.E_le he)
  have h1 : n⁻¹ * t * n = c ^ 2 := by
    calc n⁻¹ * t * n = n⁻¹ * (a * a) * n := by rw [← sq, ha2]
      _ = (n⁻¹ * a * n) * (n⁻¹ * a * n) := by group
      _ = e * (c * e) * c := by rw [hec]; group
      _ = (e * e) * (c * c) := by rw [← hcomm]; group
      _ = c ^ 2 := by rw [← sq e, D.E_sq e he, one_mul, sq]
  have hc2 : orderOf (c ^ 2) = 2 := by rw [← h1, SolomonWong.orderOf_conj_eq, ht]
  rw [h1]
  exact eq_of_orderOf_eq_two_of_isCyclic hCc (pow_mem hc 2) htC hc2 ht

theorem sup_centralizer_eq [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (D : DavisSolomonFacts G t L E) (ht : orderOf t = 2)
    (hCc : IsCyclic (centralizer (L : Set G))) (hC2 : IsPGroup 2 (centralizer (L : Set G)))
    (htC : t ∈ centralizer (L : Set G))
    (hCE : centralizer (E : Set G) ≤ E ⊔ centralizer (L : Set G)) (htL : t ∈ L) :
    L ⊔ centralizer (L : Set G) = L := by
  rw [D.centralizer_eq_zpowers hnonab ht hCc hC2 htC hCE]
  exact sup_eq_left.2 (zpowers_le.2 htL)

end DavisSolomonFacts

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem DavisSolomonFacts.of_standard (hset : StandardSetting G L) {t : G}
    (ht : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype) {E : Subgroup G} (hEL : E ≤ L)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) (hE : Nat.card E = 2 ^ 10)
    (hrank : ∀ τ ∈ centralizer {t}, orderOf τ = 2 → τ ∉ L ⊔ centralizer (L : Set G) →
      ∀ B : Subgroup G, B ≤ centralizer {t} ⊓ centralizer {τ} → (∀ b ∈ B, b ^ 2 = 1) →
        Nat.card B ≤ 2 ^ 8)
    (hsq : ∀ a : L, a ^ 2 ∈ center L → a ^ 2 = 1)
    (hclass : ∀ B : Subgroup G, B ≤ L → (∀ b ∈ B, b ^ 2 = 1) → Nat.card B = 2 ^ 10 →
      ∃ l ∈ L, B = conjSubgroup E l)
    (hfuse : ∀ s ∈ L, orderOf s = 2 → ∃ l ∈ L, l⁻¹ * s * l ∈ E)
    (hgen : normalizer (E : Set G) ⊓ L ≤
      E ⊔ closure {y | y ∈ normalizer (E : Set G) ⊓ L ∧ Odd (orderOf y)})
    (hodd : Odd ((normalizer (E : Set G)).relIndex L))
    (huniq : ∀ B : Subgroup G, B ≤ normalizer (E : Set G) ⊓ L → (∀ b ∈ B, b ^ 2 = 1) →
      Nat.card B = 2 ^ 10 → B = E)
    (hout : (L ⊔ centralizer {t} ⊓ centralizer (L : Set G)).relIndex (centralizer {t}) ≤ 2) :
    DavisSolomonFacts G t L E := by
  obtain ⟨-, hCc, -, -, hN, hLt, hCt⟩ := std_center_facts hset ht htZ
  rw [inf_of_le_right hCt] at hout
  have hZ : Even (Nat.card (center L)) := by
    obtain ⟨z, hzZ, rfl⟩ := htZ
    have h2 : orderOf (⟨z, hzZ⟩ : center L) = 2 := by
      rw [Subgroup.orderOf_mk]
      simpa using ht
    exact even_iff_two_dvd.2 (h2 ▸ orderOf_dvd_natCard _)
  exact ⟨hLt, hN.le, hEL, hE2, hE, hrank,
    fun y hy hy2 => mem_of_sq_eq_one_of_mem_sup_centralizer hCc hZ hsq hy hy2, hclass, hfuse,
    hgen, hodd, huniq, hout⟩

theorem std_exists_normalizer_conj_ne (hset : StandardSetting G L) {t : G} {E : Subgroup G}
    (ht : orderOf t = 2) (D : DavisSolomonFacts G t L E) :
    ∃ n ∈ normalizer (E : Set G), n⁻¹ * t * n ≠ t :=
  have := hset.simple
  D.exists_normalizer_conj_ne hset.nonab ht

theorem std_centralizer_eq_zpowers (hset : StandardSetting G L) {t : G} (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) {E : Subgroup G} (D : DavisSolomonFacts G t L E)
    (hCE : centralizer (E : Set G) ≤ E ⊔ centralizer (L : Set G)) :
    centralizer (L : Set G) = zpowers t ∧ Nat.card (centralizer (L : Set G)) = 2 ∧
      L ⊔ centralizer (L : Set G) = L := by
  have := hset.simple
  obtain ⟨htC, hCc, hC2, -, -, -, -⟩ := std_center_facts hset ht htZ
  have hC := D.centralizer_eq_zpowers hset.nonab ht hCc hC2 htC hCE
  have htL : t ∈ L := by
    obtain ⟨z, -, rfl⟩ := htZ
    exact z.2
  refine ⟨hC, by rw [hC, Nat.card_zpowers, ht],
    D.sup_centralizer_eq hset.nonab ht hCc hC2 htC hCE htL⟩

end Standard

end CFSG.EvenSmallLie.UnitarySix
