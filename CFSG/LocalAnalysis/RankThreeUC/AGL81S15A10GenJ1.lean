module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace A10GenJ1

open Equiv Equiv.Perm MulAction

theorem exists_notMem (s : Finset (Fin 10)) (hs : s.card < 10) : ∃ e : Fin 10, e ∉ s := by
  by_contra h
  have hs' : s = Finset.univ :=
    Finset.eq_univ_iff_forall.2 fun x => not_not.1 fun hx => h ⟨x, hx⟩
  rw [hs', Finset.card_univ, Fintype.card_fin] at hs
  exact lt_irrefl _ hs

theorem threeCycle_facts {c d e : Fin 10} (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    (swap c e * swap c d) ∈ alternatingGroup (Fin 10) ∧ (swap c e * swap c d) c = d ∧
      ∀ x, x ≠ c → x ≠ d → x ≠ e → (swap c e * swap c d) x = x := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hce, Perm.sign_swap hcd]
    decide
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hcd.symm hde]
  · intro x hxc hxd hxe
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxc hxe]

theorem mem_block_of_ne {G : Subgroup (Perm (Fin 10))} {a b : Fin 10}
    (hA : ∀ σ ∈ alternatingGroup (Fin 10), σ a = a → σ b = b → σ ∈ G)
    {B : Set (Fin 10)} (hB : IsBlock G B) {c w : Fin 10} (hc : c ∈ B) (hca : c ≠ a) (hcb : c ≠ b)
    (hw : w ∈ B) (hwc : w ≠ c) {d : Fin 10} (hda : d ≠ a) (hdb : d ≠ b) : d ∈ B := by
  by_cases hdc : d = c
  · exact hdc ▸ hc
  by_cases hdw : d = w
  · exact hdw ▸ hw
  obtain ⟨e, he⟩ := exists_notMem {a, b, c, d, w} (lt_of_le_of_lt Finset.card_le_five (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
  obtain ⟨hea, heb, hec, hed, hew⟩ := he
  obtain ⟨h1, h2, h3⟩ := threeCycle_facts (Ne.symm hdc) (Ne.symm hec) (Ne.symm hed)
  have hhG : (swap c e * swap c d) ∈ G :=
    hA _ h1 (h3 a (Ne.symm hca) (Ne.symm hda) (Ne.symm hea))
      (h3 b (Ne.symm hcb) (Ne.symm hdb) (Ne.symm heb))
  have hwfix : (⟨swap c e * swap c d, hhG⟩ : G) • w = w :=
    h3 w hwc (fun h => hdw h.symm) (fun h => hew h.symm)
  have hgB := (isBlock_iff_smul_eq_of_mem.1 hB) (g := ⟨swap c e * swap c d, hhG⟩) hw
    (by rw [hwfix]; exact hw)
  have hmem := Set.smul_mem_smul_set (a := (⟨swap c e * swap c d, hhG⟩ : G)) hc
  rw [hgB] at hmem
  exact h2 ▸ hmem

theorem isPreprimitive_of {G : Subgroup (Perm (Fin 10))} {a b : Fin 10} (hab : a ≠ b)
    (hA : ∀ σ ∈ alternatingGroup (Fin 10), σ a = a → σ b = b → σ ∈ G)
    (hN : ∀ i j : Fin 10, ∃ σ ∈ G, σ i = j) : IsPreprimitive G (Fin 10) := by
  have hpt : IsPretransitive G (Fin 10) :=
    ⟨fun x y => by
      obtain ⟨σ, hσ, h⟩ := hN x y
      exact ⟨⟨σ, hσ⟩, h⟩⟩
  obtain ⟨c0, hc0⟩ := exists_notMem {a, b} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc0
  refine IsPreprimitive.of_isTrivialBlock_base c0 ?_
  intro B hcB hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨w, hwB, hwc⟩ := (Set.not_subsingleton_iff.1 hsub).exists_ne c0
  have hΩ : ∀ d, d ≠ a → d ≠ b → d ∈ B := fun d hda hdb =>
    mem_block_of_ne hA hB hcB hc0.1 hc0.2 hwB hwc hda hdb
  have hsub8 : ({a, b}ᶜ : Set (Fin 10)) ⊆ B := fun d hd =>
    hΩ d (fun h => hd (by simp [h])) (fun h => hd (by simp [h]))
  have h8 : ({a, b}ᶜ : Set (Fin 10)).ncard = 8 := by
    have h := Set.ncard_add_ncard_compl ({a, b} : Set (Fin 10))
    rw [Set.ncard_pair hab, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega
  have hle := Set.ncard_le_ncard hsub8 (Set.toFinite B)
  refine hB.eq_univ_of_card_lt ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

theorem exists_three_points (a b : Fin 10) :
    ∃ c d e : Fin 10, c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ e ≠ a ∧ e ≠ b ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  obtain ⟨c, hc⟩ := exists_notMem {a, b} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  obtain ⟨d, hd⟩ := exists_notMem {a, b, c} (lt_of_le_of_lt Finset.card_le_three (by norm_num))
  obtain ⟨e, he⟩ := exists_notMem {a, b, c, d} (lt_of_le_of_lt Finset.card_le_four (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd he
  exact ⟨c, d, e, hc.1, hc.2, hd.1, hd.2.1, he.1, he.2.1, Ne.symm hd.2.2, Ne.symm he.2.2.1,
    Ne.symm he.2.2.2⟩

theorem disjoint_of_commute {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α < 15)
    {p q : Perm α} (hp : p ^ 5 = 1) (hq : q ^ 3 = 1) (hpq : Commute p q) :
    Perm.Disjoint p q := by
  intro x
  by_contra hcon
  push Not at hcon
  obtain ⟨hpx, hqx⟩ := hcon
  have h15 : (p * q) ^ 15 = 1 := by
    rw [hpq.mul_pow, show (15 : ℕ) = 5 * 3 by norm_num, pow_mul, hp, one_pow, one_mul,
      mul_comm, pow_mul, hq, one_pow]
  have hper : Function.IsPeriodicPt (⇑(p * q)) 15 x := by
    show (⇑(p * q))^[15] x = x
    rw [← Equiv.Perm.coe_pow, h15]
    rfl
  have hdvd := hper.minimalPeriod_dvd
  have hle : Function.minimalPeriod (⇑(p * q)) x ≤ Fintype.card α := Function.minimalPeriod_le_card
  have hfix : ((p * q) ^ Function.minimalPeriod (⇑(p * q)) x) x = x := by
    rw [Equiv.Perm.coe_pow]
    exact Function.iterate_minimalPeriod
  have hp3 : (p ^ 3) x = x → p x = x := fun h => by
    have : p = p ^ 3 * p ^ 3 := by
      rw [← pow_add, show 3 + 3 = 5 + 1 by norm_num, pow_add, hp, one_mul, pow_one]
    calc p x = (p ^ 3 * p ^ 3) x := by rw [← this]
      _ = x := by rw [Perm.mul_apply, h, h]
  have hq2 : (q ^ 2) x = x → q x = x := fun h => by
    have : q = q ^ 2 * q ^ 2 := by
      rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hq, one_mul, pow_one]
    calc q x = (q ^ 2 * q ^ 2) x := by rw [← this]
      _ = x := by rw [Perm.mul_apply, h, h]
  have hpq3 : (p * q) ^ 3 = p ^ 3 := by rw [hpq.mul_pow, hq, mul_one]
  have hpq5 : (p * q) ^ 5 = q ^ 2 := by
    rw [hpq.mul_pow, hp, one_mul, show 5 = 3 + 2 by norm_num, pow_add, hq, one_mul]
  generalize Function.minimalPeriod (⇑(p * q)) x = d at hdvd hle hfix
  have hdlt : d < 15 := lt_of_le_of_lt hle hα
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hcases : d = 1 ∨ d = 3 ∨ d = 5 := by
    interval_cases d <;> first | omega | (exfalso; revert hdvd; decide)
  rcases hcases with rfl | rfl | rfl
  · have h1 : (p * q) x = x := by simpa using hfix
    have h3 := Perm.pow_apply_eq_self_of_apply_eq_self h1 3
    rw [hpq3] at h3
    exact hpx (hp3 h3)
  · rw [hpq3] at hfix
    exact hpx (hp3 hfix)
  · rw [hpq5] at hfix
    exact hqx (hq2 hfix)

theorem isThreeCycle_of_commute {p q : Perm (Fin 10)} (hp : p ^ 5 = 1) (hp1 : p ≠ 1)
    (hq : q ^ 3 = 1) (hq1 : q ≠ 1) (hpq : Commute p q) : IsThreeCycle q := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hop : orderOf p = 5 := orderOf_eq_prime hp hp1
  have hoq : orderOf q = 3 := orderOf_eq_prime hq hq1
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := p) (by rw [hop]; exact Nat.prime_five)
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := q) (by rw [hoq]; exact Nat.prime_three)
  have hsp : p.support.card = (m + 1) * 5 := by
    rw [← Equiv.Perm.sum_cycleType, hm, hop, Multiset.sum_replicate, smul_eq_mul]
  have hsq : q.support.card = (n + 1) * 3 := by
    rw [← Equiv.Perm.sum_cycleType, hn, hoq, Multiset.sum_replicate, smul_eq_mul]
  have hdisj := disjoint_of_commute (by simp) hp hq hpq
  have hcard : p.support.card + q.support.card ≤ 10 := by
    rw [← Finset.card_union_of_disjoint (Equiv.Perm.disjoint_iff_disjoint_support.1 hdisj)]
    simpa using Finset.card_le_univ (p.support ∪ q.support)
  have hn0 : n = 0 := by omega
  rw [← card_support_eq_three_iff, hsq, hn0]

def u8 : Perm (Fin 8) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

def c8 : Perm (Fin 8) := swap 5 6 * swap 5 7

theorem u8_mem : u8 ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup]
  decide

theorem c8_mem : c8 ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup]
  decide

theorem u8_pow : u8 ^ 5 = 1 := by decide

theorem c8_pow : c8 ^ 3 = 1 := by decide

theorem u8_comm : Commute u8 c8 :=
  (by decide : u8 * c8 = c8 * u8)

theorem c8_isThreeCycle : IsThreeCycle c8 :=
  isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem isThreeCycle_map {φ : alternatingGroup (Fin 8) →* Perm (Fin 10)}
    (hφ : Function.Injective φ) {t : alternatingGroup (Fin 8)}
    (ht : IsThreeCycle (t : Perm (Fin 8))) : IsThreeCycle (φ t) := by
  set u : alternatingGroup (Fin 8) := ⟨u8, u8_mem⟩
  set c : alternatingGroup (Fin 8) := ⟨c8, c8_mem⟩
  have hu1 : u ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hc1 : c ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
  have hup : u ^ 5 = 1 := Subtype.ext u8_pow
  have hcp : c ^ 3 = 1 := Subtype.ext c8_pow
  have hcomm : Commute u c := Subtype.ext u8_comm
  have hq : IsThreeCycle (φ c) :=
    isThreeCycle_of_commute (p := φ u) (q := φ c) (by rw [← map_pow, hup, map_one])
      (fun h => hu1 (hφ (by rw [h, map_one]))) (by rw [← map_pow, hcp, map_one])
      (fun h => hc1 (hφ (by rw [h, map_one]))) (hcomm.map φ)
  have hconj : IsConj c t :=
    alternatingGroup.isThreeCycle_isConj (by simp) c8_isThreeCycle ht
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hφt : φ t = φ g * φ c * (φ g)⁻¹ := by rw [← hg]; simp [map_mul, map_inv]
  have hconj' : IsConj (φ c) (φ t) := isConj_iff.2 ⟨φ g, hφt.symm⟩
  show (φ t).cycleType = {3}
  rw [← isConj_iff_cycleType_eq.1 hconj']
  exact hq.cycleType

open scoped Pointwise

theorem three_cycle_smul_block {α : Type*} [Fintype α] [DecidableEq α] {K : Subgroup (Perm α)}
    {B : Set α} (hB : IsBlock K B) {t : Perm α} (htK : t ∈ K) (ht : IsThreeCycle t) {x y : α}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y) : t • B = B := by
  have hblock := isBlock_iff_smul_eq_of_mem.1 hB (g := ⟨t, htK⟩)
  by_cases hfix : ∃ z ∈ B, t z = z
  · obtain ⟨z, hz, htz⟩ := hfix
    exact hblock hz (by show t z ∈ B; rw [htz]; exact hz)
  · have hfix' : ∀ z ∈ B, t z ≠ z := fun z hz h => hfix ⟨z, hz, h⟩
    obtain ⟨i, hi⟩ := ht.isCycle.exists_pow_eq (hfix' x hx) (hfix' y hy)
    have h3 : t ^ 3 = 1 := by rw [← ht.orderOf]; exact pow_orderOf_eq_one t
    have hpow : t ^ (i % 3) = t ^ i := by
      have := pow_mod_orderOf t i
      rwa [ht.orderOf] at this
    have hmod : (t ^ (i % 3)) x = y := by rw [hpow]; exact hi
    have hlt : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hm : i % 3
    · exact absurd hmod hxy
    · rw [pow_one] at hmod
      exact hblock hx (by show t x ∈ B; rw [hmod]; exact hy)
    · have hyx : t y = x := by
        rw [← hmod, ← Perm.mul_apply, ← pow_succ', h3]
        rfl
      exact hblock hy (by show t y ∈ B; rw [hyx]; exact hx)

theorem isPreprimitive_of_three_cycles {α : Type*} [Fintype α] [DecidableEq α]
    {K : Subgroup (Perm α)} (htrans : ∀ x y : α, ∃ g ∈ K, g x = y)
    (hgen : K ≤ Subgroup.closure {t : Perm α | t ∈ K ∧ IsThreeCycle t}) (a : α) :
    IsPreprimitive K α := by
  have hpt : IsPretransitive K α := ⟨fun x y => by
    obtain ⟨g, hg, h⟩ := htrans x y
    exact ⟨⟨g, hg⟩, h⟩⟩
  refine IsPreprimitive.of_isTrivialBlock_base a ?_
  intro B _ hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.1 hsub
  have hS : K ≤ MulAction.stabilizer (Perm α) B := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro t ⟨htK, ht⟩
    exact MulAction.mem_stabilizer_iff.2 (three_cycle_smul_block hB htK ht hx hy hxy)
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨g, hg, hgx⟩ := htrans x z
  have hgB := MulAction.mem_stabilizer_iff.1 (hS hg)
  have h2 : g • x ∈ g • B := Set.smul_mem_smul_set hx
  rw [hgB] at h2
  rw [← hgx]
  exact h2

section Orbit

open scoped Classical

variable (φ : alternatingGroup (Fin 8) →* Perm (Fin 10)) (x₀ : Fin 10)

@[expose] def orb : Set (Fin 10) := {z | ∃ s, φ s x₀ = z}

theorem orb_iff (s : alternatingGroup (Fin 8)) (z : Fin 10) :
    φ s z ∈ orb φ x₀ ↔ z ∈ orb φ x₀ := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨s⁻¹ * r, ?_⟩
    rw [map_mul, map_inv, Perm.mul_apply, hr]
    simp
  · rintro ⟨r, rfl⟩
    exact ⟨s * r, by rw [map_mul, Perm.mul_apply]⟩

@[expose] def restr : alternatingGroup (Fin 8) →* Perm (orb φ x₀) where
  toFun s := (φ s).subtypePerm (p := fun z => z ∈ orb φ x₀) (orb_iff φ x₀ s)
  map_one' := Equiv.ext fun x => Subtype.ext (by simp)
  map_mul' s t := Equiv.ext fun x => Subtype.ext (by
    change (φ (s * t)) x = (φ s) ((φ t) x)
    rw [map_mul]
    rfl)

theorem restr_apply (s : alternatingGroup (Fin 8)) (y : orb φ x₀) :
    ((restr φ x₀ s y : orb φ x₀) : Fin 10) = φ s y := rfl

theorem restr_trans (y z : orb φ x₀) : ∃ g ∈ (restr φ x₀).range, g y = z := by
  obtain ⟨y, r₁, rfl⟩ := y
  obtain ⟨z, r₂, rfl⟩ := z
  refine ⟨restr φ x₀ (r₂ * r₁⁻¹), ⟨_, rfl⟩, Subtype.ext ?_⟩
  rw [restr_apply, map_mul, map_inv, Perm.mul_apply]
  simp

theorem three_cycle_dichotomy (hφ : Function.Injective φ) {s : alternatingGroup (Fin 8)}
    (hs : IsThreeCycle (s : Perm (Fin 8))) :
    (∀ z, φ s z ≠ z → z ∈ orb φ x₀) ∨ (∀ z, φ s z ≠ z → z ∉ orb φ x₀) := by
  have h3 : IsThreeCycle (φ s) := isThreeCycle_map hφ hs
  by_cases hex : ∃ y, φ s y ≠ y ∧ y ∈ orb φ x₀
  · left
    obtain ⟨y, hy, hyO⟩ := hex
    intro z hz
    obtain ⟨i, hi⟩ := h3.isCycle.exists_pow_eq hy hz
    rw [← hi]
    have := (orb_iff φ x₀ (s ^ i) y).2 hyO
    simpa [map_pow] using this
  · right
    push Not at hex
    exact hex

theorem restr_of_isThreeCycle (hφ : Function.Injective φ) {s : alternatingGroup (Fin 8)}
    (hs : IsThreeCycle (s : Perm (Fin 8))) :
    restr φ x₀ s = 1 ∨ IsThreeCycle (restr φ x₀ s) := by
  rcases three_cycle_dichotomy φ x₀ hφ hs with hin | hout
  · right
    have h3 : IsThreeCycle (φ s) := isThreeCycle_map hφ hs
    have hof : Equiv.Perm.ofSubtype (restr φ x₀ s) = φ s :=
      Equiv.Perm.ofSubtype_subtypePerm (orb_iff φ x₀ s) hin
    show (restr φ x₀ s).cycleType = {3}
    rw [← Equiv.Perm.cycleType_ofSubtype, hof]
    exact h3.cycleType
  · left
    refine Equiv.ext fun y => Subtype.ext ?_
    by_contra h
    exact hout y.1 h y.2

theorem restr_range_eq (hφ : Function.Injective φ) {s₀ : alternatingGroup (Fin 8)}
    (hs₀ : IsThreeCycle (s₀ : Perm (Fin 8))) (hx₀ : φ s₀ x₀ ≠ x₀) :
    Nat.card (orb φ x₀) = 8 ∧ (restr φ x₀).range = alternatingGroup (orb φ x₀) := by
  set K := (restr φ x₀).range with hK
  have hKcl : K = Subgroup.closure (restr φ x₀ ''
      {g : alternatingGroup (Fin 8) | IsThreeCycle (g : Perm (Fin 8))}) := by
    rw [hK, MonoidHom.range_eq_map, ← alternatingGroup.closure_isThreeCycles_eq_top,
      MonoidHom.map_closure]
  have hgen : K ≤ Subgroup.closure {g : Perm (orb φ x₀) | g ∈ K ∧ IsThreeCycle g} := by
    refine hKcl.le.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨s, hs, rfl⟩
    rcases restr_of_isThreeCycle φ x₀ hφ hs with h1 | h3
    · rw [h1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure
        (show restr φ x₀ s ∈ {g : Perm (orb φ x₀) | g ∈ K ∧ IsThreeCycle g} from ⟨⟨s, rfl⟩, h3⟩)
  have hx0mem : x₀ ∈ orb φ x₀ := ⟨1, by simp⟩
  have hpt : IsPreprimitive K (orb φ x₀) :=
    isPreprimitive_of_three_cycles (restr_trans φ x₀) hgen ⟨x₀, hx0mem⟩
  have hne : restr φ x₀ s₀ ≠ 1 := by
    intro h
    have := congrArg (fun g : Perm (orb φ x₀) => ((g ⟨x₀, hx0mem⟩ : orb φ x₀) : Fin 10)) h
    exact hx₀ this
  have hg3 : IsThreeCycle (restr φ x₀ s₀) :=
    (restr_of_isThreeCycle φ x₀ hφ hs₀).resolve_left hne
  have hAlt : alternatingGroup (orb φ x₀) ≤ K :=
    Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hpt hg3 ⟨s₀, rfl⟩
  haveI hnt : Nontrivial (orb φ x₀) :=
    ⟨⟨⟨x₀, hx0mem⟩, ⟨φ s₀ x₀, s₀, rfl⟩, fun h => hx₀ (congrArg Subtype.val h).symm⟩⟩
  have hker : (restr φ x₀).ker = ⊥ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top_of_card_ne_six (α := Fin 8)
        (by simp) (by simp) (N := (restr φ x₀).ker) with h | h
    · exact h
    · have hmem : s₀ ∈ (restr φ x₀).ker := by rw [h]; trivial
      exact absurd (MonoidHom.mem_ker.1 hmem) hne
  have hinj : Function.Injective (restr φ x₀) := (MonoidHom.ker_eq_bot_iff _).1 hker
  have h8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hcardK : Nat.card K = 20160 := by
    rw [hK, ← h8]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hlow : 20160 ≤ (Nat.card (orb φ x₀)).factorial := by
    calc 20160 = Nat.card K := hcardK.symm
      _ ≤ Nat.card (Perm (orb φ x₀)) := Subgroup.card_le_card_group K
      _ = (Nat.card (orb φ x₀)).factorial := Nat.card_perm
  have hup : (Nat.card (orb φ x₀)).factorial / 2 ≤ 20160 := by
    calc (Nat.card (orb φ x₀)).factorial / 2 = Nat.card (alternatingGroup (orb φ x₀)) :=
          nat_card_alternatingGroup.symm
      _ ≤ Nat.card K := Subgroup.card_le_of_le hAlt
      _ = 20160 := hcardK
  have hn8 : Nat.card (orb φ x₀) = 8 := by
    by_contra hne8
    rcases Nat.lt_or_gt_of_ne hne8 with hlt | hgt
    · have h1 : (Nat.card (orb φ x₀)).factorial ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
      have h7 : (7 : ℕ).factorial = 5040 := by decide
      omega
    · have h1 : (9 : ℕ).factorial ≤ (Nat.card (orb φ x₀)).factorial := Nat.factorial_le (by omega)
      have h9 : (9 : ℕ).factorial = 362880 := by decide
      omega
  refine ⟨hn8, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge hAlt ?_).symm
  rw [hcardK, nat_card_alternatingGroup, hn8]
  decide

end Orbit

theorem embed_contains_stabilizer (φ : alternatingGroup (Fin 8) →* Perm (Fin 10))
    (hφ : Function.Injective φ) :
    ∃ a b : Fin 10, a ≠ b ∧ ∀ σ ∈ alternatingGroup (Fin 10), σ a = a → σ b = b → σ ∈ φ.range := by
  classical
  set s₀ : alternatingGroup (Fin 8) := ⟨c8, c8_mem⟩
  have hs₀ : IsThreeCycle (s₀ : Perm (Fin 8)) := c8_isThreeCycle
  have h3 : IsThreeCycle (φ s₀) := isThreeCycle_map hφ hs₀
  obtain ⟨x₀, hx₀s⟩ := h3.isCycle.nonempty_support
  have hx₀ : φ s₀ x₀ ≠ x₀ := Perm.mem_support.1 hx₀s
  obtain ⟨hn8, hK⟩ := restr_range_eq φ x₀ hφ hs₀ hx₀
  have hO : (orb φ x₀).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hn8
  have hOc : (orb φ x₀)ᶜ.ncard = 2 := by
    have h := Set.ncard_add_ncard_compl (orb φ x₀)
    rw [hO, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega
  obtain ⟨a, b, hab, habO⟩ := Set.ncard_eq_two.1 hOc
  have hout : ∀ z, z ∉ orb φ x₀ → z = a ∨ z = b := fun z hz => by
    have : z ∈ (orb φ x₀)ᶜ := hz
    rw [habO] at this
    simpa using this
  have hnot : a ∉ orb φ x₀ ∧ b ∉ orb φ x₀ := by
    have ha : a ∈ (orb φ x₀)ᶜ := by rw [habO]; simp
    have hb : b ∈ (orb φ x₀)ᶜ := by rw [habO]; simp
    exact ⟨ha, hb⟩
  have hgen3 : ∀ s : alternatingGroup (Fin 8), IsThreeCycle (s : Perm (Fin 8)) →
      φ s a = a ∧ φ s b = b := by
    intro s hs
    have h3s : IsThreeCycle (φ s) := isThreeCycle_map hφ hs
    rcases three_cycle_dichotomy φ x₀ hφ hs with hin | hout'
    · refine ⟨?_, ?_⟩
      · by_contra h
        exact hnot.1 (hin a h)
      · by_contra h
        exact hnot.2 (hin b h)
    · exfalso
      have hsub : (φ s).support ⊆ {a, b} := fun z hz => by
        have := hout z (hout' z (Perm.mem_support.1 hz))
        simpa using this
      have hc := Finset.card_le_card hsub
      rw [h3s.card_support] at hc
      have h2 : ({a, b} : Finset (Fin 10)).card ≤ 2 := Finset.card_le_two
      omega
  have hfix : ∀ s : alternatingGroup (Fin 8), φ s a = a ∧ φ s b = b := by
    intro s
    have hle : (⊤ : Subgroup (alternatingGroup (Fin 8))) ≤
        ((MulAction.stabilizer (Perm (Fin 10)) a) ⊓
          (MulAction.stabilizer (Perm (Fin 10)) b)).comap φ := by
      rw [← alternatingGroup.closure_isThreeCycles_eq_top, Subgroup.closure_le]
      intro t ht
      simp only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_inf,
        MulAction.mem_stabilizer_iff, Perm.smul_def]
      exact hgen3 t ht
    have := hle (Subgroup.mem_top s)
    simpa only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_inf,
      MulAction.mem_stabilizer_iff, Perm.smul_def] using this
  refine ⟨a, b, hab, fun σ hσ hσa hσb => ?_⟩
  have hσO : ∀ z, σ z ∈ orb φ x₀ ↔ z ∈ orb φ x₀ := by
    intro z
    constructor
    · intro hz
      by_contra hzO
      rcases hout z hzO with h | h
      · rw [h, hσa] at hz
        exact hnot.1 hz
      · rw [h, hσb] at hz
        exact hnot.2 hz
    · intro hz
      by_contra hσzO
      rcases hout _ hσzO with h | h
      · have hza : z = a := σ.injective (h.trans hσa.symm)
        exact hnot.1 (hza ▸ hz)
      · have hzb : z = b := σ.injective (h.trans hσb.symm)
        exact hnot.2 (hzb ▸ hz)
  have hsgn : Perm.sign (σ.subtypePerm (p := fun z => z ∈ orb φ x₀) hσO) = 1 := by
    rw [Perm.sign_subtypePerm σ hσO (fun z hz => ?_)]
    · exact mem_alternatingGroup.1 hσ
    · by_contra hzO
      rcases hout z hzO with h | h
      · exact hz (by rw [h]; exact hσa)
      · exact hz (by rw [h]; exact hσb)
  have hmem : σ.subtypePerm (p := fun z => z ∈ orb φ x₀) hσO ∈ (restr φ x₀).range := by
    rw [hK]
    exact mem_alternatingGroup.2 hsgn
  obtain ⟨s, hs⟩ := hmem
  refine ⟨s, Equiv.ext fun z => ?_⟩
  by_cases hz : z ∈ orb φ x₀
  · exact congrArg (fun g : Perm (orb φ x₀) => ((g ⟨z, hz⟩ : orb φ x₀) : Fin 10)) hs
  · rcases hout z hz with h | h
    · rw [h, (hfix s).1, hσa]
    · rw [h, (hfix s).2, hσb]


theorem stabilizer_le_closure_three_cycles (a b : Fin 10) (σ : alternatingGroup (Fin 10))
    (hσa : (σ : Perm (Fin 10)) a = a) (hσb : (σ : Perm (Fin 10)) b = b) :
    σ ∈ Subgroup.closure {t : alternatingGroup (Fin 10) |
      IsThreeCycle (t : Perm (Fin 10)) ∧ (t : Perm (Fin 10)) a = a ∧
        (t : Perm (Fin 10)) b = b} := by
  classical
  let p : Fin 10 → Prop := fun z => z ≠ a ∧ z ≠ b
  have hσp : ∀ z, p ((σ : Perm (Fin 10)) z) ↔ p z := by
    intro z
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
      · rw [h, hσa]
      · rw [h, hσb]
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
      · exact (σ : Perm (Fin 10)).injective (h.trans hσa.symm)
      · exact (σ : Perm (Fin 10)).injective (h.trans hσb.symm)
  have hσs : ∀ z, (σ : Perm (Fin 10)) z ≠ z → p z := by
    intro z hz
    refine ⟨fun h => hz ?_, fun h => hz ?_⟩
    · rw [h, hσa]
    · rw [h, hσb]
  have hσX : (σ : Perm (Fin 10)).subtypePerm hσp ∈
      Subgroup.closure {g : Perm (Subtype p) | IsThreeCycle g} := by
    rw [Equiv.Perm.closure_three_cycles_eq_alternating, mem_alternatingGroup,
      Perm.sign_subtypePerm _ hσp hσs]
    exact mem_alternatingGroup.1 σ.2
  have hmap : (σ : Perm (Fin 10)) ∈
      Subgroup.closure ((Perm.ofSubtype : Perm (Subtype p) →* Perm (Fin 10)) ''
        {g | IsThreeCycle g}) := by
    rw [← MonoidHom.map_closure, ← Equiv.Perm.ofSubtype_subtypePerm hσp hσs]
    exact Subgroup.mem_map.2 ⟨_, hσX, rfl⟩
  have hle : Subgroup.closure ((Perm.ofSubtype : Perm (Subtype p) →* Perm (Fin 10)) ''
      {g | IsThreeCycle g}) ≤ (Subgroup.closure {t : alternatingGroup (Fin 10) |
        IsThreeCycle (t : Perm (Fin 10)) ∧ (t : Perm (Fin 10)) a = a ∧
          (t : Perm (Fin 10)) b = b}).map (alternatingGroup (Fin 10)).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have h3 : IsThreeCycle (Perm.ofSubtype g) := by
      show (Perm.ofSubtype g).cycleType = {3}
      rw [Equiv.Perm.cycleType_ofSubtype]
      exact hg.cycleType
    exact ⟨⟨Perm.ofSubtype g, h3.mem_alternatingGroup⟩, Subgroup.subset_closure
      ⟨h3, Equiv.Perm.ofSubtype_apply_of_not_mem g (fun h => h.1 rfl),
        Equiv.Perm.ofSubtype_apply_of_not_mem g (fun h => h.2 rfl)⟩, rfl⟩
  obtain ⟨x, hx, hxσ⟩ := hle hmap
  exact (Subtype.ext hxσ : x = σ) ▸ hx

end A10GenJ1

theorem alt_ten_sup_eq_top (a b : Fin 10) (hab : a ≠ b) (A N : Subgroup (alternatingGroup (Fin 10)))
    (hA : ∀ σ : alternatingGroup (Fin 10), (σ : Equiv.Perm (Fin 10)) a = a →
      (σ : Equiv.Perm (Fin 10)) b = b → σ ∈ A)
    (hN : ∀ i j : Fin 10, ∃ σ ∈ N, (σ : Equiv.Perm (Fin 10)) i = j) : A ⊔ N = ⊤ := by
  set G : Subgroup (Equiv.Perm (Fin 10)) := (A ⊔ N).map (alternatingGroup (Fin 10)).subtype
  have hAG : ∀ σ ∈ alternatingGroup (Fin 10), σ a = a → σ b = b → σ ∈ G := fun σ hσ ha hb =>
    Subgroup.mem_map.2 ⟨⟨σ, hσ⟩, Subgroup.mem_sup_left (hA ⟨σ, hσ⟩ ha hb), rfl⟩
  have hNG : ∀ i j : Fin 10, ∃ σ ∈ G, σ i = j := fun i j => by
    obtain ⟨σ, hσ, h⟩ := hN i j
    exact ⟨σ, Subgroup.mem_map.2 ⟨σ, Subgroup.mem_sup_right hσ, rfl⟩, h⟩
  have hprim := A10GenJ1.isPreprimitive_of hab hAG hNG
  obtain ⟨c, d, e, hca, hcb, hda, hdb, hea, heb, hcd, hce, hde⟩ := A10GenJ1.exists_three_points a b
  obtain ⟨h1, -, h3⟩ := A10GenJ1.threeCycle_facts hcd hce hde
  have hgG : (Equiv.swap c e * Equiv.swap c d) ∈ G :=
    hAG _ h1 (h3 a (Ne.symm hca) (Ne.symm hda) (Ne.symm hea))
      (h3 b (Ne.symm hcb) (Ne.symm hdb) (Ne.symm heb))
  have hle := Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same hce hcd (Ne.symm hde)) hgG
  refine eq_top_iff.2 fun σ _ => ?_
  obtain ⟨k, hk, hkσ⟩ := Subgroup.mem_map.1 (hle σ.2)
  exact (Subtype.ext hkσ : k = σ) ▸ hk

theorem alt_ten_exists_stabilizer_le (H : Subgroup (alternatingGroup (Fin 10)))
    (e : Nonempty (↥H ≃* Equiv.Perm (Fin 8))) :
    ∃ a b : Fin 10, a ≠ b ∧ ∀ σ : alternatingGroup (Fin 10),
      (σ : Equiv.Perm (Fin 10)) a = a → (σ : Equiv.Perm (Fin 10)) b = b → σ ∈ H := by
  obtain ⟨e⟩ := e
  let φ : alternatingGroup (Fin 8) →* Equiv.Perm (Fin 10) :=
    ((alternatingGroup (Fin 10)).subtype.comp H.subtype).comp
      (e.symm.toMonoidHom.comp (alternatingGroup (Fin 8)).subtype)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : (e.symm (x : Equiv.Perm (Fin 8)) : H) = e.symm (y : Equiv.Perm (Fin 8)) :=
      Subtype.ext (Subtype.ext hxy)
    exact Subtype.ext (e.symm.injective h1)
  obtain ⟨a, b, hab, h⟩ := A10GenJ1.embed_contains_stabilizer φ hφ
  refine ⟨a, b, hab, fun σ hσa hσb => ?_⟩
  obtain ⟨g, hg⟩ := h σ σ.2 hσa hσb
  have hσ : σ = ((e.symm (g : Equiv.Perm (Fin 8)) : H) : alternatingGroup (Fin 10)) :=
    Subtype.ext hg.symm
  rw [hσ]
  exact (e.symm (g : Equiv.Perm (Fin 8))).2

theorem alt_ten_stabilizer_le_closure_odd (a b : Fin 10) (H : Subgroup (alternatingGroup (Fin 10)))
    (hH : ∀ σ : alternatingGroup (Fin 10), (σ : Equiv.Perm (Fin 10)) a = a →
      (σ : Equiv.Perm (Fin 10)) b = b → σ ∈ H)
    (σ : alternatingGroup (Fin 10)) (hσa : (σ : Equiv.Perm (Fin 10)) a = a)
    (hσb : (σ : Equiv.Perm (Fin 10)) b = b) :
    σ ∈ Subgroup.closure {x : alternatingGroup (Fin 10) | x ∈ H ∧ Odd (orderOf x)} := by
  refine (Subgroup.closure_mono ?_) (A10GenJ1.stabilizer_le_closure_three_cycles a b σ hσa hσb)
  rintro t ⟨h3, ha, hb⟩
  refine ⟨hH t ha hb, ?_⟩
  have : orderOf t = 3 := by rw [← Subgroup.orderOf_coe, h3.orderOf]
  rw [this]
  exact ⟨1, by norm_num⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
