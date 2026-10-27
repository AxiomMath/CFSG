module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Foundations.PGroupNilpotent
import CFSG.FeitThompson.Foundations.NonabelianPGroupInvariantCentralDerived

open Subgroup Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {p a : ℕ} {L P E Q : Subgroup G}

theorem le_of_natCard_prime_of_inf_ne_bot {S : Subgroup G} (hp : (Nat.card Q).Prime)
    (hQS : Q ⊓ S ≠ ⊥) : Q ≤ S := by
  have : Fact (Nat.card Q).Prime := ⟨hp⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Q ⊓ S).subgroupOf Q) with hb | ht
  · refine absurd ?_ hQS
    have h2 := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hb)
    rwa [inf_right_comm, inf_idem] at h2
  · exact (Subgroup.subgroupOf_eq_top.mp ht).trans inf_le_right

theorem conj_mem_inf_centralizer_of_mem_normalizer {g : G}
    (hg : g ∈ normalizer (P : Set G)) {z : G} (hz : z ∈ P ⊓ centralizer (P : Set G)) :
    g * z * g⁻¹ ∈ P ⊓ centralizer (P : Set G) := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg z).1 hz.1, mem_centralizer_iff.mpr fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g ∈ P := (Subgroup.mem_normalizer_iff''.1 hg x).1 hx
  have hcomm := mem_centralizer_iff.1 hz.2 _ hx'
  calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * z * g⁻¹) * x := by group

theorem conj_mem_commutator_of_mem_normalizer {g : G}
    (hg : g ∈ normalizer (P : Set G)) {z : G} (hz : z ∈ ⁅P, P⁆) : g * z * g⁻¹ ∈ ⁅P, P⁆ := by
  have hP : P.map (MulAut.conj g : G →* G) = P := Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  have hmap : (⁅P, P⁆).map (MulAut.conj g : G →* G) = ⁅P, P⁆ := by
    rw [Subgroup.map_commutator, hP]
  exact hmap ▸ ⟨z, hz, rfl⟩

open Classical in
noncomputable def centralSection (P Q : Subgroup G) : Subgroup G :=
  if Q ⊓ (P ⊓ centralizer (P : Set G)) = ⊥ then P ⊓ centralizer (P : Set G) ⊓ ⁅P, P⁆ else Q

theorem centralSection_of_inf_eq_bot (hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) = ⊥) :
    centralSection P Q = P ⊓ centralizer (P : Set G) ⊓ ⁅P, P⁆ := by
  rw [centralSection, if_pos hQ]

theorem centralSection_of_inf_ne_bot (hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) ≠ ⊥) :
    centralSection P Q = Q := by
  rw [centralSection, if_neg hQ]

structure IsPrimeFixedTISetup (G : Type*) [Group G] (p a : ℕ) (L P E Q : Subgroup G) : Prop where
  prime : p.Prime
  odd_prime : Odd p
  one_le_exponent : 1 ≤ a
  odd_natCard : Odd (Nat.card G)
  le_of_left : P ≤ L
  le_of_right : E ≤ L
  not_isMulCommutative : ¬ IsMulCommutative ↥P
  natCard_eq_pow : Nat.card P = p ^ a
  normal : (P.subgroupOf L).Normal
  coe_mul_coe : (P : Set G) * (E : Set G) = (L : Set G)
  inf_eq_bot : P ⊓ E = ⊥
  coprime : (Nat.card P).Coprime (Nat.card E)
  ne_bot : E ≠ ⊥
  isCyclic : IsCyclic ↥E
  le_commutator : Q ≤ ⁅P, P⁆
  natCard_eq_prime : Nat.card Q = p
  inf_centralizer_eq : ∀ e ∈ E, e ≠ 1 → P ⊓ centralizer ({e} : Set G) = Q
  normalizer_eq : normalizer (P : Set G) = L
  inf_conj_eq_bot : ∀ g : G, g ∉ L → P ⊓ MulAut.conj g • P = ⊥

namespace IsPrimeFixedTISetup

variable (h : IsPrimeFixedTISetup G p a L P E Q)

include h

theorem finite : Finite G :=
  Nat.finite_of_card_ne_zero fun h0 => by simpa [h0, Nat.odd_iff] using h.odd_natCard

theorem not_dvd_natCard_right : ¬ p ∣ Nat.card E := by
  refine (Nat.Prime.coprime_iff_not_dvd h.prime).1 ?_
  refine Nat.Coprime.coprime_dvd_left ?_ h.coprime
  rw [h.natCard_eq_pow]
  exact dvd_pow_self p (Nat.one_le_iff_ne_zero.mp h.one_le_exponent)

theorem natCard_middle : Nat.card L = Nat.card P * Nat.card E := by
  have h2 := natCard_mul_mul_natCard_inf P E
  rw [h.coe_mul_coe, h.inf_eq_bot] at h2
  simpa using h2

theorem exists_mem_mul_eq {l : G} (hl : l ∈ L) : ∃ u ∈ P, ∃ e ∈ E, u * e = l := by
  have hl' : l ∈ (P : Set G) * (E : Set G) := by rw [h.coe_mul_coe]; exact hl
  obtain ⟨u, hu, e, he, hue⟩ := Set.mem_mul.1 hl'
  exact ⟨u, hu, e, he, hue⟩

theorem natCard_eq_pow_factorization : Nat.card P = p ^ (Nat.card G).factorization p := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hfin : Finite G := h.finite
  obtain ⟨R, hPR⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card h.natCard_eq_pow)
  obtain ⟨k, hk⟩ := (R.isPGroup'.to_le (inf_le_left (b := L))).exists_card_eq
  have hdvd : p ^ k ∣ Nat.card P * Nat.card E := by
    rw [← hk, ← h.natCard_middle]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hdvd' : p ^ k ∣ p ^ a := by
    rw [← h.natCard_eq_pow]
    exact (Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd h.prime).2 h.not_dvd_natCard_right)).dvd_of_dvd_mul_right hdvd
  have hPeq : P = (R : Subgroup G) ⊓ L := by
    refine Subgroup.eq_of_le_of_card_ge (le_inf hPR h.le_of_left) ?_
    rw [hk, h.natCard_eq_pow]
    exact Nat.le_of_dvd (pow_pos h.prime.pos a) hdvd'
  have hnil : Group.IsNilpotent ↥(R : Subgroup G) := by
    obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
    exact isNilpotent_of_natCard_eq_prime_pow h.prime hn
  have htop : P.subgroupOf (R : Subgroup G) = ⊤ := by
    by_contra hne
    have hlt := Group.normalizerCondition_of_isNilpotent (P.subgroupOf (R : Subgroup G))
      (lt_top_iff_ne_top.mpr hne)
    rw [← Subgroup.subgroupOf_normalizer_eq hPR, h.normalizer_eq] at hlt
    obtain ⟨x, hxL, hxP⟩ := SetLike.exists_of_lt hlt
    exact hxP (Subgroup.mem_subgroupOf.mpr (hPeq ▸ ⟨x.2, Subgroup.mem_subgroupOf.mp hxL⟩))
  have hPR' : P = (R : Subgroup G) := le_antisymm hPR (Subgroup.subgroupOf_eq_top.mp htop)
  rw [hPR', R.card_eq_multiplicity]

theorem centralizer_singleton_le {z : G} (hz : z ∈ P) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) ≤ L := by
  intro g hg
  by_contra hgL
  have hfix : (MulAut.conj g)⁻¹ • z = z := by
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
    rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hg]
    group
  have hz' : z ∈ P ⊓ MulAut.conj g • P := by
    refine Subgroup.mem_inf.mpr ⟨hz, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hfix]
    exact hz
  rw [h.inf_conj_eq_bot g hgL, Subgroup.mem_bot] at hz'
  exact hz1 hz'

theorem right_le_centralizer_prime_fixed : E ≤ centralizer (Q : Set G) := by
  intro e he
  refine mem_centralizer_iff.mpr fun q hq => ?_
  by_cases he1 : e = 1
  · simp [he1]
  · rw [← h.inf_centralizer_eq e he he1] at hq
    exact mem_centralizer_singleton_iff.1 hq.2

theorem prime_fixed_le_left : Q ≤ P := h.le_commutator.trans (Subgroup.commutator_le_self P)

theorem centralSection_le : centralSection P Q ≤ P ⊓ centralizer (P : Set G) ⊓ ⁅P, P⁆ := by
  by_cases hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) = ⊥
  · rw [centralSection_of_inf_eq_bot hQ]
  · rw [centralSection_of_inf_ne_bot hQ]
    exact le_inf (le_of_natCard_prime_of_inf_ne_bot (h.natCard_eq_prime ▸ h.prime) hQ)
      h.le_commutator

theorem centralSection_ne_bot : centralSection P Q ≠ ⊥ := by
  by_cases hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) = ⊥
  · rw [centralSection_of_inf_eq_bot hQ]
    exact inf_centralizer_inf_commutator_ne_bot P h.prime h.natCard_eq_pow h.not_isMulCommutative
  · rw [centralSection_of_inf_ne_bot hQ]
    intro h0
    rw [h0] at hQ
    simp at hQ

theorem centralSection_le_middle : centralSection P Q ≤ L :=
  h.centralSection_le.trans ((inf_le_left.trans inf_le_left).trans h.le_of_left)

theorem conj_mem_centralSection {g : G} (hg : g ∈ L) {z : G} (hz : z ∈ centralSection P Q) :
    g * z * g⁻¹ ∈ centralSection P Q := by
  have hgn : g ∈ normalizer (P : Set G) := h.normalizer_eq ▸ hg
  by_cases hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) = ⊥
  · rw [centralSection_of_inf_eq_bot hQ] at hz ⊢
    exact ⟨conj_mem_inf_centralizer_of_mem_normalizer hgn hz.1,
      conj_mem_commutator_of_mem_normalizer hgn hz.2⟩
  · rw [centralSection_of_inf_ne_bot hQ] at hz ⊢
    obtain ⟨u, hu, e, he, rfl⟩ := h.exists_mem_mul_eq hg
    have hQP : Q ≤ P ⊓ centralizer (P : Set G) :=
      le_of_natCard_prime_of_inf_ne_bot (h.natCard_eq_prime ▸ h.prime) hQ
    have h1 : u * z * u⁻¹ = z := by
      rw [mem_centralizer_iff.1 (hQP hz).2 u hu]; group
    have h2 : e * z * e⁻¹ = z := by
      rw [← mem_centralizer_iff.1 (h.right_le_centralizer_prime_fixed he) z hz]; group
    have h3 : u * e * z * (u * e)⁻¹ = z := by
      calc u * e * z * (u * e)⁻¹ = u * (e * z * e⁻¹) * u⁻¹ := by group
        _ = u * z * u⁻¹ := by rw [h2]
        _ = z := h1
    rw [h3]; exact hz

theorem centralSection_normal_subgroupOf : ((centralSection P Q).subgroupOf L).Normal :=
  (Subgroup.normal_subgroupOf_iff h.centralSection_le_middle).mpr
    fun _ _ hz hk => h.conj_mem_centralSection hk hz

theorem inf_centralizer_singleton_centralSection_eq_bot
    (hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) = ⊥) {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    centralSection P Q ⊓ centralizer ({e} : Set G) = ⊥ := by
  rw [centralSection_of_inf_eq_bot hQ, eq_bot_iff, ← hQ]
  refine le_inf ?_ (inf_le_left.trans inf_le_left)
  rw [← h.inf_centralizer_eq e he he1]
  exact le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right

theorem centralizer_singleton_eq_left (hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) = ⊥) {z : G}
    (hz : z ∈ centralSection P Q) (hz1 : z ≠ 1) : centralizer ({z} : Set G) = P := by
  have hzZ : z ∈ P ⊓ centralizer (P : Set G) := (h.centralSection_le hz).1
  refine le_antisymm (fun g hg => ?_) fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.1 hzZ.2 x hx)
  obtain ⟨u, hu, e, he, rfl⟩ := h.exists_mem_mul_eq (h.centralizer_singleton_le hzZ.1 hz1 hg)
  have hcomm : u * e * z = z * (u * e) := mem_centralizer_singleton_iff.1 hg
  have huz : u * z = z * u := mem_centralizer_iff.1 hzZ.2 u hu
  have hez : e * z = z * e := by
    refine mul_left_cancel (a := u) ?_
    calc u * (e * z) = u * e * z := by group
      _ = z * (u * e) := hcomm
      _ = (z * u) * e := by group
      _ = (u * z) * e := by rw [huz]
      _ = u * (z * e) := by group
  have he1 : e = 1 := by
    by_contra he1
    have hmem : z ∈ centralSection P Q ⊓ centralizer ({e} : Set G) :=
      ⟨hz, mem_centralizer_singleton_iff.mpr hez.symm⟩
    rw [h.inf_centralizer_singleton_centralSection_eq_bot hQ he he1, Subgroup.mem_bot] at hmem
    exact hz1 hmem
  simpa [he1] using hu

theorem inf_centralizer_singleton_eq_left (hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) = ⊥) {z : G}
    (hz : z ∈ centralSection P Q) (hz1 : z ≠ 1) : L ⊓ centralizer ({z} : Set G) = P := by
  rw [h.centralizer_singleton_eq_left hQ hz hz1, inf_eq_right]
  exact h.le_of_left

theorem prime_fixed_le_center_left (hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) ≠ ⊥) :
    Q ≤ P ⊓ centralizer (P : Set G) :=
  le_of_natCard_prime_of_inf_ne_bot (h.natCard_eq_prime ▸ h.prime) hQ

theorem centralSection_le_center_middle (hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) ≠ ⊥) :
    centralSection P Q ≤ L ⊓ centralizer (L : Set G) := by
  rw [centralSection_of_inf_ne_bot hQ]
  refine le_inf (h.prime_fixed_le_left.trans h.le_of_left) fun z hz => ?_
  refine mem_centralizer_iff.mpr fun l hl => ?_
  obtain ⟨u, hu, e, he, rfl⟩ := h.exists_mem_mul_eq hl
  have huz : u * z = z * u := mem_centralizer_iff.1 (h.prime_fixed_le_center_left hQ hz).2 u hu
  have hez : z * e = e * z := mem_centralizer_iff.1 (h.right_le_centralizer_prime_fixed he) z hz
  calc u * e * z = u * (e * z) := by group
    _ = u * (z * e) := by rw [← hez]
    _ = (u * z) * e := by group
    _ = (z * u) * e := by rw [huz]
    _ = z * (u * e) := by group

theorem centralizer_singleton_eq_middle (hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) ≠ ⊥) {z : G}
    (hz : z ∈ centralSection P Q) (hz1 : z ≠ 1) : centralizer ({z} : Set G) = L := by
  have hzL := h.centralSection_le_center_middle hQ hz
  refine le_antisymm (h.centralizer_singleton_le (h.centralSection_le hz).1.1 hz1) fun l hl => ?_
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.1 hzL.2 l hl)

theorem inf_centralizer_singleton_eq_middle (hQ : Q ⊓ (P ⊓ centralizer (P : Set G)) ≠ ⊥) {z : G}
    (hz : z ∈ centralSection P Q) (hz1 : z ≠ 1) : L ⊓ centralizer ({z} : Set G) = L := by
  rw [h.centralizer_singleton_eq_middle hQ hz hz1, inf_idem]

end IsPrimeFixedTISetup

end

end CFSG.FeitThompson
