module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixTInvariant
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.CyclicSubgroup.NormalizerCommutator

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

@[expose] def tripleNormalizer (W₁ W₂ W₃ : Subgroup G) : Subgroup G :=
  normalizer (W₁ : Set G) ⊓ normalizer (W₂ : Set G) ⊓ normalizer (W₃ : Set G)

private theorem conj_eq_or_inv_of_mem_normalizer_of_card_three {W : Subgroup G}
    (hW : Nat.card W = 3) {h : G} (hh : h ∈ Subgroup.normalizer (W : Set G)) :
    (∀ w ∈ W, h * w * h⁻¹ = w) ∨ (∀ w ∈ W, h * w * h⁻¹ = w⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have : IsCyclic W := isCyclic_of_prime_card hW
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  have hg3 : orderOf (g : G) = 3 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hW]
  have hgen : ∀ w ∈ W, ∃ j : ℤ, (g : G) ^ j = w := by
    intro w hw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, hw⟩)
    exact ⟨j, by rw [← Subgroup.coe_zpow, hj]⟩
  have hc : h * (g : G) * h⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hh _).mp g.2
  obtain ⟨k, hk⟩ := hgen _ hc
  rw [← zpow_mod_orderOf, hg3] at hk
  have hk0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have hk3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hg1 : (g : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg3
    norm_num at hg3
  obtain h0 | h1 | h2 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨
      k % ((3 : ℕ) : ℤ) = 2 := by omega
  · exfalso
    rw [h0, zpow_zero] at hk
    apply hg1
    have := congrArg (fun x => h⁻¹ * x * h) hk
    simpa [mul_assoc] using this.symm
  · left
    intro w hw
    obtain ⟨j, rfl⟩ := hgen w hw
    rw [h1, zpow_one] at hk
    rw [← conj_zpow, ← hk]
  · right
    intro w hw
    obtain ⟨j, rfl⟩ := hgen w hw
    rw [h2] at hk
    have hinv : (g : G) ^ (2 : ℤ) = (g : G)⁻¹ := by
      have h3' : (g : G) ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one _
      rw [eq_inv_iff_mul_eq_one, zpow_two, ← h3', pow_three, mul_assoc]
    rw [← conj_zpow, ← hk, hinv, inv_zpow]

private theorem mem_normalizer_of_conj_eq_inv {W : Subgroup G} {t : G}
    (h : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) : t ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [h w hw]
    exact W.inv_mem hw
  · intro hw
    set u : G := t * w * t⁻¹ with hu
    have hmem : u ∈ W := by rwa [hu]
    have hinv : t * u⁻¹ * t⁻¹ = u := by
      calc t * u⁻¹ * t⁻¹ = (t * u * t⁻¹)⁻¹ := by group
        _ = (u⁻¹)⁻¹ := by rw [h u hmem]
        _ = u := by simp
    have hw' : w = u⁻¹ := by
      calc w = t⁻¹ * u * t := by rw [hu]; group
        _ = t⁻¹ * (t * u⁻¹ * t⁻¹) * t := by rw [hinv]
        _ = u⁻¹ := by group
    rw [hw']
    exact W.inv_mem hmem

private theorem mem_normalizer_of_comm {W U : Subgroup G} {t : G}
    (h : ∀ w ∈ U, t * w = w * t) (hWU : W ≤ U) :
    t ∈ Subgroup.normalizer (W : Set G) := by
  have htU : t ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => (h w hw).symm
  exact Subgroup.centralizer_le_normalizer (W : Set G)
    (Subgroup.centralizer_le (s := (W : Set G)) (t := (U : Set G))
      (fun x hx => hWU hx) htU)

private theorem sq_mem_centralizer_of_mem_normalizer_of_card_three {W : Subgroup G}
    (hW : Nat.card W = 3) {t : G} (ht : t ∈ Subgroup.normalizer (W : Set G)) :
    t ^ 2 ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rcases conj_eq_or_inv_of_mem_normalizer_of_card_three hW ht with h | h
  · intro w hw
    have hcomm : t * w = w * t := by
      calc t * w = (t * w * t⁻¹) * t := by group
        _ = w * t := by rw [h w hw]
    calc w * t ^ 2 = (w * t) * t := by rw [pow_two]; group
      _ = (t * w) * t := by rw [hcomm]
      _ = t ^ 2 * w := by rw [mul_assoc, ← hcomm, pow_two, mul_assoc]
  · intro w hw
    have hconj : t ^ 2 * w * (t ^ 2)⁻¹ = w := by
      calc t ^ 2 * w * (t ^ 2)⁻¹ = t * (t * w * t⁻¹) * t⁻¹ := by
            rw [pow_two]; group
        _ = t * w⁻¹ * t⁻¹ := by rw [h w hw]
        _ = (t * w * t⁻¹)⁻¹ := by group
        _ = (w⁻¹)⁻¹ := by rw [h w hw]
        _ = w := by simp
    calc w * t ^ 2 = (t ^ 2 * w * (t ^ 2)⁻¹) * t ^ 2 := by rw [hconj]
      _ = t ^ 2 * w := by rw [pow_two]; group

private theorem commutator_mem_centralizer_of_mem_normalizer_of_card_three {W : Subgroup G}
    (hW : Nat.card W = 3) {t u : G} (ht : t ∈ Subgroup.normalizer (W : Set G))
    (hu : u ∈ Subgroup.normalizer (W : Set G)) :
    t * u * t⁻¹ * u⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic W := isCyclic_of_prime_card hW
  have hle : ⁅Subgroup.normalizer (W : Set G), Subgroup.normalizer (W : Set G)⁆ ≤
      Subgroup.centralizer (W : Set G) :=
    CFSG.GroupTheory.CyclicSubgroup.commutator_le_centralizer W _ _ le_rfl le_rfl
  have hmem := Subgroup.commutator_le.mp hle t ht u hu
  simpa only [commutatorElement_def] using hmem

private theorem four_dvd_card_of_commute {X : Type*} [Group X] [Finite X] {a b : X}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hc : a * b = b * a) : 4 ∣ Nat.card X := by
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : b * (a * b) = a := by rw [← mul_assoc, ← hc, mul_assoc, hb, mul_one]
  have h3 : a * b * a = b := by rw [mul_assoc, ← hc, h1]
  have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
  have hia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hiab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h5
  let V : Subgroup X :=
    { carrier := {1, a, b, a * b}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp only [one_mul, mul_one, ha, hb, h1, h2, h3, h4, h5, ← hc, true_or, or_true]
      one_mem' := Set.mem_insert _ _
      inv_mem' := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · simp [hia]
        · simp [hib]
        · simp [hiab] }
  have hab1 : a * b ≠ 1 := fun h => hab (by rw [← hib, ← mul_eq_one_iff_eq_inv.mp h])
  have haab : a ≠ a * b := fun h => hb1 (by
    have := congrArg (a⁻¹ * ·) h
    simpa using this.symm)
  have hbab : b ≠ a * b := fun h => ha1 (by
    have := congrArg (· * b⁻¹) h
    simpa using this.symm)
  have hV : Nat.card V = 4 := by
    show Nat.card ↥({1, a, b, a * b} : Set X) = 4
    rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair hbab]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, haab⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
  rw [← hV]
  exact card_subgroup_dvd_card V

theorem IsE27InvConfig.t₁_mem_tripleNormalizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) : t₁ ∈ tripleNormalizer W₁ W₂ W₃ := by
  rw [tripleNormalizer]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact mem_normalizer_of_conj_eq_inv hc.inv₁
  · exact mem_normalizer_of_comm hc.comm₁ le_sup_left
  · exact mem_normalizer_of_comm hc.comm₁ le_sup_right

theorem IsE27InvConfig.t₂_mem_tripleNormalizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) : t₂ ∈ tripleNormalizer W₁ W₂ W₃ := by
  rw [tripleNormalizer]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact mem_normalizer_of_comm hc.comm₂ le_sup_left
  · exact mem_normalizer_of_conj_eq_inv hc.inv₂
  · exact mem_normalizer_of_comm hc.comm₂ le_sup_right

theorem IsE27InvConfig.t₃_mem_tripleNormalizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) : t₃ ∈ tripleNormalizer W₁ W₂ W₃ := by
  rw [tripleNormalizer]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact mem_normalizer_of_comm hc.comm₃ le_sup_left
  · exact mem_normalizer_of_comm hc.comm₃ le_sup_right
  · exact mem_normalizer_of_conj_eq_inv hc.inv₃

theorem IsE27InvConfig.tripleNormalizer_le_normalizer
    {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    tripleNormalizer W₁ W₂ W₃ ≤ Subgroup.normalizer (V : Set G) := by
  intro g hg
  rw [tripleNormalizer] at hg
  have h1 : W₁.map (MulAut.conj g) = W₁ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg.1.1
  have h2 : W₂.map (MulAut.conj g) = W₂ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg.1.2
  have h3 : W₃.map (MulAut.conj g) = W₃ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg.2
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hc.join, Subgroup.map_sup,
    Subgroup.map_sup, h1, h2, h3]

theorem IsE27InvConfig.sq_mem_centralizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) {g : G}
    (hg : g ∈ tripleNormalizer W₁ W₂ W₃) : g ^ 2 ∈ centralizer (V : Set G) := by
  rw [tripleNormalizer] at hg
  have h1 := sq_mem_centralizer_of_mem_normalizer_of_card_three hc.card₁ hg.1.1
  have h2 := sq_mem_centralizer_of_mem_normalizer_of_card_three hc.card₂ hg.1.2
  have h3 := sq_mem_centralizer_of_mem_normalizer_of_card_three hc.card₃ hg.2
  rw [hc.join, CFSG.centralizer_sup_eq (W₁ ⊔ W₂) W₃, CFSG.centralizer_sup_eq W₁ W₂]
  exact ⟨⟨h1, h2⟩, h3⟩

theorem IsE27InvConfig.commutator_mem_centralizer {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) {g g' : G}
    (hg : g ∈ tripleNormalizer W₁ W₂ W₃) (hg' : g' ∈ tripleNormalizer W₁ W₂ W₃) :
    g * g' * g⁻¹ * g'⁻¹ ∈ centralizer (V : Set G) := by
  rw [tripleNormalizer] at hg hg'
  have h1 := commutator_mem_centralizer_of_mem_normalizer_of_card_three hc.card₁
    hg.1.1 hg'.1.1
  have h2 := commutator_mem_centralizer_of_mem_normalizer_of_card_three hc.card₂
    hg.1.2 hg'.1.2
  have h3 := commutator_mem_centralizer_of_mem_normalizer_of_card_three hc.card₃
    hg.2 hg'.2
  rw [hc.join, CFSG.centralizer_sup_eq (W₁ ⊔ W₂) W₃, CFSG.centralizer_sup_eq W₁ W₂]
  exact ⟨⟨h1, h2⟩, h3⟩

theorem four_dvd_relindex_of_klein {Y : Type} [Group Y] [Finite Y] {B V : Subgroup Y}
    {a b : Y} (ha : a ∈ B ⊓ normalizer (V : Set Y))
    (hb : b ∈ B ⊓ normalizer (V : Set Y))
    (haa : a ^ 2 ∈ centralizer (V : Set Y)) (hbb : b ^ 2 ∈ centralizer (V : Set Y))
    (hab : a * b * a⁻¹ * b⁻¹ ∈ centralizer (V : Set Y))
    (ha1 : a ∉ centralizer (V : Set Y)) (hb1 : b ∉ centralizer (V : Set Y))
    (hab1 : a * b ∉ centralizer (V : Set Y)) :
    4 ∣ (B ⊓ centralizer (V : Set Y)).relIndex (B ⊓ normalizer (V : Set Y)) := by
  let N : Subgroup Y := B ⊓ Subgroup.normalizer (V : Set Y)
  let C : Subgroup Y := B ⊓ Subgroup.centralizer (V : Set Y)
  haveI hnorm : (C.subgroupOf N).Normal :=
    Subgroup.inf_subgroupOf_inf_normal_of_right B (Subgroup.centralizer (V : Set Y))
      (Subgroup.normalizer (V : Set Y))
  haveI : Finite (↥N ⧸ C.subgroupOf N) := Quotient.finite _
  let aN : N := ⟨a, ha⟩
  let bN : N := ⟨b, hb⟩
  let qa : ↥N ⧸ C.subgroupOf N := QuotientGroup.mk aN
  let qb : ↥N ⧸ C.subgroupOf N := QuotientGroup.mk bN
  have ha2 : qa * qa = 1 := by
    change ((aN * aN : N) : ↥N ⧸ C.subgroupOf N) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change a * a ∈ B ⊓ Subgroup.centralizer (V : Set Y)
    exact ⟨B.mul_mem ha.1 ha.1, by simpa [aN, pow_two] using haa⟩
  have hb2 : qb * qb = 1 := by
    change ((bN * bN : N) : ↥N ⧸ C.subgroupOf N) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change b * b ∈ B ⊓ Subgroup.centralizer (V : Set Y)
    exact ⟨B.mul_mem hb.1 hb.1, by simpa [bN, pow_two] using hbb⟩
  have haq1 : qa ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    have h' : a ∈ B ⊓ Subgroup.centralizer (V : Set Y) := by simpa [C, aN] using h
    exact ha1 h'.2
  have hbq1 : qb ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    have h' : b ∈ B ⊓ Subgroup.centralizer (V : Set Y) := by simpa [C, bN] using h
    exact hb1 h'.2
  have habar1 : qa * qb ≠ 1 := by
    intro h
    change ((aN * bN : N) : ↥N ⧸ C.subgroupOf N) = 1 at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    have h' : a * b ∈ B ⊓ Subgroup.centralizer (V : Set Y) := by
      simpa [C, aN, bN] using h
    exact hab1 h'.2
  have hcomm : qa * qb = qb * qa := by
    have hcN : aN * bN * aN⁻¹ * bN⁻¹ ∈ C.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      change a * b * a⁻¹ * b⁻¹ ∈ B ⊓ Subgroup.centralizer (V : Set Y)
      exact ⟨B.mul_mem (B.mul_mem (B.mul_mem ha.1 hb.1) (B.inv_mem ha.1))
        (B.inv_mem hb.1), by simpa [aN, bN] using hab⟩
    have hq : ((aN * bN * aN⁻¹ * bN⁻¹ : N) : ↥N ⧸ C.subgroupOf N) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hcN
    have hq' : qa * qb * qa⁻¹ * qb⁻¹ = 1 := by
      simpa [qa, qb] using hq
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hq'
    exact hq'
  have hne : qa ≠ qb := by
    intro h
    exact habar1 (by rw [← h]; exact ha2)
  have h4 : 4 ∣ Nat.card (↥N ⧸ C.subgroupOf N) :=
    four_dvd_card_of_commute ha2 hb2 haq1 hbq1 hne hcomm
  simpa [Subgroup.relIndex, Subgroup.index, C, N] using h4

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
