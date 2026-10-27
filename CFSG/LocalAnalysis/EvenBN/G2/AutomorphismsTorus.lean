module

public import CFSG.LocalAnalysis.EvenBN.G2.AutomorphismsTable
public import CFSG.LocalAnalysis.EvenBN.G2.TorusCentralizers

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem dvd_two_pow_facts {n k o : ℕ} (hn : 3 ≤ n) (hk : k < n) (ho : (o : ℤ) + 1 = 2 ^ n) :
    ((o : ℤ) ∣ 2 ^ k - 1 → k = 0) ∧ ¬ (o : ℤ) ∣ 2 ^ k + 1 ∧
      ∀ m : ℤ, m ≠ 0 → -3 ≤ m → m ≤ 3 → ¬ (o : ℤ) ∣ m := by
  have h8 : (8 : ℤ) ≤ 2 ^ n := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hN1 : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hN2 : 2 * (2 : ℤ) ^ k ≤ 2 ^ n := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) hk
  refine ⟨fun hd => ?_, fun hd => ?_, fun m hm hlo hhi hd => ?_⟩
  · have h0 := eq_zero_of_dvd_of_small hd (by omega) (by omega)
    have h1 : (2 : ℤ) ^ k = 1 := by omega
    rcases k with _ | k
    · rfl
    · rw [pow_succ] at h1
      omega
  · have h0 := eq_zero_of_dvd_of_small hd (by omega) (by omega)
    omega
  · exact hm (eq_zero_of_dvd_of_small hd (by omega) (by omega))

namespace Model

section WeylPairs

theorem pairA_weyl_cases (w : WeylGroup .G2) :
    (pairA (w • g2r) = 2 ∧ pairA (w • g2a) = -3) ∨ (pairA (w • g2r) = -2 ∧ pairA (w • g2a) = 3) ∨
      3 * pairA (w • g2r) + 2 * pairA (w • g2a) = 3 ∨
      3 * pairA (w • g2r) + 2 * pairA (w • g2a) = -3 := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [ha, hr] <;> decide

theorem pairB_weyl_cases (w : WeylGroup .G2) :
    pairB (w • g2r) = -1 ∨ (pairB (w • g2r) = 1 ∧ pairB (w • g2a) = -2) ∨
      2 * pairB (w • g2r) + pairB (w • g2a) = 1 ∨ 2 * pairB (w • g2r) + pairB (w • g2a) = -1 := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [ha, hr] <;> decide

end WeylPairs

section Bruhat

variable
  {K : Type} [Field K]

theorem exists_weyl_of_conj_torus {s s' g : ModGL .G2 K} (hs : s ∈ torusGroup .G2 K)
    (hs' : s' ∈ torusGroup .G2 K) (hg : g ∈ adjointGroup .G2 K) (hsg : s * g = g * s') :
    ∃ w : WeylGroup .G2, s * canonicalRep (coxeterSystem .G2) K w =
      canonicalRep (coxeterSystem .G2) K w * s' := by
  have hg' : g ∈ (adjointGroup .G2 K : Set (ModGL .G2 K)) := hg
  rw [LieType.Chevalley.adjointGroup_eq_iUnion_bruhatCell] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  set n := canonicalRep (coxeterSystem .G2) K w with hn
  have hbij := LieType.Chevalley.bijOn_bruhatCell (τ := .G2) (K := K) w
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := hbij.surjOn hw
  simp only at hbu hb hu
  have hsB : s ∈ borelGroup .G2 K := LieType.Chevalley.torusGroup_le_borelGroup hs
  have hnT : n ∈ normalizer (torusGroup .G2 K : Set (ModGL .G2 K)) :=
    (LieType.Chevalley.canonical_weyl_root_transport .G2 K).2.2 w
  have hk : s * n * s'⁻¹ * n⁻¹ ∈ torusGroup .G2 K := by
    have h1 : n * s'⁻¹ * n⁻¹ ∈ torusGroup .G2 K := (mem_normalizer_iff.1 hnT _).1 (inv_mem hs')
    rw [show s * n * s'⁻¹ * n⁻¹ = s * (n * s'⁻¹ * n⁻¹) by group]
    exact mul_mem hs h1
  have hu' : s' * u * s'⁻¹ ∈ rootSpan .G2 K (LieType.Chevalley.inversionSet w) :=
    (mem_normalizer_iff.1 (LieType.Chevalley.torusGroup_le_normalizer_rootSpan
      (fun α h => h.1) hs') u).1 hu
  have hb' : s * b * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) ∈ borelGroup .G2 K :=
    mul_mem (mul_mem (mul_mem hsB hb) (inv_mem hsB))
      (LieType.Chevalley.torusGroup_le_borelGroup hk)
  have heq : s * b * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) * n * (s' * u * s'⁻¹) = b * n * u := by
    calc s * b * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) * n * (s' * u * s'⁻¹) =
        s * (b * n * u) * s'⁻¹ := by group
      _ = b * n * u := by rw [hbu, hsg, mul_inv_cancel_right]
  have hinj := hbij.injOn (x₁ := (s * b * s⁻¹ * (s * n * s'⁻¹ * n⁻¹), s' * u * s'⁻¹))
    (x₂ := (b, u)) ⟨hb', hu'⟩ ⟨hb, hu⟩ heq
  simp only [Prod.mk.injEq] at hinj
  obtain ⟨h1, -⟩ := hinj
  obtain ⟨h₀, hh₀, u₀, hu₀, rfl⟩ := exists_torus_mul_of_mem_borel hb
  have hsu₀ : s * u₀ * s⁻¹ ∈ posUnipotent .G2 K := torus_conj_mem_posUnipotent hs hu₀
  have hc : s * h₀ = h₀ * s := torus_mul_comm hs hh₀
  have e2 : s * u₀ * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) = u₀ := by
    calc s * u₀ * s⁻¹ * (s * n * s'⁻¹ * n⁻¹) =
        h₀⁻¹ * (s * (h₀ * u₀) * s⁻¹ * (s * n * s'⁻¹ * n⁻¹)) := by
          rw [← mul_assoc s h₀, hc]
          group
      _ = u₀ := by rw [h1, inv_mul_cancel_left]
  have hk1 : s * n * s'⁻¹ * n⁻¹ = 1 := by
    have hkU : s * n * s'⁻¹ * n⁻¹ ∈ posUnipotent .G2 K := by
      rw [eq_inv_mul_of_mul_eq e2]
      exact mul_mem (inv_mem hsu₀) hu₀
    have h := LieType.Chevalley.torusGroup_inf_posUnipotent (τ := .G2) (R := K)
    rw [eq_bot_iff] at h
    exact mem_bot.1 (h (mem_inf.2 ⟨hk, hkU⟩))
  refine ⟨w, ?_⟩
  calc s * n = s * n * s'⁻¹ * n⁻¹ * (n * s') := by group
    _ = n * s' := by rw [hk1, one_mul]

variable [CharP K 2]

theorem zpow_eq_of_conj_canonicalRep (i : Fin Tag.G2.rank) {w : WeylGroup .G2} {t t' : Kˣ}
    (h : torusElt .G2 K i t * canonicalRep (coxeterSystem .G2) K w =
      canonicalRep (coxeterSystem .G2) K w * torusElt .G2 K i t')
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    t ^ (∑ j, Tag.G2.cartan i j * (w • α) j) = t' ^ (∑ j, Tag.G2.cartan i j * α j) := by
  set n := canonicalRep (coxeterSystem .G2) K w
  have h1 : torusElt .G2 K i t * pinnedX .G2 K (w • α) 1 * (torusElt .G2 K i t)⁻¹ =
      pinnedX .G2 K (w • α) ((t' ^ (∑ j, Tag.G2.cartan i j * α j) : Kˣ) : K) := by
    calc torusElt .G2 K i t * pinnedX .G2 K (w • α) 1 * (torusElt .G2 K i t)⁻¹ =
        torusElt .G2 K i t * (n * pinnedX .G2 K α 1 * n⁻¹) * (torusElt .G2 K i t)⁻¹ := by
          rw [canonicalRep_conj w hα]
      _ = n * (torusElt .G2 K i t' * pinnedX .G2 K α 1 * (torusElt .G2 K i t')⁻¹) * n⁻¹ := by
          rw [show torusElt .G2 K i t * (n * pinnedX .G2 K α 1 * n⁻¹) *
              (torusElt .G2 K i t)⁻¹ = (torusElt .G2 K i t * n) * pinnedX .G2 K α 1 *
              (torusElt .G2 K i t * n)⁻¹ by group, h]
          group
      _ = _ := by rw [root_torus_conjugation i hα t' 1, canonicalRep_conj w hα, mul_one]
  rw [root_torus_conjugation i (IsRoot.smul hα w) t 1, mul_one] at h1
  exact Units.ext (pinnedX_injective .G2 K _ h1)

theorem eq_zero_of_conj_torusElt_pow {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) {k : ℕ}
    (hk : k < n) {i : Fin Tag.G2.rank} (hi : i = g2ir ∨ i = g2ia) {t₀ : Kˣ}
    (ht₀ : ∀ y : Kˣ, y ∈ zpowers t₀) {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K)
    (h : torusElt .G2 K i t₀ * g = g * torusElt .G2 K i (t₀ ^ 2 ^ k)) : k = 0 := by
  obtain ⟨w, hw⟩ := exists_weyl_of_conj_torus (torusElt_mem_torusGroup _ _)
    (torusElt_mem_torusGroup _ _) hg h
  have ho : (orderOf t₀ : ℤ) + 1 = 2 ^ n := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [orderOf_eq_card_of_forall_mem_zpowers ht₀, Nat.card_units, hK, Nat.cast_sub h1]
    push_cast
    ring
  have hdvd : ∀ {α : Fin Tag.G2.rank → ℤ}, IsRoot .G2 α → (orderOf t₀ : ℤ) ∣
      (∑ j, Tag.G2.cartan i j * (w • α) j) - 2 ^ k * (∑ j, Tag.G2.cartan i j * α j) := by
    intro α hα
    have e := zpow_eq_of_conj_canonicalRep i hw hα
    rw [← zpow_natCast, ← zpow_mul] at e
    have := orderOf_dvd_sub_of_zpow_eq e
    push_cast at this
    exact this
  have hr := hdvd isRoot_g2r
  have ha := hdvd isRoot_g2a
  obtain ⟨h1, h2, h3⟩ := dvd_two_pow_facts hn hk ho
  rcases hi with rfl | rfl
  · change (orderOf t₀ : ℤ) ∣ pairA (w • g2r) - 2 ^ k * pairA g2r at hr
    change (orderOf t₀ : ℤ) ∣ pairA (w • g2a) - 2 ^ k * pairA g2a at ha
    rw [show pairA g2r = 2 by decide] at hr
    rw [show pairA g2a = -3 by decide] at ha
    have h32 : (orderOf t₀ : ℤ) ∣ 3 * pairA (w • g2r) + 2 * pairA (w • g2a) := by
      convert dvd_add (dvd_mul_of_dvd_right hr 3) (dvd_mul_of_dvd_right ha 2) using 1
      ring
    rcases pairA_weyl_cases w with ⟨ex, ey⟩ | ⟨ex, ey⟩ | e | e
    · rw [ex] at hr
      rw [ey] at ha
      exact h1 (by convert dvd_add hr ha using 1; ring)
    · rw [ex] at hr
      rw [ey] at ha
      exact absurd (by convert dvd_add hr ha using 1; ring) h2
    · rw [e] at h32
      exact absurd h32 (h3 3 (by norm_num) (by norm_num) (by norm_num))
    · rw [e] at h32
      exact absurd h32 (h3 (-3) (by norm_num) (by norm_num) (by norm_num))
  · change (orderOf t₀ : ℤ) ∣ pairB (w • g2r) - 2 ^ k * pairB g2r at hr
    change (orderOf t₀ : ℤ) ∣ pairB (w • g2a) - 2 ^ k * pairB g2a at ha
    rw [show pairB g2r = -1 by decide] at hr
    rw [show pairB g2a = 2 by decide] at ha
    have h21 : (orderOf t₀ : ℤ) ∣ 2 * pairB (w • g2r) + pairB (w • g2a) := by
      convert dvd_add (dvd_mul_of_dvd_right hr 2) ha using 1
      ring
    rcases pairB_weyl_cases w with ex | ⟨ex, -⟩ | e | e
    · rw [ex] at hr
      exact h1 (by convert hr using 1; ring)
    · rw [ex] at hr
      exact absurd (by convert hr using 1; ring) h2
    · rw [e] at h21
      exact absurd h21 (h3 1 (by norm_num) (by norm_num) (by norm_num))
    · rw [e] at h21
      exact absurd h21 (h3 (-1) (by norm_num) (by norm_num) (by norm_num))

end Bruhat

section Yamada322

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [CharP K 2] in
theorem conj_mem_centralizer_inn_iff {H : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K)
    {g : adjointGroup .G2 K} :
    MulAut.conj g ∈ centralizer (inn H : Set (MulAut (adjointGroup .G2 K))) ↔
      (g : ModGL .G2 K) ∈ centralizer (H : Set (ModGL .G2 K)) := by
  rw [mem_centralizer_inn_iff, mem_centralizer_iff]
  constructor
  · intro h y hy
    have h1 := congrArg Subtype.val (h ⟨y, hH hy⟩ hy)
    rw [MulAut.conj_apply, coe_mul, coe_mul, coe_inv] at h1
    calc y * g = (g : ModGL .G2 K) * y * (g : ModGL .G2 K)⁻¹ * g := by rw [h1]
      _ = g * y := by group
  · intro h x hx
    refine Subtype.ext ?_
    rw [MulAut.conj_apply, coe_mul, coe_mul, coe_inv, ← h _ hx]
    group

theorem centralizer_inn_eq_of_torusElt {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n)
    {i : Fin Tag.G2.rank} (hi : i = g2ir ∨ i = g2ia) {J : Subgroup (ModGL .G2 K)}
    (hJC : J ≤ adjointGroup .G2 K) (hJ : ∀ t : Kˣ, torusElt .G2 K i t ∈ J) :
    centralizer (inn J : Set (MulAut (adjointGroup .G2 K))) =
      inn (centralizer (J : Set (ModGL .G2 K))) := by
  refine le_antisymm (fun α hα => ?_) inn_centralizer_le
  obtain ⟨g, k, hk, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK (by omega) α
  obtain ⟨t₀, ht₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hfix := mem_centralizer_inn_iff.1 hα ⟨torusElt .G2 K i t₀, torusElt_mem_adjointGroup i t₀⟩
    (hJ t₀)
  have h1 := congrArg Subtype.val hfix
  rw [MulAut.mul_apply, MulAut.conj_apply, coe_mul, coe_mul, coe_inv,
    fieldAut_pow_torusElt] at h1
  have h2 : torusElt .G2 K i t₀ * g = g * torusElt .G2 K i (t₀ ^ 2 ^ k) := by
    calc torusElt .G2 K i t₀ * g =
        (g : ModGL .G2 K) * torusElt .G2 K i (t₀ ^ 2 ^ k) * (g : ModGL .G2 K)⁻¹ * g := by
          rw [h1]
      _ = g * torusElt .G2 K i (t₀ ^ 2 ^ k) := by group
  obtain rfl := eq_zero_of_conj_torusElt_pow hK hn hk hi ht₀ g.2 h2
  rw [pow_zero, mul_one] at hα ⊢
  exact conj_mem_inn ((conj_mem_centralizer_inn_iff hJC).1 hα)

theorem yamada_3_22 {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) :
    centralizer (inn (J₁ K) : Set (MulAut (adjointGroup .G2 K))) =
        inn (centralizer (J₁ K : Set (ModGL .G2 K))) ∧
      centralizer (inn (J₂ K) : Set (MulAut (adjointGroup .G2 K))) =
        inn (centralizer (J₂ K : Set (ModGL .G2 K))) :=
  ⟨centralizer_inn_eq_of_torusElt hK hn (Or.inl rfl) (torusFix_le_adjointGroup K _)
      torusElt_r_mem_J₁,
    centralizer_inn_eq_of_torusElt hK hn (Or.inr rfl) (torusFix_le_adjointGroup K _)
      torusElt_a_mem_J₂⟩

theorem centralizer_inn_centralizer_torusFix_le {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {s : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) :
    centralizer (inn (centralizer (torusFix K s : Set (ModGL .G2 K))) :
        Set (MulAut (adjointGroup .G2 K))) ≤
      inn (centralizer (torusFix K s : Set (ModGL .G2 K))) := by
  intro α hα
  have hSs : rootSubgroup .G2 K s ≤ centralizer (torusFix K s : Set (ModGL .G2 K)) :=
    fun x hx => mem_centralizer_iff.2 fun j hj => (mem_centralizer_iff.1 hj.2 x hx).symm
  have hJJ : torusFix K s ≤ centralizer (torusFix K s : Set (ModGL .G2 K)) :=
    fun x hx => mem_centralizer_iff.2 fun j hj => J_comm hj.1 hx.1
  have h1 : α ∈ centralizer (inn (rootSubgroup .G2 K s) : Set (MulAut (adjointGroup .G2 K))) :=
    centralizer_le (SetLike.coe_subset_coe.2 (inn_mono hSs)) hα
  rw [yamada_3_19_1 hK hn hs] at h1
  obtain ⟨g, -, rfl⟩ := mem_inn.1 h1
  have h2 : MulAut.conj g ∈ centralizer (inn (torusFix K s) : Set (MulAut (adjointGroup .G2 K))) :=
    centralizer_le (SetLike.coe_subset_coe.2 (inn_mono hJJ)) hα
  exact conj_mem_inn ((conj_mem_centralizer_inn_iff (torusFix_le_adjointGroup K s)).1 h2)

theorem yamada_3_22_centralizer {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) :
    centralizer (inn (centralizer (J₁ K : Set (ModGL .G2 K))) :
        Set (MulAut (adjointGroup .G2 K))) ≤ inn (centralizer (J₁ K : Set (ModGL .G2 K))) ∧
      centralizer (inn (centralizer (J₂ K : Set (ModGL .G2 K))) :
        Set (MulAut (adjointGroup .G2 K))) ≤ inn (centralizer (J₂ K : Set (ModGL .G2 K))) :=
  ⟨centralizer_inn_centralizer_torusFix_le hK hn isRoot_g2c,
    centralizer_inn_centralizer_torusFix_le hK hn isRoot_g2v⟩

end Yamada322

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

theorem normalizer_inf_centralizer_le_of
    [Finite K] {H H' : Subgroup (ModGL .G2 K)}
    (h : centralizer (Model.inn H : Set (MulAut (adjointGroup .G2 K))) ≤ Model.inn H') :
    normalizer (L : Set G) ⊓ centralizer (d.image H : Set G) ≤
      d.image H' ⊔ centralizer (L : Set G) := by
  rintro x ⟨hxN, hxc⟩
  exact (d.act_mem_inn_iff hxN).1
    (h (Model.mem_centralizer_inn_iff.2 ((d.act_mem_centralizer_inn_iff hxN).2 hxc)))

theorem image_centralizer {H : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K) :
    d.image (centralizer (H : Set (ModGL .G2 K))) = L ⊓ centralizer (d.image H : Set G) := by
  have h1 := d.image_inf_centralizer (adjointGroup .G2 K) hH
  rw [d.image_inf, d.image_adjointGroup, inf_eq_right.2 (d.image_le _)] at h1
  exact h1

section Yamada322G

variable
  [Finite K] [CharP K 2]

theorem yamada_3_22_G {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) :
    normalizer (L : Set G) ⊓ centralizer (d.J₁ : Set G) ≤
        (L ⊓ centralizer (d.J₁ : Set G)) ⊔ centralizer (L : Set G) ∧
      normalizer (L : Set G) ⊓ centralizer (d.J₂ : Set G) ≤
        (L ⊓ centralizer (d.J₂ : Set G)) ⊔ centralizer (L : Set G) := by
  obtain ⟨h1, h2⟩ := Model.yamada_3_22 hK hn
  refine ⟨?_, ?_⟩
  · rw [J₁, ← d.image_centralizer (Model.torusFix_le_adjointGroup K _)]
    exact d.normalizer_inf_centralizer_le_of h1.le
  · rw [J₂, ← d.image_centralizer (Model.torusFix_le_adjointGroup K _)]
    exact d.normalizer_inf_centralizer_le_of h2.le

theorem yamada_3_22_centralizer_G {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    normalizer (L : Set G) ⊓ centralizer ((L ⊓ centralizer (d.J₁ : Set G) : Subgroup G) : Set G) ≤
        (L ⊓ centralizer (d.J₁ : Set G)) ⊔ centralizer (L : Set G) ∧
      normalizer (L : Set G) ⊓
          centralizer ((L ⊓ centralizer (d.J₂ : Set G) : Subgroup G) : Set G) ≤
        (L ⊓ centralizer (d.J₂ : Set G)) ⊔ centralizer (L : Set G) := by
  obtain ⟨h1, h2⟩ := Model.yamada_3_22_centralizer hK hn
  refine ⟨?_, ?_⟩
  · rw [J₁, ← d.image_centralizer (Model.torusFix_le_adjointGroup K _)]
    exact d.normalizer_inf_centralizer_le_of h1
  · rw [J₂, ← d.image_centralizer (Model.torusFix_le_adjointGroup K _)]
    exact d.normalizer_inf_centralizer_le_of h2

end Yamada322G

end G2Data

end CFSG.LocalAnalysis.EvenBN.G2
