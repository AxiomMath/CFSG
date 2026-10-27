module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDelta
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaKernel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Quasithin CFSG.Sporadic.Schreier
open SolomonWong (mul_comm_of_sq_eq_one)

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem centralizer_toddE_eq (h : Setting G L D t) :
    centralizer (toddE D t : Set G) = toddE D t := by
  apply le_antisymm
  · have h1 := h.centralizer_toddE_le
    rwa [h.inf_centralizer_eq] at h1
  · intro e he
    rw [mem_centralizer_iff]
    intro f hf
    exact mul_comm_of_sq_eq_one h.toddE_sq hf he

theorem mem_toddA_of_mem_L (h : Setting G L D t) {e : G} (he : e ∈ toddE D t) (heL : e ∈ L) :
    e ∈ toddA D := by
  obtain ⟨a, ha, hea | hea⟩ := h.eq_or_eq_mul_of_mem_toddE he
  · rwa [hea]
  · exfalso
    apply h.t_not_mem
    have := mul_mem (inv_mem (toddA_le D ha)) (hea ▸ heL)
    rwa [inv_mul_cancel_left] at this

theorem normalizer_toddE_inf (h : Setting G L D t) :
    normalizer (toddE D t : Set G) ⊓ centralizer ({t} : Set G) =
      normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) := by
  have key1 : ∀ n ∈ normalizer (toddE D t : Set G) ⊓ centralizer ({t} : Set G),
      ∀ a ∈ toddA D, n * a * n⁻¹ ∈ toddA D := by
    intro n hn a ha
    have h1 : n * a * n⁻¹ ∈ toddE D t :=
      (mem_normalizer_iff.1 (mem_inf.1 hn).1 a).1 (toddA_le_toddE D t ha)
    have h2 : n * a * n⁻¹ ∈ L := (mem_normalizer_iff.1 (h.H_le (mem_inf.1 hn).2) a).1
      (toddA_le D ha)
    exact h.mem_toddA_of_mem_L h1 h2
  have key2 : ∀ n ∈ normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G),
      ∀ e ∈ toddE D t, n * e * n⁻¹ ∈ toddE D t := by
    intro n hn e he
    have hnt : n * t * n⁻¹ = t := by
      rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hn).2, mul_inv_cancel_right]
    have hnA := (mem_inf.1 hn).1
    obtain ⟨a, ha, hea | hea⟩ := h.eq_or_eq_mul_of_mem_toddE he <;> rw [hea]
    · exact toddA_le_toddE D t ((mem_normalizer_iff.1 hnA _).1 ha)
    · rw [show n * (a * t) * n⁻¹ = (n * a * n⁻¹) * (n * t * n⁻¹) by group, hnt]
      exact mul_mem (toddA_le_toddE D t ((mem_normalizer_iff.1 hnA _).1 ha)) (t_mem_toddE D t)
  apply le_antisymm
  · intro n hn
    refine mem_inf.2 ⟨mem_normalizer_iff.2 fun a => ⟨fun ha => key1 n hn a ha, fun ha => ?_⟩,
      (mem_inf.1 hn).2⟩
    have := key1 n⁻¹ (inv_mem hn) _ ha
    rwa [show n⁻¹ * (n * a * n⁻¹) * n⁻¹⁻¹ = a by group] at this
  · intro n hn
    refine mem_inf.2 ⟨mem_normalizer_iff.2 fun e => ⟨fun he => key2 n hn e he, fun he => ?_⟩,
      (mem_inf.1 hn).2⟩
    have := key2 n⁻¹ (inv_mem hn) _ he
    rwa [show n⁻¹ * (n * e * n⁻¹) * n⁻¹⁻¹ = e by group] at this

omit [Finite G] in
theorem mem_normalizer_of_conj {B : Subgroup G} {x : G} (h1 : ∀ b ∈ B, x * b * x⁻¹ ∈ B)
    (h2 : ∀ b ∈ B, x⁻¹ * b * x ∈ B) : x ∈ normalizer (B : Set G) := by
  rw [mem_normalizer_iff]
  intro b
  refine ⟨h1 b, fun hb => ?_⟩
  have := h2 _ hb
  rwa [show x⁻¹ * (x * b * x⁻¹) * x = b by group] at this

omit [Finite G] in
theorem card_toddK (D : ToddParabolic L) : Nat.card (toddK D) = 20160 := by
  rw [toddK, card_map_of_injective L.subtype_injective, D.card_K]

omit [Finite G] in
theorem toddK_le_normalizer (D : ToddParabolic L) : toddK D ≤ normalizer (toddA D : Set G) :=
  fun _ hk => mem_normalizer_of_conj (fun _ ha => conj_mem_toddA D hk ha) (fun _ ha => by
    have := conj_mem_toddA D (inv_mem hk) ha
    rwa [inv_inv] at this)

omit [Finite G] in
theorem disjoint_toddA_toddK (D : ToddParabolic L) : Disjoint (toddA D) (toddK D) := by
  rw [disjoint_iff, toddA, toddK, ← map_inf_eq _ _ _ L.subtype_injective, D.A_inf_K,
    Subgroup.map_bot]

omit [Finite G] in
theorem card_toddA_sup_toddK (D : ToddParabolic L) :
    Nat.card (toddA D ⊔ toddK D : Subgroup G) = 2 ^ 9 * 20160 := by
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ (toddK_le_normalizer D)
    (disjoint_toddA_toddK D), card_toddA, card_toddK]

theorem mem_normalizer_t (h : Setting G L D t) {B : Subgroup G} (hBL : B ≤ L) :
    t ∈ normalizer (B : Set G) :=
  mem_normalizer_of_conj (fun b hb => by rw [← h.comm (hBL hb), mul_inv_cancel_right]; exact hb)
    (fun b hb => by rw [mul_assoc, h.comm (hBL hb), inv_mul_cancel_left]; exact hb)

theorem card_toddAKt (h : Setting G L D t) :
    Nat.card (toddA D ⊔ toddK D ⊔ zpowers t : Subgroup G) = 2 ^ 10 * 20160 := by
  have hle : toddA D ⊔ toddK D ≤ L := sup_le (toddA_le D) (toddK_le D)
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (zpowers_le.2 (h.mem_normalizer_t hle)) ?_, card_toddA_sup_toddK, Nat.card_zpowers, h.order]
  · norm_num
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers h.t_sq (mem_inf.1 hx).2 with h1 | h1
    · rw [h1]
      exact one_mem _
    · exact absurd (hle (h1 ▸ (mem_inf.1 hx).1)) h.t_not_mem

omit [Finite G] in
theorem normalizer_inf_L_le (D : ToddParabolic L) :
    normalizer (toddA D : Set G) ⊓ L ≤ toddA D ⊔ toddK D := by
  intro x hx
  obtain ⟨hxN, hxL⟩ := mem_inf.1 hx
  have hmemA : ∀ y : L, (y : G) ∈ toddA D ↔ y ∈ D.A := fun y =>
    ⟨fun ⟨b, hb, hbe⟩ => (Subtype.ext hbe : b = y) ▸ hb, fun hy => ⟨y, hy, rfl⟩⟩
  have hxN' : (⟨x, hxL⟩ : L) ∈ normalizer (D.A : Set L) := by
    rw [mem_normalizer_iff]
    intro a
    rw [← hmemA, ← hmemA]
    exact mem_normalizer_iff.1 hxN (a : G)
  rw [D.normalizer_A] at hxN'
  have := mem_map_of_mem L.subtype hxN'
  rwa [Subgroup.map_sup] at this

theorem NHA_inf_le (h : Setting G L D t) :
    (normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G)) ⊓ (L ⊔ zpowers t) ≤
      toddA D ⊔ toddK D ⊔ zpowers t := by
  intro x hx
  have hxN := (mem_inf.1 (mem_inf.1 hx).1).1
  obtain ⟨l, hl, hxl | hxl⟩ :=
    exists_eq_or_eq_mul h.t_sq (fun y hy => h.comm hy) (mem_inf.1 hx).2
  · rw [hxl] at hxN ⊢
    exact mem_sup_left (normalizer_inf_L_le D (mem_inf.2 ⟨hxN, hl⟩))
  · have htN := h.mem_normalizer_t (toddA_le D)
    have hlN : l ∈ normalizer (toddA D : Set G) := by
      have e : l = x * t⁻¹ := by rw [hxl]; group
      rw [e]
      exact mul_mem hxN (inv_mem htN)
    rw [hxl]
    exact mul_mem (mem_sup_left (normalizer_inf_L_le D (mem_inf.2 ⟨hlN, hl⟩)))
      (mem_sup_right (mem_zpowers t))

theorem le_NHA (h : Setting G L D t) :
    toddA D ⊔ toddK D ⊔ zpowers t ≤
      normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) := by
  refine sup_le (sup_le (le_inf le_normalizer ((toddA_le D).trans h.le_H))
    (le_inf (toddK_le_normalizer D) h.toddK_le_H)) (zpowers_le.2 (mem_inf.2
      ⟨h.mem_normalizer_t (toddA_le D), mem_centralizer_singleton_iff.2 rfl⟩))

theorem relIndex_Lt_dvd_six (h : Setting G L D t) :
    (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 6 ∧
      ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).Normal := by
  have := h.relIndex_dvd_six
  rwa [h.inf_centralizer_eq] at this

theorem card_NHA (h : Setting G L D t) :
    2 ^ 10 * 20160 ∣ Nat.card (normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) :
      Subgroup G) ∧
    Nat.card (normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∣
      2 ^ 10 * 20160 * 6 := by
  set M := normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) with hM
  set F := L ⊔ zpowers t with hF
  refine ⟨h.card_toddAKt ▸ Subgroup.card_dvd_of_le h.le_NHA, ?_⟩
  have hMH : M ≤ centralizer ({t} : Set G) := inf_le_right
  have e : Nat.card M = Nat.card (F ⊓ M : Subgroup G) * F.relIndex M := by
    rw [← relIndex_bot_left, ← relIndex_bot_left, ← inf_relIndex_right F M,
      relIndex_mul_relIndex _ _ _ bot_le inf_le_right]
  have h6 : F.relIndex M ∣ 6 := by
    obtain ⟨h6, hn⟩ := h.relIndex_Lt_dvd_six
    have h1 := Subgroup.relIndex_dvd_index_of_normal (F.subgroupOf (centralizer ({t} : Set G)))
      (M.subgroupOf (centralizer ({t} : Set G)))
    rw [Subgroup.relIndex_subgroupOf hMH] at h1
    exact h1.trans h6
  have hFM : Nat.card (F ⊓ M : Subgroup G) ∣ 2 ^ 10 * 20160 := by
    rw [← h.card_toddAKt]
    refine Subgroup.card_dvd_of_le fun x hx => h.NHA_inf_le ?_
    exact mem_inf.2 ⟨(mem_inf.1 hx).2, (mem_inf.1 hx).1⟩
  rw [e]
  exact Nat.mul_dvd_mul hFM h6

theorem relIndex_L_dvd (h : Setting G L D t) : L.relIndex (centralizer ({t} : Set G)) ∣ 12 := by
  have hFH : L ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le h.le_H (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hLF : L.relIndex (L ⊔ zpowers t) = 2 := by
    have hc := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer L (zpowers t)
      (zpowers_le.2 (h.mem_normalizer_t le_rfl)) (by
        rw [disjoint_iff, eq_bot_iff]
        intro x hx
        rcases eq_one_or_eq_of_mem_zpowers h.t_sq (mem_inf.1 hx).2 with h1 | h1
        · rw [h1]
          exact one_mem _
        · exact absurd (h1 ▸ (mem_inf.1 hx).1) h.t_not_mem)
    rw [Nat.card_zpowers, h.order] at hc
    have e := relIndex_mul_relIndex ⊥ L (L ⊔ zpowers t) bot_le le_sup_left
    rw [relIndex_bot_left, relIndex_bot_left, hc] at e
    have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hL0) e
  rw [← relIndex_mul_relIndex L (L ⊔ zpowers t) _ le_sup_left hFH, hLF]
  exact Nat.mul_dvd_mul_left 2 h.relIndex_Lt_dvd_six.1

theorem t_not_mem_commutator (h : Setting G L D t) :
    t ∉ ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ := by
  set H := centralizer ({t} : Set G) with hHdef
  have hLn : (L.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.1 (h.H_le g.2) x).1 hx
  have htH : t ∈ H := mem_centralizer_singleton_iff.2 rfl
  set z : H ⧸ L.subgroupOf H := ((⟨t, htH⟩ : H) : H ⧸ L.subgroupOf H) with hz
  have hQ : Nat.card (H ⧸ L.subgroupOf H) ∣ 12 := by
    rw [← index_eq_card]
    exact h.relIndex_L_dvd
  have hz1 : z ≠ 1 := by
    rw [hz, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact h.t_not_mem
  have hz2 : orderOf z = 2 := by
    refine orderOf_eq_prime ?_ hz1
    rw [hz, ← QuotientGroup.mk_pow]
    have : (⟨t, htH⟩ : H) ^ 2 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h.t_sq)
    rw [this, QuotientGroup.mk_one]
  have hzc : z ∈ center (H ⧸ L.subgroupOf H) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hz, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 y.2)
  have hnot := not_mem_commutator_of_card_dvd_twelve hQ hz2 hzc
  intro ht
  apply hnot
  rw [← Subgroup.map_subtype_commutator] at ht
  obtain ⟨t', ht', htt'⟩ := ht
  have e : t' = ⟨t, htH⟩ := Subtype.ext htt'
  have hmap : (commutator H).map (QuotientGroup.mk' (L.subgroupOf H)) ≤
      commutator (H ⧸ L.subgroupOf H) := by
    rw [commutator_def, map_commutator, commutator_def]
    exact commutator_mono le_top le_top
  exact hmap ⟨t', ht', by rw [e]; rfl⟩

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
