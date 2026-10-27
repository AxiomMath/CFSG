module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.TransportJ
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.M12Std.PropA

structure RbcModel {P : Type*} [Group P] (K D : Subgroup P) (t₀ x₀ : P) : Prop where
  Y_comm : ∀ a ∈ centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)),
    ∀ b ∈ centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)), a * b = b * a
  Y_exp4 : ∀ y ∈ centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)), y ^ 4 = 1
  Y_inf_D : centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)) ⊓ D = zpowers x₀
  normalizer_J : K ⊓ normalizer (jOf D x₀ : Set P) = K ⊓ centralizer ({x₀} : Set P)
  of_exp2 : (∀ y ∈ centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)),
      y * y = 1) →
    centralizer ((K ⊓ centralizer ({x₀} : Set P) : Subgroup P) : Set P) ⊓
        (centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P))) =
      closure ({t₀, x₀} : Set P) ∧
    ∃ o ∈ centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)),
      ∃ n ∈ K ⊓ centralizer ({x₀} : Set P), n * o * n⁻¹ = o * x₀
  perfect_cent : ∀ c ∈ K, c ^ 2 ∈ zpowers t₀ → c ∉ zpowers t₀ →
    ∀ Q ≤ D ⊓ centralizer ({c} : Set P), ⁅Q, Q⁆ = Q → Q = ⊥ ∨
      ∃ x ∈ D, orderOf x = 2 ∧ Nat.card ↥(D ⊓ centralizer ({x} : Set P)) = 240 ∧
        Q = jOf D x ∧ D ⊓ centralizer (jOf D x : Set P) = zpowers x
  normal_small : ∀ N : Subgroup P, N ≤ K ⊓ centralizer ({x₀} : Set P) →
    (N.subgroupOf (K ⊓ centralizer ({x₀} : Set P))).Normal → jOf D x₀ ≤ N → x₀ ∉ N →
      Nat.card ↥N ≤ 120

structure RbcFacts {G : Type*} [Group G] (L : Subgroup G) (t x : G) : Prop where
  Y_comm : ∀ a ∈ centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)),
    ∀ b ∈ centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)), a * b = b * a
  Y_exp4 : ∀ y ∈ centralizer (jOf L x : Set G) ⊓
    (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)), y ^ 4 = 1
  Y_inf_D : centralizer (jOf L x : Set G) ⊓
    (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) ⊓ L = zpowers x
  normalizer_J : centralizer ({t} : Set G) ⊓ normalizer (jOf L x : Set G) =
    centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)
  of_exp2 : (∀ y ∈ centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)), y * y = 1) →
    centralizer ((centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :
        Set G) ⊓ (centralizer (jOf L x : Set G) ⊓
          (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) =
      closure ({t, x} : Set G) ∧
    ∃ o ∈ centralizer (jOf L x : Set G) ⊓
        (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)),
      ∃ n ∈ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G), n * o * n⁻¹ = o * x
  perfect_cent : ∀ c ∈ centralizer ({t} : Set G), c ^ 2 ∈ zpowers t → c ∉ zpowers t →
    ∀ Q ≤ L ⊓ centralizer ({c} : Set G), ⁅Q, Q⁆ = Q → Q = ⊥ ∨
      ∃ x' ∈ L, orderOf x' = 2 ∧ Nat.card ↥(L ⊓ centralizer ({x'} : Set G)) = 240 ∧
        Q = jOf L x' ∧ L ⊓ centralizer (jOf L x' : Set G) = zpowers x'
  normal_small : ∀ N : Subgroup G, N ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) →
    (N.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))).Normal →
      jOf L x ≤ N → x ∉ N → Nat.card ↥N ≤ 120

section Transport

variable {G P : Type*} [Group G] [Group P] {L : Subgroup G} {t x : G} {K D : Subgroup P}
  {t₀ x₀ : P} {ι : ↥(centralizer ({t} : Set G)) →* P}

private theorem mem_push_iff {C : Subgroup G} {ι : ↥C →* P} (hι : Function.Injective ι)
    {H : Subgroup G} (c : ↥C) : ι c ∈ push ι H ↔ (c : G) ∈ H := by
  rw [mem_push]
  constructor
  · rintro ⟨c', hc', hcc'⟩
    rw [← hι hcc']
    exact hc'
  · exact fun h => ⟨c, h, rfl⟩

private theorem push_map_subtype {C : Subgroup G} (ι : ↥C →* P) (H : Subgroup ↥C) :
    push ι (H.map C.subtype) = H.map ι := by
  have h : (H.map C.subtype).subgroupOf C = H :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective C) H
  change ((H.map C.subtype).subgroupOf C).map ι = H.map ι
  rw [h]

private theorem push_zpowers' {C : Subgroup G} (ι : ↥C →* P) {g : G} (hg : g ∈ C) :
    push ι (zpowers g) = zpowers (ι ⟨g, hg⟩) := by
  have h1 : zpowers g = (zpowers (⟨g, hg⟩ : ↥C)).map C.subtype := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [h1, push_map_subtype, MonoidHom.map_zpowers]

private theorem push_closure_pair {C : Subgroup G} (ι : ↥C →* P) {a b : G} (ha : a ∈ C)
    (hb : b ∈ C) :
    push ι (closure ({a, b} : Set G)) = closure ({ι ⟨a, ha⟩, ι ⟨b, hb⟩} : Set P) := by
  have h1 : closure ({a, b} : Set G) =
      (closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥C)).map C.subtype := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [h1, push_map_subtype, MonoidHom.map_closure, Set.image_pair]

private theorem push_normalizer {C : Subgroup G} {ι : ↥C →* P} (hι : Function.Injective ι)
    {H : Subgroup G} (hH : H ≤ C) :
    push ι (normalizer (H : Set G)) = normalizer (push ι H : Set P) ⊓ ι.range := by
  ext p
  rw [Subgroup.mem_inf, mem_push]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨?_, ⟨c, rfl⟩⟩
    rw [Subgroup.mem_normalizer_iff] at hc ⊢
    intro q
    constructor
    · intro hq
      obtain ⟨a, ha, rfl⟩ := (mem_push ι).mp hq
      have h1 : (c : G) * a * (c : G)⁻¹ ∈ H := (hc a).mp ha
      have hmem : ι c * ι a * (ι c)⁻¹ = ι (c * a * c⁻¹) := by simp
      rw [hmem]
      exact (mem_push ι).mpr ⟨c * a * c⁻¹, by simpa using h1, rfl⟩
    · intro hq
      obtain ⟨a, ha, hae⟩ := (mem_push ι).mp hq
      have hq' : q = ι (c⁻¹ * a * c) := by
        have : ι (c⁻¹ * a * c) = (ι c)⁻¹ * (ι c * q * (ι c)⁻¹) * ι c := by
          rw [map_mul, map_mul, map_inv, hae]
        rw [this]
        group
      rw [hq']
      refine (mem_push ι).mpr ⟨c⁻¹ * a * c, ?_, rfl⟩
      have h3 : (c : G) * ((c : G)⁻¹ * a * c) * (c : G)⁻¹ = a := by group
      have := (hc ((c : G)⁻¹ * a * c)).mpr (by rw [h3]; exact ha)
      simpa using this
  · rintro ⟨hp, c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hp ⊢
    intro g
    constructor
    · intro hg
      have hgC : g ∈ C := hH hg
      have h1 : ι ⟨g, hgC⟩ ∈ push ι H := (mem_push ι).mpr ⟨⟨g, hgC⟩, hg, rfl⟩
      have h2 := (hp (ι ⟨g, hgC⟩)).mp h1
      obtain ⟨a, ha, hae⟩ := (mem_push ι).mp h2
      have h3 : a = c * ⟨g, hgC⟩ * c⁻¹ := hι (by rw [hae]; simp)
      have : (c : G) * g * (c : G)⁻¹ = (a : G) := by rw [h3]; rfl
      rw [this]
      exact ha
    · intro hg
      have hgC : (c : G) * g * (c : G)⁻¹ ∈ C := hH hg
      have hg'C : g ∈ C := by
        have := C.mul_mem (C.mul_mem (C.inv_mem c.2) hgC) c.2
        simpa [mul_assoc] using this
      have h1 : ι ⟨(c : G) * g * (c : G)⁻¹, hgC⟩ ∈ push ι H := (mem_push ι).mpr ⟨_, hg, rfl⟩
      have h2 : ι c * ι ⟨g, hg'C⟩ * (ι c)⁻¹ ∈ push ι H := by
        have : ι c * ι ⟨g, hg'C⟩ * (ι c)⁻¹ = ι ⟨(c : G) * g * (c : G)⁻¹, hgC⟩ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [this]
        exact h1
      have h3 := (hp (ι ⟨g, hg'C⟩)).mpr h2
      obtain ⟨a, ha, hae⟩ := (mem_push ι).mp h3
      have h4 : a = ⟨g, hg'C⟩ := hι hae
      rw [h4] at ha
      exact ha

private theorem emb_D_le_K (hE : IsEmb L t x K D t₀ x₀ ι) : D ≤ K := by
  rw [← hE.push_L, ← hE.range_eq]
  intro p hp
  obtain ⟨c, -, rfl⟩ := (mem_push ι).mp hp
  exact MonoidHom.mem_range.mpr ⟨c, rfl⟩

private theorem emb_push_Cx (hE : IsEmb L t x K D t₀ x₀ ι) :
    push ι (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) =
      K ⊓ centralizer ({x₀} : Set P) := by
  rw [push_inf hE.inj (centralizer ({x} : Set G)) (centralizer ({t} : Set G)),
    push_centralizer_singleton hE.inj hE.x_mem_C, push_self ι, hE.range_eq,
    hE.map_x ⟨x, hE.x_mem_C⟩ rfl]
  rw [inf_assoc, inf_idem, inf_comm]

private theorem emb_push_Y (hE : IsEmb L t x K D t₀ x₀ ι) :
    push ι (centralizer (jOf L x : Set G) ⊓
        (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) =
      centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)) := by
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) := hE.J_le.trans inf_le_right
  rw [push_inf hE.inj, push_centralizer hE.inj hJ_C, emb_push_Cx hE,
    hE.push_jOf (emb_D_le_K hE), hE.range_eq, inf_assoc, inf_left_idem]

private theorem emb_push_jOf (hE : IsEmb L t x K D t₀ x₀ ι) {x' : G} (hx' : x' ∈ L) :
    push ι (jOf L x') = jOf D (ι ⟨x', hE.L_le hx'⟩) := by
  have hx'C : x' ∈ centralizer ({t} : Set G) := hE.L_le hx'
  have hA : L ⊓ centralizer ({x'} : Set G) ≤ centralizer ({t} : Set G) :=
    le_trans inf_le_left hE.L_le
  have hpush : push ι (L ⊓ centralizer ({x'} : Set G)) =
      D ⊓ centralizer ({ι ⟨x', hx'C⟩} : Set P) := by
    rw [push_inf hE.inj L (centralizer ({x'} : Set G)), hE.push_L,
      push_centralizer_singleton hE.inj hx'C, hE.range_eq]
    rw [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left (emb_D_le_K hE))]
  change push ι ⁅L ⊓ centralizer ({x'} : Set G), L ⊓ centralizer ({x'} : Set G)⁆ =
    jOf D (ι ⟨x', hx'C⟩)
  rw [push_commutator ι (H := L ⊓ centralizer ({x'} : Set G))
    (H' := L ⊓ centralizer ({x'} : Set G)) hA hA, hpush]

private theorem emb_mem_Y (hE : IsEmb L t x K D t₀ x₀ ι) {a : G}
    (ha : a ∈ centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) :
    ι ⟨a, ha.2.2⟩ ∈ centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)) := by
  rw [← emb_push_Y hE]
  exact (mem_push_iff hE.inj ⟨a, ha.2.2⟩).2 ha

private theorem emb_Y_comm (hE : IsEmb L t x K D t₀ x₀ ι) (M : RbcModel K D t₀ x₀) :
    ∀ a ∈ centralizer (jOf L x : Set G) ⊓
        (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)),
      ∀ b ∈ centralizer (jOf L x : Set G) ⊓
        (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)), a * b = b * a := by
  intro a ha b hb
  have h := M.Y_comm _ (emb_mem_Y hE ha) _ (emb_mem_Y hE hb)
  rw [← map_mul, ← map_mul] at h
  simpa using congrArg Subtype.val (hE.inj h)

private theorem emb_Y_exp4 (hE : IsEmb L t x K D t₀ x₀ ι) (M : RbcModel K D t₀ x₀) :
    ∀ y ∈ centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)), y ^ 4 = 1 := by
  intro y hy
  have h := M.Y_exp4 _ (emb_mem_Y hE hy)
  rw [← map_pow] at h
  have h2 : (⟨y, hy.2.2⟩ : ↥(centralizer ({t} : Set G))) ^ 4 = 1 :=
    hE.inj (by rw [h, map_one])
  simpa using congrArg Subtype.val h2

private theorem emb_Y_inf_D (hE : IsEmb L t x K D t₀ x₀ ι) (M : RbcModel K D t₀ x₀) :
    centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) ⊓ L = zpowers x := by
  have hYL_C : centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) ⊓ L ≤
        centralizer ({t} : Set G) :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hz_C : zpowers x ≤ centralizer ({t} : Set G) := Subgroup.zpowers_le.mpr hE.x_mem_C
  apply push_injective_of_le hE.inj hYL_C hz_C
  rw [push_inf hE.inj, emb_push_Y hE, hE.push_L, push_zpowers' ι hE.x_mem_C,
    hE.map_x ⟨x, hE.x_mem_C⟩ rfl]
  exact M.Y_inf_D

private theorem emb_normalizer_J (hE : IsEmb L t x K D t₀ x₀ ι) (M : RbcModel K D t₀ x₀) :
    centralizer ({t} : Set G) ⊓ normalizer (jOf L x : Set G) =
      centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) := by
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) := hE.J_le.trans inf_le_right
  apply push_injective_of_le hE.inj inf_le_left inf_le_right
  rw [push_inf hE.inj, push_normalizer hE.inj hJ_C, hE.push_jOf (emb_D_le_K hE), push_self ι,
    emb_push_Cx hE, hE.range_eq, inf_comm (normalizer _) K, inf_left_idem]
  exact M.normalizer_J

private theorem emb_of_exp2 (hE : IsEmb L t x K D t₀ x₀ ι) (M : RbcModel K D t₀ x₀) :
    (∀ y ∈ centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)), y * y = 1) →
    centralizer ((centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :
        Set G) ⊓ (centralizer (jOf L x : Set G) ⊓
          (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) =
      closure ({t, x} : Set G) ∧
    ∃ o ∈ centralizer (jOf L x : Set G) ⊓
        (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)),
      ∃ n ∈ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G), n * o * n⁻¹ = o * x := by
  intro hexp
  have hx0 : ι ⟨x, hE.x_mem_C⟩ = x₀ := hE.map_x _ rfl
  have htC : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have ht0 : ι ⟨t, htC⟩ = t₀ := hE.map_t _ rfl
  have hCx_C : centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) := inf_le_right
  have hY_C : centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) ≤ centralizer ({t} : Set G) :=
    inf_le_right.trans hCx_C
  have hexpP : ∀ y ∈ centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)),
      y * y = 1 := by
    intro y hy
    rw [← emb_push_Y hE] at hy
    obtain ⟨c, hc, rfl⟩ := (mem_push ι).mp hy
    have h1 : (c : G) * (c : G) = 1 := hexp (c : G) hc
    have h2 : c * c = 1 := Subtype.ext (by simpa using h1)
    rw [← map_mul, h2, map_one]
  obtain ⟨hcent, o₀, ho₀, n₀, hn₀, hno⟩ := M.of_exp2 hexpP
  refine ⟨?_, ?_⟩
  · have hleft : centralizer ((centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) :
        Subgroup G) : Set G) ⊓ (centralizer (jOf L x : Set G) ⊓
          (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) ≤
        centralizer ({t} : Set G) := inf_le_right.trans hY_C
    have hcl : closure ({t, x} : Set G) ≤ centralizer ({t} : Set G) := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact htC
      · exact hE.x_mem_C
    apply push_injective_of_le hE.inj hleft hcl
    have hYK : centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)) ≤ K :=
      inf_le_right.trans inf_le_left
    rw [push_inf hE.inj, push_centralizer hE.inj hCx_C, emb_push_Cx hE, emb_push_Y hE,
      push_closure_pair ι htC hE.x_mem_C, ht0, hx0, hE.range_eq, inf_assoc,
      inf_eq_right.mpr hYK]
    exact hcent
  · rw [← emb_push_Y hE] at ho₀
    obtain ⟨o₁, ho₁, rfl⟩ := (mem_push ι).mp ho₀
    rw [← emb_push_Cx hE] at hn₀
    obtain ⟨n₁, hn₁, rfl⟩ := (mem_push ι).mp hn₀
    refine ⟨(o₁ : G), ho₁, (n₁ : G), hn₁, ?_⟩
    have h2 : n₁ * o₁ * n₁⁻¹ = o₁ * ⟨x, hE.x_mem_C⟩ := by
      apply hE.inj
      simp only [map_mul, map_inv, hx0]
      exact hno
    simpa using congrArg Subtype.val h2

private theorem emb_perfect_cent (hE : IsEmb L t x K D t₀ x₀ ι) (M : RbcModel K D t₀ x₀) :
    ∀ c ∈ centralizer ({t} : Set G), c ^ 2 ∈ zpowers t → c ∉ zpowers t →
      ∀ Q ≤ L ⊓ centralizer ({c} : Set G), ⁅Q, Q⁆ = Q → Q = ⊥ ∨
        ∃ x' ∈ L, orderOf x' = 2 ∧ Nat.card ↥(L ⊓ centralizer ({x'} : Set G)) = 240 ∧
          Q = jOf L x' ∧ L ⊓ centralizer (jOf L x' : Set G) = zpowers x' := by
  intro c hcC hc2 hcn Q hQ hperf
  have hDK : D ≤ K := emb_D_le_K hE
  have hQL : Q ≤ L := hQ.trans inf_le_left
  have hQC : Q ≤ centralizer ({t} : Set G) := hQL.trans hE.L_le
  have htC : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have ht0 : ι ⟨t, htC⟩ = t₀ := hE.map_t _ rfl
  have hc₀K : ι ⟨c, hcC⟩ ∈ K := by
    rw [← hE.range_eq]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hc₀2 : (ι ⟨c, hcC⟩) ^ 2 ∈ zpowers t₀ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc2
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : (⟨t, htC⟩ : ↥(centralizer ({t} : Set G))) ^ k = ⟨c, hcC⟩ ^ 2 :=
      Subtype.ext (by simpa using hk)
    rw [← ht0, ← map_zpow, h1, map_pow]
  have hc₀n : ι ⟨c, hcC⟩ ∉ zpowers t₀ := by
    intro h
    apply hcn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : (⟨t, htC⟩ : ↥(centralizer ({t} : Set G))) ^ k = ⟨c, hcC⟩ :=
      hE.inj (by rw [map_zpow, ht0, hk])
    simpa using congrArg Subtype.val h1
  have hQ₀ : push ι Q ≤ D ⊓ centralizer ({ι ⟨c, hcC⟩} : Set P) := by
    refine le_inf ?_ ?_
    · rw [← hE.push_L]
      exact push_mono ι hQL
    · have h1 : push ι Q ≤ push ι (centralizer ({c} : Set G)) :=
        push_mono ι (hQ.trans inf_le_right)
      rw [push_centralizer_singleton hE.inj hcC] at h1
      exact h1.trans inf_le_left
  have hperf₀ : ⁅push ι Q, push ι Q⁆ = push ι Q := by
    rw [← push_commutator ι hQC hQC, hperf]
  rcases M.perfect_cent _ hc₀K hc₀2 hc₀n (push ι Q) hQ₀ hperf₀ with
    hbot | ⟨x₁, hx₁D, hx₁ord, hx₁card, hQx₁, hcentx₁⟩
  · left
    exact push_injective_of_le hE.inj hQC bot_le (by rw [hbot, push_bot])
  · right
    rw [← hE.push_L] at hx₁D
    obtain ⟨y, hyL, hyx⟩ := (mem_push ι).mp hx₁D
    have hyC : (y : G) ∈ centralizer ({t} : Set G) := y.2
    have hyx' : ι ⟨(y : G), hyC⟩ = x₁ := hyx
    have hJ : push ι (jOf L (y : G)) = jOf D x₁ := by
      rw [emb_push_jOf hE hyL, hyx']
    have hJy_C : jOf L (y : G) ≤ centralizer ({t} : Set G) :=
      (Subgroup.commutator_le_self _).trans (inf_le_left.trans hE.L_le)
    refine ⟨(y : G), hyL, ?_, ?_, ?_, ?_⟩
    · have h1 : orderOf y = 2 := by
        rw [← orderOf_injective ι hE.inj y, hyx]
        exact hx₁ord
      rw [Subgroup.orderOf_coe]
      exact h1
    · have hle : L ⊓ centralizer ({(y : G)} : Set G) ≤ centralizer ({t} : Set G) :=
        inf_le_left.trans hE.L_le
      have hpush : push ι (L ⊓ centralizer ({(y : G)} : Set G)) =
          D ⊓ centralizer ({x₁} : Set P) := by
        rw [push_inf hE.inj, hE.push_L, push_centralizer_singleton hE.inj hyC, hE.range_eq,
          inf_comm (centralizer _) K, ← inf_assoc, inf_eq_left.mpr hDK, hyx']
      rw [← card_push hE.inj hle, hpush]
      exact hx₁card
    · apply push_injective_of_le hE.inj hQC
        ((Subgroup.commutator_le_self _).trans (inf_le_left.trans hE.L_le))
      rw [hJ]
      exact hQx₁
    · have hle : L ⊓ centralizer (jOf L (y : G) : Set G) ≤ centralizer ({t} : Set G) :=
        inf_le_left.trans hE.L_le
      have hz : zpowers (y : G) ≤ centralizer ({t} : Set G) := Subgroup.zpowers_le.mpr hyC
      apply push_injective_of_le hE.inj hle hz
      rw [push_inf hE.inj, hE.push_L, push_centralizer hE.inj hJy_C, hJ, hE.range_eq,
        inf_comm (centralizer _) K, ← inf_assoc, inf_eq_left.mpr hDK, hcentx₁,
        push_zpowers' ι hyC, hyx']

private theorem emb_normal_small (hE : IsEmb L t x K D t₀ x₀ ι) (M : RbcModel K D t₀ x₀) :
    ∀ N : Subgroup G, N ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) →
      (N.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))).Normal →
        jOf L x ≤ N → x ∉ N → Nat.card ↥N ≤ 120 := by
  intro N hNle hNnorm hJN hxN
  have hDK : D ≤ K := emb_D_le_K hE
  have hNC : N ≤ centralizer ({t} : Set G) := hNle.trans inf_le_right
  have hx0 : ι ⟨x, hE.x_mem_C⟩ = x₀ := hE.map_x _ rfl
  have hN₀le : push ι N ≤ K ⊓ centralizer ({x₀} : Set P) := by
    rw [← emb_push_Cx hE]
    exact push_mono ι hNle
  have hN₀norm : ((push ι N).subgroupOf (K ⊓ centralizer ({x₀} : Set P))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN₀le]
    intro h k hh hk
    rw [← emb_push_Cx hE] at hk
    obtain ⟨b, hb, rfl⟩ := (mem_push ι).mp hk
    obtain ⟨a, ha, rfl⟩ := (mem_push ι).mp hh
    have hconj : (b : G) * (a : G) * (b : G)⁻¹ ∈ N :=
      (Subgroup.normal_subgroupOf_iff hNle).mp hNnorm (a : G) (b : G) ha hb
    have e : ι (b * a * b⁻¹) = ι b * ι a * (ι b)⁻¹ := by simp only [map_mul, map_inv]
    rw [← e]
    exact (mem_push ι).mpr ⟨b * a * b⁻¹, by simpa using hconj, rfl⟩
  have hJN₀ : jOf D x₀ ≤ push ι N := by
    rw [← hE.push_jOf hDK]
    exact push_mono ι hJN
  have hxN₀ : x₀ ∉ push ι N := by
    intro h
    rw [← hx0] at h
    exact hxN ((mem_push_iff hE.inj ⟨x, hE.x_mem_C⟩).1 h)
  have h := M.normal_small (push ι N) hN₀le hN₀norm hJN₀ hxN₀
  rwa [card_push hE.inj hNC] at h

theorem IsEmb.rbcFacts (hE : IsEmb L t x K D t₀ x₀ ι) (M : RbcModel K D t₀ x₀) :
    RbcFacts L t x :=
  ⟨emb_Y_comm hE M, emb_Y_exp4 hE M, emb_Y_inf_D hE M, emb_normalizer_J hE M, emb_of_exp2 hE M,
    emb_perfect_cent hE M, emb_normal_small hE M⟩

end Transport

end CFSG.EvenSporadicStandard.M12Std.Rbc
