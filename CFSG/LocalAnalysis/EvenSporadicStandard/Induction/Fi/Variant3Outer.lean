module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem false_of_commute_quasisimple {X : Type} [Group X] (hX : CFSG.IsQuasisimple X)
    (h : ∀ a b : X, a * b = b * a) : False := by
  obtain ⟨a, b, hab⟩ := hX.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h a' b'])

variable {H : Type} [Group H] [Finite H] {K₁ L₁ T : Subgroup H} {s : H}

omit [Finite H] in
theorem false_of_commute_le {K L : Subgroup H} (hKq : CFSG.IsQuasisimple ↥K) (hKL : K ≤ L)
    (h : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a) : False :=
  false_of_commute_quasisimple hKq fun a b => Subtype.ext (h a a.2 b (hKL b.2))

theorem false_of_link_centralized (hdata : Sol78Link5bData K₁ L₁ T s)
    (hKq : CFSG.IsQuasisimple ↥K₁) (hKL : K₁ ≤ L₁) (hne : K₁ ≠ L₁)
    (hs : ∀ l ∈ L₁, l * s = s * l) : False := by
  have hLle : L₁ ≤ centralizer ((T ⊔ zpowers s : Subgroup H) : Set H) := by
    intro l hl
    have hle : T ⊔ zpowers s ≤ centralizer ({l} : Set H) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 (hdata.L_comp.1 hl) x hx
      · rw [Subgroup.zpowers_le]
        exact mem_centralizer_singleton_iff.2 (hs l hl).symm
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.1 (hle hy)
  have hLcomp : IsCompIn L₁ (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H)) :=
    isCompIn_of_le hdata.L_comp hLle (Subgroup.centralizer_le fun x hx => Subgroup.mem_sup_left hx)
  exact false_of_commute_le hKq hKL (hdata.K_comp.commute_of_ne hLcomp hne)

theorem link5b_outer (hdata : Sol78Link5bData K₁ L₁ T s) (hKq : CFSG.IsQuasisimple ↥K₁)
    (hKL : K₁ ≤ L₁) (hne : K₁ ≠ L₁)
    (hcent : ∀ x ∈ L₁, (∀ k ∈ K₁, k * x = x * k) → ∀ l ∈ L₁, l * x = x * l) :
    s ∈ normalizer (L₁ : Set H) ∧ s ∉ L₁ ⊔ centralizer (L₁ : Set H) ∧
      ∀ k ∈ K₁, k * s = s * k := by
  have hsN : s ∈ normalizer (L₁ : Set H) :=
    Solomon78.mem_normalizer_iff_map_conj_eq.2 hdata.link.1.symm
  have hKs : ∀ k ∈ K₁, k * s = s * k := fun k hk =>
    (mem_centralizer_iff.1 (hdata.K_comp.1 hk) s
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))).symm
  have hnot : s ∉ L₁ ⊔ centralizer (L₁ : Set H) := by
    intro hs
    obtain ⟨c, hc, l, hl, hcl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (A := centralizer (L₁ : Set H)) (B := L₁)
      (fun x hx => mem_centralizer_iff.2 fun y hy => (mem_centralizer_iff.1 hy x hx).symm)
      (sup_comm L₁ (centralizer (L₁ : Set H)) ▸ hs)
    have hcl' : ∀ x ∈ L₁, c * x = x * c := fun x hx => (mem_centralizer_iff.1 hc x hx).symm
    have hlK : ∀ k ∈ K₁, k * l = l * k := by
      intro k hk
      have h1 := hKs k hk
      have h2 : c * (k * l) = c * (l * k) := by
        calc c * (k * l) = (c * k) * l := by rw [mul_assoc]
          _ = (k * c) * l := by rw [hcl' k (hKL hk)]
          _ = k * (c * l) := by rw [mul_assoc]
          _ = k * s := by rw [hcl]
          _ = s * k := h1
          _ = (c * l) * k := by rw [hcl]
          _ = c * (l * k) := by rw [mul_assoc]
      exact mul_left_cancel h2
    have hlz := hcent l hl hlK
    refine false_of_link_centralized hdata hKq hKL hne fun x hx => ?_
    calc x * s = x * (c * l) := by rw [hcl]
      _ = (x * c) * l := by rw [mul_assoc]
      _ = (c * x) * l := by rw [← hcl' x hx]
      _ = c * (x * l) := by rw [mul_assoc]
      _ = c * (l * x) := by rw [hlz x hx]
      _ = (c * l) * x := by rw [mul_assoc]
      _ = s * x := by rw [hcl]
  exact ⟨hsN, hnot, hKs⟩

theorem exists_involution_central_in_T (hT2 : IsPGroup 2 ↥T) (hT1 : T ≠ ⊥)
    (hsN : s ∈ normalizer (T : Set H)) (hs2 : s ^ 2 ∈ T) :
    ∃ t ∈ T, orderOf t = 2 ∧ ∀ y ∈ T ⊔ zpowers s, y * t = t * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(T ⊔ zpowers s) := isPGroup_sup_zpowers hT2 hsN hs2
  set P : Subgroup H := T ⊔ zpowers s with hPdef
  have hTP : T ≤ P := le_sup_left
  have hTn : (T.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTP]
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.zpowers_le]
    exact hsN
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hne : T.subgroupOf P ≠ ⊥ := by
    intro h
    apply hT1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hTP hx⟩ : ↥P) ∈ T.subgroupOf P := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hA : T.subgroupOf P ⊓ center ↥P ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hA2 : IsPGroup 2 ↥(T.subgroupOf P ⊓ center ↥P) := hP.to_subgroup _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(T.subgroupOf P ⊓ center ↥P)) 2
    (two_dvd_card_of_isPGroup hA2 hA)
  have hxP : (x : ↥P) ∈ T.subgroupOf P := x.2.1
  have hxc : (x : ↥P) ∈ center ↥P := x.2.2
  refine ⟨((x : ↥P) : H), Subgroup.mem_subgroupOf.1 hxP, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx
  · intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hxc ⟨y, hy⟩)

theorem exists_outer_pair (hdata : Sol78Link5bData K₁ L₁ T s) (hT1 : T ≠ ⊥)
    (hsN : s ∈ normalizer (L₁ : Set H)) (hnot : s ∉ L₁ ⊔ centralizer (L₁ : Set H))
    (hKs : ∀ k ∈ K₁, k * s = s * k)
    (hinv : s ^ 2 ≠ 1 → ∃ u t : H, orderOf u = 2 ∧ orderOf t = 2 ∧
      t ∈ centralizer (L₁ : Set H) ∧ u * t = t * u ∧ u ∈ normalizer (L₁ : Set H) ∧
      u ∉ L₁ ⊔ centralizer (L₁ : Set H) ∧ ∀ k ∈ K₁, k * u = u * k) :
    ∃ u t : H, orderOf u = 2 ∧ orderOf t = 2 ∧ t ∈ centralizer (L₁ : Set H) ∧ u * t = t * u ∧
      u ∈ normalizer (L₁ : Set H) ∧ u ∉ L₁ ⊔ centralizer (L₁ : Set H) ∧
      ∀ k ∈ K₁, k * u = u * k := by
  by_cases hs2 : s ^ 2 = 1
  · have hs1 : s ≠ 1 := by
      rintro rfl
      exact hnot (Subgroup.one_mem _)
    obtain ⟨t, htT, ht2, htc⟩ :=
      exists_involution_central_in_T hdata.T_two hT1 hdata.s_norm hdata.s_sq
    refine ⟨s, t, orderOf_eq_prime hs2 hs1, ht2, ?_, ?_, hsN, hnot, hKs⟩
    · exact mem_centralizer_iff.2 fun l hl => (mem_centralizer_iff.1 (hdata.L_comp.1 hl) t htT).symm
    · exact htc _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact hinv hs2

end CFSG.EvenSporadicStandard.Induction.Fi.V3
