module

public import CFSG.GH74.GLS.Stage4.LocalCor97
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.StronglyEmbedded.UniqueCosetBasic
public import CFSG.GH74.GLS.SP.GlueBN

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

theorem eq_top_of_oneClass [Finite G]
    (hSE : ∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M)
    {G₁ : Subgroup G} {z : G} (hz2 : orderOf z = 2) (hzG₁ : z ∈ G₁)
    (hC : centralizer ({z} : Set G) ≤ G₁)
    (hcl : ∀ t ∈ G₁, orderOf t = 2 → ∃ a ∈ G₁, a * z * a⁻¹ = t) : G₁ = ⊤ := by
  by_contra hne
  refine hSE G₁ ?_
  refine CFSG.StronglyEmbedded.UniqueCoset.isStronglyEmbeddedOrder_of_involutions hne hzG₁ hz2 ?_
  intro t ht ht2 g hg
  obtain ⟨a, ha, hat⟩ := hcl t ht ht2
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [← ht2]
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
    simpa [MulAut.conj_apply, mul_assoc] using this
  obtain ⟨b, hb, hbs⟩ := hcl _ hg hs2
  have hcz : (a⁻¹ * g * b) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : a⁻¹ * g * b * z * (a⁻¹ * g * b)⁻¹ = z := by
      have e : b * z * b⁻¹ = g⁻¹ * t * g := hbs
      have e2 : a * z * a⁻¹ = t := hat
      calc a⁻¹ * g * b * z * (a⁻¹ * g * b)⁻¹ = a⁻¹ * g * (b * z * b⁻¹) * g⁻¹ * a := by group
        _ = a⁻¹ * g * (g⁻¹ * t * g) * g⁻¹ * a := by rw [e]
        _ = a⁻¹ * t * a := by group
        _ = z := by rw [← e2]; group
    have : a⁻¹ * g * b * z = z * (a⁻¹ * g * b) := by
      have := congrArg (fun x => x * (a⁻¹ * g * b)) h1
      simpa [mul_assoc] using this
    exact this
  have hmem : a⁻¹ * g * b ∈ G₁ := hC hcz
  have : g = a * (a⁻¹ * g * b) * b⁻¹ := by group
  rw [this]
  exact G₁.mul_mem (G₁.mul_mem ha hmem) (G₁.inv_mem hb)

theorem mem_of_sq_eq_one_of_odd {G₀ F : Subgroup G} (hF : F ≤ normalizer (G₀ : Set G))
    (hodd : ∀ f ∈ F, Odd (orderOf f)) {t : G} (ht : t ∈ G₀ ⊔ F) (ht2 : t * t = 1) : t ∈ G₀ := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left G₀ F hF] at ht
  obtain ⟨g, hg, f, hf, rfl⟩ := Set.mem_mul.1 ht
  have hfn : f ∈ normalizer (G₀ : Set G) := hF hf
  have htn : g * f ∈ normalizer (G₀ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer hg) hfn
  have hg' : (g * f) * g⁻¹ * (g * f)⁻¹ ∈ G₀ := by
    have := (mem_normalizer_iff.1 htn (g⁻¹)).1 (G₀.inv_mem hg)
    simpa [mul_assoc] using this
  have h4 : (g * f)⁻¹ = g * f := by
    rw [inv_eq_iff_mul_eq_one]; exact ht2
  rw [h4] at hg'
  have hf2 : f * f ∈ G₀ := by
    have e : f * f = g⁻¹ * ((g * f) * g⁻¹ * (g * f)) := by group
    rw [e]
    exact G₀.mul_mem (G₀.inv_mem hg) hg'
  obtain ⟨k, hk⟩ := hodd f hf
  have hfp : f ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one f
  have hfeq : f = (f * f) ^ (k + 1) := by
    calc f = f ^ (2 * k + 1) * f := by rw [hfp, one_mul]
      _ = f ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
      _ = (f * f) ^ (k + 1) := by rw [pow_mul, sq]
  have hfG : f ∈ G₀ := by rw [hfeq]; exact G₀.pow_mem hf2 _
  exact G₀.mul_mem hg hfG

theorem eq_top_of_gen [Finite G] [IsSimpleGroup G]
    (hSE : ∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M)
    {G₀ F : Subgroup G} {z : G} (hz2 : orderOf z = 2) (hzG₀ : z ∈ G₀)
    (hF : F ≤ normalizer (G₀ : Set G)) (hodd : ∀ f ∈ F, Odd (orderOf f))
    (hC : centralizer ({z} : Set G) ≤ G₀ ⊔ F)
    (hone : ∀ t ∈ G₀, orderOf t = 2 → ∃ a ∈ G₀, a * z * a⁻¹ = t) : G₀ = ⊤ := by
  have hG₁ : G₀ ⊔ F = ⊤ := by
    refine eq_top_of_oneClass hSE hz2 (Subgroup.mem_sup_left hzG₀) hC (fun t ht ht2 => ?_)
    have htsq : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2, sq] at this
    have htG₀ : t ∈ G₀ := mem_of_sq_eq_one_of_odd hF hodd ht htsq
    obtain ⟨a, ha, hat⟩ := hone t htG₀ ht2
    exact ⟨a, Subgroup.mem_sup_left ha, hat⟩
  have hnorm : G₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ G₀ ⊔ F := by rw [hG₁]; trivial
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left G₀ F hF] at hg
    obtain ⟨g₁, hg₁, f, hf, rfl⟩ := Set.mem_mul.1 hg
    have h1 : f * n * f⁻¹ ∈ G₀ := by
      have := (mem_normalizer_iff.1 (hF hf) n).1 hn
      exact this
    have := G₀.mul_mem (G₀.mul_mem hg₁ h1) (G₀.inv_mem hg₁)
    have e : g₁ * (f * n * f⁻¹) * g₁⁻¹ = g₁ * f * n * (g₁ * f)⁻¹ := by group
    rwa [e] at this
  rcases hnorm.eq_bot_or_eq_top with h | h
  · rw [h] at hzG₀
    have : z = 1 := hzG₀
    rw [this, orderOf_one] at hz2
    omega
  · exact h

theorem oneClass_of_transfer {Q : Type*} [Group Q] [Finite Q] {S S₀ : Subgroup Q} {z : Q}
    (hS : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.index) (hS₀S : S₀ ≤ S) (hS₀idx : S₀.relIndex S = 2)
    (hno : ∀ N : Subgroup Q, N.Normal → N.index ≠ 2)
    (hcl : ∀ t ∈ S₀, orderOf t = 2 → ∃ g : Q, g * z * g⁻¹ = t) :
    ∀ t : Q, orderOf t = 2 → ∃ g : Q, g * z * g⁻¹ = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht2
  let S' : Sylow 2 Q := hS.toSylow hSidx
  have hS'S : (S' : Subgroup Q) = S := rfl
  have hzt : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht2]; norm_num
  obtain ⟨P', hP'⟩ := hzt.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q S' P'
  have htS : g⁻¹ * t * g ∈ S := by
    have h1 : t ∈ ((g • S' : Sylow 2 Q) : Subgroup Q) := by
      rw [hg]; exact hP' (mem_zpowers t)
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨s, hs, rfl⟩ := h1
    have : g⁻¹ * (MulAut.conj g • s) * g = s := by
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hs
  set t' := g⁻¹ * t * g with ht'
  have ht'2 : orderOf t' = 2 := by
    rw [← ht2]
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
    simpa [MulAut.conj_apply, mul_assoc, ht'] using this
  have hgoal : ∀ h : Q, h * z * h⁻¹ = t' → ∃ g' : Q, g' * z * g'⁻¹ = t := by
    intro h hh
    refine ⟨g * h, ?_⟩
    have : g * h * z * (g * h)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ := by group
    rw [this, hh, ht']
    group
  by_cases hmem : ∃ x : Q, x⁻¹ * t' * x ∈ S₀
  · obtain ⟨x, hx⟩ := hmem
    have hx2 : orderOf (x⁻¹ * t' * x) = 2 := by
      rw [← ht'2]
      have := orderOf_injective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective t'
      simpa [MulAut.conj_apply, mul_assoc] using this
    obtain ⟨h, hh⟩ := hcl _ hx hx2
    refine hgoal (x * h) ?_
    have : x * h * z * (x * h)⁻¹ = x * (h * z * h⁻¹) * x⁻¹ := by group
    rw [this, hh]
    group
  · have hmem' : ∀ x : Q, x⁻¹ * t' * x ∉ S₀ := fun x hx => hmem ⟨x, hx⟩
    by_cases hS₀t : t' ∈ S₀
    · obtain ⟨h, hh⟩ := hcl _ hS₀t ht'2
      exact hgoal h hh
    · exfalso
      obtain ⟨N, hN, hNidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hS hSidx hS₀S hS₀idx htS hS₀t
        (fun y hy hyS₀ => by
          rw [ht'2]
          have h1 : orderOf y ≠ 1 := fun h1 => hyS₀ (by
            rw [orderOf_eq_one_iff.1 h1]; exact S₀.one_mem)
          have h2 : 0 < orderOf y := orderOf_pos y
          omega)
        (fun g' => hmem' g')
      exact hno N hN hNidx

theorem orderOf_conj_eq (t x : G) : orderOf (x⁻¹ * t * x) = orderOf t := by
  have := orderOf_injective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective t
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem mem_of_odd_orderOf {N : Subgroup G} (hN : N.index = 2) {x : G} (hx : Odd (orderOf x)) :
    x ∈ N := by
  obtain ⟨k, hk⟩ := hx
  have hxp : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hsq : x * x ∈ N := Subgroup.mul_self_mem_of_index_two hN x
  have heq : x = (x * x) ^ (k + 1) := by
    calc x = x ^ (2 * k + 1) * x := by rw [hxp, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
      _ = (x * x) ^ (k + 1) := by rw [pow_mul, sq]
  rw [heq]
  exact N.pow_mem hsq _

theorem no_index_two {Q : Type*} [Group Q] [Finite Q] {S : Subgroup Q} (hSidx : ¬ 2 ∣ S.index)
    (hS : S ≤ Subgroup.closure {x : Q | Odd (orderOf x)}) :
    ∀ N : Subgroup Q, N.Normal → N.index ≠ 2 := by
  intro N hN hN2
  have h1 : Subgroup.closure {x : Q | Odd (orderOf x)} ≤ N :=
    (Subgroup.closure_le N).2 (fun x hx => mem_of_odd_orderOf hN2 hx)
  have hSN : S ≤ N := hS.trans h1
  have hdvd : N.index ∣ S.index := Subgroup.index_dvd_of_le hSN
  rw [hN2] at hdvd
  exact hSidx hdvd

theorem closure_odd_subtype {G₀ S : Subgroup G}
    (hodd : S ≤ Subgroup.closure {x : G | x ∈ G₀ ∧ Odd (orderOf x)}) :
    S.subgroupOf G₀ ≤ Subgroup.closure {x : G₀ | Odd (orderOf x)} := by
  have h1 : Subgroup.closure {x : G | x ∈ G₀ ∧ Odd (orderOf x)} ≤
      (Subgroup.closure {x : G₀ | Odd (orderOf x)}).map G₀.subtype := by
    refine (Subgroup.closure_le _).2 (fun x hx => ?_)
    exact ⟨⟨x, hx.1⟩, Subgroup.subset_closure (by simpa [Subgroup.orderOf_mk] using hx.2), rfl⟩
  intro y hy
  obtain ⟨w, hw, hwy⟩ := h1 (hodd hy)
  have : w = y := Subtype.ext hwy
  rw [← this]; exact hw

theorem oneClass_in [Finite G] {G₀ S S₀ : Subgroup G} {z : G}
    (hSG₀ : S ≤ G₀) (hS : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.index)
    (hS₀S : S₀ ≤ S) (hS₀idx : S₀.relIndex S = 2)
    (hodd : S ≤ Subgroup.closure {x : G | x ∈ G₀ ∧ Odd (orderOf x)})
    (hcl : ∀ t ∈ S₀, orderOf t = 2 → ∃ g ∈ G₀, g * z * g⁻¹ = t) (hzG₀ : z ∈ G₀) :
    ∀ t ∈ G₀, orderOf t = 2 → ∃ a ∈ G₀, a * z * a⁻¹ = t := by
  have hSQ : IsPGroup 2 (S.subgroupOf G₀) :=
    hS.comap_of_injective G₀.subtype G₀.subtype_injective
  have hSidxQ : ¬ 2 ∣ (S.subgroupOf G₀).index := by
    intro h
    apply hSidx
    have hd : S.relIndex G₀ ∣ S.index := Subgroup.relIndex_dvd_index_of_le hSG₀
    exact h.trans hd
  have hS₀S' : S₀.subgroupOf G₀ ≤ S.subgroupOf G₀ := by
    intro y hy
    exact hS₀S hy
  have hS₀idxQ : (S₀.subgroupOf G₀).relIndex (S.subgroupOf G₀) = 2 := by
    rw [Subgroup.relIndex_subgroupOf hSG₀]
    exact hS₀idx
  have hno := no_index_two hSidxQ (closure_odd_subtype hodd)
  have key := oneClass_of_transfer (z := (⟨z, hzG₀⟩ : G₀)) hSQ hSidxQ hS₀S' hS₀idxQ hno
    (fun t ht ht2 => by
      have ht' : (t : G) ∈ S₀ := ht
      have ht2' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht2
      obtain ⟨g, hg, hgt⟩ := hcl (t : G) ht' ht2'
      exact ⟨⟨g, hg⟩, Subtype.ext hgt⟩)
  intro t ht ht2
  have ht2' : orderOf (⟨t, ht⟩ : G₀) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  obtain ⟨g, hg⟩ := key _ ht2'
  exact ⟨g, g.2, congrArg Subtype.val hg⟩


end Generic

variable {G : Type} [Group G]

structure Gen97 (p : ℕ) (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G)
    (z : G) (S K₁ K₂ F P₀ : Subgroup G) : Prop where
  z_ord : orderOf z = 2
  K₁_eq : K₁ = root 1 ⊔ root (-1)
  K₂_eq : K₂ = root 4 ⊔ root (-4)
  S_pGroup : IsPGroup 2 S
  S_sylow : ¬ 2 ∣ S.index
  z_mem : z ∈ S ⊓ (K₁ ⊔ K₂)
  S_idx : (S ⊓ (K₁ ⊔ K₂)).relIndex S = 2
  z_class : ∀ t ∈ S ⊓ (K₁ ⊔ K₂), orderOf t = 2 →
    ∃ g ∈ (H ⊔ U) ⊔ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}), g * z * g⁻¹ = t
  S_le : S ≤ ⨆ n ∈ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}), conjBy n (K₁ ⊔ K₂)
  F_odd : ∀ f ∈ F, Odd (orderOf f)
  F_normB : F ≤ normalizer ((H ⊔ U : Subgroup G) : Set G)
  F_normN : F ≤ normalizer ((Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) : Subgroup G) : Set G)
  C_le : centralizer ({z} : Set G) ≤ K₁ ⊔ K₂ ⊔ S ⊔ F
  P₀_le : P₀ ≤ F
  P₀_pGroup : IsPGroup p P₀
  P₀_normU : P₀ ≤ normalizer (U : Set G)
  Sylow_UP₀ : ∃ T : Sylow p G, (T : Subgroup G) = U ⊔ P₀

theorem normalizer_sup_of_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (A : Set G) → g ∈ normalizer (B : Set G) →
      ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ A ⊔ B := by
    intro g hA hB x hx
    have : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left (by simpa [MulAut.conj_apply] using (mem_normalizer_iff.1 hA a).1 ha)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right (by simpa [MulAut.conj_apply] using (mem_normalizer_iff.1 hB b).1 hb)
    have h2 := this hx
    rw [Subgroup.mem_comap] at h2
    simpa [MulAut.conj_apply] using h2
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hA hB x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hx
  simpa [mul_assoc] using this

namespace Gen97

variable {p : ℕ} {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G} {root : ℤ → Subgroup G}
  {z : G} {S K₁ K₂ F P₀ : Subgroup G}

theorem root_le_G₀ (D : Cor97 p H r₁ r₂ U root) {i : ℤ} (hi : IsRoot 6 i) :
    root i ≤ (H ⊔ U) ⊔ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) := by
  have hr₁ : r₁ ∈ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) :=
    Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hr₂ : r₂ ∈ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) :=
    Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hw₀ : (r₁ * r₂) ^ 3 ∈ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ hr₁ hr₂) 3
  have hi0 := hi.1
  have hi6 : i.natAbs ≤ 6 := hi.2
  rcases lt_or_gt_of_ne hi0 with hneg | hpos
  ·
    intro x hx
    have hx' : x ∈ negGen 6 root := by
      have := mem_negGen_of_mem (n := 6) (root := root) (k := -i) (by omega) (by omega)
        (y := x) (by simpa using hx)
      exact this
    have hc := D.negGen_le_conj hx'
    rw [mem_conjBy_iff] at hc
    have h1 : x = ((r₁ * r₂) ^ 3)⁻¹ * ((r₁ * r₂) ^ 3 * x * ((r₁ * r₂) ^ 3)⁻¹) * (r₁ * r₂) ^ 3 := by
      group
    rw [h1]
    have hU : (r₁ * r₂) ^ 3 * x * ((r₁ * r₂) ^ 3)⁻¹ ∈ (H ⊔ U) ⊔ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right hc)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hw₀)) hU)
      (Subgroup.mem_sup_right hw₀)
  · intro x hx
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (D.root_le_U (by omega) (by omega) hx))


theorem top [Finite G] [IsSimpleGroup G] (D : Cor97 p H r₁ r₂ U root)
    (E : Gen97 p H r₁ r₂ U root z S K₁ K₂ F P₀)
    (hSE : ∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) :
    (H ⊔ U) ⊔ Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) = ⊤ := by
  have : Fact p.Prime := ⟨D.prime⟩
  set N := Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) with hN
  set G₀ := (H ⊔ U) ⊔ N with hG₀
  have hNG₀ : N ≤ G₀ := le_sup_right
  have hroot : ∀ i, IsRoot 6 i → root i ≤ G₀ := fun i hi => root_le_G₀ D hi
  have hK₁ : K₁ ≤ G₀ := by
    rw [E.K₁_eq]
    exact sup_le (hroot 1 ⟨by norm_num, by norm_num⟩) (hroot (-1) ⟨by norm_num, by norm_num⟩)
  have hK₂ : K₂ ≤ G₀ := by
    rw [E.K₂_eq]
    exact sup_le (hroot 4 ⟨by norm_num, by norm_num⟩) (hroot (-4) ⟨by norm_num, by norm_num⟩)
  have hK : K₁ ⊔ K₂ ≤ G₀ := sup_le hK₁ hK₂
  set Hodd : Subgroup G := Subgroup.closure {x : G | x ∈ G₀ ∧ Odd (orderOf x)} with hHodd
  have hHoddG₀ : Hodd ≤ G₀ := (Subgroup.closure_le G₀).2 (fun x hx => hx.1)
  have hroot_odd : ∀ i, IsRoot 6 i → root i ≤ Hodd := by
    intro i hi x hx
    refine Subgroup.subset_closure ⟨hroot i hi hx, ?_⟩
    rcases (Nat.dvd_prime D.prime).1 (orderOf_dvd_of_pow_eq_one (D.root_exp i hi x hx)) with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact D.prime.odd_of_ne_two D.p_ne_two
  have hK_odd : K₁ ⊔ K₂ ≤ Hodd := by
    rw [E.K₁_eq, E.K₂_eq]
    exact sup_le (sup_le (hroot_odd 1 ⟨by norm_num, by norm_num⟩) (hroot_odd (-1) ⟨by norm_num, by norm_num⟩))
      (sup_le (hroot_odd 4 ⟨by norm_num, by norm_num⟩) (hroot_odd (-4) ⟨by norm_num, by norm_num⟩))
  have hHodd_conj : ∀ n ∈ G₀, ∀ x ∈ Hodd, n * x * n⁻¹ ∈ Hodd := by
    intro n hn x hx
    have : Hodd ≤ Hodd.comap (MulAut.conj n).toMonoidHom := by
      refine (Subgroup.closure_le _).2 (fun y hy => ?_)
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · simpa [MulAut.conj_apply] using G₀.mul_mem (G₀.mul_mem hn hy.1) (G₀.inv_mem hn)
      · have h1 : orderOf (n * y * n⁻¹) = orderOf y := by
          have := orderOf_conj_eq y n⁻¹
          simpa using this
        show Odd (orderOf (n * y * n⁻¹))
        rw [h1]
        exact hy.2
    have h2 := this hx
    rw [Subgroup.mem_comap] at h2
    simpa [MulAut.conj_apply] using h2
  have hS_odd : S ≤ Hodd := by
    refine E.S_le.trans (iSup₂_le fun n hn x hx => ?_)
    have hx' : n * x * n⁻¹ ∈ Hodd := hK_odd (by simpa [mem_conjBy_iff] using hx)
    have := hHodd_conj n⁻¹ (G₀.inv_mem (hNG₀ hn)) _ hx'
    simpa [mul_assoc] using this
  have hSG₀ : S ≤ G₀ := hS_odd.trans hHoddG₀
  have hzG₀ : z ∈ G₀ := hSG₀ E.z_mem.1
  have hcl : ∀ t ∈ S ⊓ (K₁ ⊔ K₂), orderOf t = 2 → ∃ g ∈ G₀, g * z * g⁻¹ = t := E.z_class
  have hone := oneClass_in hSG₀ E.S_pGroup E.S_sylow inf_le_left E.S_idx hS_odd hcl hzG₀
  have hFnorm : F ≤ normalizer (G₀ : Set G) := fun f hf =>
    normalizer_sup_of_normalizer (E.F_normB hf) (E.F_normN hf)
  have hC : centralizer ({z} : Set G) ≤ G₀ ⊔ F :=
    E.C_le.trans (sup_le (sup_le (sup_le (hK₁.trans le_sup_left) (hK₂.trans le_sup_left))
      (hSG₀.trans le_sup_left)) le_sup_right)
  exact eq_top_of_gen hSE E.z_ord hzG₀ hFnorm E.F_odd hC hone

theorem U_sylow [Finite G] [IsSimpleGroup G] (D : Cor97 p H r₁ r₂ U root)
    (E : Gen97 p H r₁ r₂ U root z S K₁ K₂ F P₀)
    (hSE : ∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) :
    ∃ T : Sylow p G, (T : Subgroup G) = U := by
  have : Fact p.Prime := ⟨D.prime⟩
  have hgen := top D E hSE
  have R := D.toRGD2
  have := R.cartan_normal
  have hT := R.isTitsSystem hgen
  have hnorm := hT.normalizer_parabolic (J := ∅) (Finset.empty_subset _)
  rw [Finset.coe_empty, parabolic_empty] at hnorm
  have hP₀B : P₀ ≤ H ⊔ U := by
    intro x hx
    have h1 := E.F_normB (E.P₀_le hx)
    rw [hnorm] at h1
    exact h1
  have hP₀U : P₀ ≤ U := by
    intro x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 E.P₀_pGroup ⟨x, hx⟩
    have hxk : x ^ (p ^ k) = 1 := by
      have h2 : orderOf x = p ^ k := by simpa using hk
      rw [← h2]
      exact pow_orderOf_eq_one x
    exact D.mem_U_of_pow_eq_one (hP₀B hx) hxk
  obtain ⟨T, hT'⟩ := E.Sylow_UP₀
  exact ⟨T, by rw [hT']; exact sup_eq_left.2 hP₀U⟩

end Gen97

end CFSG.GH74.GLS.Stage4
