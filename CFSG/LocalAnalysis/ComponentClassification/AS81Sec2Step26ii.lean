module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step26iiAut
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Mod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools Sec2V4 Equiv
open scoped commutatorElement

namespace Sec2

section Index

variable {G : Type} [Group G]

theorem mk_eq_mk_of_mul_mem {K L : Subgroup G} {x c : ↥L} (hx : (x : G) * x ∈ K)
    (h : (x : G) * c ∈ K) : (x : ↥L ⧸ K.subgroupOf L) = c := by
  rw [QuotientGroup.eq, mem_subgroupOf]
  have e : ((x⁻¹ * c : ↥L) : G) = ((x : G) * x)⁻¹ * ((x : G) * c) := by
    simp only [coe_mul, coe_inv]
    group
  rw [e]
  exact K.mul_mem (K.inv_mem hx) h

theorem relIndex_le_two [Finite G] {K L : Subgroup G} (hsq : ∀ a ∈ L, a * a ∈ K)
    (h : ∀ a ∈ L, ∀ b ∈ L, a ∈ K ∨ b ∈ K ∨ a * b ∈ K) : K.relIndex L ≤ 2 := by
  by_cases h0 : ∃ a ∈ L, a ∉ K
  · obtain ⟨a, haL, haK⟩ := h0
    let f : Fin 2 → ↥L ⧸ K.subgroupOf L :=
      ![((1 : ↥L) : ↥L ⧸ K.subgroupOf L), ((⟨a, haL⟩ : ↥L) : ↥L ⧸ K.subgroupOf L)]
    have hf : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H c =>
        rcases h a haL c c.2 with h1 | h1 | h1
        · exact absurd h1 haK
        · refine ⟨0, ?_⟩
          show ((1 : ↥L) : ↥L ⧸ K.subgroupOf L) = c
          rw [QuotientGroup.eq, mem_subgroupOf]
          simpa using h1
        · exact ⟨1, mk_eq_mk_of_mul_mem (hsq a haL) h1⟩
    calc K.relIndex L = Nat.card (↥L ⧸ K.subgroupOf L) := rfl
      _ ≤ Nat.card (Fin 2) := Nat.card_le_card_of_surjective f hf
      _ = 2 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 2)
  · push Not at h0
    rw [relIndex_eq_one.mpr h0]
    norm_num

theorem relIndex_le_four [Finite G] {K L : Subgroup G} (hsq : ∀ a ∈ L, a * a ∈ K)
    (h : ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, a ∈ K ∨ b ∈ K ∨ a * b ∈ K ∨ c ∈ K ∨ a * c ∈ K ∨
      b * c ∈ K ∨ a * b * c ∈ K) : K.relIndex L ≤ 4 := by
  by_cases h0 : ∃ a ∈ L, ∃ b ∈ L, a ∉ K ∧ b ∉ K ∧ a * b ∉ K
  · obtain ⟨a, ha, b, hb, haK, hbK, habK⟩ := h0
    let f : Fin 4 → ↥L ⧸ K.subgroupOf L := ![((1 : ↥L) : ↥L ⧸ K.subgroupOf L),
      ((⟨a, ha⟩ : ↥L) : ↥L ⧸ K.subgroupOf L),
      ((⟨b, hb⟩ : ↥L) : ↥L ⧸ K.subgroupOf L),
      ((⟨a * b, L.mul_mem ha hb⟩ : ↥L) : ↥L ⧸ K.subgroupOf L)]
    have hf : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H c =>
        rcases h a ha b hb c c.2 with h1 | h1 | h1 | h1 | h1 | h1 | h1
        · exact absurd h1 haK
        · exact absurd h1 hbK
        · exact absurd h1 habK
        · refine ⟨0, ?_⟩
          show ((1 : ↥L) : ↥L ⧸ K.subgroupOf L) = c
          rw [QuotientGroup.eq, mem_subgroupOf]
          simpa using h1
        · exact ⟨1, mk_eq_mk_of_mul_mem (hsq a ha) h1⟩
        · exact ⟨2, mk_eq_mk_of_mul_mem (hsq b hb) h1⟩
        · exact ⟨3, mk_eq_mk_of_mul_mem (x := ⟨a * b, L.mul_mem ha hb⟩)
            (hsq _ (L.mul_mem ha hb)) h1⟩
    calc K.relIndex L = Nat.card (↥L ⧸ K.subgroupOf L) := rfl
      _ ≤ Nat.card (Fin 4) := Nat.card_le_card_of_surjective f hf
      _ = 4 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 4)
  · push Not at h0
    refine (relIndex_le_two hsq fun a ha b hb => ?_).trans (by norm_num)
    by_cases haK : a ∈ K
    · exact Or.inl haK
    by_cases hbK : b ∈ K
    · exact Or.inr (Or.inl hbK)
    exact Or.inr (Or.inr (h0 a ha b hb haK hbK))

end Index

theorem cond_add_cond_injective {u₁ u₂ : Fin 5 → ZMod 2} (h1 : u₁ ≠ 0) (h2 : u₂ ≠ 0)
    (h12 : u₁ ≠ u₂) :
    Function.Injective fun pq : Bool × Bool => cond pq.1 u₁ 0 + cond pq.2 u₂ 0 := by
  have hs : u₁ + u₂ ≠ 0 := fun h => h12 (by
    rw [← add_zero u₁, ← vec_add_self u₂, ← add_assoc, h, zero_add])
  have hs1 : u₁ + u₂ ≠ u₁ := fun h => h2 (by simpa using h)
  have hs2 : u₁ + u₂ ≠ u₂ := fun h => h1 (by simpa using h)
  rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ h <;>
    simp only [Bool.cond_false, Bool.cond_true, add_zero, zero_add] at h <;>
    first
    | rfl
    | exact absurd h h1
    | exact absurd h.symm h1
    | exact absurd h h2
    | exact absurd h.symm h2
    | exact absurd h h12
    | exact absurd h.symm h12
    | exact absurd h hs
    | exact absurd h.symm hs
    | exact absurd h hs1
    | exact absurd h.symm hs1
    | exact absurd h hs2
    | exact absurd h.symm hs2

theorem matAct_invol₀ (m : Pair) : matAct (invol 0) m = (m.2, m.1) := by
  simp [matAct, invol]

theorem matAct_invol₁ (m : Pair) : matAct (invol 1) m = (m.1 + m.2, m.2) := by
  simp [matAct, invol]

theorem matAct_invol₂ (m : Pair) : matAct (invol 2) m = (m.1, m.1 + m.2) := by
  simp [matAct, invol]

theorem sixteen_le_card_of_invol {N : AddSubgroup Pair} {π : Perm (Fin 5)} {i : Fin 3}
    (hN : ∀ m : Pair, IsEven m.1 → IsEven m.2 → m + matAct (invol i) (act₂ π m) ∈ N) :
    16 ≤ Nat.card N := by
  have key : ∀ (ι : (Fin 5 → ZMod 2) → Pair) (p : Pair → Fin 5 → ZMod 2),
      (∀ v, IsEven v → IsEven (ι v).1 ∧ IsEven (ι v).2) →
      (∀ v w, p (ι v + matAct (invol i) (act₂ π (ι v))) =
        p (ι w + matAct (invol i) (act₂ π (ι w))) → v = w) → 16 ≤ Nat.card N := by
    intro ι p hι hp
    rw [← card_even]
    exact Nat.card_le_card_of_injective
      (fun v => ⟨ι v.1 + matAct (invol i) (act₂ π (ι v.1)), hN _ (hι v.1 v.2).1 (hι v.1 v.2).2⟩)
      fun v w h => Subtype.ext (hp v.1 w.1 (congrArg (fun x : N => p x) h))
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 :=
    (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i
  · refine key (fun v => (v, 0)) Prod.fst (fun v hv => ⟨hv, isEven_zero⟩) fun v w h => ?_
    simpa [matAct_invol₀, act₂, act_zero] using h
  · refine key (fun v => (0, v)) Prod.fst (fun v hv => ⟨isEven_zero, hv⟩) fun v w h => ?_
    simp only [matAct_invol₁, act₂, act_zero, Prod.mk_add_mk, zero_add] at h
    rw [← act_inv_act π v, h, act_inv_act]
  · refine key (fun v => (v, 0)) Prod.snd (fun v hv => ⟨hv, isEven_zero⟩) fun v w h => ?_
    simp only [matAct_invol₂, act₂, act_zero, Prod.mk_add_mk, add_zero, zero_add] at h
    rw [← act_inv_act π v, h, act_inv_act]

theorem cond_injective {u : Fin 5 → ZMod 2} (hu : u ≠ 0) :
    Function.Injective fun p : Bool => cond p u 0 := by
  rintro (_ | _) (_ | _) h <;> simp only [Bool.cond_false, Bool.cond_true] at h
  · rfl
  · exact absurd h.symm hu
  · exact absurd h hu
  · rfl

theorem cond_add_cond_mem {N : AddSubgroup Pair} {x y : Pair} (hx : x ∈ N) (hy : y ∈ N)
    (p q : Bool) : cond p x 0 + cond q y 0 ∈ N := by
  cases p <;> cases q <;> simp [hx, hy, N.add_mem hx hy, N.zero_mem]

theorem mem_of_matOne {N : AddSubgroup Pair} {π : Perm (Fin 5)}
    (hN : ∀ m : Pair, IsEven m.1 → IsEven m.2 → m + matAct matOne (act₂ π m) ∈ N)
    {v : Fin 5 → ZMod 2} (hv : IsEven v) :
    ((v + act π v, 0) : Pair) ∈ N ∧ ((0, v + act π v) : Pair) ∈ N := by
  have h1 := hN (v, 0) hv isEven_zero
  have h2 := hN (0, v) isEven_zero hv
  simp only [matAct_matOne, act₂, act_zero, Prod.mk_add_mk, add_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem four_le_card_of_ne_one {N : AddSubgroup Pair} {π : Perm (Fin 5)}
    (hN : ∀ m : Pair, IsEven m.1 → IsEven m.2 → m + matAct matOne (act₂ π m) ∈ N)
    (hπ : π ≠ 1) : 4 ≤ Nat.card N := by
  obtain ⟨v, hv, hvπ⟩ : ∃ v, IsEven v ∧ act π v ≠ v := by
    by_contra h
    push Not at h
    exact hπ (eq_one_of_act_eq h)
  obtain ⟨h1, h2⟩ := mem_of_matOne hN hv
  have hu0 : v + act π v ≠ 0 := fun h0 => hvπ (by
    rw [← add_zero (act π v), ← h0, ← add_assoc, add_comm (act π v) v, add_assoc,
      vec_add_self, add_zero])
  let f : Bool × Bool → N := fun pq => ⟨cond pq.1 ((v + act π v, 0) : Pair) 0 +
    cond pq.2 ((0, v + act π v) : Pair) 0, cond_add_cond_mem h1 h2 pq.1 pq.2⟩
  have hf : Function.Injective f := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    have h' := congrArg Subtype.val h
    have e : ∀ p q : Bool,
        cond p ((v + act π v, 0) : Pair) 0 + cond q ((0, v + act π v) : Pair) 0 =
          (cond p (v + act π v) 0, cond q (v + act π v) 0) := by
      intro p q
      cases p <;> cases q <;> simp [Prod.ext_iff]
    simp only [f, e, Prod.mk.injEq] at h'
    rw [cond_injective hu0 h'.1, cond_injective hu0 h'.2]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this

theorem sixteen_le_card_of_highRank {N : AddSubgroup Pair} {π : Perm (Fin 5)}
    (hN : ∀ m : Pair, IsEven m.1 → IsEven m.2 → m + matAct matOne (act₂ π m) ∈ N)
    (hπ : HighRank π) : 16 ≤ Nat.card N := by
  obtain ⟨v₁, v₂, hv₁, hv₂, h1, h2, h12⟩ := hπ
  obtain ⟨a₁, b₁⟩ := mem_of_matOne hN hv₁
  obtain ⟨a₂, b₂⟩ := mem_of_matOne hN hv₂
  set u₁ := v₁ + act π v₁
  set u₂ := v₂ + act π v₂
  let c : Bool × Bool → Fin 5 → ZMod 2 := fun pq => cond pq.1 u₁ 0 + cond pq.2 u₂ 0
  have hc : Function.Injective c := cond_add_cond_injective h1 h2 h12
  have hmem : ∀ x : (Bool × Bool) × (Bool × Bool), ((c x.1, c x.2) : Pair) ∈ N := by
    intro x
    have e : ((c x.1, c x.2) : Pair) =
        (cond x.1.1 ((u₁, 0) : Pair) 0 + cond x.1.2 ((u₂, 0) : Pair) 0) +
          (cond x.2.1 ((0, u₁) : Pair) 0 + cond x.2.2 ((0, u₂) : Pair) 0) := by
      obtain ⟨⟨_ | _, _ | _⟩, ⟨_ | _, _ | _⟩⟩ := x <;> simp [c, Prod.ext_iff]
    rw [e]
    exact N.add_mem (cond_add_cond_mem a₁ a₂ _ _) (cond_add_cond_mem b₁ b₂ _ _)
  have hf : Function.Injective fun x : (Bool × Bool) × (Bool × Bool) =>
      (⟨(c x.1, c x.2), hmem x⟩ : N) := by
    intro x y h
    have h' := congrArg Subtype.val h
    simp only [Prod.mk.injEq] at h'
    exact Prod.ext (hc h'.1) (hc h'.2)
  have := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool] at this

variable {G : Type} [Group G] {S Z H : Subgroup G}

theorem Coord.mem_img_commutator (C : Coord S Z H) (hS : Special S Z) {d : G}
    (hd : d ∈ normalizer (S : Set G)) {π : Perm (Fin 5)} {M : Mat2} (h : C.ActsAs d π M)
    {m : Pair} (hm1 : IsEven m.1) (hm2 : IsEven m.2) :
    m + matAct M (act₂ π m) ∈ C.img hS (⁅S, zpowers d⁆ ⊔ Z) := by
  obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
  rw [Prod.mk.eta] at hsm
  have hds : d * s⁻¹ * d⁻¹ ∈ S := (mem_normalizer_iff.mp hd _).mp (S.inv_mem hs)
  have e : ⁅s, d⁆ = s * (d * s⁻¹ * d⁻¹) := by
    rw [commutatorElement_def]
    group
  refine ⟨⁅s, d⁆, ⟨mem_sup_left (commutator_mem_commutator hs (mem_zpowers d)), ?_⟩, ?_⟩
  · rw [e]
    exact S.mul_mem hs hds
  · rw [e, C.Ψ_mul hS hs hds, h _ (S.inv_mem hs), C.Ψ_inv hS hs, hsm]

theorem Coord.card_commutator_sup [Finite G] (C : Coord S Z H) (hS : Special S Z) {d : G}
    (hd : d ∈ normalizer (S : Set G)) :
    Nat.card (⁅S, zpowers d⁆ ⊔ Z : Subgroup G) =
      4 * Nat.card (C.img hS (⁅S, zpowers d⁆ ⊔ Z)) := by
  refine C.card_eq_four_mul hS le_sup_right (sup_le (commutator_le.mpr fun a ha b hb => ?_) hS.le)
  have hb : b ∈ normalizer (S : Set G) := (zpowers_le.mpr hd) hb
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact S.mul_mem ha ((mem_normalizer_iff.mp hb _).mp (S.inv_mem ha))

theorem Coord.mem_of_actsAs_one [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hsyl : IsSylowOf 2 S (centralizerMod (normalizer (S : Set G)) S Z)) {d : G}
    (hd : d ∈ normalizer (S : Set G)) (h : C.ActsAs d 1 matOne) (h2 : d * d ∈ S) : d ∈ S := by
  have hc := mem_centralizerMod_of hS hd fun s hs => by
    rw [← C.Ψ_eq_iff hS ((mem_normalizer_iff.mp hd s).mp hs) hs, h s hs, act₂_one, matAct_matOne]
  refine mem_of_mem_centralizerMod hsyl hc (n := 11) ?_
  have h1 : (⟨d * d, h2⟩ : ↥S) ^ Nat.card S = 1 := pow_card_eq_one'
  rw [C.card_S hS] at h1
  have h3 : (d * d) ^ 1024 = 1 := by
    have := congrArg Subtype.val h1
    simpa using this
  calc d ^ 2 ^ 11 = (d * d) ^ 1024 := by rw [← sq, ← pow_mul]; norm_num
    _ = 1 := h3

@[expose] def Coord.permSubgroup (C : Coord S Z H) : Subgroup G where
  carrier := {d | d ∈ normalizer (S : Set G) ∧ ∃ π, C.ActsAs d π matOne}
  mul_mem' := by
    rintro a b ⟨ha, π, hπ⟩ ⟨hb, π', hπ'⟩
    refine ⟨mul_mem ha hb, π * π', ?_⟩
    have := hπ.mul hπ' hb
    rwa [matMul_matOne] at this
  one_mem' := ⟨one_mem _, 1, C.actsAs_one⟩
  inv_mem' := by
    rintro a ⟨ha, π, hπ⟩
    refine ⟨inv_mem ha, π⁻¹, fun s hs => ?_⟩
    have hs' : a⁻¹ * s * a⁻¹⁻¹ ∈ S := (mem_normalizer_iff.mp (inv_mem ha) s).mp hs
    have h1 := hπ _ hs'
    have e : a * (a⁻¹ * s * a⁻¹⁻¹) * a⁻¹ = s := by group
    rw [e, matAct_matOne] at h1
    rw [matAct_matOne, h1, act₂_mul, inv_mul_cancel, act₂_one]

variable [Finite G] (C : Coord S Z H) (hS : Special S Z) (hHS : H ≤ normalizer (S : Set G))
  (hSH : normalizer (S : Set G) ≤ normalizer (H : Set G))
  (hsyl : IsSylowOf 2 S (centralizerMod (normalizer (S : Set G)) S Z))
include C hS hHS hSH hsyl

theorem Coord.sixteen_le_card_commutator {t : G} (ht : t ∈ normalizer (S : Set G)) (htS : t ∉ S)
    (ht2 : t * t ∈ S) : 16 ≤ Nat.card (⁅S, zpowers t⁆ ⊔ Z : Subgroup G) := by
  obtain ⟨π, M, h⟩ := C.exists_actsAs hS hHS hSH ht
  have hM := (h.sq_eq hS ht ht2).1
  have hN := fun m (hm1 : IsEven (m : Pair).1) hm2 => C.mem_img_commutator hS ht h hm1 hm2
  rw [C.card_commutator_sup hS ht]
  by_cases hM1 : M = matOne
  · subst hM1
    have hπ1 : π ≠ 1 := by
      rintro rfl
      exact htS (C.mem_of_actsAs_one hS hsyl ht h ht2)
    have := four_le_card_of_ne_one hN hπ1
    omega
  · obtain ⟨i, rfl⟩ := invol_cases M hM hM1
    have := sixteen_le_card_of_invol hN
    omega

theorem Coord.exists_sixtyfour_le {D : Subgroup G} (hD : D ≤ normalizer (S : Set G))
    (hDe : ∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S)
    (hidx : 4 ≤ (D ⊓ S).relIndex D) :
    ∃ d ∈ D, 64 ≤ Nat.card (⁅S, zpowers d⁆ ⊔ Z : Subgroup G) := by
  have hsq : ∀ x ∈ D, x * x ∈ S := fun x hx => (hDe x hx x hx).1
  obtain ⟨a, ha, b, hb, haS, hbS, habS⟩ : ∃ a ∈ D, ∃ b ∈ D, a ∉ S ∧ b ∉ S ∧ a * b ∉ S := by
    by_contra hne
    push Not at hne
    have h2 := relIndex_le_two (K := D ⊓ S) (L := D) (fun x hx => ⟨D.mul_mem hx hx, hsq x hx⟩)
      fun x hx y hy => by
        by_cases hxS : x ∈ S
        · exact Or.inl ⟨hx, hxS⟩
        by_cases hyS : y ∈ S
        · exact Or.inr (Or.inl ⟨hy, hyS⟩)
        exact Or.inr (Or.inr ⟨D.mul_mem hx hy, hne x hx y hy hxS hyS⟩)
    omega
  have hinv : ∀ x ∈ D, ∀ π M, C.ActsAs x π M → matMul M M = matOne → M ≠ matOne →
      64 ≤ Nat.card (⁅S, zpowers x⁆ ⊔ Z : Subgroup G) := by
    intro x hx π M h hM hM1
    obtain ⟨i, rfl⟩ := invol_cases M hM hM1
    rw [C.card_commutator_sup hS (hD hx)]
    have := sixteen_le_card_of_invol fun m hm1 hm2 => C.mem_img_commutator hS (hD hx) h hm1 hm2
    omega
  have hhigh : ∀ x ∈ D, ∀ π, C.ActsAs x π matOne → HighRank π →
      64 ≤ Nat.card (⁅S, zpowers x⁆ ⊔ Z : Subgroup G) := by
    intro x hx π h hπ
    rw [C.card_commutator_sup hS (hD hx)]
    have := sixteen_le_card_of_highRank
      (fun m hm1 hm2 => C.mem_img_commutator hS (hD hx) h hm1 hm2) hπ
    omega
  have hab := D.mul_mem ha hb
  obtain ⟨πa, Ma, hA⟩ := C.exists_actsAs hS hHS hSH (hD ha)
  obtain ⟨πb, Mb, hB⟩ := C.exists_actsAs hS hHS hSH (hD hb)
  have hAB := hA.mul hB (hD hb)
  obtain ⟨hMa, hπa⟩ := hA.sq_eq hS (hD ha) (hsq a ha)
  obtain ⟨hMb, hπb⟩ := hB.sq_eq hS (hD hb) (hsq b hb)
  have hπab := (hAB.sq_eq hS (hD hab) (hsq _ hab)).2
  by_cases hMa1 : Ma = matOne
  · by_cases hMb1 : Mb = matOne
    · subst hMa1 hMb1
      rw [matMul_matOne] at hAB
      have hπa1 : πa ≠ 1 := by
        rintro rfl
        exact haS (C.mem_of_actsAs_one hS hsyl (hD ha) hA (hsq a ha))
      have hπb1 : πb ≠ 1 := by
        rintro rfl
        exact hbS (C.mem_of_actsAs_one hS hsyl (hD hb) hB (hsq b hb))
      have hπab1 : πa * πb ≠ 1 := by
        intro e
        rw [e] at hAB
        exact habS (C.mem_of_actsAs_one hS hsyl (hD hab) hAB (hsq _ hab))
      rcases exists_conj_double hπa hπb hπab hπa1 hπb1 hπab1 with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
      · exact ⟨a, ha, hhigh a ha πa hA (highRank_of_conj hg)⟩
      · exact ⟨b, hb, hhigh b hb πb hB (highRank_of_conj hg)⟩
      · exact ⟨a * b, hab, hhigh _ hab _ hAB (highRank_of_conj hg)⟩
    · exact ⟨b, hb, hinv b hb πb Mb hB hMb hMb1⟩
  · exact ⟨a, ha, hinv a ha πa Ma hA hMa hMa1⟩

theorem Coord.relIndex_le_eight {D : Subgroup G} (hD : D ≤ normalizer (S : Set G))
    (hDe : ∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S) : (D ⊓ S).relIndex D ≤ 8 := by
  have hsq : ∀ x ∈ D, x * x ∈ S := fun x hx => (hDe x hx x hx).1
  have hSP : D ⊓ S ≤ D ⊓ C.permSubgroup := fun x hx =>
    ⟨hx.1, Subgroup.le_normalizer hx.2, 1, C.actsAs_of_mem hS hx.2⟩
  have h1 : (D ⊓ C.permSubgroup).relIndex D ≤ 2 := by
    refine relIndex_le_two (fun x hx => hSP ⟨D.mul_mem hx hx, hsq x hx⟩) fun a ha b hb => ?_
    obtain ⟨πa, Ma, hA⟩ := C.exists_actsAs hS hHS hSH (hD ha)
    obtain ⟨πb, Mb, hB⟩ := C.exists_actsAs hS hHS hSH (hD hb)
    have hAB := hA.mul hB (hD hb)
    by_cases hMa1 : Ma = matOne
    · exact Or.inl ⟨ha, hD ha, πa, hMa1 ▸ hA⟩
    by_cases hMb1 : Mb = matOne
    · exact Or.inr (Or.inl ⟨hb, hD hb, πb, hMb1 ▸ hB⟩)
    obtain ⟨i, rfl⟩ := invol_cases Ma (hA.sq_eq hS (hD ha) (hsq a ha)).1 hMa1
    obtain ⟨j, rfl⟩ := invol_cases Mb (hB.sq_eq hS (hD hb) (hsq b hb)).1 hMb1
    have hij := invol_mul_invol i j
      (hAB.sq_eq hS (hD (D.mul_mem ha hb)) (hsq _ (D.mul_mem ha hb))).1
    rw [hij] at hAB
    exact Or.inr (Or.inr ⟨D.mul_mem ha hb, hD (D.mul_mem ha hb), πa * πb, hAB⟩)
  have h2 : (D ⊓ S).relIndex (D ⊓ C.permSubgroup) ≤ 4 := by
    refine relIndex_le_four (fun x hx => ⟨D.mul_mem hx.1 hx.1, hsq x hx.1⟩)
      fun a ha b hb c hc => ?_
    obtain ⟨haD, -, πa, hA⟩ := ha
    obtain ⟨hbD, hbN, πb, hB⟩ := hb
    obtain ⟨hcD, hcN, πc, hC⟩ := hc
    have hAB := hA.mul hB hbN
    have hAC := hA.mul hC hcN
    have hBC := hB.mul hC hcN
    rw [matMul_matOne] at hAB hAC hBC
    have hABC := hAB.mul hC hcN
    rw [matMul_matOne] at hABC
    have hmem : ∀ x ∈ D, C.ActsAs x 1 matOne → x ∈ D ⊓ S := fun x hx h =>
      ⟨hx, C.mem_of_actsAs_one hS hsyl (hD hx) h (hsq x hx)⟩
    have sq : ∀ x ∈ D, ∀ π, C.ActsAs x π matOne → π * π = 1 := fun x hx π h =>
      (h.sq_eq hS (hD hx) (hsq x hx)).2
    have hab := D.mul_mem haD hbD
    have hac := D.mul_mem haD hcD
    have hbc := D.mul_mem hbD hcD
    have habc := D.mul_mem hab hcD
    rcases dep_of_three (sq a haD πa hA) (sq b hbD πb hB) (sq c hcD πc hC) (sq _ hab _ hAB)
      (sq _ hac _ hAC) (sq _ hbc _ hBC) with h | h | h | h | h | h | h
    · exact Or.inl (hmem a haD (h ▸ hA))
    · exact Or.inr (Or.inl (hmem b hbD (h ▸ hB)))
    · exact Or.inr (Or.inr (Or.inl (hmem _ hab (h ▸ hAB))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hmem c hcD (h ▸ hC)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hmem _ hac (h ▸ hAC))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hmem _ hbc (h ▸ hBC)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hmem _ habc (h ▸ hABC)))))))
  calc (D ⊓ S).relIndex D = (D ⊓ S).relIndex (D ⊓ C.permSubgroup) *
        (D ⊓ C.permSubgroup).relIndex D :=
        (relIndex_mul_relIndex _ _ _ hSP inf_le_left).symm
    _ ≤ 4 * 2 := Nat.mul_le_mul h2 h1
    _ = 8 := rfl

end Sec2

open Sec2

theorem step26ii_of (h24 : Step24) (h26 : Step26) : Step26ii := by
  intro G _ _ A R g E F hS
  obtain ⟨-, -, -, -, -, hsyl, -, hHS, hSH⟩ := h26 G A R g E F hS
  have hSp := special_of h24 hS
  obtain ⟨C⟩ := nonempty_coord h26 hS
  exact ⟨fun t ht htS ht2 => C.sixteen_le_card_commutator hSp hHS hSH hsyl ht htS ht2,
    fun D hD hDe hidx => C.exists_sixtyfour_le hSp hHS hSH hsyl hD hDe hidx,
    fun D hD hDe => C.relIndex_le_eight hSp hHS hSH hsyl hD hDe⟩

end CFSG.ComponentClassification.AS81
