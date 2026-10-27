module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Data.Nat.Prime.Defs
import CFSG.FeitThompson.Local.FrobeniusWielandtFixedPointOrder
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Totient

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {A V : Type*} [Group A] [Group V] {D K : Subgroup A}

theorem forall_mem_zpowers_map_eq_iff (ρ : A →* MulAut V) (t : A) (v : V) :
    (∀ s ∈ Subgroup.zpowers t, ρ s v = v) ↔ ρ t v = v := by
  refine ⟨fun h => h t (Subgroup.mem_zpowers t), fun h s hs => ?_⟩
  have ht : t ∈ (MulAction.stabilizer (MulAut V) v).comap ρ := by
    simpa [MulAction.mem_stabilizer_iff] using h
  have := Subgroup.zpowers_le.2 ht hs
  simpa [MulAction.mem_stabilizer_iff] using this

theorem natCard_eq_natCard_fixedPoints_pow_natCard_of_disjoint [Finite A] [Finite V]
    [Group.IsSolvable A] [Group.IsSolvable V] {T : Subgroup A} (ρ : A →* MulAut V)
    (hcop : (Nat.card A).Coprime (Nat.card V)) (hD : D.Normal) (hdisj : Disjoint D T)
    (hfrob : ∀ t ∈ T, t ≠ 1 → D ⊓ Subgroup.centralizer {t} = ⊥)
    (hCD : ∀ v : V, (∀ d ∈ D, ρ d v = v) → v = 1) :
    Nat.card V = Nat.card {v : V // ∀ t ∈ T, ρ t v = v} ^ Nat.card T := by
  set A' := D ⊔ T with hA'
  have hDA' : D ≤ A' := le_sup_left
  have hTA' : T ≤ A' := le_sup_right
  set ρ' : A' →* MulAut V := ρ.comp A'.subtype with hρ'
  have hcop' : (Nat.card A').Coprime (Nat.card V) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card A') hcop
  have hD' : (D.subgroupOf A').Normal := hD.subgroupOf A'
  have hcompl : Subgroup.IsComplement' (D.subgroupOf A') (T.subgroupOf A') := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · refine Subgroup.disjoint_def.2 fun {x} hx1 hx2 => ?_
      exact Subtype.ext (Subgroup.disjoint_def.1 hdisj (Subgroup.mem_subgroupOf.1 hx1)
        (Subgroup.mem_subgroupOf.1 hx2))
    · refine Set.eq_univ_of_forall fun x => ?_
      have hx : (x : A) ∈ (D : Set A) * (T : Set A) := by
        rw [← @Subgroup.normal_mul _ _ D T hD]
        exact x.2
      obtain ⟨d, hd, t, ht, hdt⟩ := hx
      exact ⟨⟨d, hDA' hd⟩, Subgroup.mem_subgroupOf.2 hd, ⟨t, hTA' ht⟩,
        Subgroup.mem_subgroupOf.2 ht, Subtype.ext hdt⟩
  have hC' : ∀ w ∈ T.subgroupOf A', w ≠ 1 →
      D.subgroupOf A' ⊓ Subgroup.centralizer {w} = ⊥ := by
    intro w hw hw1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx1 : (x : A) ∈ D := Subgroup.mem_subgroupOf.1 hx.1
    have hx2 : (w : A) * (x : A) = (x : A) * (w : A) := by
      have := Subgroup.mem_centralizer_iff.1 hx.2 w rfl
      exact_mod_cast congrArg Subtype.val this
    have hmem : (x : A) ∈ D ⊓ Subgroup.centralizer {(w : A)} :=
      ⟨hx1, Subgroup.mem_centralizer_iff.2 (by simpa using hx2)⟩
    rw [hfrob w (Subgroup.mem_subgroupOf.1 hw) fun h => hw1 (Subtype.ext h)] at hmem
    exact Subtype.ext (Subgroup.mem_bot.1 hmem)
  have hone : ∀ B : Subgroup A', D.subgroupOf A' ≤ B →
      Nat.card {v : V // ∀ b ∈ B, ρ' b v = v} = 1 := by
    intro B hB
    have hval : ∀ x : {v : V // ∀ b ∈ B, ρ' b v = v}, (x : V) = 1 := by
      intro x
      refine hCD x fun d hd => ?_
      have := x.2 ⟨d, hDA' hd⟩ (hB (Subgroup.mem_subgroupOf.2 hd))
      simpa [hρ'] using this
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext ((hval x).trans (hval y).symm)⟩, ⟨⟨1, fun b _ => map_one _⟩⟩⟩
  have key := natCard_mul_natCard_fixedPoints_pow_natCard_eq ρ' hcop' hD' hcompl hC'
  rw [hone ⊤ le_top, hone (D.subgroupOf A') le_rfl, one_pow, one_mul, mul_one] at key
  have hCT : Nat.card {v : V // ∀ b ∈ T.subgroupOf A', ρ' b v = v}
      = Nat.card {v : V // ∀ t ∈ T, ρ t v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      ⟨fun h t ht => by simpa [hρ'] using h ⟨t, hTA' ht⟩ (Subgroup.mem_subgroupOf.2 ht),
        fun h b hb => by simpa [hρ'] using h b (Subgroup.mem_subgroupOf.1 hb)⟩)
  have hTcard : Nat.card (T.subgroupOf A') = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA').toEquiv
  rw [hCT, hTcard] at key
  exact key

section Main

variable [Finite A] [Finite V] [Group.IsSolvable A] [Group.IsSolvable V] [Nontrivial V]
  {ρ : A →* MulAut V} (hcop : (Nat.card A).Coprime (Nat.card V)) (hD : D.Normal)
  (hDK : Subgroup.IsComplement' D K) (hK : K ≠ ⊥)
  (hfrob : ∀ k ∈ K, k ≠ 1 → D ⊓ Subgroup.centralizer {k} = ⊥)
  (hCD : FixedPoints.subgroup (ρ.comp D.subtype).range V = ⊥)
  (hCK : ∀ k ∈ K, k ≠ 1 → FixedPoints.subgroup (ρ.comp (Subgroup.zpowers k).subtype).range V
    = FixedPoints.subgroup (ρ.comp K.subtype).range V)

include hcop hD hDK hK hfrob hCD hCK

theorem prime_natCard_and_fixedPoints_ne_bot_and_natCard_eq_pow :
    (Nat.card K).Prime ∧ FixedPoints.subgroup (ρ.comp K.subtype).range V ≠ ⊥ ∧
      Nat.card V
        = Nat.card (FixedPoints.subgroup (ρ.comp K.subtype).range V) ^ Nat.card K := by
  have hCD' : ∀ v : V, (∀ d ∈ D, ρ d v = v) → v = 1 := by
    intro v hv
    have : v ∈ FixedPoints.subgroup (ρ.comp D.subtype).range V :=
      (mem_fixedPoints_comp_subtype_iff ρ D).2 hv
    rw [hCD, Subgroup.mem_bot] at this
    exact this
  have hCK' : ∀ k ∈ K, k ≠ 1 → ∀ v : V, (ρ k v = v ↔ ∀ k' ∈ K, ρ k' v = v) := by
    intro k hk hk1 v
    rw [← forall_mem_zpowers_map_eq_iff ρ k v,
      ← mem_fixedPoints_comp_subtype_iff ρ (Subgroup.zpowers k),
      ← mem_fixedPoints_comp_subtype_iff ρ K, hCK k hk hk1]
  have hVK : Nat.card V = Nat.card {v : V // ∀ k ∈ K, ρ k v = v} ^ Nat.card K :=
    natCard_eq_natCard_fixedPoints_pow_natCard_of_disjoint ρ hcop hD hDK.disjoint hfrob hCD'
  set a := Nat.card {v : V // ∀ k ∈ K, ρ k v = v} with ha
  have h1a : 2 ≤ a := by
    rcases Nat.lt_or_ge a 2 with h | h
    · exfalso
      have hle : Nat.card V ≤ 1 := by
        rw [hVK]
        calc a ^ Nat.card K ≤ 1 ^ Nat.card K := Nat.pow_le_pow_left (by omega) _
          _ = 1 := one_pow _
      have := Finite.one_lt_card (α := V)
      omega
    · exact h
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (n := Nat.card K) (by have := (Subgroup.one_lt_card_iff_ne_bot K).2 hK; omega)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, htord⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpdvd
  have htK : (t : A) ∈ K := t.2
  have htord' : orderOf (t : A) = p := by rw [Subgroup.orderOf_coe]; exact htord
  have ht1 : (t : A) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord'
    exact hp.one_lt.ne' htord'.symm
  set T := Subgroup.zpowers (t : A) with hT
  have hTK : T ≤ K := Subgroup.zpowers_le.2 htK
  have hVT : Nat.card V = Nat.card {v : V // ∀ s ∈ T, ρ s v = v} ^ Nat.card T :=
    natCard_eq_natCard_fixedPoints_pow_natCard_of_disjoint ρ hcop hD
      (hDK.disjoint.mono_right hTK)
      (fun s hs hs1 => hfrob s (hTK hs) hs1) hCD'
  have hTcard : Nat.card T = p := by rw [hT, Nat.card_zpowers, htord']
  have hCTeq : Nat.card {v : V // ∀ s ∈ T, ρ s v = v} = a := by
    rw [ha]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [forall_mem_zpowers_map_eq_iff]
    exact hCK' (t : A) htK ht1 v
  rw [hCTeq, hTcard] at hVT
  have hpeq : p = Nat.card K := Nat.pow_right_injective h1a (hVT.symm.trans hVK)
  have hcard : Nat.card (FixedPoints.subgroup (ρ.comp K.subtype).range V) = a := by
    rw [ha, natCard_fixedPoints_comp_subtype_eq_natCard_subtype]
  refine ⟨hpeq ▸ hp, ?_, ?_⟩
  · rw [← Subgroup.one_lt_card_iff_ne_bot, hcard]; omega
  · rw [hcard]; exact hVK

theorem prime_natCard_of_fixedPoints_eq : (Nat.card K).Prime :=
  (prime_natCard_and_fixedPoints_ne_bot_and_natCard_eq_pow hcop hD hDK hK hfrob hCD hCK).1

theorem fixedPoints_ne_bot_of_fixedPoints_eq :
    FixedPoints.subgroup (ρ.comp K.subtype).range V ≠ ⊥ :=
  (prime_natCard_and_fixedPoints_ne_bot_and_natCard_eq_pow hcop hD hDK hK hfrob hCD hCK).2.1

theorem natCard_eq_natCard_fixedPoints_pow_natCard_of_fixedPoints_eq :
    Nat.card V = Nat.card (FixedPoints.subgroup (ρ.comp K.subtype).range V) ^ Nat.card K :=
  (prime_natCard_and_fixedPoints_ne_bot_and_natCard_eq_pow hcop hD hDK hK hfrob hCD hCK).2.2

end Main

theorem prime_natCard_and_fixedPoints_ne_one_and_natCard_eq_pow [Finite A] [Finite V]
    [Group.IsSolvable A] [Group.IsSolvable V] [Nontrivial V] (ρ : A →* MulAut V)
    (hcop : (Nat.card A).Coprime (Nat.card V)) (hD : D.Normal)
    (hDK : Subgroup.IsComplement' D K) (hK : K ≠ ⊥)
    (hfrob : ∀ k ∈ K, k ≠ 1 → D ⊓ Subgroup.centralizer {k} = ⊥)
    (hCD : {v : V | ∀ d ∈ D, ρ d v = v} = {1})
    (hCK : ∀ k ∈ K, k ≠ 1 → {v : V | ρ k v = v} = {v : V | ∀ k' ∈ K, ρ k' v = v}) :
    (Nat.card K).Prime ∧ {v : V | ∀ k ∈ K, ρ k v = v} ≠ {1} ∧
      Nat.card V = Nat.card {v : V | ∀ k ∈ K, ρ k v = v} ^ Nat.card K := by
  have hCD' : FixedPoints.subgroup (ρ.comp D.subtype).range V = ⊥ := by
    refine Subgroup.eq_bot_iff_forall _ |>.2 fun v hv => ?_
    have : v ∈ ({1} : Set V) := hCD ▸ (mem_fixedPoints_comp_subtype_iff ρ D).1 hv
    simpa using this
  have hCK' : ∀ k ∈ K, k ≠ 1 →
      FixedPoints.subgroup (ρ.comp (Subgroup.zpowers k).subtype).range V
        = FixedPoints.subgroup (ρ.comp K.subtype).range V := by
    intro k hk hk1
    refine SetLike.ext fun v => ?_
    rw [mem_fixedPoints_comp_subtype_iff ρ (Subgroup.zpowers k),
      mem_fixedPoints_comp_subtype_iff ρ K, forall_mem_zpowers_map_eq_iff]
    exact Set.ext_iff.1 (hCK k hk hk1) v
  obtain ⟨hp, hne, hcard⟩ :=
    prime_natCard_and_fixedPoints_ne_bot_and_natCard_eq_pow hcop hD hDK hK hfrob hCD' hCK'
  have hcardeq : Nat.card (FixedPoints.subgroup (ρ.comp K.subtype).range V)
      = Nat.card {v : V | ∀ k ∈ K, ρ k v = v} :=
    natCard_fixedPoints_comp_subtype_eq_natCard_subtype ρ K
  refine ⟨hp, ?_, by rw [hcard, hcardeq]⟩
  intro hbad
  refine hne (Subgroup.eq_bot_iff_forall _ |>.2 fun v hv => ?_)
  have : v ∈ ({1} : Set V) := hbad ▸ (mem_fixedPoints_comp_subtype_iff ρ K).1 hv
  simpa using this

end CFSG.FeitThompson
