module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4W49Hat
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4W49Cover

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.W49

open Subgroup ModIso
open scoped Pointwise commutatorElement

structure PairCoords {G : Type} [Group G] (z : G) (T : Subgroup G) (κ : GL (Fin 3) (ZMod 2) →* G)
    (E₀ : Subgroup G) (e : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G) : Prop where
  mem : ∀ a b, e a b ∈ T
  add : ∀ a b a' b', e (a + a') (b + b') = e a b * e a' b'
  surj : ∀ t ∈ T, ∃ a b, e a b = t
  inj : ∀ a b, e a b = 1 → a = 0 ∧ b = 0
  swap : ∀ a b, z * e a b * z⁻¹ = e b a
  diag : ∀ (A : GL (Fin 3) (ZMod 2)) (g : G), g ∈ normalizer (T : Set G) →
    (∃ ε ∈ E₀, g = ε * κ A) → ∀ a b, g * e a b * g⁻¹ = e (mv A a) (mv A b)

theorem pairCoords_of_tCoords {G : Type} [Group G] {z : G} {T : Subgroup G}
    {κ : GL (Fin 3) (ZMod 2) →* G} {E₀ : Subgroup G}
    {cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G} (hc : TCoords z T κ E₀ cT) :
    PairCoords z T κ E₀ (fun a b => cT b (a + b)) where
  mem a b := hc.mem _ _
  add a b a' b' := by
    rw [← hc.add]
    congr 1
    abel
  surj t ht := by
    obtain ⟨v, w, rfl⟩ := hc.surj t ht
    refine ⟨v + w, v, ?_⟩
    show cT v (v + w + v) = cT v w
    congr 1
    rw [add_comm v w, add_assoc, add_self_v, add_zero]
  inj a b h := by
    obtain ⟨h1, h2⟩ := hc.inj _ _ h
    subst h1
    rw [add_zero] at h2
    exact ⟨h2, rfl⟩
  swap a b := by
    show z * cT b (a + b) * z⁻¹ = cT a (b + a)
    rw [hc.conj_z]
    congr 1
    · rw [← add_assoc, add_comm b a, add_assoc, add_self_v, add_zero]
    · exact add_comm a b
  diag A g hg hge a b := by
    show g * cT b (a + b) * g⁻¹ = cT (mv A b) (mv A a + mv A b)
    rw [hc.conj_lin A g hg hge, Matrix.mulVec_add]

section PairLemmas

variable {G : Type} [Group G] {z : G} {T : Subgroup G} {κ : GL (Fin 3) (ZMod 2) →* G}
  {E₀ : Subgroup G} {e : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G} (he : PairCoords z T κ E₀ e)
include he

theorem PairCoords.zero : e 0 0 = 1 := by
  have h1 := he.add 0 0 0 0
  simp only [add_zero] at h1
  exact (mul_eq_left.1 h1.symm)

theorem PairCoords.sq (a b : Fin 3 → ZMod 2) : e a b * e a b = 1 := by
  rw [← he.add, add_self_v, add_self_v, he.zero]

theorem PairCoords.comm (a b a' b' : Fin 3 → ZMod 2) : e a b * e a' b' = e a' b' * e a b := by
  rw [← he.add, ← he.add, add_comm a, add_comm b]

theorem PairCoords.split (a b : Fin 3 → ZMod 2) : e a b = e a 0 * e 0 b := by
  rw [← he.add, add_zero, zero_add]

theorem PairCoords.eq_iff {a b a' b' : Fin 3 → ZMod 2} : e a b = e a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro hab
    have h1 : e (a + a') (b + b') = 1 := by rw [he.add, hab, he.sq]
    obtain ⟨h2, h3⟩ := he.inj _ _ h1
    refine ⟨?_, ?_⟩
    · have := congrArg (· + a') h2
      simpa [add_assoc, add_self_v] using this
    · have := congrArg (· + b') h3
      simpa [add_assoc, add_self_v] using this
  · rintro ⟨rfl, rfl⟩
    rfl

end PairLemmas

section Inst

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}
  {e : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G}

abbrev ON (T : Subgroup G) : Subgroup (normalizer (T : Set G)) :=
  CFSG.oddCore (normalizer (T : Set G))

@[expose] def eN (he : ∀ a b, e a b ∈ T) (a b : Fin 3 → ZMod 2) : normalizer (T : Set G) :=
  ⟨e a b, le_normalizer (he a b)⟩

@[expose] def iotaN (he : ∀ a b, e a b ∈ T) (a b : Fin 3 → ZMod 2) :
    normalizer (T : Set G) ⧸ ON T :=
  ((eN he a b : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T)

theorem mem_oddCoreOf_of_mem_ON {x : normalizer (T : Set G)} (hx : x ∈ ON T) :
    (x : G) ∈ AltStdSec.oddCoreOf (normalizer (T : Set G)) :=
  ⟨x, hx, rfl⟩

variable (c : Config G L Q n θ z) (hH : HData θ c.hn8 z T)

include hH in
theorem oddCoreOf_le_cent : AltStdSec.oddCoreOf (normalizer (T : Set G)) ≤
    centralizer (T : Set G) := by
  rw [hH.cent]
  exact le_sup_right

include hH in
theorem T_inf_oddCoreOf : T ⊓ AltStdSec.oddCoreOf (normalizer (T : Set G)) = ⊥ :=
  inf_eq_bot_of_coprime (by
    rw [hH.n0.card_eq, show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact Nat.Coprime.pow_left 6 (coprime_card_oddCoreOf _))

include hH in
theorem eq_one_of_mem_T_of_mem_ON {x : normalizer (T : Set G)} (hxT : (x : G) ∈ T)
    (hxO : x ∈ ON T) : x = 1 := by
  have h := mem_inf.2 ⟨hxT, mem_oddCoreOf_of_mem_ON hxO⟩
  rw [T_inf_oddCoreOf c hH, mem_bot] at h
  exact Subtype.ext h

@[expose] def zN (hH : HData θ c.hn8 z T) : normalizer (T : Set G) := ⟨z, hH.n0.norm⟩

include hH in
theorem zN_mul_self : zN c hH * zN c hH = 1 := Subtype.ext (z_mul_self c)

variable (he : PairCoords z T (kap θ c.hn8) (E θ c.hn8) e)
  (hsh : ∀ g ∈ normalizer (T : Set G), ∃ A B : GL (Fin 3) (ZMod 2),
    (∀ a b, g * e a b * g⁻¹ = e (mv A a) (mv B b)) ∨
      (∀ a b, g * e a b * g⁻¹ = e (mv B b) (mv A a)))
  (hcard : Nat.card (Hbar T) = 56448)

include hH he in
theorem card_hat (hcard : Nat.card (Hbar T) = 56448) :
    Nat.card (normalizer (T : Set G) ⧸ ON T) = 64 * 56448 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ON T)
  have h2 := card_normalizer_eq hH
  have h3 : Nat.card (ON T) = Nat.card (AltStdSec.oddCoreOf (normalizer (T : Set G))) :=
    (card_map_of_injective (normalizer (T : Set G)).subtype_injective).symm
  rw [hcard] at h2
  rw [h3, h2] at h1
  have hpos : 0 < Nat.card (AltStdSec.oddCoreOf (normalizer (T : Set G))) := Nat.card_pos
  have : Nat.card (normalizer (T : Set G) ⧸ ON T) *
      Nat.card (AltStdSec.oddCoreOf (normalizer (T : Set G))) =
      (64 * 56448) * Nat.card (AltStdSec.oddCoreOf (normalizer (T : Set G))) := by
    rw [← h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

include hH he hsh in
theorem hatData (hcard : Nat.card (Hbar T) = 56448) :
    HatData (iotaN he.mem) ((zN c hH : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T)
    where
  add a b a' b' := by
    rw [iotaN, iotaN, iotaN, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (he.add a b a' b')
  inj a b hab := by
    rw [iotaN, QuotientGroup.eq_one_iff] at hab
    have h1 := eq_one_of_mem_T_of_mem_ON c hH (he.mem a b) hab
    exact he.inj a b (congrArg Subtype.val h1)
  swap a b := by
    rw [iotaN, iotaN, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (he.swap a b)
  zh_sq := by rw [← QuotientGroup.mk_mul, zN_mul_self, QuotientGroup.mk_one]
  shape x := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨A, B, hg | hg⟩ := hsh g g.2
    · refine ⟨A, B, Or.inl fun a b => ?_⟩
      rw [iotaN, iotaN, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hg a b)
    · refine ⟨A, B, Or.inr fun a b => ?_⟩
      rw [iotaN, iotaN, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hg a b)
  ker x hx := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hgc : (g : G) ∈ centralizer (T : Set G) := by
      rw [mem_centralizer_iff]
      intro t ht
      obtain ⟨a, b, rfl⟩ := he.surj t ht
      have h1 := hx a b
      rw [iotaN, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq] at h1
      have hT : (((g * eN he.mem a b * g⁻¹)⁻¹ * eN he.mem a b : normalizer (T : Set G)) : G) ∈
          T := by
        have hgT : (g : G) * (e a b)⁻¹ * (g : G)⁻¹ ∈ T :=
          (mem_normalizer_iff.1 g.2 _).1 (inv_mem (he.mem a b))
        have : (((g * eN he.mem a b * g⁻¹)⁻¹ * eN he.mem a b : normalizer (T : Set G)) : G) =
            ((g : G) * (e a b)⁻¹ * (g : G)⁻¹) * e a b := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, eN]
          group
        rw [this]
        exact mul_mem hgT (he.mem a b)
      have h3 := eq_one_of_mem_T_of_mem_ON c hH hT h1
      rw [inv_mul_eq_one] at h3
      have h4 : (g : G) * e a b * (g : G)⁻¹ = e a b := by
        have := congrArg Subtype.val h3
        simpa [eN] using this
      calc e a b * g = ((g : G) * e a b * (g : G)⁻¹) * g := by rw [h4]
        _ = g * e a b := by group
    rw [hH.cent] at hgc
    have hTO : T ≤ normalizer (AltStdSec.oddCoreOf (normalizer (T : Set G)) : Set G) :=
      le_normalizer_of_conj' fun y hy x hx => conj_mem_oddCoreOf' (le_normalizer hy) hx
    have hm := Subgroup.coe_mul_of_left_le_normalizer_right T _ hTO
    have hg' : (g : G) ∈ (T : Set G) * (AltStdSec.oddCoreOf (normalizer (T : Set G)) : Set G) := by
      rw [← hm]
      exact hgc
    obtain ⟨t, ht, o, ho, hto⟩ := Set.mem_mul.1 hg'
    obtain ⟨a, b, rfl⟩ := he.surj t ht
    obtain ⟨o', ho', rfl⟩ := ho
    refine ⟨a, b, ?_⟩
    have hgeq : g = eN he.mem a b * o' := Subtype.ext (by
      rw [Subgroup.coe_mul]
      exact hto.symm)
    rw [hgeq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o').2 ho', mul_one]
    rfl
  card := card_hat c hH he hcard

abbrev DN (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (T : Subgroup G) :
    Subgroup (normalizer (T : Set G)) :=
  (Dsub θ hn).subgroupOf (normalizer (T : Set G))

include hH he in
theorem act_of_mem_Dsub {d : G} (hd : d ∈ Dsub θ c.hn8) :
    ∃ A : GL (Fin 3) (ZMod 2), ∀ a b, d * e a b * d⁻¹ = e (mv A a) (mv A b) := by
  obtain ⟨v, A, rfl⟩ := (mem_Dsub_iff θ c.hn8 _).1 hd
  exact ⟨A, he.diag A _ (Dsub_le_normalizer c hH hd) ⟨_, N0.eps_mem_E θ c.hn8 v, rfl⟩⟩

include hH he in
theorem eq_one_of_mem_DN_of_mem_ON {d : normalizer (T : Set G)} (hd : d ∈ DN θ c.hn8 T)
    (hdO : d ∈ ON T) : d = 1 := by
  have hd' : (d : G) ∈ Dsub θ c.hn8 := mem_subgroupOf.1 hd
  obtain ⟨v, A, hvA⟩ := (mem_Dsub_iff θ c.hn8 _).1 hd'
  have hc : (d : G) ∈ centralizer (T : Set G) :=
    oddCoreOf_le_cent c hH (mem_oddCoreOf_of_mem_ON hdO)
  have hact := he.diag A d d.2 ⟨_, N0.eps_mem_E θ c.hn8 v, hvA⟩
  have hA : A = 1 := eq_one_of_mv_fix fun a => by
    have h1 := hact a 0
    rw [← mem_centralizer_iff.1 hc _ (he.mem a 0), mul_inv_cancel_right] at h1
    exact ((he.eq_iff).1 h1).1.symm
  subst hA
  rw [map_one, mul_one] at hvA
  apply eq_one_of_mem_T_of_mem_ON c hH _ hdO
  rw [hvA]
  exact hH.n0.E_le (N0.eps_mem_E θ c.hn8 v)

include hH he in
theorem card_Dhat : Nat.card ((DN θ c.hn8 T).map (QuotientGroup.mk' (ON T))) = 1344 := by
  have hinj : Function.Injective ((QuotientGroup.mk' (ON T)).comp (DN θ c.hn8 T).subtype) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : (d : normalizer (T : Set G)) ∈ ON T := (QuotientGroup.eq_one_iff _).1 hd
    exact Subtype.ext (eq_one_of_mem_DN_of_mem_ON c hH he d.2 h1)
  have hmap : (DN θ c.hn8 T).map (QuotientGroup.mk' (ON T)) =
      ((QuotientGroup.mk' (ON T)).comp (DN θ c.hn8 T).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (Dsub_le_normalizer c hH)).toEquiv, card_Dsub]

theorem sq_not_dvd_1344 : ∀ p : ℕ, p.Prime → Odd p → ¬ p ^ 2 ∣ 1344 := by
  intro p hp hpo hdvd
  have h1 : p ^ 2 ≤ 1344 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 : p ≤ 36 := by nlinarith
  rw [Nat.odd_iff] at hpo
  interval_cases p <;> first | omega | (exact absurd hp (by norm_num)) | (revert hdvd; decide)

include hH he hsh in
theorem exists_lift (hcard : Nat.card (Hbar T) = 56448) :
    ∃ (Q : Subgroup (normalizer (T : Set G))) (ψ : DN θ c.hn8 T →* normalizer (T : Set G)),
      Q.map (QuotientGroup.mk' (ON T)) = K1 (iotaN he.mem) ∧ ⁅Q, Q⁆ = Q ∧ Q ⊓ ON T = ⊥ ∧
      (∀ q ∈ Q, ∀ u ∈ ON T, q * u = u * q) ∧
      (∀ a ∈ Q, ∀ x ∈ AltStdSec.zConjSub (zN c hH) Q, a * x = x * a) ∧
      Q ⊓ AltStdSec.zConjSub (zN c hH) Q = ⊥ ∧ (∀ b, ψ b ∈ Q) ∧ Function.Injective ψ ∧
      (∀ b, ψ b * (zN c hH * ψ b * (zN c hH)⁻¹) = b) := by
  have hX := hatData c hH he hsh hcard
  have hDle := Dsub_le_normalizer c hH
  have hCzB : ∀ u ∈ ON T, zN c hH * u * (zN c hH)⁻¹ = u → ∀ b ∈ DN θ c.hn8 T, u * b = b * u := by
    intro u hu hzu b hb
    have hzu' : z * (u : G) * z⁻¹ = u := congrArg Subtype.val hzu
    have hu' : (u : G) ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (u : G) * z = (z * (u : G) * z⁻¹) * z := by rw [hzu']
        _ = z * u := by group
    have hodd : Odd (orderOf (u : G)) := by
      rw [Subgroup.orderOf_coe]
      exact AltStdSec.orderOf_odd_of_mem_oddCore hu
    have hE : ∀ x ∈ E θ c.hn8, (u : G) * x = x * u := fun x hx =>
      (mem_centralizer_iff.1 (oddCoreOf_le_cent c hH (mem_oddCoreOf_of_mem_ON hu)) x
        (hH.n0.E_le hx)).symm
    exact Subtype.ext (comm_Dsub_of_odd c hu' hodd hE _ (mem_subgroupOf.1 hb))
  have hDmap : (DN θ c.hn8 T).map (normalizer (T : Set G)).subtype = Dsub θ c.hn8 := by
    rw [subgroupOf_map_subtype, inf_of_le_left hDle]
  have hBperf : ⁅DN θ c.hn8 T, DN θ c.hn8 T⁆ = DN θ c.hn8 T := by
    apply Subgroup.map_injective (normalizer (T : Set G)).subtype_injective
    rw [map_commutator, hDmap, commutator_Dsub]
  have hBz : ∀ b ∈ DN θ c.hn8 T, zN c hH * b * (zN c hH)⁻¹ = b := by
    intro b hb
    apply Subtype.ext
    have h1 := mem_centralizer_singleton_iff.1 (Dsub_le_cent c (mem_subgroupOf.1 hb))
    show z * (b : G) * z⁻¹ = b
    rw [← h1, mul_inv_cancel_right]
  have hBX : (DN θ c.hn8 T).map (QuotientGroup.mk' (ON T)) ≤ X0 (iotaN he.mem) := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨A, hA⟩ := act_of_mem_Dsub c hH he (mem_subgroupOf.1 hd)
    refine ⟨A, A, fun a b => ?_⟩
    rw [QuotientGroup.mk'_apply, iotaN, iotaN, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hA a b)
  have hBzh : ∀ b ∈ (DN θ c.hn8 T).map (QuotientGroup.mk' (ON T)),
      ((zN c hH : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T) * b *
        ((zN c hH : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T)⁻¹ = b := by
    rintro _ ⟨d, hd, rfl⟩
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hBz d hd]
  have hB := hX.mem_diag_iff hBX hBzh (card_Dhat c hH he)
  set b₀ : normalizer (T : Set G) := ⟨kap θ c.hn8 t01, kap_mem_normalizer c hH t01⟩ with hb₀
  have hb₀B : b₀ ∈ DN θ c.hn8 T := mem_subgroupOf.2 (kap_mem_Dsub θ c.hn8 t01)
  have hb₀2 : b₀ * b₀ = 1 := Subtype.ext (by
    show kap θ c.hn8 t01 * kap θ c.hn8 t01 = 1
    rw [← map_mul, t01_mul_self, map_one])
  have hb₀1 : b₀ ≠ 1 := by
    intro h1
    have h2 : kap θ c.hn8 t01 = kap θ c.hn8 1 := by
      rw [map_one]
      exact congrArg Subtype.val h1
    exact t01_ne_one (kap_injective θ c.hn8 h2)
  have hb₀N : ∀ M : Subgroup (normalizer (T : Set G)),
      (∀ b ∈ DN θ c.hn8 T, ∀ m ∈ M, b * m * b⁻¹ ∈ M) → b₀ ∈ M → DN θ c.hn8 T ≤ M := by
    intro M hM h0
    have hle : Dsub θ c.hn8 ≤ M.map (normalizer (T : Set G)).subtype := by
      refine Dsub_le_of_conj θ c.hn8 (fun d hd m hm => ?_) ⟨b₀, h0, rfl⟩
      obtain ⟨m', hm', rfl⟩ := hm
      exact ⟨⟨d, hDle hd⟩ * m' * ⟨d, hDle hd⟩⁻¹,
        hM _ (mem_subgroupOf.2 hd) _ hm', rfl⟩
    intro x hx
    obtain ⟨m, hm, hmx⟩ := hle (mem_subgroupOf.1 hx)
    rwa [Subtype.ext hmx] at hm
  have hKcov : OddCoversTrivial (K1 (iotaN he.mem)) :=
    oddCoversTrivial_of_sq_not_dvd fun p hp hpo => by
      rw [hX.card_K1]
      exact sq_not_dvd_1344 p hp hpo
  exact exists_wreath_lift_weak' (ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore _)
    (zN_mul_self c hH) hCzB hX.center_K1 hX.commutator_K1 hKcov
    (fun a ha c' hc' => hX.K1_comm_K2 ha (hX.conj_K1 hc')) hBperf hBz hB hb₀B hb₀2 hb₀1 hb₀N

end Inst

section Assembly

variable {G : Type} [Group G] [Finite G] {L Q₀ : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}
  {e : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G}
  (c : Config G L Q₀ n θ z) (hH : HData θ c.hn8 z T)
  (he : PairCoords z T (kap θ c.hn8) (E θ c.hn8) e)
  (hsh : ∀ g ∈ normalizer (T : Set G), ∃ A B : GL (Fin 3) (ZMod 2),
    (∀ a b, g * e a b * g⁻¹ = e (mv A a) (mv B b)) ∨
      (∀ a b, g * e a b * g⁻¹ = e (mv B b) (mv A a)))
  (hcard : Nat.card (Hbar T) = 56448)
  {Q : Subgroup (normalizer (T : Set G))} {ψ : DN θ c.hn8 T →* normalizer (T : Set G)}
  (hQmap : Q.map (QuotientGroup.mk' (ON T)) = K1 (iotaN he.mem)) (hQO : Q ⊓ ON T = ⊥)
  (hQOc : ∀ q ∈ Q, ∀ u ∈ ON T, q * u = u * q)
  (hQQz : ∀ a ∈ Q, ∀ x ∈ AltStdSec.zConjSub (zN c hH) Q, a * x = x * a)
  (hQQzbot : Q ⊓ AltStdSec.zConjSub (zN c hH) Q = ⊥) (hψQ : ∀ b, ψ b ∈ Q)
  (hψinj : Function.Injective ψ) (hψ : ∀ b, ψ b * (zN c hH * ψ b * (zN c hH)⁻¹) = b)

include hH he hsh hcard hQmap hQOc in
theorem mem_K1T_iff (x : G) :
    x ∈ Q.map (normalizer (T : Set G)).subtype ⊓ T ↔ ∃ a, x = e a 0 := by
  have hX := hatData c hH he hsh hcard
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hxT⟩
    obtain ⟨a, b, hab⟩ := he.surj _ hxT
    have hqe : q = eN he.mem a b := Subtype.ext hab.symm
    have hπ : iotaN he.mem a b ∈ K1 (iotaN he.mem) := by
      rw [← hQmap]
      exact ⟨q, hq, by rw [hqe]; rfl⟩
    obtain ⟨a', ha'⟩ := (hX.mem_T1).1 (hX.mem_T1_of_mem_K1 hπ)
    obtain ⟨-, hb⟩ := (hX.eq_iff).1 ha'
    refine ⟨a, ?_⟩
    rw [Subgroup.coe_subtype, hqe, hb]
    rfl
  · rintro ⟨a, rfl⟩
    refine ⟨?_, he.mem a 0⟩
    have hι : iotaN he.mem a 0 ∈ K1 (iotaN he.mem) := hX.T1_le_K1 (hX.iota_mem_T1 a)
    rw [← hQmap] at hι
    obtain ⟨q, hq, hqe⟩ := hι
    have ho : q⁻¹ * eN he.mem a 0 ∈ ON T := (QuotientGroup.eq).1 hqe
    set o := q⁻¹ * eN he.mem a 0 with hodef
    have heq : eN he.mem a 0 = q * o := by rw [hodef]; group
    have hcomm : Commute q o := hQOc q hq o ho
    obtain ⟨k, hk⟩ := AltStdSec.orderOf_odd_of_mem_oddCore ho
    have hsq : eN he.mem a 0 * eN he.mem a 0 = 1 := Subtype.ext (he.sq a 0)
    have h1 : eN he.mem a 0 ^ (2 * k + 1) = eN he.mem a 0 := by
      rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
    have h2 : (q * o) ^ (2 * k + 1) = q ^ (2 * k + 1) := by
      rw [hcomm.mul_pow, ← hk, pow_orderOf_eq_one, mul_one]
    have hmem : eN he.mem a 0 ∈ Q := by
      rw [← h1, heq, h2]
      exact pow_mem hq _
    exact ⟨_, hmem, rfl⟩

include hH he hsh hcard hQmap hQOc in
theorem card_K1T : Nat.card (Q.map (normalizer (T : Set G)).subtype ⊓ T : Subgroup G) = 8 := by
  let f : (Fin 3 → ZMod 2) → (Q.map (normalizer (T : Set G)).subtype ⊓ T : Subgroup G) :=
    fun a => ⟨e a 0, (mem_K1T_iff c hH he hsh hcard hQmap hQOc _).2 ⟨a, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' h
      exact ((he.eq_iff).1 (congrArg Subtype.val h)).1
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := (mem_K1T_iff c hH he hsh hcard hQmap hQOc _).1 hx
      exact ⟨a, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_pi]
  simp

include hH he hsh hcard hQmap hQOc in
theorem mem_conj_K1T_iff (y : G) :
    y ∈ conjSub z (Q.map (normalizer (T : Set G)).subtype ⊓ T) ↔ ∃ b, y = e 0 b := by
  rw [mem_conjSub_iff, mem_K1T_iff c hH he hsh hcard hQmap hQOc]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← he.swap, ← ha]
    group
  · rintro ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    rw [← he.swap b 0]
    group

include hH he hsh hcard hQmap hQOc in
theorem T_eq_sup : T = (Q.map (normalizer (T : Set G)).subtype ⊓ T) ⊔
    conjSub z (Q.map (normalizer (T : Set G)).subtype ⊓ T) := by
  refine le_antisymm (fun t ht => ?_) (sup_le inf_le_right fun y hy => ?_)
  · obtain ⟨a, b, rfl⟩ := he.surj t ht
    rw [he.split]
    exact mul_mem (mem_sup_left ((mem_K1T_iff c hH he hsh hcard hQmap hQOc _).2 ⟨a, rfl⟩))
      (mem_sup_right ((mem_conj_K1T_iff c hH he hsh hcard hQmap hQOc _).2 ⟨b, rfl⟩))
  · obtain ⟨b, rfl⟩ := (mem_conj_K1T_iff c hH he hsh hcard hQmap hQOc _).1 hy
    exact he.mem 0 b

include hH he hsh hcard hQmap hQO in
theorem card_Q : Nat.card Q = 1344 := by
  have hX := hatData c hH he hsh hcard
  have hinj : Function.Injective ((QuotientGroup.mk' (ON T)).comp Q.subtype) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have h1 : (q : normalizer (T : Set G)) ∈ Q ⊓ ON T :=
      mem_inf.2 ⟨q.2, (QuotientGroup.eq_one_iff _).1 hq⟩
    rw [hQO, mem_bot] at h1
    exact Subtype.ext h1
  have hmap : ((QuotientGroup.mk' (ON T)).comp Q.subtype).range = K1 (iotaN he.mem) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hQmap]
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hmap, hX.card_K1]

theorem mem_conj_K1_iff {y : G} :
    y ∈ conjSub z (Q.map (normalizer (T : Set G)).subtype) ↔
      ∃ q ∈ Q, y = zN c hH * q * (zN c hH)⁻¹ := by
  rw [mem_conjSub_iff]
  constructor
  · rintro ⟨q, hq, hqy⟩
    refine ⟨q, hq, ?_⟩
    rw [Subgroup.coe_subtype] at hqy
    show y = z * q * z⁻¹
    rw [hqy]
    group
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q, hq, ?_⟩
    show (q : G) = z⁻¹ * (z * q * z⁻¹) * z
    group

include hQQz in
theorem K1_comm_conj : ∀ a ∈ Q.map (normalizer (T : Set G)).subtype,
    ∀ b ∈ conjSub z (Q.map (normalizer (T : Set G)).subtype), a * b = b * a := by
  rintro _ ⟨q₁, hq₁, rfl⟩ b hb
  obtain ⟨q₂, hq₂, rfl⟩ := (mem_conj_K1_iff c hH).1 hb
  have h1 := hQQz q₁ hq₁ _ (AltStdSec.mem_zConjSub.2 ⟨q₂, hq₂, rfl⟩)
  exact congrArg Subtype.val h1

include hQQzbot in
theorem K1_inf_conj : Q.map (normalizer (T : Set G)).subtype ⊓
    conjSub z (Q.map (normalizer (T : Set G)).subtype) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨q₁, hq₁, rfl⟩, hx⟩
  obtain ⟨q₂, hq₂, hq⟩ := (mem_conj_K1_iff c hH).1 hx
  have h1 : q₁ = zN c hH * q₂ * (zN c hH)⁻¹ := Subtype.ext hq
  have h2 : q₁ ∈ Q ⊓ AltStdSec.zConjSub (zN c hH) Q :=
    mem_inf.2 ⟨hq₁, AltStdSec.mem_zConjSub.2 ⟨q₂, hq₂, h1.symm⟩⟩
  rw [hQQzbot, mem_bot] at h2
  rw [mem_bot, Subgroup.coe_subtype, h2, OneMemClass.coe_one]

@[expose] def kapD (c : Config G L Q₀ n θ z) (hH : HData θ c.hn8 z T) :
    GL (Fin 3) (ZMod 2) →* DN θ c.hn8 T where
  toFun A := ⟨⟨kap θ c.hn8 A, kap_mem_normalizer c hH A⟩,
    mem_subgroupOf.2 (kap_mem_Dsub θ c.hn8 A)⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' A B := Subtype.ext (Subtype.ext (map_mul _ A B))

theorem kapD_injective : Function.Injective (kapD c hH) := by
  intro A B h
  apply kap_injective θ c.hn8
  have h1 := congrArg Subtype.val h
  have h2 := congrArg Subtype.val h1
  exact h2

@[expose] def F1 (c : Config G L Q₀ n θ z) (hH : HData θ c.hn8 z T)
    (ψ : DN θ c.hn8 T →* normalizer (T : Set G)) : Subgroup G :=
  ((ψ.comp (kapD c hH)).range).map (normalizer (T : Set G)).subtype

include hψQ in
theorem F1_le : F1 c hH ψ ≤ Q.map (normalizer (T : Set G)).subtype := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  exact ⟨_, hψQ _, rfl⟩

include hψinj in
theorem card_F1 : Nat.card (F1 c hH ψ) = 168 := by
  have hinj : Function.Injective (ψ.comp (kapD c hH)) := hψinj.comp (kapD_injective c hH)
  rw [F1, card_map_of_injective (normalizer (T : Set G)).subtype_injective,
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3]

include hH he hsh hcard hQmap hQOc hψQ hψ in
theorem F1_inf_T : F1 c hH ψ ⊓ T = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨_, ⟨A, rfl⟩, rfl⟩, hxT⟩
  have hx1 : ((ψ (kapD c hH A) : normalizer (T : Set G)) : G) ∈
      Q.map (normalizer (T : Set G)).subtype ⊓ T := mem_inf.2 ⟨⟨_, hψQ _, rfl⟩, hxT⟩
  obtain ⟨a, ha⟩ := (mem_K1T_iff c hH he hsh hcard hQmap hQOc _).1 hx1
  have h0 := hψ (kapD c hH A)
  have h1 := congrArg Subtype.val h0
  have h2 : kap θ c.hn8 A = e a a := by
    have : ((ψ (kapD c hH A) : normalizer (T : Set G)) : G) *
        (z * ((ψ (kapD c hH A) : normalizer (T : Set G)) : G) * z⁻¹) = kap θ c.hn8 A := h1
    rw [← this, ha, he.swap, ← he.add, add_zero, zero_add]
  have hA : A = 1 := eq_one_of_mv_fix fun a' => by
    have h3 := he.diag A (kap θ c.hn8 A) (kap_mem_normalizer c hH A)
      ⟨1, one_mem _, by rw [one_mul]⟩ a' 0
    rw [h2, he.comm a a a' 0, mul_inv_cancel_right] at h3
    exact ((he.eq_iff).1 h3).1.symm
  subst hA
  rw [map_one, map_one]
  exact one_mem _

include hH he hsh hcard hQmap hQO hQOc hψQ hψinj hψ in
theorem K1T_sup_F1 : (Q.map (normalizer (T : Set G)).subtype ⊓ T) ⊔ F1 c hH ψ =
    Q.map (normalizer (T : Set G)).subtype := by
  set K := Q.map (normalizer (T : Set G)).subtype with hK
  have hKH : K ≤ normalizer (T : Set G) := map_subtype_le Q
  have hFK : F1 c hH ψ ≤ K := F1_le c hH hψQ
  have hnorm : F1 c hH ψ ≤ normalizer ((K ⊓ T : Subgroup G) : Set G) :=
    le_normalizer_of_conj' fun g hg x hx => mem_inf.2
      ⟨mul_mem (mul_mem (hFK hg) (mem_inf.1 hx).1) (inv_mem (hFK hg)),
        (mem_normalizer_iff.1 (hKH (hFK hg)) x).1 (mem_inf.1 hx).2⟩
  have hinf : (K ⊓ T) ⊓ F1 c hH ψ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ F1 c hH ψ ⊓ T := mem_inf.2 ⟨(mem_inf.1 hx).2, (mem_inf.1 (mem_inf.1 hx).1).2⟩
    rwa [F1_inf_T c hH he hsh hcard hQmap hQOc hψQ hψ] at h1
  have hKcard : Nat.card K = 1344 := by
    rw [hK, card_map_of_injective (normalizer (T : Set G)).subtype_injective,
      card_Q c hH he hsh hcard hQmap hQO]
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hFK) ?_
  rw [card_sup_of_inf_eq_bot hnorm hinf, card_K1T c hH he hsh hcard hQmap hQOc,
    card_F1 c hH hψinj, hKcard]

include hH he hsh hcard hQmap hQO hQOc in
theorem cent_K1T : centralizer ((Q.map (normalizer (T : Set G)).subtype ⊓ T : Subgroup G) :
    Set G) ⊓ Q.map (normalizer (T : Set G)).subtype =
      Q.map (normalizer (T : Set G)).subtype ⊓ T := by
  have hX := hatData c hH he hsh hcard
  refine le_antisymm ?_ (le_inf (fun x hx => mem_centralizer_iff.2 fun y hy => ?_) inf_le_left)
  · rintro x ⟨hxc, ⟨q, hq, rfl⟩⟩
    have hπq : ((q : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T) ∈
        K1 (iotaN he.mem) := hQmap ▸ ⟨q, hq, rfl⟩
    have hcomm : ∀ a, ((q : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T) *
        iotaN he.mem a 0 = iotaN he.mem a 0 * (q : normalizer (T : Set G) ⧸ ON T) := by
      intro a
      have h1 := mem_centralizer_iff.1 hxc (e a 0)
        ((mem_K1T_iff c hH he hsh hcard hQmap hQOc _).2 ⟨a, rfl⟩)
      rw [iotaN, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext h1.symm
    obtain ⟨a₀, ha₀⟩ := (hX.mem_T1).1 (hX.mem_T1_of_comm hπq hcomm)
    have he₀ : e a₀ 0 ∈ Q.map (normalizer (T : Set G)).subtype ⊓ T :=
      (mem_K1T_iff c hH he hsh hcard hQmap hQOc _).2 ⟨a₀, rfl⟩
    obtain ⟨q₀, hq₀, hq₀e⟩ := (mem_inf.1 he₀).1
    have hq₀' : q₀ = eN he.mem a₀ 0 := Subtype.ext hq₀e
    have h2 : q₀⁻¹ * q ∈ Q ⊓ ON T := by
      refine mem_inf.2 ⟨mul_mem (inv_mem hq₀) hq, (QuotientGroup.eq).1 ?_⟩
      rw [ha₀, hq₀']
      rfl
    rw [hQO, mem_bot, inv_mul_eq_one] at h2
    rw [← h2]
    have h3 : (q₀ : G) = e a₀ 0 := hq₀e
    show (q₀ : G) ∈ _
    rw [h3]
    exact he₀
  · obtain ⟨a, rfl⟩ := (mem_K1T_iff c hH he hsh hcard hQmap hQOc _).1 hx
    obtain ⟨b, rfl⟩ := (mem_K1T_iff c hH he hsh hcard hQmap hQOc _).1 hy
    exact he.comm b 0 a 0

include hH he hsh hcard hQmap in
theorem normalizer_le : normalizer (T : Set G) ≤
    ((Q.map (normalizer (T : Set G)).subtype ⊔
      conjSub z (Q.map (normalizer (T : Set G)).subtype)) ⊔
        AltStdSec.oddCoreOf (normalizer (T : Set G))) ⊔ zpowers z := by
  have hX := hatData c hH he hsh hcard
  set M := ((Q.map (normalizer (T : Set G)).subtype ⊔
      conjSub z (Q.map (normalizer (T : Set G)).subtype)) ⊔
        AltStdSec.oddCoreOf (normalizer (T : Set G))) ⊔ zpowers z with hM
  have hQM : ∀ q ∈ Q, ((q : normalizer (T : Set G)) : G) ∈ M := fun q hq =>
    mem_sup_left (mem_sup_left (mem_sup_left ⟨q, hq, rfl⟩))
  have hQzM : ∀ q ∈ Q, ((zN c hH * q * (zN c hH)⁻¹ : normalizer (T : Set G)) : G) ∈ M :=
    fun q hq => mem_sup_left (mem_sup_left (mem_sup_right ((mem_conj_K1_iff c hH).2 ⟨q, hq, rfl⟩)))
  have hOM : ∀ o ∈ ON T, ((o : normalizer (T : Set G)) : G) ∈ M := fun o ho =>
    mem_sup_left (mem_sup_right (mem_oddCoreOf_of_mem_ON ho))
  have hzM : z ∈ M := mem_sup_right (mem_zpowers z)
  intro g hg
  suffices h : ∀ gN : normalizer (T : Set G), (gN : G) ∈ M from h ⟨g, hg⟩
  intro gN
  set zh : normalizer (T : Set G) ⧸ ON T :=
    ((zN c hH : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T) with hzh
  obtain ⟨k₁, hk₁, k₂, hk₂, hdec⟩ := hX.exists_decomp (gN : normalizer (T : Set G) ⧸ ON T)
  rw [← hQmap] at hk₁
  obtain ⟨q₁, hq₁, rfl⟩ := hk₁
  have hk₂' := hX.conj_K2 hk₂
  rw [← hQmap] at hk₂'
  obtain ⟨q₂, hq₂, hq₂e⟩ := hk₂'
  have hk₂e : k₂ = ((zN c hH * q₂ * (zN c hH)⁻¹ : normalizer (T : Set G)) :
      normalizer (T : Set G) ⧸ ON T) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h3 : ((q₂ : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T) =
        zh * k₂ * zh⁻¹ := hq₂e
    rw [← hzh, h3]
    have hzz : zh * zh = 1 := hX.zh_sq
    calc k₂ = (zh * zh) * k₂ * (zh * zh)⁻¹ := by rw [hzz, one_mul, inv_one, mul_one]
      _ = zh * (zh * k₂ * zh⁻¹) * zh⁻¹ := by group
  have hwM : ((q₁ * (zN c hH * q₂ * (zN c hH)⁻¹) : normalizer (T : Set G)) : G) ∈ M := by
    rw [Subgroup.coe_mul]
    exact mul_mem (hQM q₁ hq₁) (hQzM q₂ hq₂)
  rcases hdec with hdec | hdec
  · rw [hk₂e, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hdec
    have h4 : gN = (q₁ * (zN c hH * q₂ * (zN c hH)⁻¹)) *
        (gN⁻¹ * (q₁ * (zN c hH * q₂ * (zN c hH)⁻¹)))⁻¹ := by group
    rw [h4, Subgroup.coe_mul]
    exact mul_mem hwM (hOM _ (inv_mem hdec))
  · rw [hk₂e, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hzh, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, QuotientGroup.eq] at hdec
    have h4 : gN = ((zN c hH)⁻¹ * (q₁ * (zN c hH * q₂ * (zN c hH)⁻¹))) *
        (gN⁻¹ * ((zN c hH)⁻¹ * (q₁ * (zN c hH * q₂ * (zN c hH)⁻¹))))⁻¹ := by group
    rw [h4, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (mul_mem (inv_mem hzM) hwM) (hOM _ (inv_mem hdec))

include hH he hsh hcard hQmap hQO hQQz in
theorem sup_inf_oddCore : (Q.map (normalizer (T : Set G)).subtype ⊔
    conjSub z (Q.map (normalizer (T : Set G)).subtype)) ⊓
      AltStdSec.oddCoreOf (normalizer (T : Set G)) = ⊥ := by
  have hX := hatData c hH he hsh hcard
  set K := Q.map (normalizer (T : Set G)).subtype with hK
  have hnorm : conjSub z K ≤ normalizer (K : Set G) :=
    le_normalizer_of_conj' fun y hy x hx => by
      rw [← K1_comm_conj c hH hQQz x hx y hy, mul_inv_cancel_right]
      exact hx
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left K (conjSub z K) hnorm
  rw [eq_bot_iff]
  rintro x ⟨hx, ⟨o, ho, rfl⟩⟩
  have hx' : ((o : normalizer (T : Set G)) : G) ∈ (K : Set G) * (conjSub z K : Set G) := by
    rw [← hm]
    exact hx
  obtain ⟨_, ⟨q₁, hq₁, rfl⟩, b, hb, hab⟩ := Set.mem_mul.1 hx'
  obtain ⟨q₂, hq₂, rfl⟩ := (mem_conj_K1_iff c hH).1 hb
  have heq : q₁ * (zN c hH * q₂ * (zN c hH)⁻¹) = o := Subtype.ext hab
  have hπ1 : ((q₁ : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T) ∈ K1 (iotaN he.mem) :=
    hQmap ▸ ⟨q₁, hq₁, rfl⟩
  have hπ2 : ((q₂ : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T) ∈ K1 (iotaN he.mem) :=
    hQmap ▸ ⟨q₂, hq₂, rfl⟩
  have hπo : ((q₁ * (zN c hH * q₂ * (zN c hH)⁻¹) : normalizer (T : Set G)) :
      normalizer (T : Set G) ⧸ ON T) = 1 := by
    rw [heq]
    exact (QuotientGroup.eq_one_iff _).2 ho
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    at hπo
  have h1 : ((q₁ : normalizer (T : Set G)) : normalizer (T : Set G) ⧸ ON T) ∈
      K1 (iotaN he.mem) ⊓ K2 (iotaN he.mem) := by
    refine mem_inf.2 ⟨hπ1, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hπo]
    exact inv_mem (hX.conj_K1 hπ2)
  rw [hX.K1_inf_K2, mem_bot, QuotientGroup.eq_one_iff] at h1
  have hq₁1 : q₁ = 1 := by
    have := mem_inf.2 ⟨hq₁, h1⟩
    rwa [hQO, mem_bot] at this
  subst hq₁1
  rw [one_mul] at heq
  have hq₂O : q₂ ∈ ON T := by
    have := (inferInstance : (ON T).Normal).conj_mem _ ho (zN c hH)⁻¹
    rwa [← heq, show (zN c hH)⁻¹ * (zN c hH * q₂ * (zN c hH)⁻¹) * (zN c hH)⁻¹⁻¹ = q₂ by group]
      at this
  have hq₂1 : q₂ = 1 := by
    have := mem_inf.2 ⟨hq₂, hq₂O⟩
    rwa [hQO, mem_bot] at this
  subst hq₂1
  rw [mem_bot, ← heq]
  simp

end Assembly

section Main

theorem wreathStruct_of_shape {G : Type} [Group G] [Finite G] {L Q₀ : Subgroup G} {n : ℕ}
    {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}
    {e : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G}
    (c : Config G L Q₀ n θ z) (hH : HData θ c.hn8 z T)
    (he : PairCoords z T (kap θ c.hn8) (E θ c.hn8) e)
    (hsh : ∀ g ∈ normalizer (T : Set G), ∃ A B : GL (Fin 3) (ZMod 2),
      (∀ a b, g * e a b * g⁻¹ = e (mv A a) (mv B b)) ∨
        (∀ a b, g * e a b * g⁻¹ = e (mv B b) (mv A a)))
    (hcard : Nat.card (Hbar T) = 56448) : WreathStruct z T := by
  obtain ⟨Q, ψ, hQmap, -, hQO, hQOc, hQQz, hQQzbot, hψQ, hψinj, hψ⟩ :=
    exists_lift c hH he hsh hcard
  refine ⟨⟨Q.map (normalizer (T : Set G)).subtype, F1 c hH ψ, map_subtype_le Q,
    K1_comm_conj c hH hQQz, K1_inf_conj c hH hQQzbot,
    card_K1T c hH he hsh hcard hQmap hQOc, T_eq_sup c hH he hsh hcard hQmap hQOc,
    (F1_le c hH hψQ).trans le_rfl, ?_, K1T_sup_F1 c hH he hsh hcard hQmap hQO hQOc hψQ hψinj hψ,
    card_F1 c hH hψinj, cent_K1T c hH he hsh hcard hQmap hQO hQOc,
    normalizer_le c hH he hsh hcard hQmap, sup_inf_oddCore c hH he hsh hcard hQmap hQO hQQz⟩⟩
  exact F1_inf_T c hH he hsh hcard hQmap hQOc hψQ hψ

theorem sec4Wreath49_of_shape (hS : ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ) (θ
    : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G), HData θ
    c.hn8 z T → Nat.card (Hbar T) = 56448 → ∃ e : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G,
    PairCoords z T (kap θ c.hn8) (E θ c.hn8) e ∧ ∀ g ∈ normalizer (T : Set G), ∃ A B : GL (Fin 3)
    (ZMod 2), (∀ a b, g * e a b * g⁻¹ = e (mv A a) (mv B b)) ∨ (∀ a b, g * e a b * g⁻¹ = e (mv B b)
    (mv A a))) : Sec4Wreath49 := by
  intro G _ _ L Q n θ z c T hH hcard
  obtain ⟨e, he, hsh⟩ := hS G L Q n θ z c T hH hcard
  exact wreathStruct_of_shape c hH he hsh hcard

end Main

end CFSG.OddStandard.AltStdSmall4.W49
