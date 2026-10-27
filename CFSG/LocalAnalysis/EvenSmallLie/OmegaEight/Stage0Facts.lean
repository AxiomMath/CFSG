module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Defs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SplitC
open CFSG.EvenSmallLie.OmegaEight.CPrime

variable {G : Type} [Group G] {t : G} {L : Subgroup G}

theorem sup_zpowers_mul_eq {K : Subgroup G} {x m : G} (hm : m ∈ K) :
    K ⊔ zpowers (x * m) = K ⊔ zpowers x := by
  apply le_antisymm
  · exact sup_le le_sup_left
      (zpowers_le.2 (mul_mem (mem_sup_right (mem_zpowers x)) (mem_sup_left hm)))
  · refine sup_le le_sup_left (zpowers_le.2 ?_)
    have h1 : x * m * m⁻¹ ∈ K ⊔ zpowers (x * m) :=
      mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (inv_mem hm))
    simpa using h1

theorem not_square_of_shapeSplit {H₀ : Subgroup G} (hS : ShapeSplit t L H₀) (x : G) :
    x * x ≠ t := by
  intro hx
  have hxC : x ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hx]
    group
  rw [hS.centralizer_eq] at hxC
  obtain ⟨u, hu, rfl | rfl⟩ := (hS.mem_sup_iff le_rfl).1 hxC
  · exact hS.not_mem (hx ▸ mul_mem hu hu)
  · apply hS.not_mem
    have hc := hS.commute_of_mem hu
    have e : u * t * (u * t) = u * u := by
      calc u * t * (u * t) = u * (t * u) * t := by group
        _ = u * (u * t) * t := by rw [hc]
        _ = u * u * (t * t) := by group
        _ = u * u := by rw [hS.mul_self, mul_one]
    rw [← hx, e]
    exact mul_mem hu hu

theorem zpow_eq_one_or_eq {b : G} (hb : b * b = 1) (n : ℤ) : b ^ n = 1 ∨ b ^ n = b := by
  by_cases hb1 : b = 1
  · left
    rw [hb1, one_zpow]
  · have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb) hb1
    rw [← zpow_mod_orderOf, hbo]
    rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [Nat.cast_ofNat, h]
    · exact Or.inl (zpow_zero b)
    · exact Or.inr (zpow_one b)

theorem mem_normalizer_of_mul_self {U : Subgroup G} {b : G} (hb : b * b = 1)
    (hbU : ∀ u ∈ U, b * u * b⁻¹ ∈ U) : b ∈ normalizer (U : Set G) := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  refine mem_normalizer_iff.2 fun u => ⟨fun hu => hbU u hu, fun hu => ?_⟩
  have e : b * (b * u * b⁻¹) * b⁻¹ = u := by
    rw [hbinv]
    calc b * (b * u * b) * b = b * b * u * (b * b) := by group
      _ = u := by rw [hb, one_mul, mul_one]
  rw [← e]
  exact hbU _ hu

theorem isPGroup_sup_zpowers {U : Subgroup G} (hU : IsPGroup 2 U) {b : G} (hb : b * b = 1)
    (hbU : ∀ u ∈ U, b * u * b⁻¹ ∈ U) : IsPGroup 2 (U ⊔ zpowers b : Subgroup G) := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rintro ⟨x, hx⟩
  obtain ⟨u, hu, n, rfl⟩ := (mem_sup_zpowers_iff (mem_normalizer_of_mul_self hb hbU)).1 hx
  have hsq : (u * b ^ n) * (u * b ^ n) ∈ U := by
    rcases zpow_eq_one_or_eq hb n with h | h <;> rw [h]
    · rw [mul_one]
      exact mul_mem hu hu
    · have e : u * b * (u * b) = u * (b * u * b⁻¹) := by
        rw [hbinv]
        simp only [mul_assoc]
      rw [e]
      exact mul_mem hu (hbU u hu)
  obtain ⟨k, hk⟩ := hU ⟨_, hsq⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' : ((u * b ^ n) * (u * b ^ n)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  change (u * b ^ n) ^ 2 ^ (k + 1) = 1
  rw [pow_succ', pow_mul, sq]
  exact hk'

theorem card_sup_zpowers {U : Subgroup G} {b : G} (hb : b * b = 1)
    (hbU : ∀ u ∈ U, b * u * b⁻¹ ∈ U) (hbn : b ∉ U) :
    Nat.card (U ⊔ zpowers b : Subgroup G) = 2 * Nat.card U := by
  have h2 : U.relIndex (U ⊔ zpowers b) = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨b, mem_sup_right (mem_zpowers b), fun x hx => ?_⟩
    obtain ⟨u, hu, n, rfl⟩ := (mem_sup_zpowers_iff (mem_normalizer_of_mul_self hb hbU)).1 hx
    rcases zpow_eq_one_or_eq hb n with h | h <;> rw [h]
    · rw [mul_one]
      exact Or.inr ⟨hu, fun h' => hbn (by simpa using mul_mem (inv_mem hu) h')⟩
    · rw [mul_assoc, hb, mul_one]
      exact Or.inl ⟨hu, fun h' => hbn (by simpa using mul_mem (inv_mem hu) h')⟩
  rw [← Subgroup.relIndex_mul_card (H := U) (K := U ⊔ zpowers b), h2,
    inf_of_le_left le_sup_left]

theorem card_eq_of_max [Finite G] {L U : Subgroup G} (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) (hU2 : IsPGroup 2 U)
    {n m : ℕ} (hL : Nat.card L = 2 ^ n * m) (hm : Odd m) : Nat.card U = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2' : IsPGroup 2 (U.subgroupOf L) := hU2.of_equiv (subgroupOfEquivOfLe hUL).symm
  obtain ⟨S, hS⟩ := hU2'.exists_le_sylow
  have hSmap : (S : Subgroup L).map L.subtype = U :=
    hUmax _ (map_subtype_le _) (S.isPGroup'.map _) fun x hx => ⟨⟨x, hUL hx⟩, hS hx, rfl⟩
  have hcardS : Nat.card S = Nat.card U := by
    rw [← hSmap, card_map_of_injective L.subtype_injective]
  have h1 : 2 ^ n ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (by rw [hL]; exact Dvd.intro m rfl)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hU2
  have h2 : 2 ^ k ∣ 2 ^ n * m := hk ▸ hL ▸ card_dvd_of_le hUL
  have h3 : 2 ^ k ∣ 2 ^ n :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)) h2
  rw [hk] at hcardS ⊢
  exact Nat.dvd_antisymm h3 (hcardS ▸ h1)

theorem mem_of_isPGroup_of_odd {K M V : Subgroup G} (hn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hodd : Odd (K.relIndex M)) (hV : IsPGroup 2 V) {x : G} (hxV : x ∈ V) (hxM : x ∈ M) :
    x ∈ K := by
  obtain ⟨k, hk⟩ := hV ⟨x, hxV⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine mem_of_coprime_relIndex hn hxM ?_
  exact (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)).coprime_dvd_right
    (orderOf_dvd_of_pow_eq_one hk')

namespace StepK

variable (hK : StepK t L)
include hK

theorem shapeC_mul_right {b m : G} (hS : ShapeC t L b) (hm : m ∈ L)
    (hc : b * m * (b * m) ∈ centralizer (L : Set G)) : ShapeC t L (b * m) := by
  have hsq : b * m * (b * m) = 1 := by
    rw [hK.mul_sq_eq hS.b_mem (by rw [hS.b_sq]; exact one_mem _) hm hc, hS.b_sq]
  refine ⟨?_, mul_mem hS.b_mem (hK.le_centralizer hm), hsq, fun h => hS.b_not_mem ?_,
    hS.relIndex_eq⟩
  · rw [sup_zpowers_mul_eq hm]
    exact hS.split
  · simpa using mul_mem h (mem_sup_left (inv_mem hm) : m⁻¹ ∈ L ⊔ zpowers t)

theorem shapeD_mul_right {b r m : G} (hS : ShapeD t L b r) (hm : m ∈ L)
    (hc : b * m * (b * m) ∈ centralizer (L : Set G)) : ShapeD t L (b * m) r := by
  have hsq : b * m * (b * m) = 1 := by
    rw [hK.mul_sq_eq hS.b_mem (by rw [hS.b_sq]; exact one_mem _) hm hc, hS.b_sq]
  refine ⟨?_, mul_mem hS.b_mem (hK.le_centralizer hm), hsq, fun h => hS.b_not_mem ?_,
    hS.r_mem, hS.r_not_mem, hS.r_pow, hS.r_order, hS.normal, hS.relIndex_sup, hS.relIndex_eq⟩
  · rw [sup_zpowers_mul_eq (mem_sup_left hm : m ∈ L ⊔ zpowers r)]
    exact hS.split
  · simpa using mul_mem h (mem_sup_left (inv_mem hm) : m⁻¹ ∈ L ⊔ zpowers t)

theorem shapeC'_mul_right {c m : G} (hS : ShapeC' t L c) (hm : m ∈ L)
    (hc : c * m * (c * m) ∈ centralizer (L : Set G)) : ShapeC' t L (c * m) := by
  have hP := hS.cprime
  have hsq : c * m * (c * m) = t := by
    rw [hK.mul_sq_eq hP.c_mem_centralizer (by rw [hP.sq]; exact mem_zpowers t) hm hc, hP.sq]
  refine ⟨⟨hP.orderOf_eq, hsq, hP.not_mem, hP.le_centralizer, hP.involution_mem,
    hP.not_mem_closure_odd⟩, mul_mem hS.c_mem_normalizer (Subgroup.le_normalizer hm), ?_,
    fun h => hS.c_not_mem ?_, hS.relIndex_eq⟩
  · rw [sup_zpowers_mul_eq hm]
    exact hS.centralizer_eq
  · simpa using mul_mem h (mem_sup_left (inv_mem hm) : m⁻¹ ∈ L ⊔ zpowers t)

theorem shapeD'_mul_right {c r m : G} (hS : ShapeD' t L c r) (hm : m ∈ L)
    (hc : c * m * (c * m) ∈ centralizer (L : Set G)) : ShapeD' t L (c * m) r := by
  have hP := hS.cprime
  have hsq : c * m * (c * m) = t := by
    rw [hK.mul_sq_eq hP.c_mem_centralizer (by rw [hP.sq]; exact mem_zpowers t) hm hc, hP.sq]
  have hmK : m ∈ L ⊔ zpowers r := mem_sup_left hm
  refine ⟨⟨hP.orderOf_eq, hsq, hP.not_mem, hP.le_centralizer, hP.involution_mem,
    hP.not_mem_closure_odd⟩, fun h => hS.c_not_mem ?_, hS.r_mem, hS.r_not_mem, hS.r_pow,
    hS.r_order, hS.le_centralizer, hS.t_not_mem,
    mul_mem hS.c_mem_normalizer (Subgroup.le_normalizer hmK), ?_, hS.odd, hS.le_normalizer,
    hS.relIndex_sup, hS.relIndex_eq⟩
  · simpa using mul_mem h (mem_sup_left (inv_mem hm) : m⁻¹ ∈ L ⊔ zpowers t)
  · rw [sup_zpowers_mul_eq hmK]
    exact hS.centralizer_eq

theorem eq_sup_of_le_sup {U : Subgroup G} (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U)
    {V : Subgroup G} (hVN : V ≤ L ⊔ zpowers t) (hV : IsPGroup 2 V) (hUV : U ⊔ zpowers t ≤ V) :
    V = U ⊔ zpowers t := by
  refine le_antisymm (fun x hx => ?_) hUV
  have h1 : V ⊓ L = U :=
    hUmax _ inf_le_right (hV.to_le inf_le_left) (le_inf (le_sup_left.trans hUV) hUL)
  have htV : t ∈ V := hUV (mem_sup_right (mem_zpowers t))
  obtain ⟨l, hl, rfl | rfl⟩ := hK.mem_sup_iff.1 (hVN hx)
  · exact mem_sup_left (by rw [← h1]; exact ⟨hx, hl⟩)
  · have hlV : l ∈ V := by simpa using V.mul_mem hx (V.inv_mem htV)
    exact mul_mem (mem_sup_left (by rw [← h1]; exact ⟨hlV, hl⟩)) (mem_sup_right (mem_zpowers t))

omit hK in
theorem card_sup_zpowers_of_le {U : Subgroup G} (hUL : U ≤ L) {b : G} (hb : b * b = 1)
    (hbN : b ∉ L ⊔ zpowers t) (hbU : ∀ u ∈ U, b * u * b⁻¹ ∈ U) :
    Nat.card (U ⊔ zpowers b : Subgroup G) = 2 * Nat.card U :=
  card_sup_zpowers hb hbU fun h => hbN (mem_sup_left (hUL h))

theorem shapeB_sylow {r : G} (hS : ShapeB t L r) {U : Subgroup G} (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) :
    ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V →
      U ⊔ zpowers t ≤ V → V = U ⊔ zpowers t := fun V hVH hV hUV =>
  hK.eq_sup_of_le_sup hUL hUmax (fun x hx => mem_of_isPGroup_of_odd
    (fun m hm y hy => hK.conj_mem_sup hm hy) (by rw [hS.relIndex_eq]; decide) hV hx (hVH hx))
    hV hUV

theorem eq_sup_sup_of_le {U : Subgroup G} (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) {b : G}
    {V : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ⊔ zpowers b ⊔ zpowers t ≤ V)
    (hout : ∀ x ∈ V, x ∉ L ⊔ zpowers t → x * b⁻¹ ∈ L ⊔ zpowers t) :
    V = U ⊔ zpowers b ⊔ zpowers t := by
  have hbV : b ∈ V := hUV (mem_sup_left (mem_sup_right (mem_zpowers b)))
  have hle : U ⊔ zpowers t ≤ U ⊔ zpowers b ⊔ zpowers t :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have h1 : V ⊓ (L ⊔ zpowers t) = U ⊔ zpowers t :=
    hK.eq_sup_of_le_sup hUL hUmax inf_le_right (hV.to_le inf_le_left)
      (le_inf (hle.trans hUV) (sup_le (hUL.trans le_sup_left) le_sup_right))
  refine le_antisymm (fun x hx => ?_) hUV
  by_cases hxN : x ∈ L ⊔ zpowers t
  · have hx' : x ∈ U ⊔ zpowers t := by
      rw [← h1]
      exact ⟨hx, hxN⟩
    exact hle hx'
  · have hy : x * b⁻¹ ∈ U ⊔ zpowers t := by
      rw [← h1]
      exact ⟨V.mul_mem hx (V.inv_mem hbV), hout x hx hxN⟩
    have h2 := mul_mem (hle hy) (mem_sup_left (mem_sup_right (mem_zpowers b)) :
      b ∈ U ⊔ zpowers b ⊔ zpowers t)
    simpa using h2

theorem shapeC_sylow {b : G} (hS : ShapeC t L b) {U : Subgroup G} (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) :
    ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V →
      U ⊔ zpowers b ⊔ zpowers t ≤ V → V = U ⊔ zpowers b ⊔ zpowers t := by
  intro V hVH hV hUV
  refine hK.eq_sup_sup_of_le hUL hUmax hV hUV fun x hx hxN => ?_
  exact mul_mem_of_not_mem_of_relIndex_eq_two hS.relIndex_eq (hVH hx) (inv_mem hS.b_mem) hxN
    (fun h => hS.b_not_mem (by simpa using inv_mem h))

theorem shapeD_sylow {b r : G} (hS : ShapeD t L b r) {U : Subgroup G} (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) :
    ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V →
      U ⊔ zpowers b ⊔ zpowers t ≤ V → V = U ⊔ zpowers b ⊔ zpowers t := by
  intro V hVH hV hUV
  have hK'H : L ⊔ zpowers t ⊔ zpowers r ≤ centralizer ({t} : Set G) :=
    sup_le hK.sup_le_centralizer (zpowers_le.2 hS.r_mem)
  have h3 : (L ⊔ zpowers t).relIndex (L ⊔ zpowers t ⊔ zpowers r) = 3 := by
    have h := relIndex_mul_relIndex (L ⊔ zpowers t) _ _ le_sup_left hK'H
    rw [hS.relIndex_sup, hS.relIndex_eq] at h
    omega
  have h2K : ∀ x ∈ V, x ∈ L ⊔ zpowers t ⊔ zpowers r → x ∈ L ⊔ zpowers t := fun x hxV hxK =>
    mem_of_isPGroup_of_odd (fun m hm k hk => hK.conj_mem_sup (hK'H hm) hk)
      (by rw [h3]; decide) hV hxV hxK
  have hbV : b ∈ V := hUV (mem_sup_left (mem_sup_right (mem_zpowers b)))
  have hbK' : b ∉ L ⊔ zpowers t ⊔ zpowers r := fun h => hS.b_not_mem (h2K b hbV h)
  refine hK.eq_sup_sup_of_le hUL hUmax hV hUV fun x hx hxN => ?_
  have hy := mul_mem_of_not_mem_of_relIndex_eq_two hS.relIndex_sup (hVH hx) (inv_mem hS.b_mem)
    (fun h => hxN (h2K x hx h)) (fun h => hbK' (by simpa using inv_mem h))
  exact h2K _ (mul_mem hx (inv_mem hbV)) hy

theorem shapeB_shapeAB {r : G} (hS : ShapeB t L r) {U Q P : Subgroup G} (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U)
    (hQL : Q ≤ L) (hP : P = L ⊓ normalizer (Q : Set G))
    (hQ : ∀ l ∈ L, (∀ q ∈ Q, l * q = q * l) → l ∈ Q)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hNQ : ∀ x ∈ centralizer ({t} : Set G),
      x ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) → x ∈ L ⊔ zpowers t) :
    ShapeAB t L U Q P := by
  have htC : t ∈ centralizer (Q : Set G) :=
    mem_centralizer_iff.2 fun q hq => hK.commute_of_mem (hQL hq)
  have htQ : t ∈ normalizer (Q : Set G) := centralizer_le_normalizer _ htC
  have hEL : (Q ⊔ zpowers t : Subgroup G) ⊓ L = Q := by
    refine le_antisymm (fun x ⟨hxE, hxL⟩ => ?_) (le_inf le_sup_left hQL)
    obtain ⟨q, hq, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => by
        rcases hK.mem_zpowers_iff.1 hb with rfl | rfl
        · rw [mul_one, one_mul]
        · exact hK.commute_of_mem (hQL ha)) hxE
    rcases hK.mem_zpowers_iff.1 hz with rfl | rfl
    · rwa [mul_one]
    · exact absurd (by simpa using L.mul_mem (L.inv_mem (hQL hq)) hxL) hK.not_mem
  refine ⟨hK.orderOf_eq, hK.not_mem, hK.le_centralizer, hS.split.not_mem_closure_odd,
    not_square_of_shapeSplit hS.split, hK.shapeB_sylow hS hUL hUmax, ?_, ?_⟩
  · apply le_antisymm
    · rintro x ⟨hxC, hxN⟩
      have hxL : x ∈ normalizer (L : Set G) := hK.le_normalizer hxC
      have hxQ : x ∈ normalizer (Q : Set G) := mem_normalizer_iff.2 fun y => by
        rw [← hEL]
        change y ∈ (Q ⊔ zpowers t : Subgroup G) ∧ y ∈ L ↔
          x * y * x⁻¹ ∈ (Q ⊔ zpowers t : Subgroup G) ∧ x * y * x⁻¹ ∈ L
        rw [← mem_normalizer_iff.1 hxN y, ← mem_normalizer_iff.1 hxL y]
      obtain ⟨l, hl, rfl | rfl⟩ := hK.mem_sup_iff.1 (hNQ x hxC hxN)
      · exact mem_sup_left (hP ▸ ⟨hl, hxQ⟩)
      · have hlQ : l ∈ normalizer (Q : Set G) := by
          simpa using mul_mem hxQ (inv_mem htQ)
        exact mul_mem (mem_sup_left (hP ▸ ⟨hl, hlQ⟩)) (mem_sup_right (mem_zpowers t))
    · refine sup_le (fun x hx => ?_) (zpowers_le.2 ⟨mem_centralizer_singleton_iff.2 rfl,
        mem_normalizer_sup htQ (Subgroup.le_normalizer (mem_zpowers t))⟩)
      rw [hP] at hx
      exact ⟨hK.le_centralizer hx.1,
        mem_normalizer_sup hx.2 (mem_normalizer_zpowers (hK.commute_of_mem hx.1))⟩
  · apply le_antisymm
    · rintro x ⟨hxC, hxQ⟩
      have hxE : x ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
        mem_normalizer_sup (centralizer_le_normalizer _ hxQ)
          (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 hxC))
      obtain ⟨l, hl, h | h⟩ := hK.mem_sup_iff.1 (hNQ x hxC hxE) <;> rw [h] at hxQ ⊢
      · exact mem_sup_left (hQ l hl fun q hq => (mem_centralizer_iff.1 hxQ q hq).symm)
      · have hlQ : l ∈ centralizer (Q : Set G) := by
          simpa using Subgroup.mul_mem _ hxQ (Subgroup.inv_mem _ htC)
        exact mul_mem (mem_sup_left (hQ l hl fun q hq => (mem_centralizer_iff.1 hlQ q hq).symm))
          (mem_sup_right (mem_zpowers t))
    · exact sup_le (fun x hx => ⟨hK.le_centralizer (hQL hx),
        mem_centralizer_iff.2 fun y hy => hQab y hy x hx⟩)
        (zpowers_le.2 ⟨mem_centralizer_singleton_iff.2 rfl, htC⟩)

end StepK

end CFSG.EvenSmallLie.OmegaEight.Stage0
