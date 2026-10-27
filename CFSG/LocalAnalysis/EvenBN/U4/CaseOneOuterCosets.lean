module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneFusion

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo card_sup_mul_card_inf_eq
  mem_normalizer_inf mem_normalizer_sup)
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G]

@[expose] noncomputable def mulConjHom {V : Subgroup G}
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {τ : G} (hτV : τ ∈ normalizer (V : Set G)) :
    V →* V where
  toFun v := ⟨v * (τ * v * τ⁻¹), mul_mem v.2 ((mem_normalizer_iff.1 hτV v).1 v.2)⟩
  map_one' := by ext; simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hb : τ * (a : G) * τ⁻¹ ∈ V := (mem_normalizer_iff.1 hτV a).1 a.2
    have hc : (b : G) * (τ * a * τ⁻¹) = (τ * a * τ⁻¹) * b := hVc _ b.2 _ hb
    calc (a : G) * b * (τ * (a * b) * τ⁻¹) = a * (b * (τ * a * τ⁻¹)) * (τ * b * τ⁻¹) := by
          group
      _ = a * ((τ * a * τ⁻¹) * b) * (τ * b * τ⁻¹) := by rw [hc]
      _ = a * (τ * a * τ⁻¹) * (b * (τ * b * τ⁻¹)) := by group

theorem coe_mulConjHom {V : Subgroup G} (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {τ : G}
    (hτV : τ ∈ normalizer (V : Set G)) (v : V) :
    (mulConjHom hVc hτV v : G) = v * (τ * v * τ⁻¹) := rfl

theorem card_le_card_inf_centralizer_sq [Finite G] {V : Subgroup G} (hV2 : ∀ v ∈ V, v * v = 1)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {τ : G} (hτ : τ * τ = 1)
    (hτV : τ ∈ normalizer (V : Set G)) :
    Nat.card V ≤ Nat.card (V ⊓ centralizer ({τ} : Set G) : Subgroup G) ^ 2 ∧
      (Nat.card V = Nat.card (V ⊓ centralizer ({τ} : Set G) : Subgroup G) ^ 2 →
        ∀ c ∈ V ⊓ centralizer ({τ} : Set G), ∃ v ∈ V, c = v * (τ * v * τ⁻¹)) := by
  set φ := mulConjHom hVc hτV with hφ
  set C := V ⊓ centralizer ({τ} : Set G) with hC
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hker : φ.ker = C.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, mem_subgroupOf, hC, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro hv
      have e : (v : G) * (τ * v * τ⁻¹) = 1 := congrArg Subtype.val hv
      have hvi : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right (hV2 _ v.2)
      have e2 : τ * v * τ⁻¹ = (v : G)⁻¹ := eq_inv_of_mul_eq_one_right e
      refine ⟨v.2, ?_⟩
      rw [hvi] at e2
      calc (v : G) * τ = τ * v * τ⁻¹ * τ := by rw [e2]
        _ = τ * v := by group
    · rintro ⟨-, hv⟩
      apply Subtype.ext
      show (v : G) * (τ * v * τ⁻¹) = 1
      rw [← hv, mul_inv_cancel_right]
      exact hV2 _ v.2
  have hrange : φ.range ≤ C.subgroupOf V := by
    rintro _ ⟨v, rfl⟩
    rw [mem_subgroupOf, coe_mulConjHom, hC, mem_inf, mem_centralizer_singleton_iff]
    refine ⟨mul_mem v.2 ((mem_normalizer_iff.1 hτV v).1 v.2), ?_⟩
    have hb : τ * (v : G) * τ⁻¹ ∈ V := (mem_normalizer_iff.1 hτV v).1 v.2
    have hc := hVc _ v.2 _ hb
    calc (v : G) * (τ * v * τ⁻¹) * τ = v * τ * v := by group
      _ = v * τ⁻¹ * v := by rw [hτi]
      _ = (τ * τ) * v * τ⁻¹ * v := by rw [hτ]; group
      _ = τ * (τ * v * τ⁻¹ * v) := by group
      _ = τ * (v * (τ * v * τ⁻¹)) := by rw [hc]
  have hcardC : Nat.card (C.subgroupOf V) = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul : Nat.card V = Nat.card φ.ker * Nat.card φ.range := by
    calc Nat.card V = Nat.card φ.ker * φ.ker.index := (card_mul_index _).symm
      _ = Nat.card φ.ker * Nat.card φ.range := by rw [index_ker]
  have hrle : Nat.card φ.range ≤ Nat.card C := hcardC ▸ Subgroup.card_le_of_le hrange
  rw [hker, hcardC] at hmul
  refine ⟨?_, fun heq c hc => ?_⟩
  · rw [hmul, sq]
    exact Nat.mul_le_mul_left _ hrle
  · have hpos : 0 < Nat.card C := Nat.card_pos
    have hr : Nat.card φ.range = Nat.card C := by
      rw [hmul, sq] at heq
      exact Nat.eq_of_mul_eq_mul_left hpos heq
    have hreq : φ.range = C.subgroupOf V :=
      Subgroup.eq_of_le_of_card_ge hrange (by rw [hcardC, hr])
    have hcV : (⟨c, (mem_inf.1 hc).1⟩ : V) ∈ C.subgroupOf V := by
      rw [mem_subgroupOf]
      exact hc
    rw [← hreq] at hcV
    obtain ⟨v, hv⟩ := hcV
    exact ⟨v, v.2, (congrArg Subtype.val hv).symm⟩

end Generic

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

theorem card_W_eq_sq_of_card_rootA (hS : Setting h L η t Q T) {u : G} (huu : u * u = 1)
    (hut : u * t = t * u) (huW : u ∈ normalizer ((𝓦 : Subgroup G) : Set G))
    (hroot : Nat.card (miyamotoPull h L η (miyamotoRootA h) ⊓ centralizer ({u} : Set G) :
      Subgroup G) = 2 ^ f) :
    Nat.card (𝓦 : Subgroup G) = Nat.card (𝓦 ⊓ centralizer ({u} : Set G) : Subgroup G) ^ 2 := by
  have hW2 : ∀ w ∈ 𝓦, w * w = 1 := fun w hw => hS.W_mul_self hw
  have hWc : ∀ a ∈ 𝓦, ∀ b ∈ 𝓦, a * b = b * a := fun a ha b hb => hS.W_comm ha hb
  have h1 := (card_le_card_inf_centralizer_sq (V := 𝓦) hW2 hWc huu huW).1
  have htt : t * t = 1 := hS.t_mul_t
  have hti : t⁻¹ = t := hS.t_inv
  have htC : t ∈ normalizer (centralizer ({u} : Set G) : Set G) := by
    refine mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx ⊢
    have hti' : t⁻¹ * u = u * t⁻¹ := by rw [hti]; exact hut.symm
    calc t * x * t⁻¹ * u = t * x * (t⁻¹ * u) := by group
      _ = t * x * (u * t⁻¹) := by rw [hti']
      _ = t * (x * u) * t⁻¹ := by group
      _ = t * (u * x) * t⁻¹ := by rw [hx]
      _ = (t * u) * x * t⁻¹ := by group
      _ = u * (t * x * t⁻¹) := by rw [← hut]; group
  set V : Subgroup G := 𝓦 ⊓ centralizer ({u} : Set G) with hV
  have htV : t ∈ normalizer ((V : Subgroup G) : Set G) :=
    mem_normalizer_inf hS.t_mem_normalizer_W htC
  have h2 := (card_le_card_inf_centralizer_sq (V := V) (fun v hv => hW2 v (mem_inf.1 hv).1)
    (fun a ha b hb => hWc a (mem_inf.1 ha).1 b (mem_inf.1 hb).1) htt htV).1
  have hVt : V ⊓ centralizer ({t} : Set G) =
      miyamotoPull h L η (miyamotoRootA h) ⊓ centralizer ({u} : Set G) := by
    rw [← hS.W_inf_C]
    ext x
    simp only [hV, mem_inf]
    tauto
  rw [hVt, hroot] at h2
  have hWcard := hS.card_W
  refine le_antisymm h1 ?_
  rw [hWcard]
  calc Nat.card V ^ 2 ≤ ((2 ^ f) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = (2 ^ f) ^ 4 := by ring

theorem exists_conj_eq_mul_F1 (hS : Setting h L η t Q T) {u : G} (huu : u * u = 1)
    (huW : u ∈ normalizer ((𝓦 : Subgroup G) : Set G))
    (huF1 : u ∈ normalizer (miyamotoF1G h L η t : Set G))
    (hW : Nat.card (𝓦 : Subgroup G) = Nat.card (𝓦 ⊓ centralizer ({u} : Set G) : Subgroup G) ^ 2)
    {r : G} (hr : r ∈ miyamotoRG h L η t Q) (hx : u * r * (u * r) = 1) :
    ∃ v ∈ 𝓦, ∃ y ∈ miyamotoF1G h L η t, v⁻¹ * (u * r) * v = u * y := by
  have hW2 : ∀ w ∈ 𝓦, w * w = 1 := fun w hw => hS.W_mul_self hw
  have hWc : ∀ a ∈ 𝓦, ∀ b ∈ 𝓦, a * b = b * a := fun a ha b hb => hS.W_comm ha hb
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
  have hwR : w ∈ miyamotoRG h L η t Q := (mem_inf.1 hw).1
  have hRF1 : w ∈ normalizer (miyamotoF1G h L η t : Set G) := hS.RG_le_normalizer_F1 hwR
  have huwW : u * w * u⁻¹ ∈ 𝓦 := (mem_normalizer_iff.1 huW w).1 hw
  have hsq : u * w * (u * w) = 1 := by
    have hmemW : u * w * (u * w) ∈ 𝓦 := by
      rw [show u * w * (u * w) = (u * w * u⁻¹) * w by rw [hui]; group]
      exact mul_mem huwW hw
    have huwN : u * w ∈ normalizer (miyamotoF1G h L η t : Set G) := mul_mem huF1 hRF1
    have hy' : (u * w)⁻¹ * y * (u * w) ∈ miyamotoF1G h L η t := by
      have := (mem_normalizer_iff.1 (inv_mem huwN) y).1 hy
      rwa [inv_inv] at this
    have hmemF : u * w * (u * w) ∈ miyamotoF1G h L η t := by
      have e : u * w * (u * w) = (((u * w)⁻¹ * y * (u * w)) * y)⁻¹ := by
        have e1 : u * (w * y) * (u * (w * y)) = 1 := hx
        calc u * w * (u * w) = u * (w * y) * (u * (w * y)) * (((u * w)⁻¹ * y * (u * w)) * y)⁻¹ :=
              by group
          _ = (((u * w)⁻¹ * y * (u * w)) * y)⁻¹ := by rw [e1, one_mul]
      rw [e]
      exact inv_mem (mul_mem hy' hy)
    have : u * w * (u * w) ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoI1G h L η : Set G) :=
      mem_inf.2 ⟨hmemF, (mem_inf.1 hmemW).2⟩
    rwa [hS.F1_inf_centralizer_I1, mem_bot] at this
  have hwC : w ∈ 𝓦 ⊓ centralizer ({u} : Set G) := by
    refine mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW2 w hw)
    calc w * u = u⁻¹ * (u * w * (u * w)) * w⁻¹ := by group
      _ = u * w := by rw [hsq, hui, hwi]; group
  obtain ⟨v, hv, rfl⟩ := (card_le_card_inf_centralizer_sq (V := 𝓦) hW2 hWc huu huW).2 hW w hwC
  refine ⟨v, hv, v⁻¹ * y * v, ?_, ?_⟩
  · have hvN := hS.RG_le_normalizer_F1 (mem_inf.1 hv).1
    have := (mem_normalizer_iff.1 (inv_mem hvN) y).1 hy
    rwa [inv_inv] at this
  · have hvv : v * v = 1 := hW2 v hv
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    have huvu : u * v * u⁻¹ ∈ 𝓦 := (mem_normalizer_iff.1 huW v).1 hv
    have hc : v * (u * v * u⁻¹) = (u * v * u⁻¹) * v := hWc v hv _ huvu
    rw [hui] at hc
    rw [hui, hvi]
    calc v * (u * (v * (u * v * u) * y)) * v = v * (u * v * u) * (v * u) * y * v := by group
      _ = (u * v * u) * v * (v * u) * y * v := by rw [hc]
      _ = u * v * u * (v * v) * u * y * v := by group
      _ = u * v * (u * u) * y * v := by rw [hvv]; group
      _ = u * (v * y * v) := by rw [huu]; group

theorem exists_conj_eq_of_mem_mul_F1 (hS : Setting h L η t Q T) {u : G} (huu : u * u = 1)
    (huF1 : u ∈ normalizer (miyamotoF1G h L η t : Set G))
    (hF : Nat.card (miyamotoF1G h L η t) =
      Nat.card (miyamotoF1G h L η t ⊓ centralizer ({u} : Set G) : Subgroup G) ^ 2)
    {y : G} (hy : y ∈ miyamotoF1G h L η t) (hx : u * y * (u * y) = 1) :
    ∃ v ∈ miyamotoF1G h L η t, v⁻¹ * (u * y) * v = u := by
  have hF2 : ∀ w ∈ miyamotoF1G h L η t, w * w = 1 := hS.F1_mul_self
  have hFc : ∀ a ∈ miyamotoF1G h L η t, ∀ b ∈ miyamotoF1G h L η t, a * b = b * a :=
    fun a ha b hb => hS.F1_comm ha hb
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hyC : y ∈ miyamotoF1G h L η t ⊓ centralizer ({u} : Set G) := by
    refine mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 ?_⟩
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hF2 y hy)
    calc y * u = u⁻¹ * (u * y * (u * y)) * y⁻¹ := by group
      _ = u * y := by rw [hx, hui, hyi]; group
  obtain ⟨v, hv, rfl⟩ := (card_le_card_inf_centralizer_sq (V := miyamotoF1G h L η t) hF2 hFc huu
    huF1).2 hF y hyC
  refine ⟨v, hv, ?_⟩
  have hvv : v * v = 1 := hF2 v hv
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have huvu : u * v * u⁻¹ ∈ miyamotoF1G h L η t := (mem_normalizer_iff.1 huF1 v).1 hv
  have hc : v * (u * v * u⁻¹) = (u * v * u⁻¹) * v := hFc v hv _ huvu
  rw [hui] at hc
  rw [hui, hvi]
  calc v * (u * (v * (u * v * u))) * v = v * (u * v * u) * (v * u) * v := by group
    _ = (u * v * u) * v * (v * u) * v := by rw [hc]
    _ = u * v * u * (v * v) * u * v := by group
    _ = u * v * (u * u) * v := by rw [hvv]; group
    _ = u := by rw [huu, mul_one, mul_assoc, hvv, mul_one]

theorem sup_zpowers_of_mem_mul_F1 (hS : Setting h L η t Q T) {u : G}
    (hu : u ∉ miyamotoF1G h L η t) {y : G} (hy : y ∈ miyamotoF1G h L η t)
    (hx : u * y * (u * y) = 1) :
    (miyamotoF1G h L η t ⊓ centralizer ({u} : Set G)) ⊔ zpowers (u * y) ≤
        centralizer ({u * y} : Set G) ∧
      CFSG.IsElementaryAbelian 2
        ((miyamotoF1G h L η t ⊓ centralizer ({u} : Set G)) ⊔ zpowers (u * y) : Subgroup G) ∧
      Nat.card ((miyamotoF1G h L η t ⊓ centralizer ({u} : Set G)) ⊔ zpowers (u * y) :
        Subgroup G) =
        2 * Nat.card (miyamotoF1G h L η t ⊓ centralizer ({u} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := miyamotoF1G h L η t ⊓ centralizer ({u} : Set G) with hC
  set x := u * y with hxdef
  have hxC : ∀ c ∈ C, c * x = x * c := by
    intro c hc
    obtain ⟨hcF, hcu⟩ := mem_inf.1 hc
    have h1 : c * u = u * c := mem_centralizer_singleton_iff.1 hcu
    calc c * x = (c * u) * y := by rw [hxdef]; group
      _ = u * (c * y) := by rw [h1]; group
      _ = u * (y * c) := by rw [hS.F1_comm hcF hy]
      _ = x * c := by rw [hxdef]; group
  have hx1 : x ≠ 1 := fun e => hu (by
    have : u = y⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [this]
    exact inv_mem hy)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx) hx1
  have hzx : zpowers x ≤ normalizer (C : Set G) := by
    rw [zpowers_le]
    exact mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2 fun c hc => hxC c hc)
  have hcard := card_sup_mul_card_inf_eq hzx
  have hinf : C ⊓ zpowers x = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    obtain ⟨hzC, hzx'⟩ := mem_inf.1 hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hzx'
    have hpow : x ^ k = 1 ∨ x ^ k = x := by
      have e := zpow_mod_orderOf x k
      rw [hxo] at e
      rcases Int.emod_two_eq_zero_or_one k with hk | hk
      · left
        rw [← e]
        push_cast
        rw [hk, zpow_zero]
      · right
        rw [← e]
        push_cast
        rw [hk, zpow_one]
    rcases hpow with h1 | h1
    · rw [h1]; exact one_mem _
    · exfalso
      rw [h1] at hzC
      apply hu
      have := mul_mem (mem_inf.1 hzC).1 (inv_mem hy)
      rwa [hxdef, mul_inv_cancel_right] at this
  rw [hinf, card_bot, mul_one, Nat.card_zpowers, hxo] at hcard
  refine ⟨sup_le (fun c hc => mem_centralizer_singleton_iff.2 (hxC c hc)) ?_,
    GMS.isElementaryAbelian_of_mul_self fun z hz => ?_, by rw [hcard, mul_comm]⟩
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl
  · obtain ⟨c, hc, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
        exact ((Commute.zpow_right (show Commute a x from hxC a ha) k)).eq) hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    have hcc : c * c = 1 := hS.F1_mul_self c (mem_inf.1 hc).1
    have hcx : Commute c (x ^ k) := Commute.zpow_right (hxC c hc) k
    have hxx : x ^ k * x ^ k = 1 := by
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hx, one_zpow]
    calc c * x ^ k * (c * x ^ k) = (c * c) * (x ^ k * x ^ k) := by
          rw [show c * x ^ k * (c * x ^ k) = c * (x ^ k * c) * x ^ k by group, ← hcx.eq]
          group
      _ = 1 := by rw [hcc, hxx, one_mul]

theorem conj_t_ne_of_card_lt (hS : Setting h L η t Q T) {u : G}
    (hu : u ∉ miyamotoF1G h L η t)
    (hlt : (2 ^ f) ^ 4 <
      Nat.card (miyamotoF1G h L η t ⊓ centralizer ({u} : Set G) : Subgroup G))
    {y : G} (hy : y ∈ miyamotoF1G h L η t) (g : G) : g * t * g⁻¹ ≠ u * y := by
  intro e
  have hx : u * y * (u * y) = 1 := by
    rw [← e, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, hS.t_mul_t]
    group
  obtain ⟨hXC, hXe, hXcard⟩ := hS.sup_zpowers_of_mem_mul_F1 hu hy hx
  have := hS.card_le_of_le_centralizer_conj g (by rw [e]; exact hXC) hXe
  omega


theorem conj_t_ne_of_preserves (hS : Setting h L η t Q T) {k : Type} [Field k]
    {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)} {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψα : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    {u : G} (huu : u * u = 1) (hu : u ∉ miyamotoF1G h L η t)
    (hX1 : ∀ x ∈ prodFactorOne ψ, u * x * u⁻¹ ∈ prodFactorOne ψ)
    (hX2 : ∀ x ∈ prodFactorTwo ψ, u * x * u⁻¹ ∈ prodFactorTwo ψ)
    {n : G} (hn : n ∈ miyamotoN1G h L η) (hnu : u * n = n * u) (hno : orderOf n = 2 ^ f + 1)
    (hcard : Nat.card (miyamotoF1G h L η t ⊓ centralizer ({u} : Set G) : Subgroup G) =
      (2 ^ f) ^ 4) (g : G) : g * t * g⁻¹ ≠ u := by
  intro e
  have hx : u * 1 * (u * 1) = 1 := by rw [mul_one, huu]
  obtain ⟨hXC, hXe, hXcard⟩ := hS.sup_zpowers_of_mem_mul_F1 hu (one_mem _) hx
  rw [mul_one] at hXC hXe hXcard
  set C := miyamotoF1G h L η t ⊓ centralizer ({u} : Set G) with hC
  set X := C ⊔ zpowers u with hX
  rw [hcard] at hXcard
  have hnM : n ∈ miyamotoM1G h L η t := hS.sec3_12_one.2.2.1 hn
  set a := α ⟨n, hn⟩ with ha
  have hψn : ψ ⟨n, hnM⟩ = (a, a) := hψα ⟨n, hn⟩ ⟨n, hnM⟩ rfl
  set d₁ : G := ((ψ.symm (a, 1) : miyamotoM1G h L η t) : G) with hd₁
  set d₂ : G := ((ψ.symm (1, a) : miyamotoM1G h L η t) : G) with hd₂
  have hd₁X : d₁ ∈ prodFactorOne ψ := Common.symm_inl_mem_prodFactorOne ψ a
  have hd₂X : d₂ ∈ prodFactorTwo ψ := Common.symm_inr_mem_prodFactorTwo ψ a
  have hn12 : n = d₁ * d₂ := by
    have : (⟨n, hnM⟩ : miyamotoM1G h L η t) = ψ.symm (a, 1) * ψ.symm (1, a) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, ← hψn, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val this
  have hinf := Common.prodFactorOne_inf_prodFactorTwo ψ
  have hcomm12 : ∀ x ∈ prodFactorOne ψ, ∀ y ∈ prodFactorTwo ψ, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.1 (Common.prodFactorTwo_le_centralizer ψ hy) x hx)
  have hfix : u * d₁ * u⁻¹ = d₁ ∧ u * d₂ * u⁻¹ = d₂ := by
    have e1 : (u * d₁ * u⁻¹) * (u * d₂ * u⁻¹) = d₁ * d₂ := by
      rw [← hn12, show u * d₁ * u⁻¹ * (u * d₂ * u⁻¹) = u * (d₁ * d₂) * u⁻¹ by group, ← hn12,
        hnu, mul_inv_cancel_right]
    have hm : d₁⁻¹ * (u * d₁ * u⁻¹) ∈ prodFactorOne ψ ⊓ prodFactorTwo ψ := by
      refine mem_inf.2 ⟨mul_mem (inv_mem hd₁X) (hX1 d₁ hd₁X), ?_⟩
      have : d₁⁻¹ * (u * d₁ * u⁻¹) = d₂ * (u * d₂ * u⁻¹)⁻¹ := by
        calc d₁⁻¹ * (u * d₁ * u⁻¹) = d₁⁻¹ * ((u * d₁ * u⁻¹) * (u * d₂ * u⁻¹)) *
              (u * d₂ * u⁻¹)⁻¹ := by group
          _ = d₂ * (u * d₂ * u⁻¹)⁻¹ := by rw [e1]; group
      rw [this]
      exact mul_mem hd₂X (inv_mem (hX2 d₂ hd₂X))
    rw [hinf, mem_bot] at hm
    have h1 : u * d₁ * u⁻¹ = d₁ := (eq_of_inv_mul_eq_one hm).symm
    refine ⟨h1, ?_⟩
    rw [h1] at e1
    exact mul_left_cancel e1
  have hcu : ∀ d : G, u * d * u⁻¹ = d → d * u = u * d := fun d hd => by
    calc d * u = (u * d * u⁻¹) * u := by rw [hd]
      _ = u * d := by group
  have hordA : orderOf a = 2 ^ f + 1 := by
    rw [ha, MulEquiv.orderOf_eq, ← hno]
    exact Subgroup.orderOf_mk n hn
  have hord : ∀ p : SL(2, k) × SL(2, k), orderOf p = 2 ^ f + 1 →
      orderOf ((ψ.symm p : miyamotoM1G h L η t) : G) = 2 ^ f + 1 := fun p hp => by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hp]
  have hord1 : orderOf d₁ = 2 ^ f + 1 := hord _ (by rw [Prod.orderOf_mk, orderOf_one,
    Nat.lcm_one_right, hordA])
  have hord2 : orderOf d₂ = 2 ^ f + 1 := hord _ (by rw [Prod.orderOf_mk, orderOf_one,
    Nat.lcm_one_left, hordA])
  set Y := zpowers d₁ ⊔ zpowers d₂ with hY
  have hYN : zpowers d₂ ≤ normalizer (zpowers d₁ : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2 fun z hz => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hz
    exact ((Commute.zpow_left (hcomm12 d₁ hd₁X d₂ hd₂X) j)).eq
  have hYinf : zpowers d₁ ⊓ zpowers d₂ = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have h1 : z ∈ prodFactorOne ψ := (zpowers_le.2 hd₁X) (mem_inf.1 hz).1
    have h2 : z ∈ prodFactorTwo ψ := (zpowers_le.2 hd₂X) (mem_inf.1 hz).2
    rw [← hinf]
    exact mem_inf.2 ⟨h1, h2⟩
  have hYcard : Nat.card Y = (2 ^ f + 1) ^ 2 := by
    have := card_sup_mul_card_inf_eq hYN
    rw [hYinf, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hord1, hord2] at this
    rw [hY, this, sq]
  have hd₁u := hcu d₁ hfix.1
  have hd₂u := hcu d₂ hfix.2
  have hYC : Y ≤ centralizer ({u} : Set G) := sup_le
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 hd₁u))
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 hd₂u))
  have hNX : ∀ d : G, d ∈ miyamotoM1G h L η t → d * u = u * d →
      d ∈ normalizer ((X : Subgroup G) : Set G) := by
    intro d hdM hdu
    have hdC : d ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 hdu
    refine mem_normalizer_sup (mem_normalizer_inf (hS.M1_le_normalizer_F1 hdM)
      (le_normalizer hdC)) (mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2
        fun z hz => ?_))
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hz
    exact ((Commute.zpow_left (show Commute u d from hdu.symm) j)).eq
  have hYX : Y ≤ normalizer ((X : Subgroup G) : Set G) := sup_le
    (zpowers_le.2 (hNX d₁ (ψ.symm (a, 1)).2 hd₁u)) (zpowers_le.2 (hNX d₂ (ψ.symm (1, a)).2 hd₂u))
  exact hS.not_sq_dvd_card_of_le_normalizer_of_conj g (by rw [e]; exact hXC) hXe hXcard
    (by rw [e]; exact hYC) hYX (by rw [hYcard])

theorem conj_t_ne_mul_of_outer (hS : Setting h L η t Q T) {k : Type} [Field k]
    {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)} {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψα : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    {u : G} (huu : u * u = 1) (hut : u * t = t * u)
    (huW : u ∈ normalizer ((𝓦 : Subgroup G) : Set G))
    (huF1 : u ∈ normalizer (miyamotoF1G h L η t : Set G)) (hu : u ∉ miyamotoF1G h L η t)
    (hroot : Nat.card (miyamotoPull h L η (miyamotoRootA h) ⊓ centralizer ({u} : Set G) :
      Subgroup G) = 2 ^ f)
    (hcase : (2 ^ f) ^ 4 <
        Nat.card (miyamotoF1G h L η t ⊓ centralizer ({u} : Set G) : Subgroup G) ∨
      ((∀ x ∈ prodFactorOne ψ, u * x * u⁻¹ ∈ prodFactorOne ψ) ∧
        (∀ x ∈ prodFactorTwo ψ, u * x * u⁻¹ ∈ prodFactorTwo ψ) ∧
        ∃ n ∈ miyamotoN1G h L η, u * n = n * u ∧ orderOf n = 2 ^ f + 1))
    {r : G} (hr : r ∈ miyamotoRG h L η t Q) (g : G) : g⁻¹ * t * g ≠ u * r := by
  intro e
  have hx : u * r * (u * r) = 1 := by
    rw [← e, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, hS.t_mul_t]
    group
  have hW := hS.card_W_eq_sq_of_card_rootA huu hut huW hroot
  obtain ⟨v, -, y, hy, hvx⟩ := hS.exists_conj_eq_mul_F1 huu huW huF1 hW hr hx
  set g' := (g * v)⁻¹ with hg'
  have e' : g' * t * g'⁻¹ = u * y := by
    rw [hg', inv_inv, ← hvx, ← e]
    group
  have hF2 : ∀ w ∈ miyamotoF1G h L η t, w * w = 1 := hS.F1_mul_self
  have hFc : ∀ a ∈ miyamotoF1G h L η t, ∀ b ∈ miyamotoF1G h L η t, a * b = b * a :=
    fun a ha b hb => hS.F1_comm ha hb
  have hlow := (card_le_card_inf_centralizer_sq (V := miyamotoF1G h L η t) hF2 hFc huu huF1).1
  rw [hS.card_F1] at hlow
  set c := Nat.card (miyamotoF1G h L η t ⊓ centralizer ({u} : Set G) : Subgroup G) with hc
  by_cases hlt : (2 ^ f) ^ 4 < c
  · exact hS.conj_t_ne_of_card_lt hu hlt hy g' e'
  · have hceq : c = (2 ^ f) ^ 4 := by
      refine le_antisymm (not_lt.1 hlt) ?_
      by_contra hc'
      push Not at hc'
      have : c ^ 2 < ((2 ^ f) ^ 4) ^ 2 := Nat.pow_lt_pow_left hc' two_ne_zero
      have e2 : ((2 ^ f) ^ 4) ^ 2 = (2 ^ f) ^ 8 := by ring
      omega
    rcases hcase with hc1 | ⟨hX1, hX2, n, hn, hnu, hno⟩
    · exact absurd hc1 hlt
    have hF : Nat.card (miyamotoF1G h L η t) = c ^ 2 := by
      rw [hS.card_F1, hceq]
      ring
    have hyx : u * y * (u * y) = 1 := by
      rw [← e', show g' * t * g'⁻¹ * (g' * t * g'⁻¹) = g' * (t * t) * g'⁻¹ by group, hS.t_mul_t]
      group
    obtain ⟨m, -, hm⟩ := hS.exists_conj_eq_of_mem_mul_F1 huu huF1 hF hy hyx
    apply hS.conj_t_ne_of_preserves hψα huu hu hX1 hX2 hn hnu hno hceq (m⁻¹ * g')
    rw [← hm, ← e']
    group

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
