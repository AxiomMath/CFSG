module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSylow
public import CFSG.Monster.B.Recog.GenericTransferExtremal

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Stage1

variable {G : Type*} [Group G]

@[expose] def InvFix (U Q : Subgroup G) : Prop :=
  ∀ h ∈ U, h ∉ Q → h * h ∈ Q → Nat.card (Q ⊓ centralizer ({h} : Set G) : Subgroup G) = 16

@[expose] def AbelBound (t : G) : Prop :=
  ∀ B : Subgroup G, B ≤ centralizer ({t} : Set G) → IsPGroup 2 B →
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → Nat.card B ≤ 128

@[expose] def sqFix {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h : G) :
    Subgroup G where
  carrier := {x | x ∈ A ∧ x * x * h = h * (x * x)}
  one_mem' := ⟨one_mem A, by simp⟩
  mul_mem' {x y} hx hy := by
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    have hxy := hA x hx.1 y hy.1
    have e : x * y * (x * y) = x * x * (y * y) := by
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = x * x * (y * y) := by group
    rw [e, mul_assoc, hy.2, ← mul_assoc, hx.2, mul_assoc]
  inv_mem' {x} hx := by
    refine ⟨inv_mem hx.1, ?_⟩
    rw [show x⁻¹ * x⁻¹ = (x * x)⁻¹ by group]
    calc (x * x)⁻¹ * h = (x * x)⁻¹ * (h * (x * x)) * (x * x)⁻¹ := by group
      _ = (x * x)⁻¹ * (x * x * h) * (x * x)⁻¹ := by rw [hx.2]
      _ = h * (x * x)⁻¹ := by group

section FixBound

variable [Finite G] {Q : Subgroup G} (hQ : Nat.card Q = 64) (hQ2 : ∀ q ∈ Q, q * q = 1)
include hQ hQ2

theorem card_fix_step {k : ℕ} {A : Subgroup G} (hL : Level Q k A) {h : G}
    (hhA : ∀ a ∈ A, h * a * h⁻¹ ∈ A) (hinv : ∀ a ∈ A, h * (h * a * h⁻¹) * h⁻¹ = a)
    (hhQ : Nat.card (Q ⊓ centralizer ({h} : Set G) : Subgroup G) ≤ 16) :
    4 * Nat.card (pw A 2 ⊓ centralizer ({h} : Set G) : Subgroup G) ≤
      Nat.card (A ⊓ centralizer ({h} : Set G) : Subgroup G) := by
  set X := sqFix hL.comm h
  have hXA : ∀ x ∈ X, x ∈ A := fun x hx => hx.1
  have hsq : ∀ x ∈ X, ∀ y ∈ X, (x * y) * (x * y) = (x * x) * (y * y) := by
    intro x hx y hy
    have hxy := hL.comm x hx.1 y hy.1
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = x * x * (y * y) := by group
  let sqX : X →* G :=
    { toFun := fun x => (x : G) * x
      map_one' := by simp
      map_mul' := fun x y => hsq x x.2 y y.2 }
  have hrange : sqX.range = pw A 2 ⊓ centralizer ({h} : Set G) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, mem_centralizer_singleton_iff.2 x.2.2⟩
      show (x : G) * x ∈ pw A 2
      rw [← sq]
      exact pow_mem_pw x.2.1 2
    · rintro ⟨hy1, hy2⟩
      obtain ⟨x, hx, rfl⟩ := (mem_pw hL.comm).1 hy1
      refine ⟨⟨x, hx, ?_⟩, by simp [sqX, sq]⟩
      rw [← sq]
      exact mem_centralizer_singleton_iff.1 hy2
  have hQX : Q ≤ X := fun q hq => ⟨hL.Q_le hq, by rw [hQ2 q hq, one_mul, mul_one]⟩
  have hker : sqX.ker = Q.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact ⟨fun h1 => hL.mem_Q x x.2.1 h1, fun hq => hQ2 x hq⟩
  have hcardX : Nat.card X = 64 * Nat.card (pw A 2 ⊓ centralizer ({h} : Set G) : Subgroup G) := by
    have := card_mul_index sqX.ker
    rw [index_ker, hker, hrange, Nat.card_congr (subgroupOfEquivOfLe hQX).toEquiv, hQ] at this
    exact this.symm
  have hδmul : ∀ x ∈ X, ∀ y ∈ X,
      (x * y)⁻¹ * (h * (x * y) * h⁻¹) = (x⁻¹ * (h * x * h⁻¹)) * (y⁻¹ * (h * y * h⁻¹)) := by
    intro x hx y hy
    have ha : x⁻¹ * (h * x * h⁻¹) ∈ A := mul_mem (inv_mem hx.1) (hhA x hx.1)
    have hc := hL.comm y⁻¹ (inv_mem hy.1) _ ha
    calc (x * y)⁻¹ * (h * (x * y) * h⁻¹) = y⁻¹ * (x⁻¹ * (h * x * h⁻¹)) * (h * y * h⁻¹) := by
          group
      _ = (x⁻¹ * (h * x * h⁻¹)) * y⁻¹ * (h * y * h⁻¹) := by rw [hc]
      _ = (x⁻¹ * (h * x * h⁻¹)) * (y⁻¹ * (h * y * h⁻¹)) := by group
  let δ : X →* G :=
    { toFun := fun x => (x : G)⁻¹ * (h * x * h⁻¹)
      map_one' := by simp
      map_mul' := fun x y => hδmul x x.2 y y.2 }
  have hfixX : A ⊓ centralizer ({h} : Set G) ≤ X := fun x hx => by
    refine ⟨hx.1, ?_⟩
    have := mem_centralizer_singleton_iff.1 hx.2
    rw [mul_assoc, this, ← mul_assoc, this, mul_assoc]
  have hδker : δ.ker = (A ⊓ centralizer ({h} : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change (x : G)⁻¹ * (h * x * h⁻¹) = 1 ↔ _
    constructor
    · intro h1
      have h2 : h * x * h⁻¹ = x := by
        have := congrArg ((x : G) * ·) h1
        simpa using this
      refine ⟨x.2.1, mem_centralizer_singleton_iff.2 ?_⟩
      calc (x : G) * h = h * x * h⁻¹ * h := by rw [h2]
        _ = h * x := by group
    · rintro ⟨-, h2⟩
      have := mem_centralizer_singleton_iff.1 h2
      rw [← this]
      group
  have hδrange : δ.range ≤ Q ⊓ centralizer ({h} : Set G) := by
    rintro _ ⟨x, rfl⟩
    have hx := x.2
    have hxA := hx.1
    have hd : (x : G)⁻¹ * (h * x * h⁻¹) ∈ A := mul_mem (inv_mem hxA) (hhA x hxA)
    have hd2 : ((x : G)⁻¹ * (h * x * h⁻¹)) * ((x : G)⁻¹ * (h * x * h⁻¹)) = 1 := by
      have hc := hL.comm _ (hhA x hxA) _ (inv_mem hxA)
      have e : ((x : G)⁻¹ * (h * x * h⁻¹)) * ((x : G)⁻¹ * (h * x * h⁻¹)) =
          ((x : G) * x)⁻¹ * (h * (x * x) * h⁻¹) := by
        calc ((x : G)⁻¹ * (h * x * h⁻¹)) * ((x : G)⁻¹ * (h * x * h⁻¹))
            = (x : G)⁻¹ * ((h * x * h⁻¹) * (x : G)⁻¹) * (h * x * h⁻¹) := by group
          _ = (x : G)⁻¹ * ((x : G)⁻¹ * (h * x * h⁻¹)) * (h * x * h⁻¹) := by rw [hc]
          _ = ((x : G) * x)⁻¹ * (h * (x * x) * h⁻¹) := by group
      rw [e, ← hx.2, mul_inv_cancel_right, inv_mul_cancel]
    refine ⟨hL.mem_Q _ hd hd2, mem_centralizer_singleton_iff.2 ?_⟩
    have hdinv : ((x : G)⁻¹ * (h * x * h⁻¹))⁻¹ = (x : G)⁻¹ * (h * x * h⁻¹) :=
      inv_eq_of_mul_eq_one_right hd2
    have e : h * ((x : G)⁻¹ * (h * x * h⁻¹)) * h⁻¹ = ((x : G)⁻¹ * (h * x * h⁻¹))⁻¹ := by
      calc h * ((x : G)⁻¹ * (h * x * h⁻¹)) * h⁻¹ = (h * x * h⁻¹)⁻¹ * (h * (h * x * h⁻¹) * h⁻¹) :=
            by group
        _ = (h * x * h⁻¹)⁻¹ * x := by rw [hinv x hxA]
        _ = ((x : G)⁻¹ * (h * x * h⁻¹))⁻¹ := by group
    rw [hdinv] at e
    calc (x : G)⁻¹ * (h * x * h⁻¹) * h = h * ((x : G)⁻¹ * (h * x * h⁻¹)) * h⁻¹ * h := by rw [e]
      _ = h * ((x : G)⁻¹ * (h * x * h⁻¹)) := by group
  have h1 := card_mul_index δ.ker
  rw [index_ker, hδker, Nat.card_congr (subgroupOfEquivOfLe hfixX).toEquiv] at h1
  have h2 : Nat.card δ.range ≤ 16 := (card_le_of_le hδrange).trans hhQ
  have h3 : Nat.card X ≤ Nat.card (A ⊓ centralizer ({h} : Set G) : Subgroup G) * 16 := by
    rw [← h1]
    exact Nat.mul_le_mul_left _ h2
  omega

theorem card_fix_ge {h : G} (hhQ : Nat.card (Q ⊓ centralizer ({h} : Set G) : Subgroup G) = 16) :
    ∀ k, 1 ≤ k → ∀ A : Subgroup G, Level Q k A → (∀ a ∈ A, h * a * h⁻¹ ∈ A) →
      (∀ a ∈ A, h * (h * a * h⁻¹) * h⁻¹ = a) →
      16 * 4 ^ (k - 1) ≤ Nat.card (A ⊓ centralizer ({h} : Set G) : Subgroup G) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro A hL _ _
    have hAQ : Q = A := eq_of_le_of_card_ge hL.Q_le (by rw [hL.card_eq, hQ]; norm_num)
    rw [← hAQ, hhQ]
    norm_num
  | succ k hk ih =>
    intro A hL hhA hinv
    have hL' : Level Q k (pw A 2) := by
      have := hL.pw_two hQ hQ2 (by omega)
      rwa [Nat.add_sub_cancel] at this
    have hhA' : ∀ a ∈ pw A 2, h * a * h⁻¹ ∈ pw A 2 := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := (mem_pw hL.comm).1 ha
      rw [← conj_pow]
      exact pow_mem_pw (hhA b hb) 2
    have hinv' : ∀ a ∈ pw A 2, h * (h * a * h⁻¹) * h⁻¹ = a := fun a ha => hinv a (pw_le A 2 ha)
    have h1 := ih (pw A 2) hL' hhA' hinv'
    have h2 := card_fix_step hQ hQ2 hL hhA hinv hhQ.le
    rw [Nat.add_sub_cancel]
    have e : 16 * 4 ^ k = 4 * (16 * 4 ^ (k - 1)) := by
      rw [show k = (k - 1) + 1 by omega, pow_succ, Nat.add_sub_cancel]; ring
    rw [e]
    exact (Nat.mul_le_mul_left 4 h1).trans h2

end FixBound

theorem mem_of_index_two [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} (hK : K.index = 2) (g : G) : g ∈ K := by
  have := normal_of_index_eq_two hK
  have := hG
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · exfalso
    rw [h, index_bot] at hK
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isCyclic_of_prime_card (p := 2) hK
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (IsCyclic.commGroup.mul_comm x y)
  · rw [h]; exact mem_top g

namespace Config

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  {k : ℕ} {A : Subgroup G} (hS : Setup ε t L U Q P a ψ p) (hC : Config t Q P k A)
include hS hC

theorem U_le_normalizer [Finite G] : U ≤ normalizer (A : Set G) := fun u hu =>
  mem_normalizer_of_conj_mem (hC.P_norm u (hS.rad.U_le_P hu))

theorem t_not_mem_AU [Finite G] : t ∉ A ⊔ U := by
  intro ht
  obtain ⟨c, hc, u, hu, hcu⟩ := exists_mul_of_mem_sup_normalizer (hC.U_le_normalizer hS) ht
  have hut := hS.shape.commute_of_mem (hS.rad.U_le_L hu)
  have hc' : c = t * u⁻¹ := by rw [hcu]; group
  have hct : c * t = t * c := by
    have hut' : u⁻¹ * t = t * u⁻¹ := Commute.inv_left hut
    rw [hc', mul_assoc, hut', ← mul_assoc]
  have hcQ := (hC.commute_iff hS hc).1 hct
  exact hS.shape.not_mem (hcu ▸ mul_mem (hS.rad.Q_le_L hcQ) (hS.rad.U_le_L hu))

theorem relIndex_AU [Finite G] : (A ⊔ U).relIndex (A ⊔ (U ⊔ zpowers t)) = 2 := by
  have htn := hC.t_not_mem_AU hS
  rw [relIndex_eq_two_iff]
  refine ⟨t, mem_sup_right (mem_sup_right (mem_zpowers t)), fun b hb => ?_⟩
  obtain ⟨c, hc, u, hu, hbe | hbe⟩ := hC.mem_T hS hb
  · have hbM : b ∈ A ⊔ U := hbe ▸ mul_mem (mem_sup_left hc) (mem_sup_right hu)
    refine Or.inr ⟨hbM, fun h => htn ?_⟩
    simpa using mul_mem (inv_mem hbM) h
  · have hbM : b * t ∈ A ⊔ U := by
      rw [hbe, mul_assoc, hS.shape.mul_self, mul_one]
      exact mul_mem (mem_sup_left hc) (mem_sup_right hu)
    refine Or.inl ⟨hbM, fun h => htn ?_⟩
    simpa using mul_mem (inv_mem h) hbM

theorem exists_conj_mem_AU [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hT : Terminal t P k A) :
    ∃ g : G, g * t * g⁻¹ ∈ A ⊔ U ∧
      Odd ((A ⊔ (U ⊔ zpowers t) : Subgroup G).relIndex (centralizer {g * t * g⁻¹})) := by
  let T : Sylow 2 G := ⟨A ⊔ (U ⊔ zpowers t), hC.isPGroup_T hS,
    fun hV hle => hC.seitz_sylow hS hT hV hle⟩
  have ht2 : t ^ 2 = 1 := by rw [sq]; exact hS.shape.mul_self
  exact CFSG.Monster.B.Recog.exists_conj_mem_odd_relIndex_of_transfer T (hC.relIndex_AU hS) ht2
    (fun K hK => mem_of_index_two hG hnab hK t)

end Config

theorem two_mul_card_le [Finite G] {t : G} (hAb : AbelBound t) (ht2 : t * t = 1) {g : G}
    {D : Subgroup G} (hD2 : IsPGroup 2 D) (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDu : ∀ d ∈ D, d * (g * t * g⁻¹) = (g * t * g⁻¹) * d) (huD : g * t * g⁻¹ ∉ D) :
    2 * Nat.card D ≤ 128 := by
  set u := g * t * g⁻¹ with hu
  have hu2 : u * u = 1 := by
    have e : g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    rw [hu, e, ht2, mul_one, mul_inv_cancel]
  have hcomm : ∀ d ∈ D, ∀ z ∈ zpowers u, d * z = z * d := by
    intro d hd z hz
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (hDu d hd) n)
  set B : Subgroup G := D ⊔ zpowers u
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    Stage1.sup_comm_of hDc (fun x hx y hy => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
      rw [← zpow_add, ← zpow_add, add_comm]) hcomm hx hy
  have hu2' : IsPGroup 2 (zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hu2)
    have h2 : orderOf u ≠ 1 := by
      rw [Ne, orderOf_eq_one_iff]
      intro h1'
      exact huD (h1' ▸ one_mem D)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd h h2
    · exact h
  have hB2 : IsPGroup 2 B := IsPGroup.to_sup_of_normal_left' hD2 hu2'
    (zpowers_le.2 (mem_normalizer_of_conj_mem fun d hd => by
      rw [← hDu d hd, mul_inv_cancel_right]; exact hd))
  have hlt : D < B := lt_of_le_of_ne le_sup_left fun h => huD (h ▸ mem_sup_right (mem_zpowers u))
  have hcard : 2 * Nat.card D ≤ Nat.card B := by
    obtain ⟨m, hm⟩ := card_dvd_of_le hlt.le
    have hne : Nat.card D ≠ Nat.card B := fun h => hlt.ne (eq_of_le_of_card_ge hlt.le h.ge)
    have hpos : 0 < Nat.card D := Nat.card_pos
    rcases m with _ | _ | m
    · simp at hm; exact absurd hm (Nat.card_pos.ne')
    · simp only [zero_add, mul_one] at hm; exact absurd hm.symm hne
    · rw [hm]; nlinarith
  set B' := B.map (MulAut.conj g⁻¹).toMonoidHom
  have hB'le : B' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hxu : x * u = u * x := hBc x hx u (mem_sup_right (mem_zpowers u))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hu] at hxu
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * x) * g := by rw [hxu]
      _ = t * (g⁻¹ * x * g) := by group
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (x * y) * g⁻¹⁻¹ by group, hBc x hx y hy]
    group
  have h := hAb B' hB'le (hB2.map _) hB'c
  rw [card_map_of_injective (MulAut.conj g⁻¹).injective] at h
  omega

namespace Config

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  {k : ℕ} {A : Subgroup G} (hS : Setup ε t L U Q P a ψ p) (hC : Config t Q P k A)
include hS hC

theorem conj_decomp [Finite G] {g : G} (hg : g * t * g⁻¹ ∈ A ⊔ U) :
    ∃ b ∈ A, ∃ h ∈ U, g * t * g⁻¹ = b * h ∧ h ∉ Q ∧ h * h ∈ Q := by
  obtain ⟨b, hb, h, hh, hbh⟩ := exists_mul_of_mem_sup_normalizer (hC.U_le_normalizer hS) hg
  have hu2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, hS.shape.mul_self]
    group
  have huA : g * t * g⁻¹ ∉ A := fun huA =>
    (hS.shape.conj_not_mem hS.rad.odd g) (hS.rad.Q_le_L (hC.level.mem_Q _ huA hu2))
  refine ⟨b, hb, h, hh, hbh, fun hq => huA (hbh ▸ mul_mem hb (hC.level.Q_le hq)), ?_⟩
  have e : h * h = (b * (h * b * h⁻¹))⁻¹ := by
    have h1 : b * h * (b * h) = 1 := hbh ▸ hu2
    calc h * h = (b * (h * b * h⁻¹))⁻¹ * (b * h * (b * h)) := by group
      _ = (b * (h * b * h⁻¹))⁻¹ := by rw [h1, mul_one]
  have hA' : h * h ∈ A := e ▸ inv_mem (mul_mem hb (hC.P_norm h (hS.rad.U_le_P hh) b hb))
  have hht := hS.shape.commute_of_mem (hS.rad.U_le_L hh)
  have hC' : h * h * t = t * (h * h) := by rw [mul_assoc, hht, ← mul_assoc, hht, mul_assoc]
  exact (hC.commute_iff hS hA').1 hC'

theorem conj_not_mem_A (g : G) : g * t * g⁻¹ ∉ A := by
  intro huA
  have hu2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, hS.shape.mul_self]
    group
  exact (hS.shape.conj_not_mem hS.rad.odd g) (hS.rad.Q_le_L (hC.level.mem_Q _ huA hu2))

theorem false_of_terminal_high [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hT : Terminal t P k A) (hk : 3 ≤ k) (hF3 : InvFix U Q)
    (hAb : AbelBound t) : False := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  obtain ⟨g, hgM, -⟩ := hC.exists_conj_mem_AU hS hG hnab hT
  obtain ⟨b, hb, h, hh, hbh, hhQ, hh2⟩ := hC.conj_decomp hS hgM
  have hhA : ∀ x ∈ A, h * x * h⁻¹ ∈ A := hC.P_norm h (hS.rad.U_le_P hh)
  have hinv : ∀ x ∈ A, h * (h * x * h⁻¹) * h⁻¹ = x := by
    intro x hx
    have hc := hC.level.comm _ (hC.level.Q_le hh2) x hx
    calc h * (h * x * h⁻¹) * h⁻¹ = (h * h) * x * (h * h)⁻¹ := by group
      _ = x := by rw [hc, mul_inv_cancel_right]
  have hfix := card_fix_ge hQ hQ2 (hF3 h hh hhQ hh2) k (by omega) A hC.level hhA hinv
  have hDu : ∀ d ∈ A ⊓ centralizer ({h} : Set G), d * (g * t * g⁻¹) = (g * t * g⁻¹) * d := by
    intro d hd
    rw [hbh]
    have h1 := hC.level.comm d hd.1 b hb
    have h2 := mem_centralizer_singleton_iff.1 hd.2
    calc d * (b * h) = b * (d * h) := by rw [← mul_assoc, h1, mul_assoc]
      _ = b * h * d := by rw [h2, mul_assoc]
  have huD : g * t * g⁻¹ ∉ A ⊓ centralizer ({h} : Set G) := fun hu =>
    hC.conj_not_mem_A hS g hu.1
  have h1 := two_mul_card_le hAb hS.shape.mul_self (hC.isPGroup_A.to_le inf_le_left)
    (fun x hx y hy => hC.level.comm x hx.1 y hy.1) hDu huD
  have h16 : 16 * 4 ^ 2 ≤ 16 * 4 ^ (k - 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
