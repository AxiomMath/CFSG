module

public import CFSG.GH74.GLS.C3.Layer1.P34Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin
open scoped Pointwise

variable {X : Type} [Group X]

theorem exists_central_of_normal [Finite X] {W N : Subgroup X} (hW : IsPGroup 2 ↥W) (hNW : N ≤ W)
    (hN : ∀ w ∈ W, ∀ n ∈ N, w * n * w⁻¹ ∈ N) (hne : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 1 ∧ ∀ w ∈ W, w * n = n * w := by
  have : Group.IsNilpotent ↥W := hW.isNilpotent
  let H : Subgroup ↥W := N.subgroupOf W
  have hHn : H.Normal := ⟨fun n hn g => by
    have := hN (g : X) g.2 (n : X) (Subgroup.mem_subgroupOf.mp hn)
    rw [Subgroup.mem_subgroupOf]
    simpa using this⟩
  have hH : H ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro n hn
    have : (⟨n, hNW hn⟩ : ↥W) ∈ H := hn
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  have hK := Group.IsNilpotent.inf_center_ne_bot_of_normal hH
  obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK
  have hnmem : (n : ↥W) ∈ H ⊓ center ↥W := n.2
  refine ⟨((n : ↥W) : X), hnmem.1, fun h1 => hn1 (Subtype.ext (Subtype.ext h1)), fun w hw => ?_⟩
  have := Subgroup.mem_center_iff.mp hnmem.2 ⟨w, hw⟩
  exact congrArg Subtype.val this

theorem commute_of_inf_bot {W A B : Subgroup X} (hAW : A ≤ W) (hBW : B ≤ W)
    (hA : ∀ w ∈ W, ∀ a ∈ A, w * a * w⁻¹ ∈ A) (hB : ∀ w ∈ W, ∀ b ∈ B, w * b * w⁻¹ ∈ B)
    (hAB : A ⊓ B = ⊥) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ B := by
    have := B.mul_mem (hB a (hAW ha) b hb) (B.inv_mem hb)
    simpa [mul_assoc] using this
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have := A.mul_mem ha (hA b (hBW hb) a⁻¹ (A.inv_mem ha))
    simpa [mul_assoc] using this
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := ⟨h2, h1⟩
  rw [hAB, Subgroup.mem_bot] at h3
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

theorem card_conjSubgroup (A : Subgroup X) (e : X) :
    Nat.card ↥(conjSubgroup A e) = Nat.card ↥A := by
  unfold conjSubgroup
  exact Subgroup.card_map_of_injective (MulAut.conj e⁻¹).injective

theorem card_mul_of_inf_bot [Finite X] {A B : Subgroup X} (h : A ⊓ B = ⊥) :
    Nat.card ↥((A : Set X) * (B : Set X)) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set X)
  rw [h1, mul_comm]
  congr 1
  have hinj : Set.InjOn ((↑) : X → X ⧸ B) (A : Set X) := by
    intro a ha a' ha' he
    have : a⁻¹ * a' ∈ B := QuotientGroup.eq.1 he
    have h2 : a⁻¹ * a' ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha) ha', this⟩
    rw [h, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.1 h2
  rw [Nat.card_image_of_injOn hinj]
  rfl

theorem zpow_involution_cases {u : X} (hu : u * u = 1) (k : ℤ) : u ^ k = 1 ∨ u ^ k = u := by
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  have hk : u ^ k = u ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, hu2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hk, h]; simp
  · right; rw [hk, h]; simp

variable {T : Subgroup X}

theorem mem_T0 {t : X} (ht : t ∈ T) (h2 : t * t = 1) : t ∈ T0 T :=
  subset_closure ⟨ht, h2⟩

theorem T0_le : T0 T ≤ T := (closure_le T).2 fun _ ht => ht.1

theorem conj_mem_T0 {g : X} (hg : g ∈ T) {a : X} (ha : a ∈ T0 T) : g⁻¹ * a * g ∈ T0 T := by
  induction ha using Subgroup.closure_induction with
  | mem t ht =>
    refine subset_closure ⟨T.mul_mem (T.mul_mem (T.inv_mem hg) ht.1) hg, ?_⟩
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht.2]; group
  | one => simp
  | mul a b _ _ ha hb =>
    have : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
    rw [this]; exact (T0 T).mul_mem ha hb
  | inv a _ ha =>
    have : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
    rw [this]; exact (T0 T).inv_mem ha

theorem conj_mem_T0_of_normalizer {e : X} (he : e ∈ normalizer (T0 T : Set X)) {a : X}
    (ha : a ∈ T0 T) : e⁻¹ * a * e ∈ T0 T := by
  have hiff := Subgroup.mem_normalizer_iff.1 he
  refine (hiff (e⁻¹ * a * e)).2 ?_
  have e1 : e * (e⁻¹ * a * e) * e⁻¹ = a := by group
  rw [e1]; exact ha

theorem conj_mem_T0_of_normalizer' {e : X} (he : e ∈ normalizer (T0 T : Set X)) {a : X}
    (ha : a ∈ T0 T) : e * a * e⁻¹ ∈ T0 T := (Subgroup.mem_normalizer_iff.1 he a).1 ha

theorem T_le_normalizer_T0 [Finite X] : T ≤ normalizer (T0 T : Set X) := fun _ hg =>
  mem_normalizer_of_conj_le fun _ ha => conj_mem_T0 hg ha

theorem T0_isPGroup (hT : IsPGroup 2 ↥T) : IsPGroup 2 ↥(T0 T) := hT.to_le T0_le

theorem isWeaklyClosedIn_T0 [Finite X] : IsWeaklyClosedIn (T0 T) T := by
  intro g hg
  have hle : conjSubgroup (T0 T) g ≤ T0 T := by
    unfold conjSubgroup
    rw [Subgroup.map_le_iff_le_comap]
    refine (closure_le _).2 ?_
    rintro t ⟨htT, ht2⟩
    show (MulAut.conj g⁻¹).toMonoidHom t ∈ T0 T
    refine mem_T0 ?_ ?_
    · exact hg ⟨t, subset_closure ⟨htT, ht2⟩, rfl⟩
    · show g⁻¹ * t * g⁻¹⁻¹ * (g⁻¹ * t * g⁻¹⁻¹) = 1
      calc g⁻¹ * t * g⁻¹⁻¹ * (g⁻¹ * t * g⁻¹⁻¹) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [ht2]; group
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  unfold conjSubgroup
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem mem_Z0 {t : X} (ht : t ∈ T) (h2 : t * t = 1) (hc : ∀ s ∈ T, s * t = t * s) : t ∈ Z0 T := by
  refine ⟨mem_T0 ht h2, h2, fun s hs => ?_⟩
  have : T0 T ≤ centralizer ({t} : Set X) := by
    refine (closure_le _).2 ?_
    rintro s ⟨hsT, -⟩
    exact mem_centralizer_singleton_iff.2 (hc s hsT)
  exact mem_centralizer_singleton_iff.1 (this hs)

theorem Z0_mul {a b : X} (ha : a ∈ Z0 T) (hb : b ∈ Z0 T) : a * b ∈ Z0 T := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨(T0 T).mul_mem ha1 hb1, ?_, fun s hs => ?_⟩
  · have hab : a * b = b * a := (hb3 a ha1)
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  · calc s * (a * b) = (s * a) * b := by group
      _ = (a * s) * b := by rw [ha3 s hs]
      _ = a * (s * b) := by group
      _ = a * (b * s) := by rw [hb3 s hs]
      _ = (a * b) * s := by group

theorem Z0_conj {e : X} (he : e ∈ normalizer (T0 T : Set X)) {a : X} (ha : a ∈ Z0 T) :
    e⁻¹ * a * e ∈ Z0 T := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  have hiff := Subgroup.mem_normalizer_iff.1 he
  have hconj : ∀ s ∈ T0 T, e⁻¹ * s * e ∈ T0 T := by
    intro s hs
    have := (hiff (e⁻¹ * s * e)).2 (by have e1 : e * (e⁻¹ * s * e) * e⁻¹ = s := by group
                                       rw [e1]; exact hs)
    exact this
  refine ⟨hconj a ha1, ?_, fun s hs => ?_⟩
  · calc e⁻¹ * a * e * (e⁻¹ * a * e) = e⁻¹ * (a * a) * e := by group
      _ = 1 := by rw [ha2]; group
  · have hs' : e * s * e⁻¹ ∈ T0 T := (hiff s).1 hs
    have := ha3 _ hs'
    calc s * (e⁻¹ * a * e) = e⁻¹ * ((e * s * e⁻¹) * a) * e := by group
      _ = e⁻¹ * (a * (e * s * e⁻¹)) * e := by rw [this]
      _ = (e⁻¹ * a * e) * s := by group

namespace Cfg34

variable {T P Q : Subgroup X} {x z f h : X} (c : Cfg34 X T P Q x z f h)
include c

theorem T_le_normalizer_Q : T ≤ normalizer (Q : Set X) := fun t ht => by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact c.Q_norm t ht a ha
  · intro ha
    have := c.Q_norm t⁻¹ (T.inv_mem ht) _ ha
    simpa [mul_assoc] using this

theorem Qfz_le : (Q ⊔ zpowers f) ⊔ zpowers z ≤ T :=
  sup_le (sup_le c.Q_le (zpowers_le.2 c.f_mem)) (zpowers_le.2 c.z_mem_T)

theorem coe_Qf : ((Q ⊔ zpowers f : Subgroup X) : Set X) = (Q : Set X) * (zpowers f : Set X) :=
  Subgroup.coe_mul_of_right_le_normalizer_left Q (zpowers f)
    (fun _ hw => c.T_le_normalizer_Q (zpowers_le.2 c.f_mem hw))

theorem coe_Qfz : (((Q ⊔ zpowers f) ⊔ zpowers z : Subgroup X) : Set X) =
    ((Q ⊔ zpowers f : Subgroup X) : Set X) * (zpowers z : Set X) := by
  have hz : z ∈ normalizer ((Q ⊔ zpowers f : Subgroup X) : Set X) := by
    have key : ∀ y ∈ Q ⊔ zpowers f, z * y * z⁻¹ = y := by
      intro y hy
      have hyT : y ∈ T := sup_le c.Q_le (zpowers_le.2 c.f_mem) hy
      have := c.z_cent_T y hyT
      calc z * y * z⁻¹ = (z * y) * z⁻¹ := rfl
        _ = (y * z) * z⁻¹ := by rw [← this]
        _ = y := by group
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [key y hy]; exact hy
    · intro hy
      have h2 := key _ hy
      have : z * y * z⁻¹ = y := by
        have e : z * (z * y * z⁻¹) * z⁻¹ = z * (z * y * z⁻¹) * z⁻¹ := rfl
        calc z * y * z⁻¹ = z⁻¹ * (z * (z * y * z⁻¹) * z⁻¹) * z := by group
          _ = z⁻¹ * (z * y * z⁻¹) * z := by rw [h2]
          _ = y := by group
      rw [← this]; exact hy
  exact Subgroup.coe_mul_of_right_le_normalizer_left (Q ⊔ zpowers f) (zpowers z)
    (fun w hw => by
      have := (normalizer ((Q ⊔ zpowers f : Subgroup X) : Set X)).zpow_mem hz
      obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hw
      exact (normalizer ((Q ⊔ zpowers f : Subgroup X) : Set X)).zpow_mem hz l)

theorem mem_Qfz {w : X} (hw : w ∈ (Q ⊔ zpowers f) ⊔ zpowers z) :
    ∃ q ∈ Q, ∃ k l : ℤ, w = q * (f ^ k * z ^ l) := by
  have hw' : w ∈ (((Q ⊔ zpowers f) ⊔ zpowers z : Subgroup X) : Set X) := hw
  rw [c.coe_Qfz] at hw'
  obtain ⟨y, hy, zz, hzz, rfl⟩ := hw'
  rw [c.coe_Qf] at hy
  obtain ⟨q, hq, ff, hff, rfl⟩ := hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hff
  obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hzz
  exact ⟨q, hq, k, l, by group⟩

theorem sq_mem_Q {w : X} (hw : w ∈ (Q ⊔ zpowers f) ⊔ zpowers z) : w * w ∈ Q := by
  obtain ⟨q, hq, k, l, rfl⟩ := c.mem_Qfz hw
  set a : X := f ^ k * z ^ l with ha
  have haT : a ∈ T := T.mul_mem (T.zpow_mem c.f_mem k) (T.zpow_mem c.z_mem_T l)
  have hfz : Commute (f ^ k) (z ^ l) := by
    have : Commute f z := c.f_cent z c.z_mem
    exact this.zpow_zpow k l
  have hf2 : (f ^ k) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [sq, c.f_sq]
  have hz2 : (z ^ l) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [sq, c.z_sq]
  have haa : a * a = 1 := by
    have : a ^ 2 = 1 := by
      rw [ha, hfz.mul_pow, hf2, hz2, one_mul]
    rwa [sq] at this
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have h1 : a * q * a⁻¹ ∈ Q := c.Q_norm a haT q hq
  have e : q * (f ^ k * z ^ l) * (q * (f ^ k * z ^ l)) = q * (a * q * a⁻¹) := by
    calc q * (f ^ k * z ^ l) * (q * (f ^ k * z ^ l)) = q * (a * q * a⁻¹) * (a * a) := by
          rw [ha]; group
      _ = q * (a * q * a⁻¹) := by rw [haa, mul_one]
  rw [e]
  exact Q.mul_mem hq h1

theorem card_Qfz_le [Finite X] :
    Nat.card ↥((Q ⊔ zpowers f) ⊔ zpowers z) ≤ 4 * Nat.card ↥Q := by
  have h1 : Nat.card ↥(((Q ⊔ zpowers f) ⊔ zpowers z : Subgroup X) : Set X) ≤
      Nat.card ↥((Q ⊔ zpowers f : Subgroup X) : Set X) * Nat.card ↥(zpowers z : Set X) := by
    rw [c.coe_Qfz]; exact Set.natCard_mul_le
  have h2 : Nat.card ↥((Q ⊔ zpowers f : Subgroup X) : Set X) ≤
      Nat.card ↥(Q : Set X) * Nat.card ↥(zpowers f : Set X) := by
    rw [c.coe_Qf]; exact Set.natCard_mul_le
  have hf : Nat.card ↥(zpowers f : Set X) = 2 := by
    have := Nat.card_zpowers f
    rw [c.f_order] at this
    exact this
  have hz : Nat.card ↥(zpowers z : Set X) = 2 := by
    have := Nat.card_zpowers z
    rw [c.z_order] at this
    exact this
  calc Nat.card ↥((Q ⊔ zpowers f) ⊔ zpowers z) ≤
      Nat.card ↥((Q ⊔ zpowers f : Subgroup X) : Set X) * Nat.card ↥(zpowers z : Set X) := h1
    _ ≤ (Nat.card ↥(Q : Set X) * Nat.card ↥(zpowers f : Set X)) * Nat.card ↥(zpowers z : Set X) :=
        Nat.mul_le_mul_right _ h2
    _ = 4 * Nat.card ↥Q := by
        have hQ : Nat.card ↥(Q : Set X) = Nat.card ↥Q := rfl
        rw [hf, hz, hQ]; ring

theorem conj_basic (e : X) :
    (e⁻¹ * z * e ∈ conjSubgroup P e) ∧
    (∀ b ∈ conjSubgroup P e, (e⁻¹ * z * e) * b = b * (e⁻¹ * z * e)) ∧
    (∀ b ∈ conjSubgroup P e, (∀ a ∈ conjSubgroup P e, a * b = b * a) → b = 1 ∨ b = e⁻¹ * z * e) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_conjSubgroup_iff]
    have e1 : e * (e⁻¹ * z * e) * e⁻¹ = z := by group
    rw [e1]; exact c.z_mem
  · intro b hb
    rw [mem_conjSubgroup_iff] at hb
    have := c.z_central _ hb
    calc (e⁻¹ * z * e) * b = e⁻¹ * (z * (e * b * e⁻¹)) * e := by group
      _ = e⁻¹ * ((e * b * e⁻¹) * z) * e := by rw [this]
      _ = b * (e⁻¹ * z * e) := by group
  · intro b hb hcent
    rw [mem_conjSubgroup_iff] at hb
    have hcen : ∀ a ∈ P, a * (e * b * e⁻¹) = (e * b * e⁻¹) * a := by
      intro a ha
      have ha' : e⁻¹ * a * e ∈ conjSubgroup P e := by
        rw [mem_conjSubgroup_iff]
        have e1 : e * (e⁻¹ * a * e) * e⁻¹ = a := by group
        rw [e1]; exact ha
      have := hcent _ ha'
      calc a * (e * b * e⁻¹) = e * ((e⁻¹ * a * e) * b) * e⁻¹ := by group
        _ = e * (b * (e⁻¹ * a * e)) * e⁻¹ := by rw [this]
        _ = (e * b * e⁻¹) * a := by group
    rcases c.z_unique _ hb hcen with h1 | h1
    · left
      have : e * b * e⁻¹ = 1 := h1
      calc b = e⁻¹ * (e * b * e⁻¹) * e := by group
        _ = 1 := by rw [this]; group
    · right
      have : e * b * e⁻¹ = z := h1
      calc b = e⁻¹ * (e * b * e⁻¹) * e := by group
        _ = e⁻¹ * z * e := by rw [this]


theorem conj_facts {e : X} (he : e ∈ normalizer (T0 T : Set X)) (hPT0 : P ≤ T0 T) :
    (∀ b ∈ conjSubgroup P e, b ∈ T0 T) ∧
    (∀ t ∈ T0 T, ∀ b ∈ conjSubgroup P e, t * b * t⁻¹ ∈ conjSubgroup P e) ∧
    (e⁻¹ * z * e ∈ conjSubgroup P e) ∧
    (∀ b ∈ conjSubgroup P e, (e⁻¹ * z * e) * b = b * (e⁻¹ * z * e)) ∧
    (∀ b ∈ conjSubgroup P e, (∀ a ∈ conjSubgroup P e, a * b = b * a) → b = 1 ∨ b = e⁻¹ * z * e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [mem_conjSubgroup_iff] at hb
    have := conj_mem_T0_of_normalizer he (hPT0 hb)
    simpa [mul_assoc] using this
  · intro t ht b hb
    rw [mem_conjSubgroup_iff] at hb ⊢
    have h1 : e * t * e⁻¹ ∈ T0 T := conj_mem_T0_of_normalizer' he ht
    have h2 := c.P_norm _ (T0_le h1) _ hb
    have e1 : e * (t * b * t⁻¹) * e⁻¹ = (e * t * e⁻¹) * (e * b * e⁻¹) * (e * t * e⁻¹)⁻¹ := by group
    rw [e1]; exact h2
  · rw [mem_conjSubgroup_iff]
    have e1 : e * (e⁻¹ * z * e) * e⁻¹ = z := by group
    rw [e1]; exact c.z_mem
  · intro b hb
    rw [mem_conjSubgroup_iff] at hb
    have := c.z_central _ hb
    calc (e⁻¹ * z * e) * b = e⁻¹ * (z * (e * b * e⁻¹)) * e := by group
      _ = e⁻¹ * ((e * b * e⁻¹) * z) * e := by rw [this]
      _ = b * (e⁻¹ * z * e) := by group
  · intro b hb hcent
    rw [mem_conjSubgroup_iff] at hb
    have hcen : ∀ a ∈ P, a * (e * b * e⁻¹) = (e * b * e⁻¹) * a := by
      intro a ha
      have ha' : e⁻¹ * a * e ∈ conjSubgroup P e := by
        rw [mem_conjSubgroup_iff]
        have e1 : e * (e⁻¹ * a * e) * e⁻¹ = a := by group
        rw [e1]; exact ha
      have := hcent _ ha'
      calc a * (e * b * e⁻¹) = e * ((e⁻¹ * a * e) * b) * e⁻¹ := by group
        _ = e * (b * (e⁻¹ * a * e)) * e⁻¹ := by rw [this]
        _ = (e * b * e⁻¹) * a := by group
    rcases c.z_unique _ hb hcen with h1 | h1
    · left
      have : e * b * e⁻¹ = 1 := h1
      calc b = e⁻¹ * (e * b * e⁻¹) * e := by group
        _ = 1 := by rw [this]; group
    · right
      have : e * b * e⁻¹ = z := h1
      calc b = e⁻¹ * (e * b * e⁻¹) * e := by group
        _ = e⁻¹ * z * e := by rw [this]

end Cfg34

end CFSG.GH74.GLS.C3.Layer1.P34
