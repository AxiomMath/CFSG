module

public import CFSG.GH74.GLS.Stage1.Main.P49NCore
public import CFSG.GH74.GLS.Stage1.Main.P49Setup
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Rest4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

namespace P49NI

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem abstract_N_sub (N A S U : Subgroup G) (u' x p : G)
    (hAN : A ≤ N) (hSN : S ≤ N) (hUN : U ≤ N) (hu'N : u' ∈ N) (hxN : x ∈ N) (hpN : p ∈ N)
    (hAn : ∀ m ∈ N, ∀ a ∈ A, m * a * m⁻¹ ∈ A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : IsPGroup 2 ↥A)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hAS : A ≤ S) (hu'S : u' ∈ S)
    (hSsq : ∀ s ∈ S, s * s ∈ A)
    (hu'2 : u' * u' = 1) (hu'A : u' ∉ A) (hu'inv : ∀ a ∈ A, u' * a * u'⁻¹ = a⁻¹)
    (hF : ∀ m ∈ N, ∀ a ∈ A, ∃ a' ∈ A, m * (a * u') * m⁻¹ = a' * u')
    (hU : IVK.IsFourSubgroup U) (hUA : U ≤ A) (hU1 : ∀ a ∈ A, a * a = 1 → a ∈ U)
    (hUn : ∀ m ∈ N, ∀ v ∈ U, m * v * m⁻¹ ∈ U)
    (hx3 : IsPGroup 3 ↥(zpowers x)) (hx : ∃ v ∈ U, x * v * x⁻¹ ≠ v)
    (hpU : ∃ w ∈ U, w ≠ 1 ∧ p * w * p⁻¹ = w) (hp : ∃ v ∈ U, p * v * p⁻¹ ≠ v) :
    ∃ h₀ t t' : G, orderOf h₀ = 2 ∧ orderOf t = 2 ∧ orderOf t' = 2 ∧ h₀ ∈ S ∧
      (∀ w ∈ U, h₀ * w = w * h₀) ∧ h₀ * t = t * h₀ ∧ h₀ * t' = t' * h₀ ∧
      (∀ w ∈ U, t * w * t⁻¹ ∈ U) ∧ (∀ w ∈ U, t' * w * t'⁻¹ ∈ U) ∧
      (∃ w ∈ U, t * w * t⁻¹ ≠ w) ∧ (∃ w ∈ U, t' * w * t'⁻¹ ≠ w) ∧
      (∃ w ∈ U, t * w * t⁻¹ = w ∧ t' * w * t'⁻¹ ≠ w) := by
  have hUN' : IVK.IsFourSubgroup (U.subgroupOf N) := by
    refine ⟨?_, ?_⟩
    · have := hU.1
      exact IsElementaryAbelian.subgroupOf hUN
    · rw [← hU.2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf N) ⊤ := by
    have h1 : CFSG.ABGLocalTools.IsSylowOf 2 S N := hS.of_le hSN le_top
    have h2 : (⊤ : Subgroup ↥N).map N.subtype = N := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) N).1 ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hSN, h2]
    exact h1
  have hAnN : (A.subgroupOf N).Normal :=
    ⟨fun n hn g => by
      have := hAn (g : G) g.2 (n : G) hn
      simpa [Subgroup.mem_subgroupOf] using this⟩
  have hAcN : ∀ a ∈ A.subgroupOf N, ∀ b ∈ A.subgroupOf N, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hAc _ ha _ hb)
  have hA2N : IsPGroup 2 ↥(A.subgroupOf N) := hA2.comap_subtype
  have hx3N : IsPGroup 3 ↥(zpowers (⟨x, hxN⟩ : ↥N)) :=
    (hx3.comap_subtype (K := N)).to_le
      (zpowers_le.2 (show (⟨x, hxN⟩ : ↥N) ∈ (zpowers x).subgroupOf N from mem_zpowers x))
  obtain ⟨h₀, t, t', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    P49N.abstract_N (M := ↥N) (A.subgroupOf N) (S.subgroupOf N) (U.subgroupOf N) ⟨u', hu'N⟩
      ⟨x, hxN⟩ ⟨p, hpN⟩ hAnN hAcN hA2N hSyl (fun a ha => hAS ha) hu'S
      (fun s hs => hSsq _ hs)
      (Subtype.ext hu'2) hu'A
      (fun a ha => Subtype.ext (hu'inv _ ha))
      (fun m a ha => by
        obtain ⟨a', ha', h⟩ := hF (m : G) m.2 (a : G) ha
        exact ⟨⟨a', hAN ha'⟩, ha', Subtype.ext h⟩)
      hUN' (fun a ha => hUA ha) (fun a ha h => hU1 _ ha (congrArg Subtype.val h))
      (fun m v hv => hUn (m : G) m.2 (v : G) hv)
      hx3N
      (by
        obtain ⟨v, hv, h⟩ := hx
        exact ⟨⟨v, hUN hv⟩, hv, fun e => h (congrArg Subtype.val e)⟩)
      (by
        obtain ⟨w, hw, hw1, h⟩ := hpU
        exact ⟨⟨w, hUN hw⟩, hw, fun e => hw1 (congrArg Subtype.val e), Subtype.ext h⟩)
      (by
        obtain ⟨v, hv, h⟩ := hp
        exact ⟨⟨v, hUN hv⟩, hv, fun e => h (congrArg Subtype.val e)⟩)
  refine ⟨(h₀ : G), (t : G), (t' : G), ?_, ?_, ?_, h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact h1
  · rw [Subgroup.orderOf_coe]; exact h2
  · rw [Subgroup.orderOf_coe]; exact h3
  · intro w hw; exact congrArg Subtype.val (h5 ⟨w, hUN hw⟩ hw)
  · exact congrArg Subtype.val h6
  · exact congrArg Subtype.val h7
  · intro w hw; exact h8 ⟨w, hUN hw⟩ hw
  · intro w hw; exact h9 ⟨w, hUN hw⟩ hw
  · obtain ⟨w, hw, h⟩ := h10
    exact ⟨(w : G), hw, fun e => h (Subtype.ext e)⟩
  · obtain ⟨w, hw, h⟩ := h11
    exact ⟨(w : G), hw, fun e => h (Subtype.ext e)⟩
  · obtain ⟨w, hw, h, h'⟩ := h12
    exact ⟨(w : G), hw, congrArg Subtype.val h, fun e => h' (Subtype.ext e)⟩

end Transfer

section Config

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q : Subgroup G} {FA : G → Prop}
  {U : Subgroup G} {x u₁ u₂ a₀ p₀ q₀ : G}

@[expose] def Aof (P : Subgroup G) (u₁ x a₀ : G) : Subgroup G :=
  (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹)

@[expose] def Wof (S U : Subgroup G) : Subgroup G := S ⊓ centralizer (U : Set G)

variable {c : R1.Setup9 G z S P Q FA U x u₁ u₂}

theorem A_le_W (d : R1.Setup9.Gd c a₀ p₀ q₀) : Aof P u₁ x a₀ ≤ Wof S U :=
  sup_le c.V₁_le_W (zpowers_le.2 (c.g_mem_W d.a_mem))

theorem A_comm (d : R1.Setup9.Gd c a₀ p₀ q₀) {a b : G} (ha : a ∈ Aof P u₁ x a₀)
    (hb : b ∈ Aof P u₁ x a₀) : a * b = b * a := by
  obtain ⟨v', hv', t, ht, rfl⟩ := c.A_mem d.a_mem d.gen hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h1 := c.A_comm_V d.a_mem d.gen ha hv'
  have h2 : a * (x * a₀ * x⁻¹) ^ k = (x * a₀ * x⁻¹) ^ k * a :=
    (Commute.zpow_right (show Commute a (x * a₀ * x⁻¹) from c.A_comm_g d.a_mem d.gen ha) k).eq
  calc a * (v' * (x * a₀ * x⁻¹) ^ k) = (a * v') * (x * a₀ * x⁻¹) ^ k := by group
    _ = (v' * a) * (x * a₀ * x⁻¹) ^ k := by rw [h1]
    _ = v' * (a * (x * a₀ * x⁻¹) ^ k) := by group
    _ = v' * ((x * a₀ * x⁻¹) ^ k * a) := by rw [h2]
    _ = (v' * (x * a₀ * x⁻¹) ^ k) * a := by group

theorem A_pgroup (d : R1.Setup9.Gd c a₀ p₀ q₀) : IsPGroup 2 ↥(Aof P u₁ x a₀) :=
  c.cfg.S_pgroup.to_le ((A_le_W d).trans inf_le_left)

theorem u'_inv_A (d : R1.Setup9.Gd c a₀ p₀ q₀) {a : G} (ha : a ∈ Aof P u₁ x a₀) :
    (p₀ * q₀) * a * (p₀ * q₀)⁻¹ = a⁻¹ := by
  obtain ⟨v, hv, t, ht, rfl⟩ := c.A_mem d.a_mem d.gen ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h1 := c.u'_inv₁ d.p_mem d.q_mem d.p_not v hv
  have h2 : (p₀ * q₀) * (x * a₀ * x⁻¹) ^ k * (p₀ * q₀)⁻¹ = ((x * a₀ * x⁻¹) ^ k)⁻¹ := by
    rw [← conj_zpow, d.u'_inv_g, inv_zpow]
  have h3 := c.V₁_comm_gpow d.a_mem d.gen hv k
  calc (p₀ * q₀) * (v * (x * a₀ * x⁻¹) ^ k) * (p₀ * q₀)⁻¹
      = ((p₀ * q₀) * v * (p₀ * q₀)⁻¹) * ((p₀ * q₀) * (x * a₀ * x⁻¹) ^ k * (p₀ * q₀)⁻¹) := by group
    _ = v⁻¹ * ((x * a₀ * x⁻¹) ^ k)⁻¹ := by rw [h1, h2]
    _ = ((x * a₀ * x⁻¹) ^ k * v)⁻¹ := by rw [mul_inv_rev]
    _ = (v * (x * a₀ * x⁻¹) ^ k)⁻¹ := by rw [h3]

theorem W_cases' (d : R1.Setup9.Gd c a₀ p₀ q₀) {w : G} (hw : w ∈ Wof S U) :
    w ∈ Aof P u₁ x a₀ ∨ ∃ a ∈ Aof P u₁ x a₀, w = a * (p₀ * q₀) := by
  rcases d.W_cases hw with h | h
  · exact Or.inl h
  · refine Or.inr ⟨w * (p₀ * q₀)⁻¹, h, ?_⟩
    group

theorem coset_sq (d : R1.Setup9.Gd c a₀ p₀ q₀) {a : G} (ha : a ∈ Aof P u₁ x a₀) :
    (a * (p₀ * q₀)) * (a * (p₀ * q₀)) = 1 := by
  have h1 := u'_inv_A d ha
  have h2 := d.u'_sq'
  calc (a * (p₀ * q₀)) * (a * (p₀ * q₀)) = a * ((p₀ * q₀) * a * (p₀ * q₀)⁻¹) * ((p₀ * q₀) * (p₀ * q₀)) := by
        group
    _ = 1 := by rw [h1, h2]; group

theorem W_invol (d : R1.Setup9.Gd c a₀ p₀ q₀) {w : G} (hw : w ∈ Wof S U) :
    w ∈ Aof P u₁ x a₀ ∨ w * w = 1 := by
  rcases W_cases' d hw with h | ⟨a, ha, rfl⟩
  · exact Or.inl h
  · exact Or.inr (coset_sq d ha)

theorem u₁_mem_A (_d : R1.Setup9.Gd c a₀ p₀ q₀) : u₁ ∈ Aof P u₁ x a₀ := mem_sup_left c.u₁_mem_V₁

theorem z_mem_A (_d : R1.Setup9.Gd c a₀ p₀ q₀) : z ∈ Aof P u₁ x a₀ := mem_sup_left c.z_mem_V₁


omit [Finite G] in
theorem A_normal_abstract {W A : Subgroup G} {m b : G} (hm : m ∈ normalizer (W : Set G))
    (hAW : A ≤ W) (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hinv : ∀ w ∈ W, w ∈ A ∨ w * w = 1) (hb : b ∈ A) (hb2 : b * b ≠ 1) :
    ∀ a ∈ A, m * a * m⁻¹ ∈ A := by
  have key : ∀ a ∈ A, a * a ≠ 1 → m * a * m⁻¹ ∈ A := by
    intro a ha ha2
    have hW : m * a * m⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 hm a).1 (hAW ha)
    rcases hinv _ hW with h | h
    · exact h
    · exfalso
      apply ha2
      have h1 : m * (a * a) * m⁻¹ = 1 := by
        calc m * (a * a) * m⁻¹ = (m * a * m⁻¹) * (m * a * m⁻¹) := by group
          _ = 1 := h
      calc a * a = m⁻¹ * (m * (a * a) * m⁻¹) * m := by group
        _ = 1 := by rw [h1]; group
  intro a ha
  by_cases ha2 : a * a = 1
  · have hab : (a * b) * (a * b) ≠ 1 := by
      intro h
      apply hb2
      have e : (a * b) * (a * b) = (a * a) * (b * b) := by
        calc (a * b) * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hAc b hb a ha]
          _ = (a * a) * (b * b) := by group
      rw [e, ha2, one_mul] at h
      exact h
    have h1 := key (a * b) (A.mul_mem ha hb) hab
    have h2 := key b hb hb2
    have e : m * a * m⁻¹ = (m * (a * b) * m⁻¹) * (m * b * m⁻¹)⁻¹ := by group
    rw [e]
    exact A.mul_mem h1 (A.inv_mem h2)
  · exact key a ha ha2

theorem A_normal (d : R1.Setup9.Gd c a₀ p₀ q₀) {m : G} (hm : m ∈ normalizer (Wof S U : Set G))
    {a : G} (ha : a ∈ Aof P u₁ x a₀) : m * a * m⁻¹ ∈ Aof P u₁ x a₀ :=
  A_normal_abstract (W := Wof S U) hm (A_le_W d) (fun a ha a' ha' => A_comm d ha ha')
    (fun w hw => W_invol d hw) (u₁_mem_A d) (by rw [c.u₁_sq]; exact c.hz1) a ha

theorem coset_inv (d : R1.Setup9.Gd c a₀ p₀ q₀) {m : G} (hm : m ∈ normalizer (Wof S U : Set G))
    {a : G} (ha : a ∈ Aof P u₁ x a₀) :
    ∃ a' ∈ Aof P u₁ x a₀, m * (a * (p₀ * q₀)) * m⁻¹ = a' * (p₀ * q₀) := by
  have hW : a * (p₀ * q₀) ∈ Wof S U := mul_mem (A_le_W d ha) d.u'_W
  have hmW : m * (a * (p₀ * q₀)) * m⁻¹ ∈ Wof S U := (Subgroup.mem_normalizer_iff.1 hm _).1 hW
  rcases W_cases' d hmW with h | ⟨a', ha', h⟩
  · exfalso
    have h1 := A_normal d (inv_mem hm) h
    have h2 : m⁻¹ * (m * (a * (p₀ * q₀)) * m⁻¹) * m⁻¹⁻¹ = a * (p₀ * q₀) := by group
    rw [h2] at h1
    apply d.u'_notin_A
    have h3 := mul_mem (inv_mem ha) h1
    have h4 : p₀ * q₀ ∈ Aof P u₁ x a₀ := by simpa using h3
    exact h4
  · exact ⟨a', ha', h⟩

theorem S_norm_W (c : R1.Setup9 G z S P Q FA U x u₁ u₂) {s : G} (hs : s ∈ S) {w : G}
    (hw : w ∈ Wof S U) : s * w * s⁻¹ ∈ Wof S U := by
  refine ⟨S.mul_mem (S.mul_mem hs hw.1) (S.inv_mem hs), Subgroup.mem_centralizer_iff.2 (fun v hv => ?_)⟩
  have hv' : s⁻¹ * v * s ∈ U := by
    have := c.U_norm s⁻¹ (S.inv_mem hs) v hv
    rwa [inv_inv] at this
  have h1 := Subgroup.mem_centralizer_iff.1 hw.2 _ hv'
  calc v * (s * w * s⁻¹) = s * ((s⁻¹ * v * s) * w) * s⁻¹ := by group
    _ = s * (w * (s⁻¹ * v * s)) * s⁻¹ := by rw [h1]
    _ = (s * w * s⁻¹) * v := by group

theorem S_le_N (c : R1.Setup9 G z S P Q FA U x u₁ u₂) : S ≤ normalizer (Wof S U : Set G) :=
  fun _ hs => CFSG.GH74.GLS.Stage1.Thm3.Sec4.M.mem_normalizer_of_both
    (fun _ hw => S_norm_W c hs hw)
    (fun _ hw => by simpa using S_norm_W c (S.inv_mem hs) hw)


theorem z_conj (c : R1.Setup9 G z S P Q FA U x u₁ u₂) {s : G} (hs : s ∈ S) : s * z * s⁻¹ = z := by
  rw [c.z_comm hs]; group

theorem conj_u_cases (c : R1.Setup9 G z S P Q FA U x u₁ u₂) {s : G} (hs : s ∈ S) :
    s * (u₁ * u₂) * s⁻¹ = u₁ * u₂ ∨ s * (u₁ * u₂) * s⁻¹ = z * (u₁ * u₂) := by
  have hmem := c.U_norm s hs _ c.u_mem
  rcases c.mem_U hmem with e | e | e | e
  · exfalso
    apply c.u_ne.1
    calc u₁ * u₂ = s⁻¹ * (s * (u₁ * u₂) * s⁻¹) * s := by group
      _ = 1 := by rw [e]; group
  · exfalso
    apply c.u_ne.2
    calc u₁ * u₂ = s⁻¹ * (s * (u₁ * u₂) * s⁻¹) * s := by group
      _ = s⁻¹ * z * s := by rw [e]
      _ = z := by
        have := z_conj c (S.inv_mem hs)
        rwa [inv_inv] at this
  · exact Or.inl e
  · exact Or.inr e

theorem p₀_conj_u (d : R1.Setup9.Gd c a₀ p₀ q₀) : p₀ * (u₁ * u₂) * p₀⁻¹ = z * (u₁ * u₂) := by
  have h1 : p₀ * u₁ * p₀⁻¹ = u₁⁻¹ := (c.quatOut₁ p₀ d.p_mem d.p_not).2 u₁ c.u₁_mem_V₁
  have h2 : p₀ * u₂ * p₀⁻¹ = u₂ := by
    rw [c.cfg.PQ_comm p₀ d.p_mem u₂ c.u₂_mem]; group
  calc p₀ * (u₁ * u₂) * p₀⁻¹ = (p₀ * u₁ * p₀⁻¹) * (p₀ * u₂ * p₀⁻¹) := by group
    _ = u₁⁻¹ * u₂ := by rw [h1, h2]
    _ = (u₁ * z) * u₂ := by rw [c.u₁_inv]
    _ = z * (u₁ * u₂) := by rw [c.z_comm (c.cfg.P_le c.u₁_mem)]; group

theorem S_sub_W (d : R1.Setup9.Gd c a₀ p₀ q₀) {s : G} (hs : s ∈ S) (hsW : s ∉ Wof S U) :
    s * p₀⁻¹ ∈ Wof S U := by
  have hp₀S : p₀ ∈ S := c.cfg.P_le d.p_mem
  have hsu : s * (u₁ * u₂) * s⁻¹ = z * (u₁ * u₂) := by
    rcases conj_u_cases c hs with h | h
    · exfalso
      apply hsW
      have hu : s * (u₁ * u₂) = (u₁ * u₂) * s := mul_inv_eq_iff_eq_mul.1 h
      exact ⟨hs, Subgroup.mem_centralizer_iff.2 (fun w hw =>
        (c.comm_U_of (c.z_comm hs) hu w hw).symm)⟩
    · exact h
  have hpu' : p₀ * (z * (u₁ * u₂)) * p₀⁻¹ = u₁ * u₂ := by
    calc p₀ * (z * (u₁ * u₂)) * p₀⁻¹ = (p₀ * z * p₀⁻¹) * (p₀ * (u₁ * u₂) * p₀⁻¹) := by group
      _ = z * (z * (u₁ * u₂)) := by rw [z_conj c hp₀S, p₀_conj_u d]
      _ = u₁ * u₂ := by rw [← mul_assoc, c.hz2, one_mul]
  have hpu : p₀⁻¹ * (u₁ * u₂) * p₀ = z * (u₁ * u₂) := by
    calc p₀⁻¹ * (u₁ * u₂) * p₀ = p₀⁻¹ * (p₀ * (z * (u₁ * u₂)) * p₀⁻¹) * p₀ := by rw [hpu']
      _ = z * (u₁ * u₂) := by group
  have hsS : s * p₀⁻¹ ∈ S := S.mul_mem hs (S.inv_mem hp₀S)
  have hu : (s * p₀⁻¹) * (u₁ * u₂) = (u₁ * u₂) * (s * p₀⁻¹) := by
    have e : (s * p₀⁻¹) * (u₁ * u₂) * (s * p₀⁻¹)⁻¹ = u₁ * u₂ := by
      calc (s * p₀⁻¹) * (u₁ * u₂) * (s * p₀⁻¹)⁻¹ = s * (p₀⁻¹ * (u₁ * u₂) * p₀) * s⁻¹ := by group
        _ = s * (z * (u₁ * u₂)) * s⁻¹ := by rw [hpu]
        _ = (s * z * s⁻¹) * (s * (u₁ * u₂) * s⁻¹) := by group
        _ = z * (z * (u₁ * u₂)) := by rw [z_conj c hs, hsu]
        _ = u₁ * u₂ := by rw [← mul_assoc, c.hz2, one_mul]
    exact mul_inv_eq_iff_eq_mul.1 e
  exact ⟨hsS, Subgroup.mem_centralizer_iff.2 (fun w hw =>
    (c.comm_U_of (c.z_comm hsS) hu w hw).symm)⟩

theorem S_sq_A (d : R1.Setup9.Gd c a₀ p₀ q₀) {s : G} (hs : s ∈ S) : s * s ∈ Aof P u₁ x a₀ := by
  by_cases hsW : s ∈ Wof S U
  · rcases W_cases' d hsW with h | ⟨a, ha, rfl⟩
    · exact mul_mem h h
    · rw [coset_sq d ha]; exact one_mem _
  · have hp₀S : p₀ ∈ S := c.cfg.P_le d.p_mem
    obtain ⟨w, hw⟩ : ∃ w, w = s * p₀⁻¹ := ⟨_, rfl⟩
    have hwW : w ∈ Wof S U := by rw [hw]; exact S_sub_W d hs hsW
    have hs_eq : s = w * p₀ := by rw [hw]; group
    have hp₀N : p₀ ∈ normalizer (Wof S U : Set G) := S_le_N c hp₀S
    have hp₀2 : p₀ * p₀ = z := (c.quatOut₁ p₀ d.p_mem d.p_not).1
    have hzA : z ∈ Aof P u₁ x a₀ := z_mem_A d
    have hss : s * s = w * (p₀ * w * p₀⁻¹) * z := by
      calc s * s = (w * p₀) * (w * p₀) := by rw [← hs_eq]
        _ = w * (p₀ * w * p₀⁻¹) * (p₀ * p₀) := by group
        _ = w * (p₀ * w * p₀⁻¹) * z := by rw [hp₀2]
    rw [hss]
    refine mul_mem ?_ hzA
    rcases W_cases' d hwW with h | ⟨a, ha, hwa⟩
    · exact mul_mem h (A_normal d hp₀N h)
    · obtain ⟨a', ha', h1⟩ := coset_inv d hp₀N ha
      rw [hwa, h1]
      have e : (a * (p₀ * q₀)) * (a' * (p₀ * q₀)) = a * a'⁻¹ := by
        have h2 := u'_inv_A d ha'
        calc (a * (p₀ * q₀)) * (a' * (p₀ * q₀))
            = a * ((p₀ * q₀) * a' * (p₀ * q₀)⁻¹) * ((p₀ * q₀) * (p₀ * q₀)) := by group
          _ = a * a'⁻¹ := by rw [h2, d.u'_sq']; group
      rw [e]
      exact mul_mem ha (inv_mem ha')

theorem Omega1_le_U (d : R1.Setup9.Gd c a₀ p₀ q₀) {a : G} (ha : a ∈ Aof P u₁ x a₀)
    (ha2 : a * a = 1) : a ∈ U := by
  obtain ⟨v, hv, t, ht, rfl⟩ := c.A_mem d.a_mem d.gen ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have hcomm := c.V₁_comm_gpow d.a_mem d.gen hv k
  have e : (v * (x * a₀ * x⁻¹) ^ k) * (v * (x * a₀ * x⁻¹) ^ k) =
      (v * v) * ((x * a₀ * x⁻¹) ^ k * (x * a₀ * x⁻¹) ^ k) := by
    calc (v * (x * a₀ * x⁻¹) ^ k) * (v * (x * a₀ * x⁻¹) ^ k)
        = v * ((x * a₀ * x⁻¹) ^ k * v) * (x * a₀ * x⁻¹) ^ k := by group
      _ = v * (v * (x * a₀ * x⁻¹) ^ k) * (x * a₀ * x⁻¹) ^ k := by rw [hcomm]
      _ = (v * v) * ((x * a₀ * x⁻¹) ^ k * (x * a₀ * x⁻¹) ^ k) := by group
  rw [e] at ha2
  have hgk : (x * a₀ * x⁻¹) ^ k * (x * a₀ * x⁻¹) ^ k = (v * v)⁻¹ := eq_inv_of_mul_eq_one_right ha2
  have hgkP : (x * a₀ * x⁻¹) ^ (k + k) ∈ P := by
    rw [zpow_add, hgk]
    exact P.inv_mem (P.mul_mem hv.1 hv.1)
  have hg1 : (x * a₀ * x⁻¹) ^ (k + k) = 1 := c.gpow_P d.a_mem d.gen _ hgkP
  rw [zpow_add] at hg1
  have hvv : v * v = 1 := inv_eq_one.1 (by rw [← hgk, hg1])
  have hvcases := c.cfg.P_inv v hv.1 hvv
  have hgeq : (x * a₀ * x⁻¹) ^ k = x * a₀ ^ k * x⁻¹ := conj_zpow
  have hak : a₀ ^ k * a₀ ^ k = 1 := by
    have h1 : x * (a₀ ^ k * a₀ ^ k) * x⁻¹ = 1 := by
      calc x * (a₀ ^ k * a₀ ^ k) * x⁻¹ = (x * a₀ ^ k * x⁻¹) * (x * a₀ ^ k * x⁻¹) := by group
        _ = (x * a₀ * x⁻¹) ^ k * (x * a₀ * x⁻¹) ^ k := by rw [hgeq]
        _ = 1 := hg1
    calc a₀ ^ k * a₀ ^ k = x⁻¹ * (x * (a₀ ^ k * a₀ ^ k) * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  have hakP : a₀ ^ k ∈ P := P.zpow_mem d.a_mem.1 k
  have htcases := c.cfg.P_inv (a₀ ^ k) hakP hak
  have hz'U : x * z * x⁻¹ ∈ U := c.x_U z c.z_mem_U
  have hzU : z ∈ U := c.z_mem_U
  rw [hgeq]
  rcases hvcases with h1 | h1 <;> rcases htcases with h2 | h2 <;> rw [h1, h2]
  · simp
  · simpa using hz'U
  · simpa using hzU
  · exact U.mul_mem hzU hz'U

theorem U_le_A (d : R1.Setup9.Gd c a₀ p₀ q₀) : U ≤ Aof P u₁ x a₀ := by
  intro w hw
  have hzA : z ∈ Aof P u₁ x a₀ := z_mem_A d
  have hz'A : x * z * x⁻¹ ∈ Aof P u₁ x a₀ := mem_sup_right (c.z'_mem_zpowers_g d.gen)
  have huA : u₁ * u₂ ∈ Aof P u₁ x a₀ := by
    rcases c.z'_cases with h | h
    · rw [← h]; exact hz'A
    · have h3 := mul_mem (inv_mem hzA) hz'A
      rw [h] at h3
      have h4 : z⁻¹ * (z * (u₁ * u₂)) = u₁ * u₂ := by group
      rwa [h4] at h3
  rcases c.mem_U hw with h | h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact hzA
  · rw [h]; exact huA
  · rw [h]; exact mul_mem hzA huA

theorem U_norm_N (d : R1.Setup9.Gd c a₀ p₀ q₀) {m : G} (hm : m ∈ normalizer (Wof S U : Set G))
    {v : G} (hv : v ∈ U) : m * v * m⁻¹ ∈ U := by
  refine Omega1_le_U d (A_normal d hm (U_le_A d hv)) ?_
  calc (m * v * m⁻¹) * (m * v * m⁻¹) = m * (v * v) * m⁻¹ := by group
    _ = 1 := by rw [c.U_four.1 v hv]; group


end Config

end P49NI

section Main

open P49NI

variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y : G}

theorem local_N49 (hc : Closed49) (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤)
    (h : Ctx49 G z S K F U x y) :
    ∃ h₀ t t' : G, orderOf h₀ = 2 ∧ orderOf t = 2 ∧ orderOf t' = 2 ∧
      (∃ g : G, g * h₀ * g⁻¹ ∈ S) ∧
      (∀ w ∈ U, h₀ * w = w * h₀) ∧ h₀ * t = t * h₀ ∧ h₀ * t' = t' * h₀ ∧
      (∀ w ∈ U, t * w * t⁻¹ ∈ U) ∧ (∀ w ∈ U, t' * w * t'⁻¹ ∈ U) ∧
      (∃ w ∈ U, t * w * t⁻¹ ≠ w) ∧ (∃ w ∈ U, t' * w * t'⁻¹ ≠ w) ∧
      (∃ w ∈ U, t * w * t⁻¹ = w ∧ t' * w * t'⁻¹ ≠ w) := by
  obtain ⟨u₁, u₂, c⟩ := setup9_of_ctx49 hc h
  obtain ⟨a₀, ha₀V, hgen⟩ := R1.exists_gen_of_cyclic c.V₁_cyc
  obtain ⟨p₀, hp₀, hp₀V⟩ := c.exists_notin_V₁
  obtain ⟨q₀, hq₀, hq₀V⟩ := c.exists_notin_V₂
  have d : R1.Setup9.Gd c a₀ p₀ q₀ := ⟨ha₀V, hgen, hp₀, hq₀, hp₀V, hq₀V⟩
  have hp₀S : p₀ ∈ S := c.cfg.P_le d.p_mem
  have hSN := S_le_N c
  have hAS : Aof (S ⊓ K) u₁ x a₀ ≤ S := (A_le_W d).trans (show Wof S U ≤ S from inf_le_left)
  have hp : ∃ v ∈ U, p₀ * v * p₀⁻¹ ≠ v := by
    refine ⟨u₁ * u₂, c.u_mem, fun e => c.hz1 ?_⟩
    rw [p₀_conj_u d] at e
    calc z = z * (u₁ * u₂) * (u₁ * u₂)⁻¹ := by group
      _ = (u₁ * u₂) * (u₁ * u₂)⁻¹ := by rw [e]
      _ = 1 := by group
  obtain ⟨h₀, t, t', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    abstract_N_sub (normalizer (Wof S U : Set G)) (Aof (S ⊓ K) u₁ x a₀) S U (p₀ * q₀) x p₀
      (hAS.trans hSN) hSN (c.U_le_S.trans hSN) (hSN d.u'_W.1) h.x_W (hSN hp₀S)
      (fun m hm a ha => A_normal d hm ha) (fun a ha b hb => A_comm d ha hb) (A_pgroup d)
      hSyl hAS d.u'_W.1 (fun s hs => S_sq_A d hs) d.u'_sq' d.u'_notin_A
      (fun a ha => u'_inv_A d ha) (fun m hm a ha => coset_inv d hm ha)
      h.U_four (U_le_A d) (fun a ha h2 => Omega1_le_U d ha h2)
      (fun m hm v hv => U_norm_N d hm hv)
      h.x3 ⟨z, c.z_mem_U, c.x_z⟩ ⟨z, c.z_mem_U, c.hz1, z_conj c hp₀S⟩ hp
  exact ⟨h₀, t, t', h1, h2, h3, ⟨1, by simpa using h4⟩, h5, h6, h7, h8, h9, h10, h11, h12⟩

end Main

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
