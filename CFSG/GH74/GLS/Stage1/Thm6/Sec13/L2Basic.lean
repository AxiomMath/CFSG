module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Phase1
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Grp

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem E24_sq (a : E24) : a * a = 1 := by
  ext i
  have : ∀ b : Multiplicative (ZMod 2), b * b = 1 := by decide
  exact this (a i)

theorem E24_comm (a b : E24) : a * b = b * a := mul_comm a b

structure Ctx2 (G : Type) [Group G] (x : G) (T V H : Subgroup G) (f : G) : Prop where
  c3 : Ctx3 G x T V H f
  e24 : Nonempty (↥(Hzero H f) ≃* E24)

theorem Out12.rank_conj [Finite G] {x : G} {T V : Subgroup G} (hout : Out12 G x T V) (g : G)
    {E : Subgroup G} (hE : E ≤ centralizer ({g * x * g⁻¹} : Set G)) (hE2 : IsElemAb2 E) :
    Nat.card E ≤ 8 := by
  have hmem : ∀ a : G, a ∈ cj g⁻¹ E ↔ g * a * g⁻¹ ∈ E := by
    intro a
    rw [mem_cj]
    simp
  have hC : cj g⁻¹ E ≤ centralizer ({x} : Set G) := by
    intro a ha
    have ha' : g * a * g⁻¹ ∈ E := (hmem a).1 ha
    have h1 := mem_centralizer_iff.1 (hE ha') (g * x * g⁻¹) rfl
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have e : g * (x * a) * g⁻¹ = g * (a * x) * g⁻¹ := by
      calc g * (x * a) * g⁻¹ = (g * x * g⁻¹) * (g * a * g⁻¹) := by group
        _ = (g * a * g⁻¹) * (g * x * g⁻¹) := h1
        _ = g * (a * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hE2' : IsElemAb2 (cj g⁻¹ E) := by
    intro a ha
    have ha' := (hmem a).1 ha
    obtain ⟨h1, h2⟩ := hE2 _ ha'
    refine ⟨?_, ?_⟩
    · have e : g * (a * a) * g⁻¹ = (g * a * g⁻¹) * (g * a * g⁻¹) := by group
      have : g * (a * a) * g⁻¹ = 1 := by rw [e, h1]
      have h3 : g * (a * a) = g := mul_inv_eq_one.1 this
      exact mul_eq_left.1 h3
    · intro b hb
      have hb' := (hmem b).1 hb
      have h3 := h2 _ hb'
      have e : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
        calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h3
          _ = g * (b * a) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e)
  have := hout.rank _ hC hE2'
  rw [card_cj] at this
  simpa using this

namespace Ctx2

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx2 G x T V H f)
include c

theorem P_card : Nat.card (Hzero H f) = 16 := by
  obtain ⟨e⟩ := c.e24
  rw [Nat.card_congr e.toEquiv, card_E24]; norm_num

theorem P_sq : ∀ a ∈ Hzero H f, a * a = 1 := by
  obtain ⟨e⟩ := c.e24
  intro a ha
  have := E24_sq (e ⟨a, ha⟩)
  have h2 : e (⟨a, ha⟩ * ⟨a, ha⟩) = e 1 := by rw [map_mul, map_one, this]
  have := e.injective h2
  exact congrArg Subtype.val this

theorem P_comm : ∀ a ∈ Hzero H f, ∀ b ∈ Hzero H f, a * b = b * a := by
  obtain ⟨e⟩ := c.e24
  intro a ha b hb
  have h2 : e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) := by
    rw [map_mul, map_mul, E24_comm]
  exact congrArg Subtype.val (e.injective h2)

theorem hD : DData V (Hzero H f) ⊥ := by
  refine ⟨bot_le, Or.inl rfl, ?_, ?_⟩
  · intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_def]
    have := c.P_comm a ha b hb
    calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [this]
      _ = 1 := by group
  · rw [Subgroup.card_bot, c.P_card]

theorem P_two : IsPGroup 2 ↥(Hzero H f) := c.c3.H_two.to_le c.c3.H0_le

theorem not_fused [Finite G] (g : G) : g * x * g⁻¹ ∉ Hzero H f :=
  not_fused_of_abelian c.c3.out c.P_two
    (fun u hu _ => ⟨Hzero H f, le_rfl, hu, c.P_comm, by rw [c.P_card]⟩) g

theorem card_cent_free [Finite G] {y : G} (g : G) (hyg : y = g * x * g⁻¹) (hy2 : y * y = 1)
    (hyN : ∀ q ∈ Hzero H f, y * q * y⁻¹ ∈ Hzero H f) :
    Nat.card ↥(Hzero H f ⊓ centralizer ({y} : Set G)) = 4 := by
  have hyP : y ∉ Hzero H f := by rw [hyg]; exact c.not_fused g
  set N := Hzero H f ⊓ centralizer ({y} : Set G) with hN
  have hlow : 16 ≤ Nat.card N ^ 2 := by
    have := card_le_cent_sq c.P_sq c.P_comm hy2 hyN
    rw [c.P_card] at this
    exact this
  have hycN : ∀ q ∈ N, q * y = y * q := by
    intro q hq
    exact (mem_centralizer_iff.1 hq.2 y rfl).symm
  have hyN' : ∀ q ∈ N, y * q * y⁻¹ ∈ N := by
    intro q hq
    have : y * q * y⁻¹ = q := by
      calc y * q * y⁻¹ = (q * y) * y⁻¹ := by rw [← hycN q hq]
        _ = q := by group
    rw [this]; exact hq
  have hyNn : y ∉ N := fun h => hyP h.1
  have hcardE : Nat.card ↥(N ⊔ zpowers y) = 2 * Nat.card N :=
    card_sup_zpowers_sq (by rw [hy2]; exact N.one_mem) hyN' hyNn
  have hEC : N ⊔ zpowers y ≤ centralizer ({y} : Set G) := by
    refine sup_le (fun q hq => hq.2) ?_
    rw [zpowers_le]
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
  have hEel : IsElemAb2 (N ⊔ zpowers y) := by
    have hNsq : ∀ q ∈ N, q * q = 1 := fun q hq => c.P_sq q hq.1
    have hNcomm : ∀ q ∈ N, ∀ q' ∈ N, q * q' = q' * q := fun q hq q' hq' => c.P_comm q hq.1 q' hq'.1
    intro a ha
    obtain ⟨q, hq, ha' | ha'⟩ := (mem_sup_zpowers_invol hy2 hyN').1 ha
    · rw [ha']
      refine ⟨hNsq q hq, ?_⟩
      intro b hb
      obtain ⟨q', hq', hb' | hb'⟩ := (mem_sup_zpowers_invol hy2 hyN').1 hb
      · rw [hb']; exact hNcomm q hq q' hq'
      · rw [hb']
        calc q * (q' * y) = (q * q') * y := by group
          _ = (q' * q) * y := by rw [hNcomm q hq q' hq']
          _ = q' * (q * y) := by group
          _ = q' * (y * q) := by rw [hycN q hq]
          _ = (q' * y) * q := by group
    · rw [ha']
      refine ⟨?_, ?_⟩
      · calc q * y * (q * y) = q * (y * q) * y := by group
          _ = q * (q * y) * y := by rw [← hycN q hq]
          _ = (q * q) * (y * y) := by group
          _ = 1 := by rw [hNsq q hq, hy2, one_mul]
      · intro b hb
        obtain ⟨q', hq', hb' | hb'⟩ := (mem_sup_zpowers_invol hy2 hyN').1 hb
        · rw [hb']
          calc q * y * q' = q * (y * q') := by group
            _ = q * (q' * y) := by rw [hycN q' hq']
            _ = (q * q') * y := by group
            _ = (q' * q) * y := by rw [hNcomm q hq q' hq']
            _ = q' * (q * y) := by group
        · rw [hb']
          calc q * y * (q' * y) = q * (y * q') * y := by group
            _ = q * (q' * y) * y := by rw [hycN q' hq']
            _ = (q * q') * (y * y) := by group
            _ = (q' * q) * (y * y) := by rw [hNcomm q hq q' hq']
            _ = q' * (q * y) * y := by group
            _ = q' * (y * q) * y := by rw [hycN q hq]
            _ = (q' * y) * (q * y) := by group
  have hE8 := Out12.rank_conj c.c3.out g (hyg ▸ hEC) hEel
  rw [hcardE] at hE8
  have hup : Nat.card N ≤ 4 := by omega
  have : 4 ≤ Nat.card N := by nlinarith
  omega

end Ctx2


namespace Ctx2

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx2 G x T V H f)
include c

theorem T_inf_P [Finite G] : T ⊓ Hzero H f = V := by
  apply le_antisymm
  · rintro g ⟨hgT, hgP⟩
    have hgH : g ∈ H := c.c3.H0_le hgP
    have hgE : g ∈ T ⊓ H := ⟨hgT, hgH⟩
    rw [c.c3.hp.T_inter] at hgE
    have hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V := by
      intro v hv
      have : x * v * x⁻¹ = v := by
        calc x * v * x⁻¹ = (v * x) * x⁻¹ := by rw [c.c3.x_comm_V hv]
          _ = v := by group
      rw [this]; exact hv
    obtain ⟨q, hq, h | h⟩ := (mem_sup_zpowers_invol c.c3.x_sq hxV).1 hgE
    · rw [h]; exact hq
    · exfalso
      apply c.c3.x_notin_H0
      have : x = q⁻¹ * g := by rw [h]; group
      rw [this]
      exact (Hzero H f).mul_mem ((Hzero H f).inv_mem (c.c3.V_le_H0 hq)) hgP
  · intro v hv
    exact ⟨c.c3.out.V_le hv, c.c3.V_le_H0 hv⟩

theorem x_mem_T : x ∈ T := c.c3.out.E_le_T x_mem_EV

end Ctx2

structure Ctx2S (G : Type) [Group G] (x : G) (T V H : Subgroup G) (f : G) (S : Subgroup G) :
    Prop where
  c2 : Ctx2 G x T V H f
  hPT : ∀ s ∈ H ⊔ T, ∀ q ∈ Hzero H f, s * q * s⁻¹ ∈ Hzero H f
  syl : Sylow2In S ⊤
  le : H ⊔ T ≤ S

theorem Ctx2.exists_S [Finite G] {x : G} {T V H : Subgroup G} {f : G} (c : Ctx2 G x T V H f)
    (h9 : IG_9_16) : ∃ S : Subgroup G, Ctx2S G x T V H f S := by
  obtain ⟨S, hS, hle⟩ := SylowIn.exists_ge (p := 2) (le_top : H ⊔ T ≤ ⊤) c.c3.Hstar_two
  exact ⟨S, c, c.c3.Hstar_norm_H0 h9 c.hD, hS, hle⟩

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem S_two : IsPGroup 2 ↥S := c.syl.2.1

theorem P_le_S : Hzero H f ≤ S := c.c2.c3.H0_le.trans (le_sup_left.trans c.le)

theorem T_le_S : T ≤ S := le_sup_right.trans c.le

theorem x_mem_S : x ∈ S := c.T_le_S c.c2.x_mem_T

theorem Hstar_decomp : ∀ s ∈ H ⊔ T, ∃ p ∈ Hzero H f, ∃ t ∈ T, s = p * t := by
  have hTn : ∀ t ∈ T, ∀ q ∈ Hzero H f, t * q * t⁻¹ ∈ Hzero H f :=
    fun t ht q hq => c.hPT t (Subgroup.mem_sup_right ht) q hq
  let M : Subgroup G :=
    { carrier := {s | ∃ p ∈ Hzero H f, ∃ t ∈ T, s = p * t}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨p, hp, t, ht, rfl⟩ ⟨p', hp', t', ht', rfl⟩
        refine ⟨p * (t * p' * t⁻¹), (Hzero H f).mul_mem hp (hTn t ht p' hp'), t * t',
          T.mul_mem ht ht', by group⟩
      inv_mem' := by
        rintro a ⟨p, hp, t, ht, rfl⟩
        refine ⟨t⁻¹ * p⁻¹ * t⁻¹⁻¹, hTn t⁻¹ (T.inv_mem ht) _ ((Hzero H f).inv_mem hp), t⁻¹, T.inv_mem ht, by group⟩ }
  have hH : H ≤ M := by
    intro h hh
    obtain ⟨q, hq, h1 | h1⟩ := (c.c2.c3.mem_H_iff).1 hh
    · exact ⟨q, hq, 1, one_mem _, by rw [h1]; simp⟩
    · exact ⟨q, hq, x, c.c2.x_mem_T, h1⟩
  have hT : T ≤ M := fun t ht => ⟨1, one_mem _, t, ht, by simp⟩
  intro s hs
  exact (sup_le hH hT) hs

theorem T_eq_cent [Finite G] : T = S ⊓ centralizer ({x} : Set G) := by
  have hTsyl : Sylow2In T (centralizer ({x} : Set G)) := c.c2.c3.out.T_sylow
  have hA2 : IsPGroup 2 ↥(S ⊓ centralizer ({x} : Set G)) := c.S_two.to_le inf_le_left
  obtain ⟨T', hT', hAT'⟩ := SylowIn.exists_ge (p := 2) (inf_le_right : S ⊓ centralizer ({x} : Set G) ≤
    centralizer ({x} : Set G)) hA2
  have hcard := card_eq_of_sylow hTsyl hT'
  have hTA : T ≤ S ⊓ centralizer ({x} : Set G) := le_inf c.T_le_S hTsyl.1
  have h1 := Subgroup.card_le_of_le hTA
  have h2 := Subgroup.card_le_of_le hAT'
  exact Subgroup.eq_of_le_of_card_ge hTA (by omega)

end Ctx2S

theorem freeSec2_bot {P : Subgroup G} (hP : ∀ a ∈ P, a * a = 1)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {y : G} (hy : ∀ g ∈ P, y * g * y⁻¹ ∈ P)
    (hcard : Nat.card ↥(P ⊓ centralizer ({y} : Set G)) ^ 2 = Nat.card P) : FreeSec2 y ⊥ P := by
  refine ⟨bot_le, ?_, ?_, ?_, hy, ?_⟩
  · intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_def]
    have := hcomm a ha b hb
    calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [this]
      _ = 1 := by group
  · intro a ha
    exact Subgroup.mem_bot.2 (hP a ha)
  · intro g hg
    rw [Subgroup.mem_bot] at hg ⊢
    rw [hg]; group
  · have hF : Nat.card (fixSec y ⊥ P) = Nat.card ↥(P ⊓ centralizer ({y} : Set G)) := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro g
      constructor
      · rintro ⟨hgP, hgy⟩
        refine ⟨hgP, ?_⟩
        show g ∈ centralizer ({y} : Set G)
        rw [mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        have h1 : y * g * y⁻¹ * g⁻¹ = 1 := Subgroup.mem_bot.1 hgy
        calc y * g = (y * g * y⁻¹ * g⁻¹) * g * y := by group
          _ = g * y := by rw [h1]; group
      · rintro ⟨hgP, hgC⟩
        refine ⟨hgP, ?_⟩
        rw [Subgroup.mem_bot]
        have := mem_centralizer_iff.1 hgC y rfl
        calc y * g * y⁻¹ * g⁻¹ = (g * y) * y⁻¹ * g⁻¹ := by rw [this]
          _ = 1 := by group
    rw [hF, hcard, Subgroup.card_bot]
    simp


@[expose] def IsFreeConj (x : G) (P : Subgroup G) (y : G) : Prop :=
  (∃ g : G, y = g * x * g⁻¹) ∧ ∀ q ∈ P, y * q * y⁻¹ ∈ P

namespace IsFreeConj

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx2 G x T V H f) {y : G}
include c

theorem sq (hy : IsFreeConj x (Hzero H f) y) : y * y = 1 := by
  obtain ⟨⟨g, rfl⟩, -⟩ := hy
  calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    _ = 1 := by rw [c.c3.x_sq]; group

theorem notin (hy : IsFreeConj x (Hzero H f) y) [Finite G] : y ∉ Hzero H f := by
  obtain ⟨⟨g, rfl⟩, -⟩ := hy
  exact c.not_fused g

theorem card4 [Finite G] (hy : IsFreeConj x (Hzero H f) y) :
    Nat.card ↥(Hzero H f ⊓ centralizer ({y} : Set G)) = 4 := by
  obtain ⟨⟨g, hg⟩, hN⟩ := hy
  exact c.card_cent_free g hg (by rw [hg]; calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
                                                  _ = 1 := by rw [c.c3.x_sq]; group) hN

theorem freeSec [Finite G] (hy : IsFreeConj x (Hzero H f) y) : FreeSec2 y ⊥ (Hzero H f) := by
  refine freeSec2_bot c.P_sq c.P_comm hy.2 ?_
  rw [hy.card4 c, c.P_card]; norm_num

theorem conj_coset [Finite G] (h10 : IG_10_31) (hy : IsFreeConj x (Hzero H f) y) :
    ∀ p ∈ Hzero H f, (p * y) * (p * y) = 1 → ∃ q ∈ Hzero H f, p * y = q * y * q⁻¹ := by
  have hy2 := hy.sq c
  have hyP := hy.notin c
  have hyN : y ∈ normalizer ((Hzero H f : Subgroup G) : Set G) :=
    mem_normalizer_of_involution hy2 hy.2
  exact h10 G (Hzero H f) y 1 (fun i => if i = 0 then ⊥ else Hzero H f) hy2 hyN hyP (by simp)
    (by simp) (by
      intro i hi
      have : i = 0 := by omega
      subst this
      simpa using hy.freeSec c)

theorem lift [Finite G] (h10 : IG_10_31) (hy : IsFreeConj x (Hzero H f) y) {g : G}
    (hg : y * g * y⁻¹ * g⁻¹ ∈ Hzero H f) : ∃ k ∈ Hzero H f, y * (k * g) * y⁻¹ = k * g :=
  lift_cent (hy.sq c) hy.2 (hy.conj_coset c h10) hg

end IsFreeConj

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
