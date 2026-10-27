module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transfer
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_10a
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transport
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129b

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

structure Hyp129 (G : Type) [Group G] [Finite G] (x z : G) (S T P Q Rd F : Subgroup G) : Prop where
  base : HBase G x S T P Q Rd F
  hz : HZ T P z
  h127 : After127 G x z S T P Q Rd F
  P4 : IP_P_four P
  f3 : IP_f3 x P
  zV : IP_z_V z P
  exp : IP_cent_P_exp T P Q
  conj : IP_P_conj x z P
  trans : IP_P_trans P Q Rd
  dih : IP_Rd_dihedral x Rd
  fuse : IP_Rd_fuse x P Rd
  Tn : IP_T_normal x z T P Rd
  IV3 : IV3_12_8c_sylow x S T P
  IG : IG_15_15
  S2 : T.relIndex S = 2

structure Ph0 (G : Type) [Group G] [Finite G] (x z : G) (S T P : Subgroup G) (a : G) : Prop where
  a_mem : a ∈ S
  a_not : a ∉ T
  a_norm : ∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T
  a_sq : a * a ∈ T
  card4 : Nat.card (omegaZ T) = 4
  xa : a * x * a⁻¹ = x * z
  xa' : a⁻¹ * x * a = x * z
  za : a * z * a⁻¹ = z
  K1 : ∀ V : Subgroup G, V ≤ P → IsFour V → ∀ s ∈ S, s ∉ T →
    s ∉ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)

section

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

namespace Hyp129

variable (H : Hyp129 G x z S T P Q Rd F)
include H

theorem T_normal_S : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T := by
  intro s hs t ht
  have hidx : (T.subgroupOf S).index = 2 := H.S2
  have hN := Subgroup.normal_of_index_eq_two hidx
  exact hN.conj_mem ⟨t, H.base.T_le_S ht⟩ ht ⟨s, hs⟩

theorem coset_eq {s s' : G} (hs : s ∈ S) (hs' : s' ∈ S) (hsT : s ∉ T) (hsT' : s' ∉ T) :
    s⁻¹ * s' ∈ T := by
  rcases pigeon_of_relIndex_two H.S2 hs hs' with h | h | h
  · exact absurd h hsT
  · exact absurd h hsT'
  · exact h

theorem ph0 : ∃ a : G, Ph0 G x z S T P a := by
  obtain ⟨a, haS, haT, hanorm, hasq⟩ := H.h127.exists_a
  have h8 := lemma_12_8 G x S T P Q Rd F z H.base H.hz H.h127 H.P4 H.f3 H.zV H.exp a haS haT
    hanorm hasq
  have hcos : ∀ s ∈ S, s ∉ T → a⁻¹ * s ∈ T := fun s hs hsT => H.coset_eq haS hs haT hsT
  have K1 : ∀ V : Subgroup G, V ≤ P → IsFour V → ∀ s ∈ S, s ∉ T →
      s ∉ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro V hVP hV s hs hsT hsN
    have hsyl := H.IV3 H.S2 V hVP hV ⟨s, hs, hsT, hsN⟩
    have ht : s⁻¹ * a ∈ T := by
      have := T.inv_mem (hcos s hs hsT)
      simpa using this
    have hc := (h8.2.2 V hVP hV ⟨s⁻¹ * a, ht, by
      have : a * (s⁻¹ * a)⁻¹ = s := by group
      rw [this]; exact hsN⟩).2 hsyl
    rw [H.S2] at hc
    omega
  have card4 : Nat.card (omegaZ T) = 4 := by
    rcases H.h127.card_Z with h4 | h8'
    · exact h4
    · exfalso
      obtain ⟨V, hVP, hV⟩ := H.P4
      have hTZ := H.h127.T_eq_Z h8'
      have hT8 : Nat.card ↥T = 8 := (congrArg (fun K : Subgroup G => Nat.card ↥K) hTZ).trans h8'
      have hEq : V ⊔ Subgroup.zpowers x = T :=
        Subgroup.eq_of_le_of_card_ge (E_le_T H.base hVP) (by rw [hT8, card_E H.base hVP hV])
      apply K1 V hVP hV a haS haT
      rw [hEq]
      exact Subgroup.mem_normalizer_iff.2 hanorm
  obtain ⟨w, ⟨hwZ, hwP⟩, _, hxw⟩ := h8.1
  have hwz : w = z := by
    rcases H.base.P_inf_Z H.hz card4 hwP hwZ with h1 | h1
    · exact absurd h1 ‹w ≠ 1›
    · exact h1
  rw [hwz] at hxw
  have hxa : a * x * a⁻¹ = x * z := by
    have hxc : x * (a * a) = (a * a) * x := H.base.x_central _ hasq
    calc a * x * a⁻¹ = a⁻¹ * ((a * a) * x * (a * a)⁻¹) * a := by group
      _ = a⁻¹ * (x * (a * a) * (a * a)⁻¹) * a := by rw [← hxc]
      _ = a⁻¹ * x * a := by group
      _ = x * z := hxw
  have hza : a * z * a⁻¹ = z := by
    have hxc : x * (a * a) = (a * a) * x := H.base.x_central _ hasq
    have hxz : x * z = z * x := (H.hz.z_central x H.base.x_mem_T).symm
    have h1 : a * (a * x * a⁻¹) * a⁻¹ = x := by
      calc a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
        _ = x * (a * a) * (a * a)⁻¹ := by rw [← hxc]
        _ = x := by group
    have hzdef : z = x * (a * x * a⁻¹) := by
      rw [hxa]
      calc z = x * x * z := by rw [H.base.x_sq, one_mul]
        _ = x * (x * z) := by rw [mul_assoc]
    calc a * z * a⁻¹ = (a * x * a⁻¹) * (a * (a * x * a⁻¹) * a⁻¹) := by
          nth_rewrite 1 [hzdef]; group
      _ = (x * z) * x := by rw [h1, hxa]
      _ = (z * x) * x := by rw [hxz]
      _ = z := by rw [mul_assoc, H.base.x_sq, mul_one]
  exact ⟨a, haS, haT, hanorm, hasq, card4, hxa, hxw, hza, K1⟩

end Hyp129

namespace Ph0

theorem sx (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a) {s : G} (hs : s ∈ S)
    (hsT : s ∉ T) : s * x * s⁻¹ = x * z := by
  have ht : a⁻¹ * s ∈ T := H.coset_eq A.a_mem hs A.a_not hsT
  have hxt : x * (a⁻¹ * s) = (a⁻¹ * s) * x := H.base.x_central _ ht
  calc s * x * s⁻¹ = a * ((a⁻¹ * s) * x * (a⁻¹ * s)⁻¹) * a⁻¹ := by group
    _ = a * (x * (a⁻¹ * s) * (a⁻¹ * s)⁻¹) * a⁻¹ := by rw [← hxt]
    _ = a * x * a⁻¹ := by group
    _ = x * z := A.xa

theorem sz (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a) (s : G) (hs : s ∈ S) :
    s * z * s⁻¹ = z := by
  by_cases hsT : s ∈ T
  · have h1 := H.hz.z_central s hsT
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [h1]
      _ = z := by group
  · have ht : a⁻¹ * s ∈ T := H.coset_eq A.a_mem hs A.a_not hsT
    have hzt : z * (a⁻¹ * s) = (a⁻¹ * s) * z := H.hz.z_central _ ht
    calc s * z * s⁻¹ = a * ((a⁻¹ * s) * z * (a⁻¹ * s)⁻¹) * a⁻¹ := by group
      _ = a * (z * (a⁻¹ * s) * (a⁻¹ * s)⁻¹) * a⁻¹ := by rw [← hzt]
      _ = a * z * a⁻¹ := by group
      _ = z := A.za

theorem W_le_T (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a) {V : Subgroup G}
    (hVP : V ≤ P) : Hconj a V ≤ T := by
  intro y hy
  have : a * y * a⁻¹ ∈ T := H.base.P_le_T (hVP hy)
  exact (A.a_norm y).2 this

omit [Finite G] in
theorem W_isFour {a : G} {V : Subgroup G} (hV : IsFour V) : IsFour (Hconj a V) :=
  ⟨hV.1.hconj a, by rw [Hconj_card]; exact hV.2⟩

theorem z_mem_W {a : G} (A : Ph0 G x z S T P a) {V : Subgroup G} (hzV : z ∈ V) :
    z ∈ Hconj a V := by
  rw [mem_Hconj, A.za]; exact hzV

theorem x_not_mem_W (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a)
    {V : Subgroup G} (hVP : V ≤ P) (hzV : z ∈ V) : x ∉ Hconj a V := by
  intro hx
  rw [mem_Hconj, A.xa] at hx
  apply H.base.x_not_mem_P
  have : x = (x * z) * z⁻¹ := by group
  rw [this]
  exact P.mul_mem (hVP hx) (P.inv_mem (hVP hzV))

theorem W_le_Rd (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a) {V : Subgroup G}
    (hVP : V ≤ P) (hV : IsFour V) : Hconj a V ≤ Rd := by
  intro y hy
  have hyT : y ∈ T := W_le_T H A hVP hy
  have hy2 : y * y = 1 := ((W_isFour hV).1 y hy).1
  exact H.h127.omega1_le (Subgroup.subset_closure ⟨hyT, hy2⟩)

end Ph0

namespace Hyp129

variable (H : Hyp129 G x z S T P Q Rd F)
include H

theorem P_le_Rd : P ≤ Rd := le_sup_left.trans H.base.R_le_Rd

theorem x_mem_Rd : x ∈ Rd := H.base.R_le_Rd (Subgroup.mem_sup_right H.base.x_mem_Q)

theorem EV_le_Rd {V : Subgroup G} (hVP : V ≤ P) : V ⊔ Subgroup.zpowers x ≤ Rd :=
  sup_le (hVP.trans H.P_le_Rd) ((Subgroup.zpowers_le).2 H.x_mem_Rd)

theorem EV_isElemAb2 {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) :
    IsElemAb2 (V ⊔ Subgroup.zpowers x) :=
  isElemAb2_sup_zpowers hV H.base.x_sq (fun u hu => H.base.x_central u (H.base.P_le_T (hVP hu)))

theorem EV_card {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) :
    Nat.card (V ⊔ Subgroup.zpowers x : Subgroup G) = 8 :=
  card_E H.base hVP hV

end Hyp129

namespace Ph0

theorem EV_conj (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a) {V : Subgroup G}
    (hzV : z ∈ V) :
    Hconj a (V ⊔ Subgroup.zpowers x) = Hconj a V ⊔ Subgroup.zpowers x := by
  rw [Hconj_sup]
  apply le_antisymm
  · refine sup_le le_sup_left (fun y hy => ?_)
    rw [mem_Hconj] at hy
    rcases zpowers_sq_cases H.base.x_sq hy with e | e
    · have : y = 1 := by
        have h1 : a * y * a⁻¹ = 1 := e
        have h2 : y = a⁻¹ * (a * y * a⁻¹) * a := by group
        rw [h2, h1]; group
      rw [this]; exact Subgroup.one_mem _
    · have hy' : y = x * z := by
        have : y = a⁻¹ * (a * y * a⁻¹) * a := by group
        rw [this, e, A.xa']
      rw [hy']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
        (Subgroup.mem_sup_left (z_mem_W A hzV))
  · refine sup_le le_sup_left ((Subgroup.zpowers_le).2 ?_)
    have hxz : x * z ∈ Hconj a (Subgroup.zpowers x) := by
      rw [mem_Hconj]
      have : a * (x * z) * a⁻¹ = x := by
        calc a * (x * z) * a⁻¹ = (a * x * a⁻¹) * (a * z * a⁻¹) := by group
          _ = (x * z) * z := by rw [A.xa, A.za]
          _ = x := by rw [mul_assoc, H.hz.z_sq, mul_one]
      rw [this]; exact Subgroup.mem_zpowers x
    have hxmem : (x * z) * z⁻¹ ∈ Hconj a V ⊔ Hconj a (Subgroup.zpowers x) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right hxz)
        (Subgroup.mem_sup_left ((Hconj a V).inv_mem (z_mem_W A hzV)))
    simpa using hxmem

theorem EW_isElemAb2 (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a)
    {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) :
    IsElemAb2 (Hconj a V ⊔ Subgroup.zpowers x) :=
  isElemAb2_sup_zpowers (W_isFour hV) H.base.x_sq
    (fun u hu => H.base.x_central u (W_le_T H A hVP hu))

theorem EW_card (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a) {V : Subgroup G}
    (hVP : V ≤ P) (hV : IsFour V) (hzV : z ∈ V) :
    Nat.card (Hconj a V ⊔ Subgroup.zpowers x : Subgroup G) = 8 :=
  card_sup_zpowers_four (W_isFour hV) H.base.x_sq H.base.x_ne_one (x_not_mem_W H A hVP hzV)
    (fun u hu => H.base.x_central u (W_le_T H A hVP hu))

theorem EW_le_Rd (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a) {V : Subgroup G}
    (hVP : V ≤ P) (hV : IsFour V) : Hconj a V ⊔ Subgroup.zpowers x ≤ Rd :=
  sup_le (W_le_Rd H A hVP hV) ((Subgroup.zpowers_le).2 H.x_mem_Rd)

theorem not_Tconj (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a)
    {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) {t : G} (ht : t ∈ T) :
    Hconj a (V ⊔ Subgroup.zpowers x) ≠ Hconj t (V ⊔ Subgroup.zpowers x) := by
  intro e
  have e2 : Hconj (t * a⁻¹) (V ⊔ Subgroup.zpowers x) = V ⊔ Subgroup.zpowers x := by
    rw [← Hconj_mul, ← e, Hconj_inv_Hconj]
  refine A.K1 V hVP hV (t * a⁻¹) (S.mul_mem (H.base.T_le_S ht) (S.inv_mem A.a_mem)) ?_
    (mem_normalizer_iff_Hconj.2 e2)
  intro htT
  apply A.a_not
  have h1 : a⁻¹ ∈ T := by
    have := T.mul_mem (T.inv_mem ht) htT
    simpa using this
  simpa using T.inv_mem h1

end Ph0

end

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
