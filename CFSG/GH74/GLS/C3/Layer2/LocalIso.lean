module

public import CFSG.GH74.GLS.C3.Layer2.LocalBasic
public import CFSG.GH74.GLS.C3.Layer2.CentralizerModel

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

namespace IsAConfig

theorem centralizes_of_range_alt (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n)
    (ψ : ↥(centralizer ({x} : Set G)) →* Equiv.Perm (Fin n))
    (hker : ψ.ker = Q.subgroupOf (centralizer ({x} : Set G)))
    (halt : ψ.range = alternatingGroup (Fin n)) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ q ∈ Q, c * q = q * c := by
  obtain ⟨e⟩ := h.K_equiv_alt
  let eK : ↥(K.subgroupOf (centralizer ({x} : Set G))) ≃* alternatingGroup (Fin n) :=
    (Subgroup.subgroupOfEquivOfLe h.K_le_C).trans e
  let ψK : ↥(K.subgroupOf (centralizer ({x} : Set G))) →* Equiv.Perm (Fin n) :=
    ψ.comp (K.subgroupOf (centralizer ({x} : Set G))).subtype
  have hinj : Function.Injective ψK := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have hk' : (k : ↥(centralizer ({x} : Set G))) ∈ ψ.ker := hk
    rw [hker, Subgroup.mem_subgroupOf] at hk'
    have hkK : ((k : ↥(centralizer ({x} : Set G))) : G) ∈ K := k.2
    have : ((k : ↥(centralizer ({x} : Set G))) : G) ∈ K ⊓ Q := ⟨hkK, hk'⟩
    rw [h.K_inf_Q hn, Subgroup.mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  have hcard : Nat.card ↥ψ.range ≤ Nat.card ↥ψK.range := by
    rw [halt, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact (Nat.card_congr eK.toEquiv).symm.le
  have hle : ψK.range ≤ ψ.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨k.1, rfl⟩
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  intro c hc q hq
  have hmem : ψ ⟨c, hc⟩ ∈ ψK.range := by rw [heq]; exact ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := hmem
  have hker' : (⟨c, hc⟩ : ↥(centralizer ({x} : Set G))) * (k : ↥(centralizer ({x} : Set G)))⁻¹ ∈
      ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : ψ (k : ↥(centralizer ({x} : Set G))) = ψ ⟨c, hc⟩ := hk
    rw [this, mul_inv_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hker'
  have hr : c * ((k : ↥(centralizer ({x} : Set G))) : G)⁻¹ ∈ Q := by simpa using hker'
  have hkK : ((k : ↥(centralizer ({x} : Set G))) : G) ∈ K := k.2
  have hkq : ((k : ↥(centralizer ({x} : Set G))) : G) * q =
      q * ((k : ↥(centralizer ({x} : Set G))) : G) :=
    ((h.mem_Q_iff q).1 hq).2 _ hkK
  have hrq : (c * ((k : ↥(centralizer ({x} : Set G))) : G)⁻¹) * q =
      q * (c * ((k : ↥(centralizer ({x} : Set G))) : G)⁻¹) := h.Q_comm hr hq
  set k' : G := ((k : ↥(centralizer ({x} : Set G))) : G) with hk'
  calc c * q = (c * k'⁻¹) * (k' * q) := by group
    _ = (c * k'⁻¹) * (q * k') := by rw [hkq]
    _ = ((c * k'⁻¹) * q) * k' := by group
    _ = (q * (c * k'⁻¹)) * k' := by rw [hrq]
    _ = q * c := by group

theorem exists_equiv_Fgrp (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n)
    (hnt : ∃ t ∈ T, ∃ q ∈ Q, t * q ≠ q * t) :
    ∃ ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n),
      ((ι (xC x) : Fgrp n) : Amb n) = x0 n ∧
      ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp n) : Amb n).1 = 1 ↔ (c : G) ∈ Q) := by
  obtain ⟨ψ, hker, hrange⟩ := h.quotientType
  have hrange' : ψ.range = ⊤ := by
    rcases hrange with h1 | ⟨-, h2⟩
    · exact h1
    · exfalso
      obtain ⟨t, htT, q, hqQ, hne⟩ := hnt
      exact hne (h.centralizes_of_range_alt hn ψ hker h2 t (h.T_le_C htT) q hqQ)
  have hQC : Q ≤ centralizer ({x} : Set G) := h.Q_le_T.trans h.T_le_C
  have hKnorm : (K.subgroupOf (centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.K_le_C).mpr h.C_le_normalizer_K
  have hQnorm : (Q.subgroupOf (centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).mpr h.C_le_normalizer_Q
  obtain ⟨e⟩ := h.K_equiv_alt
  have hQ4 : Nat.card ↥(Q.subgroupOf (centralizer ({x} : Set G))) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv).trans h.card_Q
  obtain ⟨ι, hι1, hι2⟩ := exists_mulEquiv_fgrp hn (K.subgroupOf (centralizer ({x} : Set G)))
    (Q.subgroupOf (centralizer ({x} : Set G))) ((Subgroup.subgroupOfEquivOfLe h.K_le_C).trans e)
    ψ hker hrange' hQ4
    (fun q hq => Subtype.ext (by simpa using h.Q_sq (Subgroup.mem_subgroupOf.1 hq)))
    (fun q hq r hr => Subtype.ext (h.Q_comm (Subgroup.mem_subgroupOf.1 hq)
      (Subgroup.mem_subgroupOf.1 hr)))
    (fun k hk q hq => Subtype.ext
      (((h.mem_Q_iff q).1 (Subgroup.mem_subgroupOf.1 hq)).2 k (Subgroup.mem_subgroupOf.1 hk)))
    (x := xC x) (Subgroup.mem_subgroupOf.2 h.x_mem_Q)
    (fun hx => h.x_ne_one (congrArg Subtype.val hx))
    (fun c => Subtype.ext (mem_centralizer_singleton_iff.1 c.2))
    (by
      obtain ⟨t, htT, q, hqQ, hne⟩ := hnt
      exact ⟨⟨t, h.T_le_C htT⟩, ⟨q, hQC hqQ⟩, Subgroup.mem_subgroupOf.2 hqQ,
        fun hEq => hne (congrArg Subtype.val hEq)⟩)
  refine ⟨ι, hι1, fun c => ?_⟩
  rw [hι2 c, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

theorem exists_equiv_Fgrp_T0
    [NeZero n] (h : IsAConfig n x K T Q S a) (hn : n = 6 ∨ n = 7)
    (hnt : ∃ t ∈ T, ∃ q ∈ Q, t * q ≠ q * t) :
    ∃ ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n),
      ((ι (xC x) : Fgrp n) : Amb n) = x0 n ∧
      (∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp n) : Amb n).1 = 1 ↔ (c : G) ∈ Q)) ∧
      (∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ T ↔ ((ι c : Fgrp n) : Amb n) ∈ T0 n) := by
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨ι, hι1, hι2⟩ := h.exists_equiv_Fgrp hn5 hnt
  obtain ⟨P0, hP0⟩ := isSylow_T0 n hn
  obtain ⟨hTle, hTp, hTidx⟩ := isSylowOf_iff.1 h.sylowT
  have hTm : IsSylowOf 2
      ((T.subgroupOf (centralizer ({x} : Set G))).map ι.toMonoidHom) (⊤ : Subgroup (Fgrp n)) := by
    rw [isSylowOf_iff]
    refine ⟨le_top, hTp.comap_subtype.map _, ?_⟩
    rw [Subgroup.relIndex_top_right,
      Subgroup.index_map_of_bijective (f := ι.toMonoidHom) ι.bijective]
    exact hTidx
  have hP0' : IsSylowOf 2 (P0 : Subgroup (Fgrp n)) ⊤ :=
    isSylowOf_iff.2 ⟨le_top, P0.isPGroup', by
      rw [Subgroup.relIndex_top_right]; exact P0.not_dvd_index⟩
  obtain ⟨g, -, hg⟩ := hTm.exists_mem_conj hP0'
  have hP0mem : ∀ y : Fgrp n, y ∈ (P0 : Subgroup (Fgrp n)) ↔ ((y : Fgrp n) : Amb n) ∈ T0 n := by
    intro y
    rw [← hP0]
    exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).symm
  refine ⟨ι.trans (MulAut.conj g), ?_, fun c => ?_, fun c => ?_⟩
  · have hcen := x0_central n g.2
    show ((g * ι (xC x) * g⁻¹ : Fgrp n) : Amb n) = x0 n
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hι1, hcen, mul_inv_cancel_right]
  · rw [← hι2 c]
    show ((g * ι c * g⁻¹ : Fgrp n) : Amb n).1 = 1 ↔ _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv]
    exact conj_eq_one_iff
  · show (c : G) ∈ T ↔ ((g * ι c * g⁻¹ : Fgrp n) : Amb n) ∈ T0 n
    rw [← hP0mem, hg]
    have : g⁻¹ * (g * ι c * g⁻¹) * g = ι c := by group
    rw [this, Subgroup.mem_map_equiv]
    simp [Subgroup.mem_subgroupOf]

end IsAConfig

end CFSG.GH74.GLS
