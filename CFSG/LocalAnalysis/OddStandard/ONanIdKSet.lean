module

public import CFSG.LocalAnalysis.OddStandard.ONanIdKQuot
public import CFSG.LocalAnalysis.OddStandard.ONanIdKBase

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
open scoped Pointwise

@[expose] def W0L : List AlpE :=
  [⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 2, 0⟩, ⟨0, 0, 2, 2⟩, ⟨0, 1, 0, 1⟩, ⟨0, 1, 0, 3⟩,
    ⟨0, 1, 2, 1⟩, ⟨0, 1, 2, 3⟩, ⟨0, 2, 0, 0⟩, ⟨0, 2, 0, 2⟩, ⟨0, 2, 2, 0⟩, ⟨0, 2, 2, 2⟩,
    ⟨0, 3, 0, 1⟩, ⟨0, 3, 0, 3⟩, ⟨0, 3, 2, 1⟩, ⟨0, 3, 2, 3⟩]

set_option maxRecDepth 100000 in
theorem inW0E_iff : ∀ e : AlpE, InW0E e ↔ e ∈ W0L := by decide +kernel

set_option maxRecDepth 100000 in
theorem W0L_mul : ∀ e ∈ W0L, ∀ f ∈ W0L, e * f ∈ W0L := by decide +kernel

set_option maxRecDepth 100000 in
theorem W0L_inv : ∀ e ∈ W0L, e⁻¹ ∈ W0L := by decide +kernel

theorem W0L_nodup : W0L.Nodup := by decide

set_option maxRecDepth 100000 in
theorem mjA2 : ∀ e ∈ W0L, InY0E ((e * jE)⁻¹ * (jE * e)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem mW0rep : ∀ e ∈ W0L, InY0E e ∨ InY0E ((invE 1)⁻¹ * e) ∨ InY0E ((gen 0 ^ 2)⁻¹ * e) ∨
    InY0E ((gen 1 ^ 2)⁻¹ * e) := by decide +kernel

set_option maxRecDepth 100000 in
theorem mw2 : ∀ e : AlpE, e * y0E = y0E * e →
    e * gen 1 ^ 2 * e⁻¹ ≠ invE 1 ∧ e * gen 1 ^ 2 * e⁻¹ ≠ invE 1 * zc := by
  decide +kernel

theorem mnotY0 : ¬ InY0E (gen 0 ^ 2) ∧ ¬ InY0E (gen 1 ^ 2) ∧ ¬ InY0E (invE 1) := by decide

set_option maxRecDepth 100000 in
theorem mbinv : ∀ e : AlpE, InY0E ((invE 1)⁻¹ * e) → e * e = 1 → e = invE 1 ∨ e = invE 1 * zc := by
  decide +kernel

@[expose] def W0Esub : Subgroup AlpE where
  carrier := {e | e ∈ W0L}
  one_mem' := by decide
  mul_mem' := fun ha hb => W0L_mul _ ha _ hb
  inv_mem' := fun ha => W0L_inv _ ha

theorem card_W0Esub : Nat.card W0Esub = 16 := by
  classical
  have h : Nat.card W0Esub = Nat.card ↥(W0L.toFinset : Set AlpE) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e => by simp [W0Esub])
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup W0L_nodup]
  rfl

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem V_le_Y : alpV v1 v2 v3 ≤ centralizer ({v1 * v3} : Set G) := fun _ hv =>
  mem_centralizer_singleton_iff.2 (D.comm_V hv D.y0_mem_V)

theorem j_mem_Y : invRep v1 v2 v3 s t 3 ∈ centralizer ({v1 * v3} : Set G) := by
  rw [mem_centralizer_singleton_iff, D.j_eq, D.comm_y0_phi]
  exact y0E_comm_jE

omit [Finite G] D in
theorem Q_le_Y : alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G) ≤
    centralizer ({v1 * v3} : Set G) := inf_le_right

omit [Finite G] D in
theorem Y0_le_W0 : zpowers (v1 * v3) ≤ alpW0 v1 v2 v3 := le_sup_right

theorem Y0_le_Q : zpowers (v1 * v3) ≤ alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G) :=
  le_inf (D.Y0_le_V.trans D.V_le_P) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))

theorem card_Y0 : Nat.card (zpowers (v1 * v3)) = 4 := by
  rw [Nat.card_zpowers, D.y0_eq, orderOf_injective D.E.φ D.E.inj, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem alpW0_eq_map : alpW0 v1 v2 v3 = W0Esub.map D.E.φ := by
  ext g
  constructor
  · intro hg
    obtain ⟨e, rfl⟩ := (AlpEmb.mem_alpP_iff D.E).1 (D.V_le_P (D.W0_le_V hg))
    exact Subgroup.mem_map_of_mem _ ((inW0E_iff e).1 ((D.mem_W0_phi e).1 hg))
  · rintro ⟨e, he, rfl⟩
    exact (D.mem_W0_phi e).2 ((inW0E_iff e).2 he)

theorem card_W0 : Nat.card (alpW0 v1 v2 v3) = 16 := by
  rw [D.alpW0_eq_map, card_map_of_injective D.E.inj, card_W0Esub]

theorem exists_phi_W0 {g : G} (hg : g ∈ alpW0 v1 v2 v3) : ∃ e ∈ W0L, D.E.φ e = g := by
  rw [D.alpW0_eq_map] at hg
  obtain ⟨e, he, rfl⟩ := hg
  exact ⟨e, he, rfl⟩

theorem exists_phi_V {g : G} (hg : g ∈ alpV v1 v2 v3) : ∃ e : AlpE, e.d = 0 ∧ D.E.φ e = g := by
  rw [AlpEmb.alpV_eq_map D.E] at hg
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hg
  exact ⟨e, mem_Vsub.1 he, rfl⟩

theorem mem_Vj_iff {g : G} : g ∈ alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3) ↔
    g ∈ alpV v1 v2 v3 ∨ invRep v1 v2 v3 s t 3 * g ∈ alpV v1 v2 v3 := by
  set j := invRep v1 v2 v3 s t 3 with hj
  have hj2 : j * j = 1 := D.rep_sq 3
  have hjN : j ∈ normalizer (alpV v1 v2 v3 : Set G) := D.P_le_normalizer_V (AlpEmb.invRep_mem D.E 3)
  have hle : zpowers j ≤ normalizer (alpV v1 v2 v3 : Set G) := zpowers_le.2 hjN
  constructor
  · intro hg
    rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hle] at hg
    obtain ⟨a, ha, v, hv, rfl⟩ := hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ha
    have hn : j ^ n = 1 ∨ j ^ n = j := by
      have ho : orderOf j = 2 := D.orderOf_rep 3
      rw [← zpow_mod_orderOf, ho]
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · left
        rw [Nat.cast_ofNat, h, zpow_zero]
      · right
        rw [Nat.cast_ofNat, h, zpow_one]
    dsimp only
    rcases hn with h | h
    · left
      rw [h, one_mul]
      exact hv
    · right
      rw [h, ← mul_assoc, hj2, one_mul]
      exact hv
  · rintro (h | h)
    · exact mem_sup_left h
    · have e : g = j * (j * g) := by rw [← mul_assoc, hj2, one_mul]
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers j)) (mem_sup_left h)

theorem j_notMem_V : invRep v1 v2 v3 s t 3 ∉ alpV v1 v2 v3 := by
  rw [D.j_eq, D.mem_V_phi]
  rw [jE_d]
  decide

@[expose] noncomputable def jY : centralizer ({v1 * v3} : Set G) :=
  ⟨invRep v1 v2 v3 s t 3, D.j_mem_Y⟩

theorem jY_sq : D.jY * D.jY = 1 := Subtype.ext (D.rep_sq 3)

theorem mem_of_liftV {k : centralizer ({v1 * v3} : Set G)}
    (h : πQ (v1 * v3) k ∈ liftQ (v1 * v3) (alpV v1 v2 v3)) : (k : G) ∈ alpV v1 v2 v3 :=
  mem_of_πQ_mem_liftQ D.Y0_le_V h

theorem mem_of_liftQ {k : centralizer ({v1 * v3} : Set G)}
    (h : πQ (v1 * v3) k ∈ liftQ (v1 * v3) (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G))) :
    (k : G) ∈ alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G) :=
  mem_of_πQ_mem_liftQ D.Y0_le_Q h

theorem card_C : Nat.card (liftQ (v1 * v3) (alpV v1 v2 v3)) = 16 := by
  have h := card_liftQ D.Y0_le_V D.V_le_Y
  rw [D.card_Y0, AlpEmb.card_alpV D.E] at h
  omega

theorem card_A : Nat.card (liftQ (v1 * v3) (alpW0 v1 v2 v3)) = 4 := by
  have h := card_liftQ Y0_le_W0 (D.W0_le_V.trans D.V_le_Y)
  rw [D.card_Y0, D.card_W0] at h
  omega

theorem card_Sb : Nat.card (liftQ (v1 * v3)
    (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G))) = 64 := by
  have h := card_liftQ D.Y0_le_Q Q_le_Y
  rw [D.card_Y0, D.card_Q] at h
  omega

theorem isSylowOf_Sb : IsSylowOf 2 (liftQ (v1 * v3)
    (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G))) (⊤ : Subgroup (KQ (v1 * v3))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := D.isSylowOf_Q.exists_sylow_eq_subgroupOf
  have h := isSylowOf_top (S.mapSurjective (πQ_surjective (v1 * v3)))
  rw [Sylow.coe_mapSurjective, hS] at h
  exact h

theorem invSettingK :
    InvSetting (liftQ (v1 * v3) (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)))
      (liftQ (v1 * v3) (alpV v1 v2 v3)) (liftQ (v1 * v3) (alpW0 v1 v2 v3))
      (πQ (v1 * v3) D.jY) := by
  set j := invRep v1 v2 v3 s t 3 with hj
  set y0 := v1 * v3 with hy0
  have hjN : j ∈ normalizer (alpV v1 v2 v3 : Set G) :=
    D.P_le_normalizer_V (AlpEmb.invRep_mem D.E 3)
  have hj2 : j * j = 1 := D.rep_sq 3
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj2
  have hπmul : ∀ a b : centralizer ({y0} : Set G), πQ y0 (a * b) = πQ y0 a * πQ y0 b :=
    fun a b => map_mul _ a b
  refine ⟨liftQ_mono le_sup_left, ?_, ?_, liftQ_mono D.W0_le_V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  ·
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hx
    rcases (D.mem_Vj_iff).1 hk with h | h
    · exact Or.inl (πQ_mem_liftQ h)
    · right
      rw [← hπmul]
      refine πQ_mem_liftQ ?_
      show (k : G) * j ∈ alpV v1 v2 v3
      have e : (k : G) * j = j * (j * k) * j⁻¹ := by
        calc (k : G) * j = j * j * k * j := by rw [hj2, one_mul]
          _ = j * (j * k) * j⁻¹ := by rw [hjinv]; group
      rw [e]
      exact conj_mem_V hjN h
  ·
    intro a ha b hb
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 ha
    obtain ⟨k', hk', rfl⟩ := mem_liftQ_iff.1 hb
    rw [← hπmul, ← hπmul]
    congr 1
    exact Subtype.ext (D.comm_V hk hk')
  ·
    intro c hc hc2
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hc
    rw [← hπmul, πQ_eq_one_iff] at hc2
    obtain ⟨e, he, he'⟩ := D.exists_phi_V hk
    refine πQ_mem_liftQ ?_
    rw [← he', D.mem_W0_phi]
    refine mA_of e he ?_
    rw [← D.mem_Y0_iff, map_mul, he']
    exact hc2
  ·
    intro a ha
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 ha
    rw [← hπmul, πQ_eq_one_iff]
    obtain ⟨e, he, he'⟩ := D.exists_phi_W0 hk
    show (k : G) * k ∈ zpowers y0
    rw [← he', ← map_mul, D.mem_Y0_iff]
    exact mA_sq e ((inW0E_iff e).2 he)
  ·
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hx
    rw [← hπmul]
    refine πQ_mem_liftQ ?_
    show (k : G) * k ∈ alpW0 v1 v2 v3
    rcases (D.mem_Vj_iff).1 hk with h | h
    · exact mem_sup_left (D.sq_mem_W h)
    · obtain ⟨e, he, he'⟩ := D.exists_phi_V h
      have hk' : (k : G) = D.E.φ (jE * e) := by
        rw [map_mul, he', ← D.j_eq, ← hj, ← mul_assoc, hj2, one_mul]
      rw [hk', ← map_mul, D.mem_W0_phi]
      exact mSsq e he
  ·
    exact πQ_mem_liftQ (mem_sup_right (mem_zpowers _))
  ·
    intro h
    exact D.j_notMem_V (D.mem_of_liftV h)
  ·
    rw [← hπmul, D.jY_sq, map_one]
  ·
    intro c hc
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hc
    rw [← hπmul, ← hπmul]
    refine πQ_mem_liftQ ?_
    show j * k * j ∈ alpV v1 v2 v3
    have e : j * (k : G) * j = j * k * j⁻¹ := by rw [hjinv]
    rw [e]
    exact conj_mem_V hjN hk
  ·
    intro a ha
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 ha
    rw [← hπmul, ← hπmul, πQ_eq_iff]
    obtain ⟨e, he, he'⟩ := D.exists_phi_W0 hk
    show ((k : G) * j)⁻¹ * (j * k) ∈ zpowers y0
    rw [← he', hj, D.j_eq, ← map_mul, ← map_mul, ← map_inv, ← map_mul, D.mem_Y0_iff]
    exact mjA2 e he
  ·
    intro c hc
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hc
    rw [← map_inv, ← hπmul, ← hπmul, ← hπmul]
    refine πQ_mem_liftQ ?_
    obtain ⟨e, he, he'⟩ := D.exists_phi_V hk
    show (k : G) * j * (k : G)⁻¹ * j ∈ alpW0 v1 v2 v3
    rw [← he', hj, D.j_eq, ← map_inv, ← map_mul, ← map_mul, ← map_mul, D.mem_W0_phi]
    exact mcomm e he
  ·
    intro w hw
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hw
    obtain ⟨e, he, he'⟩ := D.exists_phi_W0 hk
    obtain ⟨hd, hY⟩ := mcomm_surj e ((inW0E_iff e).2 he)
    set c := (commWit.lookup e).getD 1 with hc
    have hcV : D.E.φ c ∈ alpV v1 v2 v3 := (D.mem_V_phi c).2 hd
    refine ⟨πQ y0 ⟨D.E.φ c, D.V_le_Y hcV⟩, πQ_mem_liftQ hcV, ?_⟩
    rw [← map_inv, ← hπmul, ← hπmul, ← hπmul, πQ_eq_iff]
    show (D.E.φ c * j * (D.E.φ c)⁻¹ * j)⁻¹ * k ∈ zpowers y0
    rw [← he', hj, D.j_eq, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_inv, ← map_mul,
      D.mem_Y0_iff]
    exact hY

end FusCtx

end CFSG.OddStandard.ONanRec
