module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Split

public section

namespace CFSG.ComponentClassification.Asc76X.Hall32

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G]

namespace Split

variable {S T : Subgroup G} {z t v : G} {P₁ : Subgroup G}

theorem t_mul_t (h : Setup S T z) (hs : Split S T z t v P₁) : t * t = 1 :=
  (pow_two t).symm.trans (h.sq t hs.t_mem)

theorem z_comm_v (h : Setup S T z) (hs : Split S T z t v P₁) : z * v = v * z :=
  (h.central v hs.v_mem).symm

theorem t_conj_z (h : Setup S T z) (hs : Split S T z t v P₁) : t * z * t⁻¹ = z := by
  rw [h.comm t hs.t_mem z h.mem, mul_inv_cancel_right]

theorem t_conj_v (h : Setup S T z) (hs : Split S T z t v P₁) : t * v * t⁻¹ = z * v := by
  calc t * v * t⁻¹ = t * ((v * t * v⁻¹) * v) * t⁻¹ * t⁻¹ := by group
    _ = (t * t) * z * v * (t * t)⁻¹ := by rw [hs.v_conj_t]; group
    _ = z * v := by rw [hs.t_mul_t h]; group

theorem tv_mul_tv (h : Setup S T z) (hs : Split S T z t v P₁) : t * v * (t * v) = z := by
  calc t * v * (t * v) = t * (v * t * v⁻¹) * (v * v) := by group
    _ = z := by rw [hs.v_conj_t, hs.v_mul_v, mul_one, ← mul_assoc, hs.t_mul_t h, one_mul]

theorem t_comm_v_ne (h : Setup S T z) (hs : Split S T z t v P₁) : t * v ≠ v * t := fun e =>
  h.ne_one (by
    have h1 : v * t * v⁻¹ = t := by rw [← e, mul_inv_cancel_right]
    rw [hs.v_conj_t] at h1
    calc z = t⁻¹ * (t * z) := by group
      _ = t⁻¹ * t := by rw [h1]
      _ = 1 := inv_mul_cancel t)

theorem mem_centralizer (h : Setup S T z) (hs : Split S T z t v P₁) {q : G} (hq : q ∈ P₁) :
    q ∈ centralizer (T : Set G) :=
  mem_centralizer_of_comm h.card h.sq h.mem hs.t_mem h.ne_one hs.t_ne_one hs.t_ne_z
    (hs.comm_z q hq).symm (hs.comm_t q hq).symm

theorem eq_one_of_mem (h : Setup S T z) (hs : Split S T z t v P₁) {q : G} (hq : q ∈ P₁)
    (hqT : q ∈ T) : q = 1 := by
  have hqv := hs.comm_v q hq
  rcases eq_or_of_card_four h.card h.sq h.mem hs.t_mem h.ne_one hs.t_ne_one hs.t_ne_z hqT with
    e | e | e | e
  · exact e
  · rw [e] at hq
    exact absurd hq hs.z_not_mem
  · rw [e] at hqv
    exact absurd hqv (hs.t_comm_v_ne h)
  · rw [e] at hqv
    refine absurd (mul_right_cancel (b := z) ?_) (hs.t_comm_v_ne h)
    calc t * v * z = t * z * v := by rw [mul_assoc, ← hs.z_comm_v h, ← mul_assoc]
      _ = v * (t * z) := hqv
      _ = v * t * z := (mul_assoc _ _ _).symm

theorem t_mul_comm (h : Setup S T z) (hs : Split S T z t v P₁) {x : G}
    (hxv : x * v * x⁻¹ = z * v) : t * x * v = v * (t * x) := by
  have e : t * x * v * (t * x)⁻¹ = v := by
    calc t * x * v * (t * x)⁻¹ = t * (x * v * x⁻¹) * t⁻¹ := by group
      _ = (t * z * t⁻¹) * (t * v * t⁻¹) := by rw [hxv]; group
      _ = v := by rw [hs.t_conj_z h, hs.t_conj_v h, ← mul_assoc, h.z_mul_z, one_mul]
  exact mul_inv_eq_iff_eq_mul.mp e

theorem sq_tvq (h : Setup S T z) (hs : Split S T z t v P₁) {q : G} (hqt : q * t = t * q)
    (hqv : q * v = v * q) : t * (v * q) * (t * (v * q)) = z * (q * q) := by
  calc t * (v * q) * (t * (v * q)) = t * v * (q * t) * v * q := by group
    _ = t * v * t * (q * v) * q := by rw [hqt]; group
    _ = t * v * (t * v) * (q * q) := by rw [hqv]; group
    _ = z * (q * q) := by rw [hs.tv_mul_tv h]

theorem ne_z_mul_sq (hs : Split S T z t v P₁) {q : G} (hq : q ∈ P₁) : 1 ≠ z * (q * q) := by
  intro e
  apply hs.z_not_mem
  have e2 : z = (q * q)⁻¹ := eq_inv_iff_mul_eq_one.mpr e.symm
  rw [e2]
  exact inv_mem (mul_mem hq hq)

variable [Finite G]

theorem conj_mem (h : Setup S T z) (hs : Split S T z t v P₁) {τ g : G} (hτ : τ ∈ T)
    (huS : g⁻¹ * τ * g ∈ S)
    (huv : g⁻¹ * τ * g * v * (g⁻¹ * τ * g)⁻¹ = v ∨
      g⁻¹ * τ * g * v * (g⁻¹ * τ * g)⁻¹ = z * v) :
    g⁻¹ * τ * g ∈ T ∨ g⁻¹ * τ * g = v ∨ g⁻¹ * τ * g = z * v := by
  by_cases huC : g⁻¹ * τ * g ∈ centralizer (T : Set G)
  · exact Or.inl (h.mem_of_conj_mem_centralizer hτ huC)
  have hzC : z ∈ centralizer (T : Set G) :=
    mem_centralizer_iff.mpr fun y hy => h.comm y hy z h.mem
  have htC : t ∈ centralizer (T : Set G) :=
    mem_centralizer_iff.mpr fun y hy => h.comm y hy t hs.t_mem
  have hu2 : g⁻¹ * τ * g * (g⁻¹ * τ * g) = 1 := by
    calc g⁻¹ * τ * g * (g⁻¹ * τ * g) = g⁻¹ * (τ * τ) * g := by group
      _ = 1 := by rw [(pow_two τ).symm.trans (h.sq τ hτ)]; group
  have hzq : ∀ q ∈ P₁, ∀ g' : G, g'⁻¹ * τ * g' = z * q → q = 1 := fun q hq g' e => by
    have h1 : g'⁻¹ * τ * g' ∈ T := h.mem_of_conj_mem_centralizer hτ
      (by rw [e]; exact mul_mem hzC (hs.mem_centralizer h hq))
    rw [e] at h1
    refine hs.eq_one_of_mem h hq ?_
    have e2 : q = z * (z * q) := by rw [← mul_assoc, h.z_mul_z, one_mul]
    rw [e2]
    exact mul_mem h.mem h1
  rcases huv with huv | huv
  · obtain ⟨q, hq, e⟩ := hs.decomp _ huS (mul_inv_eq_iff_eq_mul.mp huv)
    rcases e with e | e | e | e
    · exact (huC (by rw [e]; exact hs.mem_centralizer h hq)).elim
    · exact (huC (by rw [e]; exact mul_mem hzC (hs.mem_centralizer h hq))).elim
    · obtain ⟨g', hg'⟩ := hs.conj_vp q hq
      have h1 := hzq q hq (g * g') (by rw [← hg', ← e]; group)
      right; left
      rw [e, h1, mul_one]
    · obtain ⟨g', hg'⟩ := hs.conj_zvp q hq
      have h1 := hzq q hq (g * g') (by rw [← hg', ← e]; group)
      right; right
      rw [e, h1, mul_one]
  · exfalso
    have htu := hs.t_mul_comm h huv
    obtain ⟨q, hq, e⟩ := hs.decomp _ (mul_mem (h.le hs.t_mem) huS) htu
    have hu : g⁻¹ * τ * g = t * (t * (g⁻¹ * τ * g)) := by
      rw [← mul_assoc, hs.t_mul_t h, one_mul]
    have hqt := hs.comm_t q hq
    have hqv := hs.comm_v q hq
    have hqz := hs.comm_z q hq
    rcases e with e | e | e | e
    · exact huC (by rw [hu, e]; exact mul_mem htC (hs.mem_centralizer h hq))
    · exact huC (by
        rw [hu, e]; exact mul_mem htC (mul_mem hzC (hs.mem_centralizer h hq)))
    ·
      have h1 := hs.sq_tvq h hqt hqv
      rw [← e, ← hu, hu2] at h1
      exact hs.ne_z_mul_sq hq h1
    ·
      have hzqt : z * q * t = t * (z * q) := by
        calc z * q * t = z * (q * t) := mul_assoc _ _ _
          _ = z * (t * q) := by rw [hqt]
          _ = (z * t) * q := (mul_assoc _ _ _).symm
          _ = (t * z) * q := by rw [h.comm z h.mem t hs.t_mem]
          _ = t * (z * q) := mul_assoc _ _ _
      have hzqv : z * q * v = v * (z * q) := by
        calc z * q * v = z * (q * v) := mul_assoc _ _ _
          _ = z * (v * q) := by rw [hqv]
          _ = (z * v) * q := (mul_assoc _ _ _).symm
          _ = (v * z) * q := by rw [hs.z_comm_v h]
          _ = v * (z * q) := mul_assoc _ _ _
      have h1 := hs.sq_tvq h hzqt hzqv
      have e2 : z * v * q = v * (z * q) := by rw [hs.z_comm_v h, mul_assoc]
      have e3 : z * q * (z * q) = q * q := by
        calc z * q * (z * q) = z * (q * z) * q := by group
          _ = z * (z * q) * q := by rw [hqz]
          _ = q * q := by rw [← mul_assoc z z q, h.z_mul_z, one_mul]
      rw [← e2, ← e, ← hu, hu2, e3] at h1
      exact hs.ne_z_mul_sq hq h1

theorem conj_v (h : Setup S T z) (hs : Split S T z t v P₁) :
    ∀ s ∈ S, s * v * s⁻¹ = v ∨ s * v * s⁻¹ = z * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.z_mul_z
  let N : Subgroup G :=
    { carrier := {x | x ∈ S ∧ (x * v * x⁻¹ = v ∨ x * v * x⁻¹ = z * v)}
      mul_mem' := by
        rintro a b ⟨haS, ha⟩ ⟨hbS, hb⟩
        refine ⟨mul_mem haS hbS, ?_⟩
        have haz : a * z * a⁻¹ = z := by rw [h.central a haS, mul_inv_cancel_right]
        have e : a * b * v * (a * b)⁻¹ = a * (b * v * b⁻¹) * a⁻¹ := by group
        rcases hb with hb | hb
        · rw [e, hb]; exact ha
        · have e2 : a * (z * v) * a⁻¹ = (a * z * a⁻¹) * (a * v * a⁻¹) := by group
          rw [e, hb, e2, haz]
          rcases ha with ha | ha
          · exact Or.inr (by rw [ha])
          · exact Or.inl (by rw [ha, ← mul_assoc, hz2, one_mul])
      one_mem' := ⟨one_mem S, Or.inl (by group)⟩
      inv_mem' := by
        rintro a ⟨haS, ha⟩
        refine ⟨inv_mem haS, ?_⟩
        have haz : a⁻¹ * z * a = z := by
          rw [mul_assoc, ← h.central a haS, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [inv_inv]
        rcases ha with ha | ha
        · left
          calc a⁻¹ * v * a = a⁻¹ * (a * v * a⁻¹) * a := by rw [ha]
            _ = v := by group
        · right
          calc a⁻¹ * v * a = a⁻¹ * (z * (z * v)) * a := by rw [← mul_assoc z z v, hz2, one_mul]
            _ = a⁻¹ * z * a * (a⁻¹ * (a * v * a⁻¹) * a) := by rw [ha]; group
            _ = z * v := by rw [haz]; group }
  have hNS : ∀ x : S, x ∈ N.subgroupOf S ↔
      (x : G) * v * (x : G)⁻¹ = v ∨ (x : G) * v * (x : G)⁻¹ = z * v :=
    fun x => ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp h.sylow).2
  have : Group.IsNilpotent S := hS2.isNilpotent
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent) (N.subgroupOf S) ?_
  · intro s hs'
    have h1 : (⟨s, hs'⟩ : S) ∈ N.subgroupOf S := by rw [htop]; exact mem_top _
    exact (hNS _).mp h1
  · refine le_antisymm (fun s hsN => ?_) le_normalizer
    have hvN : (⟨v, hs.v_mem⟩ : S) ∈ N.subgroupOf S :=
      (hNS _).mpr (Or.inl (show v * v * v⁻¹ = v by group))
    have h1 := (hNS _).mp ((mem_normalizer_iff.mp hsN _).mp hvN)
    simp only [coe_mul, coe_inv] at h1
    obtain ⟨n, hn⟩ := hs.v_conj
    have hu : (n * (s : G)⁻¹)⁻¹ * z * (n * (s : G)⁻¹) = (s : G) * v * (s : G)⁻¹ := by
      rw [← hn]; group
    have huS : (s : G) * v * (s : G)⁻¹ ∈ S := mul_mem (mul_mem s.2 hs.v_mem) (inv_mem s.2)
    have h2 := hs.conj_mem h h.mem (g := n * (s : G)⁻¹) (by rw [hu]; exact huS)
      (by rw [hu]; exact h1)
    rw [hu] at h2
    rcases h2 with e | e | e
    · exfalso
      have hvT : v ∈ T := by
        have h3 := (mem_normalizer_iff.mp (h.le_normalizer (inv_mem s.2)) _).mp e
        rw [inv_inv] at h3
        have e2 : (s : G)⁻¹ * ((s : G) * v * (s : G)⁻¹) * s = v := by group
        rwa [e2] at h3
      exact hs.v_not_mem (mem_centralizer_iff.mpr fun y hy => h.comm y hy v hvT)
    · exact (hNS s).mpr (Or.inl e)
    · exact (hNS s).mpr (Or.inr e)

theorem conj_mem_of_mem (h : Setup S T z) (hs : Split S T z t v P₁) {τ g : G} (hτ : τ ∈ T)
    (huS : g⁻¹ * τ * g ∈ S) : g⁻¹ * τ * g ∈ T ∨ g⁻¹ * τ * g = v ∨ g⁻¹ * τ * g = z * v :=
  hs.conj_mem h hτ huS (hs.conj_v h _ huS)

theorem sq_mem (h : Setup S T z) (hs : Split S T z t v P₁) {s : G} (hsS : s ∈ S) :
    ∃ q ∈ P₁, s * s = q * q ∨ s * s = z * (q * q) := by
  have hz2 := h.z_mul_z
  have hv2 := hs.v_mul_v
  have ht2 := hs.t_mul_t h
  have hzv := hs.z_comm_v h
  have hzt : z * t = t * z := h.comm z h.mem t hs.t_mem
  have key : ∀ a q : G, Commute q a → a * q * (a * q) = a * a * (q * q) :=
    fun a q hqa => hqa.mul_mul_mul_comm a q
  have hzvzv : z * v * (z * v) = 1 := by
    rw [key z v hzv.symm, hz2, hv2, one_mul]
  have htz2 : t * z * (t * z) = 1 := by
    rw [key t z hzt, ht2, hz2, one_mul]
  have htzv2 : t * (z * v) * (t * (z * v)) = z := by
    have e : t * (z * v) = t * v * z := by rw [hzv, mul_assoc]
    have hc' : z * (t * v) = t * v * z := by
      calc z * (t * v) = (z * t) * v := (mul_assoc _ _ _).symm
        _ = (t * z) * v := by rw [hzt]
        _ = t * (z * v) := mul_assoc _ _ _
        _ = t * (v * z) := by rw [hzv]
        _ = t * v * z := (mul_assoc _ _ _).symm
    have hc : Commute z (t * v) := hc'
    rw [e, key (t * v) z hc, hs.tv_mul_tv h, hz2, mul_one]
  rcases hs.conj_v h s hsS with e | e
  · obtain ⟨q, hq, e'⟩ := hs.decomp s hsS (mul_inv_eq_iff_eq_mul.mp e)
    have cz : Commute q z := hs.comm_z q hq
    have cv : Commute q v := hs.comm_v q hq
    refine ⟨q, hq, Or.inl ?_⟩
    rcases e' with e' | e' | e' | e'
    · rw [e']
    · rw [e', key z q cz, hz2, one_mul]
    · rw [e', key v q cv, hv2, one_mul]
    · rw [e', key (z * v) q (cz.mul_right cv), hzvzv, one_mul]
  · obtain ⟨q, hq, e'⟩ := hs.decomp _ (mul_mem (h.le hs.t_mem) hsS) (hs.t_mul_comm h e)
    have hu : s = t * (t * s) := by rw [← mul_assoc, ht2, one_mul]
    have cz : Commute q z := hs.comm_z q hq
    have cv : Commute q v := hs.comm_v q hq
    have ct : Commute q t := hs.comm_t q hq
    refine ⟨q, hq, ?_⟩
    rcases e' with e' | e' | e' | e'
    · left; rw [hu, e', key t q ct, ht2, one_mul]
    · left; rw [hu, e', ← mul_assoc t z q, key (t * z) q (ct.mul_right cz), htz2, one_mul]
    · right; rw [hu, e', ← mul_assoc t v q, key (t * v) q (ct.mul_right cv), hs.tv_mul_tv h]
    · right
      rw [hu, e', ← mul_assoc t (z * v) q, key (t * (z * v)) q (ct.mul_right (cz.mul_right cv)),
        htzv2]

end Split

end CFSG.ComponentClassification.Asc76X.Hall32
