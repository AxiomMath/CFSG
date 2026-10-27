module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_4

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

@[expose] def IsConjX (x a : G) : Prop := ∃ k : G, k⁻¹ * x * k = a

omit [Finite G] in
theorem IsConjX.conj {x a : G} (ha : IsConjX x a) (m : G) : IsConjX x (m * a * m⁻¹) := by
  obtain ⟨k, rfl⟩ := ha
  refine ⟨k * m⁻¹, ?_⟩
  group

theorem HBase.exists_pow_two_pow (h : HBase G x S T P Q Rd F) {q : G} (hq : q ∈ T) :
    ∃ k : ℕ, q ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := h.T_pgroup ⟨q, hq⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem HBase.exists_sq_eq_x_aux (h : HBase G x S T P Q Rd F) (hP4 : IP_P_four P) (Pr : G → Prop)
    (hPr : ∀ q, Pr q → Pr (q * q)) :
    ∀ (k : ℕ) (q : G), q ∈ Q → q ^ (2 ^ k) = 1 → Pr q → q ≠ 1 → q ≠ x →
      ∃ q₂ ∈ Q, q₂ * q₂ = x ∧ Pr q₂ := by
  intro k
  induction k with
  | zero =>
    intro q _ hq _ hq1 _
    simp at hq
    exact absurd hq hq1
  | succ k ih =>
    intro q hqQ hq hPrq hq1 hqx
    have hrQ : q * q ∈ Q := Q.mul_mem hqQ hqQ
    have hr : (q * q) ^ (2 ^ k) = 1 := by
      have : (q * q) ^ (2 ^ k) = q ^ (2 ^ (k + 1)) := by
        rw [← pow_two, ← pow_mul, ← pow_succ']
      rw [this]; exact hq
    by_cases hrr : (q * q) * (q * q) = 1
    · rcases h.Q_invol hP4 hrQ hrr with e | e
      · rcases h.Q_invol hP4 hqQ e with e1 | e1
        · exact absurd e1 hq1
        · exact absurd e1 hqx
      · exact ⟨q, hqQ, e, hPrq⟩
    · have hr1 : q * q ≠ 1 := fun e => hrr (by rw [e]; simp)
      have hrx : q * q ≠ x := fun e => hrr (by rw [e]; exact h.x_sq)
      exact ih (q * q) hrQ hr (hPr q hPrq) hr1 hrx

theorem HBase.exists_sq_eq_x (h : HBase G x S T P Q Rd F) (hP4 : IP_P_four P)
    (hQ : Q ≠ Subgroup.zpowers x) : ∃ q ∈ Q, q * q = x := by
  have hlt : Subgroup.zpowers x < Q :=
    lt_of_le_of_ne ((Subgroup.zpowers_le).2 h.x_mem_Q) (Ne.symm hQ)
  obtain ⟨q, hqQ, hqx⟩ := IsConcreteLE.exists_of_lt hlt
  have hq1 : q ≠ 1 := fun e => hqx (by rw [e]; exact Subgroup.one_mem _)
  have hqx' : q ≠ x := fun e => hqx (by rw [e]; exact Subgroup.mem_zpowers x)
  obtain ⟨k, hk⟩ := h.exists_pow_two_pow (h.Q_le_T hqQ)
  obtain ⟨q₂, hq₂, he, _⟩ :=
    h.exists_sq_eq_x_aux hP4 (fun _ => True) (fun _ _ => trivial) k q hqQ hk trivial hq1 hqx'
  exact ⟨q₂, hq₂, he⟩

omit [Finite G] in
theorem mem_sup_zpowers_of_normalIn {N T : Subgroup G} (hN : NormalIn N T) {b : G} (hb : b ∈ T)
    {y : G} (hy : y ∈ N ⊔ Subgroup.zpowers b) : ∃ a ∈ Subgroup.zpowers b, ∃ p ∈ N, y = a * p := by
  have hu : b ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hN.2 b hb r hr, fun hr => ?_⟩
    have := hN.inv_conj hb hr
    have e : b⁻¹ * (b * r * b⁻¹) * b = r := by group
    rwa [e] at this
  have hnorm : Subgroup.zpowers b ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.zpowers_le).2 hu
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers b) N hnorm
  rw [sup_comm] at hy
  have hy' : y ∈ (↑(Subgroup.zpowers b ⊔ N) : Set G) := hy
  rw [hset] at hy'
  obtain ⟨a, ha, p, hp, e⟩ := Set.mem_mul.1 hy'
  exact ⟨a, ha, p, hp, e.symm⟩

theorem HBase.mem_sup_zpowers (h : HBase G x S T P Q Rd F) {u : G} (huT : u ∈ T) {y : G}
    (hy : y ∈ P ⊔ Subgroup.zpowers u) : ∃ a ∈ Subgroup.zpowers u, ∃ p ∈ P, y = a * p :=
  mem_sup_zpowers_of_normalIn h.P_normal huT hy

theorem HBase.Pstar_inf_Q (h : HBase G x S T P Q Rd F) {u : G} (huT : u ∈ T) (hu2 : u * u = 1)
    (huR : u ∉ P ⊔ Q) {y : G} (hy : y ∈ P ⊔ Subgroup.zpowers u) (hyQ : y ∈ Q) : y = 1 := by
  obtain ⟨a, ha, p, hp, e⟩ := h.mem_sup_zpowers huT hy
  rcases zpowers_sq_cases hu2 ha with e1 | e1
  · rw [e1, one_mul] at e
    have hyP : y ∈ P := by rw [e]; exact hp
    exact h.eq_one_of_mem_P_Q hyP hyQ
  · exfalso
    apply huR
    rw [e1] at e
    have : u = y * p⁻¹ := by rw [e]; group
    rw [this]
    exact (P ⊔ Q).mul_mem (Subgroup.mem_sup_right hyQ) ((P ⊔ Q).inv_mem (Subgroup.mem_sup_left hp))

theorem HBase.star (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (h4 : Nat.card (omegaZ T) = 4)
    (hwc : ∀ g : G, g⁻¹ * x * g ∈ omegaZ T → g⁻¹ * x * g = x)
    {g : G} (huT : g⁻¹ * x * g ∈ T) (hux : g⁻¹ * x * g ≠ x) :
    ∃ c₀ : G, (c₀ = z ∨ c₀ = x * z) ∧ ¬ IsConjX x (g⁻¹ * x * g * c₀) := by
  set u := g⁻¹ * x * g with hu
  have hu2 : u * u = 1 := by
    have : u * u = g⁻¹ * (x * x) * g := by rw [hu]; group
    rw [this, h.x_sq]; group
  have hu1 : u ≠ 1 := by
    intro e
    apply h.x_ne_one
    have : x = g * u * g⁻¹ := by rw [hu]; group
    rw [this, e]; group
  have huZ : u ∉ omegaZ T := fun hZ => hux (hwc g hZ)
  have hcomm : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ omegaZ T, a * b = b * a := by
    intro a ha b hb
    exact (hb.2.2 a ((Subgroup.zpowers_le.2 huT) ha)).symm
  have hdisj : Subgroup.zpowers u ⊓ omegaZ T = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcu, hcZ⟩
    rcases zpowers_sq_cases hu2 hcu with e | e
    · rw [e]; exact Subgroup.one_mem _
    · exact absurd (e ▸ hcZ) huZ
  have hAel : IsElemAb2 (Subgroup.zpowers u ⊔ omegaZ T) :=
    (isElemAb2_zpowers hu2).sup (omegaZ_isElemAb2 T) hcomm
  have hAcard : Nat.card ↥(Subgroup.zpowers u ⊔ omegaZ T) = 8 := by
    rw [card_sup_of_commute hcomm hdisj, card_zpowers_of_sq hu2 hu1, h4]
  set A := Subgroup.zpowers u ⊔ omegaZ T with hA
  have huA : u ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hAC : A ≤ Subgroup.centralizer ({u} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (hAel u huA).2 a ha
  have hApg : IsPGroup 2 ↥A := IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)
  obtain ⟨Tu, hTu, hATu⟩ := exists_sylow2_ge hApg hAC
  have hS1 : IsSylow2In (Hconj g T) (Subgroup.centralizer ({u} : Set G)) := by
    have := sylow2_conj h.T_sylow g
    rwa [Hconj_centralizer] at this
  obtain ⟨c, hc, hTuc⟩ := sylow2_exists_conj hS1 hTu
  rw [Hconj_mul] at hTuc
  have hcu : u * c = c * u := Subgroup.mem_centralizer_iff.1 hc u (Set.mem_singleton u)
  have hug' : (g * c)⁻¹ * x * (g * c) = u := by
    calc (g * c)⁻¹ * x * (g * c) = c⁻¹ * (g⁻¹ * x * g) * c := by group
      _ = c⁻¹ * u * c := by rw [hu]
      _ = c⁻¹ * (u * c) := by rw [mul_assoc]
      _ = c⁻¹ * (c * u) := by rw [hcu]
      _ = u := by group
  set g' := g * c with hg'
  set Z' := Hconj g' (omegaZ T) with hZ'
  have hZ'el : IsElemAb2 Z' := (omegaZ_isElemAb2 T).hconj g'
  have hZ'card : Nat.card Z' = 4 := by rw [hZ', Hconj_card, h4]
  have hTuT : ∀ s, s ∈ Tu ↔ g' * s * g'⁻¹ ∈ T :=
    fun s => (SetLike.ext_iff.1 hTuc s).trans mem_Hconj
  have hZ'cent : ∀ a ∈ Z', ∀ s ∈ Tu, a * s = s * a := by
    intro a ha s hs
    have h1 : g' * a * g'⁻¹ ∈ omegaZ T := ha
    have h2 : g' * s * g'⁻¹ ∈ T := (hTuT s).1 hs
    have h3 := h1.2.2 _ h2
    have : g' * (a * s) * g'⁻¹ = g' * (s * a) * g'⁻¹ := by
      calc g' * (a * s) * g'⁻¹ = (g' * a * g'⁻¹) * (g' * s * g'⁻¹) := by group
        _ = (g' * s * g'⁻¹) * (g' * a * g'⁻¹) := h3
        _ = g' * (s * a) * g'⁻¹ := by group
    simpa using this
  have hAZ' : ∀ a ∈ A, ∀ b ∈ Z', a * b = b * a :=
    fun a ha b hb => (hZ'cent b hb a (hATu ha)).symm
  have hEel : IsElemAb2 (A ⊔ Z') := hAel.sup hZ'el hAZ'
  have hEC : A ⊔ Z' ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le hAC ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (hZ'cent a ha u (hATu huA)).symm
  have hEcard : Nat.card ↥(A ⊔ Z') ≤ 8 := by
    have hC : Subgroup.centralizer ({u} : Set G) =
        Hconj g' (Subgroup.centralizer ({x} : Set G)) := by
      rw [Hconj_centralizer, hug']
    have hE0 : Hconj g'⁻¹ (A ⊔ Z') ≤ Subgroup.centralizer ({x} : Set G) := by
      have hEC' : A ⊔ Z' ≤ Hconj g' (Subgroup.centralizer ({x} : Set G)) := by
        rw [← hC]; exact hEC
      have := Hconj_le_Hconj (g := g'⁻¹) hEC'
      rwa [Hconj_inv_Hconj] at this
    have h1 := h.rank_le _ hE0 (hEel.hconj g'⁻¹)
    rw [Hconj_card] at h1
    norm_num at h1
    exact h1
  have hAE : A = A ⊔ Z' :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hAcard]; exact hEcard)
  have hZ'A : Z' ≤ A := by
    calc Z' ≤ A ⊔ Z' := le_sup_right
      _ = A := hAE.symm
  have huZ' : u ∈ Z' := by
    show g' * u * g'⁻¹ ∈ omegaZ T
    have : g' * u * g'⁻¹ = x := by
      calc g' * u * g'⁻¹ = g' * (g'⁻¹ * x * g') * g'⁻¹ := by rw [hug']
        _ = x := by group
    rw [this]; exact h.x_mem_Z
  have hwc' : ∀ a ∈ Z', IsConjX x a → a = u := by
    intro a ha hconj
    obtain ⟨k, hk⟩ := hconj
    have h1 : g' * a * g'⁻¹ ∈ omegaZ T := ha
    have e : g' * a * g'⁻¹ = (k * g'⁻¹)⁻¹ * x * (k * g'⁻¹) := by rw [← hk]; group
    have h2 := hwc (k * g'⁻¹) (by rw [← e]; exact h1)
    have h3 : g' * a * g'⁻¹ = x := by rw [e]; exact h2
    calc a = g'⁻¹ * (g' * a * g'⁻¹) * g' := by group
      _ = g'⁻¹ * x * g' := by rw [h3]
      _ = u := hug'
  have hlt : Subgroup.zpowers u < Z' := by
    refine lt_of_le_of_ne ((Subgroup.zpowers_le).2 huZ') ?_
    intro e
    have h5 : Nat.card ↥(Subgroup.zpowers u) = Nat.card ↥Z' := by rw [e]
    rw [card_zpowers_of_sq hu2 hu1, hZ'card] at h5
    omega
  obtain ⟨c1, hc1Z', hc1u⟩ := IsConcreteLE.exists_of_lt hlt
  have hc1A : c1 ∈ A := hZ'A hc1Z'
  obtain ⟨a, ha, b, hb, hc1e⟩ := mem_sup_of_commute hcomm hc1A
  have hc₀ : ∃ c₀ : G, c₀ ∈ omegaZ T ∧ c₀ ∈ Z' ∧ c₀ ≠ 1 := by
    rcases zpowers_sq_cases hu2 ha with e | e
    · refine ⟨b, hb, ?_, ?_⟩
      · have : c1 = b := by rw [hc1e, e, one_mul]
        rw [← this]; exact hc1Z'
      · intro hb1
        apply hc1u
        have : c1 = 1 := by rw [hc1e, e, hb1, one_mul]
        rw [this]; exact Subgroup.one_mem _
    · refine ⟨b, hb, ?_, ?_⟩
      · have : b = u * c1 := by rw [hc1e, e, ← mul_assoc, hu2, one_mul]
        rw [this]; exact Z'.mul_mem huZ' hc1Z'
      · intro hb1
        apply hc1u
        have : c1 = u := by rw [hc1e, e, hb1, mul_one]
        rw [this]; exact Subgroup.mem_zpowers u
  obtain ⟨c₀, hc₀Z, hc₀Z', hc₀1⟩ := hc₀
  have hc₀x : c₀ ≠ x := by
    intro e
    have hxZ' : x ∈ Z' := by rw [← e]; exact hc₀Z'
    have := hwc' x hxZ' ⟨1, by simp⟩
    exact hux this.symm
  have hc₀cases : c₀ = z ∨ c₀ = x * z := by
    rcases h.Z_cases hz h4 c₀ hc₀Z with e | e | e | e
    · exact absurd e hc₀1
    · exact absurd e hc₀x
    · exact Or.inl e
    · exact Or.inr e
  refine ⟨c₀, hc₀cases, ?_⟩
  intro hconj
  have huc₀Z' : u * c₀ ∈ Z' := Z'.mul_mem huZ' hc₀Z'
  have h6 := hwc' _ huc₀Z' hconj
  apply hc₀1
  exact mul_left_cancel (h6.trans (mul_one u).symm)

theorem HBase.not_conj_ux (h : HBase G x S T P Q Rd F) (hz : HZ T P z)
    (htrans : IP_P_trans P Q Rd) {u : G} (huT : u ∈ T) (huRd : u ∈ Rd) (huR : u ∉ P ⊔ Q)
    (hu2 : u * u = 1) (hxu : IsConjX x u)
    (hstar : ∃ c₀ : G, (c₀ = z ∨ c₀ = x * z) ∧ ¬ IsConjX x (u * c₀)) {t : G} :
    t⁻¹ * u * t ≠ u * x := by
  intro e
  have h1 : (1 * u) * (1 * u) = 1 := by simpa using hu2
  have hzu : z * u = u * z := hz.z_central u huT
  have h2 : (z * u) * (z * u) = 1 := by
    have : z * u * (z * u) = (z * z) * (u * u) := by
      calc z * u * (z * u) = z * (u * z) * u := by group
        _ = z * (z * u) * u := by rw [hzu]
        _ = (z * z) * (u * u) := by group
    rw [this, hz.z_sq, hu2]; group
  obtain ⟨p, hp, hpe⟩ := htrans u huRd huR hu2 1 (Subgroup.one_mem P) z hz.z_mem_P h1 h2
  rw [one_mul] at hpe
  have hpT : p ∈ T := h.P_le_T hp
  have hX1 : IsConjX x (u * z) := by
    have : u * z = p * u * p⁻¹ := by rw [hpe]; exact hzu.symm
    rw [this]; exact hxu.conj p
  have hX2 : IsConjX x (u * x) := by
    have : u * x = t⁻¹ * u * t⁻¹⁻¹ := by rw [inv_inv]; exact e.symm
    rw [this]; exact hxu.conj t⁻¹
  have hpx : p * x * p⁻¹ = x := by
    have := h.x_central p hpT
    calc p * x * p⁻¹ = x * p * p⁻¹ := by rw [← this]
      _ = x := by group
  have hzx : z * x = x * z := hz.z_central x h.x_mem_T
  have hX3 : IsConjX x (u * (x * z)) := by
    have e3 : p * (u * x) * p⁻¹ = u * (x * z) := by
      calc p * (u * x) * p⁻¹ = (p * u * p⁻¹) * (p * x * p⁻¹) := by group
        _ = (z * u) * x := by rw [hpe, hpx]
        _ = u * (z * x) := by rw [hzu]; group
        _ = u * (x * z) := by rw [hzx]
    rw [← e3]; exact hX2.conj p
  obtain ⟨c₀, hc₀, hnot⟩ := hstar
  rcases hc₀ with e1 | e1
  · rw [e1] at hnot; exact hnot hX1
  · rw [e1] at hnot; exact hnot hX3

theorem HBase.conj_mem_Pu (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd)
    (hP4 : IP_P_four P) (htrans : IP_P_trans P Q Rd) {u : G} (huT : u ∈ T) (huRd : u ∈ Rd)
    (huR : u ∉ P ⊔ Q) (hu2 : u * u = 1) (hnot : ∀ t ∈ T, t⁻¹ * u * t ≠ u * x) {t : G}
    (ht : t ∈ T) : ∃ p ∈ P, t⁻¹ * u * t = p * u := by
  have hvT : t⁻¹ * u * t ∈ T := T.mul_mem (T.mul_mem (T.inv_mem ht) huT) ht
  have hv2 : t⁻¹ * u * t * (t⁻¹ * u * t) = 1 := by
    have : t⁻¹ * u * t * (t⁻¹ * u * t) = t⁻¹ * (u * u) * t := by group
    rw [this, hu2]; group
  have hvRd : t⁻¹ * u * t ∈ Rd := involution_mem_Rd h hout hvT hv2
  have hvR : t⁻¹ * u * t ∉ P ⊔ Q := by
    intro hvR
    apply huR
    have := h.R_normal.2 t ht _ hvR
    have e : t * (t⁻¹ * u * t) * t⁻¹ = u := by group
    rwa [e] at this
  have huinvRd : u⁻¹ ∈ Rd := Rd.inv_mem huRd
  have huinvR : u⁻¹ ∉ P ⊔ Q := fun hh => huR (by simpa using (P ⊔ Q).inv_mem hh)
  have hmem := relIndex_two_mul_mem h.R_index_le_two huinvRd hvRd huinvR hvR
  obtain ⟨p, hp, q, hq, hpq⟩ := h.mem_R.1 hmem
  have hvpq : t⁻¹ * u * t = u * (p * q) := by rw [← hpq]; group
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hp' : u * p * u⁻¹ ∈ P := h.P_normal.2 u huT p hp
  have hq' : u * q * u⁻¹ ∈ Q := h.Q_normal.2 u huT q hq
  have hqp : (u * q * u⁻¹) * p = p * (u * q * u⁻¹) := (h.PQ_comm p hp _ hq').symm
  have e1 : t⁻¹ * u * t * (t⁻¹ * u * t) = (u * p * u⁻¹) * (u * q * u⁻¹) * p * q := by
    calc t⁻¹ * u * t * (t⁻¹ * u * t) = u * (p * q) * (u * (p * q)) := by rw [hvpq]
      _ = u * (p * q) * (u⁻¹ * (p * q)) := by rw [huinv]
      _ = (u * p * u⁻¹) * (u * q * u⁻¹) * p * q := by group
  have hvv : t⁻¹ * u * t * (t⁻¹ * u * t) = ((u * p * u⁻¹) * p) * ((u * q * u⁻¹) * q) := by
    rw [e1]
    calc (u * p * u⁻¹) * (u * q * u⁻¹) * p * q
        = (u * p * u⁻¹) * ((u * q * u⁻¹) * p) * q := by group
      _ = (u * p * u⁻¹) * (p * (u * q * u⁻¹)) * q := by rw [hqp]
      _ = ((u * p * u⁻¹) * p) * ((u * q * u⁻¹) * q) := by group
  have h1' : ((u * p * u⁻¹) * p) * ((u * q * u⁻¹) * q) = 1 := by rw [← hvv]; exact hv2
  have hPP : (u * p * u⁻¹) * p = ((u * q * u⁻¹) * q)⁻¹ := eq_inv_of_mul_eq_one_left h1'
  have hPP1 : (u * p * u⁻¹) * p = 1 :=
    h.eq_one_of_mem_P_Q (P.mul_mem hp' hp) (by rw [hPP]; exact Q.inv_mem (Q.mul_mem hq' hq))
  have hQQ : (u * q * u⁻¹) * q = 1 := by rw [hPP1, one_mul] at h1'; exact h1'
  have hinvq : u * q * u⁻¹ = q⁻¹ := eq_inv_of_mul_eq_one_left hQQ
  have hq1x : q = 1 ∨ q = x := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨k, hk⟩ := h.exists_pow_two_pow (h.Q_le_T hq)
    obtain ⟨q₂, hq₂Q, hq₂sq, hq₂inv⟩ := h.exists_sq_eq_x_aux hP4
      (fun q => u * q * u⁻¹ = q⁻¹)
      (fun q hq' => by
        have e5 : u * (q * q) * u⁻¹ = (u * q * u⁻¹) * (u * q * u⁻¹) := by group
        rw [e5, hq', mul_inv_rev]) k q hq hk hinvq hcon.1 hcon.2
    apply hnot q₂ (h.Q_le_T hq₂Q)
    have h1 : q₂⁻¹ * u * q₂ = (q₂ * q₂)⁻¹ * u := by
      calc q₂⁻¹ * u * q₂ = q₂⁻¹ * (u * q₂ * u⁻¹) * u := by group
        _ = q₂⁻¹ * q₂⁻¹ * u := by rw [hq₂inv]
        _ = (q₂ * q₂)⁻¹ * u := by rw [mul_inv_rev]
    rw [h1, hq₂sq]
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right h.x_sq
    rw [hxinv]
    exact h.x_central u huT
  rcases hq1x with e | e
  · refine ⟨u * p * u⁻¹, hp', ?_⟩
    rw [hvpq, e]
    group
  · exfalso
    have hxcent : ∀ w ∈ T, x * w = w * x := h.x_central
    have hw : (u * p * u⁻¹ * u) * (u * p * u⁻¹ * u) = 1 := by
      have hwT : u * p * u⁻¹ * u ∈ T :=
        T.mul_mem (T.mul_mem (T.mul_mem huT (h.P_le_T hp)) (T.inv_mem huT)) huT
      have hvx : t⁻¹ * u * t = (u * p * u⁻¹ * u) * x := by rw [hvpq, e]; group
      have : (u * p * u⁻¹ * u * x) * (u * p * u⁻¹ * u * x) =
          (u * p * u⁻¹ * u) * (u * p * u⁻¹ * u) := by
        have hc := hxcent _ hwT
        calc (u * p * u⁻¹ * u * x) * (u * p * u⁻¹ * u * x)
            = (u * p * u⁻¹ * u) * (x * (u * p * u⁻¹ * u)) * x := by group
          _ = (u * p * u⁻¹ * u) * ((u * p * u⁻¹ * u) * x) * x := by rw [hc]
          _ = (u * p * u⁻¹ * u) * (u * p * u⁻¹ * u) * (x * x) := by group
          _ = (u * p * u⁻¹ * u) * (u * p * u⁻¹ * u) := by rw [h.x_sq, mul_one]
      rw [← this, ← hvx]; exact hv2
    obtain ⟨p₀, hp₀, hp₀e⟩ := htrans u huRd huR hu2 1 (Subgroup.one_mem P) (u * p * u⁻¹) hp'
      (by simpa using hu2) hw
    rw [one_mul] at hp₀e
    have hp₀T : p₀ ∈ T := h.P_le_T hp₀
    have hp₀x : p₀ * x * p₀⁻¹ = x := by
      have := h.x_central p₀ hp₀T
      calc p₀ * x * p₀⁻¹ = x * p₀ * p₀⁻¹ := by rw [← this]
        _ = x := by group
    apply hnot (t * p₀) (T.mul_mem ht hp₀T)
    have hvx : t⁻¹ * u * t = (u * p * u⁻¹ * u) * x := by rw [hvpq, e]; group
    calc (t * p₀)⁻¹ * u * (t * p₀) = p₀⁻¹ * (t⁻¹ * u * t) * p₀ := by group
      _ = p₀⁻¹ * ((u * p * u⁻¹ * u) * x) * p₀ := by rw [hvx]
      _ = p₀⁻¹ * ((p₀ * u * p₀⁻¹) * (p₀ * x * p₀⁻¹)) * p₀ := by rw [hp₀e, hp₀x]
      _ = u * x := by group

theorem HBase.u_not_mem_R (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (hP4 : IP_P_four P)
    (hconj : IP_P_conj x z P) (hwc : ∀ g : G, g⁻¹ * x * g ∈ omegaZ T → g⁻¹ * x * g = x)
    {g : G} (hux : g⁻¹ * x * g ≠ x) : g⁻¹ * x * g ∉ P ⊔ Q := by
  set u := g⁻¹ * x * g with hu
  have hu2 : u * u = 1 := by
    have : u * u = g⁻¹ * (x * x) * g := by rw [hu]; group
    rw [this, h.x_sq]; group
  have hu1 : u ≠ 1 := by
    intro e
    apply h.x_ne_one
    have : x = g * u * g⁻¹ := by rw [hu]; group
    rw [this, e]; group
  have hxu : IsConjX x u := ⟨g, rfl⟩
  intro huR
  obtain ⟨p, hp, q, hq, e, hp2, hq2⟩ := h.R_invol huR hu2
  have hq1x : q = 1 ∨ q = x := h.Q_invol hP4 hq hq2
  have hp1 : p ≠ 1 := by
    intro hp1
    rcases hq1x with e1 | e1
    · apply hu1; rw [e, hp1, e1]; simp
    · apply hux; rw [e, hp1, e1]; simp
  obtain ⟨c, hc, hce⟩ := hconj p hp hp2 hp1
  have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.1 hc x (Set.mem_singleton x)
  have hcx : c * x * c⁻¹ = x := by
    calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [hxc]
      _ = x := by group
  have hcu : c * u * c⁻¹ = z * q := by
    rw [e]
    calc c * (p * q) * c⁻¹ = (c * p * c⁻¹) * (c * q * c⁻¹) := by group
      _ = z * q := by
        rw [hce]
        rcases hq1x with e1 | e1
        · rw [e1]; group
        · rw [e1, hcx]
  have hconjzq : IsConjX x (z * q) := by rw [← hcu]; exact hxu.conj c
  obtain ⟨k, hk⟩ := hconjzq
  have hqZ : q ∈ omegaZ T := by
    rcases hq1x with e1 | e1
    · rw [e1]; exact Subgroup.one_mem _
    · rw [e1]; exact h.x_mem_Z
  have hzqZ : z * q ∈ omegaZ T := (omegaZ T).mul_mem (hz.mem_Z h.P_le_T) hqZ
  have hkx := hwc k (by rw [hk]; exact hzqZ)
  have hzq : z * q = x := by rw [← hk]; exact hkx
  rcases hq1x with e1 | e1
  · rw [e1, mul_one] at hzq
    exact h.x_ne_z hz hzq.symm
  · rw [e1] at hzq
    apply hz.z_ne_one
    calc z = z * x * x⁻¹ := by group
      _ = x * x⁻¹ := by rw [hzq]
      _ = 1 := by group

theorem lemma_12_5 (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (hout : IP_outer x T Rd)
    (hcf : IP_cent_four T P Q Rd) (hP4 : IP_P_four P) (hRf : IP_Rd_factor T P Q Rd)
    (hconj : IP_P_conj x z P) (htrans : IP_P_trans P Q Rd) (h4 : Nat.card (omegaZ T) = 4)
    (hwc : ∀ g : G, g⁻¹ * x * g ∈ omegaZ T → g⁻¹ * x * g = x)
    (g : G) (huT : g⁻¹ * x * g ∈ T) (hux : g⁻¹ * x * g ≠ x) :
    NormalIn (P ⊔ Subgroup.zpowers (g⁻¹ * x * g)) T ∧ Q = Subgroup.zpowers x := by
  set u := g⁻¹ * x * g with hu
  have hu2 : u * u = 1 := by
    have : u * u = g⁻¹ * (x * x) * g := by rw [hu]; group
    rw [this, h.x_sq]; group
  have hu1 : u ≠ 1 := by
    intro e
    apply h.x_ne_one
    have : x = g * u * g⁻¹ := by rw [hu]; group
    rw [this, e]; group
  have huRd : u ∈ Rd := involution_mem_Rd h hout huT hu2
  have hxu : IsConjX x u := ⟨g, rfl⟩
  have huR : u ∉ P ⊔ Q := h.u_not_mem_R hz hP4 hconj hwc hux
  have hstar := h.star hz h4 hwc huT hux
  have hnot : ∀ t ∈ T, t⁻¹ * u * t ≠ u * x := fun _ _ =>
    h.not_conj_ux hz htrans huT huRd huR hu2 hxu hstar
  have hN1 : ∀ t ∈ T, ∃ p ∈ P, t⁻¹ * u * t = p * u := fun t ht =>
    h.conj_mem_Pu hout hP4 htrans huT huRd huR hu2 hnot ht
  have hnorm : NormalIn (P ⊔ Subgroup.zpowers u) T := by
    refine ⟨sup_le h.P_le_T ((Subgroup.zpowers_le).2 huT), fun t ht a ha => ?_⟩
    have hle : P ⊔ Subgroup.zpowers u ≤ Hconj t (P ⊔ Subgroup.zpowers u) := by
      refine sup_le (fun p hp => ?_) ((Subgroup.zpowers_le).2 ?_)
      · exact Subgroup.mem_sup_left (h.P_normal.2 t ht p hp)
      · obtain ⟨p, hp, e⟩ := hN1 t⁻¹ (T.inv_mem ht)
        show t * u * t⁻¹ ∈ P ⊔ Subgroup.zpowers u
        have e' : t * u * t⁻¹ = p * u := by simpa using e
        rw [e']
        exact Subgroup.mul_mem_sup hp (Subgroup.mem_zpowers u)
    exact hle ha
  refine ⟨hnorm, ?_⟩
  by_contra hQ
  obtain ⟨q, hqQ, hqsq⟩ := h.exists_sq_eq_x hP4 hQ
  have hqT : q ∈ T := h.Q_le_T hqQ
  have huP : u ∈ P ⊔ Subgroup.zpowers u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hcomm : u * q * u⁻¹ * q⁻¹ = 1 := by
    apply h.Pstar_inf_Q huT hu2 huR
    · have h1 : q * u⁻¹ * q⁻¹ ∈ P ⊔ Subgroup.zpowers u :=
        hnorm.2 q hqT u⁻¹ ((P ⊔ Subgroup.zpowers u).inv_mem huP)
      have := (P ⊔ Subgroup.zpowers u).mul_mem huP h1
      simpa [mul_assoc] using this
    · exact Q.mul_mem (h.Q_normal.2 u huT q hqQ) (Q.inv_mem hqQ)
  have hqu : q * u = u * q := by
    have h1 : u * q * u⁻¹ = q := by
      calc u * q * u⁻¹ = (u * q * u⁻¹ * q⁻¹) * q := by group
        _ = q := by rw [hcomm, one_mul]
    calc q * u = (u * q * u⁻¹) * u := by rw [h1]
      _ = u * q := by group
  have hgu : g * u * g⁻¹ = x := by rw [hu]; group
  have hc₀sq : (g * q * g⁻¹) * (g * q * g⁻¹) = g * x * g⁻¹ := by
    have : (g * q * g⁻¹) * (g * q * g⁻¹) = g * (q * q) * g⁻¹ := by group
    rw [this, hqsq]
  have hc₀C : g * q * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc x * (g * q * g⁻¹) = (g * u * g⁻¹) * (g * q * g⁻¹) := by rw [hgu]
      _ = g * (u * q) * g⁻¹ := by group
      _ = g * (q * u) * g⁻¹ := by rw [hqu]
      _ = (g * q * g⁻¹) * (g * u * g⁻¹) := by group
      _ = (g * q * g⁻¹) * x := by rw [hgu]
  have hy₀2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    have : (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    rw [this, h.x_sq]; group
  have hc₀4 : (g * q * g⁻¹) ^ 4 = 1 := by
    have : (g * q * g⁻¹) ^ 4 = (g * q * g⁻¹) * (g * q * g⁻¹) * ((g * q * g⁻¹) * (g * q * g⁻¹)) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [this, hc₀sq, hy₀2]
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers (g * q * g⁻¹)) := by
    rw [isPGroup_iff_card_dvd_pow]
    exact ⟨2, by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hc₀4⟩
  obtain ⟨T', hT', hc₀T'⟩ := exists_sylow2_ge hpg ((Subgroup.zpowers_le).2 hc₀C)
  obtain ⟨c, hc, hT'c⟩ := sylow2_exists_conj h.T_sylow hT'
  have hc₀T : c * (g * q * g⁻¹) * c⁻¹ ∈ T := by
    have : g * q * g⁻¹ ∈ T' := hc₀T' (Subgroup.mem_zpowers _)
    rw [hT'c] at this
    exact this
  have ht₀ : (c * (g * q * g⁻¹) * c⁻¹) * (c * (g * q * g⁻¹) * c⁻¹) *
      ((c * (g * q * g⁻¹) * c⁻¹) * (c * (g * q * g⁻¹) * c⁻¹)) = 1 := by
    have : (c * (g * q * g⁻¹) * c⁻¹) * (c * (g * q * g⁻¹) * c⁻¹) *
        ((c * (g * q * g⁻¹) * c⁻¹) * (c * (g * q * g⁻¹) * c⁻¹)) =
        c * ((g * q * g⁻¹) * (g * q * g⁻¹) * ((g * q * g⁻¹) * (g * q * g⁻¹))) * c⁻¹ := by group
    rw [this, hc₀sq, hy₀2]; group
  have h124 := lemma_12_4' h hz hout hcf hP4 hRf hc₀T ht₀
  have hZ' : (c * (g * q * g⁻¹) * c⁻¹) * (c * (g * q * g⁻¹) * c⁻¹) ∈ omegaZ T := by
    rw [h.Z_eq hz h4]; exact h124
  have hsq' : (c * (g * q * g⁻¹) * c⁻¹) * (c * (g * q * g⁻¹) * c⁻¹) = c * (g * x * g⁻¹) * c⁻¹ := by
    have : (c * (g * q * g⁻¹) * c⁻¹) * (c * (g * q * g⁻¹) * c⁻¹) =
        c * ((g * q * g⁻¹) * (g * q * g⁻¹)) * c⁻¹ := by group
    rw [this, hc₀sq]
  rw [hsq'] at hZ'
  have hy₀conj : IsConjX x (g * x * g⁻¹) := ⟨g⁻¹, by group⟩
  obtain ⟨k, hk⟩ := hy₀conj.conj c
  have hkx := hwc k (by rw [hk]; exact hZ')
  have hcy : c * (g * x * g⁻¹) * c⁻¹ = x := by rw [← hk]; exact hkx
  have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.1 hc x (Set.mem_singleton x)
  have hcinv : c⁻¹ * x * c = x := by
    calc c⁻¹ * x * c = c⁻¹ * (x * c) := by rw [mul_assoc]
      _ = c⁻¹ * (c * x) := by rw [hxc]
      _ = x := by group
  have hy₀x : g * x * g⁻¹ = x := by
    calc g * x * g⁻¹ = c⁻¹ * (c * (g * x * g⁻¹) * c⁻¹) * c := by group
      _ = c⁻¹ * x * c := by rw [hcy]
      _ = x := hcinv
  apply hux
  calc u = g⁻¹ * x * g := hu
    _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hy₀x]
    _ = x := by group

end CFSG.GH74.GLS.Stage1.Thm6.Sec12

