module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.IP
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Setting

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G]

theorem zpowers_sq_cases {x a : G} (hx : x * x = 1) (ha : a ∈ Subgroup.zpowers x) :
    a = 1 ∨ a = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, hx2, one_zpow]
  · right; rw [zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]

theorem zpowers_inf_zpowers {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a ≠ b) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hca, hcb⟩
  rcases zpowers_sq_cases ha hca with rfl | rfl
  · exact Subgroup.one_mem _
  · rcases zpowers_sq_cases hb hcb with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd h hab

theorem isFour_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hc : a * b = b * a) :
    IsFour (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers b, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow (show Commute a b from hc) k l).eq
  refine ⟨(isElemAb2_zpowers ha).sup (isElemAb2_zpowers hb) hcomm, ?_⟩
  rw [card_sup_of_commute hcomm (zpowers_inf_zpowers ha hb hab), card_zpowers_of_sq ha ha1,
    card_zpowers_of_sq hb hb1]

theorem no_two_fours {C : Subgroup G} (hr : Rank2Le C 3) {A B : Subgroup G} (hA : IsFour A)
    (hB : IsFour B) (hAC : A ≤ C) (hBC : B ≤ C) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hd : A ⊓ B = ⊥) : False := by
  have hE : IsElemAb2 (A ⊔ B) := hA.1.sup hB.1 hc
  have hcard : Nat.card ↥(A ⊔ B) = 16 := by rw [card_sup_of_commute hc hd, hA.2, hB.2]
  have := hr (A ⊔ B) (sup_le hAC hBC) hE
  rw [hcard] at this
  norm_num at this

theorem relIndex_two_mul_mem [Finite G] {R M : Subgroup G} (h2 : R.relIndex M ≤ 2) {a b : G}
    (ha : a ∈ M) (hb : b ∈ M) (haR : a ∉ R) (hbR : b ∉ R) : a * b ∈ R := by
  have hne : (R.subgroupOf M).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : (R.subgroupOf M).index ≤ 2 := h2
  have hcases : (R.subgroupOf M).index = 1 ∨ (R.subgroupOf M).index = 2 := by omega
  rcases hcases with h1 | h2'
  · exfalso
    have : R.subgroupOf M = ⊤ := Subgroup.index_eq_one.1 h1
    have hmem : (⟨a, ha⟩ : ↥M) ∈ R.subgroupOf M := by rw [this]; trivial
    exact haR hmem
  · have key := (Subgroup.mul_mem_iff_of_index_two h2' (a := (⟨a, ha⟩ : ↥M)) (b := ⟨b, hb⟩))
    have : (⟨a, ha⟩ * ⟨b, hb⟩ : ↥M) ∈ R.subgroupOf M := by
      rw [key]
      exact iff_of_false (fun h => haR h) (fun h => hbR h)
    exact this

theorem NormalIn.inv_conj {N T : Subgroup G} (hN : NormalIn N T) {t : G} (ht : t ∈ T) {n : G}
    (hn : n ∈ N) : t⁻¹ * n * t ∈ N := by
  have := hN.2 t⁻¹ (T.inv_mem ht) n hn
  simpa using this

section Derived

variable [Finite G] {x : G} {S T P Q Rd F : Subgroup G}

theorem HBase.T_pgroup (h : HBase G x S T P Q Rd F) : IsPGroup 2 ↥T := h.T_sylow.2.1

theorem HBase.S_pgroup (h : HBase G x S T P Q Rd F) : IsPGroup 2 ↥S := h.S_sylow.2.1

theorem HBase.P_le_T (h : HBase G x S T P Q Rd F) : P ≤ T := h.P_normal.1

theorem HBase.Q_le_T (h : HBase G x S T P Q Rd F) : Q ≤ T := h.Q_normal.1

theorem HBase.Rd_le_T (h : HBase G x S T P Q Rd F) : Rd ≤ T := h.Rd_normal.1

theorem HBase.R_le_T (h : HBase G x S T P Q Rd F) : P ⊔ Q ≤ T := sup_le h.P_le_T h.Q_le_T

theorem HBase.x_mem_T (h : HBase G x S T P Q Rd F) : x ∈ T := h.Q_le_T h.x_mem_Q

theorem HBase.T_le_C (h : HBase G x S T P Q Rd F) : T ≤ Subgroup.centralizer ({x} : Set G) :=
  h.T_sylow.1

theorem HBase.x_central (h : HBase G x S T P Q Rd F) : ∀ t ∈ T, x * t = t * x := by
  intro t ht
  exact Subgroup.mem_centralizer_iff.1 (h.T_le_C ht) x (Set.mem_singleton x)

theorem HBase.mem_R (h : HBase G x S T P Q Rd F) {a : G} :
    a ∈ P ⊔ Q ↔ ∃ p ∈ P, ∃ q ∈ Q, a = p * q :=
  ⟨fun ha => mem_sup_of_commute h.PQ_comm ha, by
    rintro ⟨p, hp, q, hq, rfl⟩; exact Subgroup.mul_mem_sup hp hq⟩

theorem HBase.R_normal (h : HBase G x S T P Q Rd F) : NormalIn (P ⊔ Q) T := by
  refine ⟨h.R_le_T, fun t ht a ha => ?_⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := h.mem_R.1 ha
  have : t * (p * q) * t⁻¹ = (t * p * t⁻¹) * (t * q * t⁻¹) := by group
  rw [this]
  exact Subgroup.mul_mem_sup (h.P_normal.2 t ht p hp) (h.Q_normal.2 t ht q hq)

theorem HBase.eq_one_of_mem_P_Q (h : HBase G x S T P Q Rd F) {a : G} (hP : a ∈ P) (hQ : a ∈ Q) :
    a = 1 := by
  have : a ∈ P ⊓ Q := ⟨hP, hQ⟩
  rw [h.PQ_disjoint] at this
  exact Subgroup.mem_bot.1 this

theorem HBase.x_not_mem_P (h : HBase G x S T P Q Rd F) : x ∉ P :=
  fun hx => h.x_ne_one (h.eq_one_of_mem_P_Q hx h.x_mem_Q)

theorem HBase.Q_invol (h : HBase G x S T P Q Rd F) (hP : IP_P_four P) {q : G} (hq : q ∈ Q)
    (hq2 : q * q = 1) : q = 1 ∨ q = x := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨V, hVP, hV⟩ := hP
  have hqT : q ∈ T := h.Q_le_T hq
  have hB : IsFour (Subgroup.zpowers x ⊔ Subgroup.zpowers q) :=
    isFour_pair h.x_sq hq2 h.x_ne_one hcon.1 (Ne.symm hcon.2) (h.x_central q hqT)
  have hBQ : Subgroup.zpowers x ⊔ Subgroup.zpowers q ≤ Q :=
    sup_le ((Subgroup.zpowers_le).2 h.x_mem_Q) ((Subgroup.zpowers_le).2 hq)
  refine no_two_fours h.rank_le hV hB (fun a ha => h.T_le_C (h.P_le_T (hVP ha)))
    (fun a ha => h.T_le_C (h.Q_le_T (hBQ ha))) (fun a ha b hb => h.PQ_comm a (hVP ha) b (hBQ hb)) ?_
  rw [eq_bot_iff, ← h.PQ_disjoint]
  exact inf_le_inf hVP hBQ

end Derived

theorem omegaZ_le (T : Subgroup G) : omegaZ T ≤ T := fun _ ha => ha.1

theorem omegaZ_isElemAb2 (T : Subgroup G) : IsElemAb2 (omegaZ T) :=
  fun _ ha => ⟨ha.2.1, fun _ hb => ha.2.2 _ hb.1⟩

theorem normalizes_inv {T : Subgroup G} {m : G} (hm : ∀ a, a ∈ T ↔ m * a * m⁻¹ ∈ T) :
    ∀ a, a ∈ T ↔ m⁻¹ * a * m⁻¹⁻¹ ∈ T := by
  intro a
  rw [inv_inv, hm (m⁻¹ * a * m)]
  have : m * (m⁻¹ * a * m) * m⁻¹ = a := by group
  rw [this]

theorem omegaZ_conj_mem {T : Subgroup G} {m : G} (hm : ∀ a, a ∈ T ↔ m * a * m⁻¹ ∈ T) {u : G}
    (hu : u ∈ omegaZ T) : m * u * m⁻¹ ∈ omegaZ T := by
  obtain ⟨huT, hu2, huc⟩ := hu
  refine ⟨(hm u).1 huT, ?_, ?_⟩
  · have : m * u * m⁻¹ * (m * u * m⁻¹) = m * (u * u) * m⁻¹ := by group
    rw [this, hu2]; group
  · intro t ht
    have ht' : m⁻¹ * t * m ∈ T := by
      have := (normalizes_inv hm t).1 ht
      simpa using this
    have hc := huc _ ht'
    have : m * u * m⁻¹ * t = t * (m * u * m⁻¹) := by
      calc m * u * m⁻¹ * t = m * (u * (m⁻¹ * t * m)) * m⁻¹ := by group
        _ = m * ((m⁻¹ * t * m) * u) * m⁻¹ := by rw [hc]
        _ = t * (m * u * m⁻¹) := by group
    exact this

theorem omegaZ_conj_inv_mem {T : Subgroup G} {m : G} (hm : ∀ a, a ∈ T ↔ m * a * m⁻¹ ∈ T) {u : G}
    (hu : u ∈ omegaZ T) : m⁻¹ * u * m ∈ omegaZ T := by
  have := omegaZ_conj_mem (normalizes_inv hm) hu
  simpa using this

theorem comm_of_normal_inf_bot {A B T : Subgroup G} (hA : NormalIn A T) (hB : NormalIn B T)
    (hd : A ⊓ B = ⊥) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have := A.mul_mem ha (hA.2 b (hB.1 hb) a⁻¹ (A.inv_mem ha))
    simpa [mul_assoc] using this
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ B := by
    have := B.mul_mem (hB.2 a (hA.1 ha) b hb) (B.inv_mem hb)
    simpa [mul_assoc] using this
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := ⟨h1, h2⟩
  rw [hd, Subgroup.mem_bot] at h3
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem sylow2_of_card [Finite G] {T H P' : Subgroup G} (hTH : T ≤ H) (hT : IsPGroup 2 ↥T)
    (hP' : IsSylow2In P' H) (hcard : Nat.card P' ≤ Nat.card T) : IsSylow2In T H := by
  obtain ⟨P'', hP'', hTP''⟩ := exists_sylow2_ge hT hTH
  have h1 : Nat.card P'' = Nat.card P' := sylow2_card_eq hP'' hP'
  have h2 : T = P'' := Subgroup.eq_of_le_of_card_ge hTP'' (by rw [h1]; exact hcard)
  rw [h2]; exact hP''

section HZLemmas

variable {z : G} {T P : Subgroup G}

theorem HZ.mem_Z (hz : HZ T P z) (hPT : P ≤ T) : z ∈ omegaZ T :=
  ⟨hPT hz.z_mem_P, hz.z_sq, hz.z_central⟩

theorem HZ.T_le_cent (hz : HZ T P z) : T ≤ Subgroup.centralizer ({z} : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hz.z_central t ht

end HZLemmas

section Derived2

variable [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

theorem HBase.omegaZ_le_C (h : HBase G x S T P Q Rd F) :
    omegaZ T ≤ Subgroup.centralizer ({x} : Set G) := fun _ ha => h.T_le_C ha.1

theorem HBase.x_mem_Z (h : HBase G x S T P Q Rd F) : x ∈ omegaZ T :=
  ⟨h.x_mem_T, h.x_sq, h.x_central⟩

theorem HBase.x_ne_z (h : HBase G x S T P Q Rd F) (hz : HZ T P z) : x ≠ z := by
  intro e
  apply hz.z_ne_one
  exact h.eq_one_of_mem_P_Q hz.z_mem_P (by rw [← e]; exact h.x_mem_Q)

theorem HBase.isFour_xz (h : HBase G x S T P Q Rd F) (hz : HZ T P z) :
    IsFour (Subgroup.zpowers x ⊔ Subgroup.zpowers z) :=
  isFour_pair h.x_sq hz.z_sq h.x_ne_one hz.z_ne_one (h.x_ne_z hz) (hz.z_central x h.x_mem_T).symm

theorem HBase.xz_le_Z (h : HBase G x S T P Q Rd F) (hz : HZ T P z) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ omegaZ T :=
  sup_le ((Subgroup.zpowers_le).2 h.x_mem_Z) ((Subgroup.zpowers_le).2 (hz.mem_Z h.P_le_T))

theorem HBase.card_Z (h : HBase G x S T P Q Rd F) (hz : HZ T P z) :
    Nat.card (omegaZ T) = 4 ∨ Nat.card (omegaZ T) = 8 := by
  have hdvd : 4 ∣ Nat.card (omegaZ T) := by
    have := Subgroup.card_dvd_of_le (h.xz_le_Z hz)
    rwa [(h.isFour_xz hz).2] at this
  have hle8 : Nat.card (omegaZ T) ≤ 8 := by
    have := h.rank_le _ h.omegaZ_le_C (omegaZ_isElemAb2 T)
    norm_num at this
    exact this
  have hpos : 0 < Nat.card (omegaZ T) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  omega

theorem HBase.Z_eq (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (h4 : Nat.card (omegaZ T) = 4) :
    omegaZ T = Subgroup.zpowers x ⊔ Subgroup.zpowers z :=
  (Subgroup.eq_of_le_of_card_ge (h.xz_le_Z hz) (by rw [h4, (h.isFour_xz hz).2])).symm

theorem HBase.Z_cases (h : HBase G x S T P Q Rd F) (hz : HZ T P z)
    (h4 : Nat.card (omegaZ T) = 4) : ∀ u ∈ omegaZ T, u = 1 ∨ u = x ∨ u = z ∨ u = x * z := by
  intro u hu
  rw [h.Z_eq hz h4] at hu
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute x z from (hz.z_central x h.x_mem_T).symm) k l).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hu
  rcases zpowers_sq_cases h.x_sq ha with rfl | rfl <;>
    rcases zpowers_sq_cases hz.z_sq hb with rfl | rfl <;> simp

theorem HBase.P_inf_Z (h : HBase G x S T P Q Rd F) (hz : HZ T P z)
    (h4 : Nat.card (omegaZ T) = 4) {u : G} (huP : u ∈ P) (huZ : u ∈ omegaZ T) :
    u = 1 ∨ u = z := by
  rcases h.Z_cases hz h4 u huZ with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd (h1 ▸ huP) h.x_not_mem_P
  · exact Or.inr h1
  · exfalso
    apply h.x_not_mem_P
    have : x = u * z := by rw [h1, mul_assoc, hz.z_sq, mul_one]
    rw [this]
    exact P.mul_mem huP hz.z_mem_P

theorem HBase.sylow_cent_of_conj (h : HBase G x S T P Q Rd F) {y g : G} (hg : g⁻¹ * x * g = y)
    (hTy : T ≤ Subgroup.centralizer ({y} : Set G)) :
    IsSylow2In T (Subgroup.centralizer ({y} : Set G)) := by
  have h1 := sylow2_conj h.T_sylow g
  rw [Hconj_centralizer, hg] at h1
  exact sylow2_of_card hTy h.T_pgroup h1 (by rw [Hconj_card])

end Derived2

end CFSG.GH74.GLS.Stage1.Thm6.Sec12
