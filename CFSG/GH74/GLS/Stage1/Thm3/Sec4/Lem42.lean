module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

namespace M4

variable [Finite G]

omit [Finite G] in
theorem Rm_le_S : Rm O S K₁ K₂ ≤ S := sup_le inf_le_left inf_le_left

theorem PQ_comm (h : M4 O FA SD z S K₁ K₂) :
    ∀ a ∈ Pm S K₁ K₂, ∀ b ∈ Qm O S K₁ K₂, a * b = b * a :=
  fun _ ha _ hb => (h.Q_comm_P hb ha).symm

theorem pair_sq (h : M4 O FA SD z S K₁ K₂) {Ka Kb : Subgroup G} (hp : IsPair K₁ K₂ Ka Kb)
    {ta tb v : G} (hta : ta ∈ Pm S K₁ K₂ ⊓ Ka) (htb : tb ∈ Pm S K₁ K₂ ⊓ Kb)
    (hv : v ∈ Qm O S K₁ K₂) (ht2 : (ta * tb * v) * (ta * tb * v) = 1)
    (hnot : ta * tb * v ∉ secCent Ka (O Ka)) : ta * ta = z := by
  have htaP : ta ∈ Pm S K₁ K₂ := hta.1
  have htbP : tb ∈ Pm S K₁ K₂ := htb.1
  have htaK : ta ∈ Ka := hta.2
  have htbK : tb ∈ Kb := htb.2
  have hab : Commute ta tb := h.comm_of_S' hp htaK htbK htaP.1 htbP.1
  have hva : Commute v ta := h.Q_comm_P hv htaP
  have hvb : Commute v tb := h.Q_comm_P hv htbP
  have hsq : (ta * tb * v) * (ta * tb * v) = (ta * ta) * (tb * tb) * (v * v) := by
    have h1 : Commute (ta * tb) v := hva.symm.mul_left hvb.symm
    have := h1.mul_pow 2
    rw [hab.mul_pow 2] at this
    simpa [pow_two, mul_assoc] using this
  rw [hsq] at ht2
  have htb1 : tb ∈ secCent Ka (O Ka) := h.Kb_le_secCent hp htbK
  have hbb : tb * tb ∈ secCent Ka (O Ka) := mul_mem htb1 htb1
  have hvv : v * v ∈ secCent Ka (O Ka) := mul_mem (h.Q_mem_secCent_comp hv hp.left)
    (h.Q_mem_secCent_comp hv hp.left)
  have hc : tb * tb * (v * v) ∈ secCent Ka (O Ka) := mul_mem hbb hvv
  have hta2 : ta * ta = (tb * tb * (v * v))⁻¹ := eq_inv_of_mul_eq_one_left (by
    simpa [mul_assoc] using ht2)
  have hta2' : ta * ta ∈ secCent Ka (O Ka) := by rw [hta2]; exact inv_mem hc
  have htaS : ta ∈ S := htaP.1
  have hmem : ta * ta ∈ S ⊓ ZsM O Ka :=
    ⟨mul_mem htaS htaS, mul_mem htaK htaK, hta2'⟩
  rw [(h.S_inf_Zs_comp hp.left).2] at hmem
  rcases (mem_zpowers_of_sq h.z_sq).1 hmem with h1 | h1
  · exfalso
    apply hnot
    have hta1 : ta ∈ secCent Ka (O Ka) := by
      rcases h.inv_comp hp.left htaK h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact h.z_mem_secCent_comp hp.left
    exact mul_mem (mul_mem hta1 htb1) (h.Q_mem_secCent_comp hv hp.left)
  · exact h1

end M4

namespace M42

open M4

variable [Finite G]

theorem lemma42 (h : M42 O FA SD z S K₁ K₂)
    (hex : ∃ t ∈ Rm O S K₁ K₂, orderOf t = 2 ∧ IsConj z t ∧ t ≠ z) :
    (∀ u ∈ Pm S K₁ K₂, orderOf u = 2 → IsConj z u) ∧ Qm O S K₁ K₂ = zpowers z := by
  obtain ⟨t, htR, ht2, htz, htne⟩ := hex
  obtain ⟨ht2', ht1⟩ := orderOf_two_iff.1 ht2
  have htS : t ∈ S := Rm_le_S htR
  have htC : t ∈ centralizer ({z} : Set G) := h.S_syl.1 htS
  have htnot : t ∉ ZsM O (K₁ ⊔ K₂) := by
    intro htZ
    have : t ∈ S ⊓ ZsM O (K₁ ⊔ K₂) := ⟨htS, htZ⟩
    rw [h.S_inf_Zs] at this
    rcases (mem_zpowers_of_sq h.z_sq).1 this with h1 | h1
    · exact ht1 h1
    · exact htne h1
  have hD₁ := h.hc t htC htz htnot K₁ (Or.inl rfl)
  have hD₂ := h.hc t htC htz htnot K₂ (Or.inr rfl)
  obtain ⟨x, hx, v, hv, rfl⟩ := mem_sup_of_commute h.PQ_comm htR
  have hx' := hx
  rw [h.P_eq] at hx'
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ :=
    mem_sup_of_commute (A := Pm S K₁ K₂ ⊓ K₁) (B := Pm S K₁ K₂ ⊓ K₂)
      (fun a ha b hb => h.comm_of_S ha.2 hb.2 ha.1.1 hb.1.1) hx'
  have hcomm12 : t₁ * t₂ = t₂ * t₁ := h.comm_of_S ht₁.2 ht₂.2 ht₁.1.1 ht₂.1.1
  have hnot₁ : t₁ * t₂ * v ∉ secCent K₁ (O K₁) := by
    intro hs
    rcases h.unique_inv_D htC (Or.inl rfl) hD₁ hs (centralizer_comm htC)
      (by rfl) ht2' with h1 | h1
    · exact ht1 h1
    · exact htne h1
  have hnot₂ : t₁ * t₂ * v ∉ secCent K₂ (O K₂) := by
    intro hs
    rcases h.unique_inv_D htC (Or.inr rfl) hD₂ hs (centralizer_comm htC)
      (by rfl) ht2' with h1 | h1
    · exact ht1 h1
    · exact htne h1
  have hp₁ : IsPair K₁ K₂ K₁ K₂ := Or.inl ⟨rfl, rfl⟩
  have hp₂ : IsPair K₁ K₂ K₂ K₁ := Or.inr ⟨rfl, rfl⟩
  have hq₁ : t₁ * t₁ = z := h.pair_sq hp₁ ht₁ ht₂ hv ht2' hnot₁
  have hq₂ : t₂ * t₂ = z := by
    have ht2'' : t₂ * t₁ * v * (t₂ * t₁ * v) = 1 := by rw [← hcomm12]; exact ht2'
    have hnot₂' : t₂ * t₁ * v ∉ secCent K₂ (O K₂) := by rw [← hcomm12]; exact hnot₂
    exact h.pair_sq hp₂ ht₂ ht₁ hv ht2'' hnot₂'
  have hv_t₁ : v * t₁ = t₁ * v := h.Q_comm_P hv ht₁.1
  have hv_t₂ : v * t₂ = t₂ * v := h.Q_comm_P hv ht₂.1
  have hv2 : v * v = 1 := by
    have h1 : Commute (t₁ * t₂) v := (Commute.mul_left (hv_t₁.symm) (hv_t₂.symm))
    have h2 : (t₁ * t₂ * v) * (t₁ * t₂ * v) = (t₁ * t₁) * (t₂ * t₂) * (v * v) := by
      have := h1.mul_pow 2
      rw [(show Commute t₁ t₂ from hcomm12).mul_pow 2] at this
      simpa [pow_two, mul_assoc] using this
    rw [h2, hq₁, hq₂, h.z_sq, one_mul] at ht2'
    exact ht2'
  have hvt : v * (t₁ * t₂ * v) = (t₁ * t₂ * v) * v := by
    calc v * (t₁ * t₂ * v) = (v * t₁) * t₂ * v := by group
      _ = t₁ * (v * t₂) * v := by rw [hv_t₁]; group
      _ = t₁ * (t₂ * v) * v := by rw [hv_t₂]
      _ = (t₁ * t₂ * v) * v := by group
  have hvz : v = 1 ∨ v = z :=
    h.unique_inv_D htC (Or.inl rfl) hD₁ (h.Q_mem_secCent_comp hv (Or.inl rfl))
      (centralizer_comm (h.Q_le_C hv)) hvt hv2
  have hvP : v ∈ Pm S K₁ K₂ := by
    rcases hvz with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact h.z_mem_P
  have htP : t₁ * t₂ * v ∈ Pm S K₁ K₂ :=
    mul_mem (mul_mem (ht₁.1) (ht₂.1)) hvP
  have hfus : ∀ u ∈ Pm S K₁ K₂, orderOf u = 2 → IsConj z u := by
    intro u hu hu2
    obtain ⟨hu2', hu1⟩ := orderOf_two_iff.1 hu2
    by_cases huz : u = z
    · rw [huz]
    · obtain ⟨k, -, hk⟩ := h.f31a u (t₁ * t₂ * v) hu.2 htP.2 hu2' ht2' hu1 ht1 huz htne
      have hut : IsConj u (t₁ * t₂ * v) := isConj_iff.2 ⟨k, hk⟩
      exact htz.trans hut.symm
  refine ⟨hfus, ?_⟩
  have hQz : zpowers z ≤ Qm O S K₁ K₂ := zpowers_le.2 h.z_mem_Q
  apply le_antisymm ?_ hQz
  by_contra hQ
  have hex' : ∃ q ∈ Qm O S K₁ K₂, q ∉ zpowers z := by
    by_contra hne
    push Not at hne
    exact hQ (fun q hq => hne q hq)
  obtain ⟨q, hq, hqz⟩ := hex'
  have huniq : ∀ q' ∈ Qm O S K₁ K₂, q' * q' = 1 → q' = 1 ∨ q' = z := by
    intro q' hq' hq'2
    have hq't : q' * (t₁ * t₂ * v) = (t₁ * t₂ * v) * q' := h.Q_comm_P hq' htP
    exact h.unique_inv_D htC (Or.inl rfl) hD₁ (h.Q_mem_secCent_comp hq' (Or.inl rfl))
      (centralizer_comm (h.Q_le_C hq')) hq't hq'2
  have hQp : IsPGroup 2 ↥(Qm O S K₁ K₂) := h.S_pgroup.to_inf_left
  obtain ⟨w, hwQ, hw2⟩ := exists_sq_eq_of_unique_inv hQp huniq hq hqz
  have hw_t₂ : w * t₂ = t₂ * w := h.Q_comm_P hwQ ht₂.1
  have hw_t₁ : w * t₁ = t₁ * w := h.Q_comm_P hwQ ht₁.1
  have hy2 : (t₂ * w) * (t₂ * w) = 1 := by
    have h1 : Commute t₂ w := hw_t₂.symm
    have := h1.mul_pow 2
    simpa [pow_two, mul_assoc, hq₂, hw2, h.z_sq] using this
  have hwP : w ∈ Pm S K₁ K₂ → False := by
    intro hwP
    have : w ∈ zpowers z := h.P_inf_Q ⟨hwP, hwQ⟩
    rcases (mem_zpowers_of_sq h.z_sq).1 this with h1 | h1
    · rw [h1] at hw2; simp at hw2; exact h.z_ne hw2.symm
    · rw [h1] at hw2; exact h.z_ne (by simpa [h.z_sq] using hw2.symm)
  have hy1 : t₂ * w ≠ 1 := by
    intro h1
    apply hwP
    have : w = t₂⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]; exact inv_mem ht₂.1
  have hyz : t₂ * w ≠ z := by
    intro h1
    apply hwP
    have : w = t₂⁻¹ * z := by
      have := congrArg (fun x => t₂⁻¹ * x) h1
      simpa [mul_assoc] using this
    rw [this]; exact mul_mem (inv_mem ht₂.1) h.z_mem_P
  have hy_cent : (t₂ * w) * z = z * (t₂ * w) := by
    have h1 : t₂ * z = z * t₂ := centralizer_comm (h.K_le_C (mem_sup_right ht₂.2))
    have h2 : w * z = z * w := centralizer_comm (h.Q_le_C hwQ)
    calc t₂ * w * z = t₂ * (w * z) := by group
      _ = t₂ * (z * w) := by rw [h2]
      _ = (t₂ * z) * w := by group
      _ = (z * t₂) * w := by rw [h1]
      _ = z * (t₂ * w) := by group
  have hy_t : (t₂ * w) * (t₁ * t₂ * v) = (t₁ * t₂ * v) * (t₂ * w) := by
    have hvw : v * w = w * v := by
      rcases hvz with h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact (centralizer_comm (h.Q_le_C hwQ)).symm
    have hvt₂ : v * t₂ = t₂ * v := hv_t₂
    calc t₂ * w * (t₁ * t₂ * v) = t₂ * (w * t₁) * t₂ * v := by group
      _ = t₂ * (t₁ * w) * t₂ * v := by rw [hw_t₁]
      _ = t₂ * t₁ * (w * t₂) * v := by group
      _ = t₂ * t₁ * (t₂ * w) * v := by rw [hw_t₂]
      _ = t₁ * t₂ * t₂ * (w * v) := by
        rw [← hcomm12]; group
      _ = t₁ * t₂ * t₂ * (v * w) := by rw [hvw]
      _ = t₁ * t₂ * (t₂ * v) * w := by group
      _ = t₁ * t₂ * (v * t₂) * w := by rw [hv_t₂]
      _ = (t₁ * t₂ * v) * (t₂ * w) := by group
  have hy_sec : t₂ * w ∈ secCent K₁ (O K₁) :=
    mul_mem (h.cs₁ ht₂.2) (h.Q_mem_secCent_comp hwQ (Or.inl rfl))
  rcases h.unique_inv_D htC (Or.inl rfl) hD₁ hy_sec hy_cent hy_t hy2 with h1 | h1
  · exact hy1 h1
  · exact hyz h1

end M42

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
