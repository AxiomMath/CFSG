module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_8Aux

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

theorem part_a4 (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (h127 : After127 G x z S T P Q Rd F)
    (h4 : Nat.card (omegaZ T) = 4) {a : G} (haS : a ∈ S) (haT : a ∉ T)
    (haTn : ∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T) : a⁻¹ * x * a = x * z := by
  have hu : a⁻¹ * x * a ∈ omegaZ T := omegaZ_conj_inv_mem haTn h.x_mem_Z
  have hne : a⁻¹ * x * a ≠ x := by
    intro hh
    apply haT
    apply h.extremal a haS
    calc a * x = a * (a⁻¹ * x * a) := by rw [hh]
      _ = x * a := by group
  have hne1 : a⁻¹ * x * a ≠ 1 := by
    intro hh
    apply h.x_ne_one
    calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
      _ = 1 := by rw [hh]; group
  rcases h.Z_cases hz h4 _ hu with h1 | h1 | h1 | h1
  · exact absurd h1 hne1
  · exact absurd h1 hne
  · exact absurd h1 (h127.z_not_conj h4 a).1
  · exact h1

theorem part_b4 (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (h127 : After127 G x z S T P Q Rd F)
    (h4 : Nat.card (omegaZ T) = 4) (hexp : IP_cent_P_exp T P Q) {a : G} (haS : a ∈ S)
    (haT : a ∉ T) (haTn : ∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T) {s : G} (hsT : s ∈ T)
    (hsc : ∀ s' ∈ S, s * s' = s' * s) : s ∈ omegaZ T ⊓ P := by
  have hsq : s * s ∈ Q := hexp s hsT (fun p hp => hsc p (h.T_le_S (h.P_le_T hp)))
  rw [h127.Q_eq] at hsq
  have hs2 : s * s = 1 := by
    rcases zpowers_sq_cases h.x_sq hsq with h1 | h1
    · exact h1
    · exfalso
      apply haT
      apply h.extremal a haS
      have h2 := hsc a haS
      calc a * x = a * (s * s) := by rw [h1]
        _ = (a * s) * s := by group
        _ = (s * a) * s := by rw [h2]
        _ = s * (a * s) := by group
        _ = s * (s * a) := by rw [h2]
        _ = x * a := by rw [← h1]; group
  have hsZ : s ∈ omegaZ T := ⟨hsT, hs2, fun t ht => hsc t (h.T_le_S ht)⟩
  rcases h.Z_cases hz h4 s hsZ with h1 | h1 | h1 | h1
  · rw [h1]; exact (omegaZ T ⊓ P).one_mem
  · exfalso
    apply haT
    apply h.extremal a haS
    have h2 := hsc a haS
    rw [h1] at h2
    exact h2.symm
  · rw [h1]; exact Subgroup.mem_inf.2 ⟨hz.mem_Z h.P_le_T, hz.z_mem_P⟩
  · exfalso
    have ha := part_a4 h hz h127 h4 haS haT haTn
    have h2 := hsc a haS
    rw [h1] at h2
    have e1 : a⁻¹ * (x * z) * a = x * z := by
      calc a⁻¹ * (x * z) * a = a⁻¹ * ((x * z) * a) := by group
        _ = a⁻¹ * (a * (x * z)) := by rw [h2]
        _ = x * z := by group
    have e2 : a⁻¹ * (x * z) * a = (a⁻¹ * x * a) * (a⁻¹ * z * a) := by group
    rw [ha] at e2
    have e3 : a⁻¹ * z * a = 1 := by
      have := e1.symm.trans e2
      exact mul_left_cancel (a := x * z) (by rw [mul_one]; exact this.symm)
    apply hz.z_ne_one
    calc z = a * (a⁻¹ * z * a) * a⁻¹ := by group
      _ = 1 := by rw [e3]; group

theorem part_ab8 (h : HBase G x S T P Q Rd F) (h127 : After127 G x z S T P Q Rd F)
    (hf3 : IP_f3 x P) (hzV : IP_z_V z P) (hP4 : IP_P_four P) (h8 : Nat.card (omegaZ T) = 8)
    {a : G} (haS : a ∈ S) (haT : a ∉ T) (haTn : ∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T) :
    (∃ w : G, w ∈ omegaZ T ⊓ P ∧ w ≠ 1 ∧ a⁻¹ * x * a = x * w) ∧
      (∀ s : G, s ∈ T → (∀ s' ∈ S, s * s' = s' * s) → s ∈ omegaZ T ⊓ P) := by
  obtain ⟨V, hVP, hV⟩ := hP4
  have hTZ := h127.T_eq_Z h8
  have hEq : V ⊔ Subgroup.zpowers x = T := by
    have hT8 : Nat.card ↥T = 8 := (congrArg (fun K : Subgroup G => Nat.card ↥K) hTZ).trans h8
    exact Subgroup.eq_of_le_of_card_ge (E_le_T h hVP) (by rw [hT8, card_E h hVP hV])
  have haN : a⁻¹ ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [hEq, Subgroup.mem_normalizer_iff]
    intro t
    exact normalizes_inv haTn t
  obtain ⟨f, y, c⟩ := exists_ctx h h127 hf3 hzV hVP hV (S.inv_mem haS)
    (fun hh => haT (by simpa using T.inv_mem hh)) haN
  have hTomega : ∀ t ∈ T, t ∈ omegaZ T := fun t ht => by rw [← hTZ]; exact ht
  refine ⟨?_, ?_⟩
  · obtain ⟨u0, hu0, hu01, hu⟩ := c.struct
    refine ⟨u0, Subgroup.mem_inf.2 ⟨hTomega _ (h.P_le_T (hVP hu0)), hVP hu0⟩, hu01, ?_⟩
    simpa using hu
  · intro s hsT hsc
    have hsE : s ∈ V ⊔ Subgroup.zpowers x := by rw [hEq]; exact hsT
    have hs : s ∈ V := (c.V_iff hsE).2 (not_conjTo_central h h127.T_ne_S hsc)
    exact Subgroup.mem_inf.2 ⟨hTomega s hsT, hVP hs⟩

theorem lemma_12_8 :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (S T P Q Rd F : Subgroup G) (z : G),
      HBase G x S T P Q Rd F → HZ T P z → After127 G x z S T P Q Rd F → IP_P_four P →
      IP_f3 x P → IP_z_V z P → IP_cent_P_exp T P Q → ∀ a : G, a ∈ S → a ∉ T →
        (∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T) → a * a ∈ T →
        (∃ w : G, w ∈ omegaZ T ⊓ P ∧ w ≠ 1 ∧ a⁻¹ * x * a = x * w) ∧
        (∀ s : G, s ∈ T → (∀ s' ∈ S, s * s' = s' * s) → s ∈ omegaZ T ⊓ P) ∧
        ∀ V : Subgroup G, V ≤ P → IsFour V →
          (∃ t ∈ T, a * t⁻¹ ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) →
          (∀ v ∈ V, ∃ g : G, g ∈ Subgroup.centralizer (V : Set G) ∧
            g ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ∧
              g * x * g⁻¹ = x * v) ∧
          (IsSylow2In (S ⊓ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))
            (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) → 2 < T.relIndex S) := by
  intro G _ _ x S T P Q Rd F z h hz h127 hP4 hf3 hzV hexp a haS haT haTn _ha2
  have hab : (∃ w : G, w ∈ omegaZ T ⊓ P ∧ w ≠ 1 ∧ a⁻¹ * x * a = x * w) ∧
      (∀ s : G, s ∈ T → (∀ s' ∈ S, s * s' = s' * s) → s ∈ omegaZ T ⊓ P) := by
    rcases h127.card_Z with h4 | h8
    · exact ⟨⟨z, Subgroup.mem_inf.2 ⟨hz.mem_Z h.P_le_T, hz.z_mem_P⟩, hz.z_ne_one,
        part_a4 h hz h127 h4 haS haT haTn⟩,
        fun s hsT hsc => part_b4 h hz h127 h4 hexp haS haT haTn hsT hsc⟩
    · exact part_ab8 h h127 hf3 hzV hP4 h8 haS haT haTn
  refine ⟨hab.1, hab.2, ?_⟩
  intro V hVP hV ⟨t, htT, htN⟩
  have haS' : a * t⁻¹ ∈ S := S.mul_mem haS (S.inv_mem (h.T_le_S htT))
  have haT' : a * t⁻¹ ∉ T := fun hh => haT (by simpa using T.mul_mem hh htT)
  refine ⟨fusion_V h h127 hf3 hzV hVP hV haS' haT' htN, fun hsyl => ?_⟩
  obtain ⟨f, y, c⟩ := exists_ctx h h127 hf3 hzV hVP hV haS' haT' htN
  exact two_lt_relIndex_of_sylow h c hsyl

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
