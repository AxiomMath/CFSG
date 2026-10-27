module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_6

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G] [Finite G]

structure After127 (G : Type*) [Group G] [Finite G] (x z : G) (S T P Q Rd F : Subgroup G) :
    Prop where
  T_ne_S : T ≠ S
  exists_a : ∃ a ∈ S, a ∉ T ∧ (∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T) ∧ a * a ∈ T
  Q_eq : Q = Subgroup.zpowers x
  omega1_le : omega1 T ≤ Rd
  omega1_phi : ∀ V : Subgroup G, V ≤ P → IsFour V →
    omega1 (phi2 (centIn T (V ⊔ Subgroup.zpowers x))) ≤ Subgroup.zpowers x
  card_Z : Nat.card (omegaZ T) = 4 ∨ Nat.card (omegaZ T) = 8
  T_eq_Z : Nat.card (omegaZ T) = 8 → T = omegaZ T
  Z_eq : Nat.card (omegaZ T) = 4 → omegaZ T = Subgroup.zpowers x ⊔ Subgroup.zpowers z
  z_not_conj : Nat.card (omegaZ T) = 4 → ∀ g : G, g⁻¹ * x * g ≠ z ∧ g⁻¹ * (x * z) * g ≠ z
  sq_order_four : ∀ t ∈ T, orderOf t = 4 → t * t ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z
  Pstar_normal : Nat.card (omegaZ T) = 4 → (∀ g : G, g⁻¹ * x * g ∈ omegaZ T → g⁻¹ * x * g = x) →
    ∀ g : G, g⁻¹ * x * g ∈ T → g⁻¹ * x * g ≠ x →
      NormalIn (P ⊔ Subgroup.zpowers (g⁻¹ * x * g)) T ∧ Q = Subgroup.zpowers x

theorem exists_sq_mem_normalizer {S T : Subgroup G} (hS : IsPGroup 2 ↥S) (hTS : T < S) :
    ∃ a ∈ S, a ∉ T ∧ (∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T) ∧ a * a ∈ T := by
  obtain ⟨a₀, ha₀S, ha₀T, ha₀n⟩ := exists_mem_normalizer_of_lt hS hTS
  obtain ⟨k, hk⟩ := hS ⟨a₀, ha₀S⟩
  have hk' : a₀ ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hex : ∃ j : ℕ, a₀ ^ (2 ^ j) ∈ T := ⟨k, by rw [hk']; exact T.one_mem⟩
  classical
  obtain ⟨j, hj, hjmin⟩ : ∃ j : ℕ, a₀ ^ (2 ^ j) ∈ T ∧ ∀ m < j, a₀ ^ (2 ^ m) ∉ T :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hj0 : j ≠ 0 := by
    intro h0
    apply ha₀T
    have : a₀ ^ (2 ^ j) = a₀ := by rw [h0]; simp
    rw [← this]; exact hj
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hnot : a₀ ^ (2 ^ i) ∉ T := hjmin i (by omega)
  have hpow : ∀ m : ℕ, ∀ t : G, t ∈ T ↔ a₀ ^ m * t * (a₀ ^ m)⁻¹ ∈ T := by
    intro m
    induction m with
    | zero => intro t; simp
    | succ m ih =>
      intro t
      have e : a₀ ^ (m + 1) * t * (a₀ ^ (m + 1))⁻¹ =
          a₀ ^ m * (a₀ * t * a₀⁻¹) * (a₀ ^ m)⁻¹ := by
        rw [pow_succ]
        generalize a₀ ^ m = w
        group
      rw [e, ← ih (a₀ * t * a₀⁻¹)]
      exact ha₀n t
  refine ⟨a₀ ^ (2 ^ i), S.pow_mem ha₀S _, hnot, fun t => hpow _ t, ?_⟩
  have h2 : 2 ^ i + 2 ^ i = 2 ^ j := by rw [hi, pow_succ]; ring
  rw [← pow_add, h2]
  exact hj

variable {x z : G} {S T P Q Rd F : Subgroup G}

theorem HBase.exists_HZ (h : HBase G x S T P Q Rd F) (hP4 : IP_P_four P) :
    ∃ z : G, HZ T P z := by
  have hne : P ≠ ⊥ := by
    obtain ⟨V, hVP, hV⟩ := hP4
    intro hbot
    have hVbot : V = ⊥ := le_bot_iff.1 (hbot ▸ hVP)
    have h4 := hV.2
    rw [hVbot] at h4
    simp at h4
  obtain ⟨u, hu, hu1, hu2, huc⟩ :=
    exists_central_involution_of_normal h.T_pgroup h.P_le_T h.P_normal.2 hne
  exact ⟨u, ⟨hu, hu2, hu1, huc⟩⟩


theorem after_12_7 {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}
    (hZ : IG_15_3) (hBur : IG_16_2) (h : HBase G x S T P Q Rd F)
    (hz : HZ T P z) (hout : IP_outer x T Rd) (hcf : IP_cent_four T P Q Rd) (hP4 : IP_P_four P)
    (hRf : IP_Rd_factor T P Q Rd) (hconj : IP_P_conj x z P) (htrans : IP_P_trans P Q Rd)
    (hCRd : IP_cent_Rd P Q Rd) (hexp : IP_cent_P_exp T P Q) (hST : T ≠ S) :
    After127 G x z S T P Q Rd F where
  T_ne_S := hST
  exists_a := exists_sq_mem_normalizer h.S_pgroup (lt_of_le_of_ne h.T_le_S hST)
  Q_eq := lemma_12_6 hZ hBur h hz hout hcf hP4 hRf hconj htrans hCRd hexp
  omega1_le := (lemma_12_2 h hout hcf).1
  omega1_phi := (lemma_12_2 h hout hcf).2
  card_Z := h.card_Z hz
  T_eq_Z := lemma_12_3b hZ hBur h hout hcf hP4 hCRd
  Z_eq := h.Z_eq hz
  z_not_conj := fun h4 => lemma_12_3a h hz hP4 h4
  sq_order_four := fun _ ht ht4 => lemma_12_4 h hz hout hcf hP4 hRf ht ht4
  Pstar_normal := fun h4 hwc g huT hux =>
    lemma_12_5 h hz hout hcf hP4 hRf hconj htrans h4 hwc g huT hux

end CFSG.GH74.GLS.Stage1.Thm6.Sec12
