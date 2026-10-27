module

public import CFSG.HardMathSupport.Foote.E27.Defs

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem eq_of_lt_card {T S R : Subgroup X} (hTS : T ≤ S) (hSR : S ≤ R) (hne : T ≠ S)
    (hR : Nat.card R = 27) (hT : Nat.card T = 9) : S = R := by
  have h1 : Nat.card S ∣ 27 := hR ▸ Subgroup.card_dvd_of_le hSR
  have h2 : 9 ∣ Nat.card S := hT ▸ Subgroup.card_dvd_of_le hTS
  have h3 : Nat.card S ≠ 9 := fun h => hne (Subgroup.eq_of_le_of_card_ge hTS (by omega))
  have h4 : Nat.card S = 27 := by
    obtain ⟨k, hk⟩ := h2
    have hk3 : k ≤ 3 := by
      have : Nat.card S ≤ 27 := Nat.le_of_dvd (by norm_num) h1
      omega
    rw [hk] at h1 h3 ⊢
    interval_cases k <;> omega
  exact Subgroup.eq_of_le_of_card_ge hSR (by rw [hR, h4])

theorem E27Config.le_of_mem (h : E27Config X K R T z) (hz : z ∈ K) : R ≤ K := by
  have hzT : T < T ⊔ zpowers z := lt_of_le_of_ne le_sup_left fun he =>
    h.z_not_mem (he ▸ (le_sup_right : zpowers z ≤ T ⊔ zpowers z) (mem_zpowers z))
  have hS : T ⊔ zpowers z ≤ R := sup_le h.T_le_R ((zpowers_le).mpr h.z_mem)
  have := eq_of_lt_card le_sup_left hS hzT.ne h.card_R h.card_T
  rw [← this]
  exact sup_le h.T_le_K ((zpowers_le).mpr hz)

theorem E27Config.inf_eq_of_not_mem (h : E27Config X K R T z) (hz : z ∉ K) : R ⊓ K = T := by
  have hle : T ≤ R ⊓ K := le_inf h.T_le_R h.T_le_K
  by_contra hne
  have := eq_of_lt_card hle inf_le_left (Ne.symm hne) h.card_R h.card_T
  have hz' : z ∈ R ⊓ K := by rw [this]; exact h.z_mem
  exact hz hz'.2

theorem E27Config.card_le_nine_of_isPGroup (h : E27Config X K R T z) (hz : z ∉ K)
    {Q : Subgroup X} (hQ : Q ≤ centralizer ({z} : Set X) ⊓ K) (hQ3 : IsPGroup 3 Q) :
    Nat.card Q ≤ 9 := by
  obtain ⟨S, hS⟩ := h.sylow
  have hQC : Q ≤ centralizer ({z} : Set X) := hQ.trans inf_le_left
  have hQK : Q ≤ K := hQ.trans inf_le_right
  have hQ1 : IsPGroup 3 (Q.subgroupOf (centralizer ({z} : Set X))) := hQ3.comap_subtype
  obtain ⟨P, hP⟩ := hQ1.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(centralizer ({z} : Set X))) S P
  have hT := h.inf_eq_of_not_mem hz
  have key : ∀ q : Q, ((g : X)⁻¹ * q * g : X) ∈ T := by
    intro q
    have h1 : (⟨q, hQC q.2⟩ : ↥(centralizer ({z} : Set X))) ∈
        ((g • S : Sylow 3 ↥(centralizer ({z} : Set X))) : Subgroup _) := by
      rw [hg]; exact hP q.2
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : ((g : X)⁻¹ * q * g : X) ∈ R := by
      have := Subgroup.mem_map_of_mem (Subgroup.subtype (centralizer ({z} : Set X))) h1
      rw [hS] at this
      simpa [MulAut.smul_def] using this
    have h3 : ((g : X)⁻¹ * q * g : X) ∈ K := by
      have := h.normal.conj_mem q (hQK q.2) (g : X)⁻¹
      simpa using this
    rw [← hT]
    exact ⟨h2, h3⟩
  have hinj : Function.Injective (fun q : Q => (⟨(g : X)⁻¹ * q * g, key q⟩ : T)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only at this
    exact Subtype.ext (by simpa using this)
  calc Nat.card Q ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
    _ = 9 := h.card_T

theorem E27Config.isSylow_centralizer_of_not_mem (h : E27Config X K R T z) (hz : z ∉ K) :
    ∃ S : Sylow 3 ↥(centralizer ({z} : Set X) ⊓ K),
      Subgroup.map (centralizer ({z} : Set X) ⊓ K).subtype
        (S : Subgroup ↥(centralizer ({z} : Set X) ⊓ K)) = T := by
  set D := centralizer ({z} : Set X) ⊓ K with hD
  have hTD : T ≤ D := by
    refine le_inf ?_ h.T_le_K
    intro t ht
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (h.elem.1.is_comm.comm (⟨t, h.T_le_R ht⟩ : R) ⟨z, h.z_mem⟩)
  let T' : Subgroup ↥D := T.subgroupOf D
  have hT'card : Nat.card T' = 9 := by
    rw [← h.card_T]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTD).toEquiv
  have hT'p : IsPGroup 3 T' := by
    have : Nat.card T' = 3 ^ 2 := by rw [hT'card]; norm_num
    exact IsPGroup.of_card this
  obtain ⟨Q, hQ⟩ := hT'p.exists_le_sylow
  have hQp : IsPGroup 3 (Subgroup.map D.subtype (Q : Subgroup ↥D)) := Q.isPGroup'.map _
  have hQle : Nat.card (Subgroup.map D.subtype (Q : Subgroup ↥D)) ≤ 9 :=
    h.card_le_nine_of_isPGroup hz (by rintro _ ⟨x, -, rfl⟩; exact x.2) hQp
  have hQcard : Nat.card (Q : Subgroup ↥D) ≤ 9 := by
    rwa [Subgroup.card_map_of_injective D.subtype_injective] at hQle
  have hQeq : T' = (Q : Subgroup ↥D) :=
    Subgroup.eq_of_le_of_card_ge hQ (by omega)
  refine ⟨Q, ?_⟩
  rw [← hQeq]
  exact Subgroup.map_subgroupOf_eq_of_le hTD

end CFSG.HardMathSupport.Foote.E27
