module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9a
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Dihedral

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

theorem dihData_of_dih {G : Type*} [Group G] [Finite G] {D T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hDT : D ≤ T) (hD : IsDihedral2 D) (h8 : 8 ≤ Nat.card D) :
    ∃ ρ s : G, ∃ j : ℕ, DihData D ρ s j := by
  classical
  obtain ⟨ρ, s, hρ, hs, hs2, hsρ, hel⟩ := hD
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨ρ, hDT hρ⟩
  have hk' : orderOf ρ = 2 ^ k := by rw [← hk]; exact (Subgroup.orderOf_mk ρ (hDT hρ)).symm
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exfalso
    have hρ2 : ρ * ρ = 1 := by
      have h1 : ρ ^ orderOf ρ = 1 := pow_orderOf_eq_one ρ
      interval_cases k
      · rw [hk'] at h1
        have h' : ρ = 1 := by simpa using h1
        rw [h', mul_one]
      · rw [hk'] at h1; simpa [pow_two] using h1
    have hsub : (D : Set G) ⊆ ((({1, ρ, s, s * ρ} : Finset G)) : Set G) := by
      intro d hd
      obtain ⟨i, rfl | rfl⟩ := hel d hd
      · rcases zpowers_sq_cases hρ2 (Subgroup.mem_zpowers_iff.2 ⟨i, rfl⟩) with e | e <;>
          simp [e]
      · rcases zpowers_sq_cases hρ2 (Subgroup.mem_zpowers_iff.2 ⟨i, rfl⟩) with e | e <;>
          simp [e]
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : Nat.card D = (D : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]; rfl
    have h4 : ({1, ρ, s, s * ρ} : Finset G).card ≤ 4 := Finset.card_le_four
    omega
  · refine ⟨ρ, s, k - 2, ⟨hρ, hs, hs2, hsρ, hel, ?_⟩⟩
    rw [hk']
    have : k = (k - 2) + 2 := by omega
    rw [this, pow_add]
    norm_num
    ring

structure Ph1 (G : Type) [Group G] [Finite G] (x z : G) (T P Rd : Subgroup G) (a : G)
    (V P₁ F' : Subgroup G) : Prop where
  V_le : V ≤ P
  V_four : IsFour V
  z_V : z ∈ V
  P_le : P ≤ P₁
  le_Rd : P₁ ≤ Rd
  inf_x : P₁ ⊓ Subgroup.zpowers x = ⊥
  sup_x : P₁ ⊔ Subgroup.zpowers x = Rd
  dih : IsDihedral2 P₁
  big : 8 ≤ Nat.card P₁
  cases : P₁ = P ∨ ∃ u : G, u ∈ Hconj a V ∧ u * u = 1 ∧ u ∉ P ⊔ Subgroup.zpowers x ∧
    P₁ = P ⊔ Subgroup.zpowers u
  F_le : F' ≤ T
  x_le : Subgroup.zpowers x ≤ F'
  F_cyc : IsCyclic F'
  F_inf : F' ⊓ Rd = Subgroup.zpowers x
  T_eq : Rd ⊔ F' = T
  F_c1 : ∀ w ∈ F', w ^ 4 = 1 → (∀ p ∈ P, w * p = p * w) ∧
    ∀ b ∈ Rd, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z
  F_c3 : Nat.card P = 4 → F' = Subgroup.zpowers x
  F_c4 : 8 ≤ Nat.card P → ∀ t ∈ T, (∀ p ∈ P, t * p = p * t) →
    ∃ u ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z, ∃ w ∈ F', w ^ 4 = 1 ∧ t = u * w

section

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

namespace Hyp129

variable (H : Hyp129 G x z S T P Q Rd F)
include H

theorem exists_ph1 {a : G} (A : Ph0 G x z S T P a) :
    ∃ V P₁ F' : Subgroup G, Ph1 G x z T P Rd a V P₁ F' := by
  obtain ⟨V, hVP, hV⟩ := H.P4
  have hzV : z ∈ V := H.zV V hVP hV
  obtain ⟨F', hF'T, hxF', hFcyc, hFinf, hTeq, hc1, hc3, hc4⟩ : ∃ F' : Subgroup G, F' ≤ T ∧
      Subgroup.zpowers x ≤ F' ∧ IsCyclic F' ∧ F' ⊓ Rd = Subgroup.zpowers x ∧ Rd ⊔ F' = T ∧
      (∀ w ∈ F', w ^ 4 = 1 → (∀ p ∈ P, w * p = p * w) ∧
        ∀ b ∈ Rd, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z) ∧
      (Nat.card P = 4 → F' = Subgroup.zpowers x) ∧
      (8 ≤ Nat.card P → ∀ t ∈ T, (∀ p ∈ P, t * p = p * t) →
        ∃ u ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z, ∃ w ∈ F', w ^ 4 = 1 ∧ t = u * w) := by
    rcases H.Tn with hI | hII
    · exfalso
      obtain ⟨t, htT, e⟩ := hI (V ⊔ Subgroup.zpowers x) (Hconj a V ⊔ Subgroup.zpowers x)
        (H.EV_le_Rd hVP) (Ph0.EW_le_Rd H A hVP hV) (H.EV_isElemAb2 hVP hV)
        (Ph0.EW_isElemAb2 H A hVP hV) (H.EV_card hVP hV) (Ph0.EW_card H A hVP hV hzV)
      exact Ph0.not_Tconj H A hVP hV htT ((Ph0.EV_conj H A hzV).trans e)
    · obtain ⟨F', h1, h2, h3, h4, h5, h6, h7, h8⟩ := hII
      exact ⟨F', h1, h2, h3, h4, h5, h6, h7, h8⟩
  by_cases hR : P ⊔ Subgroup.zpowers x = Rd
  ·
    have hinf : P ⊓ Subgroup.zpowers x = ⊥ := by
      rw [← H.h127.Q_eq]; exact H.base.PQ_disjoint
    have hP8 : 8 ≤ Nat.card P := by
      by_contra hlt
      have hlt' : Nat.card P < 8 := not_le.1 hlt
      have hP4' : 4 ≤ Nat.card P := by
        have := Subgroup.card_le_of_le hVP
        rwa [hV.2] at this
      have hpg : IsPGroup 2 ↥P := H.base.T_pgroup.to_le H.base.P_le_T
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
      have hP4 : Nat.card P = 4 := by
        by_cases hn2 : n ≤ 2
        · interval_cases n
          · rw [pow_zero] at hn; omega
          · rw [pow_one] at hn; omega
          · rw [hn]; norm_num
        · exfalso
          have h8' : (8 : ℕ) ≤ 2 ^ n := by
            calc 8 = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      have hVP' : V = P := Subgroup.eq_of_le_of_card_ge hVP (by rw [hP4, hV.2])
      have hEV : V ⊔ Subgroup.zpowers x = Rd := by rw [hVP', hR]
      have hEW : Hconj a V ⊔ Subgroup.zpowers x = V ⊔ Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge (by rw [hEV]; exact Ph0.EW_le_Rd H A hVP hV)
          (by rw [H.EV_card hVP hV, Ph0.EW_card H A hVP hV hzV])
      exact Ph0.not_Tconj H A hVP hV (t := 1) T.one_mem
        (by rw [Ph0.EV_conj H A hzV, hEW, Hconj_one])
    exact ⟨V, P, F', ⟨hVP, hV, hzV, le_rfl, H.P_le_Rd, hinf, hR, H.dih P H.P_le_Rd hinf hR, hP8,
      Or.inl rfl, hF'T, hxF', hFcyc, hFinf, hTeq, hc1, hc3, hc4⟩⟩
  ·
    have hWnR : ¬ Hconj a V ≤ P ⊔ Subgroup.zpowers x := by
      intro hle
      obtain ⟨r, hrRd, e⟩ := H.fuse hR (V ⊔ Subgroup.zpowers x) (Hconj a V ⊔ Subgroup.zpowers x)
        (sup_le (hVP.trans le_sup_left) le_sup_right) (sup_le hle le_sup_right)
        (H.EV_isElemAb2 hVP hV) (Ph0.EW_isElemAb2 H A hVP hV) (H.EV_card hVP hV)
        (Ph0.EW_card H A hVP hV hzV)
      exact Ph0.not_Tconj H A hVP hV (H.base.Rd_le_T hrRd) ((Ph0.EV_conj H A hzV).trans e)
    obtain ⟨u, huW, huR⟩ := IsConcreteLE.not_le_iff_exists.1 hWnR
    have hu2 : u * u = 1 := ((Ph0.W_isFour hV).1 u huW).1
    have huT : u ∈ T := Ph0.W_le_T H A hVP huW
    have huRd : u ∈ Rd := Ph0.W_le_Rd H A hVP hV huW
    have hmem : ∀ y ∈ P ⊔ Subgroup.zpowers u, y ∈ P ∨ ∃ p ∈ P, y = u * p := by
      intro y hy
      obtain ⟨a', ha', p, hp, rfl⟩ := mem_sup_zpowers_of_normalIn H.base.P_normal huT hy
      rcases zpowers_sq_cases hu2 ha' with e | e
      · left; rw [e, one_mul]; exact hp
      · right; exact ⟨p, hp, by rw [e]⟩
    have hinf : (P ⊔ Subgroup.zpowers u) ⊓ Subgroup.zpowers x = ⊥ := by
      rw [eq_bot_iff]
      rintro c ⟨hcP1, hcx⟩
      rcases zpowers_sq_cases H.base.x_sq hcx with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · exfalso
        rw [h1] at hcP1
        rcases hmem _ hcP1 with hxP | ⟨p, hp, hxp⟩
        · exact H.base.x_not_mem_P hxP
        · apply huR
          have : u = x * p⁻¹ := by rw [hxp]; group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
            (Subgroup.mem_sup_left (P.inv_mem hp))
    have hmono : P ⊔ Subgroup.zpowers x ≤ (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers x :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    have hsup : (P ⊔ Subgroup.zpowers u) ⊔ Subgroup.zpowers x = Rd := by
      apply le_antisymm
      · exact sup_le (sup_le H.P_le_Rd ((Subgroup.zpowers_le).2 huRd))
          ((Subgroup.zpowers_le).2 H.x_mem_Rd)
      · intro r hr
        by_cases hrR : r ∈ P ⊔ Subgroup.zpowers x
        · exact hmono hrR
        · have hR2 : (P ⊔ Subgroup.zpowers x).relIndex Rd ≤ 2 := by
            have := H.base.R_index_le_two
            rwa [H.h127.Q_eq] at this
          have h1 := relIndex_two_mul_mem hR2 hr (Rd.inv_mem huRd) hrR
            (fun h => huR (by simpa using (P ⊔ Subgroup.zpowers x).inv_mem h))
          have : r = (r * u⁻¹) * u := by group
          rw [this]
          exact Subgroup.mul_mem _ (hmono h1)
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)))
    have hne : P ≠ P ⊔ Subgroup.zpowers u := by
      intro e
      apply huR
      have : u ∈ P := by rw [e]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
      exact Subgroup.mem_sup_left this
    have hbig : 8 ≤ Nat.card (P ⊔ Subgroup.zpowers u : Subgroup G) := by
      have hP4' : 4 ≤ Nat.card P := by
        have := Subgroup.card_le_of_le hVP
        rwa [hV.2] at this
      obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : P ≤ P ⊔ Subgroup.zpowers u)
      have hm1 : m ≠ 1 := fun h => hne (Subgroup.eq_of_le_of_card_ge le_sup_left
        (by rw [hm, h, mul_one]))
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := Nat.card_pos (α := ↥(P ⊔ Subgroup.zpowers u))
        omega
      have hm2 : 2 ≤ m := by omega
      calc 8 = 4 * 2 := by norm_num
        _ ≤ Nat.card P * m := Nat.mul_le_mul hP4' hm2
        _ = _ := hm.symm
    have hleRd : P ⊔ Subgroup.zpowers u ≤ Rd :=
      sup_le H.P_le_Rd ((Subgroup.zpowers_le).2 huRd)
    exact ⟨V, P ⊔ Subgroup.zpowers u, F', ⟨hVP, hV, hzV, le_sup_left, hleRd, hinf, hsup,
      H.dih _ hleRd hinf hsup, hbig, Or.inr ⟨u, huW, hu2, huR, rfl⟩, hF'T, hxF', hFcyc, hFinf,
      hTeq, hc1, hc3, hc4⟩⟩

end Hyp129

end

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
