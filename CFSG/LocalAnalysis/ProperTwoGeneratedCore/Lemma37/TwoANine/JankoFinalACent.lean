module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalAW

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal

open Subgroup JankoTwelve

variable {G : Type} [Group G]

theorem conj_comm_eq_inv {v u s : G} (hvu : v * u * v⁻¹ = u) (hvs : v * s * v⁻¹ = s⁻¹)
    (hc : (u * s * u⁻¹)⁻¹ * s = s * (u * s * u⁻¹)⁻¹) :
    v * (u * s * u⁻¹ * s⁻¹) * v⁻¹ = (u * s * u⁻¹ * s⁻¹)⁻¹ := by
  calc v * (u * s * u⁻¹ * s⁻¹) * v⁻¹
      = (v * u * v⁻¹) * (v * s * v⁻¹) * (v * u * v⁻¹)⁻¹ * (v * s * v⁻¹)⁻¹ := by group
    _ = (u * s * u⁻¹)⁻¹ * s := by rw [hvu, hvs]; group
    _ = s * (u * s * u⁻¹)⁻¹ := hc
    _ = (u * s * u⁻¹ * s⁻¹)⁻¹ := by group

variable [Finite G] {z : G} {fr : JankoFrame G z} {m s : G} (h : Hyp fr)
  (p12 : JankoProp12 fr) (hm : JankoChoiceM fr m)
  (hs : fr.E ⊓ centralizer ({m} : Set G) = zpowers s) (hs3 : orderOf s = 3)

include h p12 hs in
theorem conj_comm_mem {v u : G} (hu : u ∈ fr.U ⊓ centralizer ({v} : Set G))
    (hvs : v * s * v⁻¹ = s⁻¹) :
    u * s * u⁻¹ * s⁻¹ ∈ fr.S ∧ v * (u * s * u⁻¹ * s⁻¹) * v⁻¹ = (u * s * u⁻¹ * s⁻¹)⁻¹ := by
  have hsI : s ∈ fr.I := E_le_I (s_mem_E hs)
  refine ⟨comm_mem_S h p12 hsI hu.1, conj_comm_eq_inv ?_ hvs ?_⟩
  · rw [← mem_centralizer_singleton_iff.mp hu.2, mul_inv_cancel_right]
  · have haI : u * s * u⁻¹ ∈ fr.I := (mem_normalizer_iff.mp (p12.U_le_normalizer_I hu.1) s).mp hsI
    exact h.p11.I_comm _ (inv_mem haI) s hsI

theorem le_card_of_comm_mem {v : G} {Q : Subgroup G} (hQ : Nat.card Q = 3)
    (hv : Nat.card (fr.U ⊓ centralizer ({v} : Set G) : Subgroup G) = 3 ^ 4)
    (hsub : ∀ u ∈ fr.U ⊓ centralizer ({v} : Set G), u * s * u⁻¹ * s⁻¹ ∈ Q) :
    27 ≤ Nat.card (fr.U ⊓ centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G) :
      Subgroup G) := by
  have h1 := card_conj_orbit_mul (fr.U ⊓ centralizer ({v} : Set G)) s
  have hsub' : {y | ∃ u ∈ fr.U ⊓ centralizer ({v} : Set G), u * s * u⁻¹ = y} ⊆
      (fun q => q * s) '' (Q : Set G) := by
    rintro y ⟨u, hu, rfl⟩
    exact ⟨u * s * u⁻¹ * s⁻¹, hsub u hu, by group⟩
  have h2 : {y | ∃ u ∈ fr.U ⊓ centralizer ({v} : Set G), u * s * u⁻¹ = y}.ncard ≤ 3 := by
    calc _ ≤ ((fun q => q * s) '' (Q : Set G)).ncard := Set.ncard_le_ncard hsub' (Set.toFinite _)
      _ ≤ (Q : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 3 := by rw [← Nat.card_coe_set_eq]; exact hQ
  rw [hv] at h1
  have : 3 ^ 4 ≤ 3 * Nat.card (fr.U ⊓ centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G) :
      Subgroup G) := by
    rw [← h1]; exact Nat.mul_le_mul_right _ h2
  omega

include h p12 hs in
theorem X_inf_z : fr.U ⊓ centralizer ({s} : Set G) ⊓ centralizer ({z} : Set G) = fr.E := by
  refine le_antisymm (fun x hx => ?_) (le_inf (le_inf (h.E_le_N.trans h.N_le_U) fun e he =>
    mem_centralizer_singleton_iff.mpr (fr.E_comm e he s (s_mem_E hs))) fr.E_le)
  rw [← p12.U_inf_centralizer_z]
  exact ⟨hx.1.1, hx.2⟩

include h p12 hs in
theorem X_inf_t_inf_z : fr.U ⊓ centralizer ({s} : Set G) ⊓ centralizer ({fr.t} : Set G) ⊓
    centralizer ({z} : Set G) = fr.P₂ := by
  rw [inf_right_comm, X_inf_z h p12 hs, fr.E_inf_centralizer_t]

include h hs in
theorem z_mem_normalizer_X :
    z ∈ normalizer ((fr.U ⊓ centralizer ({s} : Set G) : Subgroup G) : Set G) :=
  inf_mem_normalizer h.z_mem_normalizer_U (mem_normalizer_centralizer_singleton
    (mem_centralizer_singleton_iff.mp (fr.E_le (s_mem_E hs))).symm)

include h hm hs hs3 in
theorem t_mem_normalizer_X :
    fr.t ∈ normalizer ((fr.U ⊓ centralizer ({s} : Set G) : Subgroup G) : Set G) :=
  inf_mem_normalizer h.t_mem_normalizer_U (mem_normalizer_centralizer_of_inv (t_mul_s h hm hs hs3))

include h p12 hm hs hs3 in
theorem card_X_inf_t_mul :
    Nat.card (fr.U ⊓ centralizer ({s} : Set G) ⊓ centralizer ({fr.t} : Set G) : Subgroup G) *
      Nat.card (fr.U ⊓ centralizer ({s} : Set G) ⊓ centralizer ({fr.t * z} : Set G) :
        Subgroup G) = 3 ^ 6 := by
  have hodd : Odd (Nat.card (fr.U ⊓ centralizer ({s} : Set G) : Subgroup G)) := by
    rw [card_U_inf_s h p12 hs hs3]; exact Odd.pow (by decide)
  have hbw := h.bw (t_mem_normalizer_X h hm hs hs3) (z_mem_normalizer_X h hs) hodd
  rw [X_inf_t_inf_z h p12 hs, X_inf_z h p12 hs, card_U_inf_s h p12 hs hs3, h.card_P₂,
    fr.card_E] at hbw
  linarith

include h p12 hm hs in
theorem W_inf_eq {v : G} (hv : v * m * v⁻¹ = m⁻¹)
    (hvX : v ∈ normalizer ((fr.U ⊓ centralizer ({s} : Set G) : Subgroup G) : Set G)) :
    Wof fr m s ⊓ centralizer ({v} : Set G) =
      fr.U ⊓ centralizer ({s} : Set G) ⊓ centralizer ({v} : Set G) := by
  refine le_antisymm (fun w hw => ?_) (inf_le_inf_right _ le_sup_left)
  obtain ⟨hwW, hwv⟩ := hw
  rw [Wof, sup_comm] at hwW
  obtain ⟨y, hy, x, hx, rfl⟩ :=
    exists_mul_of_mem_sup (zpowers_le.mpr (m_mem_normalizer p12 hm hs)) hwW
  have hvy : v * y * v⁻¹ = y⁻¹ := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← conj_zpow, hv, inv_zpow]
  have hvx : v * x * v⁻¹ ∈ fr.U ⊓ centralizer ({s} : Set G) := (mem_normalizer_iff.mp hvX x).mp hx
  have hfix : v * (y * x) * v⁻¹ = y * x := by
    rw [← mem_centralizer_singleton_iff.mp hwv, mul_inv_cancel_right]
  have hyy : y * y = v * x * v⁻¹ * x⁻¹ := by
    calc y * y = y * (v * (y * x) * v⁻¹) * x⁻¹ := by rw [hfix]; group
      _ = y * (v * y * v⁻¹) * (v * x * v⁻¹) * x⁻¹ := by group
      _ = v * x * v⁻¹ * x⁻¹ := by rw [hvy]; group
  have hmem : y * y ∈ zpowers m ⊓ (fr.U ⊓ centralizer ({s} : Set G)) :=
    mem_inf.mpr ⟨mul_mem hy hy, by rw [hyy]; exact mul_mem hvx (inv_mem hx)⟩
  rw [zpowers_inf_U_inf h hm, mem_bot] at hmem
  have hy3 : y ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hm.orderOf_m ▸ orderOf_dvd_of_mem_zpowers hy)
  obtain rfl : y = 1 := eq_one_of_sq_of_cube (by rw [sq]; exact hmem) hy3
  rw [one_mul] at hwv ⊢
  exact ⟨hx, hwv⟩

include h p12 hm hs hs3 in
theorem le_card_X_inf_t : 27 ≤ Nat.card (fr.U ⊓ centralizer ({s} : Set G) ⊓
    centralizer ({fr.t} : Set G) : Subgroup G) := by
  rw [inf_right_comm]
  refine le_card_of_comm_mem h.p11.card_P3bbar p12.card_U_inf_t fun u hu => ?_
  obtain ⟨hyS, hty⟩ := conj_comm_mem h p12 hs hu (t_mul_s h hm hs hs3)
  generalize u * s * u⁻¹ * s⁻¹ = y at hyS hty ⊢
  have hzy : z * y * z⁻¹ = y⁻¹ := h.z_inv_of_mem_S hyS
  have hconj : fr.t * z * y * (fr.t * z)⁻¹ = y := by
    calc fr.t * z * y * (fr.t * z)⁻¹ = fr.t * (z * y * z⁻¹) * fr.t⁻¹ := by group
      _ = (fr.t * y * fr.t⁻¹)⁻¹ := by rw [hzy]; group
      _ = y := by rw [hty, inv_inv]
  show y ∈ fr.ZN ⊓ centralizer ({fr.t * z} : Set G)
  exact ⟨h.S_le_ZN hyS, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hconj).symm⟩

include hs in
omit [Finite G] in
theorem z_conj_s : z * s * z⁻¹ = s := by
  rw [← mem_centralizer_singleton_iff.mp (fr.E_le (s_mem_E hs)), mul_inv_cancel_right]

include h hm hs hs3 in
theorem tz_conj_s : fr.t * z * s * (fr.t * z)⁻¹ = s⁻¹ := by
  calc fr.t * z * s * (fr.t * z)⁻¹ = fr.t * (z * s * z⁻¹) * fr.t⁻¹ := by group
    _ = s⁻¹ := by rw [z_conj_s hs, t_mul_s h hm hs hs3]

include h p12 hm hs hs3 in
theorem le_card_X_inf_tz : 27 ≤ Nat.card (fr.U ⊓ centralizer ({s} : Set G) ⊓
    centralizer ({fr.t * z} : Set G) : Subgroup G) := by
  rw [inf_right_comm]
  refine le_card_of_comm_mem h.p11.card_P3bar p12.card_U_inf_tz fun u hu => ?_
  obtain ⟨hyS, htzy⟩ := conj_comm_mem h p12 hs hu (tz_conj_s h hm hs hs3)
  generalize u * s * u⁻¹ * s⁻¹ = y at hyS htzy ⊢
  have hzy : z⁻¹ * y * z = y⁻¹ := by
    have := h.z_inv_of_mem_S hyS
    rw [h.z_inv] at this ⊢
    exact this
  have hconj : fr.t * y * fr.t⁻¹ = y := by
    calc fr.t * y * fr.t⁻¹ = fr.t * z * (z⁻¹ * y * z) * (fr.t * z)⁻¹ := by group
      _ = (fr.t * z * y * (fr.t * z)⁻¹)⁻¹ := by rw [hzy]; group
      _ = y := by rw [htzy, inv_inv]
  show y ∈ fr.ZN ⊓ centralizer ({fr.t} : Set G)
  exact ⟨h.S_le_ZN hyS, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hconj).symm⟩

include h p12 hm hs hs3 in
theorem card_X_inf_t : Nat.card (fr.U ⊓ centralizer ({s} : Set G) ⊓
    centralizer ({fr.t} : Set G) : Subgroup G) = 3 ^ 3 := by
  have h1 := card_X_inf_t_mul h p12 hm hs hs3
  have h4 := Nat.mul_le_mul_left (Nat.card (fr.U ⊓ centralizer ({s} : Set G) ⊓
    centralizer ({fr.t} : Set G) : Subgroup G)) (le_card_X_inf_tz h p12 hm hs hs3)
  rw [h1] at h4
  have h2 := le_card_X_inf_t h p12 hm hs hs3
  clear h1
  omega

include h p12 hm hs hs3 in
theorem card_X_inf_tz : Nat.card (fr.U ⊓ centralizer ({s} : Set G) ⊓
    centralizer ({fr.t * z} : Set G) : Subgroup G) = 3 ^ 3 := by
  have h1 := card_X_inf_t_mul h p12 hm hs hs3
  rw [card_X_inf_t h p12 hm hs hs3] at h1
  omega

include h p12 hm hs hs3 in
theorem card_W_inf_t :
    Nat.card (Wof fr m s ⊓ centralizer ({fr.t} : Set G) : Subgroup G) = 3 ^ 3 := by
  rw [W_inf_eq h p12 hm hs hm.t_mul_m (t_mem_normalizer_X h hm hs hs3)]
  exact card_X_inf_t h p12 hm hs hs3

include h p12 hm hs hs3 in
theorem card_W_inf_tz :
    Nat.card (Wof fr m s ⊓ centralizer ({fr.t * z} : Set G) : Subgroup G) = 3 ^ 3 := by
  have hzm : z * m * z⁻¹ = m := by
    rw [← mem_centralizer_singleton_iff.mp (fr.K_le hm.mem_K), mul_inv_cancel_right]
  have htzm : fr.t * z * m * (fr.t * z)⁻¹ = m⁻¹ := by
    calc fr.t * z * m * (fr.t * z)⁻¹ = fr.t * (z * m * z⁻¹) * fr.t⁻¹ := by group
      _ = m⁻¹ := by rw [hzm, hm.t_mul_m]
  rw [W_inf_eq h p12 hm hs htzm (mul_mem (t_mem_normalizer_X h hm hs hs3)
    (z_mem_normalizer_X h hs))]
  exact card_X_inf_tz h p12 hm hs hs3

include h p12 hm hs hs3 in
theorem card_W_inf_z :
    Nat.card (Wof fr m s ⊓ centralizer ({z} : Set G) : Subgroup G) = 3 ^ 4 := by
  have hle : fr.E ⊔ zpowers m ≤ Wof fr m s ⊓ centralizer ({z} : Set G) := by
    refine sup_le (le_inf ?_ fr.E_le)
      (zpowers_le.mpr ⟨mem_sup_right (mem_zpowers m), fr.K_le hm.mem_K⟩)
    rw [← X_inf_z h p12 hs]
    exact inf_le_left.trans le_sup_left
  have hlow := card_le_of_le hle
  rw [card_E_sup_m hm] at hlow
  have hY : Wof fr m s ⊓ centralizer ({z} : Set G) ≤
      normalizer ((fr.U ⊓ centralizer ({s} : Set G) : Subgroup G) : Set G) :=
    inf_le_left.trans (sup_le le_normalizer (zpowers_le.mpr (m_mem_normalizer p12 hm hs)))
  have h1 := card_sup_mul_card_inf hY
  have h2 : Nat.card (Wof fr m s ⊓ centralizer ({z} : Set G) ⊓
      (fr.U ⊓ centralizer ({s} : Set G)) : Subgroup G) ≤ 27 := by
    rw [← fr.card_E, ← X_inf_z h p12 hs]
    exact card_le_of_le (le_inf inf_le_right (inf_le_left.trans inf_le_right))
  have h3 : Nat.card (Wof fr m s ⊓ centralizer ({z} : Set G) ⊔
      (fr.U ⊓ centralizer ({s} : Set G)) : Subgroup G) ≤ 3 ^ 8 := by
    rw [← card_W h p12 hm hs hs3]
    exact card_le_of_le (sup_le inf_le_left le_sup_left)
  rw [card_U_inf_s h p12 hs hs3] at h1
  refine le_antisymm ?_ (by norm_num; exact hlow)
  nlinarith

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal
