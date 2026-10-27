module

public import CFSG.GH74.GLS.Stage4.T2FourK
public import CFSG.GH74.GLS.Stage4.T2Sing
public import CFSG.GH74.GLS.Stage4.T2F1
public import CFSG.GH74.GLS.Stage4.Q9.Leaf

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.Assembly.LowTwoRank

section Q9

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G} {K₁ K₂ : Subgroup G}
  {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2q9_setting_core
    (hr : pRank 2 G = 3) (hSet : Ch6Setup G Gs 9 9 z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (hBad : Ch6Bad3 G) (hTD : T2TnsData z t K₁ K₂) :
    Nonempty (Stage4.Q9.Q9Setting G z K₁ K₂ F₁ F₂) := by
  have hC₁ := t2_C_eq_C₁_nine hSet hRem
  have := hSet.finite₁
  have := hSet.finite₂
  have hzord : orderOf z = 2 := hSet.central.1
  have hzz : z * z = 1 := t2C_zz hSet
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; decide
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; norm_num
  obtain ⟨⟨e₁, hze₁⟩, -⟩ := t2C_coords hSet
  obtain ⟨e₁', g₁, hns₁, hact₁⟩ := hRem.diag₁
  obtain ⟨e₂', g₂, hns₂, hact₂⟩ := hRem.diag₂
  have hK₁inv := t2P53_invK hodd₁ e₁ hSet.z_mem₁ hze₁
  have hnc := t2B_hnc hSet hRem hC₁
  have hone := hSet.one_class
  obtain ⟨H, w₁, w₂, hT, ε₁, ε₂, hε₁, hε₂, hq₁, hq₂, hcyc₁, hcyc₂, hcard₁, hcard₂, hform⟩ :=
    t2Four_of_rem hSet hRem hC₁ (by norm_num : 5 ≤ 9)
  have hε₁1 : ε₁ = 1 := by
    rcases hε₁ with h | h
    · exact h
    · subst h; exact absurd hq₁ (by decide)
  have hε₂1 : ε₂ = 1 := by
    rcases hε₂ with h | h
    · exact h
    · subst h; exact absurd hq₂ (by decide)
  have hc₁ : Nat.card ↥(H ⊓ K₁) = 2 * 5 := by
    have := hcard₁; rw [hε₁1] at this; omega
  have hc₂ : Nat.card ↥(H ⊓ K₂) = 2 * 5 := by
    have := hcard₂; rw [hε₂1] at this; omega
  obtain ⟨Q₁, Q₂, hQ₁H, hQ₂H, hQ₁c, hQ₂c, hQ₁e, hQ₂e, hQ₁₂, hdec⟩ :=
    hT.odd_part hSet.z_mem₁ hSet.z_mem₂ 5 (by decide) hcyc₁ hcyc₂ hc₁ hc₂ hform
  have hcommQ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy =>
    hT.K_comm x (hQ₁H hx).2 y (hQ₂H hy).2
  have hQe := t2Q_exp hcommQ hQ₁e hQ₂e
  have hQcard : Nat.card ↥(Q₁ ⊔ Q₂) = 5 * 5 := by
    rw [t2H_card_sup_comm_disjoint Q₁ Q₂ hcommQ hQ₁₂, hQ₁c, hQ₂c]
  have hUQ : t2U z t ⊓ (Q₁ ⊔ Q₂) = ⊥ := t2U_inf_Q_eq_bot hT.zz hT.uu hT.zu_comm (by decide) hQe
  have hUcard : Nat.card ↥(t2U z t) = 4 :=
    t2U_card hT.zz hT.uu hT.zu_comm hT.z_ne hT.u_ne hT.zu_ne
  have hUH : t2U z t ≤ H :=
    t2U_le_of_mem hT.zz hT.uu hT.zu_comm hT.z_mem_H hT.u_mem_H
  have hQH : Q₁ ⊔ Q₂ ≤ H := sup_le (fun x hx => (hQ₁H hx).1) (fun x hx => (hQ₂H hx).1)
  have hHeq : H = t2U z t ⊔ (Q₁ ⊔ Q₂) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    · exact sup_le hUH hQH
  have hHcard : Nat.card ↥H = 100 := by
    have hc : ∀ x ∈ t2U z t, ∀ y ∈ Q₁ ⊔ Q₂, x * y = y * x := fun x hx y hy =>
      hT.H_comm x (hUH hx) y (hQH hy)
    rw [hHeq, t2H_card_sup_comm_disjoint _ _ hc hUQ, hUcard, hQcard]
  have hH3 : ¬ 3 ∣ Nat.card ↥H := by rw [hHcard]; decide
  have hiso := hT.zmodProd_ten (fun x hx => (hQ₁H hx).1) (fun x hx => (hQ₂H hx).1) hQ₁c hQ₂c hQ₁₂
    hHcard
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hRem.sq) hT.u_ne
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone t htord)
  have hconj : ∃ g : G, g⁻¹ * z * g = t := ⟨c⁻¹, by simpa using hc⟩
  obtain ⟨as, has3, hasN, hd1, hd2, -⟩ :=
    hT.exists_exact hr hodd₁ h3₁ e₁ hK₁inv hnc hconj hH3
  have has1 : as ≠ 1 := by
    intro h1; apply hT.zu_ne
    rw [h1] at hd1; simpa using hd1
  obtain ⟨u, H', w₁', w₂', hT', huK, h16⟩ := t2Four_K_nine hSet hRem hC₁
  have huord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hT'.uu) hT'.u_ne
  obtain ⟨c', hc'⟩ := isConj_iff.1 (hone u huord)
  have hconj' : ∃ g : G, g⁻¹ * z * g = u := ⟨c'⁻¹, by simpa using hc'⟩
  obtain ⟨w₁'', w₂'', a, hW⟩ := hT'.exists_weyl hr hodd₁ h3₁ e₁ hK₁inv hnc hconj'
    (t2_not_three_dvd_of_exp16 h16) (fun a _ _ d1 d2 => hT'.hCH_of_exp16 hr h16 d1 d2)
  have hzuU : z * u ∈ t2U z u := Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))
  have hzU : z ∈ t2U z u := Subgroup.subset_closure (by simp)
  have hidx : (K₁ ⊔ K₂).relIndex (centralizer ({z} : Set G)) = 2 := hT.C_idx
  refine ⟨
    { z_ord := hzord, one_class := hone, card₁ := hSet.card₁, card₂ := hSet.card₂,
      φ₁ := e₁', φ₂ := e₂',
      le_centralizer₁ := fun x hx => hSet.le_centralizer (Subgroup.mem_sup_left hx),
      le_centralizer₂ := fun x hx => hSet.le_centralizer (Subgroup.mem_sup_right hx),
      normal₁ := hT.C_norm₁, normal₂ := hT.C_norm₂, comm := hSet.comm,
      inter_eq := hSet.inter_eq, index_two := hidx,
      card3 := t2_card3 hSet hBad, card2 := t2_card2 hSet,
      t := t, t_ord := htord, t_mem := Subgroup.mem_centralizer_singleton_iff.2 hRem.comm_z,
      t_notin := t2B_t_notin hSet hRem,
      A := g₁, B := g₂,
      A_act := fun k k' hk => by
        obtain ⟨y, hy1, hy2⟩ := hact₁ k
        have : k' = y := Subtype.ext (by rw [hk, hy1])
        subst this; exact hy2,
      B_act := fun k k' hk => by
        obtain ⟨y, hy1, hy2⟩ := hact₂ k
        have : k' = y := Subtype.ext (by rw [hk, hy1])
        subst this; exact hy2,
      A_det := hns₁, B_det := hns₂,
      Hs := H, Hs_iso := hiso,
      Hs_le := fun x hx => Subgroup.mem_centralizer_iff.2 (fun s hs =>
        (hT.H_comm s (hUH hs) x hx)),
      Hs_ge₁ := fun x hx => (hT.H₁_iff x hx.1).2
        (hx.2 |> fun hx' => (Subgroup.mem_centralizer_iff.1 hx' t
          (Subgroup.subset_closure (by simp))).symm),
      Hs_ge₂ := fun x hx => (hT.H₂_iff x hx.1).2
        (hx.2 |> fun hx' => (Subgroup.mem_centralizer_iff.1 hx' t
          (Subgroup.subset_closure (by simp))).symm),
      normalizer_eq := ?_,
      tns := hTD H w₁ w₂ hT Q₁ Q₂ 5 (by decide) hQ₁H hQ₂H hQ₁e hQ₂e hdec hH3,
      as := as, as_ord := orderOf_eq_prime has3 has1, as_mem := hasN,
      as_moves := ?_,
      u := u, u_mem := huK, u_ord := huord, u_ne := hT'.zu_ne.symm,
      w₁ := w₁'', w₂ := w₂'', w₁_mem := hW.four.w₁_mem, w₂_mem := hW.four.w₂_mem,
      w₁_sq := hW.four.w₁_sq, w₂_sq := hW.four.w₂_sq, w₁_act := hW.four.w₁_u,
      w₂_act := hW.four.w₂_u,
      a := a, a_norm_z := by rw [hW.a_conj_z]; exact hzuU,
      a_norm_u := by rw [hW.a_conj_u]; exact hzU,
      a_moves := by
        rw [hW.a_conj_z]
        intro h1
        apply hT'.u_ne
        have : z * u = z * 1 := by rw [h1, mul_one]
        exact mul_left_cancel this,
      a_cent := by
        calc a * (w₁'' * w₂'') * a⁻¹ = (w₁'' * w₂'') * a * a⁻¹ := by rw [hW.a_cent]
          _ = w₁'' * w₂'' := by group }⟩
  ·
    ext g
    constructor
    · intro hg
      exact Subgroup.mem_normalizer_fintype (fun x hx => hT.normH hr hg x hx)
    · intro hg
      apply t2U_norm (z := z) (u := t)
      · have h1 := (Subgroup.mem_normalizer_iff.1 hg z).1 hT.z_mem_H
        have h2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
          calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
            _ = 1 := by rw [hzz]; group
        exact (t2U_mem hT.zz hT.uu hT.zu_comm).2 (hT.omega1 hr _ h1 h2)
      · have h1 := (Subgroup.mem_normalizer_iff.1 hg t).1 hT.u_mem_H
        have h2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
          calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
            _ = 1 := by rw [hRem.sq]; group
        exact (t2U_mem hT.zz hT.uu hT.zu_comm).2 (hT.omega1 hr _ h1 h2)
  · intro h1
    apply hT.zu_ne
    have : z = as⁻¹ * z * as := by
      calc z = as⁻¹ * (as * z * as⁻¹) * as := by group
        _ = as⁻¹ * z * as := by rw [h1]
    rw [this, hd1]

theorem q9SettingOf_of_order
    (hRemL : Ch6T2Rem) (hOrd : Ch6P56bOrder) :
    Stage4.Q9.Q9SettingOf := by
  intro G _ _ hStd hr Gs _ hAt hBad
  obtain ⟨z, K₁, K₂, F₁, F₂, iF₁, iF₂, hSet⟩ := ch6_setup hr hAt
  obtain ⟨t, hRem⟩ := hRemL G hStd hr Gs 9 9 z K₁ K₂ F₁ F₂ hSet
  refine ⟨z, K₁, K₂, F₁, F₂, iF₁, iF₂, ?_⟩
  exact t2q9_setting_core hr hSet hRem hBad
    (T2TnsData.of_order (n := 2) hOrd hStd hr le_rfl hAt hBad hSet hRem)

end Q9

end CFSG.GH74.GLS.Stage4.Rest
