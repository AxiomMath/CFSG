module

public import CFSG.GH74.GLS.C3.Layer1.U1aY
public import CFSG.GH74.GLS.C3.Layer1.U1aZStar
public import CFSG.GH74.GLS.C3.Layer1.U1aFP
public import CFSG.GH74.GLS.C3.Layer1.U1aPU1
public import CFSG.GH74.GLS.C3.Layer1.U1aRank

public section

namespace CFSG.GH74.GLS.C3.Layer1.U1a

open Subgroup CFSG.GH74.Uniqueness

variable {G : Type} [Group G] [Finite G] {M L N W Q T : Subgroup G}

private theorem conj_mul_mem_of_mem_conjugate {g y : G} (hy : y ∈ CFSG.conjugate Q g) :
    g * y * g⁻¹ ∈ Q := by
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
  simpa [MulAut.conj_apply, mul_assoc] using hq

theorem exists_conj_rank_two_of_not_A2 (h : ¬ A2 M Q) :
    ∃ g : G, g ∉ M ∧ 2 ≤ CFSG.pRank 2 ↥(CFSG.conjugate Q g ⊓ M) := by
  rw [A2] at h
  push Not at h
  obtain ⟨a, haQ, b, hbQ, ha2, hb2, hab, hcomm, g, hag, hbg, hgM⟩ := h
  refine ⟨g, hgM, ?_⟩
  have hxa : g⁻¹ * a * g ∈ CFSG.conjugate Q g :=
    Subgroup.mem_map.2 ⟨a, haQ, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hxb : g⁻¹ * b * g ∈ CFSG.conjugate Q g :=
    Subgroup.mem_map.2 ⟨b, hbQ, by simp [MulAut.conj_apply, mul_assoc]⟩
  refine two_le_pRank_of_commute (D := CFSG.conjugate Q g ⊓ M)
    (x := g⁻¹ * a * g) (y := g⁻¹ * b * g) ⟨hxa, hag⟩ ⟨hxb, hbg⟩
    ((orderOf_conj_eq g).trans ha2) ((orderOf_conj_eq g).trans hb2) ?_ ?_
  · calc (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [hcomm]
      _ = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by group
  · intro hxy
    exact hab (by simpa using hxy)

theorem not_A2_of_exists_conj_rank_two
    (h : ∃ g : G, g ∉ M ∧ 2 ≤ CFSG.pRank 2 ↥(CFSG.conjugate Q g ⊓ M)) : ¬ A2 M Q := by
  rintro hA2
  obtain ⟨g, hgM, hrank⟩ := h
  obtain ⟨x, hxD, y, hyD, hx2, hy2, hxy_ne, hxy_comm⟩ :=
    exists_commuting_involutions (D := CFSG.conjugate Q g ⊓ M) hrank
  have hxQ : g * x * g⁻¹ ∈ Q := conj_mul_mem_of_mem_conjugate hxD.1
  have hyQ : g * y * g⁻¹ ∈ Q := conj_mul_mem_of_mem_conjugate hyD.1
  have hx2' : orderOf (g * x * g⁻¹) = 2 := by rw [orderOf_conj_eq', hx2]
  have hy2' : orderOf (g * y * g⁻¹) = 2 := by rw [orderOf_conj_eq', hy2]
  have hxy_ne' : g * x * g⁻¹ ≠ g * y * g⁻¹ := by
    intro hxy
    apply hxy_ne
    have := congrArg (fun z => g⁻¹ * z * g) hxy
    simpa [mul_assoc] using this
  have hxy_comm' : (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) := by
    calc (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hxy_comm]
      _ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
  have hgM' : g ∈ M :=
    hA2 (g * x * g⁻¹) hxQ (g * y * g⁻¹) hyQ hx2' hy2' hxy_ne' hxy_comm' g
      (by simpa [mul_assoc] using hxD.2)
      (by simpa [mul_assoc] using hyD.2)
  exact hgM hgM'

theorem not_A2_iff_exists_conj_rank_two :
    ¬ A2 M Q ↔ ∃ g : G, g ∉ M ∧ 2 ≤ CFSG.pRank 2 ↥(CFSG.conjugate Q g ⊓ M) :=
  ⟨exists_conj_rank_two_of_not_A2, not_A2_of_exists_conj_rank_two⟩

namespace Setup

variable (S : Setup M L N W Q T)
include S

theorem false_of_A2 (hA2 : A2 M Q) (hY : ∃ y, Yset M Q y) : False := by
  obtain ⟨y, hy⟩ := hY
  obtain ⟨z, hzQ, hz2, hzT⟩ := S.exists_central_involution
  have hyM : y ∈ M := hy.2.1
  have hy2 : orderOf y = 2 := hy.1
  have hyW : y ∉ W := by
    intro hyW
    obtain ⟨c, hcW, hc⟩ := S.exists_conj_Q hyW hy2
    exact S.Y_not_mem_Q hA2 hzQ hz2 hzT (hy.conj (S.W_le hcW)) hc
  obtain ⟨l, hl, hne, hcomm⟩ := exists_commuting_conj S hy2 hyM hyW
  have hy' : Yset M Q (l * y * l⁻¹) := hy.conj' (S.L_le hl)
  have hV : Vset Q (y * (l * y * l⁻¹)) :=
    S.vset_mul hA2 hy.vset hy'.vset (Ne.symm hne) hcomm.symm
  have hyinv : y⁻¹ = y := inv_eq_self_of_orderOf_eq_two hy2
  have hv₀L : y * (l * y * l⁻¹) ∈ L := by
    have h := S.L_norm y hyM l hl
    have e : y * (l * y * l⁻¹) = (y * l * y⁻¹) * l⁻¹ := by rw [hyinv]; group
    rw [e]
    exact L.mul_mem h (L.inv_mem hl)
  have hv₀M : y * (l * y * l⁻¹) ∈ M := M.mul_mem hyM hy'.2.1
  rcases S.mem_W_or_Yset hV hv₀M with hW | hY0
  · exact S.LW _ hv₀L hW hV.1
  · obtain ⟨a₀, ha₀Q, b₀, hb₀Q, ha₀2, hb₀2, hab₀, hcomm₀⟩ := S.rankQ
    have ha₀1 := mul_self_eq_one_of_orderOf_eq_two ha₀2
    have hb₀1 := mul_self_eq_one_of_orderOf_eq_two hb₀2
    have hAW : closure ({a₀, b₀} : Set G) ≤ W := by
      rw [closure_le]
      rintro x (rfl | rfl)
      · exact S.Q_le_W ha₀Q
      · exact S.Q_le_W hb₀Q
    obtain ⟨n, hnN, hn⟩ := exists_conj_centralized_by_two_group (A := closure ({a₀, b₀} : Set G))
      (v := y * (l * y * l⁻¹)) hV.1 (isPGroup_closure_pair ha₀1 hb₀1 hcomm₀) S.N_odd
      (S.N_norm _ hv₀M)
      (fun a ha n hn => S.N_norm a (S.W_le (hAW ha)) n hn)
      (fun a ha => S.W_comm a (hAW ha) _ hv₀L)
    have hv₁Y : Yset M Q (n * (y * (l * y * l⁻¹)) * n⁻¹) :=
      hY0.conj' (S.L_le (S.N_le hnN))
    have hcentral : ∀ a ∈ ({a₀, b₀} : Set G),
        a * (n * (y * (l * y * l⁻¹)) * n⁻¹) = (n * (y * (l * y * l⁻¹)) * n⁻¹) * a := by
      intro a ha
      have h1 := hn a (subset_closure ha)
      calc a * (n * (y * (l * y * l⁻¹)) * n⁻¹)
          = (a * (n * (y * (l * y * l⁻¹)) * n⁻¹) * a⁻¹) * a := by group
        _ = (n * (y * (l * y * l⁻¹)) * n⁻¹) * a := by rw [h1]
    exact S.Y_no_four hA2 hv₁Y (S.Q_le_W ha₀Q) (S.Q_le_W hb₀Q) ha₀2 hb₀2 hab₀ hcomm₀
      (hcentral a₀ (by simp)) (hcentral b₀ (by simp))

omit S [Finite G] in
private theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem exists_conj_inter (hCor : S_CorZD) (hG : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a) :
    ∃ g : G, g ∉ M ∧ 2 ≤ CFSG.pRank 2 ↥(CFSG.conjugate Q g ⊓ M) := by
  by_contra hcon
  push Not at hcon
  have hA2 : A2 M Q := by
    by_contra hnot
    obtain ⟨g, hgM, hrank⟩ := exists_conj_rank_two_of_not_A2 hnot
    exact (not_le.mpr (hcon g hgM)) hrank
  by_cases hU : ∀ x ∈ Q, orderOf x = 2 → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M
  · exact pu1_false hCor hG hnon S hU
  · push Not at hU
    obtain ⟨x, hxQ, hx2, g, hg, hgM⟩ := hU
    exact S.false_of_A2 hA2 ⟨g⁻¹ * x * g, (orderOf_conj_eq g).trans hx2, hg, x, hxQ, hx2, g, hgM,
      rfl⟩

end Setup

end CFSG.GH74.GLS.C3.Layer1.U1a
