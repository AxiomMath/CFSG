module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5Data
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5W
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5Skeleton

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem normal_vec : ∀ p q r s : Fin 2,
    addV (addV (p, q, r, s) (0, 0, 0, s)) (r, 0, r, 0) = (p + r, q, 0, 0) := by decide

theorem orbit_vec : ∀ v : V4, (v.2.2.1 = 1 ∧ v.2.2.2 = 0) ↔
    (v = (0, 0, 1, 0) ∨ v = (1, 0, 1, 0) ∨ v = (0, 1, 1, 0) ∨ v = (1, 1, 1, 0)) := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Inst.QD

variable {I : S.Inst} (D : I.QD)

theorem exists_normal {w₀ : X} (hw₀ : w₀ ∈ D.Q) (hM : I.Mat w₀ (transCols 1 0)) :
    ∃ α β p q : Fin 2, D.eL (w₀ * I.ki ^ (β : ℕ) * S.t ^ (α : ℕ)) = I.wV (p, q, 0, 0) := by
  obtain ⟨⟨p, q, r, s⟩, hv⟩ := I.eq_wV (D.eL_mem hw₀ hM)
  have hk : I.ki ∈ D.Q := D.E_le I.ki_mem_E
  have ht : S.t ∈ D.Q := D.E_le I.t_mem_E
  have hkC := I.E_le_centralizer I.ki_mem_E
  have htC := I.E_le_centralizer I.t_mem_E
  have hβ : ∀ β : Fin 2, w₀ * I.ki ^ (β : ℕ) ∈ D.Q ∧
      I.Mat (w₀ * I.ki ^ (β : ℕ)) (transCols 1 0) ∧
      D.eL (w₀ * I.ki ^ (β : ℕ)) = I.wV (addV (p, q, r, s) (0, 0, 0, β)) := by
    intro β
    rcases Fin.exists_fin_two.mp ⟨β, rfl⟩ with rfl | rfl
    · simp only [Fin.val_zero, pow_zero, mul_one]
      exact ⟨hw₀, hM, by rw [hv]; simp [addV]⟩
    · simp only [Fin.val_one, pow_one]
      refine ⟨mul_mem hw₀ hk, hM.mul_central hkC, ?_⟩
      rw [D.eL_mul_ki hw₀, hv, show I.ki = I.wV (0, 0, 0, 1) by simp [Inst.wV], ← I.wV_add]
  refine ⟨r, s, p + r, q, ?_⟩
  obtain ⟨h1, h2, h3⟩ := hβ s
  rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with rfl | rfl
  · simp only [Fin.val_zero, pow_zero, mul_one]
    rw [h3, ← normal_vec p q 0 s]
    simp [addV]
  · simp only [Fin.val_one, pow_one]
    rw [D.eL_mul_t h1 h2, h3,
      show S.t * S.z = I.wV (1, 0, 1, 0) by simp [Inst.wV, S.z_comm_of_mem_T S.data.t_mem_T],
      ← I.wV_add, normal_vec]

end Inst.QD

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

omit H in
theorem y_mat : S.inst₁.Mat S.y xCols := by
  have huT := S.y_mem.1
  have hc : ∀ {g : X}, g ∈ S.B → S.y * g * S.y⁻¹ = g := fun hg => by
    rw [← S.central_of_mem_B hg huT]; group
  refine Inst.Mat.mk (I := S.inst₁) (S.T_le_normalizer_E S.xy_mem huT) ?_ ?_ ?_ ?_
  · rw [hc (subset_closure (by simp))]; simp [xCols, sigCols, Inst.wV]
  · have := S.inst₁.ui_conj_yi
    rw [show S.inst₁.ui = S.y from rfl] at this
    rw [this]; simp [xCols, sigCols, Inst.wV]
  · rw [hc (subset_closure (by simp))]; simp [xCols, sigCols, Inst.wV]
  · rw [hc S.inst₁.ki_mem_B]; simp [xCols, sigCols, Inst.wV]

theorem exists_sec5 (F : S.Frame) (hF : F.Normal) : Nonempty (S.Sec5 F T₁) := by
  obtain ⟨hx, hy, hk⟩ := hF
  have hE₁ : F.E₁ = S.inst₁.E := by rw [Frame.E₁, hy]; rfl
  have hE₂ : F.E₂ = S.E S.y := by rw [Frame.E₂, hx, hy, inv_mul_cancel_left]
  have hu : F.xF * F.yF = S.y := by rw [hx, hy, inv_mul_cancel_left]
  set I := S.inst₁ with hI
  have hIy : I.yi = S.x * S.y := rfl
  have hIk : I.ki = S.k := rfl
  obtain ⟨g, hg, hgT, hgE, hgt, hgk⟩ := H.exists_g
  obtain ⟨hgsq, hT₁eq⟩ := H.sq_mem_and_eq hg hgT
  obtain ⟨R, hRp, hRN, hRmax, hT₂R, hRc, hRC⟩ := H.exists_R
  have hTR : S.data.T ≤ R := H.T_le_T₂of.trans hT₂R
  have hu2 : S.y * S.y = 1 := by rw [← pow_two]; exact S.y_sq
  obtain ⟨d, hdM, hdQ, hd3, hud⟩ := H.exists_d₅ I hRN hRc hRC (hTR S.y_mem.1) y_mat hu2
  set D := H.qd I hRp hRN hRc hRC hdM hdQ hd3 with hD
  have hDQ : D.Q = R ⊓ oddTwoCoreIn (normalizer (I.E : Set X)) := rfl
  have hDd : D.d = d := rfl
  obtain ⟨hQcard, -, -⟩ := H.Q_props I hRN hRc hRC
  obtain ⟨w₀, hw₀T₂, hw₀T, hw₀2, hw₀x, hw₀y, hw₀k, hw₀t⟩ := H.exists_w
  have hcz : ∀ {c : X}, c * S.x = S.x * c → c * S.z * c⁻¹ = S.z := by
    intro c h
    have hcx : c * S.x * c⁻¹ = S.x := by rw [h]; group
    rw [show S.z = S.x ^ 2 from rfl, pow_two]
    calc c * (S.x * S.x) * c⁻¹ = (c * S.x * c⁻¹) * (c * S.x * c⁻¹) := by group
      _ = S.x * S.x := by rw [hcx]
  have hcomm_conj : ∀ {c e : X}, c * e = e * c → c * e * c⁻¹ = e := by
    intro c e h
    rw [h]; group
  have hw₀xy : w₀ * (S.x * S.y) = (S.x * S.y) * w₀ := by
    rw [← mul_assoc, hw₀x, mul_assoc, hw₀y, mul_assoc]
  have hw₀M : I.Mat w₀ (transCols 1 0) := by
    refine Inst.Mat.mk (I := I) (H.T₂of_le_normalizer I hw₀T₂) ?_ ?_ ?_ ?_
    · rw [hcz hw₀x]; simp [transCols, Inst.wV]
    · rw [hIy, hcomm_conj hw₀xy]
      simp [transCols, Inst.wV, hIy]
    · rw [hw₀t]; simp [transCols, Inst.wV, S.z_comm_of_mem_T S.data.t_mem_T]
    · rw [hIk, hcomm_conj hw₀k]; simp [transCols, Inst.wV, hIk]
  have hw₀Q : w₀ ∈ D.Q := by
    rw [hDQ]
    refine mem_inf.mpr ⟨hT₂R hw₀T₂, ?_⟩
    rw [H.oddTwoCoreIn_eq I]
    exact ⟨⟨w₀, hw₀M.1⟩, H.mem_Pre5_of_mat I hw₀M, rfl⟩
  obtain ⟨α, β, p, q, he⟩ := D.exists_normal hw₀Q hw₀M
  have hkT₂ : S.k ∈ S.T₂of T₁ := H.T_le_T₂of S.k_mem
  have htT₂ : S.t ∈ S.T₂of T₁ := H.T_le_T₂of S.data.t_mem_T
  have hkx : S.k * S.x = S.x * S.k := S.central_of_mem_B (subset_closure (by simp)) S.x_mem.1
  have hky : S.k * S.y = S.y * S.k := S.central_of_mem_B (subset_closure (by simp)) S.y_mem.1
  have hkt : S.k * S.t = S.t * S.k := S.central_of_mem_B (subset_closure (by simp))
    S.data.t_mem_T
  have htx : S.t * S.x = S.x * S.t := (S.data.commute_t S.x_mem.1).symm
  have hty : S.t * S.y = S.y * S.t := (S.data.commute_t S.y_mem.1).symm
  set w := w₀ * S.k ^ (β : ℕ) with hw
  have hwT₂ : w ∈ S.T₂of T₁ := mul_mem hw₀T₂ (pow_mem hkT₂ _)
  have hwT : w ∉ S.data.T := fun h => hw₀T (by
    have := mul_mem h (inv_mem (pow_mem S.k_mem (β : ℕ)))
    rwa [hw, mul_inv_cancel_right] at this)
  have hwx : w * S.x = S.x * w := by
    rw [hw, mul_assoc, (Commute.pow_left hkx _).eq, ← mul_assoc, hw₀x, mul_assoc]
  have hwy : w * S.y = S.y * w := by
    rw [hw, mul_assoc, (Commute.pow_left hky _).eq, ← mul_assoc, hw₀y, mul_assoc]
  have hwk : w * S.k = S.k * w := by
    rw [hw, mul_assoc, ← pow_succ, pow_succ', ← mul_assoc, hw₀k, mul_assoc]
  have hwt : w * S.t * w⁻¹ = S.t * S.z := by
    calc w * S.t * w⁻¹ = w₀ * (S.k ^ (β : ℕ) * S.t * (S.k ^ (β : ℕ))⁻¹) * w₀⁻¹ := by
          rw [hw]; group
      _ = S.t * S.z := by rw [(Commute.pow_left hkt _).eq, mul_inv_cancel_right, hw₀t]
  have hw2 : w ^ 2 = 1 := by
    rw [hw, (Commute.pow_right hw₀k _).mul_pow, hw₀2, one_mul, ← pow_mul, mul_comm, pow_mul,
      S.k_sq, one_pow]
  set w₁ := w * S.t ^ (α : ℕ) with hw₁
  have hw₁e : D.eL w₁ = I.wV (p, q, 0, 0) := he
  have hkQ : S.k ∈ D.Q := D.E_le I.ki_mem_E
  have htQ : S.t ∈ D.Q := D.E_le I.t_mem_E
  have hw₁Q : w₁ ∈ D.Q := mul_mem (mul_mem hw₀Q (pow_mem hkQ _)) (pow_mem htQ _)
  have hw₁M : I.Mat w₁ (transCols 1 0) :=
    (hw₀M.mul_central (pow_mem (I.E_le_centralizer I.ki_mem_E) _)).mul_central
      (pow_mem (I.E_le_centralizer I.t_mem_E) _)
  have hsq : w₁ ^ 2 = I.wV (α, 0, 0, 0) := by
    rcases Fin.exists_fin_two.mp ⟨α, rfl⟩ with rfl | rfl
    · simp only [hw₁, Fin.val_zero, pow_zero, mul_one, hw2]
      simp [Inst.wV]
    · simp only [hw₁, Fin.val_one, pow_one]
      calc (w * S.t) ^ 2 = (w * S.t * w⁻¹) * w ^ 2 * S.t := by rw [pow_two, pow_two]; group
        _ = S.t * S.z * S.t := by rw [hwt, hw2, mul_one]
        _ = I.wV (1, 0, 0, 0) := by
            rw [mul_assoc, S.z_comm_of_mem_T S.data.t_mem_T, ← mul_assoc, ← pow_two, S.t_sq,
              one_mul]
            simp [Inst.wV]
  have hc12 := D.commute_w₁_w₂ hw₁Q hw₁M hw₁e hsq
  have hdw₂ := D.d_w2 hw₁Q hw₁M hw₁e hsq
  have hw₂Q := D.w2_mem hw₁Q
  have hw₂M := D.w2_mat hw₁M
  have hw₂R : D.w2 w₁ ∈ R := (mem_inf.mp hw₂Q).1
  have hsq₂ : (D.w2 w₁) ^ 2 = I.wV (0, α, 0, 0) := by
    rw [Inst.QD.w2, conj_pow, hsq, D.d_mat.conj, dCols_a]
  have hyw₁ : S.y * w₁ * S.y⁻¹ = w₁ := by
    have c1 : Commute S.y w₀ := hw₀y.symm
    have c2 : Commute S.y S.k := hky.symm
    have c3 : Commute S.y S.t := hty.symm
    have hc : Commute S.y (w₀ * S.k ^ (β : ℕ) * S.t ^ (α : ℕ)) :=
      (c1.mul_right (c2.pow_right _)).mul_right (c3.pow_right _)
    rw [hw₁, hw, hc.eq]; group
  have hd3w : D.d ^ 3 * w₁ = w₁ * D.d ^ 3 := D.d_cube w₁ hw₁Q
  refine ⟨{
    T₂ := S.T₂of T₁
    R := R
    Q := D.Q
    w := w
    g := g
    d := d
    w₁ := w₁
    w₂ := D.w2 w₁
    case := if α = 0 then .E else .H
    orbit := ?_
    automizer := ?_
    zy_normal := ?_
    k_fixed := ?_
    normalizer_eq := ?_
    g_mem := hg
    g_E := ?_
    g_t := ?_
    g_k := ?_
    g_sq_mem := hgsq
    g_sq_not_mem := H.sq_not_mem_T hg hgt hgk
    T₁_eq := hT₁eq
    center_T₁ := H.center_T₁ hg hgt hgk
    not_sylow := H.not_sylow
    T₂_eq := ?_
    T₂_eq_sup := H.T₂of_eq_sup hwT₂ hwT hw2
    card_T₂ := H.card_T₂of
    w_sq := hw2
    w_t := hwt
    w_x := ?_
    w_y := ?_
    w_k := ?_
    isPGroup_R := hRp
    R_le := ?_
    R_maximal := ?_
    T₂_le := hT₂R
    R_eq := H.R_eq_sup hRc hT₂R hw₂R hw₂M
    card_R := hRc
    R_inf_centralizer := ?_
    le_E := ?_
    Q_eq := ?_
    Q_eq_sup := ?_
    w₁_eq := ?_
    w₂_t := ?_
    w₂_z := ?_
    w₂_y := ?_
    w₂_k := ?_
    w₂_w₁ := hc12.symm
    sq_cases := ?_
    u_w₂ := ?_
    d_mem := ?_
    isPGroup_d := ?_
    d_z := ?_
    d_y := ?_
    d_k := ?_
    d_w₁ := rfl
    d_w₂ := hdw₂
    u_d := ?_ }⟩
  ·
    rw [hE₁, hy]
    intro e he'
    obtain ⟨v, rfl⟩ := I.eq_wV he'
    have h1 : (∃ n ∈ normalizer (I.E : Set X), n * S.t * n⁻¹ = I.wV v) ↔ I.wV v ∈ I.orbitN :=
      Iff.rfl
    have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
    have hyt : (S.x * S.y) * S.t = S.t * (S.x * S.y) := S.data.commute_t S.xy_mem.1
    have e1 : S.t = I.wV (0, 0, 1, 0) := by simp [Inst.wV]
    have e2 : S.t * S.z = I.wV (1, 0, 1, 0) := by simp [Inst.wV, hzt]
    have e3 : S.t * (S.x * S.y) = I.wV (0, 1, 1, 0) := by simp [Inst.wV, hIy, hyt]
    have e4 : S.t * S.z * (S.x * S.y) = I.wV (1, 1, 1, 0) := by
      rw [show I.wV (1, 1, 1, 0) = S.z * (S.x * S.y) * S.t by simp [Inst.wV, hIy]]
      calc S.t * S.z * (S.x * S.y) = S.z * S.t * (S.x * S.y) := by rw [hzt]
        _ = S.z * (S.t * (S.x * S.y)) := by group
        _ = S.z * ((S.x * S.y) * S.t) := by rw [hyt]
        _ = S.z * (S.x * S.y) * S.t := by group
    rw [h1, H.mem_orbitN_iff I v, orbit_vec, e4, e3, e2, e1, I.wV_injective'.eq_iff,
      I.wV_injective'.eq_iff, I.wV_injective'.eq_iff, I.wV_injective'.eq_iff]
  · rw [hE₁]; exact H.automizer I
  · rw [hE₁, hy]; exact fun n hn => H.zy_normal I hn
  · rw [hE₁, hk]; exact fun n hn => H.k_fixed I hn
  · rw [hE₁]; exact H.normalizer_eq_sup I hRN hRc hRC (hTR S.x_mem.1) hdM
  · rw [hE₁, hE₂]; exact hgE
  · rw [hk]; exact hgt
  · rw [hk]; exact hgk
  · rw [hE₁]; rfl
  · rw [hx]; exact (Commute.inv_right hwx).eq
  · rw [hy, ← mul_assoc, hwx, mul_assoc, hwy, mul_assoc]
  · rw [hk]; exact hwk
  · rw [hE₁]; exact hRN
  · rw [hE₁]; exact hRmax
  · rw [hE₁]; exact hRC
  · rw [hE₁]; exact fun P hP hPC => le_E I hP hPC
  · rw [hE₁]; rfl
  · rw [hE₁]
    exact Q_eq_sup I hQcard D.E_le hw₁Q hw₂Q hw₁M hw₂M hc12.symm
      (by rw [hsq]; exact I.wV_mem _) (by rw [hsq₂]; exact I.wV_mem _)
  · rcases Fin.exists_fin_two.mp ⟨α, rfl⟩ with rfl | rfl
    · left; exact ⟨rfl, by simp [hw₁]⟩
    · right; exact ⟨rfl, by simp [hw₁]⟩
  · rw [hy, hw₂M.conj_t]
    simp [transCols, Inst.wV, hIy, S.data.commute_t S.xy_mem.1]
  · have := Inst.QD.commute_wV_transl hw₂M 1 0 0
    rwa [show I.wV (1, 0, 0, 0) = S.z by simp [Inst.wV]] at this
  · have := Inst.QD.commute_wV_transl hw₂M 0 1 0
    rwa [show I.wV (0, 1, 0, 0) = F.yF by simp [Inst.wV, hIy, hy]] at this
  · have := Inst.QD.commute_wV_transl hw₂M 0 0 1
    rwa [show I.wV (0, 0, 0, 1) = F.kF by simp [Inst.wV, hIk, hk]] at this
  · rcases Fin.exists_fin_two.mp ⟨α, rfl⟩ with rfl | rfl
    · left
      refine ⟨rfl, by rw [hsq]; simp [Inst.wV], by rw [hsq₂]; simp [Inst.wV]⟩
    · right
      refine ⟨rfl, by rw [hsq]; simp [Inst.wV], by rw [hsq₂, hy]; simp [Inst.wV, hIy]⟩
  · rw [hu]
    have h1 : S.y * D.w2 w₁ * S.y⁻¹ = d⁻¹ * w₁ * d := by
      calc S.y * D.w2 w₁ * S.y⁻¹ = (S.y * d * S.y⁻¹) * (S.y * w₁ * S.y⁻¹) *
            (S.y * d * S.y⁻¹)⁻¹ := by simp only [Inst.QD.w2, hDd]; group
        _ = d⁻¹ * w₁ * d := by rw [hud, hyw₁, inv_inv]
    rw [h1, ← hdw₂]
    calc d⁻¹ * w₁ * d = d⁻¹ * (D.d ^ 3 * w₁ * (D.d ^ 3)⁻¹) * d := by rw [hd3w]; group
      _ = D.d * D.w2 w₁ * D.d⁻¹ := by
          simp only [Inst.QD.w2, hDd, pow_succ, pow_zero, one_mul]; group
  · rw [hE₁]
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hdM.1, hdQ⟩, hdM.mem_centralizer_t (by decide)⟩
  · obtain ⟨a, ha⟩ := hd3
    have hdvd : orderOf d ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one ha
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  · rw [hy, hdM.conj_z]; simp [dCols, sigCols, Inst.wV, hIy]
  · rw [hy, ← hIy, hdM.conj_yi]; simp [dCols, sigCols, Inst.wV, hIy]
  · rw [hk, ← hIk, hdM.conj_ki]; simp [dCols, sigCols, Inst.wV]
  · rw [hu, hud, inv_mul_cancel]; exact one_mem _

end Sec5Hyp

end A7Base

theorem fritzA7Section5Data : FritzA7Section5Data := by
  intro X _ _ S F T₁ h4 hF hg
  exact (A7Base.Sec5Hyp.of_sec4 h4 hF hg).exists_sec5 F hF

end CFSG.ComponentClassification.HSFLit
