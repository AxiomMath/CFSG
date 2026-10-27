module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Shape

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

namespace Setup27

variable {G : Type} [Group G] [Finite G] {A R X O Sy Wt P : Subgroup G} {t : G}
  (H : Setup27 A R X O Sy Wt P t)

include H

theorem comm_t_mem_R {w : G} (hw : w ∈ Sy ⊓ Wt) : t * w * t⁻¹ * w⁻¹ ∈ R :=
  H.sit.S.commutator_t_mem_W (H.sit.hSy.le (mem_inf.mp hw).1)

theorem comm_t_mul {w₁ w₂ : G} (hw₁ : w₁ ∈ Sy ⊓ Wt) (hw₂ : w₂ ∈ Sy ⊓ Wt) :
    t * (w₁ * w₂) * t⁻¹ * (w₁ * w₂)⁻¹ =
      (t * w₁ * t⁻¹ * w₁⁻¹) * (t * w₂ * t⁻¹ * w₂⁻¹) := by
  have hRW : R ≤ Sy ⊓ Wt := H.sit.S.W_le_inf_Wt H.sit.hSy H.sit.hWt
  have hab := H.sit.S.elem_inf_Wt H.sit.hSy H.sit.hWt
  have hc : w₁⁻¹ * (t * w₂ * t⁻¹ * w₂⁻¹) = (t * w₂ * t⁻¹ * w₂⁻¹) * w₁⁻¹ :=
    L34.comm_of_isElemAbelian hab ((Sy ⊓ Wt).inv_mem hw₁) (hRW (H.comm_t_mem_R hw₂))
  calc t * (w₁ * w₂) * t⁻¹ * (w₁ * w₂)⁻¹
      = (t * w₁ * t⁻¹) * (t * w₂ * t⁻¹ * w₂⁻¹) * w₁⁻¹ := by group
    _ = (t * w₁ * t⁻¹) * (w₁⁻¹ * (t * w₂ * t⁻¹ * w₂⁻¹)) := by rw [mul_assoc _ _ (w₁⁻¹), ← hc]
    _ = (t * w₁ * t⁻¹ * w₁⁻¹) * (t * w₂ * t⁻¹ * w₂⁻¹) := by group

theorem comm_t_inv {w : G} (hw : w ∈ Sy ⊓ Wt) :
    t * w⁻¹ * t⁻¹ * (w⁻¹)⁻¹ = (t * w * t⁻¹ * w⁻¹)⁻¹ := by
  have h1 := H.comm_t_mul hw ((Sy ⊓ Wt).inv_mem hw)
  have h2 : t * (w * w⁻¹) * t⁻¹ * (w * w⁻¹)⁻¹ = 1 := by group
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem exists_comm_t_eq {r : G} (hr : r ∈ R) : ∃ w ∈ Sy ⊓ Wt, t * w * t⁻¹ * w⁻¹ = r := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  let φ : ↥(Sy ⊓ Wt) →* ↥R :=
    { toFun := fun w => ⟨t * (w : G) * t⁻¹ * (w : G)⁻¹, H.comm_t_mem_R w.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (H.comm_t_mul a.2 b.2) }
  have hle : ⁅Sy ⊓ Wt, zpowers t⁆ ≤ φ.range.map R.subtype := by
    refine commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
    have h2 : t ^ (2 : ℤ) = 1 := (zpow_two t).trans hS.t_sq
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, h2, one_zpow, commutatorElement_one_right]
      exact one_mem _
    · rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
      refine ⟨(φ ⟨g₁, hg₁⟩)⁻¹, inv_mem (φ.mem_range.mpr ⟨⟨g₁, hg₁⟩, rfl⟩), ?_⟩
      simp only [φ, commutatorElement_def, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_inv,
        Subgroup.subtype_apply]
      group
  have hr' : r ∈ ⁅Sy ⊓ Wt, zpowers t⁆ := by rw [hS.commutator_inf_Wt hSy hWt]; exact hr
  obtain ⟨y, ⟨w, hwy⟩, hy⟩ := hle hr'
  refine ⟨w, w.2, ?_⟩
  rw [← hy, ← hwy]
  rfl

theorem commutator_W_P_le : ⁅Sy ⊓ Wt, P⁆ ≤ Sy ⊓ Wt := by
  refine commutator_le.mpr fun w hw p hp => ?_
  have h1 : p * w⁻¹ * p⁻¹ ∈ Sy ⊓ Wt :=
    (mem_normalizer_iff.mp (H.le_normalizer_W hp) w⁻¹).mp ((Sy ⊓ Wt).inv_mem hw)
  have h2 : ⁅w, p⁆ = w * (p * w⁻¹ * p⁻¹) := by simp only [commutatorElement_def]; group
  rw [h2]
  exact (Sy ⊓ Wt).mul_mem hw h1

theorem conj_mem_commutator_W_P {p : G} (hp : p ∈ P) {j : G} (hj : j ∈ ⁅Sy ⊓ Wt, P⁆) :
    p * j * p⁻¹ ∈ ⁅Sy ⊓ Wt, P⁆ := by
  have h : ⁅Sy ⊓ Wt, P⁆ ≤ (⁅Sy ⊓ Wt, P⁆).comap (MulAut.conj p).toMonoidHom := by
    refine commutator_le.mpr fun w hw q hq => ?_
    rw [mem_comap]
    have e : (MulAut.conj p).toMonoidHom ⁅w, q⁆ = ⁅p * w * p⁻¹, p * q * p⁻¹⁆ := by
      simp only [commutatorElement_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    refine commutator_mem_commutator ?_ (P.mul_mem (P.mul_mem hp hq) (P.inv_mem hp))
    exact (mem_normalizer_iff.mp (H.le_normalizer_W hp) w).mp hw
  have := h hj
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

omit H in
theorem exists_three_distinct (α : Type*) [Finite α] (h : 2 < Nat.card α) :
    ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card] at h
  exact Fintype.two_lt_card_iff.mp h

theorem exists_comm_ne_one : ∃ j ∈ ⁅Sy ⊓ Wt, P⁆, t * j * t⁻¹ * j⁻¹ ≠ 1 := by
  have hS := H.sit.S
  have hRW : R ≤ Sy ⊓ Wt := hS.W_le_inf_Wt H.sit.hSy H.sit.hWt
  obtain ⟨a, b, c, hab, hac, hbc⟩ := exists_three_distinct ↥R (by rw [hS.W_card]; norm_num)
  obtain ⟨r, s, hr1, hs1, hrs⟩ : ∃ r s : ↥R, r ≠ 1 ∧ s ≠ 1 ∧ r ≠ s := by
    by_cases ha : a = 1
    · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
    · by_cases hb : b = 1
      · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨p, hp, hpr⟩ := H.hP.trans r.1 r.2 s.1 s.2 (fun h => hr1 (Subtype.ext h))
    (fun h => hs1 (Subtype.ext h))
  obtain ⟨w, hw, hwr⟩ := H.exists_comm_t_eq r.2
  have hpw : p * w * p⁻¹ ∈ Sy ⊓ Wt := (mem_normalizer_iff.mp (H.le_normalizer_W hp) w).mp hw
  have hjmem : (p * w * p⁻¹ * w⁻¹) ∈ ⁅Sy ⊓ Wt, P⁆ := by
    have := Subgroup.inv_mem _ (commutator_mem_commutator hw hp)
    rwa [commutatorElement_inv, commutatorElement_def] at this
  refine ⟨_, hjmem, fun h => hrs (Subtype.ext ?_)⟩
  have hpt : p * t * p⁻¹ = t := by rw [H.P_comm_t hp]; group
  have h1 : t * (p * w * p⁻¹) * t⁻¹ * (p * w * p⁻¹)⁻¹ = s := by
    rw [← hpr, ← hwr]
    calc t * (p * w * p⁻¹) * t⁻¹ * (p * w * p⁻¹)⁻¹
        = (p * t * p⁻¹) * (p * w * p⁻¹) * (p * t * p⁻¹)⁻¹ * (p * w * p⁻¹)⁻¹ := by rw [hpt]
      _ = p * (t * w * t⁻¹ * w⁻¹) * p⁻¹ := by group
  have h2 := H.comm_t_mul hpw ((Sy ⊓ Wt).inv_mem hw)
  have h3 : t * (p * w * p⁻¹ * w⁻¹) * t⁻¹ * (p * w * p⁻¹ * w⁻¹)⁻¹ =
      (s : G) * (r : G)⁻¹ := by
    rw [h2, h1, H.comm_t_inv hw, hwr]
  rw [h3] at h
  have : (s : G) = r := by
    have := mul_inv_eq_one.mp h
    exact this
  exact this.symm

theorem exists_comm_eq_of_mem_R {s : G} (hs : s ∈ R) :
    ∃ j ∈ ⁅Sy ⊓ Wt, P⁆, t * j * t⁻¹ * j⁻¹ = s := by
  by_cases hs1 : s = 1
  · exact ⟨1, one_mem _, by simp [hs1]⟩
  obtain ⟨j₀, hj₀, hne⟩ := H.exists_comm_ne_one
  have hjW : j₀ ∈ Sy ⊓ Wt := H.commutator_W_P_le hj₀
  have hr₀ : t * j₀ * t⁻¹ * j₀⁻¹ ∈ R := H.comm_t_mem_R hjW
  obtain ⟨p, hp, hps⟩ := H.hP.trans _ hr₀ s hs hne hs1
  refine ⟨p * j₀ * p⁻¹, H.conj_mem_commutator_W_P hp hj₀, ?_⟩
  have hpt : p * t * p⁻¹ = t := by rw [H.P_comm_t hp]; group
  rw [← hps]
  calc t * (p * j₀ * p⁻¹) * t⁻¹ * (p * j₀ * p⁻¹)⁻¹
      = (p * t * p⁻¹) * (p * j₀ * p⁻¹) * (p * t * p⁻¹)⁻¹ * (p * j₀ * p⁻¹)⁻¹ := by rw [hpt]
    _ = p * (t * j₀ * t⁻¹ * j₀⁻¹) * p⁻¹ := by group

theorem exists_mul_of_mem {w : G} (hw : w ∈ Sy ⊓ Wt) :
    ∃ j ∈ ⁅Sy ⊓ Wt, P⁆, ∃ r ∈ R, w = j * r := by
  have hS := H.sit.S
  have hRW : R ≤ Sy ⊓ Wt := hS.W_le_inf_Wt H.sit.hSy H.sit.hWt
  have hab := hS.elem_inf_Wt H.sit.hSy H.sit.hWt
  obtain ⟨j, hj, hjw⟩ := H.exists_comm_eq_of_mem_R (H.comm_t_mem_R hw)
  have hjW : j ∈ Sy ⊓ Wt := H.commutator_W_P_le hj
  have hmul := H.comm_t_mul hw ((Sy ⊓ Wt).inv_mem hjW)
  have hinv := H.comm_t_inv hjW
  rw [hinv, hjw] at hmul
  have hone : t * (w * j⁻¹) * t⁻¹ * (w * j⁻¹)⁻¹ = 1 := by
    rw [hmul]
    exact mul_inv_cancel _
  have hcomm : (w * j⁻¹) * t = t * (w * j⁻¹) := by
    have h := mul_inv_eq_one.mp hone
    calc (w * j⁻¹) * t = (t * (w * j⁻¹) * t⁻¹) * t := by rw [h]
      _ = t * (w * j⁻¹) := by group
  have hwj : w * j⁻¹ ∈ Sy ⊓ Wt ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨(Sy ⊓ Wt).mul_mem hw ((Sy ⊓ Wt).inv_mem hjW),
      mem_centralizer_singleton_iff.mpr hcomm⟩
  rw [hS.inf_Wt_inf_centralizer_t H.sit.hSy H.sit.hWt] at hwj
  refine ⟨j, hj, w * j⁻¹, hwj, ?_⟩
  have hjw' : j * w = w * j := L34.comm_of_isElemAbelian hab hjW hw
  calc w = (w * j) * j⁻¹ := by group
    _ = (j * w) * j⁻¹ := by rw [hjw']
    _ = j * (w * j⁻¹) := by group

theorem commutator_P_O_eq_bot : ⁅P, O⁆ = ⊥ := by
  refine commutator_eq_bot_iff_le_centralizer.mpr fun p hp => ?_
  rw [mem_centralizer_iff]
  intro o ho
  exact (mem_centralizer_iff.mp (H.sit.S.O_le_centralizer_A H.sit.F ho) p (H.hP.le_A hp)).symm

theorem commutator_O_W_le : ⁅O, Sy ⊓ Wt⁆ ≤ O := by
  refine commutator_le.mpr fun o ho w hw => ?_
  have h1 : w * o⁻¹ * w⁻¹ ∈ O := H.sit.S.O_norm w (H.sit.hSy.le (mem_inf.mp hw).1) _ (O.inv_mem ho)
  have h2 : ⁅o, w⁆ = o * (w * o⁻¹ * w⁻¹) := by simp only [commutatorElement_def]; group
  rw [h2]
  exact O.mul_mem ho h1

theorem O_le_centralizer_W : O ≤ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  have hS := H.sit.S
  have h1 : ⁅⁅P, O⁆, Sy ⊓ Wt⁆ = ⊥ := by rw [H.commutator_P_O_eq_bot, commutator_bot_left]
  have h2 : ⁅⁅O, Sy ⊓ Wt⁆, P⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅O, Sy ⊓ Wt⁆, P⁆ ≤ ⁅O, P⁆ := commutator_mono_left H.commutator_O_W_le
      _ = ⊥ := by rw [commutator_comm, H.commutator_P_O_eq_bot]
  have h3 : ⁅⁅Sy ⊓ Wt, P⁆, O⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  have h4 : ⁅Sy ⊓ Wt, P⁆ ≤ centralizer (O : Set G) := commutator_eq_bot_iff_le_centralizer.mp h3
  intro o ho
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨j, hj, r, hr, rfl⟩ := H.exists_mul_of_mem hw
  have hjo : o * j = j * o := mem_centralizer_iff.mp (h4 hj) o ho
  have hro : r * o = o * r := (hS.O_comm ho (mem_sup_left hr)).symm
  calc j * r * o = j * (r * o) := by rw [mul_assoc]
    _ = j * (o * r) := by rw [hro]
    _ = (j * o) * r := by rw [mul_assoc]
    _ = (o * j) * r := by rw [hjo]
    _ = o * (j * r) := by rw [mul_assoc]

theorem inf_Wt_le_normalizer_O : Sy ⊓ Wt ≤ normalizer (O : Set G) := fun x hx =>
  Subgroup.mem_normalizer_fintype fun o ho =>
    H.sit.S.O_norm x (H.sit.hSy.le (mem_inf.mp hx).1) o ho

theorem mem_inf_Wt_of_two_power {z : G} (hz : z ∈ Wt) (h2 : ∃ k : ℕ, orderOf z = 2 ^ k) :
    z ∈ Sy ⊓ Wt := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  obtain ⟨o, ho, v, hv, hov⟩ := hS.eq_mul_of_card (Z := Wt) (P := Sy ⊓ Wt) (k := 8) hWt.O_le
    inf_le_right (hS.card_inf_Wt hSy hWt) hWt.card H.inf_Wt_le_normalizer_O z hz
  have hvo : v * o = o * v := mem_centralizer_iff.mp (H.O_le_centralizer_W ho) v hv
  have hv2 : ∃ k : ℕ, orderOf v = 2 ^ k := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hSy.isPGroup.to_inf_left ⟨v, hv⟩
    exact ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩
  have hvo2 : ∃ k : ℕ, orderOf (v * o) = 2 ^ k := by
    rw [hvo, ← hov]
    exact h2
  have ho1 : o = 1 := hS.eq_one_of_two_power ho hvo hv2 hvo2
  rw [hov, ho1, one_mul]
  exact hv

theorem W_normalized_by_NE :
    normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  intro n hn
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  have hw' : w ∈ Sy ⊓ Wt := hw
  have hnw : n * w * n⁻¹ ∈ Wt := H.sit.hWt.norm n hn w (mem_inf.mp hw').2
  refine H.mem_inf_Wt_of_two_power hnw ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp H.sit.hSy.isPGroup.to_inf_left ⟨w, hw'⟩
  refine ⟨k, ?_⟩
  have := MulEquiv.orderOf_eq (MulAut.conj n) w
  rw [MulAut.conj_apply] at this
  rw [this]
  rwa [Subgroup.orderOf_mk] at hk

theorem normalizer_A_R_le_normalizer_E :
    A ⊓ normalizer (R : Set G) ≤ normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
  intro a ha
  obtain ⟨haA, haR⟩ := mem_inf.mp ha
  have hat : a * t = t * a := mem_centralizer_iff.mp H.sit.S.t_cent a haA
  refine Subgroup.mem_normalizer_fintype fun e he => ?_
  have he' : e ∈ R ⊔ zpowers t := he
  rcases (H.sit.S.mem_E_iff).mp he' with heR | ⟨r, hr, rfl⟩
  · exact mem_sup_left ((mem_normalizer_iff.mp haR e).mp heR)
  · have : a * (r * t) * a⁻¹ = (a * r * a⁻¹) * t := by
      calc a * (r * t) * a⁻¹ = a * r * a⁻¹ * (a * t * a⁻¹) := by group
        _ = (a * r * a⁻¹) * t := by rw [hat]; group
    show a * (r * t) * a⁻¹ ∈ R ⊔ zpowers t
    rw [this]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp haR r).mp hr))
      (mem_sup_right (mem_zpowers t))

theorem normalizer_A_R_le_normalizer_W :
    A ⊓ normalizer (R : Set G) ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
  H.normalizer_A_R_le_normalizer_E.trans H.W_normalized_by_NE

theorem inf_X_eq : Sy ⊓ X = (Sy ⊓ Wt) ⊔ zpowers t :=
  (H.sit.S.inf_centralizer_W_eq H.sit.hSy).symm.trans
    (H.sit.S.Sy_inf_centralizer_W H.sit.hSy H.sit.hWt)

theorem mem_inf_X_of_two_power {x : G} (hx : x ∈ X) (h2 : ∃ k : ℕ, orderOf x = 2 ^ k) :
    x ∈ Sy ⊓ X := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hYO : Sy ⊓ X ≤ normalizer (O : Set G) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun o ho => hS.O_norm y (hSy.le (mem_inf.mp hy).1) o ho
  obtain ⟨o, ho, p, hp, rfl⟩ := hS.eq_mul_of_card (Z := X) (P := Sy ⊓ X) hS.O_le_X inf_le_right
    (hS.card_inf_X hSy) hS.card_X hYO x hx
  have hpE : p ∈ (Sy ⊓ Wt) ⊔ zpowers t := H.inf_X_eq ▸ hp
  have hle : (Sy ⊓ Wt) ⊔ zpowers t ≤ centralizer ({o} : Set G) := by
    refine sup_le (fun w hw => ?_) (zpowers_le.mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (H.O_le_centralizer_W ho) w hw)
    · exact mem_centralizer_singleton_iff.mpr (hS.O_comm ho (mem_sup_right (mem_zpowers t))).symm
  have hcomm : p * o = o * p := mem_centralizer_singleton_iff.mp (hle hpE)
  have hv : ∃ n : ℕ, orderOf p = 2 ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hSy.isPGroup ⟨p, (mem_inf.mp hp).1⟩
    exact ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩
  have ho1 : o = 1 := hS.eq_one_of_two_power ho hcomm hv (by rw [hcomm]; exact h2)
  rw [ho1, one_mul]
  exact hp

theorem eq_W_of_elem {D : Subgroup G} (hDC : D ≤ centralizer (R : Set G))
    (hDe : IsElemAbelian 2 D) (hDcard : Nat.card D = 2 ^ 8)
    (hDt : D ⊓ centralizer ({t} : Set G) = R) (hDcomm : ⁅D, zpowers t⁆ = R) :
    D = Sy ⊓ Wt := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hT := H.inf_X_eq
  have htt : t * t = 1 := hS.t_sq
  have hDN : D ≤ normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
    intro d hd
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    have he' : e ∈ R ⊔ zpowers t := he
    rcases hS.mem_E_iff.mp he' with heR | ⟨r, hr, rfl⟩
    · have : d * e * d⁻¹ = e := by
        rw [← mem_centralizer_iff.mp (hDC hd) e heR, mul_inv_cancel_right]
      show d * e * d⁻¹ ∈ R ⊔ zpowers t
      rw [this]
      exact mem_sup_left heR
    · have hc : ⁅d, t⁆ ∈ R := hDcomm ▸ commutator_mem_commutator hd (mem_zpowers t)
      have h1 : d * (r * t) * d⁻¹ = r * ⁅d, t⁆ * t := by
        have hrd : d * r * d⁻¹ = r := by
          rw [← mem_centralizer_iff.mp (hDC hd) r hr, mul_inv_cancel_right]
        calc d * (r * t) * d⁻¹ = (d * r * d⁻¹) * (d * t * d⁻¹ * t⁻¹) * t := by group
          _ = r * ⁅d, t⁆ * t := by rw [hrd, commutatorElement_def]
      show d * (r * t) * d⁻¹ ∈ R ⊔ zpowers t
      rw [h1]
      exact mul_mem (mul_mem (mem_sup_left hr) (mem_sup_left hc)) (mem_sup_right (mem_zpowers t))
  have hDX : D ≤ X := fun d hd =>
    hS.normalizer_inf_centralizer_le (mem_inf.mpr ⟨hDN hd, hDC hd⟩)
  have hDT : D ≤ (Sy ⊓ Wt) ⊔ zpowers t := by
    intro d hd
    rw [← hT]
    refine H.mem_inf_X_of_two_power (hDX hd) ?_
    have h1 : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (hDe.2 d hd)
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; rfl⟩
  have hTcard : Nat.card ↥((Sy ⊓ Wt) ⊔ zpowers t) = 2 ^ 9 := by
    rw [← hT]
    exact hS.card_inf_X hSy
  have hWcard : Nat.card ↥(Sy ⊓ Wt) = 2 ^ 8 := hS.card_inf_Wt hSy hWt
  have hWT : Sy ⊓ Wt ≤ (Sy ⊓ Wt) ⊔ zpowers t := le_sup_left
  by_cases hDW : D ≤ Sy ⊓ Wt
  · exact Subgroup.eq_of_le_of_card_ge hDW (by rw [hDcard, hWcard])
  · exfalso
    obtain ⟨d₀, hd₀, hd₀W⟩ := Set.not_subset.mp hDW
    have hd₀T := hDT hd₀
    have htN : t ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
      hS.t_mem_normalizer_inf_Wt hSy hWt
    open scoped Pointwise in
    have hmul : ((Sy ⊓ Wt) ⊔ zpowers t : Subgroup G) = ((Sy ⊓ Wt : Subgroup G) : Set G) *
        ((zpowers t : Subgroup G) : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left (Sy ⊓ Wt) (zpowers t)
        (Subgroup.zpowers_le.mpr htN)
    rw [← SetLike.mem_coe, hmul] at hd₀T
    obtain ⟨w₀, hw₀, y, hy, hd₀y⟩ := hd₀T
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    replace hd₀y : w₀ * t ^ k = d₀ := hd₀y
    have hpow : ∀ k : ℤ, t ^ k = 1 ∨ t ^ k = t := by
      intro k
      have h2 : t ^ (2 : ℤ) = 1 := (zpow_two t).trans htt
      obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
      · left
        rw [zpow_mul, h2, one_zpow]
      · right
        rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
    have hd₀eq : d₀ = w₀ * t := by
      rcases hpow k with hk | hk
      · exfalso
        apply hd₀W
        rw [← hd₀y, hk, mul_one]
        exact hw₀
      · rw [← hd₀y, hk]
    have hDWR : D ⊓ (Sy ⊓ Wt) ≤ R := by
      intro u hu
      obtain ⟨huD, huW⟩ := mem_inf.mp hu
      rw [← hDt]
      refine mem_inf.mpr ⟨huD, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : u * d₀ = d₀ * u := L34.comm_of_isElemAbelian hDe huD hd₀
      have h2 : u * w₀ = w₀ * u := L34.comm_of_isElemAbelian (hS.elem_inf_Wt hSy hWt) huW hw₀
      rw [hd₀eq] at h1
      have h3 : w₀ * (u * t) = w₀ * (t * u) := by
        calc w₀ * (u * t) = (w₀ * u) * t := by rw [mul_assoc]
          _ = (u * w₀) * t := by rw [h2]
          _ = u * (w₀ * t) := by rw [mul_assoc]
          _ = (w₀ * t) * u := h1
          _ = w₀ * (t * u) := by rw [mul_assoc]
      exact mul_left_cancel h3
    have hDrel : D.relIndex ((Sy ⊓ Wt) ⊔ zpowers t) = 2 := by
      have h := Subgroup.relIndex_mul_card D ((Sy ⊓ Wt) ⊔ zpowers t)
      rw [inf_eq_left.mpr hDT, hDcard, hTcard] at h
      omega
    have hWrel : (Sy ⊓ Wt).relIndex ((Sy ⊓ Wt) ⊔ zpowers t) = 2 := by
      have h := Subgroup.relIndex_mul_card (Sy ⊓ Wt) ((Sy ⊓ Wt) ⊔ zpowers t)
      rw [inf_eq_left.mpr hWT, hWcard, hTcard] at h
      omega
    have hinf := Subgroup.relIndex_inf_le (H := D) (K := Sy ⊓ Wt) (L := (Sy ⊓ Wt) ⊔ zpowers t)
    rw [hDrel, hWrel] at hinf
    have hcard := Subgroup.relIndex_mul_card (D ⊓ (Sy ⊓ Wt)) ((Sy ⊓ Wt) ⊔ zpowers t)
    have hle2 : D ⊓ (Sy ⊓ Wt) ⊓ ((Sy ⊓ Wt) ⊔ zpowers t) = D ⊓ (Sy ⊓ Wt) :=
      inf_eq_left.mpr (inf_le_right.trans hWT)
    rw [hle2, hTcard] at hcard
    have hsmall : Nat.card ↥(D ⊓ (Sy ⊓ Wt)) ≤ 16 := by
      have := Subgroup.card_le_of_le hDWR
      rwa [hS.W_card] at this
    have hpos : 0 < Nat.card ↥(D ⊓ (Sy ⊓ Wt)) := Nat.card_pos
    have : 2 ^ 9 ≤ 4 * 16 := by
      calc 2 ^ 9 = (D ⊓ (Sy ⊓ Wt)).relIndex ((Sy ⊓ Wt) ⊔ zpowers t) *
            Nat.card ↥(D ⊓ (Sy ⊓ Wt)) := hcard.symm
        _ ≤ 4 * 16 := Nat.mul_le_mul (by omega) hsmall
    omega

end Setup27

end CFSG.OddStandard.Seitz77
