module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveLabAgree
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveLabPerm
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMDual

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Util

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem linTv_congr (e : L ≃* LinearFlag.projectiveSL n K) {i j i' j' : Fin n} (h : i ≠ j)
    (h' : i' ≠ j') (hi : i = i') (hj : j = j') : linTv e h = linTv e h' := by
  subst hi hj
  rfl

theorem swap_mul_swap_comm_of_ne {n : ℕ} {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  ext x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem pointParabolic_le (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n)
    {H : Subgroup G} (hH : ∀ i j (hij : i ≠ j), j ≠ c → linTv e hij ∈ H) :
    pointParabolic e c ≤ H := by
  refine sup_le (modelToG_pointRadical_le hK e c fun j hcj => hH c j hcj (Ne.symm hcj)) ?_
  refine (modelToG_blockSL_le_closure_linTv hK e c).trans ((closure_le H).2 ?_)
  rintro _ ⟨⟨⟨i, j⟩, hij, -, hj⟩, rfl⟩
  exact hH i j hij hj

theorem liftIn_inv {t : G} {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) {y : G}
    (h : ∃ x ∈ A, x * (t * x * t⁻¹) = y) (h' : ∃ x ∈ A, x * (t * x * t⁻¹) = y⁻¹) :
    liftIn t A y⁻¹ = (liftIn t A y)⁻¹ := by
  have h1 := liftIn_mul hA hAA h h'
  rw [mul_inv_cancel, liftIn_eq hA hAA (one_mem A) (by group)] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem liftIn_map_conj_t {t : G} (ht : t * t = 1) {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) {y : G}
    (h : ∃ x ∈ A, x * (t * x * t⁻¹) = y) :
    liftIn t (A.map (MulAut.conj t).toMonoidHom) y = t * liftIn t A y * t⁻¹ := by
  have htt := map_conj_map_conj_eq_of_mul_self ht A
  have hA' : (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((A.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    rw [htt]
    exact le_centralizer_iff.1 hA
  have hAA' : A.map (MulAut.conj t).toMonoidHom ⊓
      (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [htt, inf_comm, hAA]
  obtain ⟨h1, h2⟩ := liftIn_spec h
  apply liftIn_eq hA' hAA' (conj_mem_map_conj_t h1)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc := conj_mul_comm_of_mem hA h1 h1
  calc t * liftIn t A y * t⁻¹ * (t * (t * liftIn t A y * t⁻¹) * t⁻¹)
      = (t * liftIn t A y * t⁻¹) * ((t * t) * liftIn t A y * (t * t)⁻¹) := by group
    _ = (t * liftIn t A y * t⁻¹) * liftIn t A y := by rw [ht]; group
    _ = liftIn t A y * (t * liftIn t A y * t⁻¹) := hc
    _ = y := h2

end Util

theorem liftIn_conj_of_mem {G : Type*} [Group G] {t : G} {A : Subgroup G} {P : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hex : ∀ y ∈ P, ∃ x ∈ A, x * (t * x * t⁻¹) = y) {q y : G} (hq : q ∈ P) (hqt : q * t = t * q)
    (hy : y ∈ P) : liftIn t A (q * y * q⁻¹) = q * liftIn t A y * q⁻¹ := by
  obtain ⟨a, haA, haq⟩ := hex q hq
  have h1 := liftIn_conj hA hAA haA (by rw [haq]; exact hqt) (hex y hy)
  rwa [haq] at h1

section Label

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
  [CharP K 2]

theorem liftIn_eq_of_mem_inf (hset : SeitzSetting G L) (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c₀ c₁ : Fin n} (hc : c₀ ≠ c₁) {W₀ X₀ W₁ X₁ : Subgroup G}
    (h₀ : LinearTwoSwapModuleData e t c₀ W₀ X₀)
    (h₁ : LinearTwoSwapModuleData (e.trans (LinearFlag.dualAut n K)) t c₁ W₁ X₁)
    (hV : ∀ v ∈ modelToG e (pointRadical (K := K) c₀), liftIn t X₁ v = liftIn t X₀ v)
    (hV' : ∀ v ∈ modelToG (e.trans (LinearFlag.dualAut n K)) (pointRadical (K := K) c₁),
      liftIn t X₁ v = liftIn t X₀ v)
    {i j : Fin n} (hij : i ≠ j) (hj₀ : j ≠ c₀) (hi₁ : i ≠ c₁) :
    liftIn t X₁ (linTv e hij) = liftIn t X₀ (linTv e hij) := by
  by_cases hi₀ : i = c₀
  · subst hi₀
    exact hV _ (linTv_mem_pointRadical e hij)
  by_cases hj₁ : j = c₁
  · subst hj₁
    apply hV'
    have h := linTv_mem_pointRadical (e.trans (LinearFlag.dualAut n K)) (Ne.symm hij)
    rwa [linTv_trans_dualAut] at h
  · exact liftIn_eq_of_levi hset hn hK e ht hKt hc h₀ h₁ hV hV' hij hi₀ hi₁ hj₀ hj₁

theorem liftIn_commute_of_transport (hset : SeitzSetting G L) (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c₀ c₁ : Fin n} (hc : c₀ ≠ c₁) {W₀ X₀ W₁ X₁ : Subgroup G}
    (h₀ : LinearTwoSwapModuleData e t c₀ W₀ X₀)
    (h₁ : LinearTwoSwapModuleData (e.trans (LinearFlag.dualAut n K)) t c₁ W₁ X₁)
    (hV : ∀ v ∈ modelToG e (pointRadical (K := K) c₀), liftIn t X₁ v = liftIn t X₀ v)
    (hV' : ∀ v ∈ modelToG (e.trans (LinearFlag.dualAut n K)) (pointRadical (K := K) c₁),
      liftIn t X₁ v = liftIn t X₀ v)
    {k l : Fin n} (hk₀ : k ≠ c₀) (hk₁ : k ≠ c₁) (hl₀ : l ≠ c₀) (hl₁ : c₁ ≠ l) :
    liftIn t X₀ (linTv e hl₁) * (t * liftIn t X₁ (linTv e hk₀) * t⁻¹) =
      (t * liftIn t X₁ (linTv e hk₀) * t⁻¹) * liftIn t X₀ (linTv e hl₁) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hLt : ∀ y ∈ L, y * t = t * y := fun y hy => mem_centralizer_iff.1 htC y hy
  set e' := e.trans (LinearFlag.dualAut n K) with he'
  obtain ⟨hA₀, hAA₀, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e htt htC h₀
  obtain ⟨hA₁, hAA₁, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e' htt htC h₁
  obtain ⟨-, -, hex₀⟩ := swapModuleData_lift hset (by omega) hK e ht hKt h₀
  obtain ⟨-, -, hex₁⟩ := swapModuleData_lift hset (by omega) hK e' ht hKt h₁
  have hagree := fun {i j : Fin n} (hij : i ≠ j) (hj₀ : j ≠ c₀) (hi₁ : i ≠ c₁) =>
    liftIn_eq_of_mem_inf hset hn hK e ht hKt hc h₀ h₁ hV hV' hij hj₀ hi₁
  obtain ⟨c, hcS⟩ := exists_not_mem_of_card_lt_fin ({c₀, c₁, k, l} : Finset (Fin n))
    ((Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcS
  obtain ⟨hcc₀, hcc₁, hck, hcl⟩ := hcS
  obtain ⟨c', hc'S⟩ := exists_not_mem_of_card_lt_fin ({c₀, c₁, c, l} : Finset (Fin n))
    ((Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'S
  obtain ⟨hc'c₀, hc'c₁, hc'c, hc'l⟩ := hc'S
  set w₁ := permElt e (Equiv.swap c₀ c) with hw₁
  set w₂ := permElt e (Equiv.swap c₁ c') with hw₂
  have hw₁t := hLt w₁ (permElt_mem e _)
  have hw₂t := hLt w₂ (permElt_mem e _)
  have hw₁P₁ : w₁ ∈ pointParabolic e' c₁ :=
    (permElt_mem_pointParabolic hK (by omega) e
      (Equiv.swap_apply_of_ne_of_ne (Ne.symm hc) (Ne.symm hcc₁))).2
  have hw₂P₀ : w₂ ∈ pointParabolic e c₀ :=
    (permElt_mem_pointParabolic hK (by omega) e
      (Equiv.swap_apply_of_ne_of_ne hc (Ne.symm hc'c₀))).1
  have hcomm : w₁ * w₂ = w₂ * w₁ :=
    permElt_commute e (swap_mul_swap_comm_of_ne hc (Ne.symm hc'c₀) hcc₁ (Ne.symm hc'c))
  have hkc : k ≠ c := Ne.symm hck
  have hc'l' : c' ≠ l := hc'l
  have f1 : w₁ * linTv e hkc * w₁⁻¹ = linTv e hk₀ := by
    rw [hw₁, permElt_conj_linTv]
    apply linTv_congr
    · rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hk₀ hkc]
    · rw [Equiv.symm_swap, Equiv.swap_apply_right]
  have f4 : w₂ * linTv e hc'l' * w₂⁻¹ = linTv e hl₁ := by
    rw [hw₂, permElt_conj_linTv]
    apply linTv_congr
    · rw [Equiv.symm_swap, Equiv.swap_apply_right]
    · rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne (Ne.symm hl₁) (Ne.symm hc'l)]
  have f5 : w₁ * linTv e hc'l' * w₁⁻¹ = linTv e hc'l' := by
    rw [hw₁, permElt_conj_linTv]
    apply linTv_congr
    · rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hc'c₀ hc'c]
    · rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hl₀ (Ne.symm hcl)]
  have hm₀ : ∀ {a b : Fin n} (hab : a ≠ b), b ≠ c₀ → linTv e hab ∈ pointParabolic e c₀ :=
    fun hab hb => linTv_mem_pointParabolic e hab hb
  have hm₁ : ∀ {a b : Fin n} (hab : a ≠ b), a ≠ c₁ → linTv e hab ∈ pointParabolic e' c₁ :=
    fun hab ha => linTv_mem_pointParabolic_dual e hab ha
  have hA : liftIn t X₀ (linTv e hl₁) = w₂ * liftIn t X₁ (linTv e hc'l') * w₂⁻¹ := by
    rw [← f4, liftIn_conj_of_mem hA₀ hAA₀ hex₀ hw₂P₀ hw₂t (hm₀ hc'l' hl₀),
      hagree hc'l' hl₀ hc'c₁]
  have hB : w₁ * liftIn t X₀ (linTv e hl₁) * w₁⁻¹ = liftIn t X₀ (linTv e hl₁) := by
    have h1 : w₁ * liftIn t X₁ (linTv e hc'l') * w₁⁻¹ = liftIn t X₁ (linTv e hc'l') := by
      rw [← liftIn_conj_of_mem hA₁ hAA₁ hex₁ hw₁P₁ hw₁t (hm₁ hc'l' hc'c₁), f5]
    have hcomm' : w₁ * w₂ * w₁⁻¹ = w₂ := by rw [hcomm, mul_inv_cancel_right]
    rw [hA]
    calc w₁ * (w₂ * liftIn t X₁ (linTv e hc'l') * w₂⁻¹) * w₁⁻¹
        = (w₁ * w₂ * w₁⁻¹) * (w₁ * liftIn t X₁ (linTv e hc'l') * w₁⁻¹) *
            (w₁ * w₂ * w₁⁻¹)⁻¹ := by group
      _ = w₂ * liftIn t X₁ (linTv e hc'l') * w₂⁻¹ := by rw [hcomm', h1]
  have hC : liftIn t X₁ (linTv e hk₀) = w₁ * liftIn t X₀ (linTv e hkc) * w₁⁻¹ := by
    rw [← f1, liftIn_conj_of_mem hA₁ hAA₁ hex₁ hw₁P₁ hw₁t (hm₁ hkc hk₁),
      hagree hkc hcc₀ hk₁]
  set a := liftIn t X₀ (linTv e hl₁) with ha
  set T := t * liftIn t X₀ (linTv e hkc) * t⁻¹ with hT
  have haT : a * T = T * a := (mem_centralizer_iff.1 (hA₀ (conj_mem_map_conj_t
    (liftIn_spec (hex₀ _ (hm₀ hkc hcc₀))).1)) a (liftIn_spec (hex₀ _
      (hm₀ hl₁ hl₀))).1)
  have htw : t * (w₁ * liftIn t X₀ (linTv e hkc) * w₁⁻¹) * t⁻¹ = w₁ * T * w₁⁻¹ :=
    conj_t_conj_of_commute hw₁t
  rw [hC, htw]
  calc a * (w₁ * T * w₁⁻¹) = (w₁ * a * w₁⁻¹) * (w₁ * T * w₁⁻¹) := by rw [hB]
    _ = w₁ * (a * T) * w₁⁻¹ := by group
    _ = w₁ * (T * a) * w₁⁻¹ := by rw [haT]
    _ = (w₁ * T * w₁⁻¹) * (w₁ * a * w₁⁻¹) := by group
    _ = (w₁ * T * w₁⁻¹) * a := by rw [hB]

theorem conj_le_centralizer_of_agree (hset : SeitzSetting G L) (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c₀ c₁ : Fin n} (hc : c₀ ≠ c₁) {W₀ X₀ W₁ X₁ : Subgroup G}
    (h₀ : LinearTwoSwapModuleData e t c₀ W₀ X₀)
    (h₁ : LinearTwoSwapModuleData (e.trans (LinearFlag.dualAut n K)) t c₁ W₁ X₁)
    (hV : ∀ v ∈ modelToG e (pointRadical (K := K) c₀), liftIn t X₁ v = liftIn t X₀ v)
    (hV' : ∀ v ∈ modelToG (e.trans (LinearFlag.dualAut n K)) (pointRadical (K := K) c₁),
      liftIn t X₁ v = liftIn t X₀ v) :
    X₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (X₀ : Set G) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  set e' := e.trans (LinearFlag.dualAut n K) with he'
  obtain ⟨hA₀, hAA₀, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e htt htC h₀
  obtain ⟨hA₁, hAA₁, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e' htt htC h₁
  obtain ⟨hδ₀, -, hex₀⟩ := swapModuleData_lift hset (by omega) hK e ht hKt h₀
  obtain ⟨hδ₁, -, hex₁⟩ := swapModuleData_lift hset (by omega) hK e' ht hKt h₁
  have hm₀ : ∀ {a b : Fin n} (hab : a ≠ b), b ≠ c₀ → linTv e hab ∈ pointParabolic e c₀ :=
    fun hab hb => linTv_mem_pointParabolic e hab hb
  have hm₁ : ∀ {a b : Fin n} (hab : a ≠ b), a ≠ c₁ → linTv e hab ∈ pointParabolic e' c₁ :=
    fun hab ha => linTv_mem_pointParabolic_dual e hab ha
  have hroot : ∀ {i j : Fin n} (hij : i ≠ j), j ≠ c₀ → ∀ {k l : Fin n} (hkl : k ≠ l), k ≠ c₁ →
      liftIn t X₀ (linTv e hij) * (t * liftIn t X₁ (linTv e hkl) * t⁻¹) =
        (t * liftIn t X₁ (linTv e hkl) * t⁻¹) * liftIn t X₀ (linTv e hij) := by
    intro i j hij hj₀ k l hkl hk₁
    have hβ' := (liftIn_spec (hex₁ _ (hm₁ hkl hk₁))).1
    have hα := (liftIn_spec (hex₀ _ (hm₀ hij hj₀))).1
    by_cases hi₁ : i = c₁
    · by_cases hl₀ : l = c₀
      · have hy : linTv e hij = linTv e (show c₁ ≠ j from hi₁ ▸ hij) :=
          linTv_congr e _ _ hi₁ rfl
        have hy' : linTv e hkl = linTv e (show k ≠ c₀ from hl₀ ▸ hkl) :=
          linTv_congr e _ _ rfl hl₀
        rw [hy, hy']
        exact liftIn_commute_of_transport hset hn hK e ht hKt hc h₀ h₁ hV hV'
          (hl₀ ▸ hkl) hk₁ hj₀ (hi₁ ▸ hij)
      · rw [liftIn_eq_of_mem_inf hset hn hK e ht hKt hc h₀ h₁ hV hV' hkl hl₀ hk₁]
        have hα' := (liftIn_spec (hex₀ _ (hm₀ hkl hl₀))).1
        exact mem_centralizer_iff.1 (hA₀ (conj_mem_map_conj_t hα')) _ hα
    · rw [← liftIn_eq_of_mem_inf hset hn hK e ht hKt hc h₀ h₁ hV hV' hij hj₀ hi₁]
      have hβ := (liftIn_spec (hex₁ _ (hm₁ hij hi₁))).1
      exact mem_centralizer_iff.1 (hA₁ (conj_mem_map_conj_t hβ')) _ hβ
  have hone₀ : liftIn t X₀ 1 = 1 := liftIn_eq hA₀ hAA₀ (one_mem X₀) (by group)
  have hone₁ : liftIn t X₁ 1 = 1 := liftIn_eq hA₁ hAA₁ (one_mem X₁) (by group)
  have hstep1 : ∀ {i j : Fin n} (hij : i ≠ j), j ≠ c₀ → ∀ p' ∈ pointParabolic e' c₁,
      liftIn t X₀ (linTv e hij) * (t * liftIn t X₁ p' * t⁻¹) =
        (t * liftIn t X₁ p' * t⁻¹) * liftIn t X₀ (linTv e hij) := by
    intro i j hij hj₀
    set y := liftIn t X₀ (linTv e hij)
    let H : Subgroup G :=
      { carrier := {p' | p' ∈ pointParabolic e' c₁ ∧
          y * (t * liftIn t X₁ p' * t⁻¹) = (t * liftIn t X₁ p' * t⁻¹) * y}
        mul_mem' := fun {p q} hp hq => by
          refine ⟨mul_mem hp.1 hq.1, ?_⟩
          rw [liftIn_mul hA₁ hAA₁ (hex₁ _ hp.1) (hex₁ _ hq.1)]
          calc y * (t * (liftIn t X₁ p * liftIn t X₁ q) * t⁻¹)
              = (y * (t * liftIn t X₁ p * t⁻¹)) * (t * liftIn t X₁ q * t⁻¹) := by group
            _ = ((t * liftIn t X₁ p * t⁻¹) * y) * (t * liftIn t X₁ q * t⁻¹) := by rw [hp.2]
            _ = (t * liftIn t X₁ p * t⁻¹) * (y * (t * liftIn t X₁ q * t⁻¹)) := by group
            _ = (t * liftIn t X₁ p * t⁻¹) * ((t * liftIn t X₁ q * t⁻¹) * y) := by rw [hq.2]
            _ = (t * (liftIn t X₁ p * liftIn t X₁ q) * t⁻¹) * y := by group
        one_mem' := ⟨one_mem _, by rw [hone₁]; group⟩
        inv_mem' := fun {p} hp => by
          refine ⟨inv_mem hp.1, ?_⟩
          rw [liftIn_inv hA₁ hAA₁ (hex₁ _ hp.1) (hex₁ _ (inv_mem hp.1))]
          have h2 := hp.2
          calc y * (t * (liftIn t X₁ p)⁻¹ * t⁻¹) = (t * liftIn t X₁ p * t⁻¹)⁻¹ *
                ((t * liftIn t X₁ p * t⁻¹) * y) * (t * liftIn t X₁ p * t⁻¹)⁻¹ := by group
            _ = (t * liftIn t X₁ p * t⁻¹)⁻¹ * (y * (t * liftIn t X₁ p * t⁻¹)) *
                (t * liftIn t X₁ p * t⁻¹)⁻¹ := by rw [h2]
            _ = (t * (liftIn t X₁ p)⁻¹ * t⁻¹) * y := by group }
    have hle : pointParabolic e' c₁ ≤ H := pointParabolic_le hK e' c₁ fun a b hab hb => by
      refine ⟨linTv_mem_pointParabolic e' hab hb, ?_⟩
      rw [linTv_trans_dualAut]
      exact hroot hij hj₀ hab.symm hb
    exact fun p' hp' => (hle hp').2
  have hstep2 : ∀ p ∈ pointParabolic e c₀, ∀ p' ∈ pointParabolic e' c₁,
      liftIn t X₀ p * (t * liftIn t X₁ p' * t⁻¹) =
        (t * liftIn t X₁ p' * t⁻¹) * liftIn t X₀ p := by
    let H : Subgroup G :=
      { carrier := {p | p ∈ pointParabolic e c₀ ∧ ∀ p' ∈ pointParabolic e' c₁,
          liftIn t X₀ p * (t * liftIn t X₁ p' * t⁻¹) =
            (t * liftIn t X₁ p' * t⁻¹) * liftIn t X₀ p}
        mul_mem' := fun {p q} hp hq => by
          refine ⟨mul_mem hp.1 hq.1, fun p' hp' => ?_⟩
          rw [liftIn_mul hA₀ hAA₀ (hex₀ _ hp.1) (hex₀ _ hq.1)]
          calc liftIn t X₀ p * liftIn t X₀ q * (t * liftIn t X₁ p' * t⁻¹)
              = liftIn t X₀ p * (liftIn t X₀ q * (t * liftIn t X₁ p' * t⁻¹)) := by group
            _ = liftIn t X₀ p * ((t * liftIn t X₁ p' * t⁻¹) * liftIn t X₀ q) := by
                rw [hq.2 p' hp']
            _ = (liftIn t X₀ p * (t * liftIn t X₁ p' * t⁻¹)) * liftIn t X₀ q := by group
            _ = ((t * liftIn t X₁ p' * t⁻¹) * liftIn t X₀ p) * liftIn t X₀ q := by
                rw [hp.2 p' hp']
            _ = (t * liftIn t X₁ p' * t⁻¹) * (liftIn t X₀ p * liftIn t X₀ q) := by group
        one_mem' := ⟨one_mem _, fun p' _ => by rw [hone₀]; group⟩
        inv_mem' := fun {p} hp => by
          refine ⟨inv_mem hp.1, fun p' hp' => ?_⟩
          rw [liftIn_inv hA₀ hAA₀ (hex₀ _ hp.1) (hex₀ _ (inv_mem hp.1))]
          have h2 := hp.2 p' hp'
          calc (liftIn t X₀ p)⁻¹ * (t * liftIn t X₁ p' * t⁻¹) = (liftIn t X₀ p)⁻¹ *
                ((t * liftIn t X₁ p' * t⁻¹) * liftIn t X₀ p) * (liftIn t X₀ p)⁻¹ := by group
            _ = (liftIn t X₀ p)⁻¹ * (liftIn t X₀ p * (t * liftIn t X₁ p' * t⁻¹)) *
                (liftIn t X₀ p)⁻¹ := by rw [h2]
            _ = (t * liftIn t X₁ p' * t⁻¹) * (liftIn t X₀ p)⁻¹ := by group }
    have hle : pointParabolic e c₀ ≤ H := pointParabolic_le hK e c₀ fun a b hab hb =>
      ⟨linTv_mem_pointParabolic e hab hb, hstep1 hab hb⟩
    exact fun p hp => (hle hp).2
  rintro _ ⟨x₁, hx₁, rfl⟩
  rw [mem_centralizer_iff]
  intro x₀ hx₀
  have e₀ := liftIn_eq hA₀ hAA₀ hx₀ rfl
  have e₁ := liftIn_eq hA₁ hAA₁ hx₁ rfl
  have h := hstep2 _ (hδ₀ x₀ hx₀) _ (hδ₁ x₁ hx₁)
  rw [e₀, e₁] at h
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem swapLabel_of_moduleData (hset : SeitzSetting G L) (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c₀ c₁ : Fin n} (hc : c₀ ≠ c₁) {W₀ X₀ W₁ X₁ : Subgroup G}
    (h₀ : LinearTwoSwapModuleData e t c₀ W₀ X₀)
    (h₁ : LinearTwoSwapModuleData (e.trans (LinearFlag.dualAut n K)) t c₁ W₁ X₁)
    (hU₀ : ∀ E : Subgroup G, E ≤ seitzRadX (modelToG e (pointRadical (K := K) c₀)) t →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E = Nat.card (modelToG e (pointRadical (K := K) c₀)) *
        Nat.card (modelToG e (pointRadical (K := K) c₀)) → E = W₀)
    (hU₁ : ∀ E : Subgroup G, E ≤ seitzRadX
        (modelToG (e.trans (LinearFlag.dualAut n K)) (pointRadical (K := K) c₁)) t →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E = Nat.card (modelToG (e.trans (LinearFlag.dualAut n K))
          (pointRadical (K := K) c₁)) *
        Nat.card (modelToG (e.trans (LinearFlag.dualAut n K)) (pointRadical (K := K) c₁)) →
        E = W₁) :
    X₁ ≤ centralizer (X₀ : Set G) ∨
      X₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (X₀ : Set G) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  set e' := e.trans (LinearFlag.dualAut n K) with he'
  have hδδ : LinearFlag.dualAut n K * LinearFlag.dualAut n K = 1 :=
    (LinearFlag.standard_automorphism_transport (K := K) (n := n)).2.2.2.1
  have hee : e'.trans (LinearFlag.dualAut n K) = e := by
    ext x
    have h1 := congrArg (fun φ : MulAut (LinearFlag.projectiveSL n K) => φ (e x)) hδδ
    simp only [MulAut.mul_apply, MulAut.one_apply] at h1
    simp only [he', MulEquiv.trans_apply, h1]
  have h₀' : LinearTwoSwapModuleData (e'.trans (LinearFlag.dualAut n K)) t c₀ W₀ X₀ := by
    rw [hee]; exact h₀
  obtain ⟨hA₀, hAA₀, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e htt htC h₀
  obtain ⟨hA₁, hAA₁, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e' htt htC h₁
  obtain ⟨-, -, hex₀⟩ := swapModuleData_lift hset (by omega) hK e ht hKt h₀
  have hI := lift_eq_or_of_radical hset (by omega) hK e' ht hKt hc h₀' h₁ hU₁
  have hII := lift_eq_or_of_radical hset (by omega) hK e ht hKt hc.symm h₁ h₀ hU₀
  have hzV : linTv e hc ∈ modelToG e (pointRadical (K := K) c₀) := linTv_mem_pointRadical e hc
  have hzV' : linTv e hc ∈ modelToG e' (pointRadical (K := K) c₁) := by
    have h := linTv_mem_pointRadical e' hc.symm
    rwa [linTv_trans_dualAut] at h
  have hz1 : linTv e hc ≠ 1 := linTv_ne_one e hc
  have hzP : linTv e hc ∈ pointParabolic e c₀ := mem_sup_left hzV
  have hfix : liftIn t X₀ (linTv e hc) = t * liftIn t X₀ (linTv e hc) * t⁻¹ → False := by
    intro h
    obtain ⟨h1, h2⟩ := liftIn_spec (hex₀ _ hzP)
    have hmem : liftIn t X₀ (linTv e hc) ∈ X₀ ⊓ X₀.map (MulAut.conj t).toMonoidHom :=
      mem_inf.2 ⟨h1, h.symm ▸ conj_mem_map_conj_t h1⟩
    rw [hAA₀, mem_bot] at hmem
    apply hz1
    rw [← h2, hmem]
    group
  rcases hI with hI | hI <;> rcases hII with hII | hII
  ·
    right
    exact conj_le_centralizer_of_agree hset hn hK e ht hKt hc h₀ h₁
      (fun v hv => (hII v hv).symm) hI
  · exfalso
    apply hfix
    have h := hII _ hzV
    rwa [hI _ hzV'] at h
  · exfalso
    apply hfix
    have h := hII _ hzV
    rwa [hI _ hzV'] at h
  ·
    left
    have h₁' := h₁.map_conj htt
    have hlift : ∀ v ∈ modelToG e' (pointRadical (K := K) c₁) ⊔
        modelToG e' (blockSL (K := K) ({c₁}ᶜ : Finset (Fin n))),
        liftIn t (X₁.map (MulAut.conj t).toMonoidHom) v = t * liftIn t X₁ v * t⁻¹ := by
      obtain ⟨-, -, hex₁⟩ := swapModuleData_lift hset (by omega) hK e' ht hKt h₁
      exact fun v hv => liftIn_map_conj_t htt hA₁ hAA₁ (hex₁ v hv)
    have hP₁V : modelToG e (pointRadical (K := K) c₀) ≤ pointParabolic e' c₁ :=
      modelToG_pointRadical_le hK e c₀ fun _ hcj => linTv_mem_pointParabolic_dual e hcj hc
    have hV : ∀ v ∈ modelToG e (pointRadical (K := K) c₀),
        liftIn t (X₁.map (MulAut.conj t).toMonoidHom) v = liftIn t X₀ v := by
      intro v hv
      rw [hlift v (hP₁V hv), hII v hv]
    have hV' : ∀ v ∈ modelToG e' (pointRadical (K := K) c₁),
        liftIn t (X₁.map (MulAut.conj t).toMonoidHom) v = liftIn t X₀ v := by
      intro v hv
      rw [hlift v (mem_sup_left hv), hI v hv]
      calc t * (t * liftIn t X₀ v * t⁻¹) * t⁻¹ = (t * t) * liftIn t X₀ v * (t * t)⁻¹ := by group
        _ = liftIn t X₀ v := by rw [htt]; group
    have h := conj_le_centralizer_of_agree hset hn hK e ht hKt hc h₀ h₁' hV hV'
    rwa [map_conj_map_conj_eq_of_mul_self htt] at h

end Label

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
  [CharP K 2]

theorem mem_normalizer_sup_zpowers_of_conj {R : Subgroup G} {t x : G}
    (hxR : x ∈ centralizer (R : Set G)) (hxt : x * t * x⁻¹ ∈ R ⊔ zpowers t) :
    x ∈ normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
  have hle : (R ⊔ zpowers t).map (MulAut.conj x).toMonoidHom ≤ R ⊔ zpowers t := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← mem_centralizer_iff.1 hxR v hv, mul_inv_cancel_right]
      exact mem_sup_left hv
    · rw [zpowers_le]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxt
  have heq : (R ⊔ zpowers t).map (MulAut.conj x).toMonoidHom = R ⊔ zpowers t := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hle ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨h', hh', he⟩ := hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
    have : h' = h := mul_left_cancel (mul_right_cancel he)
    rwa [← this]

theorem wOne_facts (hset : SeitzSetting G L) (hn : 4 ≤ n) (hK : Nat.card K = 2)
    (f : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {c : Fin n}
    {W X : Subgroup G} (h : LinearTwoSwapModuleData f t c W X) :
    Nat.card (modelToG f (pointRadical (K := K) c)) = 2 ^ (n - 1) ∧
      (∀ v ∈ modelToG f (pointRadical (K := K) c), v * v = 1) ∧
      (∀ v ∈ modelToG f (pointRadical (K := K) c), v * t = t * v) ∧
      t ∉ modelToG f (pointRadical (K := K) c) ∧
      centralizer (modelToG f (pointRadical (K := K) c) : Set G) ⊓
          centralizer ({t} : Set G) ≤ modelToG f (pointRadical (K := K) c) ⊔ zpowers t ∧
      W ≤ seitzRadX (modelToG f (pointRadical (K := K) c)) t ∧
      (∀ v ∈ modelToG f (pointRadical (K := K) c),
        ∃ x ∈ seitzRadX (modelToG f (pointRadical (K := K) c)) t, t * x * t⁻¹ * x⁻¹ = v) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨-, hb, -⟩ := swapModuleData_lift hset hn hK f ht hKt h
  obtain ⟨hW2, hWc, hWt, htW, -, -, -, -, -, -, -, -⟩ := h
  set R := modelToG f (pointRadical (K := K) c) with hR
  have hRc : Nat.card R = 2 ^ (n - 1) := by
    rw [← hWt]; exact card_inf_centralizer_eq_of_pointRadical hK f hWt
  have hRW : R ≤ W := by rw [← hWt]; exact inf_le_left
  have hRt : R ≤ centralizer ({t} : Set G) := by rw [← hWt]; exact inf_le_right
  have hWab : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW2 hv hw
  have htR : ∀ v ∈ R, v * t = t * v := fun v hv => mem_centralizer_singleton_iff.1 (hRt hv)
  have hWX : W ≤ seitzRadX R t := by
    intro w hw
    refine mem_seitzRadX.2 ⟨mem_centralizer_iff.2 fun v hv => hWab v (hRW hv) w hw, ?_⟩
    apply mem_normalizer_sup_zpowers_of_conj
    · exact mem_centralizer_iff.2 fun v hv => hWab v (hRW hv) w hw
    · have htw : t * w * t⁻¹ ∈ W := (mem_normalizer_iff.1 htW w).1 hw
      have hd : w * (t * w * t⁻¹) ∈ R := by
        rw [← hWt]
        refine mem_inf.2 ⟨mul_mem hw htw, mem_centralizer_singleton_iff.2 ?_⟩
        have hc := hWab w hw _ htw
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
        calc w * (t * w * t⁻¹) * t = w * t * w := by group
          _ = w * t⁻¹ * w := by rw [htinv]
          _ = (t * t) * w * t⁻¹ * w := by rw [htt, one_mul]
          _ = t * ((t * w * t⁻¹) * w) := by group
          _ = t * (w * (t * w * t⁻¹)) := by rw [hc]
      have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW2 w hw)
      have : w * t * w⁻¹ = (w * (t * w * t⁻¹)) * t := by rw [hwinv]; group
      rw [this]
      exact mul_mem (mem_sup_left hd) (mem_sup_right (mem_zpowers t))
  refine ⟨hRc, fun v hv => hW2 v (hRW hv), htR, fun htR' => ?_,
    centralizer_pointRadical_inf_le hset (by omega) hK f ht hKt c, hWX, fun v hv => ?_⟩
  ·
    have hle : W ≤ centralizer ({t} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.2 (hWab w hw t (hRW htR'))
    have h1 : Nat.card W = Nat.card R := by rw [← hWt, inf_eq_left.2 hle]
    rw [hWc, hRc] at h1
    have h2 : n - 1 < 2 * (n - 1) := by omega
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h2
    omega
  · obtain ⟨x, hx, hxv⟩ := hb v hv
    have hxW := (mem_inf.1 hx).2
    refine ⟨x, hWX hxW, ?_⟩
    have htx : t * x * t⁻¹ ∈ W := (mem_normalizer_iff.1 htW x).1 hxW
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hW2 x hxW)
    rw [hxinv, ← hxv]
    exact hWab _ htx x hxW

theorem eq_wOne_of_card_five (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (f : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {c : Fin 5}
    {W X : Subgroup G} (h : LinearTwoSwapModuleData f t c W X) :
    ∀ E : Subgroup G, E ≤ seitzRadX (modelToG f (pointRadical (K := K) c)) t →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E = Nat.card (modelToG f (pointRadical (K := K) c)) *
        Nat.card (modelToG f (pointRadical (K := K) c)) → E = W := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hRc, hR2, htR, htnR, hker, hWX, hsurj⟩ := wOne_facts hset (by norm_num) hK f ht hKt h
  obtain ⟨hW2, hWc, -⟩ := h
  intro E hE hEc hEcard
  rw [hRc] at hEcard
  exact eq_of_le_seitzRadX_of_card hRc hR2 htt htR htnR hker hsurj hE hWX hEc
    (fun a ha b hb => mul_comm_of_forall_mul_self_eq_one hW2 ha hb)
    (by rw [hEcard]; norm_num) (by rw [hWc])

theorem eq_wOne_of_card_six (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (f : L ≃* LinearFlag.projectiveSL 6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {c : Fin 6}
    {W X : Subgroup G} (h : LinearTwoSwapModuleData f t c W X) :
    ∀ E : Subgroup G, E ≤ seitzRadX (modelToG f (pointRadical (K := K) c)) t →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E = Nat.card (modelToG f (pointRadical (K := K) c)) *
        Nat.card (modelToG f (pointRadical (K := K) c)) → E = W := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hRc, hR2, htR, htnR, hker, hWX, hsurj⟩ := wOne_facts hset (by norm_num) hK f ht hKt h
  obtain ⟨hW2, hWc, -⟩ := h
  intro E hE hEc hEcard
  rw [hRc] at hEcard
  exact eq_of_le_seitzRadX_of_card_five hRc hR2 htt htR htnR hker hsurj hE hWX hEc
    (fun a ha b hb => mul_comm_of_forall_mul_self_eq_one hW2 ha hb)
    (by rw [hEcard]; norm_num) (by rw [hWc])

end Unique

theorem linearTwoSwapLabelDualAtInput_five : LinearTwoSwapLabelDualAtInput 5 := by
  intro G _ _ L hset K _ _ hK t ht hKt e c₀ c₁ W₀ X₀ W₁ X₁ hc h₀ h₁ _ _
  exact swapLabel_of_moduleData hset le_rfl hK e ht hKt hc h₀ h₁
    (eq_wOne_of_card_five hset hK e ht hKt h₀) (eq_wOne_of_card_five hset hK _ ht hKt h₁)

theorem linearTwoSwapLabelDualAtInput_six : LinearTwoSwapLabelDualAtInput 6 := by
  intro G _ _ L hset K _ _ hK t ht hKt e c₀ c₁ W₀ X₀ W₁ X₁ hc h₀ h₁ _ _
  exact swapLabel_of_moduleData hset (by norm_num) hK e ht hKt hc h₀ h₁
    (eq_wOne_of_card_six hset hK e ht hKt h₀) (eq_wOne_of_card_six hset hK _ ht hKt h₁)

end CFSG.SeitzReduction.LinearPilot
