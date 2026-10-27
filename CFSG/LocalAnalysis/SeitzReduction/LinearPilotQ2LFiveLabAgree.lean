module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveLabSign

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Agree

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
  [CharP K 2]

theorem liftIn_eq_or_mul_of_levi (hset : SeitzSetting G L) (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c₀ c₁ : Fin n} (hc : c₀ ≠ c₁) {W₀ X₀ W₁ X₁ : Subgroup G}
    (h₀ : LinearTwoSwapModuleData e t c₀ W₀ X₀)
    (h₁ : LinearTwoSwapModuleData (e.trans (LinearFlag.dualAut n K)) t c₁ W₁ X₁)
    (hV : ∀ v ∈ modelToG e (pointRadical (K := K) c₀), liftIn t X₁ v = liftIn t X₀ v)
    (hV' : ∀ v ∈ modelToG (e.trans (LinearFlag.dualAut n K)) (pointRadical (K := K) c₁),
      liftIn t X₁ v = liftIn t X₀ v)
    {i j : Fin n} (hij : i ≠ j) (hi₀ : i ≠ c₀) (hi₁ : i ≠ c₁) (hj₀ : j ≠ c₀) (hj₁ : j ≠ c₁) :
    liftIn t X₁ (linTv e hij) = liftIn t X₀ (linTv e hij) ∨
      liftIn t X₁ (linTv e hij) = liftIn t X₀ (linTv e hij) * linTv e hc := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hLt : ∀ y ∈ L, y * t = t * y := fun y hy => mem_centralizer_iff.1 htC y hy
  set e' := e.trans (LinearFlag.dualAut n K) with he'
  obtain ⟨hA₀, hAA₀, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e htt htC h₀
  obtain ⟨hA₁, hAA₁, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e' htt htC h₁
  obtain ⟨-, hb₀, hex₀⟩ := swapModuleData_lift hset (by omega) hK e ht hKt h₀
  obtain ⟨-, -, hex₁⟩ := swapModuleData_lift hset (by omega) hK e' ht hKt h₁
  obtain ⟨hW2₀, -, hWt₀, htW₀, -, -, -, -, -, -, -, -⟩ := h₀
  set V := modelToG e (pointRadical (K := K) c₀) with hVdef
  set V' := modelToG e' (pointRadical (K := K) c₁) with hV'def
  have hVP₀ : V ≤ pointParabolic e c₀ := le_sup_left
  have hVP₁ : V ≤ pointParabolic e' c₁ :=
    modelToG_pointRadical_le hK e c₀ fun _ hcj => linTv_mem_pointParabolic_dual e hcj hc
  have hV'P₁ : V' ≤ pointParabolic e' c₁ := le_sup_left
  have hV'P₀ : V' ≤ pointParabolic e c₀ :=
    modelToG_pointRadical_le hK e' c₁ fun _ hcj => by
      rw [linTv_trans_dualAut]
      exact linTv_mem_pointParabolic e hcj.symm hc.symm
  set d := linTv e hij with hd
  have hd₀ : d ∈ pointParabolic e c₀ := linTv_mem_pointParabolic e hij hj₀
  have hd₁ : d ∈ pointParabolic e' c₁ := linTv_mem_pointParabolic_dual e hij hi₁
  have hdL : d ∈ L := (e.symm (LinearFlag.proj n K
    (Matrix.SpecialLinearGroup.transvection hij (1 : K)))).2
  have hd2 : d * d = 1 := linTv_mul_self e hij
  have hdV : ∀ v ∈ V, d * v * d⁻¹ ∈ V := fun v hv =>
    (mem_normalizer_iff.1 (modelToG_le_normalizer e (blockSL_compl_le_normalizer_pointRadical c₀)
      (linTv_mem e hij hi₀ hj₀)) v).1 hv
  have hdV' : ∀ v ∈ V', d * v * d⁻¹ ∈ V' := by
    intro v hv
    have hd' : d = linTv e' hij.symm := by rw [linTv_trans_dualAut]
    have hmem : d ∈ modelToG e' (blockSL (K := K) ({c₁}ᶜ : Finset (Fin n))) := by
      rw [hd']; exact linTv_mem e' hij.symm hj₁ hi₁
    exact (mem_normalizer_iff.1 (modelToG_le_normalizer e'
      (blockSL_compl_le_normalizer_pointRadical c₁) hmem) v).1 hv
  obtain ⟨a₀, ha₀X, ha₀d⟩ := hex₀ d hd₀
  obtain ⟨a₁, ha₁X, ha₁d⟩ := hex₁ d hd₁
  have hα := liftIn_eq hA₀ hAA₀ ha₀X ha₀d
  have hβ := liftIn_eq hA₁ hAA₁ ha₁X ha₁d
  rw [hα, hβ]
  have hdt := hLt d hdL
  have hconj₀ : ∀ y ∈ pointParabolic e c₀,
      liftIn t X₀ (d * y * d⁻¹) = a₀ * liftIn t X₀ y * a₀⁻¹ := by
    intro y hy
    have h1 := liftIn_conj hA₀ hAA₀ ha₀X (by rw [ha₀d]; exact hdt) (hex₀ y hy)
    rw [ha₀d] at h1
    rw [h1, ← ha₀d, diag_conj_eq_conj hA₀ ha₀X (liftIn_spec (hex₀ y hy)).1]
  have hconj₁ : ∀ y ∈ pointParabolic e' c₁,
      liftIn t X₁ (d * y * d⁻¹) = a₁ * liftIn t X₁ y * a₁⁻¹ := by
    intro y hy
    have h1 := liftIn_conj hA₁ hAA₁ ha₁X (by rw [ha₁d]; exact hdt) (hex₁ y hy)
    rw [ha₁d] at h1
    rw [h1, ← ha₁d, diag_conj_eq_conj hA₁ ha₁X (liftIn_spec (hex₁ y hy)).1]
  have ha₀2 : a₀ * a₀ = 1 := eq_of_mem_of_diag_eq hA₀ hAA₀ (mul_mem ha₀X ha₀X) (one_mem X₀)
    (by rw [swapDiag_mul hA₀ ha₀X ha₀X, ha₀d, hd2]; group)
  have ha₁2 : a₁ * a₁ = 1 := eq_of_mem_of_diag_eq hA₁ hAA₁ (mul_mem ha₁X ha₁X) (one_mem X₁)
    (by rw [swapDiag_mul hA₁ ha₁X ha₁X, ha₁d, hd2]; group)
  have hgt : a₁⁻¹ * a₀ ∈ centralizer ({t} : Set G) :=
    inv_mul_mem_centralizer_of_diag_eq ha₀2 ha₁2 (conj_mul_comm_of_mem hA₀ ha₀X ha₀X).symm
      (conj_mul_comm_of_mem hA₁ ha₁X ha₁X).symm (ha₀d.trans ha₁d.symm)
  have hgt' : (a₁⁻¹ * a₀) * t = t * (a₁⁻¹ * a₀) := mem_centralizer_singleton_iff.1 hgt
  have hagree : ∀ y, (y ∈ V ∨ y ∈ V') → liftIn t X₁ y = liftIn t X₀ y := fun y h =>
    h.elim (hV y) (hV' y)
  have hP₀ : ∀ y, (y ∈ V ∨ y ∈ V') → y ∈ pointParabolic e c₀ := fun y h =>
    h.elim (fun h => hVP₀ h) (fun h => hV'P₀ h)
  have hP₁ : ∀ y, (y ∈ V ∨ y ∈ V') → y ∈ pointParabolic e' c₁ := fun y h =>
    h.elim (fun h => hVP₁ h) (fun h => hV'P₁ h)
  have hgl : ∀ y, (y ∈ V ∨ y ∈ V') →
      (a₁⁻¹ * a₀) * liftIn t X₀ y = liftIn t X₀ y * (a₁⁻¹ * a₀) := by
    intro y hy
    have hdy : d * y * d⁻¹ ∈ V ∨ d * y * d⁻¹ ∈ V' :=
      hy.elim (fun h => Or.inl (hdV y h)) (fun h => Or.inr (hdV' y h))
    have h1 := hconj₀ y (hP₀ y hy)
    have h2 := hconj₁ y (hP₁ y hy)
    rw [hagree _ hdy, hagree y hy] at h2
    have h3 : a₀ * liftIn t X₀ y * a₀⁻¹ = a₁ * liftIn t X₀ y * a₁⁻¹ := h1.symm.trans h2
    calc (a₁⁻¹ * a₀) * liftIn t X₀ y = a₁⁻¹ * (a₀ * liftIn t X₀ y * a₀⁻¹) * a₀ := by group
      _ = a₁⁻¹ * (a₁ * liftIn t X₀ y * a₁⁻¹) * a₀ := by rw [h3]
      _ = liftIn t X₀ y * (a₁⁻¹ * a₀) := by group
  have hgy : ∀ y, (y ∈ V ∨ y ∈ V') → (a₁⁻¹ * a₀) * y = y * (a₁⁻¹ * a₀) := by
    intro y hy
    obtain ⟨-, hly⟩ := liftIn_spec (hex₀ y (hP₀ y hy))
    set l := liftIn t X₀ y with hl
    have h1 := hgl y hy
    have hgti : (a₁⁻¹ * a₀) * t⁻¹ = t⁻¹ * (a₁⁻¹ * a₀) := by
      calc (a₁⁻¹ * a₀) * t⁻¹ = t⁻¹ * (t * (a₁⁻¹ * a₀)) * t⁻¹ := by group
        _ = t⁻¹ * ((a₁⁻¹ * a₀) * t) * t⁻¹ := by rw [hgt']
        _ = t⁻¹ * (a₁⁻¹ * a₀) := by group
    have h2 : (a₁⁻¹ * a₀) * (t * l * t⁻¹) = (t * l * t⁻¹) * (a₁⁻¹ * a₀) := by
      calc (a₁⁻¹ * a₀) * (t * l * t⁻¹) = ((a₁⁻¹ * a₀) * t) * l * t⁻¹ := by group
        _ = t * ((a₁⁻¹ * a₀) * l) * t⁻¹ := by rw [hgt']; group
        _ = t * (l * (a₁⁻¹ * a₀)) * t⁻¹ := by rw [h1]
        _ = t * l * ((a₁⁻¹ * a₀) * t⁻¹) := by group
        _ = (t * l * t⁻¹) * (a₁⁻¹ * a₀) := by rw [hgti]; group
    rw [← hly]
    calc (a₁⁻¹ * a₀) * (l * (t * l * t⁻¹)) = ((a₁⁻¹ * a₀) * l) * (t * l * t⁻¹) := by group
      _ = (l * (a₁⁻¹ * a₀)) * (t * l * t⁻¹) := by rw [h1]
      _ = l * ((a₁⁻¹ * a₀) * (t * l * t⁻¹)) := by group
      _ = l * ((t * l * t⁻¹) * (a₁⁻¹ * a₀)) := by rw [h2]
      _ = l * (t * l * t⁻¹) * (a₁⁻¹ * a₀) := by group
  have hVt : ∀ v ∈ V, v * t = t * v := fun v hv => hLt v (modelToG_le e _ hv)
  have hgCV : a₁⁻¹ * a₀ ∈ centralizer (V : Set G) :=
    mem_centralizer_iff.2 fun v hv => (hgy v (Or.inl hv)).symm
  have hgsup := centralizer_pointRadical_inf_le hset (by omega) hK e ht hKt c₀ ⟨hgCV, hgt⟩
  have htN : t ∈ normalizer (V : Set G) := mem_normalizer_of_forall_commute hVt
  have hz1 : linTv e hc ≠ 1 := linTv_ne_one e hc
  have hzV : linTv e hc ∈ V := linTv_mem_pointRadical e hc
  rcases (mem_sup_zpowers_iff htt htN).1 hgsup with hgV | hgtV
  ·
    obtain ⟨r, hrc, hreq, hr⟩ := exists_pointRadElem_of_mem hK e c₁ hgV
    have hr' : ∀ j', j' ≠ c₁ → r j' = 0 := by
      intro j' hj'
      by_cases hj'₀ : j' = c₀
      · rw [hj'₀]; exact hrc
      refine hr j' hj'₀ hj' ?_
      have hmem : linTv e hj' ∈ V' := by
        have := linTv_mem_pointRadical e' (Ne.symm hj')
        rwa [linTv_trans_dualAut] at this
      exact hgy _ (Or.inr hmem)
    rcases eq_one_or_of_pointRadElem_one hK e hc hr' with h1 | h1 <;> rw [← hreq] at h1
    · left
      exact inv_mul_eq_one.1 h1
    · right
      have hz2 : linTv e hc * linTv e hc = 1 := linTv_mul_self e hc
      calc a₁ = a₀ * (a₁⁻¹ * a₀)⁻¹ := by group
        _ = a₀ * (linTv e hc)⁻¹ := by rw [h1]
        _ = a₀ * linTv e hc := by rw [inv_eq_of_mul_eq_one_right hz2]
  ·
    exfalso
    set v₀ := (a₁⁻¹ * a₀) * t with hv₀
    obtain ⟨x, hx, hxz⟩ := hb₀ _ hzV
    have hxl : liftIn t X₀ (linTv e hc) = x := liftIn_eq hA₀ hAA₀ (mem_inf.1 hx).1 hxz
    have hxW : x ∈ W₀ := (mem_inf.1 hx).2
    have hv₀W : v₀ ∈ W₀ := by rw [← hWt₀] at hgtV; exact (mem_inf.1 hgtV).1
    have htxW : t * x * t⁻¹ ∈ W₀ := (mem_normalizer_iff.1 htW₀ x).1 hxW
    have hcomm : v₀ * (t * x * t⁻¹) = (t * x * t⁻¹) * v₀ :=
      mul_comm_of_forall_mul_self_eq_one hW2₀ hv₀W htxW
    have h1 := hgl _ (Or.inl hzV)
    rw [hxl] at h1
    have hg : a₁⁻¹ * a₀ = v₀ * t := by rw [hv₀, mul_assoc, htt, mul_one]
    rw [hg] at h1
    have h2 : t * x * t⁻¹ = x := by
      have h3 : v₀ * (t * x * t⁻¹) = x * v₀ := by
        calc v₀ * (t * x * t⁻¹) = v₀ * t * x * t⁻¹ := by group
          _ = x * (v₀ * t) * t⁻¹ := by rw [h1]
          _ = x * v₀ := by group
      rw [hcomm] at h3
      exact mul_right_cancel h3
    have hmem : x ∈ X₀ ⊓ X₀.map (MulAut.conj t).toMonoidHom :=
      mem_inf.2 ⟨(mem_inf.1 hx).1, h2 ▸ conj_mem_map_conj_t (mem_inf.1 hx).1⟩
    rw [hAA₀, mem_bot] at hmem
    apply hz1
    rw [← hxz, hmem]
    group

theorem mul_four_eq_of_commute {G : Type*} [Group G] {a b u v : G} (hua : u * a = a * u)
    (hub : u * b = b * u) (hva : v * a = a * v) (hvb : v * b = b * v) (huv : u * v = v * u)
    (hu : u * u = 1) (hv : v * v = 1) : a * u * (b * v) * (a * u) * (b * v) = a * b * a * b := by
  have e1 : a * u * (b * v) = a * b * (u * v) := by
    calc a * u * (b * v) = a * (u * b) * v := by group
      _ = a * (b * u) * v := by rw [hub]
      _ = a * b * (u * v) := by group
  have hwa : u * v * a = a * (u * v) := by
    calc u * v * a = u * (v * a) := by group
      _ = u * (a * v) := by rw [hva]
      _ = (u * a) * v := by group
      _ = (a * u) * v := by rw [hua]
      _ = a * (u * v) := by group
  have hwb : u * v * b = b * (u * v) := by
    calc u * v * b = u * (v * b) := by group
      _ = u * (b * v) := by rw [hvb]
      _ = (u * b) * v := by group
      _ = (b * u) * v := by rw [hub]
      _ = b * (u * v) := by group
  have hww : u * v * (u * v) = 1 := by
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu, hv, one_mul]
  calc a * u * (b * v) * (a * u) * (b * v) = (a * b * (u * v)) * (a * b * (u * v)) := by
        rw [← e1]; group
    _ = a * b * ((u * v) * a) * b * (u * v) := by group
    _ = a * b * (a * (u * v)) * b * (u * v) := by rw [hwa]
    _ = a * b * a * ((u * v) * b) * (u * v) := by group
    _ = a * b * a * (b * (u * v)) * (u * v) := by rw [hwb]
    _ = a * b * a * b * (u * v * (u * v)) := by group
    _ = a * b * a * b := by rw [hww, mul_one]

theorem liftIn_eq_of_levi (hset : SeitzSetting G L) (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c₀ c₁ : Fin n} (hc : c₀ ≠ c₁) {W₀ X₀ W₁ X₁ : Subgroup G}
    (h₀ : LinearTwoSwapModuleData e t c₀ W₀ X₀)
    (h₁ : LinearTwoSwapModuleData (e.trans (LinearFlag.dualAut n K)) t c₁ W₁ X₁)
    (hV : ∀ v ∈ modelToG e (pointRadical (K := K) c₀), liftIn t X₁ v = liftIn t X₀ v)
    (hV' : ∀ v ∈ modelToG (e.trans (LinearFlag.dualAut n K)) (pointRadical (K := K) c₁),
      liftIn t X₁ v = liftIn t X₀ v)
    {i j : Fin n} (hij : i ≠ j) (hi₀ : i ≠ c₀) (hi₁ : i ≠ c₁) (hj₀ : j ≠ c₀) (hj₁ : j ≠ c₁) :
    liftIn t X₁ (linTv e hij) = liftIn t X₀ (linTv e hij) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  set e' := e.trans (LinearFlag.dualAut n K) with he'
  obtain ⟨hA₀, hAA₀, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e htt htC h₀
  obtain ⟨hA₁, hAA₁, -, -⟩ := swapModuleData_split (K := K) (by omega) hK e' htt htC h₁
  obtain ⟨-, -, hex₀⟩ := swapModuleData_lift hset (by omega) hK e ht hKt h₀
  obtain ⟨-, -, hex₁⟩ := swapModuleData_lift hset (by omega) hK e' ht hKt h₁
  obtain ⟨k, hk⟩ := exists_not_mem_of_card_lt_fin ({c₀, c₁, i, j} : Finset (Fin n))
    ((Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hk₀, hk₁, hki, hkj⟩ := hk
  have hik : i ≠ k := Ne.symm hki
  have hcomm := linTv_commutator e hik hkj hij
  rw [inv_eq_of_mul_eq_one_right (linTv_mul_self e hik),
    inv_eq_of_mul_eq_one_right (linTv_mul_self e hkj)] at hcomm
  rw [← hcomm]
  have hm₀ : ∀ {a b : Fin n} (hab : a ≠ b), b ≠ c₀ → linTv e hab ∈ pointParabolic e c₀ :=
    fun hab hb => linTv_mem_pointParabolic e hab hb
  have hm₁ : ∀ {a b : Fin n} (hab : a ≠ b), a ≠ c₁ → linTv e hab ∈ pointParabolic e' c₁ :=
    fun hab ha => linTv_mem_pointParabolic_dual e hab ha
  set d₁ := linTv e hik
  set d₂ := linTv e hkj
  have hd₁₀ := hm₀ hik hk₀
  have hd₂₀ := hm₀ hkj hj₀
  have hd₁₁ := hm₁ hik hi₁
  have hd₂₁ := hm₁ hkj hk₁
  have hL₀ : liftIn t X₀ (d₁ * d₂ * d₁ * d₂) =
      liftIn t X₀ d₁ * liftIn t X₀ d₂ * liftIn t X₀ d₁ * liftIn t X₀ d₂ := by
    rw [liftIn_mul hA₀ hAA₀ (hex₀ _ (mul_mem (mul_mem hd₁₀ hd₂₀) hd₁₀)) (hex₀ _ hd₂₀),
      liftIn_mul hA₀ hAA₀ (hex₀ _ (mul_mem hd₁₀ hd₂₀)) (hex₀ _ hd₁₀),
      liftIn_mul hA₀ hAA₀ (hex₀ _ hd₁₀) (hex₀ _ hd₂₀)]
  have hL₁ : liftIn t X₁ (d₁ * d₂ * d₁ * d₂) =
      liftIn t X₁ d₁ * liftIn t X₁ d₂ * liftIn t X₁ d₁ * liftIn t X₁ d₂ := by
    rw [liftIn_mul hA₁ hAA₁ (hex₁ _ (mul_mem (mul_mem hd₁₁ hd₂₁) hd₁₁)) (hex₁ _ hd₂₁),
      liftIn_mul hA₁ hAA₁ (hex₁ _ (mul_mem hd₁₁ hd₂₁)) (hex₁ _ hd₁₁),
      liftIn_mul hA₁ hAA₁ (hex₁ _ hd₁₁) (hex₁ _ hd₂₁)]
  rw [hL₀, hL₁]
  set z := linTv e hc with hz
  have hzP₀ : z ∈ pointParabolic e c₀ := hm₀ hc hc.symm
  have hz2 : z * z = 1 := linTv_mul_self e hc
  have hzc : ∀ {a b : Fin n} (hab : a ≠ b), a ≠ c₀ → a ≠ c₁ → b ≠ c₀ → b ≠ c₁ →
      z * liftIn t X₀ (linTv e hab) = liftIn t X₀ (linTv e hab) * z := by
    intro a b hab ha₀ ha₁ hb₀ hb₁
    have hdz : linTv e hab * z = z * linTv e hab :=
      linTv_commute e hab hc hb₀ (Ne.symm ha₁)
    have hdP := hm₀ hab hb₀
    have h1 : liftIn t X₀ (linTv e hab) * liftIn t X₀ z =
        liftIn t X₀ z * liftIn t X₀ (linTv e hab) := by
      rw [← liftIn_mul hA₀ hAA₀ (hex₀ _ hdP) (hex₀ _ hzP₀),
        ← liftIn_mul hA₀ hAA₀ (hex₀ _ hzP₀) (hex₀ _ hdP), hdz]
    have h2 := conj_mul_comm_of_mem hA₀ (liftIn_spec (hex₀ _ hzP₀)).1
      (liftIn_spec (hex₀ _ hdP)).1
    obtain ⟨-, hzl⟩ := liftIn_spec (hex₀ _ hzP₀)
    rw [← hzl]
    calc liftIn t X₀ z * (t * liftIn t X₀ z * t⁻¹) * liftIn t X₀ (linTv e hab)
        = liftIn t X₀ z * ((t * liftIn t X₀ z * t⁻¹) * liftIn t X₀ (linTv e hab)) := by group
      _ = liftIn t X₀ z * (liftIn t X₀ (linTv e hab) * (t * liftIn t X₀ z * t⁻¹)) := by rw [h2]
      _ = (liftIn t X₀ z * liftIn t X₀ (linTv e hab)) * (t * liftIn t X₀ z * t⁻¹) := by group
      _ = (liftIn t X₀ (linTv e hab) * liftIn t X₀ z) * (t * liftIn t X₀ z * t⁻¹) := by rw [h1]
      _ = liftIn t X₀ (linTv e hab) * (liftIn t X₀ z * (t * liftIn t X₀ z * t⁻¹)) := by group
  have hz₁ := hzc hik hi₀ hi₁ hk₀ hk₁
  have hz₂ := hzc hkj hk₀ hk₁ hj₀ hj₁
  have h1z : (1 : G) * z = z * 1 := by group
  rcases liftIn_eq_or_mul_of_levi hset hn hK e ht hKt hc h₀ h₁ hV hV' hik hi₀ hi₁ hk₀ hk₁
    with h1 | h1 <;>
    rcases liftIn_eq_or_mul_of_levi hset hn hK e ht hKt hc h₀ h₁ hV hV' hkj hk₀ hk₁ hj₀ hj₁
      with h2 | h2 <;> rw [h1, h2]
  · have := mul_four_eq_of_commute (a := liftIn t X₀ d₁) (b := liftIn t X₀ d₂) (u := 1) (v := z)
      (by group) (by group) hz₁ hz₂ h1z (by group) hz2
    simpa only [mul_one] using this
  · have := mul_four_eq_of_commute (a := liftIn t X₀ d₁) (b := liftIn t X₀ d₂) (u := z) (v := 1)
      hz₁ hz₂ (by group) (by group) h1z.symm hz2 (by group)
    simpa only [mul_one] using this
  · exact mul_four_eq_of_commute hz₁ hz₂ hz₁ hz₂ rfl hz2 hz2

end Agree

end CFSG.SeitzReduction.LinearPilot
