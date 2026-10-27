module

public import CFSG.LocalAnalysis.EvenBN.U4.RootF1Elem
public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutSection

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf exists_mem_ne_ne)
open scoped commutatorElement

section ModelFacts

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem miyamotoXGL_mem_A2_of [CharP K 2] (a c : K) :
    miyamotoXGL h a 0 c (h.bar a * c) ∈ miyamotoA2 h := by
  refine (miyamotoXGL_mem_A2 h).2 ⟨rfl, ?_⟩
  simp only [map_mul, h.bar_bar]
  linear_combination (h.bar a * c + a * h.bar c) * CharTwo.two_eq_zero (R := K)

theorem exists_miyamotoA2_commutator_ne [CharP K 2] (hf : 2 ≤ f) {g : GL (Fin 4) K}
    (hg : g ∈ miyamotoA2 h) (hgZ : g ∉ miyamotoZ h) : ∃ g₁ ∈ miyamotoA2 h, ∃ g₂ ∈ miyamotoA2 h,
      ⁅g₁, g⁆ ≠ 1 ∧ ⁅g₂, g⁆ ≠ 1 ∧ ⁅g₁, g⁆ ≠ ⁅g₂, g⁆ := by
  obtain ⟨a, c, d, hd, rfl⟩ := (mem_A2 h).1 hg
  have hv : ((a, c) : K × K) ≠ 0 := by
    intro hv
    obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 hv
    exact hgZ ((miyamotoXGL_mem_Z h).2 ⟨rfl, rfl, rfl, (add_bar_eq_zero_iff h).1
      (by simpa using hd)⟩)
  obtain ⟨⟨w₁, w₂⟩, hw⟩ : ∃ w, miyamotoPairing h (a, c) w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (eq_zero_of_miyamotoPairing h hcon)
  obtain ⟨μ, hμ, hμ2⟩ := exists_fixed_unit_sq_ne_one h hf
  have hμ1 : (μ : K) ≠ 1 := fun e => hμ2 (by rw [e, one_pow])
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  have e₁ : ⁅miyamotoXGL h w₁ 0 w₂ (h.bar w₁ * w₂), miyamotoXGL h a 0 c d⁆ =
      miyamotoXGL h 0 0 0 (miyamotoPairing h (a, c) (w₁, w₂)) := by
    rw [miyamotoXGL_commutator_A2_eq_pairing, miyamotoPairing_comm]
  have e₂ : ⁅miyamotoXGL h (μ * w₁) 0 (μ * w₂) (h.bar (μ * w₁) * (μ * w₂)),
      miyamotoXGL h a 0 c d⁆ =
      miyamotoXGL h 0 0 0 ((μ : K) * miyamotoPairing h (a, c) (w₁, w₂)) := by
    rw [miyamotoXGL_commutator_A2_eq_pairing, miyamotoPairing_comm,
      ← miyamotoPairing_smul_right h hμ]
    rfl
  refine ⟨_, miyamotoXGL_mem_A2_of h w₁ w₂, _, miyamotoXGL_mem_A2_of h (μ * w₁) (μ * w₂), ?_,
    ?_, ?_⟩
  · rw [e₁, ← miyamotoXGL_zero h, Ne, miyamotoXGL_inj]
    exact fun e => hw e.2.2.2
  · rw [e₂, ← miyamotoXGL_zero h, Ne, miyamotoXGL_inj]
    exact fun e => mul_ne_zero hμ0 hw e.2.2.2
  · rw [e₁, e₂, Ne, miyamotoXGL_inj]
    intro e
    apply hμ1
    have := e.2.2.2
    exact (mul_eq_right₀ hw).1 this.symm

end ModelFacts

@[expose] noncomputable def miyamotoD2G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
    (Q : Subgroup G) : Subgroup G :=
  CFSG.ABGTheoremB.pCoreIn 2
    (normalizer ((miyamotoEG h L η Q ⊔ miyamotoB2 h L η t : Subgroup G) : Set G))

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem E_comm (hS : Setting h L η t Q T) {e e' : G} (he : e ∈ miyamotoEG h L η Q)
    (he' : e' ∈ miyamotoEG h L η Q) : e * e' = e' * e :=
  hS.F1_comm (hS.E_le_F1 he) (hS.E_le_F1 he')

theorem E_mul_self (hS : Setting h L η t Q T) {e : G} (he : e ∈ miyamotoEG h L η Q) :
    e * e = 1 :=
  hS.F1_mul_self e (hS.E_le_F1 he)

theorem exists_A2G_commutator_ne (hS : Setting h L η t Q T) {a : G}
    (ha : a ∈ miyamotoA2G h L η) (haZ : a ∉ miyamotoZG h L η) :
    ∃ m₁ ∈ miyamotoA2G h L η, ∃ m₂ ∈ miyamotoA2G h L η,
      ⁅m₁, a⁆ ≠ 1 ∧ ⁅m₂, a⁆ ≠ 1 ∧ ⁅m₁, a⁆ ≠ ⁅m₂, a⁆ := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 ha
  have hgZ : (g : GL (Fin 4) K) ∉ miyamotoZ h := fun hgZ =>
    haZ ((symm_mem_miyamotoPull_iff h L η).2 hgZ)
  obtain ⟨g₁, hg₁, g₂, hg₂, h1, h2, h12⟩ := exists_miyamotoA2_commutator_ne h hS.two_le hg hgZ
  have hval : ∀ k : gramSU h (miyamotoJ4 K),
      ⁅((η.symm k : L) : G), ((η.symm g : L) : G)⁆ = ((η.symm ⁅k, g⁆ : L) : G) := fun k => by
    rw [map_commutatorElement]
    exact (map_commutatorElement L.subtype _ _).symm
  have hcoe : ∀ u v : gramSU h (miyamotoJ4 K),
      ((η.symm u : L) : G) = ((η.symm v : L) : G) ↔ (u : GL (Fin 4) K) = v := fun u v =>
    ⟨fun e => congrArg Subtype.val (η.symm.injective (Subtype.ext e)),
      fun e => by rw [Subtype.ext e]⟩
  have hcomm : ∀ k : gramSU h (miyamotoJ4 K), ((⁅k, g⁆ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      ⁅(k : GL (Fin 4) K), (g : GL (Fin 4) K)⁆ :=
    fun k => map_commutatorElement (gramSU h (miyamotoJ4 K)).subtype k g
  have hone : ((η.symm (1 : gramSU h (miyamotoJ4 K)) : L) : G) = 1 := by simp
  set k₁ : gramSU h (miyamotoJ4 K) := ⟨g₁, miyamotoA2_le_gramSU' h hg₁⟩
  set k₂ : gramSU h (miyamotoJ4 K) := ⟨g₂, miyamotoA2_le_gramSU' h hg₂⟩
  refine ⟨_, (symm_mem_miyamotoPull_iff h L η (g := k₁)).2 hg₁, _,
    (symm_mem_miyamotoPull_iff h L η (g := k₂)).2 hg₂, ?_, ?_, ?_⟩
  · rw [hval, ← hone, Ne, hcoe, hcomm]
    exact h1
  · rw [hval, ← hone, Ne, hcoe, hcomm]
    exact h2
  · rw [hval, hval, Ne, hcoe, hcomm, hcomm]
    exact h12

theorem EA2_comm_E (hS : Setting h L η t Q T) {w e : G}
    (hw : w ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η) (he : e ∈ miyamotoEG h L η Q) :
    w * e = e * w := by
  obtain ⟨e', he', a, ha, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (fun e he a ha => hS.E_comm_A2 he ha) hw
  rw [mul_assoc, ← hS.E_comm_A2 he ha, ← mul_assoc, hS.E_comm he' he, mul_assoc]

theorem conj_E_eq_or (hS : Setting h L η t Q T) {e m : G} (he : e ∈ miyamotoEG h L η Q)
    (hm : m ∈ miyamotoM0 Q) : m * e * m⁻¹ = e ∨ m * e * m⁻¹ = t * e * t⁻¹ := by
  rcases hS.mem_EA2_or_of_mem_M hm with h1 | h1
  · left
    rw [hS.EA2_comm_E h1 he, mul_inv_cancel_right]
  · right
    rw [show m * e * m⁻¹ = t * ((t⁻¹ * m) * e * (t⁻¹ * m)⁻¹) * t⁻¹ by group,
      hS.EA2_comm_E h1 he, mul_inv_cancel_right]

theorem exists_ZP_ne_ne (hS : Setting h L η t Q T) (a b : G) :
    ∃ z ∈ miyamotoZG h L η, z ≠ a ∧ z ≠ b :=
  exists_mem_ne_ne (by rw [hS.card_ZP]; have := hS.four_le; omega) a b

theorem exists_conj_ne_of_not_mem_E (hS : Setting h L η t Q T) {x : G} (hx : x ∈ miyamotoM0 Q)
    (hxE : x ∉ miyamotoEG h L η Q) : ∃ m₁ ∈ miyamotoM0 Q, ∃ m₂ ∈ miyamotoM0 Q,
      m₁ * x * m₁⁻¹ ≠ x ∧ m₂ * x * m₂⁻¹ ≠ x ∧ m₁ * x * m₁⁻¹ ≠ m₂ * x * m₂⁻¹ := by
  have hne : ∀ {z y : G}, z ≠ 1 → z * y ≠ y := fun hz e =>
    hz (mul_right_cancel (e.trans (one_mul _).symm))
  have hne' : ∀ {z z' y : G}, z ≠ z' → z * y ≠ z' * y := fun hz e => hz (mul_right_cancel e)
  obtain ⟨s, hs, w, hw, rfl⟩ : ∃ s : G, (s = 1 ∨ s = t) ∧
      ∃ w ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η, x = s * w := by
    rcases hS.mem_EA2_or_of_mem_M hx with h1 | h1
    · exact ⟨1, Or.inl rfl, x, h1, (one_mul x).symm⟩
    · exact ⟨t, Or.inr rfl, t⁻¹ * x, h1, by group⟩
  obtain ⟨e, he, a, ha, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (fun e he a ha => hS.E_comm_A2 he ha) hw
  by_cases haZ : a ∈ miyamotoZG h L η
  · have hea : e * a ∈ miyamotoEG h L η Q := mul_mem he (hS.ZP_le_E haZ)
    rcases hs with hs1 | hst
    · exact absurd (by rw [hs1, one_mul]; exact hea) hxE
    subst s
    obtain ⟨z₁, hz₁, hz₁1, -⟩ := hS.exists_ZP_ne_ne 1 1
    obtain ⟨z₂, hz₂, hz₂1, hz₂₁⟩ := hS.exists_ZP_ne_ne 1 z₁
    obtain ⟨e₁, he₁, he₁z⟩ := hS.exists_E_crossed_eq hz₁
    obtain ⟨e₂, he₂, he₂z⟩ := hS.exists_E_crossed_eq hz₂
    have key : ∀ e₀ ∈ miyamotoEG h L η Q,
        e₀⁻¹ * (t * (e * a)) * e₀⁻¹⁻¹ = (e₀⁻¹ * t * e₀ * t) * (t * (e * a)) := by
      intro e₀ he₀
      calc e₀⁻¹ * (t * (e * a)) * e₀⁻¹⁻¹ = e₀⁻¹ * t * ((e * a) * e₀) := by group
        _ = e₀⁻¹ * t * (e₀ * (e * a)) := by rw [hS.E_comm hea he₀]
        _ = e₀⁻¹ * t * e₀ * (t * t) * (e * a) := by rw [hS.t_mul_t]; group
        _ = (e₀⁻¹ * t * e₀ * t) * (t * (e * a)) := by group
    refine ⟨e₁⁻¹, hS.E_le_M (inv_mem he₁), e₂⁻¹, hS.E_le_M (inv_mem he₂), ?_, ?_, ?_⟩
    · rw [key e₁ he₁, he₁z]
      exact hne hz₁1
    · rw [key e₂ he₂, he₂z]
      exact hne hz₂1
    · rw [key e₁ he₁, key e₂ he₂, he₁z, he₂z]
      exact hne' (Ne.symm hz₂₁)
  · obtain ⟨m₁, hm₁, m₂, hm₂, h1, h2, h12⟩ := hS.exists_A2G_commutator_ne ha haZ
    have key : ∀ m ∈ miyamotoA2G h L η, m * (s * (e * a)) * m⁻¹ = ⁅m, a⁆ * (s * (e * a)) := by
      intro m hm
      have hmC : m ∈ centralizer ({t} : Set G) := hS.PG_le_C (hS.A2G_le_PG hm)
      have hz : ⁅m, a⁆ ∈ miyamotoZG h L η := hS.A2_mod_Z.2 m hm a ha
      have hms : m * s = s * m := by
        rcases hs with rfl | rfl
        · rw [one_mul, mul_one]
        · exact (mem_centralizer_singleton_iff.1 hmC)
      have hzs : ⁅m, a⁆ * s = s * ⁅m, a⁆ := by
        rcases hs with rfl | rfl
        · rw [one_mul, mul_one]
        · exact mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t hz)
      have hme : m * e = e * m := (hS.E_comm_A2 he hm).symm
      have hze : ⁅m, a⁆ * e = e * ⁅m, a⁆ := hS.E_comm (hS.ZP_le_E hz) he
      calc m * (s * (e * a)) * m⁻¹ = (m * s) * e * a * m⁻¹ := by group
        _ = s * (m * e) * a * m⁻¹ := by rw [hms]; group
        _ = s * e * (m * a * m⁻¹ * a⁻¹) * a := by rw [hme]; group
        _ = s * (e * ⁅m, a⁆) * a := by rw [commutatorElement_def]; group
        _ = s * (⁅m, a⁆ * e) * a := by rw [hze]
        _ = (s * ⁅m, a⁆) * e * a := by group
        _ = (⁅m, a⁆ * s) * e * a := by rw [hzs]
        _ = ⁅m, a⁆ * (s * (e * a)) := by group
    refine ⟨m₁, hS.A2_le_M hm₁, m₂, hS.A2_le_M hm₂, ?_, ?_, ?_⟩
    · rw [key m₁ hm₁]
      exact hne h1
    · rw [key m₂ hm₂]
      exact hne h2
    · rw [key m₁ hm₁, key m₂ hm₂]
      exact hne' h12

theorem mem_E_iff (hS : Setting h L η t Q T) {x : G} (hx : x ∈ miyamotoM0 Q) :
    x ∈ miyamotoEG h L η Q ↔ ∀ m₁ ∈ miyamotoM0 Q, ∀ m₂ ∈ miyamotoM0 Q,
      m₁ * x * m₁⁻¹ = x ∨ m₂ * x * m₂⁻¹ = x ∨ m₁ * x * m₁⁻¹ = m₂ * x * m₂⁻¹ := by
  constructor
  · intro hxE m₁ hm₁ m₂ hm₂
    rcases hS.conj_E_eq_or hxE hm₁ with h1 | h1
    · exact Or.inl h1
    rcases hS.conj_E_eq_or hxE hm₂ with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (h1.trans h2.symm))
  · intro hP
    by_contra hxE
    obtain ⟨m₁, hm₁, m₂, hm₂, h1, h2, h12⟩ := hS.exists_conj_ne_of_not_mem_E hx hxE
    rcases hP m₁ hm₁ m₂ hm₂ with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h12 h

theorem normalizer_M_le_normalizer_E (hS : Setting h L η t Q T) :
    normalizer (miyamotoM0 Q : Set G) ≤ normalizer (miyamotoEG h L η Q : Set G) := by
  intro n hn
  refine mem_normalizer_fintype fun e he => ?_
  have hx : n * e * n⁻¹ ∈ miyamotoM0 Q := (mem_normalizer_iff.1 hn e).1 (hS.E_le_M he)
  have hconj : ∀ m ∈ miyamotoM0 Q, n⁻¹ * m * n ∈ miyamotoM0 Q := fun m hm => by
    have := (mem_normalizer_iff.1 (inv_mem hn) m).1 hm
    rwa [inv_inv] at this
  have e1 : ∀ m : G, m * (n * e * n⁻¹) * m⁻¹ = n * ((n⁻¹ * m * n) * e * (n⁻¹ * m * n)⁻¹) * n⁻¹ :=
    fun m => by group
  rw [SetLike.mem_coe, hS.mem_E_iff hx]
  intro m₁ hm₁ m₂ hm₂
  rw [e1, e1]
  rcases (hS.mem_E_iff (hS.E_le_M he)).1 he _ (hconj m₁ hm₁) _ (hconj m₂ hm₂) with h1 | h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (Or.inl (by rw [h1]))
  · exact Or.inr (Or.inr (by rw [h1]))

theorem mem_EA2_of_mem_M_of_comm (hS : Setting h L η t Q T) {x : G} (hx : x ∈ miyamotoM0 Q)
    (hxE : ∀ e ∈ miyamotoEG h L η Q, x * e = e * x) :
    x ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η := by
  rcases hS.mem_EA2_or_of_mem_M hx with h1 | h1
  · exact h1
  exfalso
  obtain ⟨z, hz, hz1, -⟩ := hS.exists_ZP_ne_ne 1 1
  obtain ⟨e, he, hez⟩ := hS.exists_E_crossed_eq hz
  have hte : t * e = e * t := by
    have h2 := hS.EA2_comm_E (inv_mem h1) he
    have h3 := hxE e he
    calc t * e = x * (t⁻¹ * x)⁻¹ * e := by group
      _ = x * ((t⁻¹ * x)⁻¹ * e) := by group
      _ = x * (e * (t⁻¹ * x)⁻¹) := by rw [h2]
      _ = (x * e) * (t⁻¹ * x)⁻¹ := by group
      _ = (e * x) * (t⁻¹ * x)⁻¹ := by rw [h3]
      _ = e * t := by group
  apply hz1
  rw [← hez, mul_assoc e⁻¹, hte, ← mul_assoc, inv_mul_cancel, one_mul, hS.t_mul_t]

theorem normalizer_M_le_normalizer_EA2 (hS : Setting h L η t Q T) :
    normalizer (miyamotoM0 Q : Set G) ≤
      normalizer ((miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_fintype fun w hw => ?_
  refine hS.mem_EA2_of_mem_M_of_comm ((mem_normalizer_iff.1 hn w).1 (hS.EA2_le_M hw))
    fun e he => ?_
  have he' : n⁻¹ * e * n ∈ miyamotoEG h L η Q := by
    have := (mem_normalizer_iff.1 (hS.normalizer_M_le_normalizer_E (inv_mem hn)) e).1 he
    rwa [inv_inv] at this
  have hc := hS.EA2_comm_E hw he'
  calc n * w * n⁻¹ * e = n * (w * (n⁻¹ * e * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * e * n) * w) * n⁻¹ := by rw [hc]
    _ = e * (n * w * n⁻¹) := by group

theorem normalizer_M_inf_C_le_H (hS : Setting h L η t Q T) :
    normalizer (miyamotoM0 Q : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (CFSG.centerIn Q : Set G) := by
  obtain ⟨-, -, hMC, -, -⟩ := hS.two_core_M
  intro c hc
  rw [← hS.sec3_2.2.2.2.2, ← hMC]
  exact mem_normalizer_inf hc.1 (le_normalizer hc.2)

theorem normalizer_EB2_inf_C (hS : Setting h L η t Q T) :
    normalizer ((miyamotoEG h L η Q ⊔ miyamotoB2 h L η t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) =
      normalizer (miyamotoB2 h L η t : Set G) ⊓ centralizer ({t} : Set G) := by
  rw [hS.E_sup_B2, hS.sec3_2.2.2.2.2]
  refine le_antisymm (fun c hc => ⟨hS.normalizer_M_inf_C_le_H hc, hc.2⟩) fun c hc => ?_
  exact ⟨hS.H_le_normalizer_M hc.1, hc.2⟩

theorem exists_E_conj_eq (hS : Setting h L η t Q T) {y : G} (hy : y * y = 1)
    (hyE : t⁻¹ * y ∈ miyamotoEG h L η Q) : ∃ e ∈ miyamotoEG h L η Q, e⁻¹ * t * e = y := by
  set x := t⁻¹ * y with hx
  have hyx : y = t * x := by rw [hx, mul_inv_cancel_left]
  have h1 : t * x * t = x⁻¹ := by
    calc t * x * t = ((t * x) * (t * x)) * x⁻¹ := by group
      _ = x⁻¹ := by rw [← hyx, hy, one_mul]
  have hxZ : x ∈ miyamotoZG h L η := by
    refine (hS.crossed_eq_one_iff_E hyE).1 ?_
    calc x⁻¹ * t * x * t = x⁻¹ * (t * x * t) := by group
      _ = (x * x)⁻¹ := by rw [h1]; group
      _ = 1 := by rw [hS.E_mul_self hyE, inv_one]
  obtain ⟨e, he, hex⟩ := hS.exists_E_crossed_eq hxZ
  refine ⟨e, he, ?_⟩
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t hxZ)
  calc e⁻¹ * t * e = e⁻¹ * t * e * t * t := by rw [mul_assoc _ t t, hS.t_mul_t, mul_one]
    _ = t * x := by rw [hex, hxt]
    _ = y := hyx.symm

theorem exists_mul_of_crossed_mem_E (hS : Setting h L η t Q T) {n : G}
    (hn : n ∈ normalizer (miyamotoM0 Q : Set G)) (hnE : n⁻¹ * t * n * t ∈ miyamotoEG h L η Q) :
    ∃ c ∈ normalizer (miyamotoM0 Q : Set G) ⊓ centralizer ({t} : Set G),
      ∃ e ∈ miyamotoEG h L η Q, n = c * e := by
  have hy : (n⁻¹ * t * n) * (n⁻¹ * t * n) = 1 := by
    rw [show (n⁻¹ * t * n) * (n⁻¹ * t * n) = n⁻¹ * (t * t) * n by group, hS.t_mul_t]
    group
  have hyE : t⁻¹ * (n⁻¹ * t * n) ∈ miyamotoEG h L η Q := by
    have := (mem_normalizer_iff.1 (inv_mem hS.t_mem_normalizer_E) _).1 hnE
    rwa [inv_inv, show t⁻¹ * (n⁻¹ * t * n * t) * t = t⁻¹ * (n⁻¹ * t * n) * (t * t) by group,
      hS.t_mul_t, mul_one] at this
  obtain ⟨e, he, het⟩ := hS.exists_E_conj_eq hy hyE
  have he' : e⁻¹ ∈ miyamotoM0 Q := hS.E_le_M (inv_mem he)
  refine ⟨n * e⁻¹, ⟨mul_mem hn (le_normalizer he'),
    CFSG.LocalAnalysis.EvenBN.Common.mul_inv_mem_centralizer_of_conj_eq het⟩, e, he, by group⟩

theorem E_inf_A2 (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊓ miyamotoA2G h L η = miyamotoZG h L η :=
  le_antisymm (fun x hx => by rw [← hS.E_inf_B2]; exact ⟨hx.1, mem_sup_right hx.2⟩)
    (le_inf hS.ZP_le_E hS.ZP_le_A2)

theorem mem_B2_of_fixes_mod_ZP (hS : Setting h L η t Q T) {c : G}
    (hc : c ∈ centralizer ({t} : Set G))
    (hcA : ∀ a ∈ miyamotoA2G h L η, c * a * c⁻¹ * a⁻¹ ∈ miyamotoZG h L η) :
    c ∈ miyamotoB2 h L η t := by
  have : CharP K 2 := h.charP
  have hfix : ∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoA2 h →
      (g : GL (Fin 4) K)⁻¹ * (hS.act ⟨c, hc⟩ g : GL (Fin 4) K) ∈ miyamotoZ h := by
    intro g hg
    have haA : ((η.symm g : L) : G) ∈ miyamotoA2G h L η :=
      (symm_mem_miyamotoPull_iff h L η).2 hg
    set a : G := ((η.symm g : L) : G) with ha
    have hz := hcA a haA
    have hza : (c * a * c⁻¹ * a⁻¹) * a = a * (c * a * c⁻¹ * a⁻¹) :=
      mem_centralizer_iff.1 (hS.A2_le_centralizer_ZP haA) _ hz
    have key : ((η.symm (g⁻¹ * hS.act ⟨c, hc⟩ g) : L) : G) = c * a * c⁻¹ * a⁻¹ := by
      rw [map_mul, map_inv, coe_mul, coe_inv, coe_symm_act_apply, ← ha]
      calc a⁻¹ * (c * a * c⁻¹) = a⁻¹ * ((c * a * c⁻¹ * a⁻¹) * a) := by group
        _ = c * a * c⁻¹ * a⁻¹ := by rw [hza]; group
    have hmem : ((η.symm (g⁻¹ * hS.act ⟨c, hc⟩ g) : L) : G) ∈ miyamotoZG h L η := by
      rw [key]
      exact hz
    exact (symm_mem_miyamotoPull_iff h L η).1 hmem
  obtain ⟨a₀, ha₀, hact⟩ := (fixes_mod_Z_iff h _).1 hfix
  rw [act_apply] at hact
  obtain ⟨k, hkL, hck⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η _ a₀ hact
  have hck' : c = ((η.symm a₀ : L) : G) * k := hck
  have haC : ((η.symm a₀ : L) : G) ∈ centralizer ({t} : Set G) :=
    hS.L_le_centralizer (η.symm a₀).2
  have hkC : k ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem haC) hc
    rwa [hck', inv_mul_cancel_left] at this
  have hkt : k ∈ zpowers t := by
    rw [← hS.kernel_eq_zpowers']
    exact ⟨hkL, hkC⟩
  have haA : ((η.symm a₀ : L) : G) ∈ miyamotoA2G h L η := (symm_mem_miyamotoPull_iff h L η).2 ha₀
  rw [hck', miyamotoB2]
  exact mul_mem (mem_sup_right haA) (mem_sup_left hkt)

theorem C0_inf_C_le_B2 (hS : Setting h L η t Q T) :
    miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q) (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) ⊓
      centralizer ({t} : Set G) ≤ miyamotoB2 h L η t := by
  rintro c ⟨hc0, hcC⟩
  have hcH : c ∈ normalizer (CFSG.centerIn Q : Set G) := hS.normalizer_M_inf_C_le_H ⟨hc0.1, hcC⟩
  refine hS.mem_B2_of_fixes_mod_ZP hcC fun a ha => ?_
  have hA : c * a * c⁻¹ * a⁻¹ ∈ miyamotoA2G h L η :=
    mul_mem ((mem_normalizer_iff.1 (hS.H_le_normalizer_A2 hcH) a).1 ha) (inv_mem ha)
  rw [← hS.E_inf_A2]
  exact mem_inf.2 ⟨hc0.2.2.2 a (mem_sup_right ha), hA⟩

theorem M_le_C0 (hS : Setting h L η t Q T) :
    miyamotoM0 Q ≤ miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
      (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) := by
  have hmem : ∀ x ∈ miyamotoM0 Q, (∀ w ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η,
      x * w * x⁻¹ * w⁻¹ ∈ miyamotoEG h L η Q) → x ∈ miyamotoC0 (miyamotoM0 Q)
        (miyamotoEG h L η Q) (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) := fun x hx hw =>
    ⟨(hS.H_le_normalizers (hS.M_le_H hx)).1, (hS.H_le_normalizers (hS.M_le_H hx)).2.1,
      (hS.H_le_normalizers (hS.M_le_H hx)).2.2, hw⟩
  have hdec : ∀ w ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η, ∃ e ∈ miyamotoEG h L η Q,
      ∃ a ∈ miyamotoA2G h L η, w = e * a := fun w hw =>
    exists_mul_of_mem_sup_of_commute (fun e he a ha => hS.E_comm_A2 he ha) hw
  intro x hx
  rw [← hS.E_sup_B2, miyamotoB2] at hx
  refine (sup_le (fun e he => hmem e (hS.E_le_M he) fun w hw => ?_)
    (sup_le ((zpowers_le).2 (hmem t hS.t_mem_M fun w hw => ?_))
      fun a ha => hmem a (hS.A2_le_M ha) fun w hw => ?_)) hx
  · rw [show e * w * e⁻¹ * w⁻¹ = e * (w * e⁻¹ * w⁻¹) by group]
    exact mul_mem he ((mem_normalizer_iff.1
      (hS.H_le_normalizers (hS.M_le_H (hS.EA2_le_M hw))).2.1 e⁻¹).1 (inv_mem he))
  · obtain ⟨e, he, a, ha, rfl⟩ := hdec w hw
    have hat : a * t = t * a := mem_centralizer_singleton_iff.1 (hS.PG_le_C (hS.A2G_le_PG ha))
    have hat' : a * t⁻¹ = t⁻¹ * a := (Commute.inv_right (show Commute a t from hat)).eq
    rw [show t * (e * a) * t⁻¹ * (e * a)⁻¹ = t * e * (a * t⁻¹) * a⁻¹ * e⁻¹ by group, hat',
      show t * e * (t⁻¹ * a) * a⁻¹ * e⁻¹ = (t * e * t⁻¹) * e⁻¹ by group]
    exact mul_mem ((mem_normalizer_iff.1 hS.t_mem_normalizer_E e).1 he) (inv_mem he)
  · obtain ⟨e, he, a', ha', rfl⟩ := hdec w hw
    have hae : a * e = e * a := (hS.E_comm_A2 he ha).symm
    rw [show a * (e * a') * a⁻¹ * (e * a')⁻¹ = (a * e) * a' * a⁻¹ * a'⁻¹ * e⁻¹ by group, hae,
      show e * a * a' * a⁻¹ * a'⁻¹ * e⁻¹ = e * ⁅a, a'⁆ * e⁻¹ by rw [commutatorElement_def]; group]
    exact mul_mem (mul_mem he (hS.ZP_le_E (hS.A2_mod_Z.2 a ha a' ha'))) (inv_mem he)

theorem normalizer_M_le_normalizer_C0 (hS : Setting h L η t Q T) :
    normalizer (miyamotoM0 Q : Set G) ≤ normalizer (miyamotoC0 (miyamotoM0 Q)
      (miyamotoEG h L η Q) (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) : Set G) := fun _ hn =>
  le_normalizer_miyamotoC0 hn (hS.normalizer_M_le_normalizer_E hn)
    (hS.normalizer_M_le_normalizer_EA2 hn)

theorem conj_t_mem_E_iff_of_mem_C0 (hS : Setting h L η t Q T) {g : G}
    (hg : g ∈ miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
      (miyamotoEG h L η Q ⊔ miyamotoA2G h L η)) :
    t⁻¹ * (g * t * g⁻¹) ∈ miyamotoEG h L η Q ↔ g ∈ miyamotoM0 Q := by
  constructor
  · intro hgE
    have hδ : g⁻¹⁻¹ * t * g⁻¹ * t ∈ miyamotoEG h L η Q := by
      rw [inv_inv, show g * t * g⁻¹ * t = t * (t⁻¹ * (g * t * g⁻¹)) * t⁻¹ * (t * t) by group,
        hS.t_mul_t, mul_one]
      exact (mem_normalizer_iff.1 hS.t_mem_normalizer_E _).1 hgE
    obtain ⟨c, hc, e, he, hce⟩ := hS.exists_mul_of_crossed_mem_E (inv_mem hg.1) hδ
    have hcC0 : c ∈ miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
        (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) := by
      have e1 : c = g⁻¹ * e⁻¹ := by rw [hce]; group
      rw [e1]
      exact mul_mem (inv_mem hg) (hS.M_le_C0 (hS.E_le_M (inv_mem he)))
    have hcB := hS.C0_inf_C_le_B2 ⟨hcC0, hc.2⟩
    have e2 : g = (c * e)⁻¹ := by rw [← hce, inv_inv]
    rw [e2]
    exact inv_mem (mul_mem (hS.B2_le_M hcB) (hS.E_le_M he))
  · intro hgM
    have hy := hS.crossed_mem_ZP (hS.M_le_H (inv_mem hgM))
    rw [inv_inv] at hy
    have hyt : (g * t * g⁻¹ * t) * t = t * (g * t * g⁻¹ * t) :=
      mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t hy)
    have e1 : t⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * t := by
      calc t⁻¹ * (g * t * g⁻¹) = t⁻¹ * ((g * t * g⁻¹ * t) * t) := by
            rw [mul_assoc (g * t * g⁻¹) t t, hS.t_mul_t, mul_one]
        _ = t⁻¹ * (t * (g * t * g⁻¹ * t)) := by rw [hyt]
        _ = g * t * g⁻¹ * t := by group
    rw [e1]
    exact hS.ZP_le_E hy

theorem card_C0 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
      (miyamotoEG h L η Q ⊔ miyamotoA2G h L η)) = (2 ^ f) ^ 4 * Nat.card (miyamotoM0 Q) := by
  set E := miyamotoEG h L η Q with hE
  set EA := miyamotoEG h L η Q ⊔ miyamotoA2G h L η with hEA
  set C₀ := miyamotoC0 (miyamotoM0 Q) E EA with hC₀
  have := hS.normal_E_subgroupOf_EA2
  have hx : ∀ g ∈ C₀, t⁻¹ * (g * t * g⁻¹) ∈ EA := fun g hg => hS.conj_t_mem_EA2 hg.1 hg.2.2.1
  let φ : C₀ →* EA ⧸ E.subgroupOf EA :=
    MonoidHom.mk' (fun g => QuotientGroup.mk (⟨t⁻¹ * ((g : G) * t * (g : G)⁻¹), hx g g.2⟩ : EA))
      fun g k => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        have hk := hx k k.2
        have := g.2.2.2.2 _ (inv_mem hk)
        simp only [coe_mul, coe_inv]
        rw [show (t⁻¹ * ((g : G) * (k : G) * t * ((g : G) * (k : G))⁻¹))⁻¹ *
            (t⁻¹ * ((g : G) * t * (g : G)⁻¹) * (t⁻¹ * ((k : G) * t * (k : G)⁻¹))) =
          (g : G) * (t⁻¹ * ((k : G) * t * (k : G)⁻¹))⁻¹ * (g : G)⁻¹ *
            (t⁻¹ * ((k : G) * t * (k : G)⁻¹))⁻¹⁻¹ by group]
        exact this
  have hφ : ∀ g : C₀, φ g = QuotientGroup.mk
      (⟨t⁻¹ * ((g : G) * t * (g : G)⁻¹), hx g g.2⟩ : EA) := fun _ => rfl
  have hrange : φ.range = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    induction w using QuotientGroup.induction_on with | H w => ?_
    obtain ⟨g, hg, hgw⟩ := hS.C0_surj w w.2
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [hφ, QuotientGroup.eq, mem_subgroupOf]
    have := inv_mem hgw
    rw [mul_inv_rev, inv_inv] at this
    exact this
  have hker : φ.ker = (miyamotoM0 Q).subgroupOf C₀ := by
    ext g
    rw [MonoidHom.mem_ker, hφ, QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
    exact hS.conj_t_mem_E_iff_of_mem_C0 g.2
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, Subgroup.card_top, hker] at h1
  have hM : Nat.card ((miyamotoM0 Q).subgroupOf C₀) = Nat.card (miyamotoM0 Q) :=
    Nat.card_congr (subgroupOfEquivOfLe hS.M_le_C0).toEquiv
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf EA)
  have hE' : Nat.card (E.subgroupOf EA) = Nat.card E :=
    Nat.card_congr (subgroupOfEquivOfLe hS.E_le_EA2).toEquiv
  rw [hE', hS.card_E_sup_A2, hS.card_E] at h2
  have hq : Nat.card (EA ⧸ E.subgroupOf EA) = (2 ^ f) ^ 4 := by
    have : (2 ^ f) ^ 4 * (2 ^ f) ^ 2 = Nat.card (EA ⧸ E.subgroupOf EA) * (2 ^ f) ^ 2 := by
      rw [← h2]; ring
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) this).symm
  rw [← h1, hM, hq, mul_comm]

theorem isPGroup_C0 (hS : Setting h L η t Q T) :
    IsPGroup 2 (miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
      (miyamotoEG h L η Q ⊔ miyamotoA2G h L η)) := by
  refine IsPGroup.of_card (n := 10 * f + 1) ?_
  rw [hS.card_C0, hS.card_M]
  ring

theorem exists_mul_C0 (hS : Setting h L η t Q T) {n : G}
    (hn : n ∈ normalizer (miyamotoM0 Q : Set G)) :
    ∃ c ∈ normalizer (miyamotoM0 Q : Set G) ⊓ centralizer ({t} : Set G),
      ∃ g ∈ miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
        (miyamotoEG h L η Q ⊔ miyamotoA2G h L η), n = c * g := by
  have hw := hS.conj_t_mem_EA2 hn (hS.normalizer_M_le_normalizer_EA2 hn)
  obtain ⟨g, hg, hgw⟩ := hS.C0_surj _ hw
  set k := g⁻¹ * n with hk
  have hkN : k ∈ normalizer (miyamotoM0 Q : Set G) := mul_mem (inv_mem hg.1) hn
  have hkE : t⁻¹ * (k * t * k⁻¹) ∈ miyamotoEG h L η Q := by
    have h2 : g⁻¹ * ((t⁻¹ * (n * t * n⁻¹))⁻¹ * (t⁻¹ * (g * t * g⁻¹)))⁻¹ * g⁻¹⁻¹ ∈
        miyamotoEG h L η Q := (mem_normalizer_iff.1 (inv_mem hg.2.1) _).1 (inv_mem hgw)
    rwa [show g⁻¹ * ((t⁻¹ * (n * t * n⁻¹))⁻¹ * (t⁻¹ * (g * t * g⁻¹)))⁻¹ * g⁻¹⁻¹ =
      t⁻¹ * (k * t * k⁻¹) by rw [hk]; group] at h2
  have hδ : k⁻¹⁻¹ * t * k⁻¹ * t ∈ miyamotoEG h L η Q := by
    rw [inv_inv, show k * t * k⁻¹ * t = t * (t⁻¹ * (k * t * k⁻¹)) * t⁻¹ * (t * t) by group,
      hS.t_mul_t, mul_one]
    exact (mem_normalizer_iff.1 hS.t_mem_normalizer_E _).1 hkE
  obtain ⟨c, hc, e, he, hce⟩ := hS.exists_mul_of_crossed_mem_E (inv_mem hkN) hδ
  refine ⟨c⁻¹, inv_mem hc, c * (g * e⁻¹) * c⁻¹,
    (mem_normalizer_iff.1 (hS.normalizer_M_le_normalizer_C0 hc.1) _).1
      (mul_mem hg (hS.M_le_C0 (hS.E_le_M (inv_mem he)))), ?_⟩
  have e1 : n = g * (k⁻¹)⁻¹ := by rw [hk]; group
  rw [e1, hce]
  group

theorem miyamotoD2G_eq (hS : Setting h L η t Q T) :
    miyamotoD2G h L η t Q = CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo
      (normalizer (miyamotoM0 Q : Set G)) := by
  rw [miyamotoD2G, hS.E_sup_B2]
  exact CFSG.LocalAnalysis.EvenBN.Common.pCore_map_eq_oTwo _

theorem C0_le_D2 (hS : Setting h L η t Q T) :
    miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q) (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) ≤
      miyamotoD2G h L η t Q := by
  rw [hS.miyamotoD2G_eq]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.le_oTwo (fun g hg => hg.1)
    hS.normalizer_M_le_normalizer_C0 hS.isPGroup_C0

theorem D2_inf_C_le_B2 (hS : Setting h L η t Q T) :
    miyamotoD2G h L η t Q ⊓ centralizer ({t} : Set G) ≤ miyamotoB2 h L η t := by
  rw [hS.miyamotoD2G_eq]
  set R := CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo (normalizer (miyamotoM0 Q : Set G)) ⊓
    centralizer ({t} : Set G) with hR
  have hRH : R ≤ normalizer (CFSG.centerIn Q : Set G) := fun r hr =>
    hS.normalizer_M_inf_C_le_H ⟨CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo_le _ hr.1, hr.2⟩
  have hRn : normalizer (CFSG.centerIn Q : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (R : Set G) := fun c hc =>
    mem_normalizer_inf (CFSG.EvenSmallLie.UnitarySix.YamadaD.le_normalizer_oTwo _
      (hS.H_le_normalizer_M hc.1)) (le_normalizer hc.2)
  have hR2 : IsPGroup 2 R :=
    (CFSG.EvenSmallLie.UnitarySix.YamadaD.isPGroup_oTwo _).to_le inf_le_left
  have hRZ := hS.le_centralizer_ZP_of_isPGroup hRH
    (fun i hi r hr => (mem_normalizer_iff.1 (hRn ⟨hS.IG_le_H hi, hS.IG_le_C hi⟩) r).1 hr) hR2
  have hRK : R ≤ centralizer (CFSG.centerIn Q : Set G) := by
    rw [← hS.centralizer_centerIn_Q_eq]
    exact fun r hr => ⟨⟨hRH hr, hRZ hr⟩, hr.2⟩
  exact hS.le_B2_of_isPGroup hRK (fun k hk => hRn ⟨hS.K0_le_H hk, hS.K0_le_C hk⟩) hR2

theorem D2_le_normalizer_M (hS : Setting h L η t Q T) :
    miyamotoD2G h L η t Q ≤ normalizer (miyamotoM0 Q : Set G) := by
  rw [hS.miyamotoD2G_eq]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo_le _

theorem D2_eq_C0 (hS : Setting h L η t Q T) :
    miyamotoD2G h L η t Q = miyamotoC0 (miyamotoM0 Q) (miyamotoEG h L η Q)
      (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) := by
  refine le_antisymm (fun d hd => ?_) hS.C0_le_D2
  obtain ⟨c, hc, g, hg, rfl⟩ := hS.exists_mul_C0 (hS.D2_le_normalizer_M hd)
  have hcD : c ∈ miyamotoD2G h L η t Q := by
    have := mul_mem hd (inv_mem (hS.C0_le_D2 hg))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (hS.M_le_C0 (hS.B2_le_M (hS.D2_inf_C_le_B2 ⟨hcD, hc.2⟩))) hg

theorem mem_D2_iff (hS : Setting h L η t Q T) {d : G} :
    d ∈ miyamotoD2G h L η t Q ↔
      d ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoB2 h L η t : Subgroup G) : Set G) ∧
        ∀ w ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η, d * w * d⁻¹ * w⁻¹ ∈ miyamotoEG h L η Q := by
  rw [hS.D2_eq_C0, hS.E_sup_B2]
  exact ⟨fun hd => ⟨hd.1, hd.2.2.2⟩, fun hd => ⟨hd.1, hS.normalizer_M_le_normalizer_E hd.1,
    hS.normalizer_M_le_normalizer_EA2 hd.1, hd.2⟩⟩

theorem normalizer_EB2_eq_mul (hS : Setting h L η t Q T) {g : G}
    (hg : g ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoB2 h L η t : Subgroup G) : Set G)) :
    ∃ c ∈ normalizer (miyamotoB2 h L η t : Set G) ⊓ centralizer ({t} : Set G),
      ∃ d ∈ miyamotoD2G h L η t Q, g = c * d := by
  rw [hS.E_sup_B2] at hg
  obtain ⟨c, hc, d, hd, rfl⟩ := hS.exists_mul_C0 hg
  refine ⟨c, ?_, d, hS.C0_le_D2 hd, rfl⟩
  rw [← hS.normalizer_EB2_inf_C, hS.E_sup_B2]
  exact hc

theorem normalizer_EB2_eq_mul' (hS : Setting h L η t Q T) {g : G}
    (hg : g ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoB2 h L η t : Subgroup G) : Set G)) :
    ∃ d ∈ miyamotoD2G h L η t Q,
      ∃ c ∈ normalizer (miyamotoB2 h L η t : Set G) ⊓ centralizer ({t} : Set G), g = d * c := by
  obtain ⟨c, hc, d, hd, e⟩ := hS.normalizer_EB2_eq_mul (inv_mem hg)
  exact ⟨d⁻¹, inv_mem hd, c⁻¹, inv_mem hc, by rw [← mul_inv_rev, ← e, inv_inv]⟩

theorem card_D2 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoD2G h L η t Q) = 2 * (2 ^ f) ^ 10 := by
  rw [hS.D2_eq_C0, hS.card_C0, hS.card_M]
  ring

theorem EB2_le_D2 (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊔ miyamotoB2 h L η t ≤ miyamotoD2G h L η t Q := by
  rw [hS.E_sup_B2]
  exact hS.M_le_C0.trans hS.C0_le_D2

theorem D2_inf_C (hS : Setting h L η t Q T) :
    miyamotoD2G h L η t Q ⊓ centralizer ({t} : Set G) = miyamotoB2 h L η t :=
  le_antisymm hS.D2_inf_C_le_B2
    (le_inf ((le_sup_right.trans_eq hS.E_sup_B2).trans (hS.E_sup_B2.symm ▸ hS.EB2_le_D2))
      hS.B2_le_C)

theorem crossed_mem_EA2_of_mem_D2 (hS : Setting h L η t Q T) {d : G}
    (hd : d ∈ miyamotoD2G h L η t Q) :
    d⁻¹ * t * d * t ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η := by
  have hd' := hS.D2_le_normalizer_M (inv_mem hd)
  have h1 := hS.conj_t_mem_EA2 hd' (hS.normalizer_M_le_normalizer_EA2 hd')
  rw [inv_inv] at h1
  have htA : t ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) : Set G) :=
    hS.H_le_normalizer_EA2 (hS.M_le_H hS.t_mem_M)
  rw [show d⁻¹ * t * d * t = t * (t⁻¹ * (d⁻¹ * t * d)) * t⁻¹ * (t * t) by group, hS.t_mul_t,
    mul_one]
  exact (mem_normalizer_iff.1 htA _).1 h1

theorem crossed_mem_E_iff_of_mem_D2 (hS : Setting h L η t Q T) {d : G}
    (hd : d ∈ miyamotoD2G h L η t Q) :
    d⁻¹ * t * d * t ∈ miyamotoEG h L η Q ↔ d ∈ miyamotoEG h L η Q ⊔ miyamotoB2 h L η t := by
  rw [hS.E_sup_B2]
  constructor
  · intro hδ
    obtain ⟨c, hc, e, he, rfl⟩ := hS.exists_mul_of_crossed_mem_E (hS.D2_le_normalizer_M hd) hδ
    have hcD : c ∈ miyamotoD2G h L η t Q := by
      have := mul_mem hd (inv_mem (hS.EB2_le_D2 (mem_sup_left he)))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (hS.B2_le_M (hS.D2_inf_C_le_B2 ⟨hcD, hc.2⟩)) (hS.E_le_M he)
  · intro hdM
    exact hS.ZP_le_E (hS.crossed_mem_ZP (hS.M_le_H hdM))

theorem exists_D2_crossed_eq (hS : Setting h L η t Q T) {a : G} (ha : a ∈ miyamotoA2G h L η) :
    ∃ d ∈ miyamotoD2G h L η t Q, ∃ e ∈ miyamotoEG h L η Q, d⁻¹ * t * d * t = e * a := by
  obtain ⟨g, hg, hga⟩ := hS.C0_surj a (mem_sup_right ha)
  set e₀ := a⁻¹ * (t⁻¹ * (g * t * g⁻¹)) with he₀
  have hat : a * t = t * a := mem_centralizer_singleton_iff.1 (hS.PG_le_C (hS.A2G_le_PG ha))
  have he₁ : t * e₀ * t⁻¹ ∈ miyamotoEG h L η Q :=
    (mem_normalizer_iff.1 hS.t_mem_normalizer_E e₀).1 hga
  refine ⟨g⁻¹, hS.C0_le_D2 (inv_mem hg), t * e₀ * t⁻¹, he₁, ?_⟩
  have e1 : a * (t * e₀ * t⁻¹) = g * t * g⁻¹ * t⁻¹ := by
    rw [show a * (t * e₀ * t⁻¹) = (a * t) * e₀ * t⁻¹ by group, hat, he₀]
    group
  rw [hS.E_comm_A2 he₁ ha, e1, inv_inv, hS.t_inv]

theorem commutator_D2_EA2_mem_E (hS : Setting h L η t Q T) {d w : G}
    (hd : d ∈ miyamotoD2G h L η t Q) (hw : w ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η) :
    d * w * d⁻¹ * w⁻¹ ∈ miyamotoEG h L η Q :=
  ((hS.mem_D2_iff).1 hd).2 w hw

theorem crossed_mul_mod_E (hS : Setting h L η t Q T) {d d' : G}
    (hd : d ∈ miyamotoD2G h L η t Q) (hd' : d' ∈ miyamotoD2G h L η t Q) :
    ((d * d')⁻¹ * t * (d * d') * t)⁻¹ * ((d⁻¹ * t * d * t) * (d'⁻¹ * t * d' * t)) ∈
      miyamotoEG h L η Q := by
  set x := d⁻¹ * t * d * t with hx
  set y := d'⁻¹ * t * d' * t with hy
  have hxw := hS.crossed_mem_EA2_of_mem_D2 hd
  have hyw := hS.crossed_mem_EA2_of_mem_D2 hd'
  have h1 := hS.commutator_D2_EA2_mem_E (inv_mem hd') hxw
  have hxyN : x * y ∈ normalizer (miyamotoEG h L η Q : Set G) :=
    hS.H_le_normalizer_E (hS.M_le_H (hS.EA2_le_M (mul_mem hxw hyw)))
  have h2 := (mem_normalizer_iff.1 (inv_mem hxyN) _).1 (inv_mem h1)
  rw [show ((d * d')⁻¹ * t * (d * d') * t)⁻¹ * (x * y) =
    (t⁻¹ * d'⁻¹ * (t * t) * d' * t) *
      ((x * y)⁻¹ * (d'⁻¹ * x * d'⁻¹⁻¹ * x⁻¹)⁻¹ * (x * y)⁻¹⁻¹) by rw [hx, hy]; group,
    hS.t_mul_t, show t⁻¹ * d'⁻¹ * 1 * d' * t = 1 by group, one_mul]
  exact h2

theorem normal_EB2_subgroupOf_D2 (hS : Setting h L η t Q T) :
    ((miyamotoEG h L η Q ⊔ miyamotoB2 h L η t).subgroupOf (miyamotoD2G h L η t Q)).Normal := by
  refine (normal_subgroupOf_iff_le_normalizer hS.EB2_le_D2).2 ?_
  rw [hS.E_sup_B2]
  exact hS.D2_le_normalizer_M

theorem normal_ZP_subgroupOf_A2 (hS : Setting h L η t Q T) :
    ((miyamotoZG h L η).subgroupOf (miyamotoA2G h L η)).Normal :=
  (normal_subgroupOf_iff_le_normalizer hS.ZP_le_A2).2 fun a ha =>
    mem_normalizer_fintype fun z hz => by
      rw [← mem_centralizer_iff.1 (hS.A2_le_centralizer_ZP ha) z hz, mul_inv_cancel_right]
      exact hz

theorem exists_mulEquiv_D2 (hS : Setting h L η t Q T)
    [((miyamotoEG h L η Q ⊔ miyamotoB2 h L η t).subgroupOf (miyamotoD2G h L η t Q)).Normal]
    [((miyamotoZG h L η).subgroupOf (miyamotoA2G h L η)).Normal] :
    ∃ φ : miyamotoD2G h L η t Q ⧸
        (miyamotoEG h L η Q ⊔ miyamotoB2 h L η t).subgroupOf (miyamotoD2G h L η t Q) ≃*
      miyamotoA2G h L η ⧸ (miyamotoZG h L η).subgroupOf (miyamotoA2G h L η),
      (∀ (d : miyamotoD2G h L η t Q) (a : miyamotoA2G h L η), ∀ e ∈ miyamotoEG h L η Q,
        (d : G)⁻¹ * t * d * t = e * a → φ (QuotientGroup.mk d) = QuotientGroup.mk a) ∧
      ∀ c ∈ normalizer (miyamotoB2 h L η t : Set G) ⊓ centralizer ({t} : Set G),
        ∀ (d : miyamotoD2G h L η t Q) (a : miyamotoA2G h L η)
          (hd : c * d * c⁻¹ ∈ miyamotoD2G h L η t Q) (ha : c * a * c⁻¹ ∈ miyamotoA2G h L η),
          φ (QuotientGroup.mk d) = QuotientGroup.mk a →
            φ (QuotientGroup.mk ⟨c * d * c⁻¹, hd⟩) = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩ := by
  set E := miyamotoEG h L η Q with hE
  set EA := miyamotoEG h L η Q ⊔ miyamotoA2G h L η with hEA
  have := hS.normal_E_subgroupOf_EA2
  have hEAE : ∀ w ∈ EA, w ∈ normalizer (E : Set G) := fun w hw =>
    hS.H_le_normalizer_E (hS.M_le_H (hS.EA2_le_M hw))
  let ψ₁ : miyamotoD2G h L η t Q →* EA ⧸ E.subgroupOf EA :=
    MonoidHom.mk' (fun d => QuotientGroup.mk
      (⟨(d : G)⁻¹ * t * d * t, hS.crossed_mem_EA2_of_mem_D2 d.2⟩ : EA)) fun d d' => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        simpa using hS.crossed_mul_mod_E d.2 d'.2
  have hψ₁ : ∀ d : miyamotoD2G h L η t Q, ψ₁ d = QuotientGroup.mk
      (⟨(d : G)⁻¹ * t * d * t, hS.crossed_mem_EA2_of_mem_D2 d.2⟩ : EA) := fun _ => rfl
  let ψ₂ : miyamotoA2G h L η →* EA ⧸ E.subgroupOf EA :=
    (QuotientGroup.mk' _).comp (inclusion le_sup_right)
  have hψ₂ : ∀ a : miyamotoA2G h L η,
      ψ₂ a = QuotientGroup.mk (⟨a, mem_sup_right a.2⟩ : EA) := fun _ => rfl
  have hdec : ∀ w ∈ EA, ∃ e ∈ E, ∃ a ∈ miyamotoA2G h L η, w = e * a := fun w hw =>
    exists_mul_of_mem_sup_of_commute (fun e he a ha => hS.E_comm_A2 he ha) hw
  have hconj : ∀ a ∈ miyamotoA2G h L η, ∀ e ∈ E, a⁻¹ * e * a ∈ E := fun a ha e he => by
    have := (mem_normalizer_iff.1 (hEAE _ (inv_mem (mem_sup_right ha))) e).1 he
    rwa [inv_inv] at this
  have hker₁ : ψ₁.ker = (miyamotoEG h L η Q ⊔ miyamotoB2 h L η t).subgroupOf
      (miyamotoD2G h L η t Q) := by
    ext d
    rw [MonoidHom.mem_ker, hψ₁, QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
    exact hS.crossed_mem_E_iff_of_mem_D2 d.2
  have hsurj₁ : Function.Surjective ψ₁ := by
    intro q
    induction q using QuotientGroup.induction_on with | H w => ?_
    obtain ⟨e, he, a, ha, hw⟩ := hdec w w.2
    obtain ⟨d, hd, e', he', hd'⟩ := hS.exists_D2_crossed_eq ha
    refine ⟨⟨d, hd⟩, ?_⟩
    rw [hψ₁, QuotientGroup.eq, mem_subgroupOf]
    change ((d : G)⁻¹ * t * d * t)⁻¹ * w ∈ E
    rw [hd', hw, show (e' * a)⁻¹ * (e * a) = a⁻¹ * (e'⁻¹ * e) * a by group]
    exact hconj a ha _ (mul_mem (inv_mem he') he)
  have hker₂ : ψ₂.ker = (miyamotoZG h L η).subgroupOf (miyamotoA2G h L η) := by
    ext a
    rw [MonoidHom.mem_ker, hψ₂, QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
    change (a : G) ∈ E ↔ _
    rw [← hS.E_inf_A2]
    exact ⟨fun h1 => ⟨h1, a.2⟩, fun h1 => h1.1⟩
  have hsurj₂ : Function.Surjective ψ₂ := by
    intro q
    induction q using QuotientGroup.induction_on with | H w => ?_
    obtain ⟨e, he, a, ha, hw⟩ := hdec w w.2
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hψ₂, QuotientGroup.eq, mem_subgroupOf]
    change a⁻¹ * w ∈ E
    rw [hw, hS.E_comm_A2 he ha, inv_mul_cancel_left]
    exact he
  let φ₁ := (QuotientGroup.quotientMulEquivOfEq hker₁.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ₁ hsurj₁)
  let φ₂ := (QuotientGroup.quotientMulEquivOfEq hker₂.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ₂ hsurj₂)
  have hform : ∀ (d : miyamotoD2G h L η t Q) (a : miyamotoA2G h L η), ∀ e ∈ E,
      (d : G)⁻¹ * t * d * t = e * a → (φ₁.trans φ₂.symm) (QuotientGroup.mk d) =
        QuotientGroup.mk a := by
    intro d a e he hda
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
    change ψ₁ d = ψ₂ a
    rw [hψ₁, hψ₂, QuotientGroup.eq, mem_subgroupOf]
    change ((d : G)⁻¹ * t * d * t)⁻¹ * a ∈ E
    rw [hda, show (e * (a : G))⁻¹ * a = (a : G)⁻¹ * e⁻¹ * a by group]
    exact hconj a a.2 _ (inv_mem he)
  refine ⟨φ₁.trans φ₂.symm, hform, fun c hc d a hd ha hda => ?_⟩
  have hcH : c ∈ normalizer (CFSG.centerIn Q : Set G) := by
    rw [← hS.sec3_2.2.2.2.2]
    exact hc.1
  obtain ⟨e₀, he₀, a₀, ha₀, hd₀⟩ := hdec _ (hS.crossed_mem_EA2_of_mem_D2 d.2)
  have h1 : QuotientGroup.mk (⟨a₀, ha₀⟩ : miyamotoA2G h L η) =
      (QuotientGroup.mk a : miyamotoA2G h L η ⧸ (miyamotoZG h L η).subgroupOf
        (miyamotoA2G h L η)) := by
    rw [← hda, hform d ⟨a₀, ha₀⟩ e₀ he₀ hd₀]
  rw [QuotientGroup.eq, mem_subgroupOf] at h1
  have hce : c * e₀ * c⁻¹ ∈ E := (mem_normalizer_iff.1 (hS.H_le_normalizer_E hcH) e₀).1 he₀
  have hca : c * a₀ * c⁻¹ ∈ miyamotoA2G h L η :=
    (mem_normalizer_iff.1 (hS.H_le_normalizer_A2 hcH) a₀).1 ha₀
  have hcd : (c * d * c⁻¹)⁻¹ * t * (c * d * c⁻¹) * t = (c * e₀ * c⁻¹) * (c * a₀ * c⁻¹) := by
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (mem_centralizer_singleton_iff.1 hc.2),
      hd₀]
    group
  rw [hform ⟨c * d * c⁻¹, hd⟩ ⟨c * a₀ * c⁻¹, hca⟩ _ hce hcd, QuotientGroup.eq, mem_subgroupOf]
  change (c * a₀ * c⁻¹)⁻¹ * (c * a * c⁻¹) ∈ miyamotoZG h L η
  rw [show (c * a₀ * c⁻¹)⁻¹ * (c * a * c⁻¹) = c * (a₀⁻¹ * a) * c⁻¹ by group]
  exact (mem_normalizer_iff.1 (hS.H_le_normalizer_ZP hcH) _).1 h1

theorem sec3_8 (hS : Setting h L η t Q T) :
    (∀ g ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoB2 h L η t : Subgroup G) : Set G),
        ∃ c ∈ normalizer (miyamotoB2 h L η t : Set G) ⊓ centralizer ({t} : Set G),
          ∃ d ∈ miyamotoD2G h L η t Q, g = c * d) ∧
      Nat.card (miyamotoD2G h L η t Q) = 2 * (2 ^ f) ^ 10 ∧
      miyamotoEG h L η Q ⊔ miyamotoB2 h L η t ≤ miyamotoD2G h L η t Q ∧
      miyamotoD2G h L η t Q ⊓ centralizer ({t} : Set G) = miyamotoB2 h L η t ∧
      (∀ d ∈ miyamotoD2G h L η t Q, d⁻¹ * t * d * t ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η) ∧
      (∀ d ∈ miyamotoD2G h L η t Q, d⁻¹ * t * d * t ∈ miyamotoEG h L η Q ↔
        d ∈ miyamotoEG h L η Q ⊔ miyamotoB2 h L η t) ∧
      (∀ a ∈ miyamotoA2G h L η, ∃ d ∈ miyamotoD2G h L η t Q, ∃ e ∈ miyamotoEG h L η Q,
        d⁻¹ * t * d * t = e * a) ∧
      (∀ d ∈ miyamotoD2G h L η t Q, ∀ d' ∈ miyamotoD2G h L η t Q,
        ((d * d')⁻¹ * t * (d * d') * t)⁻¹ * ((d⁻¹ * t * d * t) * (d'⁻¹ * t * d' * t)) ∈
          miyamotoEG h L η Q) ∧
      (∀ c ∈ normalizer (miyamotoB2 h L η t : Set G) ⊓ centralizer ({t} : Set G),
        ∀ d ∈ miyamotoD2G h L η t Q,
          (c * d * c⁻¹)⁻¹ * t * (c * d * c⁻¹) * t = c * (d⁻¹ * t * d * t) * c⁻¹) ∧
      miyamotoEG h L η Q ⊓ miyamotoA2G h L η = miyamotoZG h L η ∧
      ∀ d, d ∈ miyamotoD2G h L η t Q ↔
        d ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoB2 h L η t : Subgroup G) : Set G) ∧
          ∀ w ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η,
            d * w * d⁻¹ * w⁻¹ ∈ miyamotoEG h L η Q :=
  ⟨fun _ hg => hS.normalizer_EB2_eq_mul hg, hS.card_D2, hS.EB2_le_D2, hS.D2_inf_C,
    fun _ hd => hS.crossed_mem_EA2_of_mem_D2 hd, fun _ hd => hS.crossed_mem_E_iff_of_mem_D2 hd,
    fun _ ha => hS.exists_D2_crossed_eq ha, fun _ hd _ hd' => hS.crossed_mul_mod_E hd hd',
    fun _ hc _ _ => CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj
      (mem_centralizer_singleton_iff.1 hc.2), hS.E_inf_A2, fun _ => hS.mem_D2_iff⟩

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
