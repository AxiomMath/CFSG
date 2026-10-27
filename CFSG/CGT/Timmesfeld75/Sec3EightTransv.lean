module

public import CFSG.CGT.Timmesfeld75.Sec3Conj

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def IsTransv (T L : Subgroup G) (a : G) : Prop :=
  a ∈ Subgroup.normalizer (T : Set G) ∧ a * a = 1 ∧ (∀ l ∈ L, a * l = l * a) ∧
    ∀ t ∈ T, ⁅t, a⁆ ∈ L

theorem IsTransv.conj {L : Subgroup G} {a h : G} (ha : IsTransv T L a)
    (hhT : h ∈ Subgroup.normalizer (T : Set G)) (hhL : h ∈ Subgroup.normalizer (L : Set G)) :
    IsTransv T L (h * a * h⁻¹) := by
  obtain ⟨haN, haa, haL, hat⟩ := ha
  have hhi : h⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer _).inv_mem hhT
  have hhiL : h⁻¹ ∈ Subgroup.normalizer (L : Set G) := (Subgroup.normalizer _).inv_mem hhL
  refine ⟨(Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hhT haN) hhi, ?_, ?_,
    ?_⟩
  · calc h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
      _ = 1 := by rw [haa]; group
  · intro l hl
    have hl' : h⁻¹ * l * h⁻¹⁻¹ ∈ L := conj_mem_of_mem_normalizer hhiL hl
    have e := haL _ (by simpa using hl')
    calc h * a * h⁻¹ * l = h * (a * (h⁻¹ * l * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * l * h) * a) * h⁻¹ := by rw [e]
      _ = l * (h * a * h⁻¹) := by group
  · intro t ht
    have ht' : h⁻¹ * t * h⁻¹⁻¹ ∈ T := conj_mem_of_mem_normalizer hhi ht
    have h1 := hat _ (by simpa using ht')
    have h2 := conj_mem_of_mem_normalizer hhL h1
    have e : h * ⁅h⁻¹ * t * h, a⁆ * h⁻¹ = ⁅t, h * a * h⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [← e]
    exact h2

theorem IsTransv.mul_mul_comm {L : Subgroup G} (hL : IsElemAbelian 2 L) {a b : G}
    (ha : IsTransv T L a) (hb : IsTransv T L b) {t : G} (ht : t ∈ T) :
    (a * b * (a * b)) * t = t * (a * b * (a * b)) := by
  obtain ⟨-, -, haL, hat⟩ := ha
  obtain ⟨-, -, hbL, hbt⟩ := hb
  have hla : ⁅t, a⁆ ∈ L := hat t ht
  have hlb : ⁅t, b⁆ ∈ L := hbt t ht
  have hc : ⁅t, b⁆⁻¹ * ⁅t, a⁆⁻¹ ∈ L := L.mul_mem (L.inv_mem hlb) (L.inv_mem hla)
  have hcc : (⁅t, b⁆⁻¹ * ⁅t, a⁆⁻¹) * (⁅t, b⁆⁻¹ * ⁅t, a⁆⁻¹) = 1 := elemAbelian_mul_self hL hc
  have hcent : ∀ x ∈ L, a * b * x * (a * b)⁻¹ = x := by
    intro x hx
    have h1 : a * x * a⁻¹ = x := by rw [haL x hx]; group
    have h2 : b * x * b⁻¹ = x := by rw [hbL x hx]; group
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = x := by rw [h2, h1]
  have hact : a * b * t * (a * b)⁻¹ = (⁅t, b⁆⁻¹ * ⁅t, a⁆⁻¹) * t := by
    have ea : a * t * a⁻¹ = ⁅t, a⁆⁻¹ * t := by
      simp only [commutatorElement_def]
      group
    have eb : b * t * b⁻¹ = ⁅t, b⁆⁻¹ * t := by
      simp only [commutatorElement_def]
      group
    have h1 : a * ⁅t, b⁆⁻¹ * a⁻¹ = ⁅t, b⁆⁻¹ := by rw [haL _ (L.inv_mem hlb)]; group
    calc a * b * t * (a * b)⁻¹ = a * (b * t * b⁻¹) * a⁻¹ := by group
      _ = a * (⁅t, b⁆⁻¹ * t) * a⁻¹ := by rw [eb]
      _ = (a * ⁅t, b⁆⁻¹ * a⁻¹) * (a * t * a⁻¹) := by group
      _ = ⁅t, b⁆⁻¹ * (⁅t, a⁆⁻¹ * t) := by rw [h1, ea]
      _ = (⁅t, b⁆⁻¹ * ⁅t, a⁆⁻¹) * t := by group
  set c : G := ⁅t, b⁆⁻¹ * ⁅t, a⁆⁻¹ with hcdef
  have hsq : a * b * (a * b) * t * (a * b * (a * b))⁻¹ = t := by
    calc a * b * (a * b) * t * (a * b * (a * b))⁻¹
        = (a * b) * ((a * b) * t * (a * b)⁻¹) * (a * b)⁻¹ := by group
      _ = (a * b) * (c * t) * (a * b)⁻¹ := by rw [hact]
      _ = ((a * b) * c * (a * b)⁻¹) * ((a * b) * t * (a * b)⁻¹) := by group
      _ = c * (c * t) := by rw [hcent c hc, hact]
      _ = (c * c) * t := by group
      _ = t := by rw [hcc, one_mul]
  have := mul_inv_eq_iff_eq_mul.1 hsq
  exact this

structure IsLElt (T T₁ : Subgroup G) (a : G) : Prop where
  transv : IsTransv T (normIn T T₁) a
  ne : a ≠ 1
  cent : ∀ t ∈ T, a * t = t * a → t ∈ normIn T T₁

theorem Cfg.isTransv_of_mem_normIn (c : Cfg T T₁) {b : G} (hb : b ∈ normIn T₁ T) :
    IsTransv T (normIn T T₁) b := by
  obtain ⟨hbT₁, hbN⟩ := mem_normIn.1 hb
  exact ⟨hbN, elemAbelian_mul_self c.wc₁.1 hbT₁, fun l hl => (c.comm_L_L₁ hl hb).symm,
    fun t ht => c.comm_mem_normIn ht hb⟩

theorem Sec3.isLElt_of_mem_normIn (hS : Sec3 T T₁) {b : G} (hb : b ∈ normIn T₁ T) (hb1 : b ≠ 1) :
    IsLElt T T₁ b := by
  have c := hS.cfg
  obtain ⟨hbT₁, -⟩ := mem_normIn.1 hb
  refine ⟨c.isTransv_of_mem_normIn hb, hb1, fun t ht hbt => ?_⟩
  by_contra htL
  have htM : t ∉ cfgM T T₁ := fun hM => htL (by rw [← c.inf_cfgM]; exact ⟨ht, hM⟩)
  have h1 := c.cfgM_inf_centralizer ht htM
  have hb2 : b ∈ cfgM T T₁ ⊓ Subgroup.centralizer ({t} : Set G) :=
    ⟨Cfg.normIn_le_cfgM_right T T₁ hb,
      Subgroup.mem_centralizer_singleton_iff.2 hbt⟩
  rw [h1] at hb2
  have h3 : b ∈ T ⊓ T₁ := ⟨(normIn_le _ _ hb2), hbT₁⟩
  rw [c.inf, Subgroup.mem_bot] at h3
  exact hb1 h3

theorem IsLElt.conj {a h : G} (ha : IsLElt T T₁ a) (hhT : h ∈ Subgroup.normalizer (T : Set G))
    (hhL : h ∈ Subgroup.normalizer (normIn T T₁ : Set G)) : IsLElt T T₁ (h * a * h⁻¹) := by
  refine ⟨ha.transv.conj hhT hhL, fun h1 => ha.ne ?_, fun t ht hct => ?_⟩
  · have : a = h⁻¹ * (h * a * h⁻¹) * h := by group
    rw [this, h1]
    group
  · have hhi : h⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer _).inv_mem hhT
    have ht' : h⁻¹ * t * h⁻¹⁻¹ ∈ T := conj_mem_of_mem_normalizer hhi ht
    have ht'' : h⁻¹ * t * h ∈ T := by simpa using ht'
    have hc : a * (h⁻¹ * t * h) = (h⁻¹ * t * h) * a := by
      have e : (h * a * h⁻¹) * t = t * (h * a * h⁻¹) := hct
      calc a * (h⁻¹ * t * h) = h⁻¹ * ((h * a * h⁻¹) * t) * h := by group
        _ = h⁻¹ * (t * (h * a * h⁻¹)) * h := by rw [e]
        _ = (h⁻¹ * t * h) * a := by group
    have hL := conj_mem_of_mem_normalizer hhL (ha.cent _ ht'' hc)
    have e2 : h * (h⁻¹ * t * h) * h⁻¹ = t := by group
    rwa [e2] at hL

theorem IsLElt.not_centralizes [Finite G] (hS : Sec3 T T₁) {a : G} (ha : IsLElt T T₁ a) :
    ¬ ∀ t ∈ T, a * t = t * a := by
  intro hall
  apply hS.not_le_cfgM
  intro t ht
  exact Cfg.normIn_le_cfgM_left T T₁ (ha.cent t ht (hall t ht))

theorem Sec3.not_centralizes_of_mem_normIn [Finite G] (hS : Sec3 T T₁) {b : G}
    (hb : b ∈ normIn T₁ T) (hb1 : b ≠ 1) : ¬ ∀ t ∈ T, b * t = t * b :=
  (hS.isLElt_of_mem_normIn hb hb1).not_centralizes hS

end CFSG.CGT.Timmesfeld75
