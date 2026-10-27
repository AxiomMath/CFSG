module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFAct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Core

variable {Y : Type*} [Group Y]

theorem mem_sup2 {H K : Subgroup Y} (hc : Commutes H K) {x : Y} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let S : Subgroup Y :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hc h₂ hh₂ k₁ hk₁]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        calc (h * k)⁻¹ = k⁻¹ * h⁻¹ := by group
          _ = h⁻¹ * k⁻¹ := by
              have := hc h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)
              exact this.symm }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
  exact hle hx

theorem commutes_sup {A B C : Subgroup Y} (hA : Commutes A C) (hB : Commutes B C) :
    Commutes (A ⊔ B) C := by
  intro x hx y hy
  have : A ⊔ B ≤ Subgroup.centralizer (C : Set Y) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]; intro c hc; exact (hA a ha c hc).symm
    · rw [Subgroup.mem_centralizer_iff]; intro c hc; exact (hB b hb c hc).symm
  have h := Subgroup.mem_centralizer_iff.mp (this hx) y hy
  exact h.symm

theorem mem_sup4 {J₀ J₁ J₂ J₃ : Subgroup Y} (h01 : Commutes J₀ J₁) (h02 : Commutes J₀ J₂)
    (h03 : Commutes J₀ J₃) (h12 : Commutes J₁ J₂) (h13 : Commutes J₁ J₃) (h23 : Commutes J₂ J₃)
    {x : Y} (hx : x ∈ J₀ ⊔ J₁ ⊔ J₂ ⊔ J₃) :
    ∃ p₀ ∈ J₀, ∃ p₁ ∈ J₁, ∃ p₂ ∈ J₂, ∃ p₃ ∈ J₃, x = p₀ * p₁ * p₂ * p₃ := by
  obtain ⟨u, hu, p₃, hp₃, rfl⟩ := mem_sup2 (commutes_sup (commutes_sup h03 h13) h23) hx
  obtain ⟨v, hv, p₂, hp₂, rfl⟩ := mem_sup2 (commutes_sup h02 h12) hu
  obtain ⟨p₀, hp₀, p₁, hp₁, rfl⟩ := mem_sup2 h01 hv
  exact ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, p₃, hp₃, rfl⟩


theorem prod4_sq_comm {p q r u : Y} (hpq : Commute p q) (hpr : Commute p r) (hpu : Commute p u)
    (hqr : Commute q r) (hqu : Commute q u) (hru : Commute r u) :
    (p * q * r * u) * (p * q * r * u) = (p * p) * (q * q) * (r * r) * (u * u) := by
  have h1 : Commute (p * q * r) u := (hpu.mul_left hqu).mul_left hru
  have h2 : Commute (p * q) r := hpr.mul_left hqr
  have := h1.mul_pow 2
  rw [h2.mul_pow, hpq.mul_pow] at this
  simpa [sq] using this

theorem indep4 {s : Y} {J : Fin 4 → Subgroup Y} (hq : ∀ i, Q8Facts (J i) s)
    (hcom : ∀ i j, i ≠ j → Commutes (J i) (J j)) {g : Fin 4 → Y} (hg : ∀ i, g i ∈ J i)
    (hp : g 0 * g 1 * g 2 * g 3 = 1 ∨ g 0 * g 1 * g 2 * g 3 = s) (i : Fin 4) :
    g i = 1 ∨ g i = s := by
  have hcen : ∀ i, ∀ m ∈ J i, m * (g 0 * g 1 * g 2 * g 3) = (g 0 * g 1 * g 2 * g 3) * m := by
    intro i m hm
    rcases hp with e | e
    · rw [e, one_mul, mul_one]
    · rw [e]; exact ((hq i).z_central m hm).symm
  have hcr : ∀ i j, j ≠ i → ∀ m ∈ J i, m * g j = g j * m := fun i j hj m hm =>
    hcom i j (Ne.symm hj) m hm _ (hg j)
  have c2 : ∀ i j k, j ≠ i → k ≠ i → ∀ m ∈ J i, m * (g j * g k) = (g j * g k) * m :=
    fun i j k hj hk m hm => by
      calc m * (g j * g k) = (m * g j) * g k := (mul_assoc _ _ _).symm
        _ = (g j * m) * g k := by rw [hcr i j hj m hm]
        _ = g j * (m * g k) := mul_assoc _ _ _
        _ = g j * (g k * m) := by rw [hcr i k hk m hm]
        _ = (g j * g k) * m := (mul_assoc _ _ _).symm
  have c3 : ∀ i j k l, j ≠ i → k ≠ i → l ≠ i → ∀ m ∈ J i,
      m * (g j * g k * g l) = (g j * g k * g l) * m := fun i j k l hj hk hl m hm => by
    calc m * (g j * g k * g l) = (m * (g j * g k)) * g l := (mul_assoc _ _ _).symm
      _ = ((g j * g k) * m) * g l := by rw [c2 i j k hj hk m hm]
      _ = (g j * g k) * (m * g l) := mul_assoc _ _ _
      _ = (g j * g k) * (g l * m) := by rw [hcr i l hl m hm]
      _ = (g j * g k * g l) * m := (mul_assoc _ _ _).symm
  have h0 : ∀ m ∈ J 0, g 0 * m = m * g 0 := fun m hm =>
    (comm_mid (m := m) (Pl := 1) (g := g 0) (Pr := g 1 * g 2 * g 3) (by simp)
      (c3 0 1 2 3 (by decide) (by decide) (by decide) m hm)
      (by rw [show 1 * g 0 * (g 1 * g 2 * g 3) = g 0 * g 1 * g 2 * g 3 by group]; exact hcen 0 m hm)).symm
  have h1 : ∀ m ∈ J 1, g 1 * m = m * g 1 := fun m hm =>
    (comm_mid (m := m) (Pl := g 0) (g := g 1) (Pr := g 2 * g 3) (hcr 1 0 (by decide) m hm)
      (c2 1 2 3 (by decide) (by decide) m hm)
      (by rw [show g 0 * g 1 * (g 2 * g 3) = g 0 * g 1 * g 2 * g 3 by group]; exact hcen 1 m hm)).symm
  have h2 : ∀ m ∈ J 2, g 2 * m = m * g 2 := fun m hm =>
    (comm_mid (m := m) (Pl := g 0 * g 1) (g := g 2) (Pr := g 3) (c2 2 0 1 (by decide) (by decide) m hm)
      (hcr 2 3 (by decide) m hm) (hcen 2 m hm)).symm
  have h3 : ∀ m ∈ J 3, g 3 * m = m * g 3 := fun m hm =>
    (comm_mid (m := m) (Pl := g 0 * g 1 * g 2) (g := g 3) (Pr := 1)
      (c3 3 0 1 2 (by decide) (by decide) (by decide) m hm) (by simp)
      (by rw [show g 0 * g 1 * g 2 * g 3 * 1 = g 0 * g 1 * g 2 * g 3 by group]; exact hcen 3 m hm)).symm
  have key : ∀ i : Fin 4, ∀ m ∈ J i, g i * m = m * g i := by
    intro i
    fin_cases i
    exacts [h0, h1, h2, h3]
  exact (hq i).center _ (hg i) (key i)


theorem c5_core {s b : Y} {J : Fin 4 → Subgroup Y} (hq : ∀ i, Q8Facts (J i) s)
    (hcom : ∀ i j, i ≠ j → Commutes (J i) (J j)) (hb2 : b * b = 1) (hbs : b * s = s * b)
    (hb0 : ∀ m ∈ J 0, b * m * b⁻¹ ∈ J 1) (hb1 : ∀ m ∈ J 1, b * m * b⁻¹ ∈ J 0)
    (hb2' : ∀ m ∈ J 2, b * m * b⁻¹ ∈ J 3) (hb3 : ∀ m ∈ J 3, b * m * b⁻¹ ∈ J 2) {p : Y}
    (hp : p ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3) (hq2 : (b * p) * (b * p) = 1) :
    ∃ r ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3, b * p = r * b * r⁻¹ ∨ b * p = r * b * r⁻¹ * s := by
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, p₃, hp₃, rfl⟩ :=
    mem_sup4 (hcom 0 1 (by decide)) (hcom 0 2 (by decide)) (hcom 0 3 (by decide))
      (hcom 1 2 (by decide)) (hcom 1 3 (by decide)) (hcom 2 3 (by decide)) hp
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hcm : ∀ i j, i ≠ j → ∀ m ∈ J i, ∀ m' ∈ J j, m * m' = m' * m := fun i j hij m hm m' hm' =>
    hcom i j hij m hm m' hm'
  obtain ⟨A₀, hA₀⟩ : ∃ A₀, A₀ = b * p₁ * b⁻¹ := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = b * p₀ * b⁻¹ := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, A₂ = b * p₃ * b⁻¹ := ⟨_, rfl⟩
  obtain ⟨A₃, hA₃⟩ : ∃ A₃, A₃ = b * p₂ * b⁻¹ := ⟨_, rfl⟩
  have mA₀ : A₀ ∈ J 0 := hA₀ ▸ hb1 p₁ hp₁
  have mA₁ : A₁ ∈ J 1 := hA₁ ▸ hb0 p₀ hp₀
  have mA₂ : A₂ ∈ J 2 := hA₂ ▸ hb3 p₃ hp₃
  have mA₃ : A₃ ∈ J 3 := hA₃ ▸ hb2' p₂ hp₂
  have e1 : b * (p₀ * p₁ * p₂ * p₃) * b⁻¹ = A₁ * A₀ * A₃ * A₂ := by
    rw [hA₀, hA₁, hA₂, hA₃]; group
  have h1 : (b * (p₀ * p₁ * p₂ * p₃) * b⁻¹) * (p₀ * p₁ * p₂ * p₃) = 1 := by
    calc (b * (p₀ * p₁ * p₂ * p₃) * b⁻¹) * (p₀ * p₁ * p₂ * p₃)
        = (b * (p₀ * p₁ * p₂ * p₃) * b⁻¹) * (b * b) * (p₀ * p₁ * p₂ * p₃) := by rw [hb2, mul_one]
      _ = (b * (p₀ * p₁ * p₂ * p₃)) * (b * (p₀ * p₁ * p₂ * p₃)) := by group
      _ = 1 := hq2
  have hAA : A₁ * A₀ * A₃ * A₂ = A₀ * A₁ * A₂ * A₃ := by
    have c01 : A₁ * A₀ = A₀ * A₁ := hcm 1 0 (by decide) _ mA₁ _ mA₀
    have c23 : A₃ * A₂ = A₂ * A₃ := hcm 3 2 (by decide) _ mA₃ _ mA₂
    calc A₁ * A₀ * A₃ * A₂ = (A₁ * A₀) * (A₃ * A₂) := by group
      _ = (A₀ * A₁) * (A₂ * A₃) := by rw [c01, c23]
      _ = A₀ * A₁ * A₂ * A₃ := by group
  rw [e1, hAA] at h1
  have h2 := prod4_mul2 (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) (B₀ := p₀) (B₁ := p₁) (B₂ := p₂)
    (B₃ := p₃) (hcm 1 0 (by decide) _ mA₁ _ hp₀) (hcm 2 0 (by decide) _ mA₂ _ hp₀)
    (hcm 2 1 (by decide) _ mA₂ _ hp₁) (hcm 3 0 (by decide) _ mA₃ _ hp₀)
    (hcm 3 1 (by decide) _ mA₃ _ hp₁) (hcm 3 2 (by decide) _ mA₃ _ hp₂)
  rw [h1] at h2
  have hg : ∀ k, ((![A₀, A₁, A₂, A₃] k) * (![p₀, p₁, p₂, p₃] k)) ∈ J k := fun k => by
    fin_cases k
    · exact (J 0).mul_mem mA₀ hp₀
    · exact (J 1).mul_mem mA₁ hp₁
    · exact (J 2).mul_mem mA₂ hp₂
    · exact (J 3).mul_mem mA₃ hp₃
  have hind := indep4 hq hcom (g := fun k => (![A₀, A₁, A₂, A₃] k) * (![p₀, p₁, p₂, p₃] k)) hg
    (Or.inl (by simpa using h2.symm))
  have hc₁ : A₁ * p₁ = 1 ∨ A₁ * p₁ = s := hind 1
  have hc₃ : A₃ * p₃ = 1 ∨ A₃ * p₃ = s := hind 3
  obtain ⟨c₁, hc₁def⟩ : ∃ c, c = A₁ * p₁ := ⟨_, rfl⟩
  obtain ⟨c₃, hc₃def⟩ : ∃ c, c = A₃ * p₃ := ⟨_, rfl⟩
  rw [← hc₁def] at hc₁
  rw [← hc₃def] at hc₃
  have hs2 : s * s = 1 := (hq 0).z_sq
  have hcs : ∀ c, (c = 1 ∨ c = s) → c * b = b * c := by
    rintro c (rfl | rfl)
    · simp
    · exact hbs.symm
  have hcJ : ∀ c, (c = 1 ∨ c = s) → ∀ k, ∀ m ∈ J k, c * m = m * c := by
    rintro c (rfl | rfl) k m hm
    · simp
    · exact (hq k).z_central m hm
  have eA₁ : A₁ = c₁ * p₁⁻¹ := by rw [hc₁def]; group
  have eA₃ : A₃ = c₃ * p₃⁻¹ := by rw [hc₃def]; group
  have bb : ∀ x, b * (b * x * b⁻¹) = x * b := fun x => by
    calc b * (b * x * b⁻¹) = (b * b) * x * b⁻¹ := by group
      _ = x * b⁻¹ := by rw [hb2, one_mul]
      _ = x * b := by rw [hbi]
  have hbA₀ : b * A₀⁻¹ = p₁⁻¹ * b := by
    have : A₀⁻¹ = b * p₁⁻¹ * b⁻¹ := by rw [hA₀]; group
    rw [this, bb]
  have hbA₂ : b * A₂⁻¹ = p₃⁻¹ * b := by
    have : A₂⁻¹ = b * p₃⁻¹ * b⁻¹ := by rw [hA₂]; group
    rw [this, bb]
  have hbp : b * (p₀ * p₁ * p₂ * p₃) = (A₁ * A₀ * A₃ * A₂) * b := by
    rw [← e1]; group
  have hrb : (A₀ * A₂) * b * (A₀ * A₂)⁻¹ = (A₀ * A₂ * p₃⁻¹ * p₁⁻¹) * b := by
    calc (A₀ * A₂) * b * (A₀ * A₂)⁻¹ = A₀ * A₂ * (b * A₂⁻¹ * A₀⁻¹) := by group
      _ = A₀ * A₂ * (p₃⁻¹ * b * A₀⁻¹) := by rw [hbA₂]
      _ = A₀ * A₂ * (p₃⁻¹ * (b * A₀⁻¹)) := by group
      _ = A₀ * A₂ * (p₃⁻¹ * (p₁⁻¹ * b)) := by rw [hbA₀]
      _ = (A₀ * A₂ * p₃⁻¹ * p₁⁻¹) * b := by group
  have hP0 : J 0 ≤ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hP2 : J 2 ≤ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := le_sup_right.trans le_sup_left
  refine ⟨A₀ * A₂, Subgroup.mul_mem _ (hP0 mA₀) (hP2 mA₂), ?_⟩
  have hp₁i : p₁⁻¹ ∈ J 1 := (J 1).inv_mem hp₁
  have hp₃i : p₃⁻¹ ∈ J 3 := (J 3).inv_mem hp₃
  have key : A₁ * A₀ * A₃ * A₂ = (c₁ * c₃) * (A₀ * A₂ * p₃⁻¹ * p₁⁻¹) := by
    have x1 : p₁⁻¹ * A₀ = A₀ * p₁⁻¹ := hcm 1 0 (by decide) _ hp₁i _ mA₀
    have x2 : p₃⁻¹ * A₂ = A₂ * p₃⁻¹ := hcm 3 2 (by decide) _ hp₃i _ mA₂
    have x3 : p₁⁻¹ * A₂ = A₂ * p₁⁻¹ := hcm 1 2 (by decide) _ hp₁i _ mA₂
    have x4 : p₁⁻¹ * p₃⁻¹ = p₃⁻¹ * p₁⁻¹ := hcm 1 3 (by decide) _ hp₁i _ hp₃i
    have x5 : c₃ * p₁⁻¹ = p₁⁻¹ * c₃ := hcJ c₃ hc₃ 1 _ hp₁i
    have x6 : c₃ * A₀ = A₀ * c₃ := hcJ c₃ hc₃ 0 _ mA₀
    calc A₁ * A₀ * A₃ * A₂ = c₁ * p₁⁻¹ * A₀ * (c₃ * p₃⁻¹) * A₂ := by rw [eA₁, eA₃]
      _ = c₁ * (p₁⁻¹ * A₀ * c₃) * p₃⁻¹ * A₂ := by group
      _ = c₁ * (c₃ * p₁⁻¹ * A₀) * p₃⁻¹ * A₂ := by
          rw [show p₁⁻¹ * A₀ * c₃ = c₃ * p₁⁻¹ * A₀ by
            rw [mul_assoc, ← x6, ← mul_assoc, ← x5, mul_assoc]]
      _ = c₁ * c₃ * (p₁⁻¹ * A₀) * (p₃⁻¹ * A₂) := by group
      _ = c₁ * c₃ * (A₀ * p₁⁻¹) * (A₂ * p₃⁻¹) := by rw [x1, x2]
      _ = c₁ * c₃ * A₀ * (p₁⁻¹ * A₂) * p₃⁻¹ := by group
      _ = c₁ * c₃ * A₀ * (A₂ * p₁⁻¹) * p₃⁻¹ := by rw [x3]
      _ = c₁ * c₃ * (A₀ * A₂) * (p₁⁻¹ * p₃⁻¹) := by group
      _ = c₁ * c₃ * (A₀ * A₂) * (p₃⁻¹ * p₁⁻¹) := by rw [x4]
      _ = (c₁ * c₃) * (A₀ * A₂ * p₃⁻¹ * p₁⁻¹) := by group
  have hcc : (c₁ * c₃) = 1 ∨ (c₁ * c₃) = s := by
    rcases hc₁ with e | e <;> rcases hc₃ with f | f <;> rw [e, f]
    · left; simp
    · right; simp
    · right; simp
    · left; exact hs2
  have hcc' : ∀ g ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3, True := fun _ _ => trivial
  have hcr : (c₁ * c₃) * ((A₀ * A₂) * b * (A₀ * A₂)⁻¹) = ((A₀ * A₂) * b * (A₀ * A₂)⁻¹) * (c₁ * c₃) := by
    rcases hcc with e | e
    · rw [e]; simp
    · rw [e]
      have hA₀c : s * A₀ = A₀ * s := (hq 0).z_central _ mA₀
      have hA₂c : s * A₂ = A₂ * s := (hq 2).z_central _ mA₂
      have hA₀i : s * A₀⁻¹ = A₀⁻¹ * s := (Commute.inv_right (show Commute s A₀ from hA₀c)).eq
      have hA₂i : s * A₂⁻¹ = A₂⁻¹ * s := (Commute.inv_right (show Commute s A₂ from hA₂c)).eq
      calc s * (A₀ * A₂ * b * (A₀ * A₂)⁻¹) = s * A₀ * A₂ * b * A₂⁻¹ * A₀⁻¹ := by group
        _ = A₀ * (s * A₂) * b * A₂⁻¹ * A₀⁻¹ := by rw [hA₀c]; group
        _ = A₀ * A₂ * (s * b) * A₂⁻¹ * A₀⁻¹ := by rw [hA₂c]; group
        _ = A₀ * A₂ * (b * s) * A₂⁻¹ * A₀⁻¹ := by rw [hbs.symm]
        _ = A₀ * A₂ * b * (s * A₂⁻¹) * A₀⁻¹ := by group
        _ = A₀ * A₂ * b * (A₂⁻¹ * s) * A₀⁻¹ := by rw [hA₂i]
        _ = A₀ * A₂ * b * A₂⁻¹ * (s * A₀⁻¹) := by group
        _ = A₀ * A₂ * b * A₂⁻¹ * (A₀⁻¹ * s) := by rw [hA₀i]
        _ = (A₀ * A₂ * b * (A₀ * A₂)⁻¹) * s := by group
  have hfin : b * (p₀ * p₁ * p₂ * p₃) = ((A₀ * A₂) * b * (A₀ * A₂)⁻¹) * (c₁ * c₃) := by
    rw [hbp, key, hcr.symm, hrb]; group
  rcases hcc with e | e
  · left; rw [hfin, e, mul_one]
  · right; rw [hfin, e]


theorem noconj_core {s b : Y} {J : Fin 4 → Subgroup Y} (hq : ∀ i, Q8Facts (J i) s)
    (hcom : ∀ i j, i ≠ j → Commutes (J i) (J j)) (hb2 : b * b = 1) (hbs : b * s = s * b)
    (hb0 : ∀ m ∈ J 0, b * m * b⁻¹ ∈ J 1) (hb1 : ∀ m ∈ J 1, b * m * b⁻¹ ∈ J 0)
    (hb2' : ∀ m ∈ J 2, b * m * b⁻¹ ∈ J 3) (hb3 : ∀ m ∈ J 3, b * m * b⁻¹ ∈ J 2) {p : Y}
    (hp : p ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3) : p * b * p⁻¹ ≠ b * s := by
  intro hpb
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, p₃, hp₃, rfl⟩ :=
    mem_sup4 (hcom 0 1 (by decide)) (hcom 0 2 (by decide)) (hcom 0 3 (by decide))
      (hcom 1 2 (by decide)) (hcom 1 3 (by decide)) (hcom 2 3 (by decide)) hp
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hcm : ∀ i j, i ≠ j → ∀ m ∈ J i, ∀ m' ∈ J j, m * m' = m' * m := fun i j hij m hm m' hm' =>
    hcom i j hij m hm m' hm'
  obtain ⟨A₀, hA₀⟩ : ∃ A₀, A₀ = b * p₁ * b⁻¹ := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = b * p₀ * b⁻¹ := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, A₂ = b * p₃ * b⁻¹ := ⟨_, rfl⟩
  obtain ⟨A₃, hA₃⟩ : ∃ A₃, A₃ = b * p₂ * b⁻¹ := ⟨_, rfl⟩
  have mA₀ : A₀ ∈ J 0 := hA₀ ▸ hb1 p₁ hp₁
  have mA₁ : A₁ ∈ J 1 := hA₁ ▸ hb0 p₀ hp₀
  have mA₂ : A₂ ∈ J 2 := hA₂ ▸ hb3 p₃ hp₃
  have mA₃ : A₃ ∈ J 3 := hA₃ ▸ hb2' p₂ hp₂
  have e1 : b * (p₀ * p₁ * p₂ * p₃) * b⁻¹ = A₁ * A₀ * A₃ * A₂ := by
    rw [hA₀, hA₁, hA₂, hA₃]; group
  have h1 : (p₀ * p₁ * p₂ * p₃) * (A₁ * A₀ * A₃ * A₂)⁻¹ = s := by
    rw [← e1]
    calc (p₀ * p₁ * p₂ * p₃) * (b * (p₀ * p₁ * p₂ * p₃) * b⁻¹)⁻¹
        = (p₀ * p₁ * p₂ * p₃) * b * (p₀ * p₁ * p₂ * p₃)⁻¹ * b⁻¹ := by group
      _ = (b * s) * b⁻¹ := by rw [hpb]
      _ = s := by rw [hbs]; group
  have hAA : A₁ * A₀ * A₃ * A₂ = A₀ * A₁ * A₂ * A₃ := by
    have c01 : A₁ * A₀ = A₀ * A₁ := hcm 1 0 (by decide) _ mA₁ _ mA₀
    have c23 : A₃ * A₂ = A₂ * A₃ := hcm 3 2 (by decide) _ mA₃ _ mA₂
    calc A₁ * A₀ * A₃ * A₂ = (A₁ * A₀) * (A₃ * A₂) := by group
      _ = (A₀ * A₁) * (A₂ * A₃) := by rw [c01, c23]
      _ = A₀ * A₁ * A₂ * A₃ := by group
  rw [hAA] at h1
  have hinv : (A₀ * A₁ * A₂ * A₃)⁻¹ = A₀⁻¹ * A₁⁻¹ * A₂⁻¹ * A₃⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [prod4_mul2 (hcm 1 0 (by decide) _ mA₁ _ ((J 0).inv_mem mA₀))
      (hcm 2 0 (by decide) _ mA₂ _ ((J 0).inv_mem mA₀))
      (hcm 2 1 (by decide) _ mA₂ _ ((J 1).inv_mem mA₁))
      (hcm 3 0 (by decide) _ mA₃ _ ((J 0).inv_mem mA₀))
      (hcm 3 1 (by decide) _ mA₃ _ ((J 1).inv_mem mA₁))
      (hcm 3 2 (by decide) _ mA₃ _ ((J 2).inv_mem mA₂))]
    simp
  rw [hinv] at h1
  have h2 := prod4_mul2 (A₀ := p₀) (A₁ := p₁) (A₂ := p₂) (A₃ := p₃) (B₀ := A₀⁻¹) (B₁ := A₁⁻¹)
    (B₂ := A₂⁻¹) (B₃ := A₃⁻¹)
    (hcm 1 0 (by decide) _ hp₁ _ ((J 0).inv_mem mA₀))
    (hcm 2 0 (by decide) _ hp₂ _ ((J 0).inv_mem mA₀))
    (hcm 2 1 (by decide) _ hp₂ _ ((J 1).inv_mem mA₁))
    (hcm 3 0 (by decide) _ hp₃ _ ((J 0).inv_mem mA₀))
    (hcm 3 1 (by decide) _ hp₃ _ ((J 1).inv_mem mA₁))
    (hcm 3 2 (by decide) _ hp₃ _ ((J 2).inv_mem mA₂))
  rw [h1] at h2
  have hg : ∀ k, ((![p₀, p₁, p₂, p₃] k) * (![A₀⁻¹, A₁⁻¹, A₂⁻¹, A₃⁻¹] k)) ∈ J k := fun k => by
    fin_cases k
    · exact (J 0).mul_mem hp₀ ((J 0).inv_mem mA₀)
    · exact (J 1).mul_mem hp₁ ((J 1).inv_mem mA₁)
    · exact (J 2).mul_mem hp₂ ((J 2).inv_mem mA₂)
    · exact (J 3).mul_mem hp₃ ((J 3).inv_mem mA₃)
  have hind := indep4 hq hcom (g := fun k => (![p₀, p₁, p₂, p₃] k) * (![A₀⁻¹, A₁⁻¹, A₂⁻¹, A₃⁻¹] k)) hg
    (Or.inr (by simpa using h2.symm))
  have hs2 : s * s = 1 := (hq 0).z_sq
  have hcs : ∀ c, (c = 1 ∨ c = s) → c * b = b * c := by
    rintro c (rfl | rfl)
    · simp
    · exact hbs.symm
  have e₀ : p₀ * A₀⁻¹ = 1 ∨ p₀ * A₀⁻¹ = s := hind 0
  have e₁ : p₁ * A₁⁻¹ = 1 ∨ p₁ * A₁⁻¹ = s := hind 1
  have e₂ : p₂ * A₂⁻¹ = 1 ∨ p₂ * A₂⁻¹ = s := hind 2
  have e₃ : p₃ * A₃⁻¹ = 1 ∨ p₃ * A₃⁻¹ = s := hind 3
  have hbb' : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hb2, inv_one]
  have rel01 : b * (p₀ * A₀⁻¹) * b⁻¹ = (p₁ * A₁⁻¹)⁻¹ := by
    calc b * (p₀ * A₀⁻¹) * b⁻¹ = (b * p₀ * b⁻¹) * (b * b) * p₁⁻¹ * (b⁻¹ * b⁻¹) := by
          rw [hA₀]; group
      _ = (p₁ * A₁⁻¹)⁻¹ := by rw [hb2, hbb', mul_one, mul_one, hA₁]; group
  have rel23 : b * (p₂ * A₂⁻¹) * b⁻¹ = (p₃ * A₃⁻¹)⁻¹ := by
    calc b * (p₂ * A₂⁻¹) * b⁻¹ = (b * p₂ * b⁻¹) * (b * b) * p₃⁻¹ * (b⁻¹ * b⁻¹) := by
          rw [hA₂]; group
      _ = (p₃ * A₃⁻¹)⁻¹ := by rw [hb2, hbb', mul_one, mul_one, hA₃]; group
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hinvc : ∀ c, (c = 1 ∨ c = s) → c⁻¹ = c := by
    rintro c (rfl | rfl)
    · simp
    · exact hsi
  have hsq : ∀ c, (c = 1 ∨ c = s) → c * c = 1 := by
    rintro c (rfl | rfl)
    · simp
    · exact hs2
  have fix : ∀ c, (c = 1 ∨ c = s) → b * c * b⁻¹ = c := fun c hc => by
    rw [← hcs c hc]; group
  have q01 : p₁ * A₁⁻¹ = p₀ * A₀⁻¹ := by
    have h := (fix _ e₀).symm.trans rel01
    calc p₁ * A₁⁻¹ = ((p₁ * A₁⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (p₀ * A₀⁻¹)⁻¹ := by rw [← h]
      _ = p₀ * A₀⁻¹ := hinvc _ e₀
  have q23 : p₃ * A₃⁻¹ = p₂ * A₂⁻¹ := by
    have h := (fix _ e₂).symm.trans rel23
    calc p₃ * A₃⁻¹ = ((p₃ * A₃⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (p₂ * A₂⁻¹)⁻¹ := by rw [← h]
      _ = p₂ * A₂⁻¹ := hinvc _ e₂
  have hprod : (p₀ * A₀⁻¹) * (p₁ * A₁⁻¹) * (p₂ * A₂⁻¹) * (p₃ * A₃⁻¹) = s := h2.symm
  rw [q01, q23] at hprod
  have h1' : (p₀ * A₀⁻¹) * (p₀ * A₀⁻¹) * (p₂ * A₂⁻¹) * (p₂ * A₂⁻¹) = 1 := by
    rw [hsq _ e₀, one_mul, hsq _ e₂]
  exact (hq 0).z_ne (by rw [← hprod, h1'])


private theorem fpf_label : ∀ π : Fin 4 → Fin 4, (∀ i, π i ≠ i) → (∀ i, π (π i) = i) →
    ∃ σ : Equiv.Perm (Fin 4), π (σ 0) = σ 1 ∧ π (σ 1) = σ 0 ∧ π (σ 2) = σ 3 ∧ π (σ 3) = σ 2 := by
  decide +kernel

theorem sup4_perm (J : Fin 4 → Subgroup Y) (σ : Equiv.Perm (Fin 4)) :
    J (σ 0) ⊔ J (σ 1) ⊔ J (σ 2) ⊔ J (σ 3) = J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := by
  have hle : ∀ (f : Fin 4 → Subgroup Y) (k : Fin 4), f k ≤ f 0 ⊔ f 1 ⊔ f 2 ⊔ f 3 := by
    intro f k
    fin_cases k
    · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
    · exact (le_sup_right.trans le_sup_left).trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  apply le_antisymm
  · exact sup_le (sup_le (sup_le (hle J _) (hle J _)) (hle J _)) (hle J _)
  · have : ∀ k, J k ≤ J (σ 0) ⊔ J (σ 1) ⊔ J (σ 2) ⊔ J (σ 3) := fun k => by
      have := hle (fun i => J (σ i)) (σ.symm k)
      simpa using this
    exact sup_le (sup_le (sup_le (this 0) (this 1)) (this 2)) (this 3)

theorem c5_gen {s b : Y} {J : Fin 4 → Subgroup Y} (hq : ∀ i, Q8Facts (J i) s)
    (hcom : ∀ i j, i ≠ j → Commutes (J i) (J j)) (hJinj : Function.Injective J) (hb2 : b * b = 1)
    (hbs : b * s = s * b) (hperm : ∀ i, ∃ j, conjSub b (J i) = J j)
    (hmove : ∀ i, conjSub b (J i) ≠ J i) :
    (∀ p ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3, (b * p) * (b * p) = 1 →
      ∃ r ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3, b * p = r * b * r⁻¹ ∨ b * p = r * b * r⁻¹ * s) ∧
    ∀ p ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3, p * b * p⁻¹ ≠ b * s := by
  choose π hπ using hperm
  have hπ1 : ∀ i, π i ≠ i := fun i e => hmove i (by rw [hπ i, e])
  have hπ2 : ∀ i, π (π i) = i := fun i => by
    apply hJinj
    rw [← hπ (π i), ← hπ i, ← conjSub_mul, hb2, conjSub_one]
  obtain ⟨σ, h01, h10, h23, h32⟩ := fpf_label π hπ1 hπ2
  have hmem : ∀ i m, m ∈ J i → b * m * b⁻¹ ∈ J (π i) := fun i m hm => by
    have := conj_mem_conjSub (n := b) hm
    rwa [hπ i] at this
  have hσinj : Function.Injective σ := σ.injective
  have hq' : ∀ i, Q8Facts ((fun k => J (σ k)) i) s := fun i => hq _
  have hcom' : ∀ i j, i ≠ j → Commutes ((fun k => J (σ k)) i) ((fun k => J (σ k)) j) :=
    fun i j hij => hcom _ _ (fun e => hij (hσinj e))
  have hb0 : ∀ m ∈ J (σ 0), b * m * b⁻¹ ∈ J (σ 1) := fun m hm => h01 ▸ hmem _ m hm
  have hb1 : ∀ m ∈ J (σ 1), b * m * b⁻¹ ∈ J (σ 0) := fun m hm => h10 ▸ hmem _ m hm
  have hb2' : ∀ m ∈ J (σ 2), b * m * b⁻¹ ∈ J (σ 3) := fun m hm => h23 ▸ hmem _ m hm
  have hb3 : ∀ m ∈ J (σ 3), b * m * b⁻¹ ∈ J (σ 2) := fun m hm => h32 ▸ hmem _ m hm
  rw [← sup4_perm J σ]
  exact ⟨fun p hp hq2 => c5_core hq' hcom' hb2 hbs hb0 hb1 hb2' hb3 hp hq2,
    fun p hp => noconj_core hq' hcom' hb2 hbs hb0 hb1 hb2' hb3 hp⟩


theorem P_le_centralizer {s : Y} {J : Fin 4 → Subgroup Y} (hq : ∀ i, Q8Facts (J i) s) :
    J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 ≤ Subgroup.centralizer ({s} : Set Y) := by
  have : ∀ i, J i ≤ Subgroup.centralizer ({s} : Set Y) := fun i m hm => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hq i).z_central m hm).symm
  exact sup_le (sup_le (sup_le (this 0) (this 1)) (this 2)) (this 3)

theorem P_normalizes {J : Fin 4 → Subgroup Y} (hcom : ∀ i j, i ≠ j → Commutes (J i) (J j))
    (i : Fin 4) {p : Y} (hp : p ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3) : conjSub p (J i) = J i := by
  have hle : J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 ≤ Subgroup.normalizer (J i : Set Y) := by
    have : ∀ k, J k ≤ Subgroup.normalizer (J i : Set Y) := fun k => by
      by_cases hk : k = i
      · subst hk; exact Subgroup.le_normalizer
      · intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro g
        constructor
        · intro hg
          have e : m * g * m⁻¹ = g := by rw [hcom k i hk m hm g hg]; group
          rw [e]; exact hg
        · intro hg
          have h1 := hcom k i hk m hm _ hg
          have h3 : m * (m * g * m⁻¹) = m * g := by
            calc m * (m * g * m⁻¹) = (m * g * m⁻¹) * m := h1
              _ = m * g := by group
          have h2 : m * g * m⁻¹ = g := mul_left_cancel h3
          rw [h2] at hg
          exact hg
    exact sup_le (sup_le (sup_le (this 0) (this 1)) (this 2)) (this 3)
  exact conjSub_eq_of_mem_normalizer (hle hp)

theorem c7_class {s t b : Y} {J : Fin 4 → Subgroup Y} {N : Subgroup Y}
    (hq : ∀ i, Q8Facts (J i) s) (hcom : ∀ i j, i ≠ j → Commutes (J i) (J j))
    (hJinj : Function.Injective J) (hb2 : b * b = 1) (hbs : b * s = s * b)
    (hperm : ∀ i, ∃ j, conjSub b (J i) = J j) (hmove : ∀ i, conjSub b (J i) ≠ J i)
    (hNC : N ≤ Subgroup.centralizer ({s} : Set Y)) (hPN : J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 ≤ N)
    (hodd : ∀ g ∈ N, ∃ m : ℕ, Odd m ∧ g ^ m ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3)
    (hG : ∀ c ∈ Subgroup.centralizer ({s} : Set Y), c * b = b * c → c * t = t * c) {ℓ : Y}
    (hℓ : ℓ ∈ N) (hcomm : b * ℓ * b⁻¹ * ℓ⁻¹ ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3) :
    ∃ r ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3, ∃ c ∈ N, c * t = t * c ∧ ℓ = r * c := by
  obtain ⟨hc5, hnc⟩ := c5_gen hq hcom hJinj hb2 hbs hperm hmove
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hPs := P_le_centralizer hq
  have hsP : ∀ r ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3, r * s = s * r := fun r hr =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hPs hr))
  have hq2 : (b * (b * ℓ * b⁻¹ * ℓ⁻¹)) * (b * (b * ℓ * b⁻¹ * ℓ⁻¹)) = 1 := by
    have e : b * (b * ℓ * b⁻¹ * ℓ⁻¹) = ℓ * b * ℓ⁻¹ := by
      calc b * (b * ℓ * b⁻¹ * ℓ⁻¹) = (b * b) * ℓ * b⁻¹ * ℓ⁻¹ := by group
        _ = ℓ * b * ℓ⁻¹ := by rw [hb2, one_mul, hbi]
    rw [e]
    calc ℓ * b * ℓ⁻¹ * (ℓ * b * ℓ⁻¹) = ℓ * (b * b) * ℓ⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  obtain ⟨r, hr, hcase⟩ := hc5 _ hcomm hq2
  have e : b * (b * ℓ * b⁻¹ * ℓ⁻¹) = ℓ * b * ℓ⁻¹ := by
    calc b * (b * ℓ * b⁻¹ * ℓ⁻¹) = (b * b) * ℓ * b⁻¹ * ℓ⁻¹ := by group
      _ = ℓ * b * ℓ⁻¹ := by rw [hb2, one_mul, hbi]
  rw [e] at hcase
  have hrN : r ∈ N := hPN hr
  rcases hcase with h | h
  ·
    refine ⟨r, hr, r⁻¹ * ℓ, N.mul_mem (N.inv_mem hrN) hℓ, ?_, by group⟩
    apply hG _ (hNC (N.mul_mem (N.inv_mem hrN) hℓ))
    have : r⁻¹ * ℓ * b * (r⁻¹ * ℓ)⁻¹ = b := by
      calc r⁻¹ * ℓ * b * (r⁻¹ * ℓ)⁻¹ = r⁻¹ * (ℓ * b * ℓ⁻¹) * r := by group
        _ = r⁻¹ * (r * b * r⁻¹) * r := by rw [h]
        _ = b := by group
    exact mul_inv_eq_iff_eq_mul.mp this
  ·
    exfalso
    set ℓ' := r⁻¹ * ℓ with hℓ'
    have hℓ'N : ℓ' ∈ N := N.mul_mem (N.inv_mem hrN) hℓ
    have hℓ's : ℓ' * s = s * ℓ' := Subgroup.mem_centralizer_singleton_iff.mp (hNC hℓ'N)
    have hconj : ℓ' * b * ℓ'⁻¹ = b * s := by
      calc ℓ' * b * ℓ'⁻¹ = r⁻¹ * (ℓ * b * ℓ⁻¹) * r := by rw [hℓ']; group
        _ = r⁻¹ * (r * b * r⁻¹ * s) * r := by rw [h]
        _ = b * (r⁻¹ * s * r) := by group
        _ = b * s := by
            rw [show r⁻¹ * s * r = s by
              calc r⁻¹ * s * r = r⁻¹ * (s * r) := mul_assoc _ _ _
                _ = r⁻¹ * (r * s) := by rw [hsP r hr]
                _ = s := by group]
    obtain ⟨m, hm, hmP⟩ := hodd ℓ' hℓ'N
    have hs2 : s * s = 1 := (hq 0).z_sq
    have hpow : ∀ k : ℕ, ℓ' ^ k * b * (ℓ' ^ k)⁻¹ = b * s ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hℓ'sk : ℓ' * s ^ k = s ^ k * ℓ' := (Commute.pow_right (show Commute ℓ' s from hℓ's) k).eq
        calc ℓ' ^ (k + 1) * b * (ℓ' ^ (k + 1))⁻¹ = ℓ' * (ℓ' ^ k * b * (ℓ' ^ k)⁻¹) * ℓ'⁻¹ := by
              rw [pow_succ']; group
          _ = ℓ' * (b * s ^ k) * ℓ'⁻¹ := by rw [ih]
          _ = (ℓ' * b * ℓ'⁻¹) * (ℓ' * s ^ k * ℓ'⁻¹) := by group
          _ = (b * s) * s ^ k := by
              rw [hconj, mul_inv_eq_iff_eq_mul.mpr hℓ'sk]
          _ = b * s ^ (k + 1) := by rw [pow_succ', mul_assoc]
    obtain ⟨j, rfl⟩ := hm
    have hsodd : s ^ (2 * j + 1) = s := by
      rw [pow_succ, pow_mul, sq, hs2, one_pow, one_mul]
    exact hnc _ hmP (by rw [hpow, hsodd])


@[expose] def commSub (A : Subgroup Y) (s q : Y) (hs2 : s * s = 1) (hsA : ∀ a ∈ A, s * a = a * s) : Subgroup Y where
  carrier := {r | r ∈ A ∧ (r * q * r⁻¹ * q⁻¹ = 1 ∨ r * q * r⁻¹ * q⁻¹ = s)}
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have e : a * b * q * (a * b)⁻¹ * q⁻¹ =
        a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) := by group
    have has : a * s * a⁻¹ = s := by rw [← hsA a ha]; group
    rw [e]
    rcases hcb with h2 | h2
    · rw [h2]
      simpa using hca
    · rw [h2, has]
      rcases hca with h1 | h1
      · rw [h1]; right; simp
      · rw [h1]; left; exact hs2
  one_mem' := ⟨A.one_mem, Or.inl (by simp)⟩
  inv_mem' := by
    rintro r ⟨hr, hc⟩
    refine ⟨A.inv_mem hr, ?_⟩
    have hrs : r⁻¹ * s * r = s := by
      calc r⁻¹ * s * r = r⁻¹ * (s * r) := mul_assoc _ _ _
        _ = r⁻¹ * (r * s) := by rw [hsA r hr]
        _ = s := by group
    have e : r⁻¹ * q * r⁻¹⁻¹ * q⁻¹ = r⁻¹ * (r * q * r⁻¹ * q⁻¹)⁻¹ * r := by group
    rw [e]
    rcases hc with h | h
    · rw [h]; left; simp
    · rw [h]
      right
      rw [show s⁻¹ = s from inv_eq_of_mul_eq_one_right hs2]
      exact hrs

theorem P_comm_center {s : Y} {J : Fin 4 → Subgroup Y} (hq : ∀ i, Q8Facts (J i) s)
    (hcom : ∀ i j, i ≠ j → Commutes (J i) (J j)) {r q : Y} (hr : r ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3)
    (hqP : q ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3) : r * q * r⁻¹ * q⁻¹ = 1 ∨ r * q * r⁻¹ * q⁻¹ = s := by
  have hs2 : s * s = 1 := (hq 0).z_sq
  have hPs := P_le_centralizer hq
  have hsP : ∀ g ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3, s * g = g * s := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hPs hg)).symm
  have hs1 : ∀ i, ∀ q ∈ J i, ∀ r ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3,
      r * q * r⁻¹ * q⁻¹ = 1 ∨ r * q * r⁻¹ * q⁻¹ = s := by
    intro i q hqi r hr
    have hle : J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 ≤ commSub (J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3) s q hs2 hsP := by
      have : ∀ j, J j ≤ commSub (J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3) s q hs2 hsP := by
        intro j g hg
        have hgP : g ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := by
          fin_cases j
          · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hg))
          · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hg))
          · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hg)
          · exact Subgroup.mem_sup_right hg
        refine ⟨hgP, ?_⟩
        by_cases hji : j = i
        · subst hji
          by_cases hc : g * q = q * g
          · left
            calc g * q * g⁻¹ * q⁻¹ = (q * g) * g⁻¹ * q⁻¹ := by rw [hc]
              _ = 1 := by group
          · right
            exact (hq j).comm_eq g hg q hqi hc
        · left
          have := hcom j i hji g hg q hqi
          calc g * q * g⁻¹ * q⁻¹ = (q * g) * g⁻¹ * q⁻¹ := by rw [this]
            _ = 1 := by group
      exact sup_le (sup_le (sup_le (this 0) (this 1)) (this 2)) (this 3)
    exact (hle hr).2
  have hle2 : J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 ≤ commSub (J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3) s r hs2 hsP := by
    have : ∀ j, J j ≤ commSub (J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3) s r hs2 hsP := by
      intro j g hg
      have hgP : g ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := by
        fin_cases j
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hg))
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hg))
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hg)
        · exact Subgroup.mem_sup_right hg
      refine ⟨hgP, ?_⟩
      have h := hs1 j g hg r hr
      have e : g * r * g⁻¹ * r⁻¹ = (r * g * r⁻¹ * g⁻¹)⁻¹ := by group
      rw [e]
      rcases h with h | h
      · left; rw [h]; simp
      · right; rw [h]; exact inv_eq_of_mul_eq_one_right hs2
    exact sup_le (sup_le (sup_le (this 0) (this 1)) (this 2)) (this 3)
  have h := (hle2 hqP).2
  have e : r * q * r⁻¹ * q⁻¹ = (q * r * q⁻¹ * r⁻¹)⁻¹ := by group
  rw [e]
  rcases h with h | h
  · left; rw [h]; simp
  · right; rw [h]; exact inv_eq_of_mul_eq_one_right hs2

end Core

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
