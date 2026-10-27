module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem comm_beta_z : ∀ a ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j), ∀ b ∈ zpowers z,
    a * b = b * a := by
  have hσ := hs.setup
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  intro a ha b hb
  rcases L415.mem_zpowers_two hβ2 ha with rfl | rfl <;>
    rcases L415.mem_zpowers_two hz2 hb with rfl | rfl <;> try simp
  exact hσ.X_comm hs.beta.mem_X (subset_closure (by simp))

theorem conj_t_not_mem {g : X} (hg : g ∈ W) :
    g * t * g⁻¹ ∉ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z := by
  have hσ := hs.setup
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have hcen : ∀ x ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z, ∀ y ∈ W,
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := L415.mem_sup_of_commute hc.comm_beta_z hx
    have hay : a * y = y * a := by
      rcases L415.mem_zpowers_two hβ2 ha with rfl | rfl
      · simp
      · exact (hc.comm_beta hy).symm
    have hby : b * y = y * b := by
      rcases L415.mem_zpowers_two hz2 hb with rfl | rfl
      · simp
      · exact (hc.comm_z hy).symm
    calc a * b * y = a * (y * b) := by rw [mul_assoc, hby]
      _ = (a * y) * b := by group
      _ = y * a * b := by rw [hay]
      _ = y * (a * b) := by group
  intro h1
  apply hc.t_not_comm
  have hz₁' : g * z₁ * g⁻¹ ∈ W := mul_mem (mul_mem hg hc.z₁_mem) (inv_mem hg)
  have h2 := hcen _ h1 _ hz₁'
  calc t * z₁ = g⁻¹ * ((g * t * g⁻¹) * (g * z₁ * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * z₁ * g⁻¹) * (g * t * g⁻¹)) * g := by rw [h2]
    _ = z₁ * t := by group

theorem false_of_le_centralizer_t (hKC : AutPSL2CentralizerInput) {𝒱 : Subgroup X}
    (hW𝒱 : W ≤ 𝒱) {Y : Subgroup X} (hYn : ∀ v ∈ 𝒱, ∀ y ∈ Y, v * y * v⁻¹ ∈ Y)
    (hY2 : ∀ y ∈ Y, y ^ 2 = 1) (hY8 : Nat.card Y = 8) (hYt : Y ≤ centralizer {t}) : False := by
  classical
  have hσ := hs.setup
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hYX : Y ≤ closure {t, w ^ (orderOf w / 2), z} :=
    hσ.le_X_of_elem_centralizer hYt hY2 (fun g hg y hy => hYn g (hW𝒱 (hc.T_le_W hg)) y hy)
  have hYX' : Y = closure {t, w ^ (orderOf w / 2), z} :=
    eq_of_le_of_card_ge hYX (by rw [hσ.card_X, hY8])
  have hs4 : ∀ g ∈ W, g * t * g⁻¹ ∈ ({t, t * (w ^ (orderOf w / 2) * t ^ i * z ^ j), t * z,
      t * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * z)} : Finset X) := by
    intro g hg
    have h1 : g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := by
      rw [← hYX']
      exact hYn g (hW𝒱 hg) t (hYX' ▸ htX)
    rcases hc.mem_X_cases h1 with h2 | h2
    · exact absurd h2 (hc.conj_t_not_mem hg)
    · obtain ⟨a, ha, b, hb, hab⟩ := L415.mem_sup_of_commute hc.comm_beta_z h2
      have h3 : g * t * g⁻¹ = t * (a * b) := by
        calc g * t * g⁻¹ = t⁻¹ * (t * (g * t * g⁻¹)) := by group
          _ = t * (a * b) := by rw [hab, hti]
      rw [h3]
      rcases L415.mem_zpowers_two hβ2 ha with rfl | rfl <;>
        rcases L415.mem_zpowers_two hz2 hb with rfl | rfl <;> simp
  have h1 := hc.eight_le_of_conj_mem hKC hs4
  have h2 := L415.card_le_four t (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) (t * z)
    (t * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * z))
  omega

theorem false_of_tβ_mem (hKC : AutPSL2CentralizerInput) {𝒱 : Subgroup X} (hW𝒱 : W ≤ 𝒱)
    {Y : Subgroup X} (hYn : ∀ v ∈ 𝒱, ∀ y ∈ Y, v * y * v⁻¹ ∈ Y)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hzY : z ∈ Y)
    (hC4 : Nat.card ↥(Y ⊓ centralizer {t}) = 4)
    (htβY : t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈ Y) : False := by
  classical
  have hσ := hs.setup
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβdef
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hβ2 : β * β = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have htβ : t * β = β * t := mem_centralizer_singleton_iff.mp (hc.isSylowOf_W.le hc.t_mem_W)
  have htz : t * z = z * t := hc.comm_z hc.t_mem_W
  have hβz : β * z = z * β := hσ.X_comm hs.beta.mem_X (subset_closure (by simp))
  have htβ2 : (t * β) * (t * β) = 1 := by
    calc t * β * (t * β) = t * (β * t) * β := by group
      _ = t * (t * β) * β := by rw [htβ]
      _ = (t * t) * (β * β) := by group
      _ = 1 := by rw [ht2, hβ2, one_mul]
  have hYβt : ∀ y ∈ Y, y * β = β * y → y * t = t * y := by
    intro y hy hyβ
    have h1 := hYc y hy _ htβY
    calc y * t = y * (t * β) * β⁻¹ := by group
      _ = (t * β) * y * β⁻¹ := by rw [h1]
      _ = t * (β * y) * β⁻¹ := by group
      _ = t * (y * β) * β⁻¹ := by rw [hyβ]
      _ = t * y := by group
  have hconj : ∀ g ∈ W, g * (t * β) * g⁻¹ ∈ Y ⊓ centralizer {t} := by
    intro g hg
    have h1 : g * (t * β) * g⁻¹ ∈ Y := hYn g (hW𝒱 hg) _ htβY
    have hgβ : g * β = β * g := hc.comm_beta hg
    have h2 : g * (t * β) * g⁻¹ * β = β * (g * (t * β) * g⁻¹) := by
      have hginv : g⁻¹ * β = β * g⁻¹ := by
        calc g⁻¹ * β = g⁻¹ * (β * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * β) * g⁻¹ := by rw [hgβ]
          _ = β * g⁻¹ := by group
      calc g * (t * β) * g⁻¹ * β = g * (t * β) * (g⁻¹ * β) := by group
        _ = g * (t * β) * (β * g⁻¹) := by rw [hginv]
        _ = g * t * (β * β) * g⁻¹ := by group
        _ = g * (β * t) * β * g⁻¹ := by rw [← htβ]; group
        _ = (g * β) * (t * β) * g⁻¹ := by group
        _ = (β * g) * (t * β) * g⁻¹ := by rw [hgβ]
        _ = β * (g * (t * β) * g⁻¹) := by group
    exact mem_inf.mpr ⟨h1, mem_centralizer_singleton_iff.mpr (hYβt _ h1 h2)⟩
  have hzC : z ∈ Y ⊓ centralizer {t} := mem_inf.mpr ⟨hzY, mem_centralizer_singleton_iff.mpr
    htz.symm⟩
  have htβC : t * β ∈ Y ⊓ centralizer {t} := mem_inf.mpr ⟨htβY,
    mem_centralizer_singleton_iff.mpr (by rw [mul_assoc, ← htβ, ← mul_assoc])⟩
  have htβz : t * β ∉ zpowers z := by
    intro h1
    apply hc.conj_t_not_mem (one_mem W)
    rw [show (1 : X) * t * 1⁻¹ = (t * β) * β by simp [mul_assoc, hβ2]]
    exact mul_mem (mem_sup_right h1) (mem_sup_left (mem_zpowers β))
  have hcomm₂ : ∀ a ∈ zpowers z, ∀ b ∈ zpowers (t * β), a * b = b * a := by
    intro a ha b hb
    rcases L415.mem_zpowers_two hz2 ha with ha' | ha' <;>
      rcases L415.mem_zpowers_two htβ2 hb with hb' | hb' <;> rw [ha', hb'] <;> try simp
    calc z * (t * β) = (z * t) * β := by group
      _ = (t * z) * β := by rw [htz]
      _ = t * (z * β) := by group
      _ = t * (β * z) := by rw [hβz]
      _ = t * β * z := by group
  obtain ⟨hEc, hE2⟩ := L415.elem_zpowers hz2
  obtain ⟨-, -, hcardE⟩ := L415.elem_sup hEc hE2 htβ2 htβz (fun a ha => hcomm₂ a ha _
    (mem_zpowers _))
  have hEle : zpowers z ⊔ zpowers (t * β) ≤ Y ⊓ centralizer {t} :=
    sup_le (zpowers_le.mpr hzC) (zpowers_le.mpr htβC)
  have hEeq : zpowers z ⊔ zpowers (t * β) = Y ⊓ centralizer {t} :=
    eq_of_le_of_card_ge hEle (by rw [hC4, hcardE, L415.card_zpowers_two hz2 hσ.z_ne_one])
  have hs2 : ∀ g ∈ W, g * t * g⁻¹ ∈ ({t, t * z} : Finset X) := by
    intro g hg
    have h1 := hconj g hg
    rw [← hEeq] at h1
    obtain ⟨a, ha, b, hb, hab⟩ := L415.mem_sup_of_commute hcomm₂ h1
    have hgβ : g * β * g⁻¹ = β := by rw [hc.comm_beta hg, mul_inv_cancel_right]
    have h2 : g * t * g⁻¹ = a * b * β := by
      calc g * t * g⁻¹ = g * (t * β) * g⁻¹ * (g * β * g⁻¹)⁻¹ := by group
        _ = a * b * β := by rw [← hab, hgβ, inv_eq_of_mul_eq_one_right hβ2]
    rcases L415.mem_zpowers_two hz2 ha with ha' | ha' <;>
      rcases L415.mem_zpowers_two htβ2 hb with hb' | hb' <;> rw [ha', hb'] at h2
    · exfalso
      apply hc.conj_t_not_mem hg
      rw [h2, one_mul, one_mul]
      exact mem_sup_left (mem_zpowers β)
    · rw [h2]
      simp only [one_mul, Finset.mem_insert, Finset.mem_singleton]
      left
      rw [mul_assoc, hβ2, mul_one]
    · exfalso
      apply hc.conj_t_not_mem hg
      rw [h2, mul_one]
      exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left (mem_zpowers β))
    · rw [h2]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      calc z * (t * β) * β = z * t * (β * β) := by group
        _ = t * z := by rw [hβ2, mul_one, htz]
  have h1 := hc.eight_le_of_conj_mem hKC hs2
  have h2 : ({t, t * z} : Finset X).card ≤ 2 := Finset.card_le_two
  omega

end Config415

end CFSG.ComponentClassification.HarrisLit
