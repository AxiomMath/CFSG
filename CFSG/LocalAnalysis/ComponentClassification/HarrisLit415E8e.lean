module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8d

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem normalizer_of_E8 [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) (hA : AutPSL2RCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱) (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z)
    {Y : Subgroup X} (hY𝒱 : Y ≤ 𝒱) (hYn : ∀ v ∈ 𝒱, ∀ y ∈ Y, v * y * v⁻¹ ∈ Y)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hY2 : ∀ y ∈ Y, y ^ 2 = 1) (hY8 : Nat.card Y = 8)
    (hzY : z ∈ Y) :
    (∀ v ∈ 𝒱, v ∈ normalizer (W : Set X)) ∨
      ∀ v ∈ 𝒱, v ∈ normalizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X) := by
  have hσ := hs.setup
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have ht𝒱 := hW𝒱 hc.t_mem_W
  have htz : t * z = z * t := hc.comm_z hc.t_mem_W
  have hTt : ∀ g ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w, g * t = t * g := fun g hg =>
    mem_centralizer_singleton_iff.mp (hs.sylow.le (hσ.T_le hg))
  by_cases hYt : Y ≤ centralizer {t}
  · exact absurd (hc.false_of_le_centralizer_t hKC hW𝒱 hYn hY2 hY8 hYt) not_false
  have hC4' : 4 ≤ Nat.card ↥(Y ⊓ centralizer {t}) :=
    card_centralizer_ge_four hYc hY2 hY8 (fun y hy => hYn t ht𝒱 y hy) (by rw [sq]; exact ht2)
  have hCX : Y ⊓ centralizer {t} ≤ closure {t, w ^ (orderOf w / 2), z} := by
    refine hσ.le_X_of_elem_centralizer inf_le_right (fun x hx => hY2 x (mem_inf.mp hx).1) ?_
    intro g hg x hx
    refine mem_inf.mpr ⟨hYn g (hW𝒱 (hc.T_le_W hg)) x (mem_inf.mp hx).1, ?_⟩
    have h1 := hTt g hg
    have h2 : x * t = t * x := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    have hginv : g⁻¹ * t = t * g⁻¹ := by
      calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * t) * g⁻¹ := by rw [h1]
        _ = t * g⁻¹ := by group
    rw [mem_centralizer_singleton_iff]
    calc g * x * g⁻¹ * t = g * x * (g⁻¹ * t) := by group
      _ = g * x * (t * g⁻¹) := by rw [hginv]
      _ = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [h2]
      _ = (g * t) * x * g⁻¹ := by group
      _ = (t * g) * x * g⁻¹ := by rw [h1]
      _ = t * (g * x * g⁻¹) := by group
  have hC4 : Nat.card ↥(Y ⊓ centralizer {t}) = 4 := by
    have h1 : Nat.card ↥(Y ⊓ centralizer {t}) ∣ 8 := by
      rw [← hY8]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(Y ⊓ centralizer {t}) ≠ 8 := by
      intro h3
      apply hYt
      have h4 := eq_of_le_of_card_ge (inf_le_left : Y ⊓ centralizer {t} ≤ Y) (by rw [h3, hY8])
      rw [← h4]
      exact inf_le_right
    have h3 := Nat.le_of_dvd (by norm_num) h1
    interval_cases h : Nat.card ↥(Y ⊓ centralizer {t}) <;> simp_all
  have htY : t ∉ Y := fun h1 => hYt (fun y hy =>
    mem_centralizer_singleton_iff.mpr (hYc y hy t h1))
  obtain ⟨c, hcC, hcz⟩ : ∃ c ∈ Y ⊓ centralizer {t}, c ∉ zpowers z := by
    by_contra hno
    push Not at hno
    have h1 := Subgroup.card_le_of_le (fun x hx => hno x hx :
      Y ⊓ centralizer {t} ≤ zpowers z)
    rw [hC4, L415.card_zpowers_two hz2 hσ.z_ne_one] at h1
    omega
  have hcY := (mem_inf.mp hcC).1
  rcases hc.mem_X_cases (hCX hcC) with h1 | h1
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := L415.mem_sup_of_commute hc.comm_beta_z h1
    have hbY : b ∈ Y := by
      rcases L415.mem_zpowers_two hz2 hb with h | h <;> rw [h]
      · exact one_mem _
      · exact hzY
    have hβY : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ Y := by
      rcases L415.mem_zpowers_two hβ2 ha with h | h
      · exfalso
        apply hcz
        rw [hab, h, one_mul]
        exact hb
      · rw [← h, show a = c * b⁻¹ by rw [hab]; group]
        exact mul_mem hcY (inv_mem hbY)
    exact hc.normalizer_of_beta_mem hnab hKC hA h412 h𝒱 hW𝒱 hz𝒱 hY𝒱 hYn hYc hY2 hY8 hzY hC4 hβY
  ·
    exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := L415.mem_sup_of_commute hc.comm_beta_z h1
    have hbY : b ∈ Y := by
      rcases L415.mem_zpowers_two hz2 hb with h | h <;> rw [h]
      · exact one_mem _
      · exact hzY
    have hc' : c = t * (a * b) := by
      calc c = t⁻¹ * (t * c) := by group
        _ = t * (a * b) := by rw [hab, hti]
    rcases L415.mem_zpowers_two hβ2 ha with h | h
    · apply htY
      rw [show t = c * b⁻¹ by rw [hc', h]; group]
      exact mul_mem hcY (inv_mem hbY)
    · apply hc.false_of_tβ_mem hKC hW𝒱 hYn hYc hzY hC4
      rw [show t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) = c * b⁻¹ by rw [hc', h]; group]
      exact mul_mem hcY (inv_mem hbY)

theorem conj_mem_of_V
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) (hA : AutPSL2RCentralizerInput) (hD : AutPSL2RDerivedInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱) {τ : X} (hτ : τ ∈ 𝒱)
    (hτz : τ * z * τ⁻¹ = z)
    (hτβ : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) :
    ∀ v ∈ 𝒱, v * z₁ * v⁻¹ = z₁ ∨ v * z₁ * v⁻¹ = t * z₁ * t⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcen, hz𝒱⟩ := hc.center_V hKC h𝒱 hW𝒱 hτ hτz hτβ
  obtain ⟨Y, hY𝒱, hYn, hYc, hY2, hY8⟩ := exists_normal_E8 hs.standing.sect h𝒱
  have hzY : z ∈ Y := by
    have : Group.IsNilpotent ↥𝒱 := h𝒱.isPGroup.isNilpotent
    have hN : (Y.subgroupOf 𝒱).Normal := ⟨fun y hy g => hYn g g.2 y hy⟩
    have hne : Y.subgroupOf 𝒱 ≠ ⊥ := by
      intro h1
      have h2 : Nat.card ↥(Y.subgroupOf 𝒱) = 8 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hY𝒱).toEquiv, hY8]
      rw [h1, Subgroup.card_bot] at h2
      omega
    obtain ⟨⟨c, hcY, hcZ⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    rcases hcen c c.2 (fun v hv => congrArg Subtype.val
        ((mem_center_iff.mp hcZ) ⟨v, hv⟩).symm) with h1 | h1
    · exact absurd (Subtype.ext (Subtype.ext h1)) hc1
    · rw [← h1]
      exact hcY
  rcases hc.normalizer_of_E8 hnab hKC hA h412 h𝒱 hW𝒱 hz𝒱 hY𝒱 hYn hYc hY2 hY8 hzY with h | h
  · intro v hv
    exact hc.conj_mem_of_normalizer_W hnab hKC hA h412 (h v hv)
  · intro v hv
    rcases hc.conj_mem_of_normalizer_W₀ hnab hKC hA hD h412 (h v hv) with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      apply hc.t_not_comm
      have h2 : z₁ = z := by
        calc z₁ = v⁻¹ * (v * z₁ * v⁻¹) * v := by group
          _ = v⁻¹ * (z * v) := by rw [h1, mul_assoc]
          _ = v⁻¹ * (v * z) := by rw [hz𝒱 v hv]
          _ = z := by group
      rw [h2]
      exact hc.comm_z hc.t_mem_W

end Config415

end CFSG.ComponentClassification.HarrisLit
