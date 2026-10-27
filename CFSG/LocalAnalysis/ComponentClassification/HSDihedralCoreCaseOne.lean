module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreElem
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreChar

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)
open CFSG.ComponentClassification.HSFLit (HaradaInput ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A] [Finite A]

namespace LocalDatum

variable (Δ : LocalDatum X A)

omit [Finite X] [Finite A] in
theorem exists_QD_or (h1 : Δ.CaseOne) (hA : AutFacts Δ) {σ : X} (hσS : σ ∈ Δ.S)
    (hσD : Δ.ψe σ ∉ Δ.Dbar) {s : X} (hs : s ∈ Δ.S) :
    ∃ q ∈ Δ.Q, ∃ d ∈ Δ.D, s = q * d ∨ s = q * d * σ := by
  by_cases hsD : Δ.ψe s ∈ Δ.Dbar
  · obtain ⟨q, hq, d, hd, rfl⟩ := Δ.exists_QD hs hsD
    exact ⟨q, hq, d, hd, Or.inl rfl⟩
  · have h := hA.index_one h1 _ (Δ.ψe_mem_R hs) _ (Δ.ψe_mem_R hσS) hsD hσD
    rw [← Δ.ψe_inv hσS, ← Δ.ψe_mul hs (inv_mem hσS)] at h
    obtain ⟨q, hq, d, hd, hqd⟩ := Δ.exists_QD (mul_mem hs (inv_mem hσS)) h
    exact ⟨q, hq, d, hd, Or.inr (by rw [← hqd]; group)⟩

omit [Finite X] [Finite A] in
theorem commute_of_mul_commute {q d g : X} (hqg : q * g = g * q)
    (h : q * d * g = g * (q * d)) : d * g = g * d := by
  have : q * (d * g) = q * (g * d) := by
    calc q * (d * g) = q * d * g := by group
      _ = g * (q * d) := h
      _ = q * (g * d) := by rw [← mul_assoc, ← hqg, mul_assoc]
  exact mul_left_cancel this

theorem false_of_caseOne_small (hH : HaradaInput) (hA : AutFacts Δ)
    (hX : ¬ SectionalRankLeFour X) (h1 : Δ.CaseOne) (hQ : ∀ y ∈ Δ.Q, y = 1 ∨ y = Δ.t) :
    False := by
  have htD : Δ.t * Δ.dz ∉ Δ.D := fun h => Δ.t_not_mem_D (by
    have := mul_mem h (inv_mem Δ.dz_mem)
    rwa [mul_inv_cancel_right] at this)
  have hzS := Δ.D_le Δ.dz_mem
  have hbS := Δ.D_le Δ.db_mem
  refine Δ.false_of_harada hH hA hX (E := zpowers Δ.t ⊔ zpowers Δ.dz ⊔ zpowers Δ.db)
    (E8_le Δ.t_mem hzS hbS) mem_E8_left
    (elem_E8 Δ.t_sq Δ.dz_sq Δ.db_sq (Δ.commute_t hzS).symm (Δ.commute_t hbS).symm
      Δ.commute_db_dz.symm)
    (card_E8 Δ.t_sq Δ.dz_sq Δ.db_sq (Δ.commute_t hzS).symm (Δ.commute_t hbS).symm
      Δ.commute_db_dz.symm Δ.t_ne_one Δ.dz_ne_one (fun h => Δ.t_not_mem_D (h ▸ Δ.dz_mem))
      ⟨Δ.db_ne_one, fun h => Δ.t_not_mem_D (h ▸ Δ.db_mem), Δ.db_ne_dz,
        fun h => htD (h ▸ Δ.db_mem)⟩) fun s hs hsE => ?_
  have hsz : s * Δ.dz = Δ.dz * s := hsE _ mem_E8_mid
  have hsb : s * Δ.db = Δ.db * s := hsE _ mem_E8_right
  have hz2 : Δ.ψe Δ.dz ^ 2 = 1 := by rw [← Δ.ψe_pow hzS, Δ.dz_sq, Δ.ψe_one]
  have hb2 : Δ.ψe Δ.db ^ 2 = 1 := by rw [← Δ.ψe_pow hbS, Δ.db_sq, Δ.ψe_one]
  have hzb : Δ.ψe Δ.dz * Δ.ψe Δ.db = Δ.ψe Δ.db * Δ.ψe Δ.dz := by
    rw [← Δ.ψe_mul hzS hbS, ← Δ.ψe_mul hbS hzS, Δ.commute_db_dz]
  have hz1 : Δ.ψe Δ.dz ≠ 1 := fun h => Δ.dz_ne_one (Δ.eq_one_of_ψe Δ.dz_mem h)
  have hb1 : Δ.ψe Δ.db ≠ 1 := fun h => Δ.db_ne_one (Δ.eq_one_of_ψe Δ.db_mem h)
  have hbz : Δ.ψe Δ.db ≠ Δ.ψe Δ.dz := fun h =>
    Δ.db_ne_dz (Δ.eq_of_ψe_eq Δ.db_mem Δ.dz_mem h)
  have hmem := hA.klein_one h1 (zpowers (Δ.ψe Δ.dz) ⊔ zpowers (Δ.ψe Δ.db))
    (sup_le (zpowers_le.mpr (Δ.ψe_mem_Dbar Δ.dz_mem))
      (zpowers_le.mpr (Δ.ψe_mem_Dbar Δ.db_mem)))
    (card_E4 hz2 hb2 hzb hz1 hb1 hbz) (elem_E4 hz2 hb2 hzb).sq_eq_one _ (Δ.ψe_mem_R hs)
    fun e he => commute_of_mem_sup ((Δ.commute_iff hs Δ.dz_mem).mp hsz)
      ((Δ.commute_iff hs Δ.db_mem).mp hsb) he
  obtain ⟨q, hq, d, hd, rfl⟩ := Δ.exists_QD hs hmem
  have hdb := commute_of_mul_commute (Δ.commute_of_mem_Q_D hq Δ.db_mem) hsb
  have hqE : q ∈ zpowers Δ.t ⊔ zpowers Δ.dz ⊔ zpowers Δ.db := by
    rcases hQ q hq with rfl | rfl
    · exact one_mem _
    · exact mem_E8_left
  have hdE : d ∈ zpowers Δ.t ⊔ zpowers Δ.dz ⊔ zpowers Δ.db := by
    rcases Δ.mem_of_commute_db hd hdb with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact mem_E8_mid
    · exact mem_E8_right
    · exact mul_mem mem_E8_right mem_E8_mid
  exact mul_mem hqE hdE

omit [Finite A] in
theorem sq_mem_Q_of_commute_inv (h1 : Δ.CaseOne) {c : X} (hc : c ∈ Δ.S)
    (hcI : ∀ i ∈ Δ.S, i ^ 2 = 1 → c * i = i * c) : c ^ 2 ∈ Δ.Q :=
  Δ.sq_mem_Q_of_caseOne h1 hc fun _ hd =>
    Δ.commute_of_commute_inv (fun i hi hi2 => hcI i (Δ.D_le hi) hi2) hd

omit [Finite A] in
theorem false_of_caseOne_inv (φ : Δ.Fusion) (h1 : Δ.CaseOne) {q₁ : X} (hq₁ : q₁ ∈ Δ.Q)
    (hq₁t : q₁ ^ 2 = Δ.t) (hinv : ∀ i ∈ Δ.S, i ^ 2 = 1 → Δ.ψe i ∈ Δ.Dbar) : False := by
  refine φ.false_of_char_inv (fun c hc hcI => Δ.sq_mem_Q_of_commute_inv h1 hc hcI)
    (Δ.Q_le hq₁) (fun i hi hi2 => ?_) hq₁t
  obtain ⟨q, hq, d, hd, rfl⟩ := Δ.exists_QD hi (hinv i hi hi2)
  have h1 := Δ.commute_Q hq₁ hq
  have h2 := Δ.commute_of_mem_Q_D hq₁ hd
  calc q₁ * (q * d) = q * (q₁ * d) := by rw [← mul_assoc, h1, mul_assoc]
    _ = q * d * q₁ := by rw [h2, mul_assoc]

omit [Finite A] in
theorem false_of_caseOne_center (φ : Δ.Fusion) (h1 : Δ.CaseOne) (hA : AutFacts Δ) {σ : X}
    (hσS : σ ∈ Δ.S) (hσD : Δ.ψe σ ∉ Δ.Dbar) {q₁ : X} (hq₁ : q₁ ∈ Δ.Q) (hq₁t : q₁ ^ 2 = Δ.t)
    (hq₁σ : q₁ * σ = σ * q₁) : False := by
  refine φ.false_of_char_center (fun c hc hcZ => Δ.sq_mem_Q_of_caseOne h1 hc
    fun d hd => hcZ d (Δ.D_le hd)) (Δ.Q_le hq₁) (fun s hs => ?_) hq₁t
  obtain ⟨q, hq, d, hd, h | h⟩ := Δ.exists_QD_or h1 hA hσS hσD hs
  · have h1 := Δ.commute_Q hq₁ hq
    have h2 := Δ.commute_of_mem_Q_D hq₁ hd
    rw [h]
    calc q₁ * (q * d) = q * (q₁ * d) := by rw [← mul_assoc, h1, mul_assoc]
      _ = q * d * q₁ := by rw [h2, mul_assoc]
  · have h1 := Δ.commute_Q hq₁ hq
    have h2 := Δ.commute_of_mem_Q_D hq₁ hd
    rw [h]
    calc q₁ * (q * d * σ) = q * (q₁ * d) * σ := by rw [← mul_assoc, ← mul_assoc, h1]; group
      _ = q * d * (q₁ * σ) := by rw [h2]; group
      _ = q * d * σ * q₁ := by rw [hq₁σ]; group

theorem false_of_caseOne_sigma (hH : HaradaInput) (hA : AutFacts Δ)
    (hX : ¬ SectionalRankLeFour X) (h1 : Δ.CaseOne) {σ : X} (hσS : σ ∈ Δ.S) (hσ2 : σ ^ 2 = 1)
    (hσD : Δ.ψe σ ∉ Δ.Dbar) (hCQ : ∀ c ∈ Δ.Q, c * σ = σ * c → c = 1 ∨ c = Δ.t) : False := by
  obtain ⟨z, hzD, hz1, hz2, hzS⟩ := Δ.exists_central_inv_D
  have hzS' := Δ.D_le hzD
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hσ2])
  have hDbar : ∀ y ∈ Δ.S, y = 1 ∨ y = Δ.t ∨ y = z ∨ y = Δ.t * z → Δ.ψe y ∈ Δ.Dbar := by
    rintro y - (rfl | rfl | rfl | rfl)
    · rw [Δ.ψe_one]; exact one_mem _
    · rw [Δ.ψe_t]; exact one_mem _
    · exact Δ.ψe_mem_Dbar hzD
    · rw [Δ.ψe_mul Δ.t_mem hzS', Δ.ψe_t, one_mul]; exact Δ.ψe_mem_Dbar hzD
  have hσE : σ ≠ 1 ∧ σ ≠ Δ.t ∧ σ ≠ z ∧ σ ≠ Δ.t * z := by
    refine ⟨fun h => hσD (hDbar σ hσS (Or.inl h)), fun h => hσD (hDbar σ hσS (Or.inr (Or.inl h))),
      fun h => hσD (hDbar σ hσS (Or.inr (Or.inr (Or.inl h)))),
      fun h => hσD (hDbar σ hσS (Or.inr (Or.inr (Or.inr h))))⟩
  set E := zpowers Δ.t ⊔ zpowers z ⊔ zpowers σ
  have hP : ∀ y ∈ Δ.S, Δ.ψe y ∈ Δ.Dbar → y * σ = σ * y → y ∈ E := by
    intro y hy hyD hyσ
    obtain ⟨q, hq, d, hd, rfl⟩ := Δ.exists_QD hy hyD
    have hconj : σ * q * σ⁻¹ * (σ * d * σ⁻¹) = q * d := by
      calc σ * q * σ⁻¹ * (σ * d * σ⁻¹) = σ * (q * d) * σ⁻¹ := by group
        _ = q * d := by rw [← hyσ]; group
    obtain ⟨hq', hd'⟩ := Δ.QD_unique (Δ.conj_mem_Q hσS hq) hq (Δ.conj_mem_D σ hσS d hd) hd hconj
    have hqσ : q * σ = σ * q := by
      calc q * σ = σ * q * σ⁻¹ * σ := by rw [hq']
        _ = σ * q := by group
    have hdσ : d * σ = σ * d := by
      calc d * σ = σ * d * σ⁻¹ * σ := by rw [hd']
        _ = σ * d := by group
    have hqE : q ∈ E := by
      rcases hCQ q hq hqσ with rfl | rfl
      · exact one_mem _
      · exact mem_E8_left
    have hdE : d ∈ E := by
      by_cases hd1 : d = 1
      · rw [hd1]; exact one_mem _
      have hmem : ∀ e ∈ Δ.D, e * σ = σ * e → Δ.ψe e ∈ Δ.Dbar ⊓ centralizer {Δ.ψe σ} :=
        fun e he heσ => mem_inf.mpr ⟨Δ.ψe_mem_Dbar he, mem_centralizer_singleton_iff.mpr
          (by rw [← Δ.ψe_mul (Δ.D_le he) hσS, ← Δ.ψe_mul hσS (Δ.D_le he), heσ])⟩
      have h := eq_of_mem_card_le_two (hA.inv_one h1 _ (Δ.ψe_mem_R hσS) hσD
        (by rw [← Δ.ψe_pow hσS, hσ2, Δ.ψe_one])) (hmem z hzD (hzS σ hσS).symm) (hmem d hd hdσ)
        (fun h => hz1 (Δ.eq_one_of_ψe hzD h)) (fun h => hd1 (Δ.eq_one_of_ψe hd h))
      rw [← Δ.eq_of_ψe_eq hzD hd h]
      exact mem_E8_mid
    exact mul_mem hqE hdE
  refine Δ.false_of_harada hH hA hX (E := E) (E8_le Δ.t_mem hzS' hσS) mem_E8_left
    (elem_E8 Δ.t_sq hz2 hσ2 (Δ.commute_t hzS').symm (Δ.commute_t hσS).symm (hzS σ hσS).symm)
    (card_E8 Δ.t_sq hz2 hσ2 (Δ.commute_t hzS').symm (Δ.commute_t hσS).symm (hzS σ hσS).symm
      Δ.t_ne_one hz1 (fun h => Δ.t_not_mem_D (h ▸ hzD)) hσE) fun s hs hsE => ?_
  have hsσ : s * σ = σ * s := hsE _ mem_E8_right
  by_cases hsD : Δ.ψe s ∈ Δ.Dbar
  · exact hP s hs hsD hsσ
  · have h := hA.index_one h1 _ (Δ.ψe_mem_R hs) _ (Δ.ψe_mem_R hσS) hsD hσD
    rw [← Δ.ψe_inv hσS, ← Δ.ψe_mul hs (inv_mem hσS), hσinv] at h
    have h' := hP (s * σ) (mul_mem hs hσS) h (by rw [hsσ, mul_assoc, hsσ])
    have := mul_mem h' (mem_E8_right (a := Δ.t) (b := z))
    rwa [mul_assoc, ← pow_two, hσ2, mul_one] at this

theorem false_of_caseOne (hH : HaradaInput) (hA : AutFacts Δ) (hX : ¬ SectionalRankLeFour X)
    (h1 : Δ.CaseOne) : False := by
  obtain ⟨φ⟩ := Δ.nonempty_fusion hA hX
  by_cases hσ : ∃ σ ∈ Δ.S, σ ^ 2 = 1 ∧ Δ.ψe σ ∉ Δ.Dbar
  · obtain ⟨σ, hσS, hσ2, hσD⟩ := hσ
    by_cases hc : ∃ c ∈ Δ.Q, c * σ = σ * c ∧ c ≠ 1 ∧ c ≠ Δ.t
    · obtain ⟨c, hc, hcσ, hc1, hct⟩ := hc
      obtain ⟨n, hn⟩ := Δ.exists_pow_sq_eq_t hc hc1 hct
      exact Δ.false_of_caseOne_center φ h1 hA hσS hσD (pow_mem hc n) hn
        ((Commute.pow_left (show Commute c σ from hcσ) n))
    · push Not at hc
      exact Δ.false_of_caseOne_sigma hH hA hX h1 hσS hσ2 hσD fun c hcQ hcσ => by
        by_cases hc1 : c = 1
        · exact Or.inl hc1
        · exact Or.inr (hc c hcQ hcσ hc1)
  · push Not at hσ
    by_cases hy : ∃ y ∈ Δ.Q, y ≠ 1 ∧ y ≠ Δ.t
    · obtain ⟨y, hy, hy1, hyt⟩ := hy
      obtain ⟨q₁, hq₁, hq₁t⟩ := Δ.exists_sq_eq_t hy hy1 hyt
      exact Δ.false_of_caseOne_inv φ h1 hq₁ hq₁t hσ
    · push Not at hy
      exact Δ.false_of_caseOne_small hH hA hX h1 fun y hy' => by
        by_cases hy1 : y = 1
        · exact Or.inl hy1
        · exact Or.inr (hy y hy' hy1)

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
