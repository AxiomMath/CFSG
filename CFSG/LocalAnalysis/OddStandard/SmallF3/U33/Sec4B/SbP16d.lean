module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP15
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

namespace Setting16

variable {G : Type} [Group G] [Finite G] {Q Y : Subgroup G} {τ ω : G}

private theorem tau_cent_Y (h : Setting16 Q Y τ ω) {a : G} (ha : a ∈ Y) :
    τ * a = a * τ := by
  have haQ : a ∈ Q := h.Y_le_Q ha
  have ha2 : a ^ 2 = 1 := ((h.mem_Y a).mp ha).2
  have hainv : a⁻¹ = a := by
    rw [pow_two] at ha2
    exact inv_eq_of_mul_eq_one_right ha2
  rw [h.tau_mul haQ, hainv]

private theorem tau_conj (h : Setting16 Q Y τ ω) {q : G} (hq : q ∈ Q) :
    τ * q * τ = q⁻¹ := by
  have ht := h.tau_inv q hq
  rwa [h.tau_inv_eq] at ht

private theorem false_of_inf_le_Y (h : Setting16 Q Y τ ω) {A : Subgroup G}
    (hinv : ∀ a ∈ A, a ^ 2 = 1 → a ∈ Y) (hcard : Nat.card A = 64)
    (hleY : A ⊓ Q ≤ Y) : False := by
  have hcardAQ : Nat.card ↥(A ⊓ Q) ≤ 16 := by
    have hle := Subgroup.card_le_of_le hleY
    rw [h.card_Y] at hle
    exact hle
  have hsup : A ⊔ Q = ⊤ := h.sup_Q_eq_top (by omega) hcardAQ
  have hτ : τ ∈ A ⊔ Q := by rw [hsup]; trivial
  haveI : Q.Normal := h.normal
  obtain ⟨a', ha'A, q', hq'Q, haq⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := A) (t := Q)).mp hτ
  have ha'eq : a' = τ * q'⁻¹ := by
    rw [← haq]; group
  have ha'inv : a' ^ 2 = 1 := by
    rw [ha'eq]
    exact h.sq_tau_mul (inv_mem hq'Q)
  have ha'Y : a' ∈ Y := hinv a' ha'A ha'inv
  have hτQ : τ ∈ Q := by
    rw [← haq]
    exact mul_mem (h.Y_le_Q ha'Y) hq'Q
  exact h.tau_not_mem hτQ

theorem Q_unique (h : Setting16 Q Y τ ω) {A : Subgroup G} (hYA : Y ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hcard : Nat.card A = 64)
    (hinv : ∀ a ∈ A, a ^ 2 = 1 → a ∈ Y) : A = Q := by
  by_contra hne
  have hnotle : ¬ A ≤ Q := by
    intro hle
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by simp [h.card_Q, hcard]))
  have hnotle' : ¬ (A : Set G) ⊆ (Q : Set G) := hnotle
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hnotle'
  obtain ⟨q, hq, ha | ha | ha | ha⟩ := h.cosets a
  · exact haQ (ha ▸ hq)
  · have hsq : a ^ 2 = 1 := by rw [ha]; exact h.sq_mul_tau hq
    exact haQ (h.Y_le_Q (hinv a haA hsq))
  · have hleY : A ⊓ Q ≤ Y := by
      intro b hb
      obtain ⟨hbA, hbQ⟩ := hb
      have hba : b * (q * ω) = (q * ω) * b := by
        have := hA b hbA a haA
        rwa [ha] at this
      have hbq : b * q = q * b := h.comm b hbQ q hq
      have hbω : b * ω = ω * b := by
        apply mul_left_cancel (a := q)
        calc q * (b * ω) = (q * b) * ω := by group
          _ = (b * q) * ω := by rw [hbq]
          _ = b * (q * ω) := by group
          _ = (q * ω) * b := hba
          _ = q * (ω * b) := by group
      exact h.cent_om b hbQ hbω.symm
    exact false_of_inf_le_Y h hinv hcard hleY
  · have hleY : A ⊓ Q ≤ Y := by
      intro b hb
      obtain ⟨hbA, hbQ⟩ := hb
      have hba : b * (q * (τ * ω)) = (q * (τ * ω)) * b := by
        have := hA b hbA a haA
        rwa [ha] at this
      have hbq : b * q = q * b := h.comm b hbQ q hq
      have hbωτ : (ω * τ) * b = b * (ω * τ) := by
        have hba' : b * (q * (ω * τ)) = (q * (ω * τ)) * b := by
          rw [← h.tau_om]; exact hba
        apply mul_left_cancel (a := q)
        calc q * ((ω * τ) * b) = (q * (ω * τ)) * b := by group
          _ = b * (q * (ω * τ)) := hba'.symm
          _ = (b * q) * (ω * τ) := by group
          _ = (q * b) * (ω * τ) := by rw [hbq]
          _ = q * (b * (ω * τ)) := by group
      exact h.cent_omtau b hbQ hbωτ
    exact false_of_inf_le_Y h hinv hcard hleY

private theorem map_Q_eq (h : Setting16 Q Y τ ω) (φ : G ≃* G) :
    Q.map φ.toMonoidHom = Q := by
  apply Q_unique h (A := Q.map φ.toMonoidHom)
  · intro y hy
    have hmapY : Y.map φ.toMonoidHom = Y :=
      (Subgroup.characteristic_iff_map_eq.mp h.char_Y) φ
    rw [← hmapY] at hy
    rcases hy with ⟨z, hzY, hzy⟩
    exact ⟨z, h.Y_le_Q hzY, hzy⟩
  · intro a ha b hb
    rcases ha with ⟨a', ha'Q, rfl⟩
    rcases hb with ⟨b', hb'Q, rfl⟩
    show φ a' * φ b' = φ b' * φ a'
    rw [← map_mul, ← map_mul, h.comm a' ha'Q b' hb'Q]
  · rw [Subgroup.card_map_of_injective φ.injective, h.card_Q]
  · intro a ha ha2
    rcases ha with ⟨a', ha'Q, rfl⟩
    have ha2' : (φ a') ^ 2 = 1 := ha2
    have ha'2 : a' ^ 2 = 1 := by
      apply φ.injective
      rw [map_pow, ha2', map_one]
    have ha'Y : a' ∈ Y := (h.mem_Y a').mpr ⟨ha'Q, ha'2⟩
    have hmapY : Y.map φ.toMonoidHom = Y :=
      (Subgroup.characteristic_iff_map_eq.mp h.char_Y) φ
    rw [← hmapY]
    exact ⟨a', ha'Y, rfl⟩

theorem char_Q (h : Setting16 Q Y τ ω) : Q.Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr (fun φ => map_Q_eq h φ)

private theorem phi_tau_mem_om (h : Setting16 Q Y τ ω) (φ : G ≃* G)
    (hmapQ : Q.map φ.toMonoidHom = Q) {q : G} (hq : q ∈ Q)
    (hu : φ τ = q * ω) : False := by
  have hu2 : (φ τ) ^ 2 = 1 := by rw [← map_pow, h.tau_sq, map_one]
  have hqY : q ∈ Y := by
    set q₁ : G := ω * q * ω with hq₁def
    have hωω : ω * ω = 1 := by rw [← pow_two, h.om_sq]
    have hq1Q : q₁ ∈ Q := by
      have hc := h.normal.conj_mem q hq ω
      rw [h.om_inv_eq] at hc
      rw [hq₁def]; exact hc
    have hq1Y : q₁ ∈ Y := by
      apply h.invol_om (q := q₁) hq1Q
      have hkey : ω * q₁ = φ τ := by
        rw [hq₁def, hu]
        rw [show ω * (ω * q * ω) = (ω * ω) * q * ω by group, hωω]
        group
      rw [hkey]; exact hu2
    have hcomm : ω * q₁ = q₁ * ω := h.om_cent_Y q₁ hq1Y
    have h1 : ω * q₁ * ω = q₁ := by
      rw [hcomm, mul_assoc, hωω, mul_one]
    have h2 : ω * q₁ * ω = q := by
      rw [hq₁def]
      calc ω * (ω * q * ω) * ω = (ω * ω) * q * (ω * ω) := by group
        _ = q := by rw [hωω]; group
    rw [← h2, h1]
    exact hq1Y
  obtain ⟨r, hrQ, hr2⟩ := h.exists_om_noninv
  have hsmap : q⁻¹ * r ∈ Q.map φ.toMonoidHom := by
    rw [hmapQ]; exact mul_mem (inv_mem hq) hrQ
  obtain ⟨r', hr'Q, hr'eq⟩ := hsmap
  have hqω : q * ω = ω * q := (h.om_cent_Y q hqY).symm
  have hkey : q * ω * (q⁻¹ * r) = ω * r := by
    rw [hqω]; group
  have hωr : ω * r = φ.toMonoidHom (τ * r') := by
    have huM : φ.toMonoidHom τ = q * ω := hu
    rw [← hkey]
    calc q * ω * (q⁻¹ * r) = φ.toMonoidHom τ * (q⁻¹ * r) := by rw [← huM]
      _ = φ.toMonoidHom τ * φ.toMonoidHom r' := by rw [← hr'eq]
      _ = φ.toMonoidHom (τ * r') := (map_mul φ.toMonoidHom τ r').symm
  have hsq : (ω * r) ^ 2 = 1 := by
    rw [hωr, ← map_pow, h.sq_tau_mul hr'Q, map_one]
  exact hr2 hsq

private theorem phi_tau_mem_omtau (h : Setting16 Q Y τ ω) (φ : G ≃* G)
    (hmapQ : Q.map φ.toMonoidHom = Q) {q : G} (hq : q ∈ Q)
    (hu : φ τ = q * (τ * ω)) : False := by
  have hu2 : (φ τ) ^ 2 = 1 := by rw [← map_pow, h.tau_sq, map_one]
  have hωτ2 : (ω * τ) ^ 2 = 1 := by
    rw [pow_two]
    calc (ω * τ) * (ω * τ) = ω * (τ * ω) * τ := by group
      _ = ω * (ω * τ) * τ := by rw [h.tau_om]
      _ = (ω * ω) * (τ * τ) := by group
      _ = 1 := by
          rw [show ω * ω = 1 by rw [← pow_two, h.om_sq],
              show τ * τ = 1 by rw [← pow_two, h.tau_sq], mul_one]
  have hωτinv : (ω * τ)⁻¹ = ω * τ := by
    apply inv_eq_of_mul_eq_one_right
    rwa [pow_two] at hωτ2
  have hωτsq : (ω * τ) * (ω * τ) = 1 := by rwa [pow_two] at hωτ2
  have hqY : q ∈ Y := by
    set q₁ : G := (ω * τ) * q * (ω * τ) with hq₁def
    have hq1Q : q₁ ∈ Q := by
      have hc := h.normal.conj_mem q hq (ω * τ)
      rw [hωτinv] at hc
      rw [hq₁def]; exact hc
    have hq1Y : q₁ ∈ Y := by
      apply h.invol_omtau (q := q₁) hq1Q
      have hkey : (ω * τ) * q₁ = φ τ := by
        rw [hq₁def, hu, h.tau_om]
        rw [show (ω * τ) * ((ω * τ) * q * (ω * τ))
              = ((ω * τ) * (ω * τ)) * q * (ω * τ) by group, hωτsq]
        group
      rw [hkey]; exact hu2
    have hcommωτ : (ω * τ) * q₁ = q₁ * (ω * τ) := by
      calc (ω * τ) * q₁ = ω * (τ * q₁) := by group
        _ = ω * (q₁ * τ) := by rw [tau_cent_Y h hq1Y]
        _ = (ω * q₁) * τ := by group
        _ = (q₁ * ω) * τ := by rw [h.om_cent_Y q₁ hq1Y]
        _ = q₁ * (ω * τ) := by group
    have h1 : (ω * τ) * q₁ * (ω * τ) = q₁ := by
      rw [hcommωτ, mul_assoc, hωτsq, mul_one]
    have h2 : (ω * τ) * q₁ * (ω * τ) = q := by
      rw [hq₁def]
      calc (ω * τ) * ((ω * τ) * q * (ω * τ)) * (ω * τ)
            = ((ω * τ) * (ω * τ)) * q * ((ω * τ) * (ω * τ)) := by group
        _ = q := by rw [hωτsq]; group
    rw [← h2, h1]
    exact hq1Y
  obtain ⟨r, hrQ, hr2⟩ := h.exists_omtau_noninv
  have hsmap : q⁻¹ * r ∈ Q.map φ.toMonoidHom := by
    rw [hmapQ]; exact mul_mem (inv_mem hq) hrQ
  obtain ⟨r', hr'Q, hr'eq⟩ := hsmap
  have hu' : φ τ = q * (ω * τ) := by rw [hu, h.tau_om]
  have hqcomm : q * (ω * τ) = (ω * τ) * q := by
    have h1 : q * ω = ω * q := (h.om_cent_Y q hqY).symm
    have h2 : q * τ = τ * q := (tau_cent_Y h hqY).symm
    calc q * (ω * τ) = (q * ω) * τ := by group
      _ = (ω * q) * τ := by rw [h1]
      _ = ω * (q * τ) := by group
      _ = ω * (τ * q) := by rw [h2]
      _ = (ω * τ) * q := by group
  have hkey : q * (ω * τ) * (q⁻¹ * r) = ω * τ * r := by
    calc q * (ω * τ) * (q⁻¹ * r) = (ω * τ) * q * (q⁻¹ * r) := by rw [hqcomm]
      _ = (ω * τ) * r := by group
  have hωτr : ω * τ * r = φ.toMonoidHom (τ * r') := by
    have huM' : φ.toMonoidHom τ = q * (ω * τ) := hu'
    rw [← hkey]
    calc q * (ω * τ) * (q⁻¹ * r) = φ.toMonoidHom τ * (q⁻¹ * r) := by rw [← huM']
      _ = φ.toMonoidHom τ * φ.toMonoidHom r' := by rw [← hr'eq]
      _ = φ.toMonoidHom (τ * r') := (map_mul φ.toMonoidHom τ r').symm
  have hsq : (ω * τ * r) ^ 2 = 1 := by
    rw [hωτr, ← map_pow, h.sq_tau_mul hr'Q, map_one]
  exact hr2 hsq

theorem phi_tau_mem (h : Setting16 Q Y τ ω) (φ : G ≃* G) : ∃ q ∈ Q, φ τ = q * τ := by
  have hmapQ : Q.map φ.toMonoidHom = Q := map_Q_eq h φ
  have hu_notQ : φ τ ∉ Q := by
    intro hu
    have hmem : φ τ ∈ Q.map φ.toMonoidHom := by rw [hmapQ]; exact hu
    obtain ⟨q, hqQ, hqeq⟩ := hmem
    exact h.tau_not_mem (φ.injective hqeq ▸ hqQ)
  obtain ⟨q, hq, hu | hu | hu | hu⟩ := h.cosets (φ τ)
  · exact absurd (hu ▸ hq) hu_notQ
  · exact ⟨q, hq, hu⟩
  · exact (phi_tau_mem_om h φ hmapQ hq hu).elim
  · exact (phi_tau_mem_omtau h φ hmapQ hq hu).elim

theorem char_Qtau (h : Setting16 Q Y τ ω) : (Q ⊔ zpowers τ).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_sup, map_Q_eq h φ, MonoidHom.map_zpowers]
  apply sup_le le_sup_left
  rw [Subgroup.zpowers_le]
  change φ τ ∈ Q ⊔ zpowers τ
  obtain ⟨q, hq, hqτ⟩ := phi_tau_mem h φ
  rw [hqτ]
  exact mul_mem (Subgroup.mem_sup_left hq)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ))

private theorem om_mul_not_mem_sup (h : Setting16 Q Y τ ω) {y : G} (hy : y ∈ Y) :
    ω * y ∉ Q ⊔ zpowers τ := by
  intro hmem
  rcases (mem_sup_zpowers_iff h.tau_sq h.tau_inv).mp hmem with hQ | ⟨q, hq, hqeq⟩
  · refine h.om_not_mem ?_
    have : ω = (ω * y) * y⁻¹ := by group
    rw [this]
    exact mul_mem hQ (inv_mem (h.Y_le_Q hy))
  · have hτω : τ * ω = q⁻¹ * y := by
      calc τ * ω = q⁻¹ * (ω * y) * ω := by rw [hqeq]; group
        _ = q⁻¹ * (ω * y * ω) := by group
        _ = q⁻¹ * y := by rw [h.om_conj_Y hy]
    exact h.tau_om_not_mem (hτω ▸ mul_mem (inv_mem hq) (h.Y_le_Q hy))

private theorem tau_om_mul_not_mem_sup (h : Setting16 Q Y τ ω) {y : G} (hy : y ∈ Y) :
    (τ * ω) * y ∉ Q ⊔ zpowers τ := by
  intro hmem
  rcases (mem_sup_zpowers_iff h.tau_sq h.tau_inv).mp hmem with hQ | ⟨q, hq, hqeq⟩
  · refine h.tau_om_not_mem ?_
    have : τ * ω = ((τ * ω) * y) * y⁻¹ := by group
    rw [this]
    exact mul_mem hQ (inv_mem (h.Y_le_Q hy))
  · have hττ : τ * τ = 1 := by rw [← pow_two, h.tau_sq]
    have hω : ω = q⁻¹ * y⁻¹ := by
      have hqeq' : τ * ω = q * τ * y⁻¹ := by rw [← hqeq]; group
      calc ω = τ * (τ * ω) := by
            rw [show τ * (τ * ω) = (τ * τ) * ω by group, hττ]; group
        _ = τ * (q * τ * y⁻¹) := by rw [hqeq']
        _ = (τ * q * τ) * y⁻¹ := by group
        _ = q⁻¹ * y⁻¹ := by rw [tau_conj h hq]
    exact h.om_not_mem (hω ▸ mul_mem (inv_mem hq) (inv_mem (h.Y_le_Q hy)))

theorem tauY_eq_inf (h : Setting16 Q Y τ ω) :
    zpowers τ ⊔ Y = (closure ({τ, ω} : Set G) ⊔ Y) ⊓ (Q ⊔ zpowers τ) := by
  apply le_antisymm
  · apply sup_le
    · refine le_inf ?_ le_sup_right
      exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
    · exact le_inf le_sup_right (le_trans h.Y_le_Q le_sup_left)
  · intro x hx
    obtain ⟨hxE6, hxQτ⟩ := hx
    obtain ⟨y, hyY, hxy | hxy | hxy | hxy⟩ := h.mem_E6_iff.mp hxE6
    · rw [hxy]; exact Subgroup.mem_sup_right hyY
    · rw [hxy]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers τ))
        (Subgroup.mem_sup_right hyY)
    · rw [hxy] at hxQτ
      exact absurd hxQτ (om_mul_not_mem_sup h hyY)
    · rw [hxy] at hxQτ
      exact absurd hxQτ (tau_om_mul_not_mem_sup h hyY)

theorem char_tauY (h : Setting16 Q Y τ ω) : (zpowers τ ⊔ Y).Characteristic := by
  rw [tauY_eq_inf h]
  haveI := h.char_E6
  haveI := h.char_Qtau
  infer_instance

end Setting16

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
