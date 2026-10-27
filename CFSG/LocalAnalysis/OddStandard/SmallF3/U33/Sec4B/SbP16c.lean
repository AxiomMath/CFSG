module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSub

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

namespace Setting16

variable {G : Type} [Group G] [Finite G] {Q Y : Subgroup G} {τ ω : G}

private lemma mem_zpowers_tau_iff (h : Setting16 Q Y τ ω) {x : G} :
    x ∈ zpowers τ ↔ x = 1 ∨ x = τ := by
  have h2 : τ ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, h.tau_sq]
  constructor
  · intro hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
    · left
      rw [hm, zpow_mul, h2, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (h1 | hτ)
    · rw [h1]; exact Subgroup.one_mem _
    · rw [hτ]; exact Subgroup.mem_zpowers τ

private lemma closure_pair_comm (h : Setting16 Q Y τ ω) {a b : G}
    (ha : a ∈ closure ({τ, ω} : Set G)) (hb : b ∈ closure ({τ, ω} : Set G)) :
    a * b = b * a := by
  have hcomm : ({τ, ω} : Set G).Pairwise Commute := by
    intro x hx y hy hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hne
    · exact h.tau_om
    · exact h.tau_om.symm
    · exact absurd rfl hne
  haveI := Subgroup.isMulCommutative_closure hcomm
  exact setLike_mul_comm ha hb

private lemma mul_comm_of_center (h : Setting16 Q Y τ ω) {α β y₁ y₂ : G}
    (hα : α ∈ closure ({τ, ω} : Set G)) (hβ : β ∈ closure ({τ, ω} : Set G))
    (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y) :
    (α * y₁) * (β * y₂) = (β * y₂) * (α * y₁) := by
  have hc₁ : ∀ z, Commute y₁ z := fun z =>
    (Subgroup.mem_center_iff.mp (h.Y_le_center hy₁) z).symm
  have hc₂ : ∀ z, Commute y₂ z := fun z =>
    (Subgroup.mem_center_iff.mp (h.Y_le_center hy₂) z).symm
  have h1 : Commute (α * y₁) β :=
    Commute.mul_left (show Commute α β from closure_pair_comm h hα hβ) (hc₁ β)
  have h2 : Commute (α * y₁) y₂ :=
    Commute.mul_left (hc₂ α).symm (hc₂ y₁).symm
  exact (Commute.mul_right h1 h2).eq

theorem mem_E6_iff (h : Setting16 Q Y τ ω) {x : G} :
    x ∈ closure ({τ, ω} : Set G) ⊔ Y ↔
      ∃ y ∈ Y, x = y ∨ x = τ * y ∨ x = ω * y ∨ x = (τ * ω) * y := by
  haveI : Y.Normal := Y.normal_of_le_center h.Y_le_center
  rw [Subgroup.mem_sup_of_normal_right]
  constructor
  · rintro ⟨a, ha, y, hy, rfl⟩
    rw [h.mem_closure_pair_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨y, hy, Or.inl (one_mul y)⟩
    · exact ⟨y, hy, Or.inr (Or.inl rfl)⟩
    · exact ⟨y, hy, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨y, hy, Or.inr (Or.inr (Or.inr rfl))⟩
  · rintro ⟨y, hy, hxy | hxy | hxy | hxy⟩
    · rw [hxy]
      exact ⟨1, Subgroup.one_mem _, y, hy, one_mul y⟩
    · rw [hxy]
      exact ⟨τ, Subgroup.subset_closure (by simp), y, hy, rfl⟩
    · rw [hxy]
      exact ⟨ω, Subgroup.subset_closure (by simp), y, hy, rfl⟩
    · rw [hxy]
      have hmem : τ * ω ∈ closure ({τ, ω} : Set G) :=
        (closure ({τ, ω} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      exact ⟨τ * ω, hmem, y, hy, rfl⟩

theorem E6_comm (h : Setting16 Q Y τ ω) {a b : G} (ha : a ∈ closure ({τ, ω} : Set G) ⊔ Y)
    (hb : b ∈ closure ({τ, ω} : Set G) ⊔ Y) : a * b = b * a := by
  rw [mem_E6_iff h] at ha hb
  obtain ⟨y₁, hy₁, ha⟩ := ha
  obtain ⟨y₂, hy₂, hb⟩ := hb
  have key₁ : ∀ u : G, (u = y₁ ∨ u = τ * y₁ ∨ u = ω * y₁ ∨ u = (τ * ω) * y₁) →
      ∃ α ∈ closure ({τ, ω} : Set G), u = α * y₁ := by
    rintro u (rfl | rfl | rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by rw [one_mul]⟩
    · exact ⟨τ, Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨ω, Subgroup.subset_closure (by simp), rfl⟩
    · have hmem : τ * ω ∈ closure ({τ, ω} : Set G) :=
        (closure ({τ, ω} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      exact ⟨τ * ω, hmem, rfl⟩
  have key₂ : ∀ u : G, (u = y₂ ∨ u = τ * y₂ ∨ u = ω * y₂ ∨ u = (τ * ω) * y₂) →
      ∃ β ∈ closure ({τ, ω} : Set G), u = β * y₂ := by
    rintro u (rfl | rfl | rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by rw [one_mul]⟩
    · exact ⟨τ, Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨ω, Subgroup.subset_closure (by simp), rfl⟩
    · have hmem : τ * ω ∈ closure ({τ, ω} : Set G) :=
        (closure ({τ, ω} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      exact ⟨τ * ω, hmem, rfl⟩
  obtain ⟨α, hα, haα⟩ := key₁ a ha
  obtain ⟨β, hβ, hbβ⟩ := key₂ b hb
  rw [haα, hbβ]
  exact mul_comm_of_center h hα hβ hy₁ hy₂

theorem E6_sq (h : Setting16 Q Y τ ω) {a : G} (ha : a ∈ closure ({τ, ω} : Set G) ⊔ Y) :
    a ^ 2 = 1 := by
  rw [mem_E6_iff h] at ha
  obtain ⟨y, hy, ha⟩ := ha
  have key : ∀ u : G, (u = y ∨ u = τ * y ∨ u = ω * y ∨ u = (τ * ω) * y) →
      ∃ α ∈ closure ({τ, ω} : Set G), α ^ 2 = 1 ∧ u = α * y := by
    rintro u (rfl | rfl | rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by simp, by rw [one_mul]⟩
    · exact ⟨τ, Subgroup.subset_closure (by simp), h.tau_sq, rfl⟩
    · exact ⟨ω, Subgroup.subset_closure (by simp), h.om_sq, rfl⟩
    · have hmem : τ * ω ∈ closure ({τ, ω} : Set G) :=
        (closure ({τ, ω} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      exact ⟨τ * ω, hmem,
        by rw [(show Commute τ ω from h.tau_om).mul_pow 2, h.tau_sq, h.om_sq, one_mul], rfl⟩
  obtain ⟨α, hα, hα2, haα⟩ := key a ha
  rw [haα]
  have hy2 : y ^ 2 = 1 := ((h.mem_Y y).mp hy).2
  have hc : Commute α y := Subgroup.mem_center_iff.mp (h.Y_le_center hy) α
  rw [hc.mul_pow 2, hα2, hy2, one_mul]

theorem card_E6 (h : Setting16 Q Y τ ω) : Nat.card ↥(closure ({τ, ω} : Set G) ⊔ Y) = 64 := by
  have hτ1 : τ ≠ 1 := fun h1 => h.tau_not_mem (h1 ▸ Q.one_mem)
  have hzω : ω ∉ zpowers τ := by
    intro hmem
    rcases (mem_zpowers_tau_iff h).mp hmem with h1 | hτ
    · exact h.om_not_mem (h1 ▸ Q.one_mem)
    · exact h.tau_om_not_mem (by rw [hτ, ← pow_two, h.tau_sq]; exact Q.one_mem)
  have hcardT : Nat.card ↥(closure ({τ, ω} : Set G)) = 4 :=
    card_closure_pair h.tau_sq hτ1 h.om_sq h.tau_om hzω
  have hinf : closure ({τ, ω} : Set G) ⊓ Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxT, hxY⟩ := Subgroup.mem_inf.mp hx
    rw [h.mem_closure_pair_iff] at hxT
    rcases hxT with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd (h.Y_le_Q hxY) h.tau_not_mem
    · exact absurd (h.Y_le_Q hxY) h.om_not_mem
    · exact absurd (h.Y_le_Q hxY) h.tau_om_not_mem
  have hcomm : ∀ x ∈ closure ({τ, ω} : Set G), ∀ y ∈ Y, x * y = y * x := by
    intro x _ y hy
    exact Subgroup.mem_center_iff.mp (h.Y_le_center hy) x
  have hcard_eq := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (closure ({τ, ω} : Set G)) Y hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one, hcardT, h.card_Y] at hcard_eq
  norm_num at hcard_eq
  exact hcard_eq

theorem inf_Q_le_Y (h : Setting16 Q Y τ ω) {E : Subgroup G} (hE2 : ∀ a ∈ E, a ^ 2 = 1) :
    E ⊓ Q ≤ Y := by
  intro x hx
  obtain ⟨hxE, hxQ⟩ := Subgroup.mem_inf.mp hx
  exact (h.mem_Y x).mpr ⟨hxQ, hE2 x hxE⟩

theorem E6_inf_sup (h : Setting16 Q Y τ ω) {E : Subgroup G}
    (hE2 : ∀ a ∈ E, a ^ 2 = 1) (hcard : Nat.card E = 64) : E ⊓ Q = Y ∧ E ⊔ Q = ⊤ := by
  have hle : E ⊓ Q ≤ Y := inf_Q_le_Y h hE2
  have hcard_inf_le : Nat.card ↥(E ⊓ Q) ≤ 16 := by
    have hc := Subgroup.card_le_of_le hle
    rwa [h.card_Y] at hc
  have hsup : E ⊔ Q = ⊤ := h.sup_Q_eq_top (A := E) (by omega) hcard_inf_le
  refine ⟨?_, hsup⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hbound := card_le_mul_card_inf_of_index_le h.index_le E
  rw [hcard] at hbound
  rw [h.card_Y]
  omega

theorem exists_mul_of_sup_eq_top (h : Setting16 Q Y τ ω) {E : Subgroup G} (hE : E ⊔ Q = ⊤)
    (x : G) : ∃ e ∈ E, ∃ q ∈ Q, x = e * q := by
  haveI := h.normal
  have hx : x ∈ E ⊔ Q := by rw [hE]; exact Subgroup.mem_top x
  rw [Subgroup.mem_sup_of_normal_right] at hx
  obtain ⟨e, he, q, hq, heq⟩ := hx
  exact ⟨e, he, q, hq, heq.symm⟩

theorem E6_unique (h : Setting16 Q Y τ ω) {E : Subgroup G}
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1)
    (hcard : Nat.card E = 64) : E = closure ({τ, ω} : Set G) ⊔ Y := by
  obtain ⟨hEQ, hEsup⟩ := E6_inf_sup h hE2 hcard
  have hmem_inf : ∀ y ∈ Y, y ∈ E := by
    intro y hy
    have hmem : y ∈ E ⊓ Q := by rw [hEQ]; exact hy
    exact (Subgroup.mem_inf.mp hmem).1
  have homE : ω ∈ E := by
    obtain ⟨e, he, q, hq, hx⟩ := exists_mul_of_sup_eq_top h hEsup ω
    have heq : ω * q⁻¹ = e := by rw [hx]; group
    have hqinvY : q⁻¹ ∈ Y :=
      h.invol_om q⁻¹ (Q.inv_mem hq) (by rw [heq]; exact hE2 e he)
    have hqE : q ∈ E := hmem_inf q (by simpa using Y.inv_mem hqinvY)
    rw [hx]
    exact E.mul_mem he hqE
  have hτωE : τ * ω ∈ E := by
    obtain ⟨e, he, q, hq, hx⟩ := exists_mul_of_sup_eq_top h hEsup (τ * ω)
    have heq : ω * τ * q⁻¹ = e := by rw [← h.tau_om, hx]; group
    have hqinvY : q⁻¹ ∈ Y :=
      h.invol_omtau q⁻¹ (Q.inv_mem hq) (by rw [heq]; exact hE2 e he)
    have hqE : q ∈ E := hmem_inf q (by simpa using Y.inv_mem hqinvY)
    rw [hx]
    exact E.mul_mem he hqE
  have hτE : τ ∈ E := by
    have hmem : (τ * ω) * ω⁻¹ ∈ E := E.mul_mem hτωE (E.inv_mem homE)
    rwa [show (τ * ω) * ω⁻¹ = τ by group] at hmem
  have hTle : closure ({τ, ω} : Set G) ≤ E := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hτE
    · exact homE
  have hE6le : closure ({τ, ω} : Set G) ⊔ Y ≤ E := sup_le hTle hmem_inf
  exact (Subgroup.eq_of_le_of_card_ge hE6le (by simp [card_E6 h, hcard])).symm

theorem char_E6 (h : Setting16 Q Y τ ω) : (closure ({τ, ω} : Set G) ⊔ Y).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  let E : Subgroup G := (closure ({τ, ω} : Set G) ⊔ Y).map φ.toMonoidHom
  have hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, E6_comm h ha' hb']
  have hE2 : ∀ a ∈ E, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_pow, E6_sq h ha', map_one]
  have hcard : Nat.card E = 64 := by
    dsimp [E]
    rw [Subgroup.card_map_of_injective φ.injective, card_E6 h]
  simpa [E] using E6_unique h (E := E) hE hE2 hcard

end Setting16

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
