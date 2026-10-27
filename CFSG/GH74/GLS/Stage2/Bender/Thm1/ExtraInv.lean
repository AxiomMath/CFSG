module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Inv

variable {G : Type} [Group G]

theorem commutator_mul_central {b₁ b₂ x y : G} (h₁x : Commute b₁ x) (h₁y : Commute b₁ y)
    (h₁₂ : Commute b₁ b₂) (h₂x : Commute b₂ x) (h₂y : Commute b₂ y) :
    ⁅b₁ * x, b₂ * y⁆ = ⁅x, y⁆ := by
  have e1 : ⁅b₁ * x, b₂ * y⁆ = b₁ * (x * b₂ * y * x⁻¹) * b₁⁻¹ * y⁻¹ * b₂⁻¹ := by
    simp only [commutatorElement_def]; group
  have hc : Commute b₁ (x * b₂ * y * x⁻¹) :=
    ((h₁x.mul_right h₁₂).mul_right h₁y).mul_right h₁x.inv_right
  have e2 : b₁ * (x * b₂ * y * x⁻¹) * b₁⁻¹ = x * b₂ * y * x⁻¹ := by
    rw [hc.eq]; group
  rw [e1, e2]
  have hc2 : Commute b₂ (y * x⁻¹ * y⁻¹) := (h₂y.mul_right h₂x.inv_right).mul_right h₂y.inv_right
  calc x * b₂ * y * x⁻¹ * y⁻¹ * b₂⁻¹ = x * (b₂ * (y * x⁻¹ * y⁻¹) * b₂⁻¹) := by group
    _ = x * (y * x⁻¹ * y⁻¹) := by rw [hc2.eq]; group
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

theorem exists_fixed_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : G} (hz : z * z = 1)
    {Q : Subgroup G} (hzQ : z ∈ normalizer (Q : Set G)) (hexp : ∀ x ∈ Q, x ^ p = 1) {q : G}
    (hq : q ∈ Q) : ∃ b ∈ Q, ∃ s ∈ ⁅Q, zpowers z⁆, z * b * z⁻¹ = b ∧ q = b * s := by
  obtain ⟨a, ha⟩ : ∃ a : G, a = q⁻¹ * (z * q * z⁻¹) := ⟨_, rfl⟩
  have hzqQ : z * q * z⁻¹ ∈ Q := (mem_normalizer_iff.mp hzQ q).mp hq
  have haQ : a ∈ Q := by rw [ha]; exact Q.mul_mem (Q.inv_mem hq) hzqQ
  have hainv : z * a * z⁻¹ = a⁻¹ := by rw [ha]; exact conj_inv_elt hz q
  have haR : a ∈ ⁅Q, zpowers z⁆ := by
    have h1 : ⁅q⁻¹, z⁆ = a := by rw [ha]; simp [commutatorElement_def, mul_assoc]
    rw [← h1]
    exact Subgroup.commutator_mem_commutator (Q.inv_mem hq) (Subgroup.mem_zpowers z)
  obtain ⟨s₀, hs₀, hs₀sq⟩ := exists_sqrt hp hp2 (hexp a haQ)
  have hs₀R : s₀ ∈ ⁅Q, zpowers z⁆ := (Subgroup.zpowers_le.mpr haR) hs₀
  refine ⟨q * s₀, Q.mul_mem hq ((Subgroup.zpowers_le.mpr haQ) hs₀), s₀⁻¹, Subgroup.inv_mem _ hs₀R,
    ?_, by group⟩
  have h1 : z * s₀ * z⁻¹ = s₀⁻¹ := inverts_zpowers hainv s₀ hs₀
  have h2 : z * q * z⁻¹ = q * a := by rw [ha]; group
  calc z * (q * s₀) * z⁻¹ = (z * q * z⁻¹) * (z * s₀ * z⁻¹) := by group
    _ = (q * a) * s₀⁻¹ := by rw [h2, h1]
    _ = q * s₀ := by rw [← hs₀sq]; group

theorem commutator_le_zOf {Q : Subgroup G} (hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥) : ⁅Q, Q⁆ ≤ zOf Q :=
  le_inf (commutator_le_left_of_normalizes Subgroup.le_normalizer)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcl)

theorem commutator_le_centralizer_of_fixed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : G}
    (hz : z * z = 1) {Q : Subgroup G} (hzQ : z ∈ normalizer (Q : Set G)) (hexp : ∀ x ∈ Q, x ^ p = 1)
    (hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥) (hZ : zOf Q ≤ Cen z) {y : G} (hyQ : y ∈ Q) (hyz : z * y * z⁻¹ = y) :
    ⁅Q, zpowers z⁆ ≤ centralizer ({y} : Set G) := by
  rw [Subgroup.commutator_le]
  intro q hq g hg
  rcases mem_zpowers_cases hz hg with h | h
  · rw [h]
    simp
  · rw [h]
    have hwdef : ⁅q, z⁆ = q * (z * q⁻¹ * z⁻¹) := by simp [commutatorElement_def, mul_assoc]
    have hzq : z * q⁻¹ * z⁻¹ ∈ Q := (mem_normalizer_iff.mp hzQ q⁻¹).mp (Q.inv_mem hq)
    have hwQ : ⁅q, z⁆ ∈ Q := by rw [hwdef]; exact Q.mul_mem hq hzq
    have hwinv : z * ⁅q, z⁆ * z⁻¹ = (⁅q, z⁆)⁻¹ := by
      rw [hwdef]
      calc z * (q * (z * q⁻¹ * z⁻¹)) * z⁻¹
          = (z * q * z⁻¹) * (z * (z * q⁻¹ * z⁻¹) * z⁻¹) := by group
        _ = (z * q * z⁻¹) * q⁻¹ := by rw [conj_conj_of_mul_self hz q⁻¹]
        _ = (q * (z * q⁻¹ * z⁻¹))⁻¹ := by group
    set w : G := ⁅q, z⁆ with hw
    have hcZ : ⁅w, y⁆ ∈ zOf Q :=
      commutator_le_zOf hcl (Subgroup.commutator_mem_commutator hwQ hyQ)
    have hcCen : ⁅w, y⁆ ∈ Cen z := hZ hcZ
    have hcfix : z * ⁅w, y⁆ * z⁻¹ = ⁅w, y⁆ := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hcCen
      rw [← this]; group
    have hcinv : z * ⁅w, y⁆ * z⁻¹ = (⁅w, y⁆)⁻¹ := by
      have hyw : ⁅y, w⁆ = (⁅w, y⁆)⁻¹ := (commutatorElement_inv w y).symm
      have hconj := conjugate_commutatorElement (g₁ := w) (g₂ := y) (g₃ := z)
      rw [hwinv, hyz, commutatorElement_inv_left, hyw] at hconj
      rw [hconj]
      have hcw : Commute w (⁅w, y⁆) := by
        exact Subgroup.mem_centralizer_iff.mp hcZ.2 w hwQ
      have h3 : w * (⁅w, y⁆)⁻¹ = (⁅w, y⁆)⁻¹ * w := hcw.inv_right.eq
      calc w⁻¹ * (⁅w, y⁆)⁻¹ * w = w⁻¹ * ((⁅w, y⁆)⁻¹ * w) := by group
        _ = w⁻¹ * (w * (⁅w, y⁆)⁻¹) := by rw [h3]
        _ = (⁅w, y⁆)⁻¹ := by group
    have hc1 : ⁅w, y⁆ = 1 := by
      by_contra hne
      exact ne_inv_of_prime hp hp2 hne (hexp _ hcZ.1) (hcfix.symm.trans hcinv)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp hc1

theorem eq_commutator_of_fixed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : G} (hz : z * z = 1)
    {Q : Subgroup G} (hzQ : z ∈ normalizer (Q : Set G)) (hexp : ∀ x ∈ Q, x ^ p = 1)
    (hQ' : ⁅Q, Q⁆ = zOf Q) (hfix : ∀ y ∈ Q, z * y * z⁻¹ = y → y ∈ zOf Q) :
    ⁅Q, zpowers z⁆ = Q := by
  have hRQ : ⁅Q, zpowers z⁆ ≤ Q := commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzQ)
  apply le_antisymm hRQ
  have hdec : ∀ q ∈ Q, ∃ b ∈ zOf Q, ∃ s ∈ ⁅Q, zpowers z⁆, q = b * s := by
    intro q hq
    obtain ⟨b, hbQ, s, hs, hbz, hqbs⟩ := exists_fixed_mul hp hp2 hz hzQ hexp hq
    exact ⟨b, hfix b hbQ hbz, s, hs, hqbs⟩
  have hcent : ∀ b ∈ zOf Q, ∀ x ∈ Q, Commute b x := fun b hb x hx =>
    (Subgroup.mem_centralizer_iff.mp hb.2 x hx).symm
  have hQ'R : ⁅Q, Q⁆ ≤ ⁅Q, zpowers z⁆ := by
    rw [Subgroup.commutator_le]
    intro q₁ hq₁ q₂ hq₂
    obtain ⟨b₁, hb₁, s₁, hs₁, rfl⟩ := hdec q₁ hq₁
    obtain ⟨b₂, hb₂, s₂, hs₂, rfl⟩ := hdec q₂ hq₂
    have hs₁Q := hRQ hs₁
    have hs₂Q := hRQ hs₂
    rw [commutator_mul_central (hcent b₁ hb₁ s₁ hs₁Q) (hcent b₁ hb₁ s₂ hs₂Q)
      (hcent b₁ hb₁ b₂ hb₂.1) (hcent b₂ hb₂ s₁ hs₁Q) (hcent b₂ hb₂ s₂ hs₂Q)]
    have : ⁅s₁, s₂⁆ = s₁ * s₂ * s₁⁻¹ * s₂⁻¹ := commutatorElement_def s₁ s₂
    rw [this]
    exact (⁅Q, zpowers z⁆).mul_mem ((⁅Q, zpowers z⁆).mul_mem ((⁅Q, zpowers z⁆).mul_mem hs₁ hs₂)
      ((⁅Q, zpowers z⁆).inv_mem hs₁)) ((⁅Q, zpowers z⁆).inv_mem hs₂)
  intro q hq
  obtain ⟨b, hb, s, hs, rfl⟩ := hdec q hq
  exact (⁅Q, zpowers z⁆).mul_mem (hQ'R (hQ' ▸ hb)) hs

theorem not_isCyclic_sup {p : ℕ} (hp : p.Prime) {Q : Subgroup G} [Finite G]
    (hexp : ∀ x ∈ Q, x ^ p = 1) (hcard : Nat.card ↥(zOf Q) = p) {y : G} (hyQ : y ∈ Q)
    (hy : y ∉ zOf Q) : ¬ IsCyclic ↥(zOf Q ⊔ zpowers y) := by
  intro hcyc
  have hZQ : zOf Q ≤ Q := inf_le_left
  have hAQ : zOf Q ⊔ zpowers y ≤ Q := sup_le hZQ (Subgroup.zpowers_le.mpr hyQ)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(zOf Q ⊔ zpowers y))
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hexp (g : G) (hAQ g.2))
  have hord : orderOf g = Nat.card ↥(zOf Q ⊔ zpowers y) := orderOf_eq_card_of_forall_mem_zpowers hg
  have hle : Nat.card ↥(zOf Q ⊔ zpowers y) ≤ p :=
    hord ▸ Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  have heq : zOf Q = zOf Q ⊔ zpowers y :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard]; exact hle)
  exact hy (heq ▸ (le_sup_right : zpowers y ≤ zOf Q ⊔ zpowers y) (Subgroup.mem_zpowers y))

end Inv

end CFSG.GH74.GLS.Stage2.Bender.Thm1
