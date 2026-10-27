module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Th2.HY

open Subgroup
open scoped commutatorElement

theorem normal_subgroupOf_of_conj_mem {Q : Type*} [Group Q] {L N : Subgroup Q}
    (hN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) : (N.subgroupOf L).Normal :=
  ⟨fun n hn g => hN g g.2 n hn⟩

theorem eq_one_of_two_pow_of_mem_odd {Q : Type*} [Group Q] {O : Subgroup Q}
    (hO : Odd (Nat.card ↥O)) {z : Q} (hz : z ∈ O) {k : ℕ} (hk : z ^ (2 ^ k) = 1) : z = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥O) := (Nat.coprime_two_left.mpr hO).pow_left k
  have h1 : orderOf z = 1 :=
    (hcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)).eq_one_of_dvd
      (Subgroup.orderOf_dvd_natCard O hz)
  exact orderOf_eq_one_iff.mp h1

theorem not_odd_card_of_le_closure {Q : Type*} [Group Q] {L : Subgroup Q}
    (hL : CFSG.IsQuasisimple ↥L)
    (hgen : L ≤ Subgroup.closure {t : Q | t ∈ L ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1}) :
    ¬ Odd (Nat.card ↥L) := by
  intro hodd
  have hbot : L ≤ ⊥ := by
    refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
    rintro t ⟨ht, k, hk⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_two_pow_of_mem_odd hodd ht hk)
  have := CFSG.LocalCores.isQuasisimple_nontrivial hL
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
  exact hx (Subtype.ext (Subgroup.mem_bot.mp (hbot x.2)))

theorem exists_not_commute_of_isQuasisimple {Q : Type*} [Group Q] {L : Subgroup Q}
    (hL : CFSG.IsQuasisimple ↥L) : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hL
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, a.2, b, b.2, fun h => hab ?_⟩
  have h' : a * b = b * a := Subtype.ext h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']

theorem commute_of_odd_normal {Q : Type*} [Group Q] {L N : Subgroup Q}
    (hL : CFSG.IsQuasisimple ↥L) (hLeven : ¬ Odd (Nat.card ↥L)) (hNL : N ≤ L)
    (hNn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) (hNodd : Odd (Nat.card ↥N)) :
    ∀ n ∈ N, ∀ l ∈ L, n * l = l * n := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL (normal_subgroupOf_of_conj_mem hNn) with
    h | h
  · exfalso
    apply hLeven
    have hcard : Nat.card ↥(N.subgroupOf L) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
    rw [h, Subgroup.card_top] at hcard
    rwa [hcard]
  · intro n hn l hl
    have hc := Subgroup.mem_center_iff.mp
      (h (show (⟨n, hNL hn⟩ : ↥L) ∈ N.subgroupOf L from hn)) ⟨l, hl⟩
    exact (congrArg Subtype.val hc).symm

theorem commutatorElement_mul_mul_of_pair_commute {Q : Type*} [Group Q] {a b z w : Q}
    (hzb : Commute z b) (hzw : Commute z w) (hwa : Commute w a) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by
        group
    _ = a * (b * z) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb.eq]
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * w * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzw.eq, mul_inv_cancel_right]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hwa.inv_right.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_of_cover_odd {Q : Type} [Group Q] {L A W : Subgroup Q} (hL : CFSG.IsQuasisimple ↥L)
    (hA : A ≤ L) (hW : W ≤ L) (hWn : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W)
    (hWodd : Odd (Nat.card ↥W)) (hLeven : ¬ Odd (Nat.card ↥L))
    (hcov : ∀ l ∈ L, ∃ s ∈ A, ∃ w ∈ W, l = s * w) : A = L := by
  have hcent := commute_of_odd_normal hL hLeven hW hWn hWodd
  refine le_antisymm hA ?_
  calc L = ⁅L, L⁆ := (Subgroup.isPerfect_iff.mp hL.1).symm
    _ ≤ A := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨s₁, hs₁, w₁, hw₁, rfl⟩ := hcov x hx
      obtain ⟨s₂, hs₂, w₂, hw₂, rfl⟩ := hcov y hy
      rw [commutatorElement_mul_mul_of_pair_commute (hcent w₁ hw₁ s₂ (hA hs₂))
        (hcent w₁ hw₁ w₂ (hW hw₂)) (hcent w₂ hw₂ s₁ (hA hs₁)), commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem hs₁ hs₂) (A.inv_mem hs₁)) (A.inv_mem hs₂)

theorem centralizes_of_normalizes_of_commutators_odd {Q : Type*} [Group Q] {L O : Subgroup Q}
    (hL : CFSG.IsQuasisimple ↥L) (hLeven : ¬ Odd (Nat.card ↥L)) (hO : Odd (Nat.card ↥O)) {y : Q}
    (hyn : ∀ σ ∈ L, y * σ * y⁻¹ ∈ L) (hc : ∀ σ ∈ L, ⁅σ, y⁆ ∈ O) :
    ∀ σ ∈ L, y * σ * y⁻¹ = σ := by
  have hcomm_mem : ∀ σ ∈ L, ⁅σ, y⁆ ∈ L := by
    intro σ hσ
    have h : ⁅σ, y⁆ = σ * (y * σ⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [h]
    exact L.mul_mem hσ (hyn σ⁻¹ (L.inv_mem hσ))
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Subgroup Q, Ψ = Subgroup.closure {g : Q | ∃ σ ∈ L, g = ⁅σ, y⁆} :=
    ⟨_, rfl⟩
  have hgenΨ : ∀ σ ∈ L, ⁅σ, y⁆ ∈ Ψ := fun σ hσ => hΨ ▸ Subgroup.subset_closure ⟨σ, hσ, rfl⟩
  have hΨL : Ψ ≤ L := by
    rw [hΨ, Subgroup.closure_le]
    rintro g ⟨σ, hσ, rfl⟩
    exact hcomm_mem σ hσ
  have hΨO : Ψ ≤ O := by
    rw [hΨ, Subgroup.closure_le]
    rintro g ⟨σ, hσ, rfl⟩
    exact hc σ hσ
  have hΨn : ∀ l ∈ L, ∀ n ∈ Ψ, l * n * l⁻¹ ∈ Ψ := by
    intro l hl n hn
    rw [hΨ] at hn
    induction hn using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨σ, hσ, rfl⟩ := hg
      have h : l * ⁅σ, y⁆ * l⁻¹ = ⁅l * σ, y⁆ * ⁅l, y⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [h]
      exact Ψ.mul_mem (hgenΨ _ (L.mul_mem hl hσ)) (Ψ.inv_mem (hgenΨ _ hl))
    | one => simp
    | mul a b _ _ ha hb =>
      have h : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
      rw [h]
      exact Ψ.mul_mem ha hb
    | inv a _ ha =>
      have h : l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ := by group
      rw [h]
      exact Ψ.inv_mem ha
  have hcent := commute_of_odd_normal hL hLeven hΨL hΨn
    (hO.of_dvd_nat (Subgroup.card_dvd_of_le hΨO))
  have hconj : ∀ σ ∈ L, y * σ * y⁻¹ = σ * ⁅σ, y⁆⁻¹ := by
    intro σ hσ
    have h1 : Commute ⁅σ, y⁆ σ := hcent _ (hgenΨ σ hσ) σ hσ
    rw [← h1.inv_left.eq, commutatorElement_def]
    group
  have hfix : ∀ a ∈ L, ∀ b ∈ L, y * ⁅a, b⁆ * y⁻¹ = ⁅a, b⁆ := by
    intro a ha b hb
    have h : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [h, hconj a ha, hconj b hb]
    have h1 : Commute ⁅a, y⁆ b := hcent _ (hgenΨ a ha) b hb
    have h2 : Commute ⁅a, y⁆ ⁅b, y⁆ := hcent _ (hgenΨ a ha) _ (hcomm_mem b hb)
    have h3 : Commute ⁅b, y⁆ a := hcent _ (hgenΨ b hb) a ha
    exact commutatorElement_mul_mul_of_pair_commute h1.inv_left h2.inv_left.inv_right h3.inv_left
  intro σ hσ
  have hle : L ≤ centralizer ({y} : Set Q) := by
    calc L = ⁅L, L⁆ := (Subgroup.isPerfect_iff.mp hL.1).symm
      _ ≤ centralizer ({y} : Set Q) := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact mul_inv_eq_iff_eq_mul.mp (hfix a ha b hb)
  rw [(Subgroup.mem_centralizer_iff.mp (hle hσ)) y rfl, mul_inv_cancel_right]

theorem false_of_commute_conj_of_commutators_odd {Q : Type*} [Group Q] {L O : Subgroup Q}
    (hL : CFSG.IsQuasisimple ↥L)
    (hgen : L ≤ Subgroup.closure {t : Q | t ∈ L ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1})
    (hO : Odd (Nat.card ↥O)) {y : Q} (hc : ∀ σ ∈ L, ⁅σ, y⁆ ∈ O)
    (hcomm : ∀ x ∈ L, ∀ t ∈ L, x * (y * t * y⁻¹) = y * t * y⁻¹ * x) : False := by
  have hcent : ∀ t ∈ L, ∀ k : ℕ, t ^ (2 ^ k) = 1 → ∀ x ∈ L, x * t = t * x := by
    intro t ht k hk x hx
    have hzk : ⁅t, y⁆ ^ (2 ^ k) = 1 := by
      have h : ⁅t, y⁆ = t * (y * t * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      have hcom0 : Commute t (y * t * y⁻¹) := hcomm t ht t ht
      have hcom : Commute t (y * t * y⁻¹)⁻¹ := hcom0.inv_right
      rw [h, hcom.mul_pow, inv_pow, conj_pow, hk, mul_one, mul_inv_cancel, inv_one, mul_one]
    have h1 : ⁅t, y⁆ = 1 := eq_one_of_two_pow_of_mem_odd hO (hc t ht) hzk
    have h2 : y * t * y⁻¹ = t := by
      calc y * t * y⁻¹ = t * y * y⁻¹ := by rw [commutatorElement_eq_one_iff_mul_comm.mp h1]
        _ = t := mul_inv_cancel_right t y
    have h3 := hcomm x hx t ht
    rwa [h2] at h3
  obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute_of_isQuasisimple hL
  refine hab ?_
  have hle : L ≤ centralizer ({a} : Set Q) := by
    refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
    rintro t ⟨ht, k, hk⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    exact hcent t ht k hk a ha
  exact (Subgroup.mem_centralizer_iff.mp (hle hb)) a rfl

theorem comp_centralizes_of_commutators_odd {Q : Type} [Group Q] [Finite Q] {L O : Subgroup Q}
    (hL : CFSG.IsComponent L)
    (hgen : L ≤ Subgroup.closure {t : Q | t ∈ L ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1})
    (hO : Odd (Nat.card ↥O)) {y : Q} (hc : ∀ σ ∈ L, ⁅σ, y⁆ ∈ O) :
    ∀ σ ∈ L, y * σ * y⁻¹ = σ := by
  by_cases hyL : L.map (MulAut.conj y).toMonoidHom = L
  · refine centralizes_of_normalizes_of_commutators_odd hL.1 (not_odd_card_of_le_closure hL.1 hgen)
      hO ?_ hc
    intro σ hσ
    have h := Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hσ
    rw [hyL] at h
    exact h
  · exfalso
    have hL' : CFSG.IsComponent (L.map (MulAut.conj y).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hL
    have hLL' : ⁅L, L.map (MulAut.conj y).toMonoidHom⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hL hL').resolve_left fun h => hyL h.symm
    refine false_of_commute_conj_of_commutators_odd hL.1 hgen hO hc fun x hx t ht => ?_
    have h := Subgroup.commutator_mem_commutator hx
      (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom ht)
    rw [hLL', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h

end CFSG.GH74.GLS.Th2.HY
