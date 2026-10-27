module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbalModel
public import Certificates.Certificate23204
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

theorem pow_eight_eq_one
    {ρ : Equiv.Perm (Fin 42)} (hρ : ρ ∈ R) (h16 : ρ ^ 16 = 1) : ρ ^ 8 = 1 :=
  Certificates.certificate23204.1 ρ hρ h16

theorem exists_sixteen_witness
    {t i : ℕ} (ht : t < 64) (hi : i < 36) (hc : candOK t i = true) :
    ∃ x ∈ allM, betaRepM 1 x = x ∧ pow4X (mulM x (betaYM t i x)) = (0, 2, 0) := by
  have hrep : TabRep (candTab t i) (wordPerm (tg t) * repPerm i) :=
    (tabRep_wordTab (tg t)).comp (tabRep_repTab hi)
  rw [candOK, Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have hρR : wordPerm (tg t) * repPerm i ∈ R := R.mul_mem (S_le_R (wordPerm_mem _)) (repPerm_mem i)
  have hconj : IsConj (⟨wordPerm (tg t) * repPerm i, hρR⟩ : R) r₄R :=
    (conjClass₄.1 _).2 ⟨candTab t i, Array.mem_toList_iff.mpr (Array.contains_iff.mp h3), hrep⟩
  obtain ⟨c, hcR, hce⟩ := eq_conj_of_isConj hconj
  exact Certificates.certificate23204.2.2 t ht i hi
    (((hrep.comp hrep).beq_iff TabRep.idTab).mp h2)
    (((hrep.comp tabRep_r₂).beq_iff (tabRep_r₂.comp hrep)).mp h1) ⟨c, hcR, hce⟩

theorem candOK_of {t i : ℕ} (hi : i < 36)
    (hρR : wordPerm (tg t) * repPerm i ∈ R)
    (hρ2 : wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1)
    (hρr : wordPerm (tg t) * repPerm i * r₂ = r₂ * (wordPerm (tg t) * repPerm i))
    (hconj : IsConj (⟨wordPerm (tg t) * repPerm i, hρR⟩ : R) r₄R) : candOK t i = true := by
  have hrep : TabRep (candTab t i) (wordPerm (tg t) * repPerm i) :=
    (tabRep_wordTab (tg t)).comp (tabRep_repTab hi)
  have h1 : (comp 42 (candTab t i) r₂T == comp 42 r₂T (candTab t i)) = true :=
    ((hrep.comp tabRep_r₂).beq_iff (tabRep_r₂.comp hrep)).mpr hρr
  have h2 : (comp 42 (candTab t i) (candTab t i) == idTab 42) = true :=
    ((hrep.comp hrep).beq_iff TabRep.idTab).mpr hρ2
  obtain ⟨t', ht', hrep'⟩ := (conjClass₄.1 _).1 hconj
  have h3 : orb4.contains (candTab t i) = true := by
    apply Array.contains_eq_true_of_mem
    rw [hrep.tab_eq hrep']
    exact Array.mem_toList_iff.mp ht'
  rw [candOK, h1, h2, h3]
  rfl

theorem card_centralizer_one_inf_S :
    Nat.card ↥(centralizer ({1} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 20160 := by
  have h : centralizer ({1} : Set (Equiv.Perm (Fin 42))) ⊓ S = S :=
    inf_eq_right.mpr fun s _ => mem_centralizer_singleton_iff.mpr (by simp)
  rw [h, card_S]

theorem orderOf_eq_two_of_card {ρ : Equiv.Perm (Fin 42)}
    (hρR : ρ ∈ R) (hρ2 : ρ * ρ = 1) {n : ℕ}
    (h : Nat.card ↥(centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S) = n) (hn : n ≠ 20160) :
    orderOf (⟨ρ, hρR⟩ : R) = 2 := by
  refine PSL3Four.orderOf_eq_two_of_mul_self (fun h1 => hn ?_) (Subtype.ext hρ2)
  have : ρ = 1 := congrArg Subtype.val h1
  rw [← h, this, card_centralizer_one_inf_S]

theorem exists_conj_r₂_of_card {ρ : Equiv.Perm (Fin 42)}
    (hρR : ρ ∈ R) (hρ2 : ρ * ρ = 1)
    (h : Nat.card ↥(centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 168) :
    ∃ c ∈ R, ρ = c * r₂ * c⁻¹ := by
  rcases (PSL3Four.orderOf_eq_two_iff _).1 (orderOf_eq_two_of_card hρR hρ2 h (by norm_num))
    with hc | hc | hc | hc
  · have h1 := card_centralizer_S_of_isConj hc
    have h2 : Nat.card C₁ = 64 := card_C₁
    rw [C₁] at h2
    rw [h] at h1
    exact absurd (h1.trans h2) (by norm_num)
  · exact eq_conj_of_isConj hc
  · have h1 := card_centralizer_S_of_isConj hc
    have h2 : Nat.card C₃ = 60 := card_C₃
    rw [C₃] at h2
    rw [h] at h1
    exact absurd (h1.trans h2) (by norm_num)
  · have h1 := card_centralizer_S_of_isConj hc
    have h2 : Nat.card C₄ = 72 := card_C₄
    rw [C₄] at h2
    rw [h] at h1
    exact absurd (h1.trans h2) (by norm_num)

theorem exists_conj_r₄_of_card {ρ : Equiv.Perm (Fin 42)}
    (hρR : ρ ∈ R) (hρ2 : ρ * ρ = 1)
    (h : Nat.card ↥(centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 72) :
    IsConj (⟨ρ, hρR⟩ : R) r₄R := by
  rcases (PSL3Four.orderOf_eq_two_iff _).1 (orderOf_eq_two_of_card hρR hρ2 h (by norm_num))
    with hc | hc | hc | hc
  · have h1 := card_centralizer_S_of_isConj hc
    have h2 : Nat.card C₁ = 64 := card_C₁
    rw [C₁] at h2
    rw [h] at h1
    exact absurd (h1.trans h2) (by norm_num)
  · have h1 := card_centralizer_S_of_isConj hc
    have h2 : Nat.card C₂ = 168 := card_C₂
    rw [C₂] at h2
    rw [h] at h1
    exact absurd (h1.trans h2) (by norm_num)
  · have h1 := card_centralizer_S_of_isConj hc
    have h2 : Nat.card C₃ = 60 := card_C₃
    rw [C₃] at h2
    rw [h] at h1
    exact absurd (h1.trans h2) (by norm_num)
  · exact hc

theorem g₄_mul_r₄ : g₄ * r₄ = r₄ * g₄ :=
  Certificates.certificate23204.2.1

theorem r₂_mul_r₃ : r₂ * r₃ = r₃ * r₂ := by
  have h := r₄_mul_self
  rw [r₄] at h
  have h2 : g₅ * g₅ = 1 := r₂_mul_self
  have h3 : g₆ * g₆ = 1 := r₃_mul_self
  show g₅ * g₆ = g₆ * g₅
  calc g₅ * g₆ = (g₅ * g₆) * (g₅ * g₆) * (g₆ * g₅) := by
        rw [show (g₅ * g₆) * (g₅ * g₆) * (g₆ * g₅) = g₅ * g₆ * g₅ * (g₆ * g₆) * g₅ by group, h3]
        rw [mul_one, mul_assoc, h2, mul_one]
    _ = g₆ * g₅ := by rw [h, one_mul]

theorem r₂_mul_r₄ : r₂ * r₄ = r₄ * r₂ := by
  show g₅ * (g₅ * g₆) = g₅ * g₆ * g₅
  have h : g₅ * g₆ = g₆ * g₅ := r₂_mul_r₃
  rw [mul_assoc g₅ g₆ g₅, ← h, ← mul_assoc]

theorem r₃_mul_r₄ : r₃ * r₄ = r₄ * r₃ := by
  show g₆ * (g₅ * g₆) = g₅ * g₆ * g₆
  have h : g₅ * g₆ = g₆ * g₅ := r₂_mul_r₃
  rw [← mul_assoc, ← h]

theorem conj_r₄_mul_mem_S
    {σ : Equiv.Perm (Fin 42)} (hσ : σ ∈ R) : σ * r₄ * σ⁻¹ * r₄⁻¹ ∈ S := by
  have hcomm : ∀ g : Equiv.Perm (Fin 42), g * r₄ = r₄ * g → g * r₄ * g⁻¹ * r₄⁻¹ ∈ S := by
    intro g hg
    rw [hg, mul_inv_cancel_right, mul_inv_cancel]
    exact S.one_mem
  have hS : ∀ g ∈ S, g * r₄ * g⁻¹ * r₄⁻¹ ∈ S := by
    intro g hg
    rw [show g * r₄ * g⁻¹ * r₄⁻¹ = g * (r₄ * g⁻¹ * r₄⁻¹) by group]
    exact S.mul_mem hg (conj_mem_S r₄_mem_R (S.inv_mem hg))
  induction hσ using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hS _ g₁_mem_S
    · exact hS _ g₂_mem_S
    · exact hS _ g₃_mem_S
    · exact hcomm _ g₄_mul_r₄
    · exact hcomm _ r₂_mul_r₄
    · exact hcomm _ r₃_mul_r₄
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [show x * y * r₄ * (x * y)⁻¹ * r₄⁻¹ =
      x * (y * r₄ * y⁻¹ * r₄⁻¹) * x⁻¹ * (x * r₄ * x⁻¹ * r₄⁻¹) by group]
    exact S.mul_mem (conj_mem_S hx ihy) ihx
  | inv x hx ihx =>
    rw [show x⁻¹ * r₄ * x⁻¹⁻¹ * r₄⁻¹ = x⁻¹ * (x * r₄ * x⁻¹ * r₄⁻¹)⁻¹ * x⁻¹⁻¹ by group]
    exact conj_mem_S (R.inv_mem hx) (S.inv_mem ihx)

theorem conj_r₄_mul_r₄_mem_S
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ R) : c * r₄ * c⁻¹ * r₄ ∈ S := by
  have h := conj_r₄_mul_mem_S hc
  rwa [inv_eq_of_mul_eq_one_right r₄_mul_self] at h

theorem conj_r₂_mul_r₄_not_mem_S
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ R) : c * r₂ * c⁻¹ * r₄ ∉ S := by
  intro h
  have h1 : r₂ * (c⁻¹ * r₄ * c * r₄⁻¹) * r₂⁻¹ * (r₂ * r₄) ∈ S := by
    have h2 := conj_mem_S (R.inv_mem hc) h
    rw [show r₂ * (c⁻¹ * r₄ * c * r₄⁻¹) * r₂⁻¹ * (r₂ * r₄) =
      c⁻¹ * (c * r₂ * c⁻¹ * r₄) * c⁻¹⁻¹ by group]
    exact h2
  have h3 : r₂ * (c⁻¹ * r₄ * c * r₄⁻¹) * r₂⁻¹ ∈ S := by
    have h4 := conj_r₄_mul_mem_S (R.inv_mem hc)
    rw [inv_inv] at h4
    exact conj_mem_S r₂_mem_R h4
  have h5 : r₂ * r₄ ∈ S := by
    have := S.mul_mem (S.inv_mem h3) h1
    rwa [inv_mul_cancel_left] at this
  have h6 : r₂ * r₄ = r₃ := by
    show g₅ * (g₅ * g₆) = g₆
    rw [← mul_assoc, show g₅ * g₅ = 1 from r₂_mul_self, one_mul]
  rw [h6] at h5
  exact not_mem_S_r₃ h5

variable {G : Type} [Group G]

theorem realization_mul_self {J : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {r : Equiv.Perm (Fin 42)} (hrR : r ∈ R)
    (hr : ∀ e, q (betaHat J hxN e) = r * q e * r⁻¹) : r * r = 1 := by
  have hc : r * r ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, R.mul_mem hrR hrR⟩
    obtain ⟨e, rfl⟩ := hqsurj s hs
    have h1 := hr (betaHat J hxN e)
    rw [betaHat_betaHat J hxN hx2, hr e] at h1
    calc q e * (r * r) = r * (r * q e * r⁻¹) * r⁻¹ * (r * r) := by rw [← h1]
      _ = r * r * q e := by group
  rw [centralizer_S_inf_R] at hc
  exact mem_bot.mp hc

theorem card_centralizer_of_count [Finite G] {J : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (J : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat J))
    {r : Equiv.Perm (Fin 42)} (hr : ∀ e, q (betaHat J hxN e) = r * q e * r⁻¹) {n : ℕ}
    (hcount : Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} = n * Nat.card (zStarIn J)) :
    Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S) = n := by
  have h1 := card_set_eq_of_realization hxN hqS hqsurj hqker hr
  rw [hcount] at h1
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm

end CFSG.ComponentClassification.TBLit.L34FU
