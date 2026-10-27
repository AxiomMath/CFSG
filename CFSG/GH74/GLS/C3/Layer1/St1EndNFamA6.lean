module

public import CFSG.GH74.KGroups.A6
public import Certificates.Certificate5159

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN.A6

open CFSG CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.A6
open scoped commutatorElement

theorem evenOrd_not_odd {g : Equiv.Perm (Fin 10)} (h : evenOrd g = true) : ¬ Odd (orderOf g) := by
  unfold evenOrd at h
  rcases Bool.or_eq_true_iff.1 h with h2 | h4
  · have := (orderIs_iff g (by norm_num)).1 h2
    rw [this]; decide
  · have := (orderIs_iff g (by norm_num)).1 h4
    rw [this]; decide

theorem a6check_sound :
    (∀ g ∈ QP.originalSubgroup, orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 4 ∨ orderOf g = 5) ∧
    ∀ τ ∈ QA.originalSubgroup, τ * τ = 1 → τ ≠ 1 → ∀ κ ∈ QP.originalSubgroup, τ * κ = κ * τ →
      orderOf κ = 3 →
      ∃ g ∈ QP.originalSubgroup, ∃ h ∈ QP.originalSubgroup, τ * g = g * τ ∧ τ * h = h * τ ∧
        ¬ Odd (orderOf ((κ * g * κ⁻¹ * g⁻¹) * (h * (κ * g * κ⁻¹ * g⁻¹) * h⁻¹))) := by
  have hc := Certificates.certificate5159
  unfold a6check at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hord, hmain⟩ := hc
  refine ⟨fun g hg => ?_, fun τ hτ hτ2 hτ1 κ hκ hκτ hκ3 => ?_⟩
  · have := (List.all_eq_true.1 hord) g ((mem_elemsT QP QP_ok g).2 hg)
    simp only [Bool.or_eq_true] at this
    rcases this with (((h1 | h2) | h3) | h4) | h5
    · exact Or.inl ((orderIs_iff g (by norm_num)).1 h1)
    · exact Or.inr (Or.inl ((orderIs_iff g (by norm_num)).1 h2))
    · exact Or.inr (Or.inr (Or.inl ((orderIs_iff g (by norm_num)).1 h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((orderIs_iff g (by norm_num)).1 h4))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((orderIs_iff g (by norm_num)).1 h5))))
  · have h1 := (List.all_eq_true.1 hmain) τ ((mem_elemsT QA QA_ok τ).2 hτ)
    have hcond : decide (τ * τ = 1 ∧ τ ≠ 1) = true := by simp [hτ2, hτ1]
    rw [hcond, Bool.cond_true] at h1
    set H := (elemsT QP).filter fun κ => decide (τ * κ = κ * τ) with hH
    have hκH : κ ∈ H := by
      rw [hH, List.mem_filter]
      exact ⟨(mem_elemsT QP QP_ok κ).2 hκ, by simpa using hκτ⟩
    have h2 := (List.all_eq_true.1 h1) κ hκH
    have h3 : orderIs κ 3 = true := (orderIs_iff κ (by norm_num)).2 hκ3
    rw [h3, Bool.cond_true] at h2
    unfold wit at h2
    obtain ⟨g, hgH, h2'⟩ := List.any_eq_true.1 h2
    obtain ⟨h', hhH, h2''⟩ := List.any_eq_true.1 h2'
    have hgH' := List.mem_filter.1 hgH
    have hhH' := List.mem_filter.1 hhH
    exact ⟨g, (mem_elemsT QP QP_ok g).1 hgH'.1, h', (mem_elemsT QP QP_ok h').1 hhH'.1,
      by simpa using hgH'.2, by simpa using hhH'.2, evenOrd_not_odd h2''⟩


theorem a6_fixed_odd {K : Type} [Group K]
    (e : K ≃* QP.originalSubgroup) (α : MulAut K) (hα : α * α = 1) (hα1 : α ≠ 1)
    (κ : K) (hκ1 : κ ≠ 1) (hκo : Odd (orderOf κ)) (hκα : α κ = κ)
    (N : Subgroup K) (hN : ∀ n ∈ N, Odd (orderOf n))
    (hNn : ∀ g : K, α g = g → ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcomm : ∀ g : K, α g = g → ⁅κ, g⁆ ∈ N) : orderOf κ = 5 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  obtain ⟨hords, hmain⟩ := a6check_sound
  let p : K → Equiv.Perm (Fin 10) := fun g => ((M.e g : M.P) : Equiv.Perm (Fin 10))
  have hp_mul : ∀ g h, p (g * h) = p g * p h := fun g h => by simp [p]
  have hp_inv : ∀ g, p g⁻¹ = (p g)⁻¹ := fun g => by simp [p]
  have hp_inj : Function.Injective p := fun g h hgh => M.e.injective (Subtype.ext hgh)
  have hp_mem : ∀ g, p g ∈ QP.originalSubgroup := fun g =>
    (SetLike.ext_iff.1 hP _).1 (M.e g).2
  have hp_surj : ∀ q ∈ QP.originalSubgroup, ∃ g, p g = q := fun q hq => by
    have hq' : q ∈ M.P := (SetLike.ext_iff.1 hP q).2 hq
    obtain ⟨g, hg⟩ := M.e.surjective ⟨q, hq'⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  have hp_ord : ∀ g, orderOf (p g) = orderOf g := fun g => by
    have h1 : orderOf (p g) = orderOf (M.e g) := Subgroup.orderOf_coe (M.e g)
    rw [h1]
    exact MulEquiv.orderOf_eq M.e g
  set a : Equiv.Perm (Fin 10) := (M.Φ α : Equiv.Perm (Fin 10)) with ha
  have haA : a ∈ QA.originalSubgroup := (SetLike.ext_iff.1 hA _).1 (M.Φ α).2
  have haa : a * a = 1 := by
    rw [ha, ← M.Φ_mul, hα, M.Φ_one]
  have ha1 : a ≠ 1 := fun h1 => hα1 ((M.Φ_eq_one).1 h1)
  have hspec : ∀ g, p (α g) = a * p g * a⁻¹ := fun g => M.spec α g
  have hfix : ∀ g, α g = g ↔ a * p g = p g * a := fun g => by
    constructor
    · intro h1
      have := hspec g
      rw [h1] at this
      calc a * p g = (a * p g * a⁻¹) * a := by group
        _ = p g * a := by rw [← this]
    · intro h1
      apply hp_inj
      rw [hspec g, h1]
      group
  have hκ'ord : orderOf (p κ) = orderOf κ := hp_ord κ
  have h35 : orderOf κ = 3 ∨ orderOf κ = 5 := by
    have h1 := hords (p κ) (hp_mem κ)
    rw [hκ'ord] at h1
    rcases h1 with h | h | h | h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hκ1
    · exact absurd (h ▸ hκo) (by decide)
    · exact Or.inl h
    · exact absurd (h ▸ hκo) (by decide)
    · exact Or.inr h
  rcases h35 with h3 | h5
  · exfalso
    obtain ⟨g', hg', h', hh', hcg, hch, hev⟩ := hmain a haA haa ha1 (p κ) (hp_mem κ)
      ((hfix κ).1 hκα) (by rw [hκ'ord]; exact h3)
    obtain ⟨g, rfl⟩ := hp_surj g' hg'
    obtain ⟨h, rfl⟩ := hp_surj h' hh'
    have hgα : α g = g := (hfix g).2 hcg
    have hhα : α h = h := (hfix h).2 hch
    have h1 := hcomm g hgα
    have h2 := hNn h hhα _ h1
    have h3' := N.mul_mem h1 h2
    have h4 := hN _ h3'
    have h5 : orderOf (p (⁅κ, g⁆ * (h * ⁅κ, g⁆ * h⁻¹))) = orderOf (⁅κ, g⁆ * (h * ⁅κ, g⁆ * h⁻¹)) := hp_ord _
    apply hev
    rw [commutatorElement_def] at h5
    simp only [hp_mul, hp_inv] at h5
    rw [h5]
    rwa [commutatorElement_def] at h4
  · exact h5

end CFSG.GH74.GLS.C3.Layer1.EndN.A6
