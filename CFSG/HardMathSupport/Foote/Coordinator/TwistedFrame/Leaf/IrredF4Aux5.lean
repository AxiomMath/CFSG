module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.Action
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false

namespace Aux5

theorem mul_swap_aux {G : Type*} [Group G] {x y z w : G} (h : z * y = y * z) :
    x * z * (y * w) = x * y * (z * w) := by
  calc x * z * (y * w) = x * (z * y) * w := by simp only [mul_assoc]
    _ = x * (y * z) * w := by rw [h]
    _ = x * y * (z * w) := by simp only [mul_assoc]

theorem commute_aux {G : Type*} [Group G] {q A B Z T T' : G}
    (hA : A * q = q * T * A) (hB : B * q = q * T' * B) (hZ : Z * q = q * Z)
    (hT' : T' * A = A * T') (h : Z * A * B * q = q * (Z * A * B)) : T * T' = 1 := by
  have h1 : Z * A * B * q = q * (Z * T * T') * (A * B) := by
    calc Z * A * B * q = Z * A * (B * q) := by simp only [mul_assoc]
      _ = Z * A * (q * T' * B) := by rw [hB]
      _ = Z * (A * q) * T' * B := by simp only [mul_assoc]
      _ = Z * (q * T * A) * T' * B := by rw [hA]
      _ = (Z * q) * T * (A * T') * B := by simp only [mul_assoc]
      _ = (q * Z) * T * (T' * A) * B := by rw [hZ, hT']
      _ = q * (Z * T * T') * (A * B) := by simp only [mul_assoc]
  have h2 : q * (Z * T * T') * (A * B) = q * Z * (A * B) := by
    rw [← h1, h]
    simp only [mul_assoc]
  have h3 : Z * T * T' = Z := mul_left_cancel (mul_right_cancel h2)
  have h4 : Z * (T * T') = Z * 1 := by
    rw [mul_one, ← mul_assoc]
    exact h3
  exact mul_left_cancel h4

theorem intCast_ne_zero_of_abs_eq_one {L : Type*} [Field L] {N : ℤ} (h : |N| = 1) :
    (N : L) ≠ 0 := by
  rcases (abs_eq zero_le_one).1 h with rfl | rfl <;> simp

end Aux5


namespace Aux5

theorem alpha1_isRoot : IsRoot Tag.F4 alpha1 := mem_rootFinset.1 (by decide +kernel)

theorem root1342_isRoot : IsRoot Tag.F4 root1342 := mem_rootFinset.1 (by decide +kernel)

theorem commPairs_eq_single_of_unique {α β : Fin Tag.F4.rank → ℤ}
    (h : ∀ p ∈ commCandidates, p.1 • α + p.2 • β ∈ rootFinset .F4 ↔ p = (1, 1)) :
    commPairs .F4 α β = [(1, 1)] := by
  classical
  have hc : ∀ p ∈ commCandidates, decide (IsRoot Tag.F4 (p.1 • α + p.2 • β)) =
      decide (p = (1, 1)) := fun p hp => by
    rw [decide_eq_decide, ← mem_rootFinset (τ := Tag.F4)]
    exact h p hp
  unfold commPairs
  rw [List.filter_congr hc]
  decide

theorem comm_of_commPairs_exact {γ μ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ)
    (hμ : IsRoot Tag.F4 μ) (hne : γ ≠ μ) (hne' : γ ≠ -μ) (hcp : commPairs .F4 γ μ = [(1, 1)])
    (hsub : ¬ IsRoot Tag.F4 (μ - γ)) :
    ∃ N : ℤ, |N| = 1 ∧ ∀ (R : Type) [CommRing R] (a b : R),
      pinnedX Tag.F4 R γ a * pinnedX Tag.F4 R μ b * pinnedX Tag.F4 R γ (-a) *
        pinnedX Tag.F4 R μ (-b) = pinnedX Tag.F4 R (γ + μ) ((N : R) * a * b) := by
  obtain ⟨hC, hF⟩ := ActionAux.f4CommConst_spec hγ hμ hne hne'
  refine ⟨ActionAux.f4CommConst γ μ (1, 1), ?_, fun R _ a b => ?_⟩
  · have h := hC (1, 1) (by rw [hcp]; exact List.mem_singleton_self _)
    simpa [hsub] using h
  · have h := hF R a b
    rw [hcp] at h
    simpa [one_smul, pow_one] using h

theorem pair_comm_fwd : ∃ N : ℤ, |N| = 1 ∧ ∀ (R : Type) [CommRing R] (a b : R),
    pinnedX Tag.F4 R alpha1 a * pinnedX Tag.F4 R root1342 b * pinnedX Tag.F4 R alpha1 (-a) *
      pinnedX Tag.F4 R root1342 (-b) = pinnedX Tag.F4 R (highRoot Tag.F4) ((N : R) * a * b) := by
  obtain ⟨N, hN1, hN⟩ := comm_of_commPairs_exact alpha1_isRoot root1342_isRoot
    (by decide +kernel) (by decide +kernel) (commPairs_eq_single_of_unique (by decide +kernel))
    (fun h => absurd (mem_rootFinset.2 h) (by decide +kernel))
  have e : (alpha1 + root1342 : Fin Tag.F4.rank → ℤ) = highRoot Tag.F4 := by decide +kernel
  refine ⟨N, hN1, fun R _ a b => ?_⟩
  rw [← e]
  exact hN R a b

theorem pair_comm_bwd : ∃ N : ℤ, |N| = 1 ∧ ∀ (R : Type) [CommRing R] (a b : R),
    pinnedX Tag.F4 R root1342 a * pinnedX Tag.F4 R alpha1 b * pinnedX Tag.F4 R root1342 (-a) *
      pinnedX Tag.F4 R alpha1 (-b) = pinnedX Tag.F4 R (highRoot Tag.F4) ((N : R) * a * b) := by
  obtain ⟨N, hN1, hN⟩ := comm_of_commPairs_exact root1342_isRoot alpha1_isRoot
    (by decide +kernel) (by decide +kernel) (commPairs_eq_single_of_unique (by decide +kernel))
    (fun h => absurd (mem_rootFinset.2 h) (by decide +kernel))
  have e : (root1342 + alpha1 : Fin Tag.F4.rank → ℤ) = highRoot Tag.F4 := by decide +kernel
  refine ⟨N, hN1, fun R _ a b => ?_⟩
  rw [← e]
  exact hN R a b

theorem alpha1_mem_Deg1 : alpha1 ∈ Deg1 Tag.F4 := ⟨alpha1_isRoot, by decide +kernel⟩

theorem root1342_mem_Deg1 : root1342 ∈ Deg1 Tag.F4 := ⟨root1342_isRoot, by decide +kernel⟩

theorem disj_fwd : ∀ μ ∈ Deg1 Tag.F4, μ ≠ root1342 → alpha1 + μ ∉ rootFinset Tag.F4 := by
  intro μ hμ hne
  have h : ∀ ν ∈ rootFinset Tag.F4, ν 0 = 1 → ν ≠ root1342 → alpha1 + ν ∉ rootFinset Tag.F4 := by
    decide +kernel
  exact h μ (mem_rootFinset.2 hμ.1) hμ.2 hne

theorem disj_bwd : ∀ μ ∈ Deg1 Tag.F4, μ ≠ alpha1 → root1342 + μ ∉ rootFinset Tag.F4 := by
  intro μ hμ hne
  have h : ∀ ν ∈ rootFinset Tag.F4, ν 0 = 1 → ν ≠ alpha1 → root1342 + ν ∉ rootFinset Tag.F4 := by
    decide +kernel
  exact h μ (mem_rootFinset.2 hμ.1) hμ.2 hne

section Conj

variable {τ : Tag} {K : Type} [Field K]

theorem Xθ_mem (s : K) : pinnedX τ K (highRoot τ) s ∈ Qθ τ K :=
  Uθ_le_Qθ (mem_rootSubgroup.2 ⟨s, rfl⟩)

theorem Xθ_comm {q : ModGL τ K} (hq : q ∈ Qθ τ K) (s : K) :
    pinnedX τ K (highRoot τ) s * q = q * pinnedX τ K (highRoot τ) s :=
  CoordAux.Uθ_comm (mem_rootSubgroup.2 ⟨s, rfl⟩) (parabolicRadical_le_posUnipotent (Jθ τ) hq)

theorem Qθ_ind {P : ModGL τ K → Prop}
    (hone : P 1) (hmul : ∀ x y, x ∈ Qθ τ K → y ∈ Qθ τ K → P x → P y → P (x * y))
    (hinv : ∀ x, x ∈ Qθ τ K → P x → P x⁻¹)
    (h₁ : ∀ β ∈ Deg1 τ, ∀ t : K, P (pinnedX τ K β t))
    (h₂ : ∀ t : K, P (pinnedX τ K (highRoot τ) t)) :
    ∀ x ∈ Qθ τ K, P x := by
  let H : Subgroup (ModGL τ K) :=
    { carrier := {x | x ∈ Qθ τ K ∧ P x}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, hmul x y hx.1 hy.1 hx.2 hy.2⟩
      one_mem' := ⟨one_mem _, hone⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, hinv x hx.1 hx.2⟩ }
  have hle : Qθ τ K ≤ H := by
    show rootSpan τ K (parabolicRadicalRoots τ (Jθ τ)) ≤ H
    refine iSup₂_le fun α hα => ?_
    intro g hg
    obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hg
    rcases (CoordAux.mem_radRoots_iff α).1 hα with h | rfl
    · exact ⟨pinnedX_mem_Qθ_of_mem_Deg1 h t, h₁ α h t⟩
    · exact ⟨Xθ_mem t, h₂ t⟩
  exact fun x hx => (hle hx).2

end Conj

section Gen

variable {L : Type} [Field L]

theorem conj_good {γ μ₀ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ Deg1 Tag.F4) (N : L)
    (hcomm : ∀ a t : L, pinnedX Tag.F4 L γ a * pinnedX Tag.F4 L μ₀ t * pinnedX Tag.F4 L γ (-a) *
        pinnedX Tag.F4 L μ₀ (-t) = pinnedX Tag.F4 L (highRoot Tag.F4) (N * a * t))
    (hdisj : ∀ μ ∈ Deg1 Tag.F4, μ ≠ μ₀ → γ + μ ∉ rootFinset Tag.F4) (a : L) :
    ∀ q ∈ Qθ Tag.F4 L, pinnedX Tag.F4 L γ a * q * (pinnedX Tag.F4 L γ a)⁻¹ =
      q * pinnedX Tag.F4 L (highRoot Tag.F4) (N * a * heisCoord Tag.F4 L q μ₀) := by
  have hs := heisCoord_spec Tag.F4 L
  have hAQ : pinnedX Tag.F4 L γ a ∈ Qθ Tag.F4 L := pinnedX_mem_Qθ_of_mem_Deg1 hγ a
  refine Qθ_ind (P := fun q => pinnedX Tag.F4 L γ a * q * (pinnedX Tag.F4 L γ a)⁻¹ =
    q * pinnedX Tag.F4 L (highRoot Tag.F4) (N * a * heisCoord Tag.F4 L q μ₀)) ?_ ?_ ?_ ?_ ?_
  · rw [mul_one, mul_inv_cancel, heisCoord_one, Pi.zero_apply, mul_zero, pinnedX_zero, one_mul]
  · intro x y hx hy hPx hPy
    have e : pinnedX Tag.F4 L γ a * (x * y) * (pinnedX Tag.F4 L γ a)⁻¹ =
        (pinnedX Tag.F4 L γ a * x * (pinnedX Tag.F4 L γ a)⁻¹) *
          (pinnedX Tag.F4 L γ a * y * (pinnedX Tag.F4 L γ a)⁻¹) := by group
    have hcoord : N * a * heisCoord Tag.F4 L (x * y) μ₀ =
        N * a * heisCoord Tag.F4 L x μ₀ + N * a * heisCoord Tag.F4 L y μ₀ := by
      rw [hs.mul x hx y hy, Pi.add_apply, mul_add]
    rw [e, hPx, hPy, hcoord, pinnedX_add]
    exact mul_swap_aux (Xθ_comm hy _)
  · intro x hx hPx
    have e : pinnedX Tag.F4 L γ a * x⁻¹ * (pinnedX Tag.F4 L γ a)⁻¹ =
        (pinnedX Tag.F4 L γ a * x * (pinnedX Tag.F4 L γ a)⁻¹)⁻¹ := by group
    have hcoord : heisCoord Tag.F4 L x⁻¹ μ₀ = -heisCoord Tag.F4 L x μ₀ := by
      rw [heisCoord_inv hx, Pi.neg_apply]
    rw [e, hPx, mul_inv_rev, pinnedX_neg, hcoord, mul_neg]
    exact Xθ_comm (inv_mem hx) _
  · intro μ hμ t
    by_cases hμe : μ = μ₀
    · rw [hμe] at hμ ⊢
      have hcoord : heisCoord Tag.F4 L (pinnedX Tag.F4 L μ₀ t) μ₀ = t := by
        rw [hs.pinnedX_deg1 μ₀ hμ t, Pi.single_eq_same]
      have h := hcomm a t
      rw [← pinnedX_neg Tag.F4 L γ a, ← pinnedX_neg Tag.F4 L μ₀ t] at h
      rw [hcoord, mul_inv_eq_iff_eq_mul.1 h]
      exact Xθ_comm (pinnedX_mem_Qθ_of_mem_Deg1 hμ t) _
    · have hc := (CoordAux.commute_pinnedX_of_not_isRoot_add hγ hμ (hdisj μ hμ hμe) a t).eq
      have hcoord : heisCoord Tag.F4 L (pinnedX Tag.F4 L μ t) μ₀ = 0 := by
        rw [hs.pinnedX_deg1 μ hμ t, Pi.single_eq_of_ne (Ne.symm hμe)]
      rw [hcoord, mul_zero, pinnedX_zero, mul_one, hc, mul_assoc, mul_inv_cancel, mul_one]
  · intro t
    have hcoord : heisCoord Tag.F4 L (pinnedX Tag.F4 L (highRoot Tag.F4) t) μ₀ = 0 := by
      rw [hs.pinnedX_highRoot t, Pi.zero_apply]
    have hc := Xθ_comm hAQ t
    rw [hcoord, mul_zero, pinnedX_zero, mul_one, ← hc, mul_assoc, mul_inv_cancel, mul_one]

end Gen

end Aux5

open Aux5

theorem coord_zero_of_commutes {L : Type} [Field L] {q : ModGL Tag.F4 L} (hq : q ∈ Qθ Tag.F4 L)
    {a₁ b₁ c₁ a₂ b₂ c₂ : L} (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (h₁ : pinnedX Tag.F4 L (highRoot Tag.F4) c₁ * pinnedX Tag.F4 L alpha1 a₁ *
        pinnedX Tag.F4 L root1342 b₁ * q =
      q * (pinnedX Tag.F4 L (highRoot Tag.F4) c₁ * pinnedX Tag.F4 L alpha1 a₁ *
        pinnedX Tag.F4 L root1342 b₁))
    (h₂ : pinnedX Tag.F4 L (highRoot Tag.F4) c₂ * pinnedX Tag.F4 L alpha1 a₂ *
        pinnedX Tag.F4 L root1342 b₂ * q =
      q * (pinnedX Tag.F4 L (highRoot Tag.F4) c₂ * pinnedX Tag.F4 L alpha1 a₂ *
        pinnedX Tag.F4 L root1342 b₂)) :
    heisCoord Tag.F4 L q alpha1 = 0 ∧ heisCoord Tag.F4 L q root1342 = 0 := by
  obtain ⟨N, hN1, hN⟩ := pair_comm_fwd
  obtain ⟨N', hN1', hN'⟩ := pair_comm_bwd
  have hN0 : (N : L) ≠ 0 := intCast_ne_zero_of_abs_eq_one hN1
  have hN0' : (N' : L) ≠ 0 := intCast_ne_zero_of_abs_eq_one hN1'
  have hB1 := conj_good alpha1_mem_Deg1 (N : L) (fun a t => hN L a t) disj_fwd
  have hB2 := conj_good root1342_mem_Deg1 (N' : L) (fun a t => hN' L a t) disj_bwd
  have key : ∀ a b c : L,
      pinnedX Tag.F4 L (highRoot Tag.F4) c * pinnedX Tag.F4 L alpha1 a *
          pinnedX Tag.F4 L root1342 b * q =
        q * (pinnedX Tag.F4 L (highRoot Tag.F4) c * pinnedX Tag.F4 L alpha1 a *
          pinnedX Tag.F4 L root1342 b) →
      (N' : L) * b * heisCoord Tag.F4 L q alpha1 + (N : L) * a * heisCoord Tag.F4 L q root1342 =
        0 := by
    intro a b c h
    have hAQ : pinnedX Tag.F4 L alpha1 a ∈ Qθ Tag.F4 L :=
      pinnedX_mem_Qθ_of_mem_Deg1 alpha1_mem_Deg1 a
    have hA := mul_inv_eq_iff_eq_mul.1 (hB1 a q hq)
    have hB := mul_inv_eq_iff_eq_mul.1 (hB2 b q hq)
    have hT := commute_aux hA hB (Xθ_comm hq c) (Xθ_comm hAQ _) h
    have h0 : pinnedX Tag.F4 L (highRoot Tag.F4)
        ((N : L) * a * heisCoord Tag.F4 L q root1342 +
          (N' : L) * b * heisCoord Tag.F4 L q alpha1) =
        pinnedX Tag.F4 L (highRoot Tag.F4) 0 := by
      rw [pinnedX_add, pinnedX_zero]
      exact hT
    have h1 := pinnedX_injective Tag.F4 L (highRoot Tag.F4) h0
    linear_combination h1
  have e1 := key a₁ b₁ c₁ h₁
  have e2 := key a₂ b₂ c₂ h₂
  have hv : (N : L) * (a₁ * b₂ - a₂ * b₁) * heisCoord Tag.F4 L q root1342 = 0 := by
    linear_combination b₂ * e1 - b₁ * e2
  have hu : (N' : L) * (a₁ * b₂ - a₂ * b₁) * heisCoord Tag.F4 L q alpha1 = 0 := by
    linear_combination a₁ * e2 - a₂ * e1
  exact ⟨(mul_eq_zero.1 hu).resolve_left (mul_ne_zero hN0' hdet),
    (mul_eq_zero.1 hv).resolve_left (mul_ne_zero hN0 hdet)⟩

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux
