module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.PGroup
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


variable (K : Type) [Field K]

theorem transport_theta {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ S1set) :
    ∃ n ∈ X1 K, conjSub n (Uθ Tag.E8 K) = rootSubgroup Tag.E8 K α := by
  obtain ⟨n, hn, h, -⟩ := transport_pair K hα
  exact ⟨n, hn, h⟩

theorem commute_Uθ_rootSubgroup {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β)
    (hd : β 7 = 0 ∨ β 7 = 1) (s t : K) :
    Commute (pinnedX Tag.E8 K theta s) (pinnedX Tag.E8 K β t) := by
  obtain ⟨hne, hne'⟩ := theta_ne_of_deg β (mem_rootFinset.2 hβ) hd
  refine Heis.commute_pinnedX_of_commPairs_nil Tag.E8 K isRoot_theta hβ hne hne' ?_ s t
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  exact commCandidates_theta_data β (mem_rootFinset.2 hβ) hd p hp.1 (mem_rootFinset.2 hp.2)

theorem commute_Uθ_conjSub {p : ModGL Tag.E8 K} (hp : p ∈ Pθ Tag.E8 K)
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (hd : β 7 = 0 ∨ β 7 = 1) :
    ∀ x ∈ Uθ Tag.E8 K, ∀ y ∈ conjSub p (rootSubgroup Tag.E8 K β), x * y = y * x := by
  intro x hx y hy
  have hpn := Pθ_le_normalizer_Uθ Tag.E8 K (inv_mem hp)
  have hx' : p⁻¹ * x * p ∈ Uθ Tag.E8 K := by
    have := (Subgroup.mem_normalizer_iff.1 hpn x).1 hx
    simpa using this
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hx'
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hy)
  have hc := (commute_Uθ_rootSubgroup K hβ hd s t).eq
  have hs' : pinnedX Tag.E8 K theta s = p⁻¹ * x * p := hs
  rw [hs', ht] at hc
  calc x * y = p * ((p⁻¹ * x * p) * (p⁻¹ * y * p)) * p⁻¹ := by group
    _ = p * ((p⁻¹ * y * p) * (p⁻¹ * x * p)) * p⁻¹ := by rw [hc]
    _ = y * x := by group

theorem lemma1 [Finite K] {H : Subgroup (ModGL Tag.E8 K)} (hH : H ≤ adjointGroup Tag.E8 K)
    (hX : XS K ≤ H) (hN : ¬ H ≤ Subgroup.normalizer (XS K : Set (ModGL Tag.E8 K))) :
    ∃ g ∈ H, ∃ p ∈ Pθ Tag.E8 K, ∃ β, IsRoot Tag.E8 β ∧ (∃ w : WeylGroup Tag.E8, β = w • theta) ∧
      (β 7 = 1 ∨ β 7 = -1 ∨ β 7 = -2) ∧
      conjSub g (Uθ Tag.E8 K) = conjSub p (rootSubgroup Tag.E8 K β) ∧
      ¬ conjSub g (Uθ Tag.E8 K) ≤ XS K := by
  classical
  obtain ⟨h, hh, α, hα, hnot⟩ := exists_conj_not_le K hH hX hN
  obtain ⟨n, hn, hnα⟩ := transport_theta K hα
  have hnXS : n ∈ XS K := X1_le_XS K hn
  have hnH : n ∈ H := hX hnXS
  set g₀ : ModGL Tag.E8 K := h * n with hg₀
  have hg₀H : g₀ ∈ H := mul_mem hh hnH
  have hB : conjSub g₀ (Uθ Tag.E8 K) = conjSub h (rootSubgroup Tag.E8 K α) := by
    rw [hg₀, conjSub_mul, hnα]
  have hBnot : ¬ conjSub g₀ (Uθ Tag.E8 K) ≤ XS K := by
    rw [hB]
    exact hnot
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ α' ∈ S1set, ∀ x ∈ rootSubgroup Tag.E8 K α',
      ∀ b ∈ conjSub g₀ (Uθ Tag.E8 K), b * x = x * b := by
    intro α' hα' x hx b hb
    obtain ⟨n', hn', hn'α⟩ := transport_theta K hα'
    have hn'XS : n' ∈ XS K := X1_le_XS K hn'
    have hn'H : n' ∈ H := hX hn'XS
    set g' : ModGL Tag.E8 K := n'⁻¹ * g₀ with hg'
    have hg'H : g' ∈ H := mul_mem (inv_mem hn'H) hg₀H
    have hback : conjSub g₀ (Uθ Tag.E8 K) = conjSub n' (conjSub g' (Uθ Tag.E8 K)) := by
      rw [← conjSub_mul, hg', mul_inv_cancel_left]
    have hnotg' : ¬ conjSub g' (Uθ Tag.E8 K) ≤ XS K := by
      intro hle
      apply hBnot
      rw [hback]
      exact (conjSub_mono n' hle).trans (conjSub_le_of_mem hn'XS)
    obtain ⟨p, hp, β, hβ, hβl, hnf⟩ := Heis.exists_normalForm Tag.E8 K (hH hg'H)
    have hbd := deg_bounds β (mem_rootFinset.2 hβ)
    by_cases h1 : β 7 = 1 ∨ β 7 = -1 ∨ β 7 = -2
    · exact absurd (hcon g' hg'H p hp β hβ hβl h1 hnf) hnotg'
    · have h02 : β 7 = 0 ∨ β 7 = 2 := by omega
      rcases h02 with h0 | h2
      · have hc := commute_Uθ_conjSub K hp hβ (Or.inl h0)
        have hx' : n'⁻¹ * x * n' ∈ Uθ Tag.E8 K := by
          have : x ∈ conjSub n' (Uθ Tag.E8 K) := by rw [hn'α]; exact hx
          exact mem_conjSub_iff.1 this
        have hb' : n'⁻¹ * b * n' ∈ conjSub g' (Uθ Tag.E8 K) := by
          rw [mem_conjSub_iff]
          have h3 := mem_conjSub_iff.1 hb
          have e : g'⁻¹ * (n'⁻¹ * b * n') * g' = g₀⁻¹ * b * g₀ := by rw [hg']; group
          rw [e]
          exact h3
        have h4 := hc _ hx' _ (by rw [← hnf]; exact hb')
        calc b * x = n' * ((n'⁻¹ * b * n') * (n'⁻¹ * x * n')) * n'⁻¹ := by group
          _ = n' * ((n'⁻¹ * x * n') * (n'⁻¹ * b * n')) * n'⁻¹ := by rw [h4]
          _ = x * b := by group
      · have hβθ : β = theta := deg_eq_two β (mem_rootFinset.2 hβ) h2
        exfalso
        apply hBnot
        have h5 : conjSub g' (Uθ Tag.E8 K) = Uθ Tag.E8 K := by
          rw [hnf, hβθ]
          exact conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ Tag.E8 K hp)
        rw [hback, h5, hn'α]
        exact (rootSubgroup_le_rootSpan_of_mem hα').trans (X1_le_XS K)
  have hcommX1 : ∀ b ∈ conjSub g₀ (Uθ Tag.E8 K), ∀ x ∈ X1 K, b * x = x * b := by
    intro b hb x hx
    have hle : X1 K ≤ Subgroup.centralizer ({b} : Set (ModGL Tag.E8 K)) := by
      refine iSup₂_le fun α' hα' y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm α' hα' y hy b hb).symm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
    exact this.symm
  exact hBnot ((conjSub_Uθ_le_X2 K (hH hg₀H) hcommX1).trans (X2_le_XS K))

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
