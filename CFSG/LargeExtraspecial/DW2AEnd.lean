module

public import CFSG.LargeExtraspecial.DWSm77Main
public import CFSG.LargeExtraspecial.DW2AFull

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G}

omit [IsSimpleGroup G] in
theorem polar_eq_zero_of_mem_perp {W : Submodule (ZMod 2) S.Qt} {u v : S.Qt} (hu : u ∈ W)
    (hv : v ∈ perp S W) : polar S.q u v = 0 :=
  mem_perp.mp hv u hu

omit [IsSimpleGroup G] in
theorem polar_eq_zero_of_mem_perp' {W : Submodule (ZMod 2) S.Qt} {u v : S.Qt} (hu : u ∈ perp S W)
    (hv : v ∈ W) : polar S.q u v = 0 := by
  rw [polar_comm]
  exact mem_perp.mp hu v hv

theorem false_of_sup_ge_of_nondeg (hn : 2 ≤ S.width) (hP : NondegWeaklyClosed S) {g₀ : G}
    (hg₀Q : g₀ * S.z * g₀⁻¹ ∈ S.QG)
    (hg₀ : g₀ * S.z * g₀⁻¹ ≠ S.z) {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W)
    (hWW : W ≤ perp S W) (hW0 : W ≠ ⊥) (hlt : finrank (ZMod 2) W < S.width)
    {T : Submodule (ZMod 2) S.Qt} (hT : IsMbarInvariant S T) (hTW : T ≤ perp S W)
    (hTW0 : T ⊓ W = ⊥)
    (hdim : finrank (ZMod 2) (perp S W) ≤ finrank (ZMod 2) (T ⊔ W : Submodule (ZMod 2) S.Qt) + 1) :
    False := by
  have hperp := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  rw [S.finrank_Qt_eq_two_mul_width] at hperp
  change finrank (ZMod 2) (perp S W) = _ at hperp
  have hsupT : T ⊔ W ≤ perp S W := sup_le hTW hWW
  have hfT := Submodule.finrank_sup_add_finrank_inf_eq T W
  rw [hTW0, finrank_bot, add_zero] at hfT
  have hW1 : 1 ≤ finrank (ZMod 2) W := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hW0
  have hsupdim := Submodule.finrank_mono hsupT
  rcases Nat.lt_or_ge (finrank (ZMod 2) (T ⊔ W : Submodule (ZMod 2) S.Qt))
    (finrank (ZMod 2) (perp S W)) with hlt' | hge
  ·
    set P := perp S (T ⊔ W) with hP
    have hPdim := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (T ⊔ W)
    rw [S.finrank_Qt_eq_two_mul_width] at hPdim
    change finrank (ZMod 2) P = _ at hPdim
    have hWP : W ≤ P := by
      intro w hw
      rw [hP, mem_perp]
      intro u hu
      obtain ⟨t, ht, w', hw', rfl⟩ := Submodule.mem_sup.mp hu
      rw [polar_add_left, polar_eq_zero_of_mem_perp' (hTW ht) hw,
        polar_eq_zero_of_mem_perp' (hWW hw') hw, add_zero]
    have hPW : P ≤ perp S W := by
      intro p hp
      rw [mem_perp]
      intro w hw
      exact mem_perp.mp hp w (Submodule.mem_sup_right hw)
    obtain ⟨h₀, hh₀P, hh₀W⟩ : ∃ h₀ ∈ P, h₀ ∉ W := by
      by_contra hc
      push Not at hc
      have := Submodule.finrank_mono (show P ≤ W from hc)
      omega
    have hPeq : P = W ⊔ ZMod 2 ∙ h₀ := by
      refine (Submodule.eq_of_le_of_finrank_le (sup_le hWP ?_) ?_).symm
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hh₀P
      · rw [finrank_sup_span_singleton hh₀W]
        omega
    have hPiso : P ≤ perp S P := by
      intro p hp
      rw [mem_perp]
      intro p' hp'
      rw [hPeq] at hp hp'
      obtain ⟨w, hw, f, hf, rfl⟩ := Submodule.mem_sup.mp hp
      obtain ⟨w', hw', f', hf', rfl⟩ := Submodule.mem_sup.mp hp'
      obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hf
      obtain ⟨μ', rfl⟩ := Submodule.mem_span_singleton.mp hf'
      have hh₀perp := hPW hh₀P
      have hw'w : polar S.q w' w = 0 := polar_eq_zero_of_mem_perp hw' (hWW hw)
      have hw'h : polar S.q w' h₀ = 0 := polar_eq_zero_of_mem_perp hw' hh₀perp
      have hhw : polar S.q h₀ w = 0 := polar_eq_zero_of_mem_perp' hh₀perp hw
      have hhh : polar S.q h₀ h₀ = 0 := CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero S.q h₀
      simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hw'w,
        hw'h, hhw, hhh, smul_zero, add_zero]
    have hPsup : P ≤ T ⊔ W := by
      have := hPiso
      rw [hP, perp_perp] at this
      exact this
    obtain ⟨t₀, ht₀T, ht₀P, ht₀0⟩ : ∃ t₀ ∈ T, t₀ ∈ P ∧ t₀ ≠ 0 := by
      obtain ⟨t, ht, w, hw, hh⟩ := Submodule.mem_sup.mp (hPsup hh₀P)
      refine ⟨t, ht, ?_, fun h => hh₀W (by rw [← hh, h, zero_add]; exact hw)⟩
      have : t = h₀ - w := by rw [← hh]; abel
      rw [this]
      exact sub_mem hh₀P (hWP hw)
    have hline : T ⊓ P = ZMod 2 ∙ t₀ := by
      refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact ⟨ht₀T, ht₀P⟩
      · rw [finrank_span_singleton ht₀0]
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq (T ⊓ P) W
        have h2 : (T ⊓ P) ⊓ W = ⊥ := eq_bot_iff.mpr fun v hv =>
          (hTW0 ▸ (⟨hv.1.1, hv.2⟩ : v ∈ T ⊓ W) : v ∈ (⊥ : Submodule (ZMod 2) S.Qt))
        rw [h2, finrank_bot, add_zero] at h1
        have h3 : (T ⊓ P) ⊔ W ≤ P := sup_le inf_le_right hWP
        have h4 := Submodule.finrank_mono h3
        omega
    have hsupinv : IsMbarInvariant S (T ⊔ W) := by
      intro m v hv
      obtain ⟨t, ht, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      exact add_mem (Submodule.mem_sup_left (hT m t ht)) (Submodule.mem_sup_right (hW m w hw))
    have hinv : IsMbarInvariant S (ZMod 2 ∙ t₀) := by
      rw [← hline]
      exact hT.inf hsupinv.perp
    have hfix := apply_eq_of_invariant_span ht₀0 hinv
    exact ht₀0 (eq_zero_of_forall_ρ_apply_eq S (by omega) hfix)
  ·
    have heq : T ⊔ W = perp S W :=
      Submodule.eq_of_le_of_finrank_le hsupT (by omega)
    have hnd : T ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin T = ⊥ := by
      rw [eq_bot_iff]
      rintro t ⟨htT, htT'⟩
      have h1 : t ∈ perp S (T ⊔ W) := by
        rw [mem_perp]
        intro u hu
        obtain ⟨t', ht', w, hw, rfl⟩ := Submodule.mem_sup.mp hu
        rw [polar_add_left, polar_eq_zero_of_mem_perp hw (hTW htT)]
        have := LinearMap.BilinForm.mem_orthogonal_iff.mp htT' t' ht'
        rw [QuadraticMap.polarBilin_apply_apply] at this
        rw [this, add_zero]
      rw [heq, perp_perp] at h1
      have : t ∈ T ⊓ W := ⟨htT, h1⟩
      rwa [hTW0] at this
    have hT0 : T ≠ ⊥ := by
      intro h
      rw [h, bot_sup_eq] at heq
      rw [← heq] at hperp
      omega
    have hTtop : T ≠ ⊤ := by
      intro h
      have := Submodule.finrank_mono hTW
      rw [h, finrank_top, S.finrank_Qt_eq_two_mul_width] at this
      omega
    exact hg₀ (hP T (fun m v hv => hT m v hv) hnd hT0 hTtop g₀ hg₀Q)

end CFSG.LargeExtraspecial.DW
