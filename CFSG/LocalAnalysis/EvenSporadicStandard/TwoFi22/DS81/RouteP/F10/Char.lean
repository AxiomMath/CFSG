module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Kernel

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

namespace ExtData

variable {Q W B : Type*} [Group Q] [CommGroup W] [Group B] {ρ : Q →* MulAut W}
  (X : ExtData ρ B)

theorem π_map_eq_one_of_eq_one [IsSimpleGroup Q] (hnc : ∃ a b : Q, a * b ≠ b * a)
    (γ : B ≃* B) {b : B} (hb : X.π b = 1) : X.π (γ b) = 1 := by
  set N : Subgroup Q := X.π.ker.map (X.π.comp γ.toMonoidHom) with hNdef
  have hN : N.Normal := by
    rw [hNdef]
    exact (inferInstance : (X.π.ker).Normal).map (X.π.comp γ.toMonoidHom)
      (X.π_surjective.comp γ.surjective)
  haveI := hN
  rcases Subgroup.Normal.eq_bot_or_eq_top N with hNbot | hNtop
  ·
    have hmem : X.π (γ b) ∈ N := by
      rw [hNdef]
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    rw [hNbot] at hmem
    simpa using hmem
  ·
    exfalso
    obtain ⟨a, b', hab⟩ := hnc
    have ha : a ∈ N := by rw [hNtop]; exact Subgroup.mem_top a
    have hb' : b' ∈ N := by rw [hNtop]; exact Subgroup.mem_top b'
    rw [hNdef] at ha hb'
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, hyπ⟩ := Subgroup.mem_map.mp hb'
    have hxπ' : X.π (γ x) = a := hxπ
    have hyπ' : X.π (γ y) = b' := hyπ
    have hxy : x * y = y * x := X.ker_comm hx hy
    have hγ : γ x * γ y = γ y * γ x := by
      simpa using congrArg (fun z => γ z) hxy
    have hπ : a * b' = b' * a := by
      have h := congrArg X.π hγ
      rw [map_mul, map_mul, hxπ', hyπ'] at h
      exact h
    exact hab hπ

theorem π_map_eq_one_iff [IsSimpleGroup Q] (hnc : ∃ a b : Q, a * b ≠ b * a) (γ : B ≃* B)
    (b : B) : X.π (γ b) = 1 ↔ X.π b = 1 := by
  refine ⟨fun h => ?_, X.π_map_eq_one_of_eq_one hnc γ⟩
  have := X.π_map_eq_one_of_eq_one hnc γ.symm h
  simpa using this

end ExtData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
