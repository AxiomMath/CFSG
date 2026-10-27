module

public import CFSG.LieType.SpecialLinear.CurtisDatum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
open CFSG.LieType.Steinberg CFSG.LieType.Universal.SpecialLinear
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

noncomputable section

variable {n : ℕ} {F : Type} [Field F] [Fintype F] {p : ℕ} [Fact p.Prime] [CharP F p]
  {k V : Type} [Field k] [CharP k p] [Algebra F k]
  [AddCommGroup V] [Module k V]

theorem eq_one_of_isCoverType_univ
    {ρ : Representation k (SpecialLinearGroup (Fin (n + 1)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (n + 1)) F → k}
    (hρ : IsSimpleRep ρ)
    (ht : IsCoverType (rankOne n F p) ρ y χ Finset.univ) :
    ∀ g, ρ g = 1 := by
  classical
  have hy : y ≠ 0 := ht.2.1
  have hχ_one : χ 1 = 1 := by
    have e := ht.2.2.1 1 (one_mem _)
    rw [map_one, Module.End.one_apply] at e
    exact (smul_left_injective k hy (e.symm.trans (one_smul k y).symm) : χ 1 = 1)
  have hχ_mul : ∀ {h h' : SpecialLinearGroup (Fin (n + 1)) F},
      h ∈ (curtisDatum n F p).H → h' ∈ (curtisDatum n F p).H →
      χ (h * h') = χ h * χ h' := by
    intro h h' hh hh'
    have e := ht.2.2.1 (h * h') (mul_mem hh hh')
    rw [map_mul, Module.End.mul_apply, ht.2.2.1 h' hh', map_smul, ht.2.2.1 h hh,
      smul_smul, mul_comm] at e
    exact (smul_left_injective k hy e).symm
  have hgen : ∀ (s : Fin n) (u : Fˣ), χ (hdiag n F s u) = 1 := by
    intro s u
    have := ((ht.2.2.2 s).mp (Finset.mem_univ s)).1 u
    simpa [rankOne] using this
  have htorus : ∀ (s : Fin n) {h : SpecialLinearGroup (Fin (n + 1)) F},
      h ∈ torus n F s → χ h = 1 := by
    intro s h hh
    have hle : torus n F s ≤ (curtisDatum n F p).H := fun x hx =>
      Subgroup.mem_iSup_of_mem s hx
    refine Subgroup.closure_induction (p := fun x _ => χ x = 1) ?_ ?_ ?_ ?_ hh
    · rintro x ⟨u, hx⟩
      have hdiag_coe : (hdiag n F s u : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
          Matrix.diagonal (fun r => if r = s.castSucc then (u : F)
            else if r = s.succ then ((u⁻¹ : Fˣ) : F) else 1) :=
        SpecialLinearGroup.diag2nUnit_coe _ u
      have hfun : (fun r : Fin (n + 1) => if r = s.castSucc then (u : F)
            else if r = s.succ then ((u⁻¹ : Fˣ) : F) else 1) =
          Function.update (Function.update (1 : Fin (n + 1) → F) s.castSucc (u : F))
            s.succ ((u⁻¹ : Fˣ) : F) := by
        funext r
        by_cases h1 : r = s.castSucc
        · subst h1
          simp [(Fin.castSucc_lt_succ (i := s)).ne]
        · by_cases h2 : r = s.succ
          · subst h2
            simp [h1]
          · simp [h1, h2]
      have hx' : x = hdiag n F s u := Subtype.ext (by rw [hx, hdiag_coe, hfun])
      rw [hx']
      exact hgen s u
    · exact hχ_one
    · intro x y hx hy hx1 hy1
      exact hχ_mul (hle hx) (hle hy) ▸ by rw [hx1, hy1, one_mul]
    · intro x hx hx1
      have hxH : x ∈ (curtisDatum n F p).H := hle hx
      have hxx : χ (x * x⁻¹) = χ x * χ x⁻¹ := hχ_mul hxH (inv_mem hxH)
      rw [mul_inv_cancel, hχ_one, hx1, one_mul] at hxx
      exact hxx.symm
  have hH : ∀ h ∈ (curtisDatum n F p).H, χ h = 1 := by
    intro h hh
    have hH' : h ∈ (curtisDatum n F p).H ∧ χ h = 1 := by
      refine Subgroup.iSup_induction (S := fun s => torus n F s)
        (C := fun x => x ∈ (curtisDatum n F p).H ∧ χ x = 1) hh ?_ ?_ ?_
      · intro s x hx
        exact ⟨Subgroup.mem_iSup_of_mem s hx, htorus s hx⟩
      · exact ⟨one_mem _, hχ_one⟩
      · intro x y hx hy
        exact ⟨mul_mem hx.1 hy.1, by rw [hχ_mul hx.1 hy.1, hx.2, hy.2, mul_one]⟩
    exact hH'.2
  let ρ₀ : Representation k (SpecialLinearGroup (Fin (n + 1)) F) k :=
    Representation.trivial k (SpecialLinearGroup (Fin (n + 1)) F) k
  have hρ₀ : IsSimpleRep ρ₀ := by
    refine ⟨inferInstance, ?_⟩
    intro W hW
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).mp hbot
      rw [eq_top_iff]
      intro x _
      have h1 : (1 : k) ∈ W := by
        have := W.smul_mem w⁻¹ hw
        rwa [smul_eq_mul, inv_mul_cancel₀ hw0] at this
      simpa using W.smul_mem x h1
  have hρ₀_ct : IsCoverType (rankOne n F p) ρ₀ (1 : k) χ Finset.univ := by
    refine ⟨?_, one_ne_zero, ?_, ?_⟩
    · intro u _
      rfl
    · intro h hh
      rw [Representation.trivial_apply, hH h hh, one_smul]
    · intro s
      constructor
      · intro _
        constructor
        · intro u
          exact hH _ (Subgroup.mem_iSup_of_mem s (hdiag_mem_torus n F s u))
        · have hP : IsPGroup p ↥((curtisDatum n F p).X s) :=
            isPGroup_rootGroup_charP n F p
              ((RootSystem.ofCartan (isFiniteType_A n) ∅).single_mem s)
          have hne : (curtisDatum n F p).X s ≠ ⊥ := (curtisDatum n F p).X_ne_bot s
          have hnt : Nontrivial ↥((curtisDatum n F p).X s) :=
            (Subgroup.nontrivial_iff_ne_bot _).mpr hne
          have hgt : 1 < Nat.card ↥((curtisDatum n F p).X s) := Finite.one_lt_card
          have hdvd : p ∣ Nat.card ↥((curtisDatum n F p).X s) :=
            (hP.card_eq_or_dvd).resolve_left (by omega)
          have hcard : (Fintype.card ↥((coverId n F p).datum.X s) : k) = 0 := by
            rw [← Nat.card_eq_fintype_card]
            rw [show (coverId n F p).datum.X s = (coverId n F p).lX s from rfl,
              Nat.card_congr ((coverId n F p).lXEquiv s)]
            exact (CharP.cast_eq_zero_iff k p _).mpr hdvd
          rw [CurtisDatum.heckeT_apply]
          simp only [ρ₀, Representation.trivial_apply]
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, hcard, zero_smul]
      · intro _
        exact Finset.mem_univ s
  obtain ⟨β, hβ⟩ := iso_of_isCoverType_sl (m := n) (F := F) (p := p) (k := k)
    hρ hρ₀ ht hρ₀_ct
  intro g
  ext v
  exact β.injective (by simpa [ρ₀, Representation.trivial_apply] using hβ g v)

theorem exists_not_mem_of_isCoverType
    {ρ : Representation k (SpecialLinearGroup (Fin (n + 1)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (n + 1)) F → k} {J : Finset (Fin n)}
    (hρ : IsSimpleRep ρ) (ht : IsCoverType (rankOne n F p) ρ y χ J)
    (hne : ∃ g, ρ g ≠ 1) :
    ∃ s, s ∉ J := by
  by_contra h
  push Not at h
  obtain ⟨g, hg⟩ := hne
  have hJ : J = Finset.univ := Finset.eq_univ_of_forall h
  have ht' : IsCoverType (rankOne n F p) ρ y χ Finset.univ := by rwa [← hJ]
  exact hg (eq_one_of_isCoverType_univ hρ ht' g)

end

end CFSG.LieType.SpecialLinear
