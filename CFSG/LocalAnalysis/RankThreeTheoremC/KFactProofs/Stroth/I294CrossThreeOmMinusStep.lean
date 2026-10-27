module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmMinusRot
public import CFSG.LieType.SeitzGeneration.OrthNonsplitDims

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_mem_map_ne_zero {S : Submodule K V} (hS : PolarNondegOn Q S) {m : V} (hm : m ∈ S)
    (hm0 : m ≠ 0) : ∃ n ∈ S, Q n ≠ 0 := by
  obtain ⟨y, hyS, hy⟩ := hS.exists_polar_ne_zero hm hm0
  by_cases h : Q m = 0
  · by_cases h' : Q y = 0
    · refine ⟨m + y, S.add_mem hm hyS, fun h'' => hy ?_⟩
      have := QuadraticMap.map_add Q m y
      rw [h'', h, h'] at this
      simpa using this.symm
    · exact ⟨y, hyS, h'⟩
  · exact ⟨m, hm, h⟩

theorem exists_rotPair_of_polarNondegOn [Finite K] [FiniteDimensional K V] {S : Submodule K V}
    (hS : PolarNondegOn Q S) (hdim : 3 ≤ Module.finrank K S) :
    ∃ (c : K) (u v : V), IsRotPair Q c u v ∧ u ∈ S ∧ v ∈ S := by
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_in hS hdim
  have hS' : PolarNondegOn Q (S ⊓ P.perp) := hS.inf_perp P hPe hPf
  have hfin := finrank_inf_perp_add_two P hPe hPf
  have hne : S ⊓ P.perp ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨n, hn, hnQ⟩ := exists_mem_map_ne_zero hS' hm hm0
  obtain ⟨hnS, hnP⟩ := Submodule.mem_inf.1 hn
  obtain ⟨hen, hfn⟩ := HypPair.mem_perp.1 hnP
  have hnf : polar Q n P.f = 0 := by rw [polar_comm]; exact hfn
  refine ⟨Q n, P.e + Q n • P.f, n - Q n • P.f, ⟨hnQ, ?_, ?_, ?_⟩,
    S.add_mem hPe (S.smul_mem _ hPf), S.sub_mem hnS (S.smul_mem _ hPf)⟩
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, P.Q_e, P.Q_f,
      P.polar_ef]
    simp
  · rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, QuadraticMap.map_smul,
      polar_neg_right, polar_smul_right, hnf, P.Q_f]
    simp
  · rw [polar_add_left, polar_sub_right, polar_sub_right, polar_smul_left, polar_smul_left,
      polar_smul_right, polar_smul_right, hen, hfn, P.polar_ef, P.polar_ff]
    simp

theorem polar_apply_apply_of_pow_three {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : ∀ y, g (g (g y)) = y) (w y : V) :
    polar Q w (g (g y)) = polar Q (g w) y := by
  have h1 := polar_map_of_mem hg (g (g w)) (g y)
  have h2 := polar_map_of_mem hg (g w) y
  rw [hg3] at h1
  rw [h1, h2]

theorem polar_apply_of_pow_three {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : ∀ y, g (g (g y)) = y) (w y : V) :
    polar Q w (g y) = polar Q (g (g w)) y := by
  have h1 := polar_map_of_mem hg (g (g w)) y
  rwa [hg3] at h1

theorem exists_rotPair_of_moved {g : V ≃ₗ[K] V} (h3 : (3 : K) ≠ 0)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : ∀ y, g (g (g y)) = y)
    {S : Submodule K V} (hS : PolarNondegOn Q S) (hSg : ∀ x ∈ S, g x ∈ S) {x : V} (hxS : x ∈ S)
    (hx : g x ≠ x) :
    ∃ (c : K) (u v : V), IsRotPair Q c u v ∧ u ∈ S ∧ v ∈ S ∧ g u = v ∧ g v = -u - v := by
  set P : V → V := fun y => (2 : K) • y - g y - g (g y) with hP
  have hPS : ∀ y ∈ S, P y ∈ S := fun y hy =>
    S.sub_mem (S.sub_mem (S.smul_mem _ hy) (hSg y hy)) (hSg _ (hSg y hy))
  have hPker : ∀ y, P y + g (P y) + g (g (P y)) = 0 := by
    intro y
    simp only [hP, map_sub, map_smul, hg3]
    module
  have hPne : P x ≠ 0 := by
    intro h0
    apply hx
    have h1 : (2 : K) • x - g x - g (g x) = 0 := h0
    have h2 : (2 : K) • g x - g (g x) - x = 0 := by
      have := congrArg g h1
      simpa [map_sub, map_smul, hg3] using this
    have h4 : (3 : K) • (g x - x) = 0 := by
      have e : (3 : K) • (g x - x) =
          -(((2 : K) • x - g x - g (g x)) - ((2 : K) • g x - g (g x) - x)) := by module
      rw [e, h1, h2]
      simp
    exact sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_left h3)
  have key : ∃ w ∈ S, w + g w + g (g w) = 0 ∧ Q w ≠ 0 := by
    have hwS : P x ∈ S := hPS x hxS
    by_cases hQw : Q (P x) = 0
    · obtain ⟨y, hyS, hy⟩ := hS.exists_polar_ne_zero hwS hPne
      have hy'S : P y ∈ S := hPS y hyS
      have hpol : polar Q (P x) (P y) = 3 * polar Q (P x) y := by
        have hsum : g (P x) + g (g (P x)) = -P x := by
          have := hPker x
          rw [← sub_eq_zero]
          rw [← this]
          module
        have e1 := polar_apply_of_pow_three hg hg3 (P x) y
        have e2 := polar_apply_apply_of_pow_three hg hg3 (P x) y
        have e : polar Q (P x) (P y) =
            2 * polar Q (P x) y - polar Q (g (g (P x))) y - polar Q (g (P x)) y := by
          rw [show P y = (2 : K) • y - g y - g (g y) from rfl]
          simp only [polar_sub_right, polar_smul_right, e1, e2, smul_eq_mul]
        have e3 : (3 : K) • P x = (2 : K) • P x - g (g (P x)) - g (P x) := by
          rw [← sub_eq_zero]
          have := hsum
          rw [← sub_eq_zero] at this
          rw [← this]
          module
        have e4 := congrArg (fun z => polar Q z y) e3
        simp only [polar_smul_left, polar_sub_left, smul_eq_mul] at e4
        rw [e, ← e4]
      have hpol' : polar Q (P x) (P y) ≠ 0 := by
        rw [hpol]
        exact mul_ne_zero h3 hy
      by_cases hQy : Q (P y) = 0
      · refine ⟨P x + P y, S.add_mem hwS hy'S, ?_, fun h0 => hpol' ?_⟩
        · have h1 := hPker x
          have h2 := hPker y
          calc P x + P y + g (P x + P y) + g (g (P x + P y)) =
              (P x + g (P x) + g (g (P x))) + (P y + g (P y) + g (g (P y))) := by
                simp only [map_add]
                abel
            _ = 0 := by rw [h1, h2, add_zero]
        · have := QuadraticMap.map_add Q (P x) (P y)
          rw [h0, hQw, hQy] at this
          simpa using this.symm
      · exact ⟨P y, hy'S, hPker y, hQy⟩
    · exact ⟨P x, hwS, hPker x, hQw⟩
  obtain ⟨w, hwS, hker, hwQ⟩ := key
  have hgg : g (g w) = -w - g w := by
    have e : g (g w) - (-w - g w) = w + g w + g (g w) := by module
    exact sub_eq_zero.1 (e.trans hker)
  have hQg : Q (g w) = Q w := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg w
  have hQgg : Q (g (g w)) = Q w :=
    (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg (g w)).trans hQg
  have hp1 : polar Q w (g (g w)) = polar Q w (g w) := by
    rw [polar_apply_apply_of_pow_three hg hg3, polar_comm]
  have hp2 : polar Q (g w) (g (g w)) = polar Q w (g w) := polar_map_of_mem hg w (g w)
  have hzero : Q (w + g w + g (g w)) = 0 := by rw [hker, QuadraticMap.map_zero]
  rw [QuadraticMap.map_add Q (w + g w) (g (g w)), QuadraticMap.map_add Q w (g w), polar_add_left,
    hp1, hp2, hQg, hQgg] at hzero
  have hpolar : polar Q w (g w) = -Q w := by
    have e : (3 : K) * (polar Q w (g w) + Q w) = 0 := by linear_combination hzero
    have := (mul_eq_zero.1 e).resolve_left h3
    linear_combination this
  exact ⟨Q w, w, g w, ⟨hwQ, rfl, hQg, hpolar⟩, hwS, hSg w hwS, rfl, hgg⟩

theorem exists_rotPair_in [Finite K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg3 : ∀ y, g (g (g y)) = y) {S : Submodule K V} (hS : PolarNondegOn Q S)
    (hSg : ∀ x ∈ S, g x ∈ S) (hdim : 3 ≤ Module.finrank K S) :
    ∃ (c : K) (u v : V), IsRotPair Q c u v ∧ u ∈ S ∧ v ∈ S ∧ RotMode g u v := by
  by_cases hmove : ∃ x ∈ S, g x ≠ x
  · obtain ⟨x, hxS, hx⟩ := hmove
    obtain ⟨c, u, v, hr, hu, hv, hgu, hgv⟩ := exists_rotPair_of_moved h3 hg hg3 hS hSg hxS hx
    exact ⟨c, u, v, hr, hu, hv, Or.inr ⟨hgu, hgv⟩⟩
  · push Not at hmove
    obtain ⟨c, u, v, hr, hu, hv⟩ := exists_rotPair_of_polarNondegOn hS hdim
    exact ⟨c, u, v, hr, hu, hv, Or.inl ⟨hmove u hu, hmove v hv⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus
