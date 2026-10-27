module

public import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_gamma_two (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hU : rankThreeGamma 2 p (P : Subgroup G) ≤ M)
    {S : Subgroup G} (hSp : IsPGroup p S) (hSM : S ≤ M) (hS2 : 2 ≤ CFSG.Open.pRank p S) :
    normalizer (S : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM S hSp hSM
  have hN : normalizer ((S.map (MulAut.conj (m : G)).toMonoidHom : Subgroup G) : Set G) ≤ M :=
    (gamma_normalizer_le 2 p (P : Subgroup G) _ hm
      (by rwa [pRank_map_automorphism p hprime.one_lt])).trans hU
  intro g hg
  have himage : MulAut.conj (m : G) g ∈ M := by
    apply hN
    rw [← map_equiv_normalizer_eq S (MulAut.conj (m : G))]
    exact mem_map_of_mem _ hg
  have hproduct := M.mul_mem (M.mul_mem (M.inv_mem m.property) himage) m.property
  simpa [MulAut.conj_apply, mul_assoc] using hproduct

theorem mem_of_alperinDecomposition_of_gamma_two (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hU : rankThreeGamma 2 p (P : Subgroup G) ≤ M)
    {A : Subgroup G} {c : G}
    (hdec : CFSG.RankTwoShapes.AlperinDecomposition p (P : Subgroup G) A c) : c ∈ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hPnc : ¬ IsCyclic (P : Subgroup G) := not_isCyclic_of_two_le_pRank hprime (by omega)
  induction hdec with
  | one => exact M.one_mem
  | step _ hQ _ hn ih =>
    have hQp : IsPGroup p _ := P.isPGroup'.to_le hQ.1
    exact M.mul_mem ih (normalizer_le_of_gamma_two hS hp hM hU hQp (hQ.1.trans hPM)
      (two_le_pRank_of_not_isCyclic hprime (sigmaA_odd p hp) hQp
        (not_isCyclic_of_isAlperinSubgroup P.isPGroup' hPnc hQ)) hn)

theorem exists_mem_conj_eq_of_map_le_of_gamma_two (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hU : rankThreeGamma 2 p (P : Subgroup G) ≤ M)
    {A : Subgroup G} (hA : A ≤ P) {g : G} (hg : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ P) :
    ∃ c ∈ M, ∀ a ∈ A, c⁻¹ * a * c = g⁻¹ * a * g := by
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨c, hdec, hc⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion P hA hg
  exact ⟨c, mem_of_alperinDecomposition_of_gamma_two hS hp hM hU hdec, hc⟩

omit [Finite G] in
private theorem commutator_eq_top_focal3 [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with
    h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

theorem sylow_le_commutator_of_gamma_two (hS : Setting G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hU : rankThreeGamma 2 p (P : Subgroup G) ≤ M) : (P : Subgroup G) ≤ ⁅M, M⁆ := by
  have := hS.simple
  have hfoc := Subgroup.commutator_inf_eq_focalSubgroup P
  rw [commutator_eq_top_focal3 hS.nonab, top_inf_eq] at hfoc
  rw [hfoc, Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro _ ⟨hgP, x, hxP, u, rfl⟩
  have hux : u * x * u⁻¹ ∈ (P : Subgroup G) := by
    have h := (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hxP) hgP
    rw [commutatorElement_def] at h
    simpa [mul_assoc] using (P : Subgroup G).inv_mem h
  have hmap : (zpowers x).map (MulAut.conj u⁻¹⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    simpa [MulAut.conj_apply] using hux
  obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le_of_gamma_two hS hp hM hU
    (zpowers_le.mpr hxP) hmap
  have hcx : c⁻¹ * x * c = u * x * u⁻¹ := by
    simpa using hc x (mem_zpowers x)
  have heq : ⁅x, u⁆ = ⁅x, c⁻¹⁆ := by
    rw [commutatorElement_def, commutatorElement_def, inv_inv]
    calc x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
      _ = x * (c⁻¹ * x * c)⁻¹ := by rw [hcx]
      _ = x * c⁻¹ * x⁻¹ * c := by group
  rw [heq]
  exact commutator_mem_commutator
    ((sylow_le_of_isCoreMaxLocal hS hp hM).1 hxP) (M.inv_mem hcM)

end CFSG.LocalAnalysis.RankThreeTheoremC
