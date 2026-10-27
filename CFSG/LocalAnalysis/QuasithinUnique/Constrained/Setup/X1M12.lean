module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Out2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12Check

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family CFSG.Certificates CFSG.ComponentClassification.OuterAutomorphisms

abbrev S12 : Type := ↥NativeSporadic.M12

section Facts

theorem m12_card_eq : Nat.card S12 = 2 ^ 6 * 1485 := by
  rw [m12_card]
  norm_num

theorem m12_sylow :
    SylowData S12 6 1485 m12rl := by
  obtain ⟨hlen, hnd, h1, hmul, hpow⟩ := m12_sylow_check
  exact SylowData.of_mul_mem hlen hnd h1 hmul hpow m12_card_eq (by decide)

theorem m12_rank_le
    : ∀ B : Subgroup S12, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 3 :=
  m12_sylow.rank_le 3 m12_rank_check

theorem m12_gen1
    (B : Subgroup S12) (hsq : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥) :
    ∃ cs : List S12, cs.length = 3 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S12)), orderOf x = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hok, hcover⟩ := m12_G1_check
  obtain ⟨h1, h2⟩ := gen1_hyps m12rl m12conj m12G1 (p := 11) hok
    (fun ws => by simp [m12conj]) hcover
  exact m12_sylow.gen1 _ h1 h2 B hsq hne

theorem m12_outer_cover
    : ∀ u : Equiv.Perm (Fin 24), m12Sigma⁻¹ * u ∈ m12D.originalSubgroup →
    orderOf u = 2 → ∃ r ∈ [m12Sigma], ∃ c ∈ m12D.originalSubgroup, u = c * r * c⁻¹ := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, hsz, hord⟩ := m12_sigma_cover
  have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  exact (exists_conj_of_repsOK hn m12D m12D_check.1 (pairTables_spec hn hA hB) m12Sigma
    (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq) (by norm_num) [m12Sigma]
    (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by simp, (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord⟩)
    1000 hok).1

theorem m12D_hrep
    : ∀ u : Equiv.Perm (Fin 24), m12Sigma⁻¹ * u ∈ m12D.originalSubgroup →
    orderOf u = 2 → ∃ g' ∈ m12D.originalSubgroup, orderOf (u * (g' * u * g'⁻¹)) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine hrep_of_cover m12D.originalSubgroup [m12Sigma] m12_outer_cover ?_
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  obtain ⟨h1, h2⟩ := m12_outer_check
  exact ⟨evalCodes [m12A1, m12B1] m12OuterWord, evalCodes_mem _ m12_gens_memD _,
    orderOf_eq_prime h1 h2⟩

theorem m12_outer_dihedral
    : ∀ ψ : MulAut S12,
    ψ ∉ (MulAut.conj : S12 →* MulAut S12).range → ψ * ψ = 1 →
      ∃ α : MulAut S12, orderOf (ψ * (α * ψ * α⁻¹)) = 11 := by
  intro ψ hψ hψ2
  set e := m12EquivD with he
  have hψD : MulAut.congr e ψ ∉ inner m12D.originalSubgroup := by
    rintro ⟨d, hd⟩
    apply hψ
    refine ⟨e.symm d, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, MulEquiv.apply_symm_apply, hd]
  have hψD2 : MulAut.congr e ψ * MulAut.congr e ψ = 1 := by rw [← map_mul, hψ2, map_one]
  obtain ⟨β, hβ⟩ := outer_dihedral_of_delta m12D.originalSubgroup m12Sigma m12D_sigma_normalizes
    m12D_sigma_sq m12D_center m12D_sigma_outer m12D_mulAut_card m12D_hrep _ hψD2 hψD
  refine ⟨(MulAut.congr e).symm β, ?_⟩
  have h1 : MulAut.congr e (ψ * ((MulAut.congr e).symm β * ψ * ((MulAut.congr e).symm β)⁻¹)) =
      MulAut.congr e ψ * (β * MulAut.congr e ψ * β⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [← MulEquiv.orderOf_eq (MulAut.congr e), h1]
  exact hβ

end Facts

theorem m12_weight_lt
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (e : CQ L ≃* NativeSporadic.Carrier .M12)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have e' : CQ L ≃* S12 := e
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hidx := index_fixV_eq_two_pow hW E
  apply weight_lt_of_lt_index
  rcases out2_dichotomy hW hq.1 hirr hE hEel e' m12_center_eq_bot' m12_mulAut_card (r := 3)
    (p := 11) (by norm_num) m12_rank_le m12_outer_dihedral with hEL | ⟨hdisp, hcard⟩
  · have hcard : Nat.card E ≤ 2 ^ 3 := card_le_two_pow_of_le hW hirr hEL hEel e' m12_rank_le
    have hBsq := imgSub_sq (hEL := hEL) (e := e') hEel
    have hBcard := card_imgSub hW hirr hEL hEel e'
    have hne : imgSub L E hEL e' ≠ ⊥ := by
      intro h
      have h1 : Nat.card (imgSub L E hEL e') = 1 := by rw [h]; simp
      rw [hBcard] at h1
      exact hEne (Subgroup.card_eq_one.1 h1)
    obtain ⟨cs, hcs, hx⟩ := m12_gen1 _ hBsq hne
    have h := two_pow_le_of_inner_gen hW hEL e' (k := 3) (p := 11) (by norm_num) ⟨cs, hcs, hx⟩
    rw [orderOf_two_zmod_11] at h
    have h2 := two_pow_le_of_pow_le hidx h (ρ := 4) (by norm_num)
    omega
  · rw [orderOf_two_zmod_11] at hdisp
    have h2 := two_pow_le_of_pow_le hidx hdisp (ρ := 5) (by norm_num)
    omega

theorem sporadicExclusion_M12
    : SporadicExclusion .M12 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  exact m12_weight_lt hW hq hirr e hE hEne hEel

end CFSG.QuasithinUnique.Setup.X1
