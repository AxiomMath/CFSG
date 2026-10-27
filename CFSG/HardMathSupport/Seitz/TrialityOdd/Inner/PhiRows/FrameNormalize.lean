module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.FrameQuat
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.FrameConj

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.Bender.Thm1

section

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ℓ f : ℕ}

theorem frameTorus_rTorsion_le [Fact ℓ.Prime] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (F : D4PhiFrame K σ (ℓ ^ f) (-1)) {r : ℕ} (hr : r.Prime)
    (hr3 : 3 < r) (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hEtor : E ≤ frameTorus F)
    (hEexp : ∀ y ∈ E, y ^ r = 1) (hEcard : Nat.card E = r ^ 2)
    (P : Sylow r (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hEP : E ≤ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hPΩ : ∀ x ∈ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), x ^ r = 1 → x ∈ E)
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hy : y ∈ frameTorus F) (hyr : y ^ r = 1) :
    y ∈ E := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨c, hc⟩ := exists_conj_into_frame_torus hf K hK σ hσ hr hr3 hrd F
    (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) P.isPGroup'
  have hPc : ∀ x ∈ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      c * x * c⁻¹ ∈ frameTorus F := fun x hx => by
    have := hc x hx
    rw [← frameConj_apply] at this
    exact this
  set P'' : Sylow r (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := c • P with hP''
  have hP''mem : ∀ z, z ∈ (P'' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ↔
      ∃ x ∈ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), c * x * c⁻¹ = z := by
    intro z
    rw [hP'', Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact Iff.rfl
  have hP''le : (P'' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤ frameTorus F := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (hP''mem z).1 hz
    exact hPc x hx
  have hrt : ∀ z ∈ frameTorus F, z ^ r = 1 →
      z ∈ (P'' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro z hz hzr
    have hY : IsPGroup r (Subgroup.zpowers z) := by
      have h1 : orderOf z ∣ r := orderOf_dvd_of_pow_eq_one hzr
      rcases (Nat.dvd_prime hr).1 h1 with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
    have hcent : Subgroup.zpowers z ≤ Subgroup.centralizer
        ((P'' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : Set _) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact frameTorus_comm F (hP''le hx) ((Subgroup.zpowers_le.2 hz) hg)
    have hnorm := hcent.trans (Subgroup.centralizer_le_normalizer _)
    have hsup : IsPGroup r ((P'' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ⊔
        Subgroup.zpowers z : Subgroup _) := P''.isPGroup'.to_sup_of_normal_left' hY hnorm
    have heq := P''.is_maximal' hsup le_sup_left
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hcE : ∀ z ∈ frameTorus F, z ^ r = 1 → ∃ x ∈ E, c * x * c⁻¹ = z := by
    intro z hz hzr
    obtain ⟨x, hx, hxz⟩ := (hP''mem z).1 (hrt z hz hzr)
    refine ⟨x, hPΩ x hx ?_, hxz⟩
    have : c * x ^ r * c⁻¹ = 1 := by
      calc c * x ^ r * c⁻¹ = (c * x * c⁻¹) ^ r := (conj_pow).symm
        _ = 1 := by rw [hxz, hzr]
    calc x ^ r = c⁻¹ * (c * x ^ r * c⁻¹) * c := by group
      _ = 1 := by rw [this]; group
  have hle : E ≤ E.map (MulAut.conj c).toMonoidHom := by
    intro e he
    obtain ⟨x, hx, hxe⟩ := hcE e (hEtor he) (hEexp e he)
    exact ⟨x, hx, hxe⟩
  have hEq : E = E.map (MulAut.conj c).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
  rw [hEq]
  obtain ⟨x, hx, hxy⟩ := hcE y hy hyr
  exact ⟨x, hx, hxy⟩

theorem frameNorm_normalizes_plane [Fact ℓ.Prime] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (F : D4PhiFrame K σ (ℓ ^ f) (-1)) {r : ℕ} (hr : r.Prime)
    (hr3 : 3 < r) (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hEtor : E ≤ frameTorus F)
    (hEexp : ∀ y ∈ E, y ^ r = 1) (hEcard : Nat.card E = r ^ 2)
    (P : Sylow r (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hEP : E ≤ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hPΩ : ∀ x ∈ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), x ^ r = 1 → x ∈ E)
    {g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hg : g ∈ frameNorm F) {y : _}
    (hy : y ∈ E) : g * y * g⁻¹ ∈ E := by
  refine frameTorus_rTorsion_le hf hK hσ F hr hr3 hrd hEtor hEexp hEcard P hEP hPΩ
    (conj_mem_frameTorus hσ F hg (hEtor hy)) ?_
  calc (g * y * g⁻¹) ^ r = g * y ^ r * g⁻¹ := conj_pow
    _ = 1 := by rw [hEexp y hy]; group

end

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
