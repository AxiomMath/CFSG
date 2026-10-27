module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false

section Three

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem commute_rootSpan_of_single_three (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (zu : ModGL τ L) (hq : S.D.q = 3)
    (hnorm : ∀ g : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ↔
      zu * g * zu⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hmem : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ t : L, t ^ 3 = t →
      zu * pinnedX τ L γ t * zu⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  classical
  have h3 : (3 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  have h22 : (2 : L) * 2 = 1 := by
    have : (2 : L) * 2 = 3 + 1 := by norm_num
    rw [this, h3, zero_add]
  have hgen : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ c : L,
      Commute z (zu * pinnedX τ L γ c * zu⁻¹) := by
    intro γ hγ c
    have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
    obtain ⟨aZ, bZ, aZ', bZ', haZ, haZ', hrkZ, hE1, hE2⟩ :=
      exists_factor_data S hτ (RingHom.id L) zu hγr 0
    have hform : ∀ t : L, ((zu * pinnedX τ L γ t * zu⁻¹ : ModGL τ L) :
        Module.End L (RootModule τ L)) = 1 + t • aZ + t ^ 2 • bZ := by
      intro t
      have := hE1 t
      rw [iterHom_zero, pow_zero, pow_one] at this
      exact this
    have hc1 := congrArg (fun m : ModGL τ L => (m : Module.End L (RootModule τ L)))
      (hcomm _ (hmem γ hγ 1 (by simp))).eq
    have hc2 := congrArg (fun m : ModGL τ L => (m : Module.End L (RootModule τ L)))
      (hcomm _ (hmem γ hγ (-1) (by
        have : (-1 : L) ^ 3 = -1 := by ring
        exact this))).eq
    simp only [Units.val_mul, hform] at hc1 hc2
    set Z := (z : Module.End L (RootModule τ L)) with hZ
    have d1 : Z * aZ - aZ * Z + (Z * bZ - bZ * Z) = 0 := by
      have h := sub_eq_zero.2 hc1
      rw [← h]
      simp only [one_smul, one_pow]
      noncomm_ring
    have d2 : -(Z * aZ - aZ * Z) + (Z * bZ - bZ * Z) = 0 := by
      have h := sub_eq_zero.2 hc2
      rw [← h]
      simp only [neg_smul, one_smul, even_two.neg_pow, one_pow]
      noncomm_ring
    have hu : (2 : L) • (Z * aZ - aZ * Z) = 0 := by
      have e : (Z * aZ - aZ * Z) + (Z * aZ - aZ * Z) =
          (Z * aZ - aZ * Z + (Z * bZ - bZ * Z)) - (-(Z * aZ - aZ * Z) + (Z * bZ - bZ * Z)) := by
        abel
      rw [two_smul, e, d1, d2, sub_zero]
    have hv : (2 : L) • (Z * bZ - bZ * Z) = 0 := by
      have e : (Z * bZ - bZ * Z) + (Z * bZ - bZ * Z) =
          (Z * aZ - aZ * Z + (Z * bZ - bZ * Z)) + (-(Z * aZ - aZ * Z) + (Z * bZ - bZ * Z)) := by
        abel
      rw [two_smul, e, d1, d2, add_zero]
    have hA : Z * aZ = aZ * Z := by
      have : (Z * aZ - aZ * Z) = (2 * 2 : L) • (Z * aZ - aZ * Z) := by rw [h22, one_smul]
      rw [mul_smul, hu, smul_zero] at this
      exact sub_eq_zero.1 this
    have hB : Z * bZ = bZ * Z := by
      have : (Z * bZ - bZ * Z) = (2 * 2 : L) • (Z * bZ - bZ * Z) := by rw [h22, one_smul]
      rw [mul_smul, hv, smul_zero] at this
      exact sub_eq_zero.1 this
    have hA' : ((z : ModGL τ L) : Module.End L (RootModule τ L)) * aZ =
        aZ * ((z : ModGL τ L) : Module.End L (RootModule τ L)) := hA
    have hB' : ((z : ModGL τ L) : Module.End L (RootModule τ L)) * bZ =
        bZ * ((z : ModGL τ L) : Module.End L (RootModule τ L)) := hB
    have hfc := hform c
    generalize zu * pinnedX τ L γ c * zu⁻¹ = W at hfc ⊢
    show z * W = W * z
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hfc]
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hA', hB']
  have hmap : (rootSpan τ L (componentRoots (rootCharHom a) i)).map (MulAut.conj zu).toMonoidHom ≤
      Subgroup.centralizer {z} := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hgen γ hγ c).symm.eq
  intro g hg
  have hg' : zu⁻¹ * g * zu ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    refine (hnorm _).2 ?_
    have : zu * (zu⁻¹ * g * zu) * zu⁻¹ = g := by group
    rw [this]
    exact hg
  have hcalc : (MulAut.conj zu).toMonoidHom (zu⁻¹ * g * zu) = g := by
    show zu * (zu⁻¹ * g * zu) * zu⁻¹ = g
    group
  have hmem' : g ∈ Subgroup.centralizer {z} := hmap (Subgroup.mem_map.2 ⟨_, hg', hcalc⟩)
  exact Commute.symm (Subgroup.mem_centralizer_singleton_iff.1 hmem')

end Three

section Extraction

theorem commute_of_pm_points {L A : Type*} [Field L] [Ring A] [Algebra L A] (h2 : (2 : L) ≠ 0)
    {c₁ : L} (hc : c₁ ≠ 0) {a b z : A}
    (hp : z * (1 + c₁ • a + c₁ ^ 2 • b) = (1 + c₁ • a + c₁ ^ 2 • b) * z)
    (hm : z * (1 + (-c₁) • a + (-c₁) ^ 2 • b) = (1 + (-c₁) • a + (-c₁) ^ 2 • b) * z) :
    z * a = a * z ∧ z * b = b * z := by
  have e1 : c₁ • (z * a - a * z) + c₁ ^ 2 • (z * b - b * z) = 0 := by
    calc c₁ • (z * a - a * z) + c₁ ^ 2 • (z * b - b * z)
        = z * (1 + c₁ • a + c₁ ^ 2 • b) - (1 + c₁ • a + c₁ ^ 2 • b) * z := by
          simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
          abel
      _ = 0 := sub_eq_zero.2 hp
  have e2 : (-c₁) • (z * a - a * z) + (-c₁) ^ 2 • (z * b - b * z) = 0 := by
    calc (-c₁) • (z * a - a * z) + (-c₁) ^ 2 • (z * b - b * z)
        = z * (1 + (-c₁) • a + (-c₁) ^ 2 • b) - (1 + (-c₁) • a + (-c₁) ^ 2 • b) * z := by
          simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
          abel
      _ = 0 := sub_eq_zero.2 hm
  have hV : (2 * c₁ ^ 2) • (z * b - b * z) = 0 := by
    calc (2 * c₁ ^ 2) • (z * b - b * z)
        = (c₁ • (z * a - a * z) + c₁ ^ 2 • (z * b - b * z)) +
          ((-c₁) • (z * a - a * z) + (-c₁) ^ 2 • (z * b - b * z)) := by module
      _ = 0 := by rw [e1, e2, add_zero]
  have hV' : z * b - b * z = 0 := by
    have hne : (2 * c₁ ^ 2 : L) ≠ 0 := mul_ne_zero h2 (pow_ne_zero 2 hc)
    exact (smul_eq_zero.1 hV).resolve_left hne
  have hU : c₁ • (z * a - a * z) = 0 := by
    rw [hV', smul_zero, add_zero] at e1
    exact e1
  have hU' : z * a - a * z = 0 := (smul_eq_zero.1 hU).resolve_left hc
  exact ⟨sub_eq_zero.1 hU', sub_eq_zero.1 hV'⟩

end Extraction

end CFSG.HardMathSupport.Timmesfeld.LangTorus
