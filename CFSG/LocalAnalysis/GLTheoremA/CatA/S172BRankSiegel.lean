module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Commutator
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem rootGroup_le_orthDerived [FiniteDimensional (ZMod 2) V]
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V) {e : V} (he : Q e = 0) :
    rootGroup Q e ≤ orthDerived Q := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.1 hg
  exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eichler_mem_commutator hQ (Or.inl h5)
    he hw

theorem mul_self_eq_one_of_mem_rootGroup {e : V} {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ rootGroup Q e) :
    g * g = 1 := by
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.1 hg
  rw [eichler_mul hw hw,
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.add_self_eq_zero_f2 (ZMod 2) w,
    eichler_zero_right]

theorem isPGroup_two_subgroupOf_rootGroup (e : V) :
    IsPGroup 2 ((rootGroup Q e).subgroupOf (orthDerived Q)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : g * g = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_self_eq_one_of_mem_rootGroup (Subgroup.mem_subgroupOf.1 g.2)
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by rw [h]; rfl⟩
  · exact ⟨1, by rw [h]; rfl⟩

theorem subgroupOf_rootGroup_ne_bot [FiniteDimensional (ZMod 2) V]
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V) {e f a : V} (he : Q e = 0)
    (ha : Q a = 1) (hea : polar Q e a = 0) (hfe : polar Q f e = 1) (hfa : polar Q f a = 0) :
    (rootGroup Q e).subgroupOf (orthDerived Q) ≠ ⊥ := by
  intro hbot
  have hmem : eichler Q e a ∈ orthDerived Q :=
    rootGroup_le_orthDerived hQ h5 he (eichler_mem_rootGroup hea)
  have h1 : (⟨eichler Q e a, hmem⟩ : ↥(orthDerived Q)) ∈ (rootGroup Q e).subgroupOf (orthDerived Q) :=
    Subgroup.mem_subgroupOf.2 (eichler_mem_rootGroup hea)
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : eichler Q e a = 1 := congrArg Subtype.val h1
  have h3 := congrArg (fun g : V ≃ₗ[ZMod 2] V => g f) h2
  simp only [eichler_apply he hea, hfe, hfa, ha, LinearEquiv.coe_one, id_eq, one_smul, mul_one,
    zero_add] at h3
  have h4 : a = e := by
    have : a - e = 0 := by
      have h5' : f + a - e = f := h3
      calc a - e = (f + a - e) - f := by abel
        _ = 0 := by rw [h5', sub_self]
    exact sub_eq_zero.1 this
  rw [h4, he] at ha
  exact zero_ne_one ha

theorem mem_normalizer_subgroupOf_rootGroup {e : V} {g : ↥(orthDerived Q)}
    (hg : (g : V ≃ₗ[ZMod 2] V) e = e) :
    g ∈ Subgroup.normalizer
      (((rootGroup Q e).subgroupOf (orthDerived Q) : Subgroup ↥(orthDerived Q)) :
        Set ↥(orthDerived Q)) := by
  have key : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[ZMod 2] V) e = e →
      ∀ h ∈ (rootGroup Q e).subgroupOf (orthDerived Q),
        g * h * g⁻¹ ∈ (rootGroup Q e).subgroupOf (orthDerived Q) := by
    intro g hg h hh
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    have hgO : (g : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.commutator_le_self _ g.2
    exact conj_mem_rootGroup_of_apply_eq_smul hgO (by rw [hg, one_smul]) hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have hginv : ((g⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) e = e := by
    calc ((g⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) e
        = ((g⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ((g : V ≃ₗ[ZMod 2] V) e) := by rw [hg]
      _ = e := by
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
        rfl
  have := key g⁻¹ hginv _ hh
  simpa [mul_assoc] using this

end CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

end
