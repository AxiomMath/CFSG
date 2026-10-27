module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem normal_pSubgroup_inf_center_ne_bot {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G)
    (normal : Subgroup G) [normal.Normal] (hnontrivial : normal ≠ ⊥) :
    normal ⊓ Subgroup.center G ≠ ⊥ := by
  have : Fact prime.Prime := ⟨hprime⟩
  let : MulDistribMulAction G normal := MulDistribMulAction.compHom normal
    (MulAut.conjNormal : G →* MulAut normal)
  have hdivisor : prime ∣ Nat.card normal := by
    rcases (hpgroup.to_subgroup normal).card_eq_or_dvd with hcard | hdivisor
    · exact False.elim (hnontrivial (Subgroup.card_eq_one.mp hcard))
    · exact hdivisor
  have hone : (1 : normal) ∈ MulAction.fixedPoints G normal := by
    intro member
    exact smul_one member
  obtain ⟨fixed, hfixed, hne⟩ := hpgroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point normal hdivisor hone
  intro hbot
  have hcentral : (fixed : G) ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro member
    have heq := congrArg (fun value : normal => (value : G)) (hfixed member)
    change member * (fixed : G) * member⁻¹ = fixed at heq
    have hmul := congrArg (fun value : G => value * member) heq
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  have hmem : (fixed : G) ∈ normal ⊓ Subgroup.center G := ⟨fixed.property, hcentral⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne (Subtype.ext hmem).symm

@[expose] noncomputable def normalFixedModulo {G : Type u} [Group G]
    (normal kernel : Subgroup G) [kernel.Normal] : Subgroup G :=
  normal ⊓ (Subgroup.center (G ⧸ kernel)).comap (QuotientGroup.mk' kernel)

theorem normalFixedModulo_normal {G : Type u} [Group G]
    (normal kernel : Subgroup G) [normal.Normal] [kernel.Normal] : (normalFixedModulo normal kernel).Normal := by
  unfold normalFixedModulo
  infer_instance

theorem kernel_le_normalFixedModulo {G : Type u} [Group G]
    (normal kernel : Subgroup G) [kernel.Normal] (hle : kernel ≤ normal) :
    kernel ≤ normalFixedModulo normal kernel := by
  intro member hmember
  refine ⟨hle hmember, ?_⟩
  change QuotientGroup.mk' kernel member ∈ Subgroup.center (G ⧸ kernel)
  have heq : QuotientGroup.mk' kernel member = 1 := by
    apply MonoidHom.mem_ker.mp
    rwa [QuotientGroup.ker_mk']
  rw [heq]
  exact Subgroup.one_mem _

theorem normalFixedModulo_commutator_le_kernel {G : Type u} [Group G]
    (normal kernel : Subgroup G) [kernel.Normal] : ⁅normalFixedModulo normal kernel, ⊤⁆ ≤ kernel := by
  apply Subgroup.commutator_le.mpr
  intro first hfirst second _
  have hcenter : QuotientGroup.mk' kernel first ∈ Subgroup.center (G ⧸ kernel) := hfirst.2
  have hcommute : Commute (QuotientGroup.mk' kernel first) (QuotientGroup.mk' kernel second) :=
    (Subgroup.mem_center_iff.mp hcenter _).symm
  have hmem : ⁅first, second⁆ ∈ (QuotientGroup.mk' kernel).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    exact hcommute.commutator_eq
  rwa [QuotientGroup.ker_mk'] at hmem

theorem normalFixedModulo_strict {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G)
    (normal kernel : Subgroup G) [normal.Normal] [kernel.Normal] (hproper : kernel < normal) :
    kernel < normalFixedModulo normal kernel := by
  have himageNormal : (normal.map (QuotientGroup.mk' kernel)).Normal :=
    (inferInstance : normal.Normal).map (QuotientGroup.mk' kernel) (QuotientGroup.mk'_surjective kernel)
  have : (normal.map (QuotientGroup.mk' kernel)).Normal := himageNormal
  have himageNe : normal.map (QuotientGroup.mk' kernel) ≠ ⊥ := by
    intro heq
    have hle := (Subgroup.map_eq_bot_iff normal).mp heq
    rw [QuotientGroup.ker_mk'] at hle
    exact hproper.not_ge hle
  have hcenter := normal_pSubgroup_inf_center_ne_bot prime hprime (hpgroup.to_quotient kernel)
    (normal.map (QuotientGroup.mk' kernel)) himageNe
  apply lt_of_le_of_ne (kernel_le_normalFixedModulo normal kernel hproper.le)
  intro heq
  apply hcenter
  apply le_antisymm _ bot_le
  rintro member ⟨⟨representative, hrepresentative, rfl⟩, hcentral⟩
  have hfixed : representative ∈ normalFixedModulo normal kernel := ⟨hrepresentative, hcentral⟩
  have hkernel : representative ∈ kernel := heq.symm ▸ hfixed
  apply Subgroup.mem_bot.mpr
  apply MonoidHom.mem_ker.mp
  rwa [QuotientGroup.ker_mk']

end CFSG.RankThreeEvenClassification.Helpers
