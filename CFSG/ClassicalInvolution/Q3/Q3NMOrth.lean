module

public import CFSG.ClassicalInvolution.Q3.Q3NMLie
public import CFSG.ClassicalInvolution.Q3.Q3NMBlocks
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Split
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Balance
  CFSG.ComponentClassification

section Orth

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mem_normalizer_elementaryGroup {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    g ∈ Subgroup.normalizer (elementaryGroup Q : Set (V ≃ₗ[K] V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_elementaryGroup hg hx, fun hx => ?_⟩
  have := conj_mem_elementaryGroup (inv_mem hg) hx
  simpa [mul_assoc] using this

variable (Q) in
@[expose] noncomputable def conjE (g : V ≃ₗ[K] V)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : MulAut ↥(elementaryGroup Q) :=
  conjAut (elementaryGroup Q) g (mem_normalizer_elementaryGroup hg)

theorem mem_fixedSubgroup_conjE {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (b : ↥(elementaryGroup Q)) :
    b ∈ fixedSubgroup (conjE Q g hg) ↔ (b : V ≃ₗ[K] V) * g = g * b := by
  rw [mem_fixedSubgroup_iff]
  constructor
  · intro h
    have h' : g * (b : V ≃ₗ[K] V) * g⁻¹ = b := congrArg Subtype.val h
    calc (b : V ≃ₗ[K] V) * g = (g * (b : V ≃ₗ[K] V) * g⁻¹) * g := by rw [h']
      _ = g * b := by group
  · intro h
    refine Subtype.ext ?_
    show g * (b : V ≃ₗ[K] V) * g⁻¹ = b
    rw [← h]
    group

section TwoBlocks

variable [Finite K] [FiniteDimensional K V] {W W' : Submodule K V}

theorem oddCoreIn_fixed_eq_bot_of_two_blocks (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V)
    (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0)
    (hW0 : W ≠ ⊥) (hW'0 : W' ≠ ⊥) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgW : g ∈ stabSub W) (hgW' : g ∈ stabSub W')
    (hstab : ∀ b : ↥(elementaryGroup Q), (b : V ≃ₗ[K] V) * g = g * b →
      (b : V ≃ₗ[K] V) ∈ stabSub W ∧ (b : V ≃ₗ[K] V) ∈ stabSub W')
    (hgc : ∀ φ : ↥(elementaryGroup (Q.comp W.subtype)),
      resHom W ⟨g, hgW⟩ * φ = φ * resHom W ⟨g, hgW⟩)
    (hgc' : ∀ φ : ↥(elementaryGroup (Q.comp W'.subtype)),
      resHom W' ⟨g, hgW'⟩ * φ = φ * resHom W' ⟨g, hgW'⟩) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) (conjE Q g hg))) = ⊥ := by
  have hcen : ∀ z ∈ Subgroup.center ↥(elementaryGroup Q), (z : V ≃ₗ[K] V) ∈ scalars K V :=
    fun z hz => mem_scalars_of_mem_center hK hQ hdim hz
  have hZ := isPGroup_center_elementaryGroup hK hQ hdim
  have horth' : ∀ u ∈ W', ∀ w ∈ W, polar Q u w = 0 := fun u hu w hw => by
    rw [polar_comm]
    exact horth w hw u hu
  have hcomm : ∀ {c : V ≃ₗ[K] V} {U U' : Submodule K V} (hc : IsCompl U U')
      (horth : ∀ u ∈ U, ∀ w ∈ U', polar Q u w = 0) (hcU : c ∈ stabSub U) (hcU' : c ∈ stabSub U')
      (hφ : ∀ φ : ↥(elementaryGroup (Q.comp U.subtype)),
        resHom U ⟨c, hcU⟩ * φ = φ * resHom U ⟨c, hcU⟩) (φ : ↥(elementaryGroup (Q.comp U.subtype))),
      (blockHom Q hc horth φ : V ≃ₗ[K] V) * c = c * (blockHom Q hc horth φ : V ≃ₗ[K] V) :=
    fun hc horth hcU hcU' hφ φ => (commute_orthExtend_of_commute hc hcU hcU' (hφ φ)).symm
  refine oddCoreIn_fixed_eq_bot_of_blocks hZ (conjE Q g hg) (ι := Bool)
    (fun i => cond i (blockHom Q hc horth).range (blockHom Q hc.symm horth').range)
    ?_ ?_ ?_ ?_
  · intro i
    cases i
    · rintro _ ⟨φ, rfl⟩
      exact (mem_fixedSubgroup_conjE hg _).mpr (hcomm hc.symm horth' hgW' hgW hgc' φ)
    · rintro _ ⟨φ, rfl⟩
      exact (mem_fixedSubgroup_conjE hg _).mpr (hcomm hc horth hgW hgW' hgc φ)
  · intro i b hb x hx
    obtain ⟨hbW, hbW'⟩ := hstab b ((mem_fixedSubgroup_conjE hg b).mp hb)
    cases i
    · exact conj_blockHom_mem_range hc.symm horth' hbW' hbW hx
    · exact conj_blockHom_mem_range hc horth hbW hbW' hx
  · intro i
    cases i
    · exact oddCoreIn_map_blockHom_eq_bot hK hQ hcen hc.symm horth' hW0
    · exact oddCoreIn_map_blockHom_eq_bot hK hQ hcen hc horth hW'0
  · intro ν hν hcm
    obtain ⟨hνW, hνW'⟩ := hstab ν ((mem_fixedSubgroup_conjE hg ν).mp hν)
    obtain ⟨e₁, h₁⟩ := exists_pow_res_eq_one hK hQ hc horth hνW hνW'
      (fun φ => (hcm true _ ⟨φ, rfl⟩).symm)
    obtain ⟨e₂, h₂⟩ := exists_pow_res_eq_one hK hQ hc.symm horth' hνW' hνW
      (fun φ => (hcm false _ ⟨φ, rfl⟩).symm)
    refine ⟨e₁ + e₂, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow]
    refine pow_eq_one_of_pow_res_eq_one hc hνW hνW' ?_ ?_
    · rw [pow_add, pow_mul, h₁, one_pow]
    · rw [add_comm, pow_add, pow_mul, h₂, one_pow]

end TwoBlocks

section Involution

variable [Finite K] [FiniteDimensional K V]

theorem oddCoreIn_fixed_eq_bot_of_involution (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hgs : g ∉ scalars K V) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) (conjE Q g hg))) = ⊥ := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hc := isCompl_plusSp_minusSp h2 hg2
  have horth : ∀ u ∈ plusSp g, ∀ w ∈ minusSp g, polar Q u w = 0 := fun u hu w hw =>
    polar_plusSp_minusSp h2 hg hu hw
  have hW0 : plusSp g ≠ ⊥ := fun h => hgs (mem_scalars_of_plusSp_eq_bot h2 hg2 h)
  have hW'0 : minusSp g ≠ ⊥ := fun h => hgs (mem_scalars_of_minusSp_eq_bot h2 hg2 h)
  have hgW : g ∈ stabSub (plusSp g) := mem_stabSub_plusSp rfl
  have hgW' : g ∈ stabSub (minusSp g) := mem_stabSub_minusSp rfl
  refine oddCoreIn_fixed_eq_bot_of_two_blocks hK hQ hdim hc horth hW0 hW'0 hg hgW hgW' ?_ ?_ ?_
  · intro b hb
    exact ⟨mem_stabSub_plusSp hb, mem_stabSub_minusSp hb⟩
  · intro φ
    rw [resHom_plusSp hgW, one_mul, mul_one]
  · intro φ
    exact resHom_minusSp_comm hgW' φ

end Involution

end Orth

end CFSG.ClassicalInvolution.Q3.Q3NM
