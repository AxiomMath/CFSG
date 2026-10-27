module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaAutCentralizer

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

theorem exists_fusion_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (θ : G ≃* G')
    {α : MulAut G} {γ : MulAut G'} (hθ : ∀ x, γ (θ x) = θ (α x)) {l' : G'}
    (h1 : l' * (γ l')⁻¹ ≠ 1)
    (h2 : l' * (γ l')⁻¹ ∈
      ⁅⁅fixedSubgroup γ, fixedSubgroup γ⁆, ⁅fixedSubgroup γ, fixedSubgroup γ⁆⁆) :
    ∃ l : G, l * (α l)⁻¹ ≠ 1 ∧
      l * (α l)⁻¹ ∈ ⁅⁅fixedSubgroup α, fixedSubgroup α⁆, ⁅fixedSubgroup α, fixedSubgroup α⁆⁆ := by
  have hfix : fixedSubgroup γ = (fixedSubgroup α).map θ.toMonoidHom := by
    ext x
    constructor
    · intro hx
      refine ⟨θ.symm x, ?_, θ.apply_symm_apply x⟩
      change α (θ.symm x) = θ.symm x
      apply θ.injective
      rw [← hθ, θ.apply_symm_apply]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      change γ (θ y) = θ y
      rw [hθ, mem_fixedSubgroup.mp hy]
  have key : θ (θ.symm l' * (α (θ.symm l'))⁻¹) = l' * (γ l')⁻¹ := by
    rw [map_mul, map_inv, ← hθ, θ.apply_symm_apply]
  refine ⟨θ.symm l', fun h0 => h1 (by rw [← key, h0, map_one]), ?_⟩
  rw [hfix, ← Subgroup.map_commutator, ← Subgroup.map_commutator, ← key] at h2
  exact (Subgroup.mem_map_iff_mem θ.injective).mp h2

theorem exists_sixQ_mulEquiv {Q : Type} [Group Q] (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 1 F), Nonempty (Q ≃* sixQ h) := by
  obtain ⟨F, _, h, ⟨f⟩⟩ := exists_hypPSU_mulEquiv hQ
  exact ⟨F, _, h, ⟨f.symm.trans (hypSixQ h)⟩⟩

theorem fusion_of_lieModel {Q : Type} [Group Q] (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1)
    (α : MulAut Q) (hα : α * α = 1) (hout : ∀ m : Q, α ≠ MulAut.conj m) :
    ∃ l : Q, l * (α l)⁻¹ ≠ 1 ∧ l * (α l)⁻¹ ∈
      ⁅⁅fixedSubgroup α, fixedSubgroup α⁆, ⁅fixedSubgroup α, fixedSubgroup α⁆⁆ := by
  obtain ⟨F, _, h, ⟨φ⟩⟩ := exists_sixQ_mulEquiv hQ
  set α' : MulAut (sixQ h) := (φ.symm.trans α).trans φ
  have hα'x : ∀ x, α' x = φ (α (φ.symm x)) := fun x => rfl
  have hαα : ∀ y, α (α y) = y := fun y => by rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  have hα'2 : α' * α' = 1 := by
    ext x
    rw [MulAut.mul_apply, hα'x, hα'x, MulEquiv.symm_apply_apply, hαα, MulEquiv.apply_symm_apply,
      MulAut.one_apply]
  have hout' : ∀ q, α' ≠ MulAut.conj q := fun q hq => hout (φ.symm q) (by
    ext x
    have := congrArg (fun β : MulAut _ => β (φ x)) hq
    simp only [hα'x, MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
    rw [MulAut.conj_apply, ← φ.symm_apply_apply (α x), this, map_mul, map_mul, map_inv,
      MulEquiv.symm_apply_apply])
  obtain ⟨ω, hω⟩ := exists_omega h
  have hord : orderOf α' = 2 :=
    orderOf_eq_prime (by rw [sq, hα'2]) fun h1 => hout' 1 (by rw [h1, map_one])
  obtain ⟨A, hA⟩ := exists_conj_eq_of_orderOf_eq_two h ω hω α' hord
  set c := UnitaryHigher.primeFormConjHom h _ A
  have hkey : ∀ γ : MulAut (sixQ h), c * α' * c⁻¹ = γ →
      (∃ l' : sixQ h, l' * (γ l')⁻¹ ≠ 1 ∧
        l' * (γ l')⁻¹ ∈ ⁅⁅fixedSubgroup γ, fixedSubgroup γ⁆, ⁅fixedSubgroup γ, fixedSubgroup γ⁆⁆) →
      ∃ l : Q, l * (α l)⁻¹ ≠ 1 ∧ l * (α l)⁻¹ ∈
        ⁅⁅fixedSubgroup α, fixedSubgroup α⁆, ⁅fixedSubgroup α, fixedSubgroup α⁆⁆ := by
    rintro γ hγ ⟨l', h1, h2⟩
    refine exists_fusion_of_mulEquiv (φ.trans c) (fun x => ?_) h1 h2
    rw [← hγ]
    change c (α' (c⁻¹ (c (φ x)))) = c (φ (α x))
    rw [MulAut.inv_apply_self, hα'x, MulEquiv.symm_apply_apply]
  rcases hA with ⟨k, -, hk⟩ | hσ | hα1
  · refine absurd ?_ (hout' (c⁻¹ (sixProj h (tElt h k))))
    rw [← mulAut_mul_conj_mul_inv, ← hk]
    group
  · exact hkey _ hσ (exists_fusion_sigmaQ h hω)
  · exact hkey _ hα1 (exists_fusion_alphaOne h hω)

theorem centralizer_A_of_lieModel {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1) (D : ToddParabolic Q) (α : MulAut Q)
    (hα : ∀ a ∈ D.A, α a = a) : ∃ a ∈ D.A, α = MulAut.conj a := by
  obtain ⟨F, _, h, ⟨φ⟩⟩ := exists_sixQ_mulEquiv hQ
  have hsq : ∀ x ∈ (hermQ h).map φ.symm.toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, sq_of_mem_hermQ h hy, map_one]
  have hcard : Nat.card ((hermQ h).map φ.symm.toMonoidHom) = 2 ^ 9 := by
    rw [Subgroup.card_map_of_injective φ.symm.injective, card_hermQ]
  obtain ⟨g, hg⟩ := (D.exists_conj_eq_A hsq).2 hcard.ge
  set θ : sixQ h ≃* Q := φ.symm.trans (MulAut.conj g)
  have hθX : ∀ x ∈ hermQ h, θ x ∈ D.A := fun x hx => by
    rw [← hg]
    exact ⟨φ.symm x, ⟨x, hx, rfl⟩, rfl⟩
  set β : MulAut (sixQ h) := (θ.trans α).trans θ.symm
  have hβ : ∀ x ∈ hermQ h, β x = x := fun x hx => by
    change θ.symm (α (θ x)) = x
    rw [hα _ (hθX x hx), MulEquiv.symm_apply_apply]
  obtain ⟨y, hy, hβy⟩ := exists_eq_conj_of_fixes_hermQ h β hβ
  refine ⟨θ y, hθX y hy, ?_⟩
  ext z
  have := congrArg (fun γ : MulAut (sixQ h) => θ (γ (θ.symm z))) hβy
  change θ (θ.symm (α (θ (θ.symm z)))) = θ (y * θ.symm z * y⁻¹) at this
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv,
    MulEquiv.apply_symm_apply] at this
  rw [this, MulAut.conj_apply]

end CFSG.EvenSmallLie.UnitarySix.Yamada
