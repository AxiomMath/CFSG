module

public import CFSG.Holt.H78.AltModelSylow
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Holt.H78

open Equiv Equiv.Perm MulAction

section Aut

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ]

private theorem map_permCongrHom_alternatingGroup {Δ' : Type*} [Fintype Δ'] [DecidableEq Δ']
    (e : Δ ≃ Δ') :
    (alternatingGroup Δ).map (permCongrHom e : Perm Δ →* Perm Δ') = alternatingGroup Δ' := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_alternatingGroup] at hf ⊢
    exact (sign_permCongr e f).trans hf
  · intro hg
    refine ⟨e.symm.permCongr g, ?_, ?_⟩
    · rw [mem_alternatingGroup] at hg ⊢
      exact (sign_permCongr e.symm g).trans hg
    · ext x
      simp [permCongrHom, permCongr_apply]

theorem exists_perm_conj_eq_of_mulAut_alternatingGroup (h5 : 5 ≤ Fintype.card Δ)
    (h6 : Fintype.card Δ ≠ 6) (φ : MulAut (alternatingGroup Δ)) :
    ∃ σ : Perm Δ, ∀ a : alternatingGroup Δ,
      ((φ a : alternatingGroup Δ) : Perm Δ) = σ * a * σ⁻¹ := by
  set n := Fintype.card Δ
  let e : Δ ≃ Fin n := Fintype.equivFin Δ
  let Φ : Perm Δ ≃* Perm (Fin n) := permCongrHom e
  let ψ : alternatingGroup Δ ≃* alternatingGroup (Fin n) :=
    (Φ.subgroupMap _).trans (MulEquiv.subgroupCongr (map_permCongrHom_alternatingGroup e))
  have hψ : ∀ a, ((ψ a : alternatingGroup (Fin n)) : Perm (Fin n)) = Φ a := fun a => rfl
  obtain ⟨σ', hσ'⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    h5 h6).2 (ψ.symm.trans (φ.trans ψ))
  refine ⟨Φ.symm σ', fun a => Φ.injective ?_⟩
  have h := congrArg (fun θ : MulAut (alternatingGroup (Fin n)) =>
    ((θ (ψ a) : alternatingGroup (Fin n)) : Perm (Fin n))) hσ'
  simp only [MulAut.conjNormal_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hψ] at h
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h]

end Aut

section IndexN

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ]

theorem exists_eq_alternatingGroup_inf_stabilizer_of_relIndex_eq (h5 : 5 ≤ Fintype.card Δ)
    (h6 : Fintype.card Δ ≠ 6) {K : Subgroup (Perm Δ)} (hK : K ≤ alternatingGroup Δ)
    (hidx : K.relIndex (alternatingGroup Δ) = Fintype.card Δ) :
    ∃ δ : Δ, K = alternatingGroup Δ ⊓ stabilizer (Perm Δ) δ := by
  set A := alternatingGroup Δ
  set K' : Subgroup A := K.subgroupOf A
  have hK'idx : K'.index = Fintype.card Δ := hidx
  have : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by rwa [Nat.card_eq_fintype_card])
  obtain ⟨f⟩ : Nonempty ((A ⧸ K') ≃ Δ) := by
    rw [← Finite.card_eq, ← Subgroup.index_eq_card, hK'idx, Nat.card_eq_fintype_card]
  let ψ : A →* Perm Δ := (permCongrHom f).toMonoidHom.comp (toPermHom A (A ⧸ K'))
  have hψ : ∀ (a : A) (q : A ⧸ K'), ψ a (f q) = f (a • q) := fun a q => by
    simp [ψ, permCongrHom, permCongr_apply]
  have hcore : K'.normalCore = ⊥ := by
    have := Subgroup.normalCore_normal K'
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K'.normalCore with h | h
    · exact h
    · exfalso
      have htop : K' = ⊤ := top_le_iff.1 (h ▸ Subgroup.normalCore_le K')
      rw [htop, Subgroup.index_top] at hK'idx
      omega
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← hcore, Subgroup.normalCore_eq_ker]
    ext a
    simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hrange : ψ.range = A := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨a, rfl⟩
      have hc := Abelianization.commutator_subset_ker (Perm.sign.comp ψ)
      rw [commutator_alternatingGroup_eq_top (by rwa [Nat.card_eq_fintype_card])] at hc
      exact hc (Subgroup.mem_top a)
    · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  let θ : MulAut A := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  obtain ⟨σ, hσ⟩ := exists_perm_conj_eq_of_mulAut_alternatingGroup h5 h6 θ
  have hσψ : ∀ a : A, ψ a = σ * a * σ⁻¹ := fun a => hσ a
  have key : ∀ a : A, a ∈ K' ↔ (a : Perm Δ) (σ⁻¹ (f ((1 : A) : A ⧸ K'))) =
      σ⁻¹ (f ((1 : A) : A ⧸ K')) := by
    intro a
    have hst : a ∈ K' ↔ a • ((1 : A) : A ⧸ K') = ((1 : A) : A ⧸ K') := by
      rw [← mem_stabilizer_iff, MulAction.stabilizer_quotient]
    rw [hst, ← f.injective.eq_iff, ← hψ, hσψ, Perm.mul_apply, Perm.mul_apply,
      ← Perm.eq_inv_iff_eq]
  refine ⟨σ⁻¹ (f ((1 : A) : A ⧸ K')), ?_⟩
  ext g
  rw [Subgroup.mem_inf, mem_stabilizer_iff, Perm.smul_def]
  constructor
  · intro hg
    exact ⟨hK hg, (key ⟨g, hK hg⟩).1 hg⟩
  · rintro ⟨hgA, hgδ⟩
    exact (key ⟨g, hgA⟩).2 hgδ

end IndexN

section Orders

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ] {Δ' : Type*} [Fintype Δ'] [DecidableEq Δ']

theorem card_eq_of_mulEquiv_alternatingGroup (h2 : 2 ≤ Fintype.card Δ)
    (h2' : 2 ≤ Fintype.card Δ') (e : alternatingGroup Δ ≃* alternatingGroup Δ') :
    Fintype.card Δ = Fintype.card Δ' := by
  have : Nontrivial Δ := Fintype.one_lt_card_iff_nontrivial.1 h2
  have : Nontrivial Δ' := Fintype.one_lt_card_iff_nontrivial.1 h2'
  have h := Fintype.card_congr e.toEquiv
  have h1 := two_mul_card_alternatingGroup (α := Δ)
  have h1' := two_mul_card_alternatingGroup (α := Δ')
  rw [Fintype.card_perm] at h1 h1'
  rw [h] at h1
  exact (Nat.factorial_inj (by omega)).1 (h1.symm.trans h1')

theorem card_eq_of_mulEquiv_alternatingGroup_inf_stabilizer (h3 : 3 ≤ Fintype.card Δ)
    (h2' : 2 ≤ Fintype.card Δ') {α : Δ}
    (e : (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α : Subgroup (Perm Δ)) ≃*
      alternatingGroup Δ') :
    Fintype.card Δ' = Fintype.card Δ - 1 := by
  have hcard : Fintype.card {x // x ≠ α} = Fintype.card Δ - 1 := by simp
  rw [← hcard]
  exact (card_eq_of_mulEquiv_alternatingGroup (by rw [hcard]; omega) h2'
    ((alternatingGroupStabilizerEquiv α).trans e)).symm

end Orders

end CFSG.Holt.H78
