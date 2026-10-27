module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eSp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eComp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e.Sp

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel centralModel_SL
  centralModel_statedSp CentralModel.of_mulEquiv)
open scoped MatrixGroups

theorem conjAut_statedSp_apply {r : ℕ} {K : Type} [Field K] (g : StatedSp r K)
    (x : StatedProj (StatedSp r K)) :
    conjAut r K ⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩ x =
      (g : StatedProj (StatedSp r K)) * x * (g : StatedProj (StatedSp r K))⁻¹ := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective x
  have hconj : conjSp r K ⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩ g' = g * g' * g⁻¹ :=
    Subtype.ext ((coe_conjSp _ g').trans rfl)
  change conjAut r K _ (proj r K g') = _
  rw [conjAut_proj, hconj]
  show ((g * g' * g⁻¹ : StatedSp r K) : StatedProj (StatedSp r K)) = _
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem mulAut_conj_eq_conjAut {r : ℕ} {K : Type} [Field K] (g : StatedSp r K) :
    MulAut.conj (g : StatedProj (StatedSp r K)) =
      conjAut r K ⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩ := by
  ext x
  rw [MulAut.conj_apply, conjAut_statedSp_apply]

theorem fixedSubgroup_eq_fcp {X : Type} [Group X] (α : MulAut X) :
    HarrisLit.T1.fixedSubgroup α = FixedCommutingProduct.fixedSubgroup α := by
  ext x
  rfl

theorem comp_N_of_sp {N : ℕ → (L : Type) → [Group L] → Prop}
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → N p L)
    (hT2 : ∀ {L : Type} [Group L] {K : Type} [Field K] [Finite K] {p f : ℕ}, p.Prime → p ≠ 2 →
      Nat.card K = p ^ f → (StatedSp 3 K ≃* L) → N p L)
    {r : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hr : 2 ≤ r) (A : gsp r K)
    (hAsp : (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K) (hA : orderOf (conjAut r K A) = 2)
    {L : Subgroup (FixedCommutingProduct.fixedSubgroup (conjAut r K A))} (hL : IsComponent L) :
    N p L := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · rw [h0, pow_zero] at hK
      have := Finite.one_lt_card (α := K)
      omega
    · exact h
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  rcases sp_comp_types hp hp2 hK hr A hAsp hA hL with ⟨k, hk, ⟨eS⟩⟩ | h | h
  · by_cases hk3 : k = 3
    · subst hk3
      exact hT2 hp hp2 hK eS.symm
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    ·
      obtain rfl : k = 1 := by omega
      let eSL := ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K
      have h3 : p ^ f ≠ 3 := by
        intro h3
        have : Group.IsSolvable (StatedSp 1 K) :=
          LieType.HighestRoot.isSolvable_of_mulEquiv (hK.trans h3) eSL.symm
        have : Group.IsSolvable L :=
          Group.isSolvable_of_isSolvable_injective (f := eS.toMonoidHom) eS.injective
        have : Group.IsPerfect L := hL.1.1
        have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
        exact Group.IsPerfect.not_isSolvable L inferInstance
      have hadm : StatedLieAdmissible .PSL 2 p f :=
        CatLeafProof.OddInner.admissible_PSL hp hf le_rfl (Or.inr fun h => by
          rw [h] at hodd
          exact (by decide : ¬ Odd 2) hodd) (Or.inr h3)
      have hc := (centralModel_SL hadm hK).of_mulEquiv (eS.trans eSL.symm)
      exact hT1 hp2 hc.1 hc.2 (by rintro ⟨h | h, -⟩ <;> exact absurd h (by decide))
    · have hc := (centralModel_statedSp (CatLeafProof.OddInner.admissible_PSp hp hp2 hf hk2)
        hK).of_mulEquiv eS
      exact hT1 hp2 hc.1 hc.2 (by rintro ⟨-, h⟩; exact hk3 h)
  · exact hT1 hp2 h.1 h.2 (by rintro ⟨h | h, -⟩ <;> exact absurd h (by decide))
  · exact hT1 hp2 h.1 h.2 (by rintro ⟨h | h, -⟩ <;> exact absurd h (by decide))

theorem fam_psp_of {N : ℕ → (L : Type) → [Group L] → Prop}
    (hN : ∀ {p : ℕ} {L M : Type} [Group L] [Group M], (L ≃* M) → N p M → N p L)
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → N p L)
    (hT2 : ∀ {L : Type} [Group L] {K : Type} [Field K] [Finite K] {p f : ℕ}, p.Prime → p ≠ 2 →
      Nat.card K = p ^ f → (StatedSp 3 K ≃* L) → N p L)
    (X : Type) [Group X] (n p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : Blueprint.LieModel X .PSp n p f) (g : X) (hg : orderOf (MulAut.conj g) = 2)
    (L : Subgroup (fixedSubgroup (MulAut.conj g))) (hL : IsComponent L) : N p L := by
  obtain ⟨⟨-, -, hn, -⟩, F, _, _, hFc, ⟨θ⟩⟩ :=
    Comp.statedClassicalModel_of_lieModel (by decide) hX
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (θ g)
  have hα : MulAut.conj (θ g) =
      conjAut n F ⟨(A : GL (Fin n ⊕ Fin n) F), statedSp_le_gsp A.2⟩ := by
    rw [← hA]
    exact mulAut_conj_eq_conjAut A
  have hord : orderOf (MulAut.conj (θ g)) = 2 := by
    have e : MulAut.conj (θ g) = MulAut.congr θ (MulAut.conj g) := by
      ext x
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [e, ← hg]
    exact orderOf_injective (MulAut.congr θ).toMonoidHom (MulAut.congr θ).injective _
  set ψ₀ := MulEquiv.subgroupCongr (fixedSubgroup_eq_fcp (MulAut.conj g)) with hψ₀
  have hL₀ := LocalCores.isComponent_map_mulEquiv ψ₀ hL
  obtain ⟨L₁, hL₁, ⟨e₁⟩⟩ := Comp.exists_fixed_comp_of_isComponent θ g hL₀
  set ψ := MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup hα) with hψ
  have hL₂ := LocalCores.isComponent_map_mulEquiv ψ hL₁
  have hA2 : orderOf (conjAut n F ⟨(A : GL (Fin n ⊕ Fin n) F), statedSp_le_gsp A.2⟩) = 2 := by
    rw [← hα]
    exact hord
  exact hN (L.equivMapOfInjective ψ₀.toMonoidHom ψ₀.injective) (hN e₁
    (hN (L₁.equivMapOfInjective ψ.toMonoidHom ψ.injective)
      (comp_N_of_sp (N := N) hT1 hT2 hp hp2 hFc hn _ A.2 hA2 hL₂)))

theorem famNoSpin7_psp
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → NoSpin7 p L)
    (hT2 : ∀ {L : Type} [Group L] {K : Type} [Field K] [Finite K] {p f : ℕ}, p.Prime → p ≠ 2 →
      Nat.card K = p ^ f → (StatedSp 3 K ≃* L) → NoSpin7 p L) :
    FamNoSpin7 .PSp :=
  fun X _ n p f hp hp2 _ hX g hg L hL => fam_psp_of (N := NoSpin7)
    (fun e h => NoSpin7.of_mulEquiv e h) hT1 hT2 X n p f hp hp2 hX g hg L hL

end CFSG.ComponentClassification.HarrisLit.T1.P51e.Sp
