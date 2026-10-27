module

public import CFSG.ClassicalInvolution.Asc77.AscCX9ZA
public import CFSG.ClassicalInvolution.Asc77.AscCX9Y

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]


theorem MF2U.reflWit_psu4 {K : Type} [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hq1 : p ^ f % 4 = 1)
    {Y : Type} [Group Y] [Finite Y] (ψ : Su K p f 4 →* Y)
    (hker : ψ.ker ≤ Subgroup.center (Su K p f 4)) (hsurj : Function.Surjective ψ)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y} (htw : TwinSect0 Φ (R.map ψ) (R'.map ψ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) (β : MulAut Y)
    (hβA : ∀ y ∈ R.map ψ, β y = y) (hβA' : ∀ y ∈ R'.map ψ, β y = y) (hβ2 : β * β = 1)
    (hβ1 : β ≠ 1) (hβz : β ≠ MulAut.conj z') :
    ∃ (hA : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hA' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hB : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
      (hB' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
      IsOm5 p f (centTG _ _ β hA hA') ∧ IsOm5 p f (centTG _ _ (β * MulAut.conj z') hB hB') ∧
        DiagWit p (centTG _ _ β hA hA') (centTG _ _ (β * MulAut.conj z') hB hB') := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp2
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hRR : R ≠ R' := fun h => htw.ne (by rw [h])
  obtain ⟨hiR, hi2, hi1, hψi⟩ := CX4.U4.twin_data hK hp2 ψ hker hi htw.hzA
  obtain ⟨hi'R, hi'2, hi'1, hψi'⟩ := CX4.U4.twin_data hK hp2 ψ hker hi' htw.hzA'
  have hc : i' * i⁻¹ ∈ Subgroup.center (Su K p f 4) := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel])
  obtain ⟨g, hRg, hR'g, hig⟩ :=
    twin_std_u hK hp2 ⟨i, hi⟩ ⟨i', hi'⟩ hRR hiR hi2 hi1 hi'R hi'2 hi'1 hc
  have hi'neg : i' = ModelFacts.Orth15.InnerSu.zneg K p f * i :=
    ModelFacts.Orth15.InnerSu.twin_neg_su h2 hig hR'g hi'R hi'2 hi'1
  have hzneg : ψ (ModelFacts.Orth15.InnerSu.zneg K p f) = 1 := by
    have h1 : ψ i' = ψ (ModelFacts.Orth15.InnerSu.zneg K p f) * ψ i := by rw [hi'neg, map_mul]
    rw [hψi, hψi'] at h1
    exact mul_eq_right.mp h1.symm
  have hneg : ∀ x : Su K p f 4, suMat x = -1 → ψ x = 1 := fun x hx => by
    rw [show x = ModelFacts.Orth15.InnerSu.zneg K p f from
      suMat_injective (by rw [hx, ModelFacts.Orth15.InnerSu.suMat_zneg])]
    exact hzneg
  set θ : Su K p f 4 →* Y := ψ.comp (MulAut.conj g).toMonoidHom with hθdef
  have hθ : Function.Surjective θ := hsurj.comp (MulAut.conj g).surjective
  have hθneg : ∀ x : Su K p f 4, suMat x = -1 → θ x = 1 := by
    intro x hx
    show ψ (g * x * g⁻¹) = 1
    apply hneg
    rw [suMat_mul, suMat_mul, hx, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      suMat_mul_suMat_inv]
  have hθker : θ.ker = Subgroup.center (Su K p f 4) := by
    refine le_antisymm (fun x hx => ?_) (CX4.U4.center_le_ker hK hq1 θ hθneg)
    have hx' : g * x * g⁻¹ ∈ ψ.ker := hx
    exact ModelFacts.Orth15.InnerL4.mem_center_of_conj_mem_center (hker hx')
  have hAθ : R.map ψ = (blockEmb K p f 4 2 0 (by norm_num)).range.map θ := by
    rw [hRg, Subgroup.map_map]
  have hA'θ : R'.map ψ = (blockEmb K p f 4 2 2 (by norm_num)).range.map θ := by
    rw [hR'g, Subgroup.map_map]
  have hzθ : z' = θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) := by
    show z' = ψ (g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹)
    rw [← hig, hψi]
  rw [hAθ] at htw hβA ⊢
  rw [hA'θ] at htw hβA' ⊢
  subst hzθ
  exact MF2U.reflWit_std_U hK hp2 hq hq1 θ hθ hθker htw hconj β hβA hβA' hβ2 hβ1 hβz

theorem MF2U.reflWit_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y] (t : StatedLieTag)
    (k e : ℕ) (hadm : StatedLieAdmissible t k p e)
    (ψ : (Generic.modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (hcase : t = .PSU ∧ k = 4 ∧ p ^ e % 4 = 1)
    {R R' : Subgroup (Generic.modelUniv t k p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y} (htw : TwinSect0 Φ (R.map ψ) (R'.map ψ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) (β : MulAut Y)
    (hβA : ∀ y ∈ R.map ψ, β y = y) (hβA' : ∀ y ∈ R'.map ψ, β y = y) (hβ2 : β * β = 1)
    (hβ1 : β ≠ 1) (hβz : β ≠ MulAut.conj z') :
    ∃ (hA : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hA' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hB : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
      (hB' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
      IsOm5 p e (centTG _ _ β hA hA') ∧ IsOm5 p e (centTG _ _ (β * MulAut.conj z') hB hB') ∧
        DiagWit p (centTG _ _ β hA hA') (centTG _ _ (β * MulAut.conj z') hB hB') := by
  obtain ⟨rfl, rfl, h4⟩ := hcase
  have he : 1 ≤ e := hadm.2.1
  have h1 : 1 < p ^ e := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  have hq : 5 ≤ p ^ e := by omega
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e he
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  obtain ⟨θ, hθ⟩ : ∃ θ : Su (GaloisField p (2 * e)) p e 4 →* Y,
      θ = ψ.comp φ.symm.toMonoidHom := ⟨_, rfl⟩
  have hθφ : ∀ r, θ (φ r) = ψ r := fun r => by
    rw [hθ]
    show ψ (φ.symm (φ r)) = ψ r
    rw [MulEquiv.symm_apply_apply]
  have hθker : θ.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    intro y hy
    have h1 : φ.symm y ∈ Subgroup.center (Generic.modelUniv .PSU 4 p e Fact.out).K := by
      apply hker
      rw [MonoidHom.mem_ker, ← hθφ, MulEquiv.apply_symm_apply]
      exact MonoidHom.mem_ker.mp hy
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro w
    apply φ.symm.injective
    rw [map_mul, map_mul]
    exact h1 (φ.symm w)
  have hθsurj : Function.Surjective θ := fun y => by
    obtain ⟨r, rfl⟩ := hsurj y
    exact ⟨φ r, hθφ r⟩
  have hmap : ∀ S : Subgroup (Generic.modelUniv .PSU 4 p e Fact.out).K,
      S.map ψ = (S.map φ.toMonoidHom).map θ := fun S => by
    rw [Subgroup.map_map]
    congr 1
    ext r
    exact (hθφ r).symm
  rw [hmap R] at htw hβA ⊢
  rw [hmap R'] at htw hβA' ⊢
  exact MF2U.reflWit_psu4 hK hp2 hq h4 θ hθker hθsurj ((hφ R).mp hR) ((hφ R').mp hR') htw hconj
    β hβA hβA' hβ2 hβ1 hβz

theorem om6ReflWit_U (h1 : p ^ f % 4 = 1) : Om6ReflWit p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hY β hβA hβA' hβ2 hβ1 hβz
  obtain ⟨D, hD1, i, hi⟩ := hY.lie
  have htw := hY.twin
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : Function.Surjective (D.hom i) := by
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom i).range := by
      intro l
      rw [Subsingleton.elim l i]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : D.tag i = .PSU ∧ D.rank i = 4 ∧ p ^ f % 4 = 1 := by
    simp only [IsOrthTag] at hi
    rcases hi with ⟨h5, -⟩ | ⟨-, hε, -, -⟩ | ⟨-, -, ht, hn⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · omega
    · exfalso
      simp only [piSign, Bool.not_eq_true', decide_eq_false_iff_not] at hε
      exact hε h1
    · exact ⟨ht, hn, h1⟩
    · omega
    · omega
    · omega
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨hT, -⟩
    · exact h
    · rw [hcase.1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₁ : i₁ = i := Subsingleton.elim _ _
  have h₂ : i₂ = i := Subsingleton.elim _ _
  subst h₁ h₂
  subst hAR hAR'
  obtain ⟨hA, hA', hB, hB', h5, h5', hw⟩ := MF2U.reflWit_of_hom hY.odd (D.tag i₂) (D.rank i₂)
    (D.exp i₂) (D.admissible i₂) (D.hom i₂) (D.ker_le_center i₂) hsurj
    ⟨hcase.1, hcase.2.1, by rw [hexp]; exact h1⟩ hR hR' htw hY.conj β hβA hβA' hβ2 hβ1 hβz
  exact ⟨hA, hA', hB, hB', isOm5_of_eq hexp h5, isOm5_of_eq hexp h5', hw⟩

theorem om6ReflWit_proved : Om6ReflWit p f :=
  om6ReflWit_of om6ReflWit_U

end CFSG.ClassicalInvolution.Asc77.CX
