module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMFin
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YOFin
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X10
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped MatrixGroups

section Abstract

variable {M : Type} [Group M]

theorem nonsolvable_of_simple_center (hs : IsSimpleGroup M) (hcen : Subgroup.center M = ⊥) {z : M}
    (hz : z ≠ 1) : ¬ Group.IsSolvable M := by
  intro hsol
  haveI := hs
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsol
  apply hz
  have : z ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact hcomm g z
  rwa [hcen, Subgroup.mem_bot] at this

theorem secFacts_of_fixTwo {P : Subgroup (MulAut M)} {zs : M} (hz2 : zs * zs = 1)
    (hcen : Subgroup.center M = ⊥) (hns : ¬ Group.IsSolvable M)
    (hfix : ∀ β ∈ P, β = 1 ∨ β = MulAut.conj zs) : SecFacts P zs := by
  classical
  have hcc : MulAut.conj zs * MulAut.conj zs = 1 := by rw [← map_mul, hz2, map_one]
  refine ⟨hcen, fun β hβ => ?_, ?_, fun β hβ h1 h2 => ?_, ?_⟩
  · rcases hfix β hβ with rfl | rfl
    · exact mul_one 1
    · exact hcc
  · have hinj : Function.Injective
        (fun β : P => if (β : MulAut M) = 1 then (0 : Fin 2) else 1) := by
      intro β₁ β₂ h
      apply Subtype.ext
      by_cases h₁ : (β₁ : MulAut M) = 1 <;> by_cases h₂ : (β₂ : MulAut M) = 1 <;>
        simp only [h₁, h₂, ↓reduceIte] at h
      · rw [h₁, h₂]
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · rw [(hfix β₁ β₁.2).resolve_left h₁, (hfix β₂ β₂.2).resolve_left h₂]
    have h2 : Nat.card P ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_fin] at h2
    omega
  · rcases hfix β hβ with h | h
    · exact absurd h h1
    · exact absurd h h2
  · intro L hLP hc hsol
    have hL1 : ∀ β ∈ L, β = 1 := fun β hβ =>
      (hfix β (hLP hβ)).resolve_right fun h => hc (h ▸ hβ)
    have hsurj : Function.Surjective (fixOf L).subtype := fun x =>
      ⟨⟨x, fun β hβ => by rw [hL1 β hβ]; rfl⟩, rfl⟩
    haveI := hsol
    exact hns (solvable_of_surjective hsurj)

theorem eq_bot_or_zpowers_of_card [Finite M] {P L : Subgroup M} (hP2 : IsPGroup 2 P) (hPc : Nat.card P ≤ 4)
    (hLP : L ≤ P) {c : M} (hcP : c ∈ P) (hcL : c ∉ L) :
    L = ⊥ ∨ ∃ β ∈ L, β ≠ 1 ∧ β * β = 1 ∧ L = Subgroup.zpowers β := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : IsPGroup 2 L := hP2.to_le hLP
  obtain ⟨n, hn⟩ := hL2.exists_card_eq
  have hlt : Nat.card L < Nat.card P := by
    by_contra hge
    push Not at hge
    have := Subgroup.eq_of_le_of_card_ge hLP hge
    exact hcL (this ▸ hcP)
  have hn1 : n ≤ 1 := by
    by_contra h
    push Not at h
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · left
    have : n = 0 := by omega
    subst this
    exact Subgroup.eq_bot_of_card_eq L (by simpa using hn)
  · right
    have hn1' : n = 1 := le_antisymm hn1 h1
    subst hn1'
    have hL2' : Nat.card L = 2 := by simpa using hn
    obtain ⟨β, hβL, hβ1⟩ : ∃ β ∈ L, β ≠ 1 := by
      by_contra hno
      push Not at hno
      have : L = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.mpr (hno x hx)
      rw [this, Subgroup.card_bot] at hL2'
      omega
    have hord : orderOf β ∣ 2 := by
      rw [← hL2']
      have := orderOf_dvd_natCard (⟨β, hβL⟩ : L)
      rwa [Subgroup.orderOf_mk] at this
    have hord2 : orderOf β = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hβ1
      · exact h
    have hsq : β * β = 1 := by
      have := pow_orderOf_eq_one β
      rwa [hord2, pow_two] at this
    refine ⟨β, hβL, hβ1, hsq, ?_⟩
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hβL) ?_).symm
    rw [Nat.card_zpowers, hord2, hL2']

end Abstract


section Models

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

theorem isSimpleGroup_of_hom_psl4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type} [Group Y]
    (t : StatedLieTag) (k e : ℕ) (hadm : StatedLieAdmissible t k p e)
    (ψ : (Generic.modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (hcase : t = .PSL ∧ k = 4 ∧ ¬ p ^ e % 4 = 1)
    {R R' : Subgroup (Generic.modelUniv t k p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') : IsSimpleGroup Y := by
  have he : 1 ≤ e := hadm.2.1
  have hodd : p ^ e % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  obtain ⟨rfl, rfl, h4⟩ := hcase
  have h2 : (2 : GaloisField p e) ≠ 0 := C25W.two_ne_zero_gf (p := p) e hp2
  have hsq : ¬ IsSquare (-1 : GaloisField p e) := by
    have : Fintype (GaloisField p e) := Fintype.ofFinite _
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card,
      GaloisField.card p e (by omega)]
    omega
  obtain ⟨i, hi⟩ := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) hR
  obtain ⟨i', hi'⟩ := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) hR'
  have hRR : R ≠ R' := fun h => hne (by rw [h])
  have hk := CFSG.ClassicalInvolution.Asc77.CX.CX4.L4.ker_eq_scalars h2 hsq ψ hker hi hi' hRR hz hz'
  haveI : IsSimpleGroup (projectiveSL 4 (GaloisField p e)) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isSimpleGroup_projectiveSL (K := GaloisField p e) (n := 4)
      (by norm_num)
  let ψ' : Matrix.SpecialLinearGroup (Fin 4) (GaloisField p e) →* Y := ψ
  have hk' : ψ'.ker = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 4 (GaloisField p e) := hk
  let e' : projectiveSL 4 (GaloisField p e) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hk'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ' hsurj)
  exact e'.symm.isSimpleGroup

theorem isSimpleGroup_of_om6mData {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}
    {A A' : Subgroup Y} {z' a₀ b₀ : Y}
    (h : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Om6mData Y Φ A A' z' a₀ b₀) : IsSimpleGroup Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨D, hD1, i, hi⟩, htw, -⟩ := h
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : ∀ j : Fin D.card, Function.Surjective (D.hom j) := by
    intro j
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom j).range := by
      intro l
      rw [Subsingleton.elim l j]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : ∀ j : Fin D.card, D.tag j = .PSL ∧ D.rank j = 4 := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨h5, -⟩ | ⟨-, hε, ht, hn⟩ | ⟨-, hε, ht, hn⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · omega
    · exact ⟨ht, hn⟩
    · exfalso
      simp only [piSign, Bool.not_eq_false', decide_eq_true_eq] at hε
      norm_num at hε
    · omega
    · omega
    · omega
  have hexp : ∀ j : Fin D.card, D.exp j = 1 := by
    intro j
    rcases D.exp_eq j with h | ⟨hT, -⟩
    · exact h
    · rw [(hcase j).1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  have h4 : ¬ 3 ^ D.exp i₂ % 4 = 1 := by
    rw [hexp i₂]
    norm_num
  exact isSimpleGroup_of_hom_psl4 (p := 3) (by norm_num) (D.tag i₂) (D.rank i₂) (D.exp i₂)
    (D.admissible i₂) (D.hom i₂) (D.ker_le_center i₂) (hsurj i₂)
    ⟨(hcase i₂).1, (hcase i₂).2, h4⟩ hR hR' hne hz hz'

theorem mem_fixOf_zpowers {M : Type} [Group M] {β : MulAut M} {x : M} (hx : β x = x) :
    x ∈ fixOf (Subgroup.zpowers β) := by
  intro γ hγ
  have hle : Subgroup.zpowers β ≤ MulAction.stabilizer (MulAut M) x :=
    Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hx)
  exact MulAction.mem_stabilizer_iff.mp (hle hγ)

theorem secFacts_five {Xs : Type} [Group Xs] [Finite Xs] {Φ : Set (Subgroup Xs)}
    (D : LieSystemData 3 1 Xs Φ) {A A' : Subgroup Xs} {z' a₀ b₀ : Xs} (hD1 : D.card = 1)
    (hi : ∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i))
    (htw : TwinSect0 Φ A A' z' a₀ b₀) (hconj : ∀ J ∈ Φ, ∀ y : Xs, conjSub y J ∈ Φ)
    {P : Subgroup (MulAut Xs)} (hPfix : ∀ β ∈ P, (∀ y ∈ A, β y = y) ∧ ∀ y ∈ A', β y = y) :
    SecFacts P z' ∧ ∀ β ∈ P, β = 1 ∨ β = MulAut.conj z' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLT := CFSG.ClassicalInvolution.Q3.Q3T7P25.layerTwinFactsFive3_proved D hD1 hi htw
  have hfix : ∀ β ∈ P, β = 1 ∨ β = MulAut.conj z' := by
    intro β hβ
    rcases CFSG.ClassicalInvolution.Q3.Q3T7P25.cent5Three_proved Xs Φ D A A' z' a₀ b₀ hD1 hi htw β
      (hPfix β hβ).1 (hPfix β hβ).2 with h | h
    · exact Or.inl h
    · right
      ext y
      rw [MulAut.conj_apply]
      exact h y
  have hsimple : IsSimpleGroup Xs :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.isSimpleGroup_of_om5Data
      (⟨⟨D, hD1, hi⟩, htw, hconj⟩ : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C5O.Om5Data Xs Φ A A' z' a₀ b₀)
  have hns := nonsolvable_of_simple_center hsimple hLT.1 htw.hzA.ne_one
  exact ⟨secFacts_of_fixTwo htw.hzA.sq hLT.1 hns hfix, hfix⟩

theorem secFacts_six {Xs : Type} [Group Xs] [Finite Xs] {Φ : Set (Subgroup Xs)}
    (D : LieSystemData 3 1 Xs Φ) {A A' : Subgroup Xs} {z' a₀ b₀ : Xs} (hD1 : D.card = 1)
    (hi : ∃ i : Fin D.card, IsOrthTag 6 (!piSign 3 1) (D.tag i) (D.rank i))
    (htw : TwinSect0 Φ A A' z' a₀ b₀) (hconj : ∀ J ∈ Φ, ∀ y : Xs, conjSub y J ∈ Φ)
    {P : Subgroup (MulAut Xs)} (hP2 : IsPGroup 2 P) (hcz : MulAut.conj z' ∈ P)
    (hPfix : ∀ β ∈ P, (∀ y ∈ A, β y = y) ∧ ∀ y ∈ A', β y = y)
    (eA : A ≃* SL(2, ZMod 3)) : SecFacts P z' := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLT := CFSG.ClassicalInvolution.Asc77.CX.layer6Twin_proved 3 1 Xs Φ D A A' z' a₀ b₀ hD1 hi htw
  obtain ⟨hcen, -, -, hP, hrefl⟩ := hLT
  obtain ⟨hexp, hcard⟩ := hP P hP2 hPfix
  have hOm6 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Om6mData Xs Φ A A' z' a₀ b₀ :=
    ⟨⟨D, hD1, hi⟩, htw, hconj⟩
  have hsimple := isSimpleGroup_of_om6mData hOm6
  have hns := nonsolvable_of_simple_center hsimple hcen htw.hzA.ne_one
  refine ⟨hcen, hexp, hcard, fun β hβ h1 h2 =>
    hrefl β (hPfix β hβ).1 (hPfix β hβ).2 (hexp β hβ) h1 h2, ?_⟩
  intro L hLP hc hsol
  rcases eq_bot_or_zpowers_of_card hP2 hcard hLP hcz hc with hL | ⟨β, hβL, hβ1, hβ2, hLβ⟩
  ·
    have hL1 : ∀ γ ∈ L, γ = 1 := fun γ hγ => by
      rw [hL, Subgroup.mem_bot] at hγ
      exact hγ
    have hsurj : Function.Surjective (fixOf L).subtype := fun x =>
      ⟨⟨x, fun γ hγ => by rw [hL1 γ hγ]; rfl⟩, rfl⟩
    haveI := hsol
    exact hns (solvable_of_surjective hsurj)
  ·
    have hβP : β ∈ P := hLP hβL
    have hβz : β ≠ MulAut.conj z' := fun h => hc (h ▸ hβL)
    obtain ⟨hA₁, hA₁', -, -, ⟨Φ₂, z₂, a₂, b₂, hd⟩, -, -⟩ :=
      CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.om6ReflDiag_proved Xs Φ A A' z' a₀ b₀ hOm6 β
        (hPfix β hβP).1 (hPfix β hβP).2 hβ2 hβ1 hβz
    have hTs : IsSimpleGroup ↥(Goldschmidt75.perfRes (CFSG.ClassicalInvolution.Asc77.CX.fixSubgroup β)) :=
      CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.isSimpleGroup_of_om5Data hd
    have hnc : ¬ ∀ a b : ↥(Goldschmidt75.perfRes (CFSG.ClassicalInvolution.Asc77.CX.fixSubgroup β)),
        a * b = b * a := by
      intro hcomm
      apply CFSG.ClassicalInvolution.Q3.sl2Three_not_comm (fun a b => ?_)
      have := hcomm ⟨(eA.symm a : A), hA₁ (eA.symm a).2⟩ ⟨(eA.symm b : A), hA₁ (eA.symm b).2⟩
      have h2 : eA.symm (a * b) = eA.symm (b * a) := by
        rw [map_mul, map_mul]
        apply Subtype.ext
        have := congrArg (fun t : ↥(Goldschmidt75.perfRes (CFSG.ClassicalInvolution.Asc77.CX.fixSubgroup β)) =>
          (t : Xs)) this
        simpa using this
      exact eA.symm.injective h2
    have hTns : ¬ Group.IsSolvable ↥(Goldschmidt75.perfRes (CFSG.ClassicalInvolution.Asc77.CX.fixSubgroup β)) := by
      intro hsolT
      haveI := hTs
      exact hnc (IsSimpleGroup.comm_iff_isSolvable.mpr hsolT)
    apply hTns
    have hTfix : ∀ x ∈ Goldschmidt75.perfRes (CFSG.ClassicalInvolution.Asc77.CX.fixSubgroup β),
        x ∈ fixOf L := by
      intro x hx
      rw [hLβ]
      exact mem_fixOf_zpowers (Goldschmidt75.perfRes_le _ hx)
    let f : ↥(Goldschmidt75.perfRes (CFSG.ClassicalInvolution.Asc77.CX.fixSubgroup β)) →* ↥(fixOf L) :=
      (Subgroup.subtype _).codRestrict (fixOf L) fun x => hTfix x x.2
    haveI := hsol
    refine solvable_of_solvable_injective (f := f) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun t : ↥(fixOf L) => (t : Xs)) hxy)

end Models

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
