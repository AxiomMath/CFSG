module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Tr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Dt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Tt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Model

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem symCentShapes_sym2 : Nonempty (Sym 2 ≃* Z 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSym : Nat.card (Sym 2) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hZ : Nat.card (Z 2) = 2 := by
    simpa using Nat.card_zmod 2
  exact ⟨mulEquivOfPrimeCardEq hSym hZ⟩

private theorem symCentShapes_perm_zero (X : Type) [Group X] :
    Nonempty ((X × Sym 0) ≃* X) := by
  exact ⟨MulEquiv.prodUnique⟩

private theorem symCentShapes_z2_forall : ∀ ε : Z 2,
    ε = 1 ∨ ε = Multiplicative.ofAdd (1 : ZMod 2) := by
  decide +kernel

private theorem symCentShapes_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have hv : ((-1 : ℤˣ) : ℤ) = ((1 : ℤˣ) : ℤ) := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at hv

private theorem symCentShapes_g_mul_g :
    Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
  decide

theorem symModel_shape_D8 {u : Z 2 × Sym 6} (hu : orderOf u = 2) (hne : u ≠ symZeta)
    (hder : u ∈ _root_.commutator (Z 2 × Sym 6) ∨
      u * symZeta ∈ _root_.commutator (Z 2 × Sym 6)) :
    Nonempty (↥(Subgroup.centralizer ({u} : Set (Z 2 × Sym 6))) ≃* Elem2 2 × DihedralGroup 4) := by
  obtain ⟨ε, σ⟩ := u
  have hu2 : (ε, σ) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (ε, σ)
    rw [hu] at this
    exact this
  have hne_one : (ε, σ) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hσ2 : σ ^ 2 = 1 := by
    simpa using congrArg Prod.snd hu2
  rcases sym6_involution_types hσ2 with hσ1 | ⟨hct, hsign⟩ | ⟨hct, hsign⟩ | ⟨hct, hsign⟩
  · exfalso
    subst hσ1
    rcases symCentShapes_z2_forall ε with hε | hε
    · exact hne_one (by rw [hε]; rfl)
    · exact hne (by simp [symZeta, hε])
  · exfalso
    apply hder.elim
    · intro hmem
      have hd := (symModel_mem_derived_iff (ε, σ)).mp hmem
      exact symCentShapes_neg_one_ne_one (by rw [← hsign]; exact hd.2)
    · intro hmem
      have hd := (symModel_mem_derived_iff ((ε, σ) * symZeta)).mp hmem
      have hsec : ((ε, σ) * symZeta).2 = σ := by simp [symZeta]
      exact symCentShapes_neg_one_ne_one (by rw [← hsign, ← hsec]; exact hd.2)
  · obtain ⟨e1⟩ := symCent_prod ε σ
    obtain ⟨e2⟩ := symCent_dt 2 (σ := σ) hct
    obtain ⟨e3⟩ := symCentShapes_sym2
    obtain ⟨e4⟩ := symCent_elem2 (DihedralGroup 4)
    exact ⟨(e1.trans (MulEquiv.prodCongr (MulEquiv.refl (Z 2))
      (e2.trans (MulEquiv.prodComm.trans
        (MulEquiv.prodCongr e3 (MulEquiv.refl (DihedralGroup 4))))))).trans e4⟩
  · exfalso
    apply hder.elim
    · intro hmem
      have hd := (symModel_mem_derived_iff (ε, σ)).mp hmem
      exact symCentShapes_neg_one_ne_one (by rw [← hsign]; exact hd.2)
    · intro hmem
      have hd := (symModel_mem_derived_iff ((ε, σ) * symZeta)).mp hmem
      have hsec : ((ε, σ) * symZeta).2 = σ := by simp [symZeta]
      exact symCentShapes_neg_one_ne_one (by rw [← hsign, ← hsec]; exact hd.2)

theorem symModel_shape_S4 {u : Z 2 × Sym 6} (hu : orderOf u = 2) (hne : u ≠ symZeta)
    (h1 : u ∉ _root_.commutator (Z 2 × Sym 6))
    (h2 : u * symZeta ∉ _root_.commutator (Z 2 × Sym 6)) :
    Nonempty (↥(Subgroup.centralizer ({u} : Set (Z 2 × Sym 6))) ≃* Elem2 2 × Sym 4) := by
  obtain ⟨ε, σ⟩ := u
  have hu2 : (ε, σ) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (ε, σ)
    rw [hu] at this
    exact this
  have hne_one : (ε, σ) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hσ2 : σ ^ 2 = 1 := by
    simpa using congrArg Prod.snd hu2
  rcases sym6_involution_types hσ2 with hσ1 | ⟨hct, hsign⟩ | ⟨hct, hsign⟩ | ⟨hct, hsign⟩
  · exfalso
    subst hσ1
    rcases symCentShapes_z2_forall ε with hε | hε
    · exact hne_one (by rw [hε]; rfl)
    · exact hne (by simp [symZeta, hε])
  · obtain ⟨e1⟩ := symCent_prod ε σ
    obtain ⟨e2⟩ := symCent_tr 4 (σ := σ) hct
    obtain ⟨e4⟩ := symCent_elem2 (Sym 4)
    exact ⟨(e1.trans (MulEquiv.prodCongr (MulEquiv.refl (Z 2)) e2)).trans e4⟩
  · exfalso
    rcases symCentShapes_z2_forall ε with hε | hε
    · apply h1
      rw [symModel_mem_derived_iff]
      exact ⟨hε, hsign⟩
    · apply h2
      rw [symModel_mem_derived_iff]
      refine ⟨?_, ?_⟩
      · show (ε * Multiplicative.ofAdd (1 : ZMod 2)) = 1
        rw [hε]
        exact symCentShapes_g_mul_g
      · show Equiv.Perm.sign σ = 1
        exact hsign
  · obtain ⟨e1⟩ := symCent_prod ε σ
    obtain ⟨e2⟩ := symCent_tt 0 (σ := σ) hct
    obtain ⟨e3⟩ := symCentShapes_perm_zero (Z 2 × Sym 4)
    obtain ⟨e4⟩ := symCent_elem2 (Sym 4)
    exact ⟨(e1.trans (MulEquiv.prodCongr (MulEquiv.refl (Z 2)) (e2.trans e3))).trans e4⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
