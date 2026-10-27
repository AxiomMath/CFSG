module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUClJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClLin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClU

public section

namespace CFSG.ComponentClassification.GSThmB.QPUJ6Cl

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (innerDiagonalAction)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormP primeFormConjHom
  mem_gramSU_iff_unitary)

theorem card_mul_of_lieModel_psl_four {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (h : LieModel X .PSL 4 p f) :
    Nat.card X * Nat.gcd 4 (p ^ f - 1) =
      (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) * ((p ^ f) ^ 3 - 1) := by
  obtain ⟨hc, -⟩ := CatLeafProof.X10Lin.lieOrder_of_lieModel_classical (Or.inl rfl) hp2
    (by norm_num) h
  have hc' : Nat.card X * Nat.gcd 4 (p ^ f - 1) =
      (p ^ f) ^ (4 * (4 - 1) / 2) * ∏ i ∈ Finset.Icc 2 4, ((p ^ f) ^ i - 1) := hc
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide), show 4 * (4 - 1) / 2 = 6 from rfl] at hc'
  rw [hc']
  ring

theorem card_mul_of_lieModel_psu_four {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (h : LieModel X .PSU 4 p f) :
    Nat.card X * Nat.gcd 4 (p ^ f + 1) =
      (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) * ((p ^ f) ^ 3 + 1) := by
  obtain ⟨hc, -⟩ := CatLeafProof.X10Lin.lieOrder_of_lieModel_classical (Or.inr (Or.inl rfl))
    hp2 (by norm_num) h
  have hc' : Nat.card X * Nat.gcd 4 (p ^ f + 1) =
      (p ^ f) ^ (4 * (4 - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 4, (if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1) := hc
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide), show 4 * (4 - 1) / 2 = 6 from rfl] at hc'
  simp only [show Even 2 from ⟨1, rfl⟩, show ¬ Even 3 by decide, show Even 4 from ⟨2, rfl⟩,
    ↓reduceIte] at hc'
  rw [hc']
  ring

theorem gcd_four_of_mod {m : ℕ} :
    (m % 4 = 0 → Nat.gcd 4 m = 4) ∧ (m % 4 = 2 → Nat.gcd 4 m = 2) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Nat.gcd_rec, h]
    rfl
  · rw [Nat.gcd_rec, h]
    rfl

theorem false_of_lt_of_isL4U4Mod4 {P : Type} [Group P] [Finite P] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hP : LieModel P .PSL 4 p f ∨ LieModel P .PSU 4 p f)
    {L : Subgroup P} (hL : L ≠ ⊤) (hLm : IsL4U4Mod4 (↥L ⧸ pPrimeCore 2 ↥L) p f) : False := by
  have hlt : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) < Nat.card P :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))
      (lt_of_le_of_ne (Subgroup.card_le_card_group L)
        fun h1 => hL ((Subgroup.card_eq_iff_eq_top L).1 h1))
  have hq3 : 3 ≤ p ^ f := (show 3 ≤ p by have := hp.two_le; omega).trans
    (Nat.le_self_pow (by omega) p)
  have hq27 : 27 ≤ (p ^ f) ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq3 3
  obtain ⟨A, hA⟩ : ∃ A, A = (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := ⟨_, rfl⟩
  have hcL := gcd_four_of_mod (m := p ^ f - 1)
  have hcU := gcd_four_of_mod (m := p ^ f + 1)
  rcases hP with hP | hP <;> rcases hLm with ⟨hLm, hq⟩ | ⟨hLm, hq⟩
  ·
    have h1 := card_mul_of_lieModel_psl_four hp2 hP
    have h2 := card_mul_of_lieModel_psl_four hp2 hLm
    have hg : 0 < Nat.gcd 4 (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have : Nat.card P = Nat.card (↥L ⧸ pPrimeCore 2 ↥L) :=
      Nat.eq_of_mul_eq_mul_right hg (h1.trans h2.symm)
    omega
  ·
    have h1 := card_mul_of_lieModel_psl_four hp2 hP
    have h2 := card_mul_of_lieModel_psu_four hp2 hLm
    rw [hcL.1 (by omega), ← hA] at h1
    rw [hcU.2 (by omega), ← hA] at h2
    have hle : A * ((p ^ f) ^ 3 - 1) ≤ A * ((p ^ f) ^ 3 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  ·
    have h1 := card_mul_of_lieModel_psu_four hp2 hP
    have h2 := card_mul_of_lieModel_psl_four hp2 hLm
    rw [hcU.1 (by omega), ← hA] at h1
    rw [hcL.2 (by omega), ← hA] at h2
    have hle : A * ((p ^ f) ^ 3 + 1) ≤ A * (((p ^ f) ^ 3 - 1) * 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmul : A * (((p ^ f) ^ 3 - 1) * 2) = A * ((p ^ f) ^ 3 - 1) * 2 := by ring
    omega
  ·
    have h1 := card_mul_of_lieModel_psu_four hp2 hP
    have h2 := card_mul_of_lieModel_psu_four hp2 hLm
    have hg : 0 < Nat.gcd 4 (p ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have : Nat.card P = Nat.card (↥L ⧸ pPrimeCore 2 ↥L) :=
      Nat.eq_of_mul_eq_mul_right hg (h1.trans h2.symm)
    omega

theorem false_of_barConfig6_psl {P : Type} [Group P] [Finite P] {n p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hP : StatedClassicalModel P .PSL n p f₀) (h : BarConfig6 P p f) : False := by
  have hadm : StatedLieAdmissible .PSL n p f₀ := hP.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hLM : LieModel P .PSL n p f₀ := Or.inl ⟨by decide, hP⟩
  have : IsSimpleGroup P := (LieType.Simplicity.fam_PSL_simplicity P n p f₀ hP).2
  obtain ⟨E, L, t, J, J₀, hd⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hLM
  have : Finite (ProjectiveSpecialLinearGroup (Fin n) K) := Finite.of_equiv _ e.toEquiv
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin n) K) := e.symm.isSimpleGroup
  have hd' := hd.map e
  have hQ : FixedTwoComponentsQuasisimple (ProjectiveSpecialLinearGroup (Fin n) K) :=
    FixedTwoComponentsQuasisimple.of_mulEquiv e.symm
      (CatLeafProof.X10Lin.fixedTwoComponentsQuasisimple_lin hp2 (Or.inl rfl) hadm hLM)
  obtain ⟨B, hB⟩ := QuotientGroup.mk'_surjective (center (SpecialLinearGroup (Fin n) K)) (e t)
  obtain ⟨hA, J', hJ'c, hJ'z, hJ'm⟩ := exists_component_of_J hQ (center_eq_bot_of_barData6 hd')
    hd'.ht2 hd'.ht1 hd'.hJt hd'.hJc hd'.hJm (innerDiagonalAction n K (SpecialLinearGroup.toGL B))
    (fun x => by rw [QPUCl.innerDiagonalAction_toGL_apply, hB])
  rcases CatLeafProof.X10Lin.inner_psl_component_cases hp hp2 hK hadm _ hA hJ'c with
    ⟨z, hz, hzc, hzz, hz1⟩ | ⟨t', k, e', hT, hcm⟩
  · exact hz1 (hJ'z z hz hzc hzz)
  · rcases hT with ⟨k', -, hk3, -, hk⟩ | ⟨⟨r, hr⟩, hk⟩
    ·
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      obtain ⟨-, hk2, -⟩ :=
        QPUCl.eq_of_centralModel_of_lieModel hp hp2 (by omega) hJ'm (Or.inl rfl) hcm
      omega
    ·
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      obtain ⟨-, hk2, he⟩ :=
        QPUCl.eq_of_centralModel_of_lieModel hp hp2 (by omega) hJ'm (Or.inl rfl) hcm
      obtain rfl : n = 4 := by omega
      obtain rfl : f₀ = f := by omega
      exact false_of_lt_of_isL4U4Mod4 hp hp2 hf (Or.inl hLM) hd.hLtop hd.hLm

theorem false_of_barConfig6_psu {P : Type} [Group P] [Finite P] {n p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hP : StatedClassicalModel P .PSU n p f₀) (h : BarConfig6 P p f) : False := by
  have hadm : StatedLieAdmissible .PSU n p f₀ := hP.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hLM : LieModel P .PSU n p f₀ := Or.inl ⟨by decide, hP⟩
  have : IsSimpleGroup P := (ClassicalGroups.Unitary.fam_PSU_simplicity P n p f₀ hP).2
  obtain ⟨E, L, t, J, J₀, hd⟩ := h
  obtain ⟨K, _, hU, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hLM
  have : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv _ e.toEquiv
  have : IsSimpleGroup (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    e.symm.isSimpleGroup
  have hd' := hd.map e
  have hQ : FixedTwoComponentsQuasisimple
      (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    FixedTwoComponentsQuasisimple.of_mulEquiv e.symm
      (CatLeafProof.X10Lin.fixedTwoComponentsQuasisimple_lin hp2 (Or.inr rfl) hadm hLM)
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e t)
  obtain ⟨hA, J', hJ'c, hJ'z, hJ'm⟩ := exists_component_of_J hQ (center_eq_bot_of_barData6 hd')
    hd'.ht2 hd'.ht1 hd'.hJt hd'.hJc hd'.hJm _
    (fun x => by rw [QPUCl.primeFormConjHom_gramSU_apply hU g x, hg])
  rcases CatLeafProof.X10Lin.inner_psu_component_cases hU hp2 hadm _ hA hJ'c with
    ⟨z, hz, hzc, hzz, hz1⟩ | ⟨t', k, e', hT, hcm⟩
  · exact hz1 (hJ'z z hz hzc hzz)
  · rcases hT with ⟨k', hk3, -, hk⟩ | ⟨⟨r, hr⟩, hk⟩
    ·
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      obtain ⟨ht, -, -⟩ :=
        QPUCl.eq_of_centralModel_of_lieModel hp hp2 (by omega) hJ'm (Or.inr (Or.inl rfl)) hcm
      exact absurd ht (by decide)
    ·
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      obtain ⟨-, hk2, he⟩ :=
        QPUCl.eq_of_centralModel_of_lieModel hp hp2 (by omega) hJ'm (Or.inl rfl) hcm
      obtain rfl : n = 4 := by omega
      obtain rfl : f₀ = f := by omega
      exact false_of_lt_of_isL4U4Mod4 hp hp2 hf (Or.inr hLM) hd.hLtop hd.hLm

end CFSG.ComponentClassification.GSThmB.QPUJ6Cl
