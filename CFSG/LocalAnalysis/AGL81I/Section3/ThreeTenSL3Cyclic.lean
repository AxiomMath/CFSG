module

public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.CharacterTheory.PSL2Table.Tori
public import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.LocalAnalysis.AGL81I.Section3.SL2Cyclic
public import CFSG.LocalAnalysis.AGL81I.Section3.SL3Arith
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3DLeI
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3MaxParFinal
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.LocalAnalysis.AGL81I.Section3.GammaBasics
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenNormalizer
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenConstrained
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeConclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.AGL81I.Section3

@[expose] def sl2ToSL3Mat (F : Type) [Field F] (g : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 3) (Fin 3) F :=
  !![g 0 0, g 0 1, 0; g 1 0, g 1 1, 0; 0, 0, 1]

theorem det_sl2ToSL3Mat (F : Type) [Field F] (g : Matrix (Fin 2) (Fin 2) F) :
    (sl2ToSL3Mat F g).det = g.det := by
  simp [sl2ToSL3Mat, Matrix.det_fin_three, Matrix.det_fin_two]

theorem sl2ToSL3Mat_mul (F : Type) [Field F] (g h : Matrix (Fin 2) (Fin 2) F) :
    sl2ToSL3Mat F (g * h) = sl2ToSL3Mat F g * sl2ToSL3Mat F h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2ToSL3Mat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem sl2ToSL3Mat_one (F : Type) [Field F] : sl2ToSL3Mat F 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2ToSL3Mat]

@[expose] def sl2ToSL3 (F : Type) [Field F] :
    SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun g := ⟨sl2ToSL3Mat F g.1, by rw [det_sl2ToSL3Mat]; exact g.2⟩
  map_one' := Subtype.ext (sl2ToSL3Mat_one F)
  map_mul' g h := Subtype.ext (sl2ToSL3Mat_mul F g.1 h.1)

theorem sl2ToSL3_injective (F : Type) [Field F] : Function.Injective (sl2ToSL3 F) := by
  intro A B h
  have h' : sl2ToSL3Mat F A.1 = sl2ToSL3Mat F B.1 := congrArg Subtype.val h
  apply Subtype.ext
  ext i j
  have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i.castSucc j.castSucc) h'
  fin_cases i <;> fin_cases j <;> simpa [sl2ToSL3Mat] using h2

theorem dvd_p_add_one_pow_factorization_card_SL3 {p d : ℕ} (hp : p.Prime) (hd : d.Prime)
    (hd2 : d ≠ 2) (hdp : d ≠ p) (hdvd : d ∣ p + 1) :
    d ^ (Nat.card (SpecialLinearGroup (Fin 3) (ZMod p))).factorization d ∣ p + 1 := by
  have hp1 : 1 ≤ p := hp.one_le
  have hd3le : 3 ≤ d := by
    have := hd.two_le
    omega
  have hd_p : ¬ d ∣ p := fun h => hdp ((Nat.prime_dvd_prime_iff_eq hd hp).1 h)
  have hd_p1 : ¬ d ∣ p - 1 := by
    intro h
    have h2 := Nat.dvd_sub hdvd h
    rw [show p + 1 - (p - 1) = 2 by omega] at h2
    have hle := Nat.le_of_dvd (by norm_num) h2
    omega
  have hd_p3 : ¬ d ∣ p ^ 3 - 1 := by
    intro h
    have h3 : d ∣ p ^ 3 + 1 :=
      hdvd.trans ((show Odd 3 by decide).nat_add_dvd_pow_add_pow p 1)
    have hp3 : 1 ≤ p ^ 3 := Nat.succ_le_of_lt (pow_pos hp.pos 3)
    have h2 := Nat.dvd_sub h3 h
    rw [show p ^ 3 + 1 - (p ^ 3 - 1) = 2 by omega] at h2
    have hle := Nat.le_of_dvd (by norm_num) h2
    omega
  have hc0 : Nat.Coprime d p := hd.coprime_iff_not_dvd.mpr hd_p
  have hc1 : Nat.Coprime d (p - 1) := hd.coprime_iff_not_dvd.mpr hd_p1
  have hc2 : Nat.Coprime d (p ^ 3 - 1) := hd.coprime_iff_not_dvd.mpr hd_p3
  have hcA : Nat.Coprime (d ^ (Nat.card (SpecialLinearGroup (Fin 3) (ZMod p))).factorization d)
      (p ^ 3) :=
    Nat.Coprime.pow_right 3 (Nat.Coprime.pow_left _ hc0)
  have hcB : Nat.Coprime (d ^ (Nat.card (SpecialLinearGroup (Fin 3) (ZMod p))).factorization d)
      (p - 1) :=
    Nat.Coprime.pow_left _ hc1
  have hcC : Nat.Coprime (d ^ (Nat.card (SpecialLinearGroup (Fin 3) (ZMod p))).factorization d)
      (p ^ 3 - 1) :=
    Nat.Coprime.pow_left _ hc2
  have hcard : Nat.card (SpecialLinearGroup (Fin 3) (ZMod p)) =
      p ^ 3 * ((p - 1) * ((p ^ 3 - 1) * (p + 1))) := by
    rw [CFSG.GroupTheory.card_SL3_zmod hp]
    have hsq : p ^ 2 - 1 = (p + 1) * (p - 1) := by simpa using Nat.sq_sub_sq p 1
    rw [hsq]
    ring
  have hk : d ^ (Nat.card (SpecialLinearGroup (Fin 3) (ZMod p))).factorization d ∣
      p ^ 3 * ((p - 1) * ((p ^ 3 - 1) * (p + 1))) := by
    rw [← hcard]
    exact Nat.ordProj_dvd _ d
  exact hcC.dvd_of_dvd_mul_left (hcB.dvd_of_dvd_mul_left (hcA.dvd_of_dvd_mul_left hk))

theorem exists_cyclic_card_factorization {p d : ℕ} (hp : p.Prime) (hd : d.Prime) (hd2 : d ≠ 2)
    (hdp : d ≠ p) (hdvd : d ∣ p + 1) :
    ∃ S : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)), IsCyclic ↥S ∧
      Nat.card ↥S = d ^ (Nat.card (SpecialLinearGroup (Fin 3) (ZMod p))).factorization d := by
  have hFactD : Fact d.Prime := ⟨hd⟩
  have hFactP : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  ·
    subst hp2
    have hd3 : d = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
      · exact absurd h (Nat.Prime.ne_one hd)
      · exact h
    subst hd3
    have hcard : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
      rw [CFSG.GroupTheory.card_SL3_zmod (by norm_num : Nat.Prime 2)]
      norm_num
    have ha : (Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2))).factorization 3 = 1 := by
      rw [hcard]
      have h3 : Nat.Prime 3 := by norm_num
      have hge : 1 ≤ (168).factorization 3 :=
        (h3.dvd_iff_one_le_factorization (by norm_num : 168 ≠ 0)).mp (by norm_num : 3 ∣ 168)
      have hle : (168).factorization 3 ≤ 1 := by
        by_contra h
        have h2 : 2 ≤ (168).factorization 3 := by omega
        have := (h3.pow_dvd_iff_le_factorization (by norm_num : 168 ≠ 0)).mpr h2
        norm_num at this
      omega
    obtain ⟨S, hScard⟩ := Sylow.exists_subgroup_card_pow_prime
      (G := SpecialLinearGroup (Fin 3) (ZMod 2)) 3 (n := 1) (by rw [hcard]; norm_num)
    refine ⟨S, ?_, ?_⟩
    · have hFact3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact isCyclic_of_prime_card (by rw [hScard])
    · rw [hScard, ha]
  ·
    have hring : ringChar (ZMod p) ≠ 2 := by
      have hChar : CharP (ZMod p) p := inferInstance
      rw [ringChar.eq (ZMod p) p]
      exact hp2
    obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare (F := ZMod p) hring
    let T : Subgroup (SpecialLinearGroup (Fin 2) (ZMod p)) := CFSG.PSL2Table.nonsplitSL ν
    have hTcyc : IsCyclic ↥T := isCyclic_nonsplitSL hν
    have hTcard : Nat.card ↥T = p + 1 := by
      rw [CFSG.PSL2Table.card_nonsplitSL hring hν, ZMod.card]
    let C : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) := T.map (sl2ToSL3 (ZMod p))
    have hinj := sl2ToSL3_injective (ZMod p)
    have hCcyc : IsCyclic ↥C :=
      (Subgroup.equivMapOfInjective T (sl2ToSL3 (ZMod p)) hinj).isCyclic.mp hTcyc
    have hCcard : Nat.card ↥C = p + 1 := by
      rw [← hTcard]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective T (sl2ToSL3 (ZMod p)) hinj).toEquiv.symm
    have hdvd_a : d ^ (Nat.card (SpecialLinearGroup (Fin 3) (ZMod p))).factorization d ∣
        Nat.card ↥C := by
      rw [hCcard]
      exact dvd_p_add_one_pow_factorization_card_SL3 hp hd hd2 hdp hdvd
    obtain ⟨S₀, hS₀card⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) d
      (n := (Nat.card (SpecialLinearGroup (Fin 3) (ZMod p))).factorization d) hdvd_a
    have hCyclicC : IsCyclic ↥C := hCcyc
    have hS₀cyc : IsCyclic ↥S₀ := inferInstance
    refine ⟨S₀.map C.subtype, ?_, ?_⟩
    · exact (Subgroup.equivMapOfInjective S₀ C.subtype C.subtype_injective).isCyclic.mp hS₀cyc
    · rw [Subgroup.card_map_of_injective C.subtype_injective, hS₀card]

theorem isCyclic_of_isSylow_dvd_p_add_one_of_prime_ne_two {H : Type} [Group H] [Finite H]
    {I D : Subgroup H} {p d : ℕ} (hp : p.Prime) (hd : d.Prime) (hd2 : d ≠ 2)
    (hdp : d ≠ p) (hdvd : d ∣ p + 1)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (hD : CFSG.ABGLocalTools.IsSylowOf d D I) : IsCyclic ↥D := by
  classical
  have hFactD : Fact d.Prime := ⟨hd⟩
  have hFactP : Fact p.Prime := ⟨hp⟩
  have hDle : D ≤ I := hD.le
  let A : Subgroup ↥I := D.subgroupOf I
  let P : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) := A.map e.toMonoidHom
  have hAe : ↥A ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDle
  have hPe : ↥A ≃* ↥P := Subgroup.equivMapOfInjective A e.toMonoidHom e.injective
  have hPcard : Nat.card ↥P =
      d ^ (Nat.card (SpecialLinearGroup (Fin 3) (ZMod p))).factorization d := by
    have h1 : Nat.card ↥P = Nat.card ↥A := Nat.card_congr hPe.toEquiv.symm
    have h2 : Nat.card ↥A = Nat.card ↥D := Nat.card_congr hAe.toEquiv
    have h3 : Nat.card ↥I = Nat.card (SpecialLinearGroup (Fin 3) (ZMod p)) :=
      Nat.card_congr e.toEquiv
    rw [h1, h2, hD.card_eq, h3]
  obtain ⟨S, hScyc, hScard⟩ := exists_cyclic_card_factorization hp hd hd2 hdp hdvd
  have hPcyc : IsCyclic ↥P := by
    have h := (Sylow.equiv (Sylow.ofCard S hScard) (Sylow.ofCard P hPcard)).isCyclic.mp hScyc
    rwa [Sylow.coe_ofCard P hPcard] at h
  exact hAe.isCyclic.mp (hPe.isCyclic.mpr hPcyc)

end CFSG.LocalAnalysis.AGL81I.Section3
