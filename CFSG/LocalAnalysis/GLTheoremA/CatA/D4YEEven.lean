module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YCRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YDArith
public import CFSG.RankThree.PartTwo.Census.Spin.ExcludeDEven
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA TauCeti
open CFSG.RankThree.PartTwo.Census.Spin

@[expose] def isD4pow2 (n : ℕ) : TauCeti.CFSGIndex → Prop := fun i =>
  ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = 2 ∧ q.exponent = n ∧
    i = TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩

theorem exists_isD4pow2 {S : Type} [Group S] (h4 : catalogIs S isD4any) (hn : ¬ catalogIs S S9.isD4two) :
    ∃ n, 2 ≤ n ∧ catalogIs S (isD4pow2 n) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h4
  have hi2 : ¬ S9.isD4two i := fun h => hn ⟨i, h, ⟨e⟩⟩
  obtain ⟨q, hv, hp2, hex, rfl⟩ := exists_D4_of_isD4any_not_two hi hi2
  exact ⟨q.exponent, hex, _, ⟨q, hv, hp2, rfl, rfl⟩, ⟨e⟩⟩

theorem hasE4W_of_even {H : Type} [Group H] {K : Subgroup H} {n : ℕ} (hev : Even n)
    (hn2 : 2 ≤ n) (hK : catalogIs ↥K (isD4pow2 n)) :
    ∃ E W : Subgroup H, E ≤ K ∧ W ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ IsPGroup 2 W ∧
      W ≠ ⊥ ∧ E ≤ Subgroup.normalizer (W : Set H) := by
  obtain ⟨i, ⟨q, hv, hp2, hex, rfl⟩, ⟨e⟩⟩ := hK
  obtain ⟨hchar, hord, -, hrank⟩ := typeD_mk_data 4 q hv
  rw [hp2] at hchar hord
  have hq4 : 4 ≤ (⟨⟨.D 4 q, hv⟩, by simp⟩ : TypeDLieIndex).1.fieldOrder := by
    rw [hord, hex]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hsd : 3 ∣ (⟨⟨.D 4 q, hv⟩, by simp⟩ : TypeDLieIndex).1.fieldOrder - 1 := by
    rw [hord, hex]
    obtain ⟨m, hm⟩ := hev
    rw [hm, ← two_mul, pow_mul]
    have h := dvd_pow_sub_one (a := 2 ^ 2) (m := 3) (by norm_num) (by decide) m
    simpa using h
  have hW := CarrierD.hasWitness_torus _ hchar hq4 Nat.prime_three hsd id id
    (CarrierD.det_full_ne_zero _ hrank Nat.prime_three (by norm_num))
  rw [Fintype.card_fin] at hW
  have hW' : ∃ E P : Subgroup (CFSGIndex.lie ⟨.D 4 q, hv⟩).Group, IsMulCommutative E ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 3 ^ 4 ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧
      E ≤ Subgroup.normalizer (P : Set (CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) := by
    obtain ⟨E, P, hEc, hEp, hEcard, hP, hP2, hEP⟩ := hW
    exact ⟨E, P, hEc, hEp, hEcard.trans (by rw [hrank]), hP, hP2, hEP⟩
  obtain ⟨E, P, hEc, hEp, hEcard', hP, hP2, hEP⟩ := hW'
  let φ : (CFSGIndex.lie ⟨.D 4 q, hv⟩).Group →* ↥K := e.symm.toMonoidHom
  have hφ : Function.Injective φ := e.symm.injective
  let ψ : (CFSGIndex.lie ⟨.D 4 q, hv⟩).Group →* H := K.subtype.comp φ
  have hψ : Function.Injective ψ := K.subtype_injective.comp hφ
  refine ⟨E.map ψ, P.map ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (φ x).2
  · rintro _ ⟨x, hx, rfl⟩
    exact (φ x).2
  · exact CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map ψ ⟨hEc, hEp⟩
  · rw [Subgroup.card_map_of_injective hψ, hEcard']
  · exact hP2.map ψ
  · intro h
    exact hP ((Subgroup.map_eq_bot_iff_of_injective P hψ).1 h)
  · exact (Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map ψ)

end CFSG.LocalAnalysis.GLTheoremA.D4Y
