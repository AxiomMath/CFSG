module

public import CFSG.ClassicalInvolution.Q3.TL4ConnBendU3
public import CFSG.ClassicalInvolution.Q3.TL4ConnBendSz
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.GH74.Bender.Suzuki
public import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Bend

open CFSG.BenderSuzuki CFSG.BenderSuzuki.External CFSG.BenderSuzuki.MatrixGroups
  CFSG.Blueprint CFSG.LieType.Ree

theorem suzuki_bigCommT_sylow {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ Q : Sylow 2 (suzukiGroup a K), BigCommT ↥(Q : Subgroup (suzukiGroup a K)) := by
  have := finite_suzukiGroup hK
  refine bigCommT_sylow_of_one (Sylow.ofCard (suzukiU a K) (RankThree.card_suzukiU_eq hK)) ?_
  intro x z hxz y
  have h := suzukiU_bigComm ha hK x.2 (z : suzukiGroup a K) fun y' hy' => by
    rcases hxz ⟨y', hy'⟩ with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val h1)
  exact Subtype.ext (h y y.2)

theorem root_eq_range {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (coordR : hermitianUnipotentCoord J ≃ R)
    (hcoord : ∀ z : hermitianUnipotentCoord J, ∃ M : GL (Fin 3) E,
      (M : Matrix (Fin 3) (Fin 3) E) = !![1, (z : E × E).1, (z : E × E).2;
        0, 1, -J.conj (z : E × E).1; 0, 0, 1] ∧
      ((((coordR z : R) : ProjectiveSpecialUnitaryMatrixGroup J) :
        Matrix.ProjGenLinGroup (Fin 3) E)) = Matrix.ProjGenLinGroup.mk M) :
    R = (hermitianUnipotentPSU J hJ).range ∧ Function.Injective (hermitianUnipotentPSU J hJ) := by
  have hψ : ∀ z, ((coordR z : R) : ProjectiveSpecialUnitaryMatrixGroup J) =
      hermitianUnipotentPSU J hJ z := by
    intro z
    obtain ⟨M, hM, hMval⟩ := hcoord z
    apply Subtype.ext
    rw [hMval, hermitianUnipotentPSU_val]
    congr 1
    exact Matrix.GeneralLinearGroup.ext fun i j => by rw [hM]; rfl
  refine ⟨?_, fun z w hzw => ?_⟩
  · ext g
    constructor
    · intro hg
      obtain ⟨z, hz⟩ := coordR.surjective ⟨g, hg⟩
      exact ⟨z, by rw [← hψ, hz]⟩
    · rintro ⟨z, rfl⟩
      rw [← hψ]
      exact (coordR z).2
  · apply coordR.injective
    apply Subtype.ext
    rw [hψ, hψ, hzw]

theorem psu_bigCommT_sylow {E : Type} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (f : ℕ) (hf : 2 ≤ f) (hKcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∀ Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      BigCommT ↥(Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  set G := ProjectiveSpecialUnitaryMatrixGroup J
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite G :=
    Finite.of_injective (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) E)) Subtype.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases External.huppert_II_10_12 J (2 ^ f) hKcard hfixed hJ with
    ⟨-, -, -, -, -, -, ⟨R, -, -, -, -, -, -, -, hRcard, -, -, -, -, ⟨coordR, hcoord⟩, -, -⟩, -, -,
      -⟩
  obtain ⟨hR, hinj⟩ := root_eq_range J hJ R coordR hcoord
  have hRp : IsPGroup 2 ↥R := IsPGroup.of_card (n := f * 3) (by rw [hRcard, ← pow_mul])
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  have hB := CFSG.Open.bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ
  have hPcard : Nat.card (P : Subgroup G) = (2 ^ f) ^ 3 := (hB P).2.2.2.2
  have hRPeq : R = (P : Subgroup G) := Subgroup.eq_of_le_of_card_ge hRP (by rw [hPcard, hRcard])
  refine bigCommT_sylow_of_one P ?_
  rw [← hRPeq, hR]
  have hq : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact BigCommT.of_mulEquiv (MonoidHom.ofInjective hinj).symm
    (coord_bigComm J hKcard hfixed hq)

theorem bigCommT_sylow_of_isBenderGroup {F : Type} [Group F] [Finite F] (hB : IsBenderGroup F) :
    ∀ Q : Sylow 2 F, BigCommT ↥(Q : Subgroup F) := by
  rcases hB with ⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩
  · intro Q
    exact BigCommT.of_commute fun x y =>
      Subtype.ext (Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_psl2 hn e Q x x.2 y y.2)
  · obtain ⟨-, a', ha', K, _, _, hfa, hK, ⟨e'⟩⟩ := CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz ha
      (e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz a)))
    have hK' : Nat.card K = 2 ^ (2 * a' + 1) := hfa ▸ hK
    have := finite_suzukiGroup hK'
    exact bigCommT_sylow_of_mulEquiv e' (suzuki_bigCommT_sylow ha' hK')
  · let k := GaloisField 2 n
    let E := FiniteField.Extension k 2 2
    let J := binaryQuadraticHermitian n (by omega)
    have : CharP E 2 := CharP.of_ringHom_of_ne_zero (algebraMap k E) 2 (by norm_num)
    have hEcard : Nat.card E = (2 ^ n) ^ 2 := by
      rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
    have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
      quadraticBinaryFrobenius_fixed_card n (by omega)
    have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
    obtain ⟨e'⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hEcard hfixed
    have : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_injective (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
        (x : Matrix.ProjGenLinGroup (Fin 3) E)) Subtype.coe_injective
    exact bigCommT_sylow_of_mulEquiv (e.trans e'.symm)
      (psu_bigCommT_sylow J n hn hEcard hfixed hJ)

end CFSG.ClassicalInvolution.Q3.TL4.Bend
