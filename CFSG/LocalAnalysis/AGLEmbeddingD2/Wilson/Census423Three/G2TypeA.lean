module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.Dichotomy
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.HighestRoot CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.Sec11
open scoped MatrixGroups

theorem exp_three_of_center {X : Type} [Group X] (C : Subgroup X) {S : Type} [Group S] [Finite S]
    (e : ↥C ≃* S) (h : Nat.card (Subgroup.center S) ∣ 3) :
    ∀ g ∈ C, (∀ c ∈ C, g * c = c * g) → g ^ 3 = 1 := by
  intro g hg hgc
  have hmem : e ⟨g, hg⟩ ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have := hgc (e.symm s : X) (e.symm s).2
    have h1 : (e.symm s) * ⟨g, hg⟩ = ⟨g, hg⟩ * (e.symm s) := Subtype.ext this.symm
    have h2 := congrArg e h1
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2
  have h1 : orderOf (⟨e ⟨g, hg⟩, hmem⟩ : Subgroup.center S) ∣ Nat.card (Subgroup.center S) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (e ⟨g, hg⟩) ∣ 3 := by
    rw [← Subgroup.orderOf_coe (⟨e ⟨g, hg⟩, hmem⟩ : Subgroup.center S)] at h1
    exact h1.trans h
  have h3 : (e ⟨g, hg⟩) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h2
  have h4 : (⟨g, hg⟩ : ↥C) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, h3, map_one]
  exact congrArg Subtype.val h4

section Cent


theorem threeA_of_minus {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ 1) (h3 : 3 ∣ Nat.card K + 1) (hK4 : 4 ≤ Nat.card K)
    {z : adjointGroup .G2 K} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : ThreeA z := by
  refine ⟨KS11Lie7Proof.isQuasisimple_centralizer_threeA h3 hK4 hzS hz3 hz1, ?_⟩
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := KS11Lie4Proof.exists_quadratic_ext' K
  have : Fintype K := Fintype.ofFinite K
  have hp : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have : CharP L p :=
    charP_of_injective_algebraMap (algebraMap K L).injective p
  obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU hK h3 hdeg hzS hz3 hz1
  have hL : Nat.card L = (p ^ 1) ^ 2 := by rw [KS11Lie4Proof.natCard_quadratic hdeg, hK]
  have h3' : 3 ∣ p ^ 1 + 1 := by rwa [hK] at h3
  have hc := CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSU_three hL h3'
  exact exp_three_of_center _ e (by rw [hc])

theorem centralizer_diag_eq_range {K : Type} [Field K] [Finite K] {t : Kˣ} (ht : orderOf t = 3)
    {d : adjointGroup .G2 K}
    (hd : (d : ModGL .G2 K) = rootDiagUnit .G2 (Pi.mulSingle g2ir t)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →* ↥(adjointGroup .G2 K),
      Function.Injective φ ∧ Subgroup.centralizer ({d} : Set (adjointGroup .G2 K)) = φ.range := by
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := K)
  have hKer := KS11Lie4Proof.rootCharKernel_threeA (K := K) ht
  refine ⟨φ, hφinj, ?_⟩
  apply le_antisymm
  · intro w hw
    have hw' : (w : ModGL .G2 K) ∈ toralCentralizer .G2 K (Pi.mulSingle g2ir t) :=
      (KS11Lie4Proof.mem_centralizer_iff_toral hd).mp hw
    obtain ⟨w', ⟨X, rfl⟩, hX⟩ := CFSG.RankThree.PartTwo.Sec4.Res417Seven.toralCentralizer_threeA_le_range_a2 φ hφ ht hw'
    exact ⟨X, Subtype.ext hX⟩
  · have hle := KS11Lie4Proof.range_le_of_a2y φ hφ
      (Subgroup.centralizer ({d} : Set (adjointGroup .G2 K))) fun γ hγ c => by
        rw [KS11Lie4Proof.mem_centralizer_iff_toral hd, mem_toralCentralizer]
        refine ⟨(a2y γ c).2, ?_⟩
        rw [KS11Lie4Proof.coe_a2y hγ]
        have hmem : CFSG.LieType.Steinberg.RankTwo.g2CommRoot (a2pos (γ 0, γ 1)) ∈
            rootCharKernel (Pi.mulSingle g2ir t) := by
          rw [hKer]
          exact KS11Lie4Proof.a2_long_roots hγ
        rw [rootDiagUnit_conj_pinnedX _ hmem.1, hmem.2, Units.val_one, one_mul]
    exact hle

theorem threeA_diag {K : Type} [Field K] [Finite K] {t : Kˣ} (ht : orderOf t = 3)
    {d : adjointGroup .G2 K}
    (hd : (d : ModGL .G2 K) = rootDiagUnit .G2 (Pi.mulSingle g2ir t)) : ThreeA d := by
  obtain ⟨φ, hφinj, heq⟩ := centralizer_diag_eq_range ht hd
  let e : ↥(Subgroup.centralizer ({d} : Set (adjointGroup .G2 K))) ≃*
      Matrix.SpecialLinearGroup (Fin (2 + 1)) K :=
    (MulEquiv.subgroupCongr heq).trans (MonoidHom.ofInjective hφinj).symm
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num)), ?_⟩
  refine exp_three_of_center _ e ?_
  exact (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by norm_num) K).trans
    (Nat.gcd_dvd_left _ _)

theorem threeA_of_split {K : Type} [Field K] [Finite K] (h31 : 3 ∣ Nat.card K - 1)
    {z : adjointGroup .G2 K} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : ThreeA z := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      rootSL2 .G2 K g2v A = (z : ModGL .G2 K) := by
    have hz' : (z : ModGL .G2 K) ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) := hzS
    rw [show (g2δ : Fin Tag.G2.rank → ℤ) = g2v from rfl,
      ← range_rootSL2_of_isRoot isRoot_g2v] at hz'
    exact hz'
  have hA3 : A ^ 3 = 1 := rootSL2_injective_of_field g2v (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hz3)
  have hA1 : A ≠ 1 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    rw [← hA, map_one]
    rfl
  obtain ⟨Q, t, hQt⟩ := KS11Lie4Proof.exists_conj_HSL_of_three h31 A ⟨1, by rw [pow_one]; exact hA3⟩
  have ht3 : t ^ 3 = 1 := by
    apply KS11Lie4Proof.HSLHom_injective (K := K)
    rw [map_pow, map_one, KS11Lie4Proof.HSLHom_apply, ← hQt, conj_pow, hA3, mul_one,
      mul_inv_cancel]
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hA1
    have h1 : Q * A * Q⁻¹ = 1 := by rw [hQt]; exact map_one (KS11Lie4Proof.HSLHom K)
    calc A = Q⁻¹ * (Q * A * Q⁻¹) * Q := by group
      _ = 1 := by rw [h1]; group
  have htord : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have hρC : ∀ X : Matrix.SpecialLinearGroup (Fin 2) K, rootSL2 .G2 K g2v X ∈ adjointGroup .G2 K :=
    fun X => (exceptional_Lang_root_rank_one_data .G2 K g2v).2.2.2.2.1 X
  set y : adjointGroup .G2 K := ⟨rootSL2 .G2 K g2v Q⁻¹, hρC _⟩ with hydef
  set d : adjointGroup .G2 K := ⟨rootSL2 .G2 K g2v (HSL t), hρC _⟩ with hddef
  have hdcoe : (d : ModGL .G2 K) = rootDiagUnit .G2 (Pi.mulSingle g2ir t) :=
    (show (d : ModGL .G2 K) = rootSL2 .G2 K g2v (HSL t) from rfl).trans
      (KS11Lie7Proof.rootSL2_g2v_HSL t)
  have hz : z = y * d * y⁻¹ := by
    apply Subtype.ext
    rw [← hA]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hydef, hddef]
    rw [← map_inv, ← map_mul, ← map_mul, inv_inv]
    congr 1
    calc A = Q⁻¹ * (Q * A * Q⁻¹) * Q := by group
      _ = Q⁻¹ * HSL t * Q := by rw [hQt]
  rw [hz]
  exact (threeA_diag htord hdcoe).conj y

end Cent

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
