module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Outer
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.StandardPairFacts
import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank
import CFSG.Adapters.TauCetiExceptional.BridgeG2
import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof (g2ShortSL2 g2LongSL2 g2Short_commute_g2Long
  isQuasisimple_g2ShortSL2 isQuasisimple_sl2 g2ThreeBCent_holds g2ShortOut_holds mulAut_mul_conj
  exists_pow_conj_mul)
open CFSG.RankThree.PartTwo.KFacts (g2FieldHom coe_g2FieldHom g2_automorphism_normal_form)
open CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator (zStd eStd orderThreeSL coe_zStd coe_eStd
  zStd_pow_three eStd_pow_three zStd_mul_eStd orderThreeSL_ne_one)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Roots


variable {K : Type} [Field K]

theorem mem_g2ShortSL2_iff_rootSL2 {x : adjointGroup .G2 K} :
    x ∈ g2ShortSL2 K ↔ ∃ A : SL2 K, rootSL2 .G2 K ![1, 2] A = x := by
  change (x : ModGL .G2 K) ∈ rootSubgroup .G2 K CFSG.LieType.HighestRoot.g2δ ⊔
    rootSubgroup .G2 K (-CFSG.LieType.HighestRoot.g2δ) ↔ _
  rw [← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot CFSG.LieType.HighestRoot.isRoot_g2δ]
  exact MonoidHom.mem_range

theorem mem_g2LongSL2_iff_rootSL2 {x : adjointGroup .G2 K} :
    x ∈ g2LongSL2 K ↔ ∃ A : SL2 K, rootSL2 .G2 K ![1, 0] A = x := by
  have h10 : (![1, 0] : Fin Tag.G2.rank → ℤ) = CFSG.LieType.HighestRoot.g2e0 := by
    funext i
    fin_cases i <;> rfl
  change (x : ModGL .G2 K) ∈ rootSubgroup .G2 K CFSG.LieType.HighestRoot.g2e0 ⊔
    rootSubgroup .G2 K (-CFSG.LieType.HighestRoot.g2e0) ↔ _
  rw [h10, ← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot
    (isRoot_single .G2 CFSG.LieType.HighestRoot.g2l)]
  exact MonoidHom.mem_range

theorem coe_g2FieldHom_rootSL2 (σ : K ≃+* K) {x : adjointGroup .G2 K}
    {β : Fin Tag.G2.rank → ℤ} {A : SL2 K} (hx : rootSL2 .G2 K β A = x) :
    (g2FieldHom K σ x : ModGL .G2 K) =
      rootSL2 .G2 K β (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  rw [coe_g2FieldHom, ← hx]
  exact CFSG.RankThree.Chevalley.entrywise_rootSL2_of_field σ.toRingHom β A

theorem g2FieldHom_mem_g2ShortSL2 (σ : K ≃+* K) {x : adjointGroup .G2 K}
    (hx : x ∈ g2ShortSL2 K) : g2FieldHom K σ x ∈ g2ShortSL2 K := by
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff_rootSL2.1 hx
  exact mem_g2ShortSL2_iff_rootSL2.2 ⟨_, (coe_g2FieldHom_rootSL2 σ hA).symm⟩

theorem map_g2FieldHom_g2ShortSL2 (σ : K ≃+* K) :
    (g2ShortSL2 K).map (g2FieldHom K σ).toMonoidHom = g2ShortSL2 K := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact g2FieldHom_mem_g2ShortSL2 σ hx
  · intro x hx
    refine ⟨g2FieldHom K σ⁻¹ x, g2FieldHom_mem_g2ShortSL2 σ⁻¹ hx, ?_⟩
    change g2FieldHom K σ (g2FieldHom K σ⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem map_sl2_eq_self {σ : K →+* K} {A : SL2 K}
    (h : ∀ i j, σ ((A : Matrix (Fin 2) (Fin 2) K) i j) = (A : Matrix (Fin 2) (Fin 2) K) i j) :
    Matrix.SpecialLinearGroup.map σ A = A := by
  apply Subtype.ext
  change σ.mapMatrix (A : Matrix (Fin 2) (Fin 2) K) = A
  ext i j
  exact h i j

theorem map_orderThreeSL (σ : K →+* K) :
    Matrix.SpecialLinearGroup.map σ (orderThreeSL K) = orderThreeSL K :=
  map_sl2_eq_self fun i j => by fin_cases i <;> fin_cases j <;> simp [orderThreeSL]

theorem zStd_mem_g2ShortSL2 : zStd K ∈ g2ShortSL2 K :=
  mem_g2ShortSL2_iff_rootSL2.2 ⟨_, (coe_zStd K).symm⟩

theorem eStd_mem_g2LongSL2 : eStd K ∈ g2LongSL2 K :=
  mem_g2LongSL2_iff_rootSL2.2 ⟨_, (coe_eStd K).symm⟩

theorem g2FieldHom_zStd (σ : K ≃+* K) : g2FieldHom K σ (zStd K) = zStd K := by
  apply Subtype.ext
  rw [coe_g2FieldHom_rootSL2 σ (coe_zStd K).symm, map_orderThreeSL, coe_zStd]

theorem g2FieldHom_eStd (σ : K ≃+* K) : g2FieldHom K σ (eStd K) = eStd K := by
  apply Subtype.ext
  rw [coe_g2FieldHom_rootSL2 σ (coe_eStd K).symm, map_orderThreeSL, coe_eStd]

theorem g2_zStd_ne_one : zStd K ≠ 1 := by
  intro h
  apply orderThreeSL_ne_one K
  apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) ![1, 2]
  rw [map_one, ← coe_zStd, h, Subgroup.coe_one]

theorem g2_eStd_ne_one : eStd K ≠ 1 := by
  intro h
  apply orderThreeSL_ne_one K
  apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) ![1, 0]
  rw [map_one, ← coe_eStd, h, Subgroup.coe_one]

theorem eq_one_of_mem_g2ShortSL2_of_commute {w : adjointGroup .G2 K} (hw : w ∈ g2ShortSL2 K)
    (hc : ∀ j ∈ g2ShortSL2 K, w * j = j * w) (h3 : w ^ 3 = 1) : w = 1 := by
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff_rootSL2.1 hw
  have hinj := CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) ![1, 2]
  have hAc : A ∈ Subgroup.center (SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro P
    have hP : (⟨rootSL2 .G2 K ![1, 2] P,
        (exceptional_Lang_root_rank_one_data .G2 K ![1, 2]).2.2.2.2.1 P⟩ :
        adjointGroup .G2 K) ∈ g2ShortSL2 K := mem_g2ShortSL2_iff_rootSL2.2 ⟨P, rfl⟩
    have h1 := congrArg Subtype.val (hc _ hP)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hA] at h1
    change rootSL2 .G2 K ![1, 2] A * rootSL2 .G2 K ![1, 2] P =
      rootSL2 .G2 K ![1, 2] P * rootSL2 .G2 K ![1, 2] A at h1
    apply hinj
    rw [map_mul, map_mul]
    exact h1.symm
  have hA3 : A ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hA, ← Subgroup.coe_pow, h3, Subgroup.coe_one, map_one]
  obtain ⟨r, hr2, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hAc
  have hr2' : r ^ 2 = 1 := by simpa using hr2
  have hr3 : r ^ 3 = 1 := by
    have h : (Matrix.scalar (Fin 2) r) ^ 3 = Matrix.scalar (Fin 2) 1 := by
      rw [hrA, ← Matrix.SpecialLinearGroup.coe_pow, hA3, Matrix.SpecialLinearGroup.coe_one,
        map_one]
    rw [← map_pow] at h
    exact Matrix.scalar_inj.1 h
  have hr : r = 1 := by
    have e : r * r ^ 2 = r ^ 3 := by ring
    rwa [hr2', hr3, mul_one] at e
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [← hrA, hr, map_one, Matrix.SpecialLinearGroup.coe_one]
  apply Subtype.ext
  rw [← hA, hA1, map_one, Subgroup.coe_one]

theorem exists_g2ShortSL2_not_commute_zStd :
    ∃ w ∈ g2ShortSL2 K, (∀ σ : K ≃+* K, g2FieldHom K σ w = w) ∧ zStd K * w ≠ w * zStd K := by
  set W : SL2 K := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ with hW
  have hmem := (exceptional_Lang_root_rank_one_data .G2 K ![1, 2]).2.2.2.2.1 W
  refine ⟨⟨rootSL2 .G2 K ![1, 2] W, hmem⟩, mem_g2ShortSL2_iff_rootSL2.2 ⟨W, rfl⟩, fun σ => ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_g2FieldHom_rootSL2 σ (x := ⟨rootSL2 .G2 K ![1, 2] W, hmem⟩) (β := ![1, 2]) (A := W)
      rfl]
    change rootSL2 .G2 K ![1, 2] _ = rootSL2 .G2 K ![1, 2] W
    congr 1
    exact map_sl2_eq_self fun i j => by fin_cases i <;> fin_cases j <;> simp [hW]
  · intro h
    have h1 := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_zStd] at h1
    change rootSL2 .G2 K ![1, 2] (orderThreeSL K) * rootSL2 .G2 K ![1, 2] W =
      rootSL2 .G2 K ![1, 2] W * rootSL2 .G2 K ![1, 2] (orderThreeSL K) at h1
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg (fun P : SL2 K => (P : Matrix (Fin 2) (Fin 2) K) 0 1)
      (CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) ![1, 2] h1)
    change ((orderThreeSL K : Matrix (Fin 2) (Fin 2) K) * (W : Matrix (Fin 2) (Fin 2) K)) 0 1 =
      ((W : Matrix (Fin 2) (Fin 2) K) * (orderThreeSL K : Matrix (Fin 2) (Fin 2) K)) 0 1 at h2
    simp [hW, orderThreeSL, Matrix.mul_apply, Fin.sum_univ_two] at h2

theorem exists_g2_involution (hK2 : ringChar K ≠ 2) :
    ∃ t : adjointGroup .G2 K, t ∈ g2LongSL2 K ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧
      (∀ σ : K ≃+* K, g2FieldHom K σ t = t) ∧ ∀ m ∈ g2LongSL2 K, m * t = t * m := by
  set N : SL2 K := ⟨-1, by simp [Matrix.det_neg]⟩ with hN
  have hNc : ∀ P : SL2 K, P * N = N * P := fun P => Subtype.ext (show
    (P : Matrix (Fin 2) (Fin 2) K) * -1 = -1 * (P : Matrix (Fin 2) (Fin 2) K) by
      rw [mul_neg_one, neg_one_mul])
  have hN2 : N ^ 2 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow]
    simp [hN, sq]
  have hmem := (exceptional_Lang_root_rank_one_data .G2 K ![1, 0]).2.2.2.2.1 N
  refine ⟨⟨rootSL2 .G2 K ![1, 0] N, hmem⟩, mem_g2LongSL2_iff_rootSL2.2 ⟨N, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : rootSL2 .G2 K ![1, 0] N = rootSL2 .G2 K ![1, 0] 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := congrArg (fun P : SL2 K => (P : Matrix (Fin 2) (Fin 2) K) 0 0)
      (CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) ![1, 0] h1)
    have h3 : (-1 : K) = 1 := by simpa [hN] using h2
    exact hK2 (neg_one_eq_one_iff.1 h3)
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (rootSL2 .G2 K ![1, 0] N) ^ 2 = 1
    rw [← map_pow, hN2, map_one]
  · intro σ
    apply Subtype.ext
    rw [coe_g2FieldHom_rootSL2 σ (x := ⟨rootSL2 .G2 K ![1, 0] N, hmem⟩) (β := ![1, 0]) (A := N)
      rfl]
    change rootSL2 .G2 K ![1, 0] _ = rootSL2 .G2 K ![1, 0] N
    congr 1
    exact map_sl2_eq_self fun i j => by fin_cases i <;> fin_cases j <;> simp [hN]
  · intro m hm
    obtain ⟨P, hP⟩ := mem_g2LongSL2_iff_rootSL2.1 hm
    apply Subtype.ext
    change (m : ModGL .G2 K) * rootSL2 .G2 K ![1, 0] N = rootSL2 .G2 K ![1, 0] N * m
    rw [← hP, ← map_mul, ← map_mul, hNc]

theorem glaPLayer_g2ShortSL2_inf_fix_ne_bot [Finite K] (σ : K ≃+* K)
    (h4 : 4 ≤ Nat.card (semilinearFixedSubfield σ)) :
    GLAPLayer 3 (g2ShortSL2 K ⊓ fixSubgroup (g2FieldHom K σ)) ≠ ⊥ := by
  classical
  haveI : Finite ↥(adjointGroup .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  set K₀ := semilinearFixedSubfield σ with hK₀
  set ι₀ : SL2 K₀ →* SL2 K := Matrix.SpecialLinearGroup.map K₀.subtype with hι₀
  set ρ : SL2 K →* ↥(adjointGroup .G2 K) := (rootSL2 .G2 K ![1, 2]).codRestrict _
    (fun A => (exceptional_Lang_root_rank_one_data .G2 K ![1, 2]).2.2.2.2.1 A) with hρ
  have hρinj : Function.Injective ρ := fun A B h =>
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) ![1, 2]
      (congrArg Subtype.val h)
  have hι₀inj : Function.Injective ι₀ := fun A B h => Subtype.ext (Matrix.ext fun i j =>
    Subtype.val_injective (congrFun (congrFun (congrArg Subtype.val h) i) j))
  set L := (ρ.comp ι₀).range with hL
  have hJL : g2ShortSL2 K ⊓ fixSubgroup (g2FieldHom K σ) = L := by
    apply le_antisymm
    · rintro x ⟨hxJ, hxF⟩
      obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff_rootSL2.1 hxJ
      have hfix : Matrix.SpecialLinearGroup.map σ.toRingHom A = A := by
        apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) ![1, 2]
        calc rootSL2 .G2 K ![1, 2] (Matrix.SpecialLinearGroup.map σ.toRingHom A)
            = (g2FieldHom K σ x : ModGL .G2 K) := (coe_g2FieldHom_rootSL2 σ hA).symm
          _ = (x : ModGL .G2 K) := congrArg Subtype.val hxF
          _ = rootSL2 .G2 K ![1, 2] A := hA.symm
      have hent : ∀ i j, σ ((A : Matrix (Fin 2) (Fin 2) K) i j) =
          (A : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by
        exact congrArg (fun B : SL2 K => (B : Matrix (Fin 2) (Fin 2) K) i j) hfix
      let A₀ : Matrix (Fin 2) (Fin 2) K₀ := Matrix.of fun i j => ⟨_, hent i j⟩
      have hA₀ : A₀.map K₀.subtype = A := Matrix.ext fun _ _ => rfl
      have hdet : A₀.det = 1 := Subtype.val_injective (by
        change K₀.subtype A₀.det = K₀.subtype 1
        rw [RingHom.map_det, map_one]
        change (A₀.map K₀.subtype).det = 1
        rw [hA₀]
        exact A.2)
      refine ⟨⟨A₀, hdet⟩, Subtype.ext ?_⟩
      change rootSL2 .G2 K ![1, 2] (ι₀ ⟨A₀, hdet⟩) = (x : ModGL .G2 K)
      rw [← hA]
      exact congrArg (rootSL2 .G2 K ![1, 2]) (Subtype.ext hA₀)
    · rintro _ ⟨A₀, rfl⟩
      refine ⟨mem_g2ShortSL2_iff_rootSL2.2 ⟨ι₀ A₀, rfl⟩, ?_⟩
      show g2FieldHom K σ (ρ (ι₀ A₀)) = ρ (ι₀ A₀)
      apply Subtype.ext
      rw [coe_g2FieldHom_rootSL2 σ (x := ρ (ι₀ A₀)) (β := ![1, 2]) (A := ι₀ A₀) rfl]
      change rootSL2 .G2 K ![1, 2] _ = rootSL2 .G2 K ![1, 2] (ι₀ A₀)
      congr 1
      exact map_sl2_eq_self fun i j => (A₀ i j).2
  have eL : SL2 K₀ ≃* ↥L := MonoidHom.ofInjective (hρinj.comp hι₀inj)
  have hq : CFSG.IsQuasisimple ↥L := CFSG.IsQuasisimple.of_mulEquiv eL.symm (isQuasisimple_sl2 h4)
  obtain ⟨w, hwJ, hwfix, hzw⟩ := exists_g2ShortSL2_not_commute_zStd (K := K)
  have hzL : zStd K ∈ L := by
    rw [← hJL]
    exact ⟨zStd_mem_g2ShortSL2, g2FieldHom_zStd σ⟩
  have hwL : w ∈ L := by
    rw [← hJL]
    exact ⟨hwJ, hwfix σ⟩
  have hdvd : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute
      Nat.prime_three hzL hwL (zStd_pow_three K) hzw
  rw [hJL]
  refine CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple Nat.prime_three
    le_rfl ?_ ⟨hq.1.commutator_eq_top, hq.2.1⟩ hdvd
  rw [Subgroup.subgroupOf_self]
  infer_instance

end Roots

section Model


variable {K : Type} [Field K] [Finite K]

theorem glaPComponent_g2ShortSL2 (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) :
    GLAPComponent 3 (Subgroup.centralizer
      ((Subgroup.zpowers (eStd K) : Subgroup ↥(adjointGroup .G2 K)) : Set ↥(adjointGroup .G2 K)))
      (g2ShortSL2 K) := by
  haveI : Finite ↥(adjointGroup .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  have hB := g2ThreeBCent_holds K hK3 hK4 (eStd K) eStd_mem_g2LongSL2 (eStd_pow_three K)
    g2_eStd_ne_one
  have hC : Subgroup.centralizer ((Subgroup.zpowers (eStd K) : Subgroup ↥(adjointGroup .G2 K)) :
      Set ↥(adjointGroup .G2 K)) = Subgroup.centralizer ({eStd K} : Set ↥(adjointGroup .G2 K)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hC]
  have hJC : g2ShortSL2 K ≤ Subgroup.centralizer ({eStd K} : Set ↥(adjointGroup .G2 K)) :=
    fun j hj => Subgroup.mem_centralizer_singleton_iff.2 (g2Short_commute_g2Long hj eStd_mem_g2LongSL2)
  have hN : ((g2ShortSL2 K).subgroupOf
      (Subgroup.centralizer ({eStd K} : Set ↥(adjointGroup .G2 K)))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := hB.1 g g.2 n n.2
    have e1 : ((g * n * g⁻¹ : ↥(Subgroup.centralizer ({eStd K} : Set ↥(adjointGroup .G2 K)))) :
        ↥(adjointGroup .G2 K)) = (g : ↥(adjointGroup .G2 K)) * n * (g : ↥(adjointGroup .G2 K))⁻¹ *
          (n : ↥(adjointGroup .G2 K))⁻¹ * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1]
    exact mul_mem h1 hn⟩
  have hq := isQuasisimple_g2ShortSL2 hK4
  refine CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_three
    (CFSG.Open.IsSubnormal.step hJC hN (CFSG.Open.IsSubnormal.refl _))
    ⟨hq.1.commutator_eq_top, hq.2.1⟩ ?_
  obtain ⟨w, hwJ, -, hzw⟩ := exists_g2ShortSL2_not_commute_zStd (K := K)
  exact CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute
    Nat.prime_three zStd_mem_g2ShortSL2 hwJ (zStd_pow_three K) hzw

theorem g2_centMod_clause (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) {σ : K ≃+* K}
    (hσ3 : σ ^ 3 = 1)
    (hout : g2FieldHom K σ ∉ (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range)
    {a : ↥(adjointGroup .G2 K)} (ha : a ∈ Subgroup.zpowers (eStd K) ⊔ Subgroup.zpowers (zStd K))
    {k : ℕ} (hk : k < 3)
    (hc : ∀ j ∈ g2ShortSL2 K, j * (a * ((g2FieldHom K σ) ^ k) j * a⁻¹)⁻¹ ∈
      GLAPPrimeCoreOf 3 (g2ShortSL2 K)) :
    k = 0 ∧ a ∈ Subgroup.zpowers (eStd K) := by
  haveI : Finite ↥(adjointGroup .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := g2FieldHom K σ with hψ
  have hψ3 : ψ ^ 3 = 1 := by rw [hψ, ← map_pow, hσ3, map_one]
  have hzJ : Subgroup.zpowers (zStd K) ≤ g2ShortSL2 K :=
    Subgroup.zpowers_le.2 zStd_mem_g2ShortSL2
  have heM : Subgroup.zpowers (eStd K) ≤ g2LongSL2 K := Subgroup.zpowers_le.2 eStd_mem_g2LongSL2
  have hcommEZ : ∀ x ∈ Subgroup.zpowers (eStd K), ∀ y ∈ Subgroup.zpowers (zStd K), Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Commute.zpow_zpow (zStd_mul_eStd K).symm m n
  have hAfix : Subgroup.zpowers (eStd K) ⊔ Subgroup.zpowers (zStd K) ≤ fixSubgroup ψ :=
    sup_le (Subgroup.zpowers_le.2 (g2FieldHom_eStd σ)) (Subgroup.zpowers_le.2 (g2FieldHom_zStd σ))
  have hAel : IsElemAbelian 3 (Subgroup.zpowers (eStd K) ⊔ Subgroup.zpowers (zStd K)) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers (eStd_pow_three K))
      (CFSG.Open.isElemAbelian_zpowers (zStd_pow_three K)) fun x hx y hy => (hcommEZ x hx y hy).eq
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hψa : ∀ m : ℕ, (ψ ^ m) a = a := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, mem_fixSubgroup.1 (hAfix ha), ih]
  have hJq := isQuasisimple_g2ShortSL2 hK4
  have hJ3 : 3 ∣ Nat.card ↥(g2ShortSL2 K) := by
    have ho : orderOf (⟨zStd K, zStd_mem_g2ShortSL2⟩ : ↥(g2ShortSL2 K)) = 3 :=
      orderOf_eq_prime (Subtype.ext (by simp [zStd_pow_three]))
        (fun h => g2_zStd_ne_one (congrArg Subtype.val h))
    rw [← ho]
    exact orderOf_dvd_natCard _
  have hβJ := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf
    Nat.prime_three ⟨hJq.1.commutator_eq_top, hJq.2.1⟩ hJ3 (MulAut.conj a * ψ ^ k).toMonoidHom
    fun j hj => by
      have h := (GLAPPrimeCoreOf 3 (g2ShortSL2 K)).inv_mem (hc j hj)
      rw [mul_inv_rev, inv_inv] at h
      show (MulAut.conj a * ψ ^ k) j * j⁻¹ ∈ _
      rwa [MulAut.mul_apply, MulAut.conj_apply]
  have hcomm : Commute (MulAut.conj a) (ψ ^ k) := by
    have h := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.mulAut_mul_conj (ψ ^ k) a
    rw [hψa] at h
    exact h.symm
  have hβ3 : (MulAut.conj a * ψ ^ k) ^ 3 = 1 := by
    rw [hcomm.mul_pow, ← map_pow, ha3, map_one, one_mul, pow_right_comm, hψ3, one_pow]
  have hβin := g2ShortOut_holds K hK3 hK4 (MulAut.conj a * ψ ^ k) ⟨1, by rw [pow_one]; exact hβ3⟩
    fun x hx => hβJ x hx
  have hψk : ψ ^ k ∈ (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range := by
    rw [← inv_mul_cancel_left (MulAut.conj a) (ψ ^ k)]
    exact mul_mem (inv_mem ⟨a, rfl⟩) hβin
  have hk0 : k = 0 := by
    by_contra hk0
    have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with rfl | rfl
    · exact hout (by simpa using hψk)
    · apply hout
      have h2 : ψ = (ψ ^ 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ']
        exact hψ3
      rw [h2]
      exact inv_mem hψk
  subst hk0
  have hac : ∀ j ∈ g2ShortSL2 K, a * j = j * a := fun j hj => by
    have h := hβJ j hj
    change (MulAut.conj a * ψ ^ 0) j = j at h
    rw [pow_zero, mul_one, MulAut.conj_apply] at h
    calc a * j = a * j * a⁻¹ * a := by group
      _ = j * a := by rw [h]
  obtain ⟨x, hx, y, hy, rfl⟩ := (CFSG.mem_sup_of_commute hcommEZ).1 ha
  have hxc : ∀ j ∈ g2ShortSL2 K, x * j = j * x := fun j hj =>
    (g2Short_commute_g2Long hj (heM hx)).symm
  have hyc : ∀ j ∈ g2ShortSL2 K, y * j = j * y := fun j hj => by
    have h1 := hac j hj
    have h2 := hxc j hj
    calc y * j = x⁻¹ * (x * y * j) := by group
      _ = x⁻¹ * (j * (x * y)) := by rw [h1]
      _ = x⁻¹ * (j * x) * y := by group
      _ = x⁻¹ * (x * j) * y := by rw [h2]
      _ = j * y := by group
  have hy1 : y = 1 := eq_one_of_mem_g2ShortSL2_of_commute (hzJ hy) hyc
    ((CFSG.Open.isElemAbelian_zpowers (zStd_pow_three K)).2 y hy)
  rw [hy1, mul_one]
  exact ⟨rfl, hx⟩

theorem modelB_g2 {p : ℕ} [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p) {σ : K ≃+* K}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ModelB ↥(adjointGroup .G2 K) (g2FieldHom K σ) := by
  classical
  haveI : Finite ↥(adjointGroup .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : ringChar K = p := ringChar.eq K p
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; omega
  have hK2 : ringChar K ≠ 2 := by rw [hchar]; omega
  have hpK : p ≤ Nat.card K := calc
    p = Nat.card (ZMod p) := (Nat.card_zmod p).symm
    _ ≤ Nat.card K := Nat.card_le_card_of_injective _ (ZMod.castHom (dvd_refl p) K).injective
  have hK4 : 4 ≤ Nat.card K := by omega
  have hK₀ : 4 ≤ Nat.card (semilinearFixedSubfield σ) := by
    set K₀ := semilinearFixedSubfield σ
    haveI : CharP K₀ p := (RingHom.charP_iff K₀.subtype K₀.subtype.injective p).mpr ‹_›
    calc 4 ≤ p := by omega
      _ = Nat.card (ZMod p) := (Nat.card_zmod p).symm
      _ ≤ Nat.card K₀ :=
        Nat.card_le_card_of_injective _ (ZMod.castHom (dvd_refl p) K₀).injective
  obtain ⟨-, hinn⟩ := g2_automorphism_normal_form hK3 hK4 (K := K)
  have hout : g2FieldHom K σ ∉
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range :=
    fun h => hσ1 (hinn σ h)
  obtain ⟨t, htM, ht1, ht2, htψ, htc⟩ := exists_g2_involution (K := K) hK2
  have hcommEZ : ∀ x ∈ Subgroup.zpowers (eStd K), ∀ y ∈ Subgroup.zpowers (zStd K),
      Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Commute.zpow_zpow (zStd_mul_eStd K).symm m n
  have heo : orderOf (eStd K) = 3 := orderOf_eq_prime (eStd_pow_three K) g2_eStd_ne_one
  have hzo : orderOf (zStd K) = 3 := orderOf_eq_prime (zStd_pow_three K) g2_zStd_ne_one
  have hdisj : Subgroup.zpowers (eStd K) ⊓ Subgroup.zpowers (zStd K) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwe, hwz⟩
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_g2ShortSL2_of_commute (Subgroup.zpowers_le.2 zStd_mem_g2ShortSL2 hwz)
      (fun j hj => (g2Short_commute_g2Long hj (Subgroup.zpowers_le.2 eStd_mem_g2LongSL2 hwe)).symm)
      ((CFSG.Open.isElemAbelian_zpowers (zStd_pow_three K)).2 w hwz)
  refine ⟨by rw [← map_pow, hσ3, map_one], hout,
    Subgroup.zpowers (eStd K) ⊔ Subgroup.zpowers (zStd K), Subgroup.zpowers (eStd K),
    g2ShortSL2 K, t,
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers (eStd_pow_three K))
      (CFSG.Open.isElemAbelian_zpowers (zStd_pow_three K)) (fun x hx y hy => (hcommEZ x hx y hy).eq),
    ?_, ?_, le_sup_left, ?_, glaPComponent_g2ShortSL2 hK3 hK4, ?_, map_g2FieldHom_g2ShortSL2 σ,
    fun a ha k hk hc => g2_centMod_clause hK3 hK4 hσ3 hout ha hk hc,
    glaPLayer_g2ShortSL2_inf_fix_ne_bot σ hK₀, ht1, ht2, ?_, ?_, htψ σ⟩
  · rw [CFSG.card_sup_eq_mul_of_commute _ _ hcommEZ hdisj, Nat.card_zpowers, Nat.card_zpowers, heo,
      hzo]
    norm_num
  · intro a ha
    exact mem_fixSubgroup.1 (sup_le (Subgroup.zpowers_le.2 (g2FieldHom_eStd σ))
      (Subgroup.zpowers_le.2 (g2FieldHom_zStd σ)) ha)
  · rw [Nat.card_zpowers, heo]
  · exact sup_le
      (Subgroup.zpowers_le.2 (modelB_mem_normalizer_of_comm fun j hj =>
        (g2Short_commute_g2Long hj eStd_mem_g2LongSL2).symm))
      (Subgroup.zpowers_le.2 (Subgroup.le_normalizer zStd_mem_g2ShortSL2))
  · exact fun j hj => Subgroup.mem_centralizer_singleton_iff.2 (g2Short_commute_g2Long hj htM)
  · exact sup_le
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (htc _ eStd_mem_g2LongSL2)))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
        (g2Short_commute_g2Long zStd_mem_g2ShortSL2 htM)))

end Model

section Assembly


variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_g2 (H : P3Hyp q S B) {K : Type} [Field K] [Finite K] [Fact q.Prime] [CharP K q]
    (e : ↥(adjointGroup .G2 K) ≃* PSimple 3 S) : S267ConcA 3 S B := by
  classical
  haveI : Finite ↥(adjointGroup .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  have hq5 : 5 ≤ q := by
    have h2 := H.prime.two_le
    have h4 : q ≠ 4 := by
      rintro rfl
      exact absurd H.prime (by norm_num)
    have := H.two
    have := H.three
    omega
  have hchar : ringChar K = q := ringChar.eq K q
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; exact H.three
  have hqK : q ≤ Nat.card K := calc
    q = Nat.card (ZMod q) := (Nat.card_zmod q).symm
    _ ≤ Nat.card K := Nat.card_le_card_of_injective _ (ZMod.castHom (dvd_refl q) K).injective
  have hK5 : 5 ≤ Nat.card K := le_trans hq5 hqK
  have hK4 : 4 ≤ Nat.card K := by omega
  have h3K : ¬ 3 ∣ Nat.card K := by
    haveI := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K q
    rw [Nat.card_eq_fintype_card, hn]
    intro h
    exact H.three ((Nat.prime_dvd_prime_iff_eq Nat.prime_three H.prime).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hZX : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier (e.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot).symm) ?_
    haveI := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_hopfMultiplier hK5).2
    rw [Nat.card_of_subsingleton
      (1 : CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient .G2 K))]
    norm_num
  obtain ⟨φ, hφ, hφS⟩ := exists_embedding_of_mulEquiv H hZ e
  obtain ⟨b, hbB, β, hβ, hβφ⟩ := H.exists_outer_mem φ hφ hφS hZX
    (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.card_le_nine_of_isElemAbelian_three K h3K)
  obtain ⟨hnf, hinn⟩ := g2_automorphism_normal_form hK3 hK4 (K := K)
  obtain ⟨g, σ, hgσ⟩ := hnf β
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hβ
    rw [hgσ, map_one, mul_one]
    exact ⟨g, rfl⟩
  have hb3 : b ^ 3 = 1 := H.elem.2 b hbB
  have hβk : ∀ k : ℕ, ∀ x, φ ((β ^ k) x) = b ^ k * φ x * (b ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ β k, MulAut.mul_apply, ih, hβφ, pow_succ b k]
      group
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun x => hφ ?_
    rw [hβk 3 x, hb3, one_mul, inv_one, mul_one, MulAut.one_apply]
  have hσ3 : σ ^ 3 = 1 := by
    obtain ⟨x, hx⟩ := exists_pow_conj_mul (g2FieldHom K σ) g 3
    rw [← hgσ, hβ3, ← map_pow] at hx
    refine hinn _ ⟨x⁻¹, ?_⟩
    rw [map_inv, eq_inv_mul_of_mul_eq hx.symm, mul_one]
  have hψ3 : (g2FieldHom K σ) ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  set b' := (φ g)⁻¹ * b with hb'
  have hb'φ : ∀ x, b' * φ x * b'⁻¹ = φ (g2FieldHom K σ x) := by
    intro x
    have h1 := hβφ x
    rw [hgσ, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    rw [hb']
    calc (φ g)⁻¹ * b * φ x * ((φ g)⁻¹ * b)⁻¹ = (φ g)⁻¹ * (b * φ x * b⁻¹) * φ g := by group
      _ = (φ g)⁻¹ * (φ g * φ (g2FieldHom K σ x) * (φ g)⁻¹) * φ g := by rw [h1]
      _ = φ (g2FieldHom K σ x) := by group
  have hb'k : ∀ k : ℕ, ∀ x, b' ^ k * φ x * (b' ^ k)⁻¹ = φ (((g2FieldHom K σ) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ (g2FieldHom K σ) k, MulAut.mul_apply, ← ih, ← hb'φ, pow_succ b' k]
      group
  have hgS : φ g ∈ S := hφS ▸ ⟨g, rfl⟩
  have hb'3 : b' ^ 3 = 1 := by
    have hS3 : b' ^ 3 ∈ S := by
      have e1 : b' ^ 3 = (φ g)⁻¹ * (b * (φ g)⁻¹ * b⁻¹) * (b ^ 2 * (φ g)⁻¹ * (b ^ 2)⁻¹) * b ^ 3 := by
        rw [hb', pow_three']
        group
      rw [e1, hb3, mul_one]
      exact mul_mem (mul_mem (S.inv_mem hgS) (H.normal.conj_mem _ (S.inv_mem hgS) b))
        (H.normal.conj_mem _ (S.inv_mem hgS) (b ^ 2))
    have hc3 : ∀ s ∈ S, b' ^ 3 * s = s * b' ^ 3 := by
      intro s hs
      obtain ⟨x, rfl⟩ : ∃ x, φ x = s := by
        rw [← hφS] at hs
        exact hs
      have h1 := hb'k 3 x
      rw [hψ3, MulAut.one_apply] at h1
      calc b' ^ 3 * φ x = b' ^ 3 * φ x * (b' ^ 3)⁻¹ * b' ^ 3 := by group
        _ = φ x * b' ^ 3 := by rw [h1]
    have hmem : (⟨b' ^ 3, hS3⟩ : ↥S) ∈ Subgroup.center ↥S :=
      Subgroup.mem_center_iff.2 fun s => Subtype.ext (hc3 s s.2).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hb'B₀ : ∀ c ∈ B ⊓ centModSubgroup 3 S, b' * c = c * b' := by
    rintro c ⟨hcB, hcC⟩
    have h1 : c * (φ g)⁻¹ = (φ g)⁻¹ * c := H.comm_of_mem_centMod hcC (S.inv_mem hgS)
    have h2 : b * c = c * b := congrArg Subtype.val (H.elem.1.is_comm.comm ⟨b, hbB⟩ ⟨c, hcB⟩)
    rw [hb', mul_assoc, h2, ← mul_assoc, ← h1, mul_assoc]
  haveI : Fact q.Prime := ‹_›
  exact concA_of_modelB H hZ φ hφ hφS hb'3 hb'B₀ hb'φ (modelB_g2 hq5 hσ3 hσ1)

theorem p3At_G2 (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 Q).Valid) :
    P3At ⟨.G2 Q, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  have hQq : Q.p = q := by simpa using hchar
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hK : Nat.card (GaloisField Q.p Q.exponent) = Q.card := by
    rw [GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨eb⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 Q hv (by rw [hQq]; exact H.two)
    (GaloisField Q.p Q.exponent) hK
  have hZX : Subgroup.center ↥(adjointGroup .G2 (GaloisField Q.p Q.exponent)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  subst hQq
  exact Or.inl (concA_g2 H ((((QuotientGroup.quotientMulEquivOfEq hZX).trans
    QuotientGroup.quotientBot).symm.trans eb).trans e.symm))

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
