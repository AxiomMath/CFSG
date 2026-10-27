module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LE7
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QX7
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Levi
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Descent
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Rank1
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSylow
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelRoots
public import CFSG.GH74.GLS.IVK.Proofs2.NatModGrp
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSp
public import CFSG.ClassicalInvolution.Q3.Q3ExcLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Row
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcEField
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaE7
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaE7Tw
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73Props
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Maximal
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.Sporadic.HeldB.OuterFixed
public import Certificates.Certificate14953
public import Certificates.Certificate5133
public import Certificates.Certificate7233Base
public import Certificates.Certificate8026Base
public import Certificates.Certificate8064

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Foote5.OddLieCore.Exc
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Burgoyne.E2
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace P58b3L

@[expose] def CentInvModel (H : Type*) [Group H] : Prop :=
  ∃ (ι : Type) (S : ι → Subgroup H), (∀ i, IsComponent (S i)) ∧ (∀ i, Even (Nat.card (S i))) ∧
    ∀ g h : H, (∀ i, ∀ s ∈ S i, s * g = g * s) → (∀ i, ∀ s ∈ S i, s * h = h * s) →
      g * g = 1 → h * h = 1 → g ≠ 1 → h ≠ 1 → g = h

theorem CentInvModel.of_centModel {H : Type*} [Group H] (h : P51Q.CentModel H) :
    CentInvModel H := by
  obtain ⟨ι, S, hS, hSe, -, hi⟩ := h
  exact ⟨ι, S, hS, hSe, hi⟩

theorem CentInvModel.of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (h : CentInvModel H') : CentInvModel H := by
  obtain ⟨ι, S, hS, hSe, hi⟩ := h
  have hlift : ∀ g : H, (∀ i, ∀ s ∈ (S i).map e.symm.toMonoidHom, s * g = g * s) →
      ∀ i, ∀ s ∈ S i, s * e g = e g * s := by
    intro g hg i s hs
    have h1 := congrArg e (hg i (e.symm s) ⟨s, hs, rfl⟩)
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  refine ⟨ι, fun i => (S i).map e.symm.toMonoidHom,
    fun i => LocalCores.isComponent_map_mulEquiv e.symm (hS i), fun i => ?_,
    fun g h hg hh hg2 hh2 hg1 hh1 => e.injective ?_⟩
  · rw [← Nat.card_congr ((S i).equivMapOfInjective _ e.symm.injective).toEquiv]
    exact hSe i
  · refine hi _ _ (hlift g hg) (hlift h hh) ?_ ?_ ?_ ?_
    · rw [← map_mul, hg2, map_one]
    · rw [← map_mul, hh2, map_one]
    · exact fun h1 => hg1 (e.injective (h1.trans (map_one e).symm))
    · exact fun h1 => hh1 (e.injective (h1.trans (map_one e).symm))

theorem evenCentInv_of_centInvModel {X : Type} [Group X] {z : X} (hz : orderOf z = 2)
    {H : Type*} [Group H] (Θ : centralizer ({z} : Set X) ≃* H) (h : CentInvModel H) :
    P51Q.EvenCentInv X z := by
  obtain ⟨ι, S, hS, hSe, hinv⟩ := h
  have hlift : ∀ y : centralizer ({z} : Set X),
      (∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
        ∀ k ∈ K, (k : X) * (y : X) = (y : X) * k) → ∀ i, ∀ s ∈ S i, s * Θ y = Θ y * s := by
    intro y hy i s hs
    have hK : IsComponent ((S i).map Θ.symm.toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv Θ.symm (hS i)
    have hKe : Even (Nat.card ((S i).map Θ.symm.toMonoidHom)) := by
      rw [← Nat.card_congr ((S i).equivMapOfInjective _ Θ.symm.injective).toEquiv]
      exact hSe i
    have h1 := hy _ hK hKe (Θ.symm s) ⟨s, hs, rfl⟩
    have h2 : Θ.symm s * y = y * Θ.symm s := Subtype.ext h1
    have h3 := congrArg Θ h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  have hzC : z ∈ centralizer ({z} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzcent : ∀ i, ∀ s ∈ S i, s * Θ ⟨z, hzC⟩ = Θ ⟨z, hzC⟩ * s := by
    intro i s _
    have h2 : Θ.symm s * ⟨z, hzC⟩ = ⟨z, hzC⟩ * Θ.symm s :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Θ.symm s).2)
    have h3 := congrArg Θ h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  intro g hg hgc hgg
  by_cases hg1 : g = 1
  · exact Or.inl hg1
  · refine Or.inr ?_
    have hz1 : z ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hzz : z * z = 1 := by
      rw [← sq, ← hz]
      exact pow_orderOf_eq_one z
    have h := hinv (Θ ⟨g, hg⟩) (Θ ⟨z, hzC⟩) (hlift ⟨g, hg⟩ hgc) hzcent
      (by rw [← map_mul, ← map_one Θ]; exact congrArg Θ (Subtype.ext hgg))
      (by rw [← map_mul, ← map_one Θ]; exact congrArg Θ (Subtype.ext hzz))
      (fun h1 => hg1 (congrArg Subtype.val (Θ.injective (h1.trans (map_one Θ).symm))))
      (fun h1 => hz1 (congrArg Subtype.val (Θ.injective (h1.trans (map_one Θ).symm))))
    exact congrArg Subtype.val (Θ.injective h)

variable {K : Type} [Field K]

theorem CentInvModel.fixedSubgroup_rootDiagAut
    {a : Fin (Tag.rank .E7) → Kˣ}
    (h : CentInvModel (toralCentralizer .E7 K a)) :
    CentInvModel (fixedSubgroup (rootDiagAut .E7 K a)) := by
  have hmap : (fixedSubgroup (rootDiagAut .E7 K a)).map (adjointGroup .E7 K).subtype =
      toralCentralizer .E7 K a := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_fixedSubgroup_rootDiagAut.1 hx
    · intro hy
      exact ⟨⟨y, (Subgroup.mem_inf.1 hy).1⟩, mem_fixedSubgroup_rootDiagAut.2 hy, rfl⟩
  exact h.of_mulEquiv (((fixedSubgroup (rootDiagAut .E7 K a)).equivMapOfInjective _
    Subtype.val_injective).trans (MulEquiv.subgroupCongr hmap))

theorem mem_p51qE7Gamma1
    {y : (Fin (Tag.rank .E7) → ℤ) × ℤ} (hy : y ∈ P51Q.p51qE7Gamma1) :
    y.1 = thetaE7 ∨ ∃ j ∈ JE7, y.1 = Pi.single j 1 := by
  simp only [P51Q.p51qE7Gamma1, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl E7Model.thetaE7_eq.symm
  · exact Or.inr ⟨e7Node 1, show (e7Node 1).val ≠ 0 by decide, by funext i; fin_cases i <;> rfl⟩
  · exact Or.inr ⟨e7Node 2, show (e7Node 2).val ≠ 0 by decide, by funext i; fin_cases i <;> rfl⟩
  · exact Or.inr ⟨e7Node 3, show (e7Node 3).val ≠ 0 by decide, by funext i; fin_cases i <;> rfl⟩
  · exact Or.inr ⟨e7Node 4, show (e7Node 4).val ≠ 0 by decide, by funext i; fin_cases i <;> rfl⟩
  · exact Or.inr ⟨e7Node 5, show (e7Node 5).val ≠ 0 by decide, by funext i; fin_cases i <;> rfl⟩
  · exact Or.inr ⟨e7Node 6, show (e7Node 6).val ≠ 0 by decide, by funext i; fin_cases i <;> rfl⟩

theorem exists_iform_ne_zero_JE7 : ∀ j : Fin (Tag.rank .E7), j.val ≠ 0 →
    ∃ k : Fin (Tag.rank .E7), k.val ≠ 0 ∧ k ≠ j ∧
      iform (Pi.single k 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single j 1) ≠ 0 := by
  decide +kernel

section Certified

theorem rootSL2_thetaE7_commute_single {j : Fin (Tag.rank .E7)} (hj : j ∈ JE7)
    (A B : SL2 K) : rootSL2 .E7 K thetaE7 A * rootSL2 .E7 K (Pi.single j 1) B =
      rootSL2 .E7 K (Pi.single j 1) B * rootSL2 .E7 K thetaE7 A := by
  have hpin : ∀ σ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 σ → iform σ thetaE7 = 0 → ∀ t : K,
      rootSL2 .E7 K thetaE7 A * pinnedX .E7 K σ t =
        pinnedX .E7 K σ t * rootSL2 .E7 K thetaE7 A := by
    intro σ hσ hσθ t
    refine (commute_rootSL2_of_commute isRoot_thetaE7 (fun s => ?_) (fun s => ?_) A).symm
    · exact pinnedX_commute_of_iform_eq_zero_E7 hσ isRoot_thetaE7 hσθ t s
    · refine pinnedX_commute_of_iform_eq_zero_E7 hσ (IsRoot.neg isRoot_thetaE7) ?_ t s
      rw [show (-thetaE7 : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • thetaE7 by simp,
        iform_smul_right, hσθ, mul_zero]
  exact commute_rootSL2_of_commute (isRoot_single _ j)
    (hpin _ (isRoot_single _ j) (iform_single_eq_zero_of_mem_E7 hj))
    (hpin _ (IsRoot.neg (isRoot_single _ j)) (iform_neg_single_eq_zero_of_mem_E7 hj)) B

theorem eq_one_or_eq_thetaDiag_of_commute_rootSL2 [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hK3 : 3 ≤ Nat.card K) {g : ModGL .E7 K}
    (hgC : g ∈ toralCentralizer .E7 K (thetaDiag thetaE7 (-1 : Kˣ)))
    (hj : ∀ j ∈ JE7, ∀ A : SL2 K,
      g * rootSL2 .E7 K (Pi.single j 1) A = rootSL2 .E7 K (Pi.single j 1) A * g)
    (hg2 : g * g = 1) : g = 1 ∨ g = rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Kˣ)) := by
  classical
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hM := toralCentralizer_le_toralRootGroup_thetaE7 hK2 hgC
  obtain ⟨n, hn, A, rfl⟩ := E7Model.toralRootGroup_le_leviMulRank1 hK2 hM
  have hnj : ∀ j ∈ JE7, ∀ B : SL2 K, n * rootSL2 .E7 K (Pi.single j 1) B =
      rootSL2 .E7 K (Pi.single j 1) B * n := by
    intro j hjJ B
    have h1 := hj j hjJ B
    have h3 : rootSL2 .E7 K thetaE7 A * rootSL2 .E7 K (Pi.single j 1) B *
        (rootSL2 .E7 K thetaE7 A)⁻¹ = rootSL2 .E7 K (Pi.single j 1) B := by
      rw [rootSL2_thetaE7_commute_single hjJ A B, mul_inv_cancel_right]
    calc n * rootSL2 .E7 K (Pi.single j 1) B =
        n * (rootSL2 .E7 K thetaE7 A * rootSL2 .E7 K (Pi.single j 1) B *
          (rootSL2 .E7 K thetaE7 A)⁻¹) := by rw [h3]
      _ = n * rootSL2 .E7 K thetaE7 A * rootSL2 .E7 K (Pi.single j 1) B *
          (rootSL2 .E7 K thetaE7 A)⁻¹ := by group
      _ = rootSL2 .E7 K (Pi.single j 1) B * (n * rootSL2 .E7 K thetaE7 A) *
          (rootSL2 .E7 K thetaE7 A)⁻¹ := by rw [h1]
      _ = rootSL2 .E7 K (Pi.single j 1) B * n := by group
  set L := AlgebraicClosure K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hL2 : ringChar L ≠ 2 := by
    rw [ringChar.eq L p]
    exact hp2
  have : Fintype K := Fintype.ofFinite K
  have hK3' : 3 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  set ι := algebraMap K L with hι
  have hnG : n ∈ adjointGroup .E7 K := parabolicLevi_le_adjointGroup _ _ _ hn
  have hnLG := LieType.Chevalley.baseChangeGL_mem_adjointGroup ι hnG
  have hnLJ := baseChangeGL_mem_parabolicLevi ι hn
  have hLj : ∀ j ∈ JE7, ∀ B : SL2 L, baseChangeGL ι n * rootSL2 .E7 L (Pi.single j 1) B =
      rootSL2 .E7 L (Pi.single j 1) B * baseChangeGL ι n := by
    intro j hjJ
    refine SRE7.commute_rootSL2_of_field ι hK3' _ fun B => ?_
    have h := congrArg (baseChangeGL ι) (hnj j hjJ B)
    rwa [map_mul, map_mul, RankThree.Chevalley.baseChangeGL_rootSL2_of_field] at h
  have hLθ : ∀ s : Lˣ, Commute (baseChangeGL ι n) (rootTorusSL2 .E7 L thetaE7 s) := by
    intro s
    rw [rootTorusSL2_thetaE7]
    exact (rootDiagUnit_thetaDiag_comm_levi_E7 s hnLJ).symm
  have hT := TwE7.mem_torusGroup_of_commute_rootTorus p (Or.inr (Or.inl rfl)) hnLG
    P51Q.p51qE7Gamma1 (fun y hy => by
      rcases mem_p51qE7Gamma1 hy with h | ⟨j, -, h⟩ <;> rw [h]
      · exact isRoot_thetaE7
      · exact isRoot_single _ _)
    (fun y hy s => by
      rcases mem_p51qE7Gamma1 hy with h | ⟨j, hjJ, h⟩ <;> rw [h]
      · exact hLθ s
      · exact hLj j hjJ (HSL s))
    35 (fun α hα => P51Q.p51qE7Gamma1_reg α (mem_rootFinset.2 hα))
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hbJ : ∀ j ∈ JE7, b j = 1 := by
    intro j hjJ
    have h := TwE7.rootChar_eq_one_of_commute (isRoot_single _ j)
      (by rw [← hb]; exact hLj j hjJ (uSL 1))
    rwa [P51Q.rootChar_piSingle_eq_coord] at h
  set i₀ : Fin (Tag.rank .E7) := ⟨0, by decide⟩ with hi₀
  have hbθ : b = thetaDiag thetaE7 (b i₀) := by
    funext i
    rw [thetaDiag, iform_thetaE7_single]
    by_cases hi : i.val = 0
    · have hii : i = i₀ := Fin.ext hi
      subst hii
      simp only [hi, ↓reduceIte, zpow_one]
    · simp only [hi, ↓reduceIte, zpow_zero]
      exact hbJ i hi
  have hnL : baseChangeGL ι n = rootSL2 .E7 L thetaE7 (HSL (b i₀)) :=
    hb.trans ((congrArg (rootDiagUnit .E7) hbθ).trans (rootTorusSL2_thetaE7 _).symm)
  set B : SL2 L := HSL (b i₀) * Matrix.SpecialLinearGroup.map ι A with hBdef
  have hgL : baseChangeGL ι (n * rootSL2 .E7 K thetaE7 A) = rootSL2 .E7 L thetaE7 B := by
    rw [map_mul, hnL, RankThree.Chevalley.baseChangeGL_rootSL2_of_field, ← map_mul]
  have hinj : Function.Injective (rootSL2 .E7 L thetaE7) :=
    ((exceptional_Lang_root_rank_one_data .E7 L thetaE7).2.2.2.2.2.2.2.1 hL2).1
  have hB2 : B ^ 2 = 1 := by
    apply hinj
    rw [map_pow, map_one, ← hgL, ← map_pow, sq, hg2, map_one]
  rcases GH74.GLS.IVK.Proofs2.eq_one_or_neg_one_of_sq_eq_one (Ring.two_ne_zero hL2) hB2 with
    h | h
  · left
    apply baseChangeGL_injective ι
    rw [hgL, h, map_one, map_one]
  · right
    apply baseChangeGL_injective ι
    have hneg : (-1 : SL2 L) = HSL (-1 : Lˣ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [HSL]
    rw [hgL, h, hneg, baseChangeGL_rootDiagUnit]
    refine (rootTorusSL2_thetaE7 (-1 : Lˣ)).trans (congrArg (rootDiagUnit .E7) ?_)
    funext i
    simp [thetaDiag]

theorem centInvModel_e7_t1 [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK3 : 3 ≤ Nat.card K) : CentInvModel (toralCentralizer .E7 K (bitsTuple e7BitsOne)) := by
  classical
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hc := bitsTuple_mem (K := K) e7BitsOne
  set c := bitsTuple (K := K) e7BitsOne with hcdef
  set χ := maskChar (signTupleBits c) with hχdef
  have hkerχ : rootCharKernel c = kernelRoots χ := rootCharKernel_eq_kernelRoots hK2 hc
  have hcθ : c = thetaDiag thetaE7 (-1 : Kˣ) := by
    funext i
    fin_cases i <;> simp [hcdef, bitsTuple, e7BitsOne, listMask, thetaDiag, iform_thetaE7_single]
  have : Finite (ModGL .E7 K) := finite_modGL
  have hS : ∀ ψ : {ψ : KernelComponent χ // 2 < (componentRoots χ ψ).ncard},
      IsComponent ((componentRootSpan K χ ψ.1).subgroupOf (toralCentralizer .E7 K c)) :=
    fun ψ => P51Q.isComponent_componentRootSpan_toral_of_ncard hK2 hc ψ.1 ψ.2
  have hcomm : ∀ x : toralCentralizer .E7 K c,
      (∀ ψ : {ψ : KernelComponent χ // 2 < (componentRoots χ ψ).ncard},
        ∀ s ∈ (componentRootSpan K χ ψ.1).subgroupOf (toralCentralizer .E7 K c),
          s * x = x * s) →
      ∀ j ∈ JE7, ∀ A : SL2 K, (x : ModGL .E7 K) * rootSL2 .E7 K (Pi.single j 1) A =
        rootSL2 .E7 K (Pi.single j 1) A * x := by
    intro x hx j hjJ A
    have hker : ∀ k : Fin (Tag.rank .E7), k.val ≠ 0 → Pi.single k 1 ∈ kernelRoots χ := by
      intro k hk
      rw [← hkerχ]
      refine ⟨isRoot_single _ k, ?_⟩
      rw [P51Q.rootChar_piSingle_eq_coord, hcθ, thetaDiag, iform_thetaE7_single_of_mem hk,
        zpow_zero]
    have hjχ := hker j hjJ
    have hnχ : -Pi.single j 1 ∈ kernelRoots χ := by
      have h := hjχ
      rw [← hkerχ] at h ⊢
      exact neg_mem_rootCharKernel h
    obtain ⟨k, hk0, hkj, hjk⟩ := exists_iform_ne_zero_JE7 j hjJ
    have hkχ := hker k hk0
    set ψ : KernelComponent χ := ⟦⟨Pi.single j 1, hjχ⟩⟧ with hψ
    have hmemj : Pi.single j 1 ∈ componentRoots χ ψ := ⟨hjχ, rfl⟩
    have hmemn : -Pi.single j 1 ∈ componentRoots χ ψ := by
      refine ⟨hnχ, mk_eq_of_iform_ne_zero ?_⟩
      change iform (-Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single j 1) ≠ 0
      rw [show (-Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • Pi.single j 1 by simp,
        iform_smul_left, iform_self_isRoot_E7 (isRoot_single _ j)]
      norm_num
    have hmemk : Pi.single k 1 ∈ componentRoots χ ψ := ⟨hkχ, mk_eq_of_iform_ne_zero hjk⟩
    have hfin : (componentRoots χ ψ).Finite :=
      (finite_setOf_isRoot .E7).subset fun v hv => by
        obtain ⟨h, -⟩ := hv
        exact h.1
    have hncard : 2 < (componentRoots χ ψ).ncard := by
      refine (Set.two_lt_ncard_iff hfin).2 ⟨_, _, _, hmemj, hmemn, hmemk, ?_, ?_, ?_⟩
      · intro h
        have h1 := congrFun h j
        simp at h1
      · intro h
        have h1 := congrFun h j
        simp [Ne.symm hkj] at h1
      · intro h
        have h1 := congrFun h j
        simp [Ne.symm hkj] at h1
    have hpin : ∀ σ ∈ componentRoots χ ψ, ∀ t : K,
        (x : ModGL .E7 K) * pinnedX .E7 K σ t = pinnedX .E7 K σ t * x := by
      intro σ hσ t
      have hmem : pinnedX .E7 K σ t ∈ componentRootSpan K χ ψ := pinnedX_mem_rootSpan hσ t
      have hX := P51Q.componentRootSpan_le_toralCentralizer hK2 hc ψ hmem
      have h := hx ⟨ψ, hncard⟩ ⟨_, hX⟩ (Subgroup.mem_subgroupOf.2 hmem)
      exact (congrArg Subtype.val h).symm
    exact commute_rootSL2_of_commute (isRoot_single _ j) (hpin _ hmemj) (hpin _ hmemn) A
  have key : ∀ x : toralCentralizer .E7 K c,
      (∀ ψ : {ψ : KernelComponent χ // 2 < (componentRoots χ ψ).ncard},
        ∀ s ∈ (componentRootSpan K χ ψ.1).subgroupOf (toralCentralizer .E7 K c),
          s * x = x * s) →
      x * x = 1 → x ≠ 1 → (x : ModGL .E7 K) = rootDiagUnit .E7 c := by
    intro x hx hx2 hx1
    have hxC : (x : ModGL .E7 K) ∈ toralCentralizer .E7 K (thetaDiag thetaE7 (-1 : Kˣ)) := by
      rw [← hcθ]
      exact x.2
    rcases eq_one_or_eq_thetaDiag_of_commute_rootSL2 p hp2 hK3 hxC (hcomm x hx)
      (congrArg Subtype.val hx2) with h1 | h1
    · exact absurd (Subtype.ext h1) hx1
    · rw [h1, hcθ]
  exact ⟨{ψ : KernelComponent χ // 2 < (componentRoots χ ψ).ncard},
    fun ψ => (componentRootSpan K χ ψ.1).subgroupOf (toralCentralizer .E7 K c), hS,
    fun ψ => Burgoyne.even_card_of_isQuasisimple (hS ψ).1,
    fun g h hg hh hg2 hh2 hg1 hh1 =>
      Subtype.ext ((key g hg hg2 hg1).trans (key h hh hh2 hh1).symm)⟩

theorem e7ThreeEvenCentInv_holds : E7ThreeEvenCentInv := by
  intro X _ _ _ hX z hz
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := nonempty_mulEquiv_adjointGroup .E7
    (GH74.chevalleyExceptionalModel_of_lieModel (t := .E7) (by decide) hX).2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hf, hK3⟩ := one_le_and_three_le_of_card Nat.prime_three hp2 hK
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    exact hp2
  set z' : adjointGroup .E7 K := E z with hz'def
  have hz' : orderOf z' = 2 := (orderOf_injective E.toMonoidHom E.injective z).trans hz
  have hZ := center_adjointGroup_eq_bot (τ := .E7) (K := K)
  have hcj : Function.Injective
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : x * y * x⁻¹ = y := DFunLike.congr_fun ((MonoidHom.mem_ker).1 hx) y
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  set α : MulAut (adjointGroup .E7 K) :=
    MulAut.conj z' * rootDiagAut .E7 K (1 : Fin Tag.E7.rank → Kˣ) with hαdef
  have hα1 : rootDiagAut .E7 K (1 : Fin Tag.E7.rank → Kˣ) = 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [coe_rootDiagAut, rootDiagUnit_one, one_mul, inv_one, mul_one]
    rfl
  have hαeq : α = MulAut.conj z' := by rw [hαdef, hα1, mul_one]
  have hαo : orderOf α = 2 := by
    rw [hαeq, orderOf_injective _ hcj z', hz']
  have hfix : (centralizer ({z} : Set X)).map E.toMonoidHom = fixedSubgroup α := by
    rw [hαeq]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      change z' * E x * z'⁻¹ = E x
      rw [hz'def, ← map_inv, ← map_mul, ← map_mul, ← hx', mul_inv_cancel_right]
    · intro hy
      have hy' : z' * y * z'⁻¹ = y := hy
      refine ⟨E.symm y, Subgroup.mem_centralizer_singleton_iff.2 (E.injective ?_),
        E.apply_symm_apply y⟩
      rw [map_mul, map_mul, E.apply_symm_apply, ← hz'def]
      calc y * z' = z' * y * z'⁻¹ * z' := by rw [hy']
        _ = z' * y := by group
  let Θ₀ : centralizer ({z} : Set X) ≃* fixedSubgroup α :=
    ((centralizer ({z} : Set X)).equivMapOfInjective E.toMonoidHom E.injective).trans
      (MulEquiv.subgroupCongr hfix)
  have hmodel : CentInvModel (fixedSubgroup α) := by
    by_cases hsplit : ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) ∧ ∃ ψ : MulAut (adjointGroup .E7 K),
        ψ * α * ψ⁻¹ = rootDiagAut .E7 K (signMaskTuple .E7 K m)
    · obtain ⟨m, hm, ψ, hψ⟩ := hsplit
      have h : CentInvModel (fixedSubgroup (rootDiagAut .E7 K (signMaskTuple .E7 K m))) := by
        rcases hm with rfl | rfl | rfl
        · rw [signMaskTuple_one]
          exact CentInvModel.fixedSubgroup_rootDiagAut (centInvModel_e7_t1 3 hp2 hK3)
        · rw [signMaskTuple_two]
          exact CentInvModel.of_centModel
            (P51Q.centModel_fixedSubgroup_rootDiagAut (P51Q.centModel_e7_t4 3 hp2 hK3))
        · rw [signMaskTuple_three]
          obtain ⟨n, hn⟩ := exists_conj_rootDiagAut_three (K := K) hK2
          rw [hn]
          exact CentInvModel.of_centModel ((P51Q.centModel_e7_t7 Nat.prime_three hp2 hK).of_mulEquiv
            (P51Q.fixedSubgroupMulConjEquiv _ _).symm)
      rw [← hψ] at h
      exact h.of_mulEquiv (P51Q.fixedSubgroupMulConjEquiv ψ α)
    · push Not at hsplit
      exact CentInvModel.of_centModel (P51Q.centModel_e7_twisted hp2 hf hK hαo hsplit)
  exact evenCentInv_of_centInvModel hz Θ₀ hmodel

theorem e7ThreeNoKlein_holds : E7ThreeNoKlein :=
  e7ThreeNoKlein_of_evenCentInv e7ThreeEvenCentInv_holds

end Certified

end P58b3L

end CFSG.ComponentClassification.HarrisLit.T1
