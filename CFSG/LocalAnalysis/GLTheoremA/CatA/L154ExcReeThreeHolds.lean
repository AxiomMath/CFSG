module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeThree
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeUnitary
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeCore
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofRee
public import CFSG.RankThree.PartTwo.KFacts.AutLargeRee
public import CFSG.RankThree.PartTwo.KFacts.K71Basic
public import CFSG.RankThree.PartOne.RF4.FinalKFacts
public import CFSG.RankThree.PartOne.KC.ExactLiftingGeneric
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenProj LargeEvenProjMk
  LargeEvenSUGroup LargeEvenMatConjImage LargeEvenGUSet)
open CFSG.LieType.Ree
open CFSG.StandardType (markTag markRank markChar markDeg)

theorem l154_marking_fixed {C R : Type} [Group C] [Group R] (φC : C →* C)
    (θ : C ⧸ Subgroup.center C ≃* R) (ψ : MulAut R) (hperf : commutator C = ⊤)
    (hZ : Nat.card (Subgroup.center C) = 3) (hφ3 : ∀ z, φC (φC (φC z)) = z)
    (hind : ∀ l : C, ψ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (φC l)))
    (hkey : ψ ^ 3 = 1 → ∀ y : R, ψ y = y → y ^ 4 = 1 → y ^ 2 ≠ 1 → ψ = 1)
    {u : C} (hu : φC u = u) (hu4 : u ^ 4 = 1) (hu2 : u ^ 2 ≠ 1) : ∀ g : C, φC g = g := by
  have hψ3 : ψ ^ 3 = 1 := by
    refine MulEquiv.ext fun r => ?_
    obtain ⟨l, rfl⟩ : ∃ l : C, θ (QuotientGroup.mk l) = r := by
      obtain ⟨q, rfl⟩ := θ.surjective r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨l, rfl⟩
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    rw [hind l, hind (φC l), hind (φC (φC l)), hφ3 l]
  set y := θ (QuotientGroup.mk u) with hy
  have hψy : ψ y = y := by rw [hy, hind u, hu]
  have hy4 : y ^ 4 = 1 := by
    rw [hy, ← map_pow, ← QuotientGroup.mk_pow, hu4, QuotientGroup.mk_one, map_one]
  have hy2 : y ^ 2 ≠ 1 := by
    intro h1
    rw [hy, ← map_pow, ← QuotientGroup.mk_pow] at h1
    have h3 : u ^ 2 ∈ Subgroup.center C :=
      (QuotientGroup.eq_one_iff _).mp ((MulEquiv.map_eq_one_iff θ).mp h1)
    have h4 : orderOf (⟨u ^ 2, h3⟩ : Subgroup.center C) ∣ 3 := hZ ▸ orderOf_dvd_natCard _
    have h5 : orderOf (⟨u ^ 2, h3⟩ : Subgroup.center C) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [← pow_mul] using hu4))
    have h6 : orderOf (⟨u ^ 2, h3⟩ : Subgroup.center C) = 1 := by
      have := Nat.dvd_gcd h4 h5
      simpa using this
    exact hu2 (congrArg Subtype.val (orderOf_eq_one_iff.mp h6))
  have hψ1 : ψ = 1 := hkey hψ3 y hψy hy4 hy2
  have hfix : ∀ g ∈ (⊤ : Subgroup C), φC g = g := by
    refine CFSG.RankThree.PartOne.KCGeneric.endo_eq_of_central_perfect φC (F := ⊤)
      (Z := Subgroup.center C) (Subgroup.isPerfect_iff.2 hperf) (fun z hz g => ?_)
      (fun g _ => ?_)
    · exact (Subgroup.mem_center_iff.mp hz g).symm
    · have h1 : θ (QuotientGroup.mk (φC g)) = θ (QuotientGroup.mk g) := by
        rw [← hind g, hψ1, MulAut.one_apply]
      have h2 : (QuotientGroup.mk (φC g) : C ⧸ Subgroup.center C) = QuotientGroup.mk g :=
        θ.injective h1
      have h3 := QuotientGroup.eq_iff_div_mem.mp h2
      rwa [div_eq_mul_inv] at h3
  exact fun g => hfix g (Subgroup.mem_top g)

section Cent


theorem l154_ree_three_su {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {s : ReeTag.F4.reeGamma K a} (hs : orderOf s = 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ (2 * a + 1)) ^ 2 ∧
      Nonempty (↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))) ≃*
        unitarySU 2 (2 * a + 1) F 3) := by
  obtain ⟨ι⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK
    s hs
  refine ⟨GaloisField 2 (2 * (2 * a + 1)), inferInstance, inferInstance, ?_, ⟨ι⟩⟩
  rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]

theorem l154_ree_three_lieModel {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {s : ReeTag.F4.reeGamma K a}
    (hs : orderOf s = 3) :
    CFSG.Blueprint.LieModel (↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a)))) .PSU 3 2
      (2 * a + 1) := by
  obtain ⟨F, _, _, hF, ⟨ι⟩⟩ := l154_ree_three_su hK hs
  have h : UnitaryFieldData 2 (2 * a + 1) F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  rw [CFSG.Blueprint.LieModel.classical_iff (by decide)]
  refine ⟨?_, F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
  · refine ⟨Nat.prime_two, by omega, le_rfl, fun hc => ?_⟩
    have h2 := (Prod.mk.inj hc).2
    have h8 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · exact (QuotientGroup.congr _ _ ι (Subgroup.map_center_eq ι)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (center_eq_unitaryScalars h (by omega))).trans (unitaryPSUEquiv h (by norm_num)))

theorem l154_ree_autFix_equiv {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {α : MulAut (ReeTag.F4.reeGamma K a)} (hα3 : α ^ 3 = 1)
    (hαin : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut α) :
    ∃ (b : ℕ) (k' : Type) (_ : Field k') (_ : Finite k') (_ : CharP k' ReeTag.F4.prime),
      Nat.card k' = 2 ^ (2 * b + 1) ∧
        Nonempty (CFSG.RankThree.PartTwo.Sec4.autFix α ≃* ReeTag.F4.reeGamma k' b) := by
  obtain ⟨β, hβ, hcoset⟩ :=
    CFSG.RankThree.PartTwo.KFacts.largeRee_order_three_inFieldCoset ha hK hα3 hαin
  obtain ⟨x, hx⟩ :=
    CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj a K hK β hβ α hα3 hcoset
  obtain ⟨b, hchar, hcard, -, ι, hιinj, hιrange⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof.exists_fixedPoints_reeGammaFieldAut hK β hβ
  have hrange : ((MulAut.conj x : ReeTag.F4.reeGamma K a ≃* ReeTag.F4.reeGamma K a).toMonoidHom.comp
      ι).range = CFSG.RankThree.PartTwo.Sec4.autFix α := by
    ext z
    rw [CFSG.RankThree.PartTwo.KFacts.mem_range_conj_comp_iff (MulAut.conj x)
      (ReeTag.F4.reeGammaFieldAut K a β) ι hιrange z, ← hx]
    rfl
  have : Finite (CFSG.LieType.Chevalley.fixSubfield β) := Subtype.finite
  exact ⟨b, CFSG.LieType.Chevalley.fixSubfield β, inferInstance, inferInstance, hchar, hcard,
    ⟨(MulEquiv.subgroupCongr hrange).symm.trans
      (MonoidHom.ofInjective ((MulAut.conj x).injective.comp hιinj)).symm⟩⟩

end Cent

section Marking


theorem l154_marking_unitary_three {L : Type} [Group L] {n : ℕ} (rel : L → L → Prop)
    (h₁ : LargeEvenMarking L fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ rel φ)
    (h₂ : LargeEvenMarking L fun lab _ _ _ _ _ =>
      markTag lab = .PSU ∧ markRank lab = 3 ∧ markChar lab = 2 ∧ markDeg lab = n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ n) ^ 2 ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)),
        ∃ ψ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
          (LargeEvenGUSet (Fin 3) K (2 ^ n)), LargeEvenInduces θ rel ψ := by
  obtain ⟨-, lab, hlab, hraw⟩ := MI.marking_transport rel h₁ h₂
  obtain ⟨R, _, I, F, -, -, θ₀, ⟨ht, hr, hc, hd⟩, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hl := l154_label_twA_of_mark ht hr hc hd
  subst hl
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeUnitary] at hraw
  obtain ⟨K, _, _, hK, -, -, θ, -, ψ, hψI, hind⟩ := hraw
  exact ⟨K, inferInstance, inferInstance, hK, θ, ψ, hψI, hind⟩

end Marking

section Main


theorem l154ReeThreeRes_holds : L154ReeThreeRes := by
  intro a K _ _ _ ha hK s φ hs hφ3 hφout hφs hM
  classical
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hφ1 : φ ≠ 1 := fun h => hφout 1 (by rw [h, map_one])
  have hφin : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ := fun ⟨g, hg⟩ => hφout g hg.symm
  have hodd : Odd (2 * a + 1) := odd_two_mul_add_one a
  have hq : 2 < 2 ^ (2 * a + 1) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 2 * a + 1))
  set C := Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a)) with hC
  have hφC : ∀ z ∈ C, φ z ∈ C := by
    intro z hz
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have := congrArg φ hz
    rwa [map_mul, map_mul, hφs] at this
  let φC : ↥C →* ↥C :=
    ((φ : ReeTag.F4.reeGamma K a ≃* ReeTag.F4.reeGamma K a).toMonoidHom.comp
      C.subtype).codRestrict C (fun z => hφC z z.2)
  have hφC_val : ∀ z : ↥C, ((φC z : ↥C) : ReeTag.F4.reeGamma K a) = φ z := fun z => rfl
  obtain ⟨F, _, _, hF, ⟨ι⟩⟩ := l154_ree_three_su hK hs
  have hLM := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hM.1
    (l154_ree_three_lieModel ha hK hs)
  obtain ⟨K', _, _, hK', θ, ψ, hψI, hind⟩ := l154_marking_unitary_three (n := 2 * a + 1) _ hM hLM
  have hind' : ∀ l : ↥C, ψ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (φC l)) :=
    fun l => hind l (φC l) rfl
  obtain ⟨b, k', _, _, _, hk', ⟨φ'⟩⟩ := l154_ree_autFix_equiv ha hK hφ3 hφin
  obtain ⟨⟨s', hs'C, hs'⟩, u, huC, hφu, hu4, hu2⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.exists_fixed_pow_four_of_ree ha hK
      (MulEquiv.refl _) hφ3 hφ1 hk' φ' hφC hF ι
  have h : UnitaryFieldData 2 (2 * a + 1) K' :=
    ⟨Nat.prime_two, by omega, by rw [hK', ← pow_mul, mul_comm]⟩
  have hφ3' : ∀ z, φ (φ (φ z)) = z := fun z => by
    have := DFunLike.congr_fun hφ3 z
    simpa [pow_succ, MulAut.mul_apply] using this
  have hZ : Nat.card (Subgroup.center ↥C) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr ι).toEquiv]
    exact CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.card_center_statedSU_three hodd
      (by omega) hF
  have hall := l154_marking_fixed φC θ ψ hM.1 hZ
    (fun z => Subtype.ext (by simp only [hφC_val, hφ3'])) hind'
    (fun h3 y hy hy4 hy2 => l154_conjImage_eq_one h hodd hq hψI h3 hy hy4 hy2)
    (u := ⟨u, huC⟩) (Subtype.ext hφu) (Subtype.ext (by simpa using hu4))
    (fun h1 => hu2 (by simpa using congrArg Subtype.val h1))
  exact hs' (congrArg Subtype.val (hall ⟨s', hs'C⟩))

end Main

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
