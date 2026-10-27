module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDNMain
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

structure Setting (X : Type) [Group X] [Finite X] (a : X) (L W K : Subgroup X) : Prop
    extends SingleComponentSetting X a L W K where
  loc : LocallyTwoBalanced X
  held : Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He)
  sylow : ∃ S : Subgroup X, IsSylowTwoIn S (normalizer (L : Set X)) ∧
    ∀ B : Subgroup X, B ≤ S → IsElemTwo B → Nat.card B = 8 → wGroup B = W
  wGroup_eq : ∃ A : Subgroup X, A ≤ L ∧ IsElemTwo A ∧ Nat.card A = 64 ∧ wGroup A = W

theorem setting_of
    (hS : SchreierFor Blueprint.Catalog)
    (hHN : HeldNotProperFixedInput) (h64 : HeldSylowElementarySixtyFour) {L : Subgroup X}
    (hset : HeldSetting X L) {S : Subgroup X} (hSyl : IsSylowTwoIn S (normalizer (L : Set X)))
    {W : Subgroup X} (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W))
    (hWB : ∀ B : Subgroup X, B ≤ S → IsElemTwo B → Nat.card B = 8 → wGroup B = W)
    (hNL : normalizer (L : Set X) ≤ normalizer (W : Set X)) {K : Subgroup X}
    (hKM : K ≤ normalizer (W : Set X))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set X))))
    (hsupM : L ⊔ oddIn (normalizer (W : Set X)) = K ⊔ oddIn (normalizer (W : Set X))) :
    ∃ a : X, Setting X a L W K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimp, hnab, hK, hU, hloc, ⟨a, ha2, hLa, hLc⟩, ⟨e⟩⟩ := id hset
  have : IsSimpleGroup X := hsimp
  have hHe := nonempty_fusionZStar_equiv_held e
  have hmax : GSWeakMaximalComponent L :=
    gsWeakMaximalComponent_of_held hS hHN hnab hK ha2 hLa hLc hHe
  have haN : a ∈ normalizer (L : Set X) := mem_normalizer_of_commute fun x hx =>
    (mem_centralizer_singleton_iff.mp (hLa hx)).symm
  obtain ⟨S₀, hSyl₀, -⟩ := exists_isSylowTwoIn_mem haN ha2
  obtain ⟨E, hET, -, hEe, hE64⟩ := exists_elem_sixtyFour e h64 inf_le_right
    (hSyl₀.isPGroup.to_le inf_le_left) (card_inf_eq_1024 e hSyl₀)
  have hrank : 3 ≤ pRank 2 ↥L := three_le_pRank_of_le hEe (by omega) (hET.trans inf_le_right)
  obtain ⟨A, hAT, -, hAe, hA64⟩ := exists_elem_sixtyFour e h64 inf_le_right
    (hSyl.isPGroup.to_le inf_le_left) (card_inf_eq_1024 e hSyl)
  obtain ⟨A₀, hA₀A, hA₀8⟩ := exists_le_card_eight hAe.isPGroup (by omega)
  have hGWB : GWTwoBalanced X :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hloc
  have hWA : wGroup A = W := (wGroup_eq_of_le_eight hGWB hAe hA₀A hA₀8).trans
    (hWB A₀ ((hA₀A.trans hAT).trans inf_le_left) (hAe.mono hA₀A) hA₀8)
  exact ⟨a, ⟨⟨⟨hsimp, hnab, hK, hU, ha2, hLa, hLc, hmax, hrank, Sol78.not_psp4_of_held e,
    Or.inr (nonempty_fusionZStar_equiv_held e)⟩, hW,
    hWodd, hNL, GrS4.normalizer_ne_top_of_odd hW hWodd ha2, hKM, hKc, hsupM⟩, hloc, ⟨e⟩,
    ⟨S, hSyl, hWB⟩, ⟨A, hAT.trans inf_le_right, hAe, hA64, hWA⟩⟩⟩

omit [Finite X] in
private theorem map_subtype_subgroupOf {M : Subgroup X} (L : Subgroup M) :
    (L.map M.subtype).subgroupOf M = L := by
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]

omit [Finite X] in
theorem not_odd_card_commutator
    {J A B : Subgroup X}
    (e : J ⧸ pPrimeCore 2 ↥J ≃* Blueprint.NativeSporadic.He) (hAJ : A ≤ J) (hBJ : B ≤ J)
    (hA : A ⊔ oddIn J = J) (hB : B ⊔ oddIn J = J) : ¬ Odd (Nat.card ↥⁅A, B⁆) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup ↥heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He heEquivP.symm
  have hφs := heModelL_surjective e
  have hP : (pPrimeCore 2 ↥J).map (heModelL e) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    exact (heModelL_eq_one_iff e x).mpr hx
  have hcov : ∀ {C : Subgroup X}, C ≤ J → C ⊔ oddIn J = J →
      (C.subgroupOf J).map (heModelL e) = ⊤ := by
    intro C hCJ hC
    have h1 : C.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := by
      have h2 := congrArg (fun H : Subgroup X => H.subgroupOf J) hC
      unfold oddIn at h2
      rwa [subgroupOf_sup hCJ (map_subtype_le _), map_subtype_subgroupOf,
        subgroupOf_self] at h2
    have h3 : (⊤ : Subgroup ↥J).map (heModelL e) = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hφs]
    rwa [← h1, Subgroup.map_sup, hP, sup_bot_eq] at h3
  intro hodd
  have hcomm : (⁅A.subgroupOf J, B.subgroupOf J⁆).map (heModelL e) =
      ⁅(⊤ : Subgroup ↥heP), (⊤ : Subgroup ↥heP)⁆ := by
    rw [map_commutator, hcov hAJ hA, hcov hBJ hB]
  have hcard : Nat.card ↥⁅A.subgroupOf J, B.subgroupOf J⁆ = Nat.card ↥⁅A, B⁆ := by
    rw [← card_map_of_injective J.subtype_injective, map_commutator,
      subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hAJ, inf_of_le_left hBJ]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (⁅(⊤ : Subgroup ↥heP), (⊤ : Subgroup ↥heP)⁆) with hb | ht
  · obtain ⟨x, y, hxy⟩ := exists_mul_ne_held
    apply hxy
    apply heEquivP.injective
    rw [map_mul, map_mul]
    have hx := commutator_eq_bot_iff_le_centralizer.mp hb (mem_top (heEquivP x))
    exact ((mem_centralizer_iff.mp hx) (heEquivP y) (mem_top _)).symm
  · have hdvd := card_map_dvd (⁅A.subgroupOf J, B.subgroupOf J⁆) (heModelL e)
    rw [hcomm, ht, card_top, card_heP, hcard] at hdvd
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat hdvd)) (by decide)

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)
include h

theorem gwTwoBalanced : GWTwoBalanced X :=
  gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput h.loc

theorem le_K : L ≤ K := GrS4.le_of_singleComponentSetting h.toSingleComponentSetting

theorem K_eq : K = L ⊔ oddIn K :=
  GrS4.eq_sup_oddIn_of_singleComponentSetting h.toSingleComponentSetting

theorem oddIn_L : oddIn L = L ⊓ oddIn (normalizer (W : Set X)) :=
  GrS4.oddIn_eq_inf_of_singleComponentSetting h.toSingleComponentSetting

theorem oddIn_K_le : oddIn K ≤ oddIn (normalizer (W : Set X)) :=
  GSLit.map_pPrimeCore_le_of_isPComponent h.le_normalizer h.isPComponent_K

theorem oddIn_L' : oddIn L = L ⊓ oddIn K := by
  rw [h.oddIn_L]
  refine le_antisymm (fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).1, ?_⟩)
    (inf_le_inf_left _ h.oddIn_K_le)
  exact GrS5.inf_oddIn_le_oddIn h.le_normalizer
    (mem_inf.mpr ⟨(mem_inf.mp hx).2, h.le_K (mem_inf.mp hx).1⟩)

theorem heldK : Nonempty (K ⧸ pPrimeCore 2 K ≃* Blueprint.NativeSporadic.He) := by
  obtain ⟨e⟩ := h.held
  obtain ⟨f, -⟩ := exists_quotient_equiv_of_sup h.le_K h.K_eq.symm h.oddIn_L'
  exact ⟨f.symm.trans e⟩

theorem isHeldType : IsHeldType (L ⧸ Open.fusionZStar L) := by
  obtain ⟨e⟩ := h.held
  exact nonempty_fusionZStar_equiv_held e

theorem centralizer_le_normalizer
    (hMax : MaximalTwoComponentInputHe) :
    centralizer ({a} : Set X) ≤ normalizer (L : Set X) := by
  have : IsSimpleGroup X := h.simple
  exact GrS4.centralizer_le_normalizer_of_gsMaximalSetting_he hMax h.toGSMaximalSetting
    h.isHeldType

theorem centralizer_le (hMax : MaximalTwoComponentInputHe) :
    centralizer ({a} : Set X) ≤ normalizer (W : Set X) := by
  have : IsSimpleGroup X := h.simple
  exact GrS4.centralizer_le_of_singleComponentSetting_he hMax h.toSingleComponentSetting
    h.isHeldType

theorem mem_M (hMax : MaximalTwoComponentInputHe) :
    a ∈ normalizer (W : Set X) :=
  h.centralizer_le hMax (mem_centralizer_singleton_iff.mpr rfl)

theorem mem_kernel (hMax : MaximalTwoComponentInputHe) :
    a ∈ coreActionKernel K := by
  have : IsSimpleGroup X := h.simple
  exact GrS4.mem_coreActionKernel_of_singleComponentSetting_he hMax h.toSingleComponentSetting
    h.isHeldType

theorem exists_target
    (hMax : MaximalTwoComponentInputHe)
    (hS : SchreierFor Blueprint.Catalog) (hHN : HeldNotProperFixedInput)
    (h64 : HeldSylowElementarySixtyFour) (hMult : TBLit.HeldTrivialMultiplier) {s : X}
    (hs : orderOf s = 2) (has : a * s = s * a) (hsK : s ∈ coreActionKernel K) :
    ∃ L' : Subgroup X, L' ≤ centralizer ({s} : Set X) ∧
      IsPComponent 2 (L'.subgroupOf (centralizer ({s} : Set X))) ∧
      centralizer ({s} : Set X) ≤ normalizer (L' : Set X) ∧
      Nonempty (L' ⧸ pPrimeCore 2 L' ≃* Blueprint.NativeSporadic.He) ∧
      gsFixedLayer L s ≤ L' ∧ gsFixedLayer L s ⊔ oddIn L' = L' := by
  have : IsSimpleGroup X := h.simple
  obtain ⟨e⟩ := h.held
  have hsL : s ∈ normalizer (L : Set X) :=
    h.centralizer_le_normalizer hMax (mem_centralizer_singleton_iff.mpr has.symm)
  have hLr : ∀ j ∈ L, j⁻¹ * s⁻¹ * j * s ∈ (pPrimeCore 2 L).map L.subtype := by
    intro j hj
    have h1 : j⁻¹ * s⁻¹ * j * s ∈ oddIn K := (mem_coreActionKernel.mp hsK).2 j (h.le_K hj)
    have h2 : j⁻¹ * s⁻¹ * j * s ∈ L := by
      have h3 := (mem_normalizer_iff.mp (inv_mem hsL) j).mp hj
      rw [inv_inv] at h3
      rw [show j⁻¹ * s⁻¹ * j * s = j⁻¹ * (s⁻¹ * j * s) by group]
      exact mul_mem (inv_mem hj) h3
    show _ ∈ oddIn L
    rw [h.oddIn_L']
    exact mem_inf.mpr ⟨h2, h1⟩
  exact HeDiag.exists_held_target hMax hS hHN h64 hMult h.nonabelian h.kProper h.notU
    h.orderOf_eq hs has h.le_centralizer h.isPComponent e hsL hLr

theorem mem_normalizer_of_commute
    (hMax : MaximalTwoComponentInputHe)
    (hS : SchreierFor Blueprint.Catalog) (hHN : HeldNotProperFixedInput)
    (h64 : HeldSylowElementarySixtyFour) (hMult : TBLit.HeldTrivialMultiplier) {s : X}
    (hs : orderOf s = 2) (has : a * s = s * a) (hsK : s ∈ coreActionKernel K) {m : X}
    (hm : m ∈ normalizer (W : Set X)) (hms : m * s = s * m) :
    m ∈ normalizer (K : Set X) := by
  obtain ⟨L', -, -, hCN, ⟨e'⟩, hFL', hFsup⟩ :=
    h.exists_target hMax hS hHN h64 hMult hs has hsK
  by_contra hmK
  set F : Subgroup X := gsFixedLayer L s with hFdef
  have hFK : F ≤ K := ((map_subtype_le _).trans inf_le_left).trans h.le_K
  have hmL' : m ∈ normalizer (L' : Set X) := hCN (mem_centralizer_singleton_iff.mpr hms)
  have hL'm : conjugate L' m = L' := conjugate_eq_of_mem_normalizer hmL'
  have hOm : conjugate (oddIn L') m = oddIn L' := conjugate_eq_of_mem_normalizer
    (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L' (pPrimeCore 2 L') hmL')
  have hFmL' : conjugate F m ≤ L' := by
    rw [← hL'm]
    exact map_mono hFL'
  have hFmsup : conjugate F m ⊔ oddIn L' = L' := by
    have h1 : conjugate (F ⊔ oddIn L') m = conjugate F m ⊔ conjugate (oddIn L') m :=
      Subgroup.map_sup _ _ _
    rw [hFsup, hL'm, hOm] at h1
    exact h1.symm
  have hKm : conjugate K m ≠ K := fun h' => hmK (mem_normalizer_of_conjugate_eq h')
  have hcomm : ⁅F, conjugate F m⁆ ≤ oddIn K :=
    (commutator_mono hFK (map_mono hFK)).trans
      ((GrS5.commutator_le_inf_oddIn h.le_normalizer (conjugate_le_of_mem h.le_normalizer hm)
        h.isPComponent_K (isPComponent_conjugate_subgroupOf hm h.isPComponent_K)
        fun e => hKm e.symm).trans inf_le_left)
  exact not_odd_card_commutator e' hFL' hFmL' hFsup hFmsup
    ((odd_card_map_pPrimeCore K).of_dvd_nat (card_dvd_of_le hcomm))

end Setting

end CFSG.ComponentClassification.GrSLit.HeSN
