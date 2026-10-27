module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphTowerParab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LargeFieldProof
public import CFSG.LargeExtraspecial.S14C10Sym3
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Tower

theorem hatOf_isSubnormal {A : Type} [Group A] {P T : Subgroup A}
    (hT : CFSG.Open.IsSubnormal T P) : CFSG.Open.IsSubnormal (hatOf P T) ⊤ := by
  have hsub : CFSG.Open.IsSubnormal (T.subgroupOf P) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib (CFSG.Open.IsSubnormal.subgroupOf hT)
  have h := CFSG.Open.IsSubnormal.map (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) hsub
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h

theorem hatOf_mulEquiv_of_pCoreOf_le {A : Type} [Group A] {P T : Subgroup A}
    (hTP : T ≤ P) (hpc : pCoreOf 2 T = pCoreOf 2 P) :
    Nonempty (↥(hatOf P T) ≃* ↥T ⧸ CFSG.pCore 2 ↥T) := by
  classical
  let π := QuotientGroup.mk' (CFSG.pCore 2 ↥P)
  let f : ↥T →* ↥P ⧸ CFSG.pCore 2 ↥P := π.comp (Subgroup.inclusion hTP)
  have hrange : f.range = hatOf P T := by
    dsimp only [f]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, hatOf]
  have hker : f.ker = CFSG.pCore 2 ↥T := by
    ext t
    rw [MonoidHom.mem_ker]
    constructor
    · intro ht
      have h1 : π (Subgroup.inclusion hTP t) = 1 := ht
      have h2 : Subgroup.inclusion hTP t ∈ CFSG.pCore 2 ↥P :=
        (QuotientGroup.eq_one_iff _).mp h1
      have h3 : ((t : A)) ∈ pCoreOf 2 P :=
        (CFSG.mem_openPCoreOf_iff (G := A) (p := 2) (H := P)
          (Subgroup.inclusion hTP t)).mpr h2
      rw [← hpc] at h3
      exact (CFSG.mem_openPCoreOf_iff (G := A) (p := 2) (H := T) t).mp h3
    · intro ht
      have h1 : ((t : A)) ∈ pCoreOf 2 T :=
        (CFSG.mem_openPCoreOf_iff (G := A) (p := 2) (H := T) t).mpr ht
      rw [hpc] at h1
      have h2 : Subgroup.inclusion hTP t ∈ CFSG.pCore 2 ↥P :=
        (CFSG.mem_openPCoreOf_iff (G := A) (p := 2) (H := P)
          (Subgroup.inclusion hTP t)).mp h1
      have h3 : π (Subgroup.inclusion hTP t) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h2
      simpa [f] using h3
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))).symm⟩

theorem hatOf_of_mem_cZero {A : Type} [Group A] [Finite A] {P T : Subgroup A}
    (hT : T ∈ cZero P) (hT3 : Nonempty (↥T ⧸ CFSG.pCore 2 ↥T ≃* Equiv.Perm (Fin 3))) :
    pCoreOf 2 P ≤ T ∧ IsSubnormal (hatOf P T) ⊤ ∧ Sym.IsSymThree (hatOf P T) := by
  classical
  have hTP : T ≤ P := hT.le
  have hnot : ¬ IsTwoPrimeComponent T T := by
    rintro ⟨-, -, hperf, -⟩
    obtain ⟨e⟩ := hT3
    haveI hperfT : Group.IsPerfect ↥T := Subgroup.isPerfect_iff.mpr hperf
    have hperfQ : Group.IsPerfect (↥T ⧸ CFSG.pCore 2 ↥T) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥T))
        (QuotientGroup.mk'_surjective _)
    haveI : Group.IsPerfect (↥T ⧸ CFSG.pCore 2 ↥T) := hperfQ
    have hperf3 : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hbot : (⊤ : Subgroup (Equiv.Perm (Fin 3))) = ⊥ :=
      CFSG.LargeExtraspecial.S14.eq_bot_of_perfect_perm_three
        (P := ⊤) hperf3.commutator_eq_top
    have hcard1 : Nat.card (Equiv.Perm (Fin 3)) = 1 := by
      rw [← Subgroup.card_top (G := Equiv.Perm (Fin 3)), hbot, Subgroup.card_bot]
    have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]
    omega
  have hpc : pCoreOf 2 T = pCoreOf 2 P := (hT.shape.resolve_left hnot).1
  have hOT : pCoreOf 2 P ≤ T := by
    rw [← hpc]
    exact CFSG.openPCoreOf_le 2 T
  refine ⟨hOT, hatOf_isSubnormal hT.subnormal, ?_⟩
  obtain ⟨e⟩ := hT3
  obtain ⟨e'⟩ := hatOf_mulEquiv_of_pCoreOf_le hTP hpc
  exact ⟨e'.trans e⟩

theorem preHatOf_hatOf_eq_of_le {A : Type} [Group A] {P T : Subgroup A} (hTP : T ≤ P)
    (hOT : pCoreOf 2 P ≤ T) : preHatOf P (hatOf P T) = T := by
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).ker ≤ T.subgroupOf P := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (hOT ((CFSG.mem_openPCoreOf_iff (G := A) (p := 2) (H := P) x).mpr hx))
  rw [preHatOf, hatOf, Subgroup.comap_map_eq, sup_eq_left.mpr hker,
    Subgroup.map_subgroupOf_eq_of_le hTP]

theorem le_normalizer_of_normal_hatOf {A : Type} [Group A] {P T : Subgroup A} (hTP : T ≤ P)
    (hOT : pCoreOf 2 P ≤ T) (hn : (hatOf P T).Normal) : P ≤ normalizer (T : Set A) := by
  have hpre := preHatOf_hatOf_eq_of_le hTP hOT
  have hnorm : ((preHatOf P (hatOf P T)).subgroupOf P).Normal := by
    have hsubeq : (preHatOf P (hatOf P T)).subgroupOf P =
        (hatOf P T).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) := by
      ext x
      rw [Subgroup.mem_subgroupOf, preHatOf]
      change P.subtype x ∈ (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
        (hatOf P T)).map P.subtype ↔
        x ∈ Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) (hatOf P T)
      rw [Subgroup.mem_map_iff_mem P.subtype_injective, Subgroup.mem_comap]
    rw [hsubeq]
    exact Subgroup.Normal.comap hn _
  rw [← hpre]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (preHatOf_le P (hatOf P T))).mp hnorm

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData in
theorem four_le_lieField_of_ne_two {i : TauCeti.LieTypeIndex} (hi : IsClassicalOrG2Index i)
    (h2 : LieField i ≠ 2) : 4 ≤ LieField i := by
  have hmain : ∀ q : TauCeti.PrimePower, q.p = 2 → q.card ≠ 2 → 4 ≤ q.card := by
    intro q hq h2
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
    have hpos := q.exponent_pos
    have hexp : 2 ≤ q.exponent := by
      by_contra h
      have h1 : q.exponent = 1 := by omega
      exact h2 (by rw [hcard, h1, pow_one])
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hexp
      _ = q.card := hcard.symm
  cases i <;> simp_all only [IsClassicalOrG2Index, LieField]
  all_goals
    apply hmain
    · assumption
    · assumption


open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData in
theorem lieField_eq_two_of_subnormal_symThree {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hY : IsQuasisimple ↥Y) (hP : IsParabolicTwo Y P)
    {U : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (hUs : IsSubnormal U ⊤) (hU : Sym.IsSymThree U)
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (he : Nonempty (↥Y ⧸ center ↥Y ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    LieField d.1 = 2 := by
  classical
  by_contra h2
  obtain ⟨P'', hpar'', hle, hnot, hsol⟩ := exists_solvThree_parabolic hP hU hUs
  have hYo : Open.IsQuasisimple ↥Y := ⟨hY.1.commutator_eq_top, hY.2.1⟩
  have h4 : 4 ≤ LieField d.1 := four_le_lieField_of_ne_two hd h2
  obtain ⟨J, hJP, hJperf, hJ3⟩ :=
    largeFieldParabolic_proved A Y P'' hYo d hd h4 he hpar'' hnot
  exact hsol J hJP hJperf hJ3

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma
