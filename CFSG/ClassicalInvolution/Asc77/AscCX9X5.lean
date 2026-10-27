module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X4

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups

variable {F : Type} [Field F] {Y : Type} [Group Y] [Finite Y]
variable {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) (θ : SL(4, F) →* Y) (T : Subgroup Y)
  (hT : T = (spM (spForm m n)).map θ)

theorem map_mem_of_famT (h2 : (2 : F) ≠ 0) {Φ : Set (Subgroup Y)}
    (hA : (blockSL F 4 2 0 (by norm_num)).range.map θ ∈ Φ)
    (hA' : (blockSL F 4 2 2 (by norm_num)).range.map θ ∈ Φ)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) {L : Subgroup ↥T}
    (hL : L ∈ famT (homT hm hn θ T hT)) : L.map T.subtype ∈ Φ := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨i, ⟨k, g, hPk, -⟩, -⟩ := exists_isLongRootSp2_of_isHyperbolicPlane h2 hP
  rw [Subgroup.map_map, subtype_comp_homT, hPk, ← conjSub_map]
  have hk : ∀ k : Fin 2, (longRootSp2 F 2 k).map (θ.comp (kappa hm hn)) ∈ Φ := by
    intro k
    rw [← Subgroup.map_map]
    fin_cases k
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, kappa_longRoot0]
      exact hA
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, kappa_longRoot1]
      exact hA'
  exact hconj _ (hk k) _

theorem map_mem_RSet_of_famT (h2 : (2 : F) ≠ 0) {Φ : Set (Subgroup Y)}
    (hA : (blockSL F 4 2 0 (by norm_num)).range.map θ ∈ Φ)
    (hA' : (blockSL F 4 2 2 (by norm_num)).range.map θ ∈ Φ)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) {R : Subgroup ↥T}
    (hR : R ∈ RSet (famT (homT hm hn θ T hT))) : R.map T.subtype ∈ RSet Φ := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact mem_RSet_of_isSylow2In (map_mem_of_famT hm hn θ T hT h2 hA hA' hconj hJ)
    (isSylow2In_map_of_injOn T.subtype (fun x _ hx => Subtype.ext hx) hRJ)

theorem mem_normalizer_of_subgroupOf {B : Subgroup Y} (hB : B ≤ T) {r : ↥T}
    (hr : r ∈ Subgroup.normalizer ((B.subgroupOf T : Subgroup ↥T) : Set ↥T)) :
    (r : Y) ∈ Subgroup.normalizer (B : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hr ⊢
  intro a
  constructor
  · intro ha
    have h1 := (hr ⟨a, hB ha⟩).mp (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.mem_subgroupOf.mp h1
  · intro ha
    have haT : a ∈ T := by
      have e : a = (r : Y)⁻¹ * ((r : Y) * a * (r : Y)⁻¹) * r := by group
      rw [e]
      exact T.mul_mem (T.mul_mem (T.inv_mem r.2) (hB ha)) r.2
    have h1 := (hr ⟨a, haT⟩).mpr (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.mem_subgroupOf.mp h1

theorem map_mem_omegaNbr (h2 : (2 : F) ≠ 0) {Φ : Set (Subgroup Y)}
    (hA : (blockSL F 4 2 0 (by norm_num)).range.map θ ∈ Φ)
    (hA' : (blockSL F 4 2 2 (by norm_num)).range.map θ ∈ Φ)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) {B : Subgroup Y} (hB : B ≤ T)
    {M : Subgroup ↥T} (hM : M ∈ omegaNbr (famT (homT hm hn θ T hT)) (B.subgroupOf T)) :
    M.map T.subtype ∈ omegaNbr Φ B := by
  obtain ⟨hMf, hne, R, hR, hRM, hRN⟩ := hM
  refine ⟨map_mem_of_famT hm hn θ T hT h2 hA hA' hconj hMf, fun h => hne ?_,
    R.map T.subtype, map_mem_RSet_of_famT hm hn θ T hT h2 hA hA' hconj hR,
    Subgroup.map_mono hRM, ?_⟩
  · apply Subgroup.map_injective T.subtype_injective
    rw [h, Subgroup.map_subgroupOf_eq_of_le hB]
  · rintro _ ⟨r, hr, rfl⟩
    exact mem_normalizer_of_subgroupOf T hB (hRN hr)

theorem twinSect0_T (h2 : (2 : F) ≠ 0) {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y}
    (htw : TwinSect0 Φ ((blockSL F 4 2 0 (by norm_num)).range.map θ)
      ((blockSL F 4 2 2 (by norm_num)).range.map θ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) :
    TwinSect0 (famT (homT hm hn θ T hT))
      (((blockSL F 4 2 0 (by norm_num)).range.map θ).subgroupOf T)
      (((blockSL F 4 2 2 (by norm_num)).range.map θ).subgroupOf T)
      ⟨z', block0_le_T θ T hT htw.hzA.mem⟩ ⟨a₀, block0_le_T θ T hT htw.ha₀⟩
      ⟨b₀, block2_le_T θ T hT htw.hb₀⟩ where
  hA := ⟨stdPlane F 2 0, isHyperbolicPlane_stdPlane 0, by
    rw [planeGroup_stdPlane, map_homT_longRoot0]⟩
  hA' := ⟨stdPlane F 2 1, isHyperbolicPlane_stdPlane 1, by
    rw [planeGroup_stdPlane, map_homT_longRoot1]⟩
  ne := fun h => htw.ne (by
    have := congrArg (fun B => B.map T.subtype) h
    simpa only [Subgroup.map_subgroupOf_eq_of_le (block0_le_T θ T hT),
      Subgroup.map_subgroupOf_eq_of_le (block2_le_T θ T hT)] using this)
  hzA := isUniqueInvolution_subgroupOf htw.hzA (block0_le_T θ T hT)
  hzA' := isUniqueInvolution_subgroupOf htw.hzA' (block2_le_T θ T hT)
  ha₀ := Subgroup.mem_subgroupOf.mpr htw.ha₀
  hb₀ := Subgroup.mem_subgroupOf.mpr htw.hb₀
  ha₀sq := Subtype.ext htw.ha₀sq
  hb₀sq := Subtype.ext htw.hb₀sq
  nbA := fun M hM hMn => by
    have h1 := htw.nbA _ (map_mem_of_famT hm hn θ T hT h2 htw.hA htw.hA' hconj hM)
      (map_mem_omegaNbr hm hn θ T hT h2 htw.hA htw.hA' hconj (block0_le_T θ T hT) hMn)
    apply Subgroup.map_injective T.subtype_injective
    rw [h1, Subgroup.map_subgroupOf_eq_of_le (block2_le_T θ T hT)]
  nbA' := fun M hM hMn => by
    have h1 := htw.nbA' _ (map_mem_of_famT hm hn θ T hT h2 htw.hA htw.hA' hconj hM)
      (map_mem_omegaNbr hm hn θ T hT h2 htw.hA htw.hA' hconj (block2_le_T θ T hT) hMn)
    apply Subgroup.map_injective T.subtype_injective
    rw [h1, Subgroup.map_subgroupOf_eq_of_le (block0_le_T θ T hT)]

section Lie

variable {p f : ℕ} [Fact p.Prime]


@[expose] def lieT (hf : 1 ≤ f) (hq : 5 ≤ p ^ f) {m n : GaloisField p f} (hm : m ≠ 0)
    (hn : n ≠ 0) (θ : SL(4, GaloisField p f) →* Y)
    (hker : θ.ker = scalars 4 (GaloisField p f)) (T : Subgroup Y)
    (hT : T = (spM (spForm m n)).map θ) :
    LieSystemData p f ↥T (famT (homT hm hn θ T hT)) where
  card := 1
  tag := fun _ => .PSp
  rank := fun _ => 2
  exp := fun _ => f
  hom := fun _ => homT hm hn θ T hT
  isFundTag := fun _ => trivial
  admissible := fun _ => ⟨Fact.out, hf, le_refl 2, fun h => by
    have : p ^ f = 2 := (Prod.mk.inj h).2
    omega⟩
  exp_eq := fun _ => Or.inl rfl
  ker_le_center := fun _ => ker_homT_le_center hm hn θ T hT hker
  commute := fun i j hij => absurd (Subsingleton.elim i j) hij
  generate := eq_top_iff.mpr fun x _ =>
    Subgroup.mem_iSup_of_mem 0 (homT_surjective hm hn θ T hT x)
  fundamental := by
    rintro L ⟨P, hP, rfl⟩
    refine ⟨0, planeGroup P, (mem_fundamentalSubgroups_PSp_iff ⟨Fact.out, hf, le_refl 2,
      fun h => by have : p ^ f = 2 := (Prod.mk.inj h).2; omega⟩ _).mpr ⟨P, hP, rfl⟩, rfl⟩
  meets := fun _ => ⟨planeGroup (stdPlane (GaloisField p f) 2 0),
    (mem_fundamentalSubgroups_PSp_iff ⟨Fact.out, hf, le_refl 2,
      fun h => by have : p ^ f = 2 := (Prod.mk.inj h).2; omega⟩ _).mpr
      ⟨_, isHyperbolicPlane_stdPlane 0, rfl⟩,
    ⟨_, isHyperbolicPlane_stdPlane 0, rfl⟩⟩

theorem om5Data_T (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m n : GaloisField p f} (hm : m ≠ 0)
    (hn : n ≠ 0) (θ : SL(4, GaloisField p f) →* Y)
    (hker : θ.ker = scalars 4 (GaloisField p f)) (T : Subgroup Y)
    (hT : T = (spM (spForm m n)).map θ) {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y}
    (htw : TwinSect0 Φ ((blockSL (GaloisField p f) 4 2 0 (by norm_num)).range.map θ)
      ((blockSL (GaloisField p f) 4 2 2 (by norm_num)).range.map θ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) :
    C5O.Om5Data p f ↥T (famT (homT hm hn θ T hT))
      (((blockSL (GaloisField p f) 4 2 0 (by norm_num)).range.map θ).subgroupOf T)
      (((blockSL (GaloisField p f) 4 2 2 (by norm_num)).range.map θ).subgroupOf T)
      ⟨z', block0_le_T θ T hT htw.hzA.mem⟩ ⟨a₀, block0_le_T θ T hT htw.ha₀⟩
      ⟨b₀, block2_le_T θ T hT htw.hb₀⟩ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hq
      omega
    · exact h
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (GaloisField p f) p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)
  exact ⟨hp2, hq, ⟨lieT hf hq hm hn θ hker T hT, rfl, ⟨0, Nat.one_pos⟩,
    Or.inl ⟨rfl, rfl, rfl⟩⟩,
    twinSect0_T hm hn θ T hT h2 htw hconj,
    fun J hJ y => conjSub_mem_famT (homT_surjective hm hn θ T hT) hJ y⟩

end Lie

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
