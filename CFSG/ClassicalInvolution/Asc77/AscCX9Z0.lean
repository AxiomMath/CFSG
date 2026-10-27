module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X5

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {F : Type} [Field F] {Y : Type} [Group Y] [Finite Y] (T : Subgroup Y)
  (ψ : StatedSp 2 F →* ↥T) {A A' : Subgroup Y} (hAT : A ≤ T) (hA'T : A' ≤ T)
  (hψA : (longRootSp2 F 2 0).map (T.subtype.comp ψ) = A)
  (hψA' : (longRootSp2 F 2 1).map (T.subtype.comp ψ) = A')

include hψA hψA' in
theorem map_mem_of_famT' (h2 : (2 : F) ≠ 0) {Φ : Set (Subgroup Y)} (hA : A ∈ Φ) (hA' : A' ∈ Φ)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) {L : Subgroup ↥T} (hL : L ∈ famT ψ) :
    L.map T.subtype ∈ Φ := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨i, ⟨k, g, hPk, -⟩, -⟩ := exists_isLongRootSp2_of_isHyperbolicPlane h2 hP
  rw [Subgroup.map_map, hPk, ← conjSub_map]
  have hk : ∀ k : Fin 2, (longRootSp2 F 2 k).map (T.subtype.comp ψ) ∈ Φ := by
    intro k
    fin_cases k
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, hψA]
      exact hA
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, hψA']
      exact hA'
  exact hconj _ (hk k) _

include hψA hψA' in
theorem map_mem_RSet_of_famT' (h2 : (2 : F) ≠ 0) {Φ : Set (Subgroup Y)} (hA : A ∈ Φ)
    (hA' : A' ∈ Φ) (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) {R : Subgroup ↥T}
    (hR : R ∈ RSet (famT ψ)) : R.map T.subtype ∈ RSet Φ := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact mem_RSet_of_isSylow2In (map_mem_of_famT' T ψ hψA hψA' h2 hA hA' hconj hJ)
    (isSylow2In_map_of_injOn T.subtype (fun x _ hx => Subtype.ext hx) hRJ)

include hψA hψA' in
theorem map_mem_omegaNbr' (h2 : (2 : F) ≠ 0) {Φ : Set (Subgroup Y)} (hA : A ∈ Φ)
    (hA' : A' ∈ Φ) (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) {B : Subgroup Y} (hB : B ≤ T)
    {M : Subgroup ↥T} (hM : M ∈ omegaNbr (famT ψ) (B.subgroupOf T)) :
    M.map T.subtype ∈ omegaNbr Φ B := by
  obtain ⟨hMf, hne, R, hR, hRM, hRN⟩ := hM
  refine ⟨map_mem_of_famT' T ψ hψA hψA' h2 hA hA' hconj hMf, fun h => hne ?_,
    R.map T.subtype, map_mem_RSet_of_famT' T ψ hψA hψA' h2 hA hA' hconj hR,
    Subgroup.map_mono hRM, ?_⟩
  · apply Subgroup.map_injective T.subtype_injective
    rw [h, Subgroup.map_subgroupOf_eq_of_le hB]
  · rintro _ ⟨r, hr, rfl⟩
    exact mem_normalizer_of_subgroupOf T hB (hRN hr)

include hψA hψA' in
theorem map_longRoot_eq_subgroupOf (k : Fin 2) {B : Subgroup Y} (hB : B ≤ T)
    (hk : (longRootSp2 F 2 k).map (T.subtype.comp ψ) = B) :
    (longRootSp2 F 2 k).map ψ = B.subgroupOf T := by
  apply Subgroup.map_injective T.subtype_injective
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hB, hk]

include hψA hψA' in
theorem twinSect0_cover (h2 : (2 : F) ≠ 0) {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y}
    (htw : TwinSect0 Φ A A' z' a₀ b₀) (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) :
    TwinSect0 (famT ψ) (A.subgroupOf T) (A'.subgroupOf T) ⟨z', hAT htw.hzA.mem⟩
      ⟨a₀, hAT htw.ha₀⟩ ⟨b₀, hA'T htw.hb₀⟩ where
  hA := ⟨stdPlane F 2 0, isHyperbolicPlane_stdPlane 0, by
    rw [planeGroup_stdPlane, map_longRoot_eq_subgroupOf T ψ hψA hψA' 0 hAT hψA]⟩
  hA' := ⟨stdPlane F 2 1, isHyperbolicPlane_stdPlane 1, by
    rw [planeGroup_stdPlane, map_longRoot_eq_subgroupOf T ψ hψA hψA' 1 hA'T hψA']⟩
  ne := fun h => htw.ne (by
    have := congrArg (fun B => B.map T.subtype) h
    simpa only [Subgroup.map_subgroupOf_eq_of_le hAT, Subgroup.map_subgroupOf_eq_of_le hA'T]
      using this)
  hzA := isUniqueInvolution_subgroupOf htw.hzA hAT
  hzA' := isUniqueInvolution_subgroupOf htw.hzA' hA'T
  ha₀ := Subgroup.mem_subgroupOf.mpr htw.ha₀
  hb₀ := Subgroup.mem_subgroupOf.mpr htw.hb₀
  ha₀sq := Subtype.ext htw.ha₀sq
  hb₀sq := Subtype.ext htw.hb₀sq
  nbA := fun M hM hMn => by
    have h1 := htw.nbA _ (map_mem_of_famT' T ψ hψA hψA' h2 htw.hA htw.hA' hconj hM)
      (map_mem_omegaNbr' T ψ hψA hψA' h2 htw.hA htw.hA' hconj hAT hMn)
    apply Subgroup.map_injective T.subtype_injective
    rw [h1, Subgroup.map_subgroupOf_eq_of_le hA'T]
  nbA' := fun M hM hMn => by
    have h1 := htw.nbA' _ (map_mem_of_famT' T ψ hψA hψA' h2 htw.hA htw.hA' hconj hM)
      (map_mem_omegaNbr' T ψ hψA hψA' h2 htw.hA htw.hA' hconj hA'T hMn)
    apply Subgroup.map_injective T.subtype_injective
    rw [h1, Subgroup.map_subgroupOf_eq_of_le hAT]

section Lie

variable {p f : ℕ} [Fact p.Prime]


@[expose] def lieCover (hf : 1 ≤ f) (hq : 5 ≤ p ^ f) {Y : Type} [Group Y] (T : Subgroup Y)
    (ψ : StatedSp 2 (GaloisField p f) →* ↥T) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField p f))) :
    LieSystemData p f ↥T (famT ψ) where
  card := 1
  tag := fun _ => .PSp
  rank := fun _ => 2
  exp := fun _ => f
  hom := fun _ => ψ
  isFundTag := fun _ => trivial
  admissible := fun _ => ⟨Fact.out, hf, le_refl 2, fun h => by
    have : p ^ f = 2 := (Prod.mk.inj h).2
    omega⟩
  exp_eq := fun _ => Or.inl rfl
  ker_le_center := fun _ => hker
  commute := fun i j hij => absurd (Subsingleton.elim i j) hij
  generate := eq_top_iff.mpr fun x _ => Subgroup.mem_iSup_of_mem 0 (hsurj x)
  fundamental := by
    rintro L ⟨P, hP, rfl⟩
    refine ⟨0, planeGroup P, (mem_fundamentalSubgroups_PSp_iff ⟨Fact.out, hf, le_refl 2,
      fun h => by have : p ^ f = 2 := (Prod.mk.inj h).2; omega⟩ _).mpr ⟨P, hP, rfl⟩, rfl⟩
  meets := fun _ => ⟨planeGroup (stdPlane (GaloisField p f) 2 0),
    (mem_fundamentalSubgroups_PSp_iff ⟨Fact.out, hf, le_refl 2,
      fun h => by have : p ^ f = 2 := (Prod.mk.inj h).2; omega⟩ _).mpr
      ⟨_, isHyperbolicPlane_stdPlane 0, rfl⟩,
    ⟨_, isHyperbolicPlane_stdPlane 0, rfl⟩⟩

theorem om5Data_of_cover (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Y : Type} [Group Y] [Finite Y]
    (T : Subgroup Y) (ψ : StatedSp 2 (GaloisField p f) →* ↥T) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField p f))) {A A' : Subgroup Y}
    (hAT : A ≤ T) (hA'T : A' ≤ T)
    (hψA : (longRootSp2 (GaloisField p f) 2 0).map (T.subtype.comp ψ) = A)
    (hψA' : (longRootSp2 (GaloisField p f) 2 1).map (T.subtype.comp ψ) = A')
    {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y} (htw : TwinSect0 Φ A A' z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) :
    C5O.Om5Data p f ↥T (famT ψ) (A.subgroupOf T) (A'.subgroupOf T) ⟨z', hAT htw.hzA.mem⟩
      ⟨a₀, hAT htw.ha₀⟩ ⟨b₀, hA'T htw.hb₀⟩ := by
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
  exact ⟨hp2, hq, ⟨lieCover hf hq T ψ hsurj hker, rfl, ⟨0, Nat.one_pos⟩,
    Or.inl ⟨rfl, rfl, rfl⟩⟩, twinSect0_cover T ψ hAT hA'T hψA hψA' h2 htw hconj,
    fun J hJ y => conjSub_mem_famT hsurj hJ y⟩

end Lie

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
