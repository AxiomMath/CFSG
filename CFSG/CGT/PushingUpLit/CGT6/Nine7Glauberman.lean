module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoSeven
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionSylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG.Open
open CFSG.ComponentClassification
open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherComponentAction
open CFSG.ComponentClassification.AschbacherComponentInvolution
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly (InCatalog)
open scoped commutatorElement

@[expose] def GlaubermanAt (X : Type) [Group X] [Finite X] : Prop :=
  IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) → Even (Nat.card X) →
    ∀ (S : Sylow 2 X) (K : Subgroup (MulAut X)), Group.IsPerfect K →
      (∀ α ∈ K, ∀ s ∈ (S : Subgroup X), α s = s) → K = ⊥

section Quasisimple

variable {G : Type} [Group G]

theorem exists_noncomm_center_quotient {L : Subgroup G} (hL : QS L) :
    ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
  have h1 : commutator ↥L ≤ Subgroup.center ↥L := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center ↥L)) ⁅g₁, g₂⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcon _ _)
  have hcenter : Subgroup.center ↥L = ⊤ := eq_top_iff.2 (by rwa [hL.1] at h1)
  have hsub : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
    rw [hcenter]
    exact QuotientGroup.subsingleton_quotient_top
  obtain ⟨x, y, hxy⟩ := hsimple.toNontrivial.exists_pair_ne
  exact hxy (Subsingleton.elim x y)

end Quasisimple

section Local

variable {G : Type} [Group G] [Finite G]

theorem centralizes_of_centralizes_sylow_at (K L : Subgroup G) [Group.IsPerfect K] (hL : QS L)
    (hglaub : GlaubermanAt (↥L ⧸ Subgroup.center ↥L))
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) (P : Sylow 2 L)
    (hKP : K ≤ Subgroup.centralizer (((P : Subgroup L).map L.subtype : Subgroup G) : Set G)) :
    ⁅K, L⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := ⟨hL.1⟩
  let φ : K →* MulAut (L ⧸ Subgroup.center L) :=
    (PerfectAutomorphisms.centerQuotientHom L).comp
      (L.normalizerMonoidHom.comp (Subgroup.inclusion hKL))
  let Sb : Sylow 2 (L ⧸ Subgroup.center L) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L))
  have hfix : ∀ α ∈ φ.range, ∀ s ∈ (Sb : Subgroup (L ⧸ Subgroup.center L)), α s = s := by
    rintro _ ⟨k, rfl⟩ s hs
    have hs' : s ∈ (P : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L)) := hs
    obtain ⟨p, hp, rfl⟩ := hs'
    change PerfectAutomorphisms.onCenterQuotient
      (L.normalizerMonoidHom (Subgroup.inclusion hKL k))
      (QuotientGroup.mk' (Subgroup.center L) p) = QuotientGroup.mk' (Subgroup.center L) p
    rw [PerfectAutomorphisms.onCenterQuotient_apply_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hpS : (p : G) ∈ (P : Subgroup L).map L.subtype := ⟨p, hp, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp (hKP k.2) (p : G) hpS
    change (k : G) * p * (k : G)⁻¹ = p
    rw [← hcomm, mul_inv_cancel_right]
  have hbot : φ.range = ⊥ :=
    hglaub hL.2 (exists_noncomm_center_quotient hL) (even_card_center_quotient L hL) Sb φ.range
      (Group.IsPerfect.range φ) hfix
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  have h1 : φ ⟨k, hk⟩ = 1 := by
    have hmem : φ ⟨k, hk⟩ ∈ φ.range := ⟨⟨k, hk⟩, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at hmem
  have h2 : L.normalizerMonoidHom (Subgroup.inclusion hKL ⟨k, hk⟩) = 1 :=
    PerfectAutomorphisms.centerQuotientHom_injective L (h1.trans (map_one _).symm)
  have h3 : Subgroup.inclusion hKL ⟨k, hk⟩ ∈ L.normalizerMonoidHom.ker := h2
  rw [Subgroup.normalizerMonoidHom_ker] at h3
  exact h3

theorem lemma_2_7_two_at (a : G) (ha : orderOf a = 2)
    (K L : Subgroup G) (hglaub : GlaubermanAt (↥L ⧸ Subgroup.center ↥L))
    (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (hL : IsComponentOf L ⊤) :
    K = L ∨ ⁅K, L⁆ = ⊥ ∨
      (rightComponent L a ≠ L ∧
        K = ⁅⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G),
          ⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G)⁆) ∨
      (⁅L, Subgroup.zpowers a⁆ = L ∧ K ≤ L) := by
  by_cases hmoved : rightComponent L a ≠ L
  · rcases moved_component_alternative a ha K L hKC hK hL hmoved with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨hmoved, h⟩))
  rw [not_not] at hmoved
  have haL : a ∈ Subgroup.normalizer (L : Set G) :=
    (rightComponent_eq_iff_normalizer L a).mp hmoved
  by_cases hcent : a ∈ Subgroup.centralizer (L : Set G)
  · rcases centralized_component_alternative a K L hKC hK hL hcent with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hLa : ⁅L, Subgroup.zpowers a⁆ = L := by
    apply le_antisymm
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr haL)
    · exact (component_arbitrary_action L _ hL).resolve_right
        (fun h => hcent ((cyclic_commutator_trivial_iff L a).mp h))
  obtain ⟨S, hSL, htwo, haS, hKS, hmax⟩ := exists_maximal_invariant_two L K a
  rcases maximal_invariant_two_sylow_alternative a ha K L S hKC hK hL haL hSL htwo haS hKS hmax
    with hKL | ⟨P, hPS, hKcS, -⟩
  · exact Or.inr (Or.inr (Or.inr ⟨hLa, hKL⟩))
  · right
    left
    have hKq : QS K := ((OrdinaryComponentTransport.subgroupOf_iff K _ hKC).mp hK).2
    have : Group.IsPerfect K := ⟨hKq.1⟩
    exact centralizes_of_centralizes_sylow_at K L hL.2.2 hglaub
      (involution_component_normalizes a ha K hKC hK L hL) P (hPS ▸ hKcS)

end Local

section Schreier

theorem isSolvable_centralizer_sylow {X : Type} [Group X] [Finite X] (S : Sylow 2 X) :
    Group.IsSolvable ↥(Subgroup.centralizer (S : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := Subgroup.centralizer (S : Set X) with hC
  let P : Sylow 2 C := default
  have hPle : (P : Subgroup C).map C.subtype ≤ (S : Subgroup X) := by
    have hnorm : (P : Subgroup C).map C.subtype ≤ Subgroup.normalizer (S : Set X) := by
      rintro _ ⟨y, -, rfl⟩
      exact Subgroup.centralizer_le_normalizer (S : Set X) y.2
    have hpg : IsPGroup 2 ((P : Subgroup C).map C.subtype) := P.isPGroup'.map C.subtype
    have := S.is_maximal' (hpg.to_sup_of_normal_right' S.isPGroup' hnorm) le_sup_right
    exact le_sup_left.trans this.le
  have hcentral : ∀ y ∈ (P : Subgroup C), y ∈ Subgroup.center C := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro c
    have hyS : (y : X) ∈ (S : Subgroup X) := hPle ⟨y, hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 c.2 (y : X) hyS).symm
  have hP : Subgroup.normalizer (P : Set C) ≤ Subgroup.centralizer (P : Set C) := by
    intro n _ y hy
    exact (Subgroup.mem_center_iff.1 (hcentral y hy) n).symm
  have hodd : Odd (Nat.card (MonoidHom.transferSylow P hP).ker) := by
    have := MonoidHom.not_dvd_card_ker_transferSylow P hP
    exact Nat.odd_iff.2 (by omega)
  have hsolvK : Group.IsSolvable (MonoidHom.transferSylow P hP).ker :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsolvP : Group.IsSolvable ↥(P : Subgroup C) := by
    apply Group.isSolvable_of_comm
    intro a b
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hcentral b b.2) a)
  exact Group.isSolvable_of_ker_le_range (MonoidHom.transferSylow P hP).ker.subtype
    (MonoidHom.transferSylow P hP) (by simp)

theorem glaubermanAt_of_schreier (hS : SchreierFor InCatalog) {X : Type} [Group X] [Finite X]
    (hX : InCatalog X) : GlaubermanAt X := by
  intro hsimple hnonab _ S K hK hfix
  have : IsSimpleGroup X := hsimple
  have : Group.IsPerfect K := hK
  have hout : Group.IsSolvable (Outer X) := hS X hnonab hX
  let φ : K →* Outer X := (QuotientGroup.mk' (inner X)).comp K.subtype
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hrange : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  have hKinner : K ≤ inner X := by
    intro α hα
    have h1 : φ ⟨α, hα⟩ = 1 := by
      have hmem : φ ⟨α, hα⟩ ∈ φ.range := ⟨⟨α, hα⟩, rfl⟩
      rwa [hrange, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff α).1 h1
  let Kc : Subgroup X := K.comap (MulAut.conj : X →* MulAut X)
  have hKc : Kc ≤ Subgroup.centralizer (S : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := hfix _ hx s hs
    rw [MulAut.conj_apply] at h
    calc s * x = (x * s * x⁻¹) * x := by rw [h]
      _ = x * s := by group
  have : Group.IsSolvable ↥(Subgroup.centralizer (S : Set X)) := isSolvable_centralizer_sylow S
  have : Group.IsSolvable Kc :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKc)
  have hKeq : Kc.map (MulAut.conj : X →* MulAut X) = K := Subgroup.map_comap_eq_self hKinner
  have hsolv : Group.IsSolvable (Kc.map (MulAut.conj : X →* MulAut X)) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  rw [hKeq] at hsolv
  by_contra hne
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable K hsolv

end Schreier

end CFSG.CGT.PushingUpLit.CGT6.Nine7
