module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionTwoGroup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuasi
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveBasic
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

open CFSG.Open
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

theorem quaternion_sylow_of_rank_one_image {X Δ : Type} [Group X] [Group Δ] [Finite X]
    [Finite Δ] [Group.IsPerfect X] [Nontrivial Δ] (f : X →* Δ) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) (hr : CFSG.pRank 2 Δ ≤ 1) (P : Sylow 2 X) :
    f.ker ⊓ (P : Subgroup X) = ⊥ ∧
      ∃ n : ℕ, 3 ≤ n ∧ Nonempty ((P : Subgroup X) ≃* QuaternionGroup (2 ^ (n - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect Δ := Group.IsPerfect.ofSurjective hf
  have heven : Even (Nat.card Δ) := SectionSix.even_card_of_perfect
  let S : Sylow 2 Δ := P.mapSurjective hf
  obtain ⟨n, hn, ⟨e⟩⟩ := CFSG.LocalAnalysis.ComponentInitial.perfect_rank_one_Sylow_quaternion
    heven hr S
  set m := 2 ^ (n - 2)
  have : NeZero m := ⟨by positivity⟩
  have hS : (S : Subgroup Δ) = (P : Subgroup X).map f := Sylow.coe_mapSurjective hf P
  let fP : (P : Subgroup X) →* (S : Subgroup Δ) :=
    (f.comp (P : Subgroup X).subtype).codRestrict (S : Subgroup Δ) fun p => by
      rw [hS]
      exact ⟨p, p.2, rfl⟩
  have hfP : Function.Surjective fP := by
    rintro ⟨s, hs⟩
    have hs' : s ∈ (P : Subgroup X).map f := hS ▸ hs
    obtain ⟨p, hp, rfl⟩ := hs'
    exact ⟨⟨p, hp⟩, Subtype.ext rfl⟩
  let g : (P : Subgroup X) →* QuaternionGroup m := e.toMonoidHom.comp fP
  have hg : Function.Surjective g := e.surjective.comp hfP
  have hgker : ∀ p : (P : Subgroup X), p ∈ g.ker ↔ (p : X) ∈ f.ker := by
    intro p
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change e (fP p) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hgc : g.ker ≤ Subgroup.center (P : Subgroup X) := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    have hpc := hker ((hgker p).mp hp)
    exact Subgroup.mem_center_iff.mp hpc q
  have hcomm := AschbacherToolkit.quaternion_central_extension_of_surjective g hg hgc
  set Z := g.ker.map (P : Subgroup X).subtype
  have hZc : Z ≤ Subgroup.center X := by
    rintro _ ⟨p, hp, rfl⟩
    exact hker ((hgker p).mp hp)
  have hZp : IsPGroup 2 Z := (P.isPGroup'.to_subgroup g.ker).map _
  have htr := AschbacherToolkit.central_sylow_commutator P hZc hZp
  rw [(Group.IsPerfect.commutator_eq_top (G := X)), inf_top_eq] at htr
  have hZbot : Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ Z ⊓ (commutator (P : Subgroup X)).map (P : Subgroup X).subtype := htr ▸ hz
    obtain ⟨⟨p, hp, rfl⟩, ⟨q, hq, hqp⟩⟩ := hz'
    have hpq : q = p := Subtype.ext hqp
    subst hpq
    have : q ∈ g.ker ⊓ commutator (P : Subgroup X) := ⟨hp, hq⟩
    rw [hcomm, Subgroup.mem_bot] at this
    rw [this]
    rfl
  have hgkerbot : g.ker = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    have : (p : X) ∈ Z := ⟨p, hp, rfl⟩
    rw [hZbot, Subgroup.mem_bot] at this
    exact Subtype.ext this
  refine ⟨?_, n, hn, ⟨MulEquiv.ofBijective g ⟨(MonoidHom.ker_eq_bot_iff g).mp hgkerbot, hg⟩⟩⟩
  rw [eq_bot_iff]
  rintro x ⟨hxk, hxP⟩
  have : (⟨x, hxP⟩ : (P : Subgroup X)) ∈ g.ker := (hgker _).mpr hxk
  rw [hgkerbot, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem pRank_le_one_of_quaternion {Q : Type} [Group Q] [Finite Q] {P : Subgroup Q}
    (hP : AschbacherTheorem3.IsQuaternionTwoGroup P) : CFSG.Open.pRank 2 P ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨E, hEP, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (H := P) (k := 2) (by omega)
  have hE4 : Nat.card E = 4 := by rw [hcard]; norm_num
  have hinv : ∀ x ∈ E, x ≠ 1 → orderOf x = 2 := fun x hx hne =>
    orderOf_eq_prime (hE.2 x hx) hne
  have hsub : ¬ (E : Set Q) ⊆ {1, (1 : Q)} := by
    intro h
    have := card_le_two_of_subset h
    omega
  obtain ⟨x, hx, hxne⟩ := Set.not_subset.mp hsub
  have hx1 : x ≠ 1 := fun h => hxne (Or.inl h)
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ E, y ≠ 1 ∧ y ≠ x := by
    by_contra hno
    push Not at hno
    have h2 : (E : Set Q) ⊆ {1, x} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (hno y hy h1)
    have := card_le_two_of_subset h2
    omega
  exact hyne.2 (SectionSix.quaternion_unique_involution hP (hEP hy) (hEP hx) (hinv y hy hyne.1)
    (hinv x hx hx1))

theorem unique_involution_of_rank_one_image {Q : Type} [Group Q] [Finite Q] {X : Subgroup Q}
    (hX : aschbacherThm5IsSemisimple X) {Δ : Type} [Group Δ] [Finite Δ] (f : X →* Δ)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X) (hr : CFSG.pRank 2 Δ ≤ 1) :
    ∃ c ∈ X, orderOf c = 2 ∧ (∀ x ∈ X, orderOf x = 2 → x = c) ∧
      ∀ hc : c ∈ X, f ⟨c, hc⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect X := semisimple_perfect X hX
  have : Nontrivial X := semisimple_nontrivial X hX
  have hΔ : Nontrivial Δ := by
    by_contra hΔ
    rw [not_nontrivial_iff_subsingleton] at hΔ
    have htop : f.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Subsingleton.elim _ _
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (hker (htop ▸ Subgroup.mem_top a)) b).symm
    have hab : commutator X = ⊥ := by
      rw [eq_bot_iff, commutator, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, hcomm]
    rw [Group.IsPerfect.commutator_eq_top] at hab
    exact (top_ne_bot (α := Subgroup X)) hab
  let P : Sylow 2 X := default
  obtain ⟨hPk, n, hn, ⟨e⟩⟩ := quaternion_sylow_of_rank_one_image f hf hker hr P
  have hPq : AschbacherTheorem3.IsQuaternionTwoGroup (P : Subgroup X) := ⟨n, hn, ⟨e⟩⟩
  obtain ⟨k, K, hk, hKinj, hgen, hcomp, -⟩ := semisimple_component_presentation X hX
  have hKX : ∀ l, K l ≤ X := fun l => hgen ▸ le_iSup K l
  have hsub := SectionSix.components_subsingleton_of_sylow (X := X)
    (K := fun l => (K l).subgroupOf X) (Q := ⊤) (R := (P : Subgroup X)) hcomp
    (fun _ => le_top)
    (fun i j hij x hx y hy => by
      have hc := OrdinaryComponentTransport.commute_local_distinct (K i) (K j) X (hKX i)
        (hKX j) (hcomp i) (hcomp j) (fun h => hij (hKinj h))
      have hxy := Subgroup.commutator_mem_commutator hx hy
      rw [show ⁅(K i).subgroupOf X, (K j).subgroupOf X⁆ = ⊥ by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_bot]
        apply Subtype.ext
        have := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
          (Subgroup.mem_subgroupOf.mp hb)
        rw [hc, Subgroup.mem_bot] at this
        exact this, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hxy
      exact hxy)
    (isSylowOf_iff.mpr ⟨le_top, P.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact P.not_dvd_index⟩) (Or.inr (Or.inr hPq))
  have hk1 : k = 1 := by
    by_contra hk1
    have := hsub ⟨0, hk⟩ ⟨1, by omega⟩
    simp [Fin.ext_iff] at this
  subst hk1
  have hX0 : K 0 = X := by
    rw [← hgen]
    exact (iSup_unique (fun l => K l)).symm
  have hQ : CFSG.IsQuasisimple X := by
    have h0 := (hcomp 0).2.2
    have htop : (K 0).subgroupOf X = ⊤ := by
      rw [hX0]
      exact Subgroup.subgroupOf_self X
    rw [htop] at h0
    exact CatalogueBAlternating.quasisimple_iff_native.mpr
      (Components.quasisimple_of_equiv Subgroup.topEquiv.symm h0)
  have hrX : CFSG.pRank 2 X ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← (CFSG.SectionRank.pRank_sylow P).1]
    exact pRank_le_one_of_quaternion hPq
  obtain ⟨-, ⟨z, hz2, hzuniq⟩, hzc, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.quasisimple_rank_one_unique_central_involution hQ hrX
  have hzP : z ∈ (P : Subgroup X) := by
    have hzn : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (hzc z hz2))
    have hz2' : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
    exact hz2'.le_sylow_of_normal P (Subgroup.mem_zpowers z)
  refine ⟨z, z.2, by rw [Subgroup.orderOf_coe]; exact hz2, fun x hx hx2 => ?_, fun hc hfc => ?_⟩
  · have := hzuniq ⟨x, hx⟩ (show orderOf (⟨x, hx⟩ : X) = 2 by
      rw [Subgroup.orderOf_mk]; exact hx2)
    exact congrArg Subtype.val this
  · have hzk : z ∈ f.ker ⊓ (P : Subgroup X) := ⟨MonoidHom.mem_ker.mpr hfc, hzP⟩
    rw [hPk, Subgroup.mem_bot] at hzk
    rw [hzk, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
