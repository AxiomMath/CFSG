module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalCentral
public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

theorem thm5IH_isClassicalMember_map_normal {K Y : Type} [Group K] [Finite K] [Group Y]
    (θ : K →* Y) (hker : θ.ker ≤ Subgroup.center K) (hnorm : θ.range.Normal)
    (hodd : Odd (Nat.card (GaloisField p f))) {L : Subgroup K} {z : K}
    (h : IsClassicalMember p f L z) (hz : θ z ≠ 1) :
    IsClassicalMember p f (L.map θ) (θ z) where
  orderOf_eq_two := by
    refine orderOf_eq_prime ?_ hz
    rw [← map_pow, ← h.orderOf_eq_two, pow_orderOf_eq_one, map_one]
  mem := Subgroup.mem_map_of_mem θ h.mem
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map θ
  subnormal := by
    have hA := isSubnormal_map θ h.subnormal
    set B := Subgroup.centralizer ({θ z} : Set Y) with hB
    set B' := θ.range ⊓ B with hB'
    set A := (Subgroup.centralizer ({z} : Set K)).map θ with hA'
    have hle : A ≤ B' := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, ?_⟩
      show θ x ∈ Subgroup.centralizer ({θ z} : Set Y)
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hx]
    have hcomm : ⁅B', B'⁆ ≤ A := commutator_le_map_centralizer θ hker z
    have hnormA : (A.subgroupOf B').Normal := by
      refine ⟨fun a ha x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have hc : ⁅(x : Y), (a : Y)⁆ ∈ A :=
        hcomm (Subgroup.commutator_mem_commutator x.2 a.2)
      have e : ((x * a * x⁻¹ : B') : Y) = ⁅(x : Y), (a : Y)⁆ * (a : Y) := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact A.mul_mem hc ha
    have hB'B : B' ≤ B := inf_le_right
    have hnormB : (B'.subgroupOf B).Normal := by
      refine ⟨fun a ha x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      refine ⟨?_, (x * a * x⁻¹ : B).2⟩
      have : ((x * a * x⁻¹ : B) : Y) = (x : Y) * (a : Y) * (x : Y)⁻¹ := rfl
      rw [this]
      exact hnorm.conj_mem _ ha.1 _
    exact isSubnormal_trans hA (IsSubnormal.step hle hnormA
      (IsSubnormal.step hB'B hnormB (IsSubnormal.refl B)))
  nonempty_equiv := by
    obtain ⟨e⟩ := h.nonempty_equiv
    set φ := θ.subgroupMap L with hφdef
    have hφ : Function.Surjective φ := MonoidHom.subgroupMap_surjective θ L
    have : Finite ↥(L.map θ) := Finite.of_surjective φ hφ
    have hkodd : Odd (Nat.card φ.ker) := by
      by_contra hne
      obtain ⟨x, hx⟩ := exists_orderOf_eq_two_of_even_card hne
      have hxk : θ ((x : L) : K) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
        simpa [hφdef] using this
      have hxL : orderOf (x : L) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
      have hxc : ((x : L) : K) ∈ Subgroup.center K := hker (MonoidHom.mem_ker.mpr hxk)
      have hne' : ((x : L) : K) ≠ z := fun h' => hz (by rw [← h']; exact hxk)
      exact false_of_two_commuting_involutions_sl2 hodd e (a := (x : L)) (b := ⟨z, h.mem⟩) hxL
        (by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two)
        (Subtype.ext ((Subgroup.mem_center_iff.mp hxc z).symm))
        (fun hh => hne' (congrArg Subtype.val hh))
    exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv φ hφ hkodd).symm.trans e⟩

section Inner

variable {S H : Type} [Group S] [Group H]

theorem thm5IH_innerL_ker_le_center (L : Subgroup H) :
    ((toInducedAutOn L).comp (Subgroup.inclusion (Subgroup.le_normalizer (H := L)))).ker ≤
      Subgroup.center ↥L := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_center_iff]
  intro h
  have hc := Lemma52Proof.commute_of_toInducedAutOn_eq_one L (Subgroup.le_normalizer g.2) hg
  exact Subtype.ext (hc h h.2).symm

theorem thm5IH_isClassicalMember_innerHom [Finite H] [Group.IsPerfect S] (ψ : S →* H)
    (hker : ψ.ker ≤ Subgroup.center S) (hodd : Odd (Nat.card (GaloisField p f)))
    {K : Subgroup H} {z : H} (hK : IsClassicalMember p f K z) {R : Subgroup S}
    (hKR : K = R.map ψ) {x : S} (hx : ψ x = z) (hx1 : FrameVertex.innerHom ψ x ≠ 1) :
    IsClassicalMember p f (R.map (FrameVertex.innerHom ψ)) (FrameVertex.innerHom ψ x) := by
  classical
  obtain ⟨-, hnorm, -⟩ := FrameVertex.innerHom_spec ψ hker
  set L : Subgroup H := ψ.range with hL
  set ρ : ↥L →* ↥(inducedAutOn L) :=
    (toInducedAutOn L).comp (Subgroup.inclusion (Subgroup.le_normalizer (H := L))) with hρ
  have hKL : K ≤ L := by
    rw [hKR]
    exact Subgroup.map_le_range ψ R
  have hsec : Balance.Bootstrap.IsSectionMember p f ⊤ K z :=
    { le := le_top
      orderOf_eq_two := hK.orderOf_eq_two
      mem := hK.mem
      perfect := hK.perfect
      subnormal := by rw [inf_top_eq]; exact hK.subnormal
      nonempty_equiv := hK.nonempty_equiv }
  obtain ⟨hzL, hcl⟩ := (hsec.restrict (le_top : L ≤ ⊤) hKL).toIn
  have hρx : ρ ⟨z, hzL⟩ = FrameVertex.innerHom ψ x := by
    rw [FrameVertex.innerHom_apply]
    have : (⟨z, Subgroup.le_normalizer hzL⟩ : ↥(Subgroup.normalizer (L : Set H))) =
        ⟨ψ x, FrameVertex.mem_normalizer_range ψ x⟩ := Subtype.ext hx.symm
    exact congrArg (toInducedAutOn L) this
  have hrange : ρ.range = (FrameVertex.innerHom ψ).range := by
    ext y
    constructor
    · rintro ⟨⟨l, hl⟩, rfl⟩
      obtain ⟨s, rfl⟩ := hl
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨ψ s, s, rfl⟩, rfl⟩
  have hnorm' : ρ.range.Normal := by
    rw [hrange]
    exact hnorm
  have hmap := thm5IH_isClassicalMember_map_normal ρ (thm5IH_innerL_ker_le_center L) hnorm' hodd
    hcl (by rw [hρx]; exact hx1)
  have hset : (K.subgroupOf L).map ρ = R.map (FrameVertex.innerHom ψ) := by
    ext y
    constructor
    · rintro ⟨⟨l, hlL⟩, hlK, rfl⟩
      have hlK' : l ∈ K := hlK
      rw [hKR] at hlK'
      obtain ⟨s, hs, rfl⟩ := hlK'
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨ψ s, s, rfl⟩, ?_, rfl⟩
      show ψ s ∈ K
      rw [hKR]
      exact Subgroup.mem_map_of_mem ψ hs
  rw [← hρx, ← hset]
  exact hmap

end Inner

end CFSG.ClassicalInvolution.Asc77
