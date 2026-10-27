module

public import CFSG.GH74.Uniqueness.Section4Struct
public import CFSG.GH74.Uniqueness.Section4Lemma45
public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Covers
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearFourCentralCover

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section CoverRigid

variable {J : Type} [Group J] [Finite J]

omit [Finite J] in
theorem mulAut_eq_one_of_central_quotient (hperf : commutator J = ⊤) {N : Subgroup J}
    (hN : N ≤ center J) (τ : MulAut J) (hτ : ∀ x : J, x⁻¹ * τ x ∈ N) : τ = 1 := by
  let lam : J →* center J :=
    { toFun := fun x => ⟨x⁻¹ * τ x, hN (hτ x)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc : x⁻¹ * τ x ∈ center J := hN (hτ x)
        have h1 : y⁻¹ * (x⁻¹ * τ x) = (x⁻¹ * τ x) * y⁻¹ :=
          Subgroup.mem_center_iff.mp hc y⁻¹
        change (x * y)⁻¹ * τ (x * y) = (x⁻¹ * τ x) * (y⁻¹ * τ y)
        rw [map_mul, mul_inv_rev]
        calc y⁻¹ * x⁻¹ * (τ x * τ y) = y⁻¹ * (x⁻¹ * τ x) * τ y := by group
          _ = (x⁻¹ * τ x) * y⁻¹ * τ y := by rw [h1]
          _ = (x⁻¹ * τ x) * (y⁻¹ * τ y) := by group }
  have hker : commutator J ≤ lam.ker := Abelianization.commutator_subset_ker lam
  rw [hperf] at hker
  ext x
  have hx : lam x = 1 := (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x)))
  have : x⁻¹ * τ x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp this).symm

theorem mulAut_eq_one_of_centralizes_sylow
    (hperf : commutator J = ⊤) {N : Subgroup J} [N.Normal]
    (hN : N ≤ center J) (hB : CFSG.BenderSuzuki.IsBenderGroup (J ⧸ N))
    (S : Sylow 2 J) (hS : centralizer (S : Set J) ≤ N) (σ : MulAut J)
    (hσN : N.map (σ : J →* J) = N) (hσ : ∀ s ∈ (S : Subgroup J), σ s = s) : σ = 1 := by
  obtain ⟨n, i, e, hT⟩ := exists_benderType_of_isBenderGroup hB
  let q : J →* J ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  let Sb : Sylow 2 (J ⧸ N) := S.mapSurjective hq
  let α : MulAut (J ⧸ N) := QuotientGroup.congr N N σ hσN
  have hα : ∀ x : J, α (q x) = q (σ x) := fun x => rfl
  have hfix : ∀ x ∈ (Sb : Subgroup (J ⧸ N)), α x = x := by
    intro x hx
    have hx' : x ∈ (S : Subgroup J).map q := hx
    obtain ⟨s, hs, rfl⟩ := hx'
    rw [hα, hσ s hs]
  obtain ⟨rb, hrb, hαr⟩ := hT.lemma_3_6_a Sb α hfix
  obtain ⟨r, hrS, hrq⟩ : ∃ r ∈ (S : Subgroup J), q r = rb := by
    have : rb ∈ (S : Subgroup J).map q := (Bender.mem_rootCenter_iff.mp hrb).1
    obtain ⟨r, hr, h⟩ := this
    exact ⟨r, hr, h⟩
  let τ : MulAut J := MulAut.conj r⁻¹ * σ
  have hτx : ∀ x : J, τ x = r⁻¹ * σ x * r := fun x => by
    simp [τ]
  have hτ : ∀ x : J, x⁻¹ * τ x ∈ N := by
    intro x
    have h1 : q (τ x) = q x := by
      rw [hτx, map_mul, map_mul, map_inv, hrq, ← hα x, hαr (q x)]
      group
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change (q x)⁻¹ * q (τ x) = 1
    rw [h1, inv_mul_cancel]
  have hτ1 : τ = 1 := mulAut_eq_one_of_central_quotient hperf hN τ hτ
  have hσr : ∀ x : J, σ x = r * x * r⁻¹ := by
    intro x
    have h := hτx x
    rw [hτ1, MulAut.one_apply] at h
    calc σ x = r * (r⁻¹ * σ x * r) * r⁻¹ := by group
      _ = r * x * r⁻¹ := by rw [← h]
  have hrN : r ∈ N := by
    refine hS (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
    have h := hσ s hs
    rw [hσr] at h
    calc s * r = r * s * r⁻¹ * r := by rw [h]
      _ = r * s := by group
  have hrc := hN hrN
  ext x
  rw [hσr, MulAut.one_apply]
  have := Subgroup.mem_center_iff.mp hrc x
  calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [this]
    _ = x := by group

end CoverRigid

section Cover

open CFSG.ProperTwoGeneratedCore.Lemma37 CFSG.ShultStronglyClosedTI

variable {J : Type} [Group J] [Finite J]

theorem center_eq_of_isBenderGroup_quotient
    {N : Subgroup J} [N.Normal] (hN : N ≤ center J)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (J ⧸ N)) : center J = N := by
  refine le_antisymm (fun c hc => ?_) hN
  have hcb : (c : J ⧸ N) ∈ center (J ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hc y]
  rw [center_eq_bot_of_isBenderGroup hB, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcb
  exact hcb

theorem centralizer_sylow_le_of_cover
    (hperf : commutator J = ⊤) {N : Subgroup J} [N.Normal]
    (hN : N ≤ center J) (hN2 : Nat.card N = 2)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (J ⧸ N)) (P : Sylow 2 J) :
    centralizer (P : Set J) ≤ N := by
  have hZ : center J = N := center_eq_of_isBenderGroup_quotient hN hB
  have hZ2 : Nat.card (center J) = 2 := by rw [hZ]; exact hN2
  have hB' : CFSG.BenderSuzuki.IsBenderGroup (J ⧸ center J) := by
    have e0 : J ⧸ center J ≃* J ⧸ N := QuotientGroup.quotientMulEquivOfEq hZ
    cases hB with
    | isPSL2 n hn e => exact .isPSL2 n hn (e0.trans e)
    | isSuzuki n hn e => exact .isSuzuki n hn (e0.trans e)
    | isPSU3 n hn e => exact .isPSU3 n hn (e0.trans e)
  have : Group.IsPerfect J := ⟨hperf⟩
  have hp : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by simpa using hN2)
  have hne : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hN2
    omega
  rcases bender_cover_quotient hperf hZ2 hB' with he | he
  ·
    obtain ⟨e⟩ := he
    let ψ : CFSG.Theory.Comparator.PSL2Model 2 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
      linearCover_pslEquivSL
    let η : J →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
      ψ.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center J)))
    have hker : η.ker = N := by
      rw [← hZ]
      ext x
      change ψ (e (x : J ⧸ center J)) = 1 ↔ x ∈ center J
      rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    have hsurj : Function.Surjective η :=
      ψ.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hcard : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    have h := four_field_linear_central_two_cover_sylow_centralizer hcard η hsurj
      (by rw [hker]; exact hN) (by rw [hker]; exact hp)
    have h' := (h.2 (by rw [hker]; exact hne) P).2.2.2.1
    rw [hker] at h'
    exact h'.le
  ·
    obtain ⟨e⟩ := he
    let ψ : ↥(CFSG.Theory.Comparator.SzModel 1) ≃*
        ↥(CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) :=
      MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup 1)
    let η : J →* ↥(CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) :=
      ψ.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center J)))
    have hker : η.ker = N := by
      rw [← hZ]
      ext x
      change ψ (e (x : J ⧸ center J)) = 1 ↔ x ∈ center J
      rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    have hsurj : Function.Surjective η :=
      ψ.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have h := suzukiCover_matrix_nontrivial_Sylow_centralizer 1 le_rfl η hsurj
      (by rw [hker]; exact hN) (by rw [hker]; exact hp) (by rw [hker]; exact hne)
    have h' := h.1 P
    rw [hker] at h'
    exact h'.le

end Cover

theorem benderCoverRigid : BenderCoverRigid := by
  intro X _ _ K A _ _ hAK hAc hA2 hperf hB S z hz k hk
  let N : Subgroup ↥K := A.subgroupOf K
  have hNc : N ≤ center ↥K := by
    intro a' ha'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hAc (a' : X) ha' g g.2).symm
  have hN2 : Nat.card N = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
    exact hA2
  have hperfJ : commutator ↥K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [map_subtype_commutator', hperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hZ : center ↥K = N := center_eq_of_isBenderGroup_quotient hNc hB
  let σ : MulAut ↥K := MulAut.conjNormal (H := K) z
  have hσ : ∀ g : ↥K, ((σ g : ↥K) : X) = z * (g : X) * z⁻¹ := fun g => MulAut.conjNormal_apply z g
  have hσc : ∀ c ∈ center ↥K, σ c ∈ center ↥K := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := σ.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc g']
  have hσN : N.map (σ : ↥K →* ↥K) = N := by
    rw [← hZ]
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hσc c hc
    · intro c hc
      refine ⟨σ.symm c, Subgroup.mem_center_iff.mpr fun g => ?_, σ.apply_symm_apply c⟩
      apply σ.injective
      rw [map_mul, map_mul, σ.apply_symm_apply, Subgroup.mem_center_iff.mp hc (σ g)]
  have h1 := mulAut_eq_one_of_centralizes_sylow hperfJ hNc hB S
    (centralizer_sylow_le_of_cover hperfJ hNc hN2 hB S) σ hσN
    (fun s hs => Subtype.ext (by rw [hσ]; exact hz s hs))
  have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨k, hk⟩)
  rw [hσ] at h2
  exact h2

end CFSG.GH74.Uniqueness
