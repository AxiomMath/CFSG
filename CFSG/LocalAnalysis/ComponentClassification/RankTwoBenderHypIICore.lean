module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII

public section

namespace CFSG.ComponentClassification.RankTwoBender

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b

variable {H : Type*} [Group H]

theorem mem_normalizer_of_commute_involution [Finite H] {P X : Subgroup H} (hXP : X ≤ P)
    (htight : TightlyEmbedded (X.subgroupOf P)) {s : H} (hsX : s ∈ X) (hs1 : s ≠ 1)
    (hs2 : s * s = 1) {y : H} (hyP : y ∈ P) (hys : y * s = s * y) :
    y ∈ normalizer (X : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hyN
  set y' : P := ⟨y, hyP⟩ with hy'
  have hy'N : y' ∉ normalizer ((X.subgroupOf P : Subgroup P) : Set P) := by
    intro hN
    apply hyN
    rw [mem_normalizer_iff]
    intro z
    by_cases hzP : z ∈ P
    · have h := (mem_normalizer_iff.mp hN) ⟨z, hzP⟩
      simpa [mem_subgroupOf, hy'] using h
    · have h1 : z ∉ X := fun h => hzP (hXP h)
      have h2 : y * z * y⁻¹ ∉ X := by
        intro h
        apply hzP
        have := P.mul_mem (P.mul_mem (P.inv_mem hyP) (hXP h)) hyP
        rwa [show y⁻¹ * (y * z * y⁻¹) * y = z by group] at this
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have hodd := htight.2 y' hy'N
  set K := X.subgroupOf P ⊓ rightConjugate (X.subgroupOf P) y' with hK
  have hsK : (⟨s, hXP hsX⟩ : P) ∈ K := by
    refine ⟨mem_subgroupOf.mpr hsX, (mem_rightConjugate_iff _ _ _).mpr ?_⟩
    rw [mem_subgroupOf]
    change y * s * y⁻¹ ∈ X
    rw [hys, mul_inv_cancel_right]
    exact hsX
  set k : K := ⟨⟨s, hXP hsX⟩, hsK⟩ with hk
  have hk2 : k ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp [hk, sq, hs2]
  have hk1 : k ≠ 1 := by
    intro h
    apply hs1
    have := congrArg (fun z : K => ((z : P) : H)) h
    simpa [hk] using this
  have hord : orderOf k = 2 := orderOf_eq_prime hk2 hk1
  have hdvd := orderOf_dvd_natCard k
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem isTwoNilpotent_range [Finite H] {H' : Type*} [Group H'] [Finite H']
    {X : Subgroup H} (hX : IsTwoNilpotent X) (ρ : X →* H') : IsTwoNilpotent ρ.range := by
  obtain ⟨N, hNX, hNn, hNodd, k, hk⟩ := hX
  let f : X →* ρ.range := ρ.rangeRestrict
  have hf : Function.Surjective f := ρ.rangeRestrict_surjective
  set N' : Subgroup H' := (N.subgroupOf X).map ρ with hN'
  have hN'f : N'.subgroupOf ρ.range = (N.subgroupOf X).map f := by
    ext ⟨w, hw⟩
    simp only [mem_subgroupOf, hN', mem_map]
    constructor
    · rintro ⟨x, hx, hxw⟩
      exact ⟨x, hx, Subtype.ext hxw⟩
    · rintro ⟨x, hx, hxw⟩
      exact ⟨x, hx, congrArg Subtype.val hxw⟩
  refine ⟨N', map_le_range _ _, ?_, ?_, ?_⟩
  · rw [hN'f]
    exact hNn.map f hf
  · refine hNodd.of_dvd_nat ((card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (subgroupOfEquivOfLe hNX).toEquiv]
  · have hdvd : N'.relIndex ρ.range ∣ 2 ^ k := by
      rw [relIndex, hN'f, ← hk, relIndex]
      exact index_map_dvd _ hf
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨m, hm⟩

theorem false_of_twoNilpotent_cover [Finite H] {B X : Subgroup H} (hBs : IsSimpleGroup B)
    (hZ : center B = ⊥) (heven : Even (Nat.card B)) (hXN : X ≤ normalizer (B : Set H))
    (hX2 : IsTwoNilpotent X)
    (hcover : ∀ x ∈ B, ∃ c ∈ centralizer (B : Set H), x * c ∈ X) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : X →* MulAut B := B.normalizerMonoidHom.comp (inclusion hXN)
  let ι : B →* MulAut B := MulAut.conj
  have hι : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [← hZ, mem_center_iff]
    intro y
    have h : x * y * x⁻¹ = y := by
      simpa [ι, MulAut.conj_apply] using DFunLike.congr_fun (MonoidHom.mem_ker.mp hx) y
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  have hInn : ι.range ≤ ρ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, hc, hxc⟩ := hcover x x.2
    refine ⟨⟨x * c, hxc⟩, ?_⟩
    ext z
    have hcz : c * (z : H) = (z : H) * c := (mem_centralizer_iff.mp hc z z.2).symm
    simp only [ρ, ι, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe, coe_inclusion,
      MulAut.conj_apply, coe_mul, coe_inv]
    rw [mul_inv_rev,
      show (x : H) * c * z * (c⁻¹ * (x : H)⁻¹) = x * (c * z) * c⁻¹ * (x : H)⁻¹ by group, hcz]
    group
  obtain ⟨N, hNI, hNn, hNodd, m, hm⟩ := (isTwoNilpotent_range hX2 ρ).mono hInn
  let e : B ≃* ι.range := MonoidHom.ofInjective hι
  have : IsSimpleGroup B := hBs
  have : IsSimpleGroup ι.range := e.symm.isSimpleGroup
  have : Finite ι.range := Finite.of_surjective e e.surjective
  rcases hNn.eq_bot_or_eq_top with hbot | htop
  ·
    have hN : N = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hNI hx⟩ : ι.range) ∈ N.subgroupOf ι.range := mem_subgroupOf.mpr hx
      rw [hbot] at this
      exact congrArg Subtype.val (mem_bot.mp this)
    rw [hN, relIndex_bot_left] at hm
    have hBcard : Nat.card B = 2 ^ m := by rw [Nat.card_congr e.toEquiv, hm]
    have hp : IsPGroup 2 B := IsPGroup.of_card hBcard
    have : Nontrivial B := hBs.toNontrivial
    have hnt := hp.center_nontrivial
    rw [hZ] at hnt
    exact (nontrivial_iff_ne_bot _).mp hnt rfl
  ·
    have hN : N = ι.range := by
      apply le_antisymm hNI
      intro x hx
      have : (⟨x, hx⟩ : ι.range) ∈ N.subgroupOf ι.range := by rw [htop]; exact mem_top _
      exact mem_subgroupOf.mp this
    rw [hN, ← Nat.card_congr e.toEquiv] at hNodd
    exact (Nat.not_even_iff_odd.mpr hNodd) heven

theorem center_eq_bot_of_bender {X : Type} [Group X] [Finite X] (hX : fusionIsBenderGroup X) :
    center X = ⊥ := by
  have : IsSimpleGroup X := isSimpleGroup_of_bender hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 X))
    obtain ⟨-, hcard, hU4⟩ := bender_sylow_facts hX U
    have hn : (U : Subgroup X).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hg : g ∈ center X := h ▸ mem_top g
      rwa [show g * x * g⁻¹ = x by rw [(mem_center_iff.mp hg x).symm, mul_inv_cancel_right]]
    have : Unique (Sylow 2 X) := Sylow.unique_of_normal U hn
    rw [Nat.card_unique] at hcard
    omega

theorem even_card_of_bender {X : Type} [Group X] [Finite X] (hX : fusionIsBenderGroup X) :
    Even (Nat.card X) := by
  obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 X))
  obtain ⟨-, -, hU4⟩ := bender_sylow_facts hX U
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp U.isPGroup'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  exact even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans (hk ▸ card_subgroup_dvd_card _))

end CFSG.ComponentClassification.RankTwoBender
