module

public import CFSG.GH74.Uniqueness.Theorem4
public import CFSG.GH74.Uniqueness.SE

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Nonabelian

variable {X : Type*} [Group X] {M : Subgroup X}

theorem exists_mul_ne_of_isStronglyEmbedded (hM : IsStronglyEmbedded M) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨hne, heven, hodd⟩ := hM
  obtain ⟨g, hg⟩ : ∃ g : X, g ∉ M := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.mpr fun x _ => hall x)
  have hconj : conjugate M g = M := by
    ext x
    rw [mem_conjugate_iff, hcomm g x, mul_assoc, mul_inv_cancel, mul_one]
  have h := hodd g hg
  rw [hconj, inf_idem] at h
  exact (Nat.not_even_iff_odd.mpr h) heven

end Nonabelian

section Transport

theorem mem_pPrimeCore_top_iff {X : Type*} [Group X] (y : ↥(⊤ : Subgroup X)) :
    y ∈ pPrimeCore 2 ↥(⊤ : Subgroup X) ↔ (y : X) ∈ pPrimeCore 2 X := by
  have h := pPrimeCore_map_iso 2 (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)
  rw [← h]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y', hy', hyy'⟩
    have : y' = y := Subtype.ext hyy'
    rwa [this] at hy'

theorem isBenderGroup_isBorel_derivedBar_of_eq_top {X : Type} [Group X] [Finite X] (M : Subgroup X)
    (hD : commutator X = ⊤) (L : Subgroup X) (hL : L = ⊤)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (↥L ⧸ pPrimeCore 2 ↥L))
    (hBorel : IsBorel ((M.comap L.subtype).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)))) :
    CFSG.BenderSuzuki.IsBenderGroup (derivedBar X) ∧ IsBorel (derivedBarImage M) := by
  subst hL
  have hmem : ∀ y : X, y ∈ commutator X := fun y => hD ▸ Subgroup.mem_top y
  refine (bender_borel_iff_exists_hom M).mpr ?_
  let φ : ↥(commutator X) →* (↥(⊤ : Subgroup X) ⧸ pPrimeCore 2 ↥(⊤ : Subgroup X)) :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(⊤ : Subgroup X))).comp
      ((commutator X).subtype.codRestrict (⊤ : Subgroup X) (fun _ => Subgroup.mem_top _))
  have hφ : ∀ x : ↥(commutator X), φ x = QuotientGroup.mk (⟨(x : X), trivial⟩ : ↥(⊤ : Subgroup X)) :=
    fun _ => rfl
  refine ⟨_, inferInstance, φ, ?_, ?_, hB, ?_⟩
  · intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨(a : X), hmem _⟩, rfl⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, QuotientGroup.eq_one_iff]
    exact mem_pPrimeCore_top_iff _
  · obtain ⟨S, hS⟩ := hBorel
    refine ⟨S, ?_⟩
    rw [← hS]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : X), trivial⟩, hx, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨(a : X), hmem _⟩, ha, rfl⟩

end Transport

section Reduction

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.isStronglyEmbedded_of_odd_card
    (S : ZDSetup X Z M) {t : X} (_ht : t ∈ Z)
    (htM : t ∉ M) (hodd : Odd (Nat.card ↥(M ⊓ conjugate M t))) : IsStronglyEmbedded M := by
  refine ⟨S.prodDisc.1, ?_, ?_⟩
  · obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
    have hdvd : orderOf z ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hzM
    rw [S.invariant.1 z hz] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  · intro g hg
    have hMω : M ∈ omega M := self_mem_omega M
    have hne_t : M ≠ conjugate M t := ((S.prodDisc.conjugate_ne_iff hMω).mpr htM).symm
    have hne_g : M ≠ conjugate M g := ((S.prodDisc.conjugate_ne_iff hMω).mpr hg).symm
    obtain ⟨h, h1, h2⟩ := S.theorem4.1 M hMω (conjugate M t) (conjugate_mem_omega hMω t) hne_t
      M hMω (conjugate M g) (conjugate_mem_omega hMω g) hne_g
    have key : M ⊓ conjugate M g = conjugate (M ⊓ conjugate M t) h := by
      rw [conjugate_inf, h1, h2]
    rw [key]
    have hcard : Nat.card ↥(conjugate (M ⊓ conjugate M t) h) = Nat.card ↥(M ⊓ conjugate M t) :=
      Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective
    rw [hcard]
    exact hodd

open scoped commutatorElement in
theorem ZDSetup.false_of_isStronglyEmbedded
    (S : ZDSetup X Z M) (h : IsStronglyEmbedded M) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  have hnonab := exists_mul_ne_of_isStronglyEmbedded h
  have hZ : Z = {x : X | orderOf x = 2} :=
    S.prodDisc.eq_involutions_of_isStronglyEmbedded S.invariant h
  have hL : involutionClosure X = ⊤ := by
    unfold involutionClosure
    rw [← hZ]
    exact S.gen
  have hD : commutator X = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (commutator X) with hb | ht
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact ht
  have heven : Even (Nat.card X) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp h.2.1).trans (Subgroup.card_subgroup_dvd_card M))
  have hN : pPrimeCore 2 X = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (pPrimeCore 2 X) with hb | ht
    · exact hb
    · exfalso
      have hcop := pPrimeCore_coprime_card (p := 2) (G := X)
      rw [ht, Subgroup.card_top] at hcop
      exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp hcop)) heven
  rcases S_SE_proof X M h with hlow | ⟨hB, -, hBorel⟩
  · rw [hL] at hlow
    have h2 : 2 ≤ Open.pRank 2 (⊤ : Subgroup X) := S.two_le_twoRank
    omega
  · obtain ⟨hBender, hBorel'⟩ :=
      isBenderGroup_isBorel_derivedBar_of_eq_top M hD _ hL hB hBorel
    refine S.counterexample (Or.inr ⟨1, M.one_mem, one_pow 2, ?_, ?_, ?_, ?_, ?_, hBender, hBorel', ?_⟩)
    · rw [hD, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    · rw [Subgroup.zpowers_one_eq_bot, inf_bot_eq]
    · rw [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_left]
      exact bot_le
    · rw [hD]
      exact le_top
    · rw [hN]
      exact bot_le
    · intro z hz
      refine ⟨⟨z, hD ▸ Subgroup.mem_top z, (one_mul z).symm⟩, fun o ho => ?_⟩
      rw [hN, Subgroup.mem_bot] at ho
      rw [ho, mul_one]
      intro hz1
      have h2 := S.invariant.1 z hz
      rw [hz1, orderOf_one] at h2
      exact absurd h2 (by norm_num)

theorem ZDSetup.false_of_odd_card
    (S : ZDSetup X Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M)
    (hodd : Odd (Nat.card ↥(M ⊓ conjugate M t))) : False :=
  S.false_of_isStronglyEmbedded (S.isStronglyEmbedded_of_odd_card ht htM hodd)

end Reduction

end CFSG.GH74.Uniqueness
