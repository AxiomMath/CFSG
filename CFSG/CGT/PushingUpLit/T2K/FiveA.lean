module

public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CGT.PushingUpLit.T2K.FourSevenA
public import CFSG.CGT.PushingUpLit.T2K.FourSix

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

section PGroup

variable {G : Type} [Group G] [Finite G]

theorem eq_of_normalizer_inf_le {T X : Subgroup G} (hT : IsPGroup 2 T) (hXT : X ≤ T)
    (hN : T ⊓ Subgroup.normalizer (X : Set G) ≤ X) : X = T := by
  by_contra hne
  have hlt : X.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    intro hTX
    exact hne (le_antisymm hXT hTX)
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  obtain ⟨⟨n, hnT⟩, hnN, hnX⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := ↥T) _ hlt)
  apply hnX
  have hnN' : n ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := (Subgroup.mem_normalizer_iff.1 hnN ⟨x, hXT hx⟩).1 hx
      exact h1
    · intro hx
      have hxT : x ∈ T := by
        have : n⁻¹ * (n * x * n⁻¹) * n ∈ T := T.mul_mem (T.mul_mem (T.inv_mem hnT) (hXT hx)) hnT
        simpa [mul_assoc] using this
      have h1 := (Subgroup.mem_normalizer_iff.1 hnN ⟨x, hxT⟩).2 hx
      exact h1
  exact hN ⟨hnT, hnN'⟩

theorem isSylowOf_top_of_normalizer_le {M T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hN : Subgroup.normalizer (T : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := hT.isPGroup.exists_le_sylow
  have hTQeq : T = (Q : Subgroup G) := by
    refine eq_of_normalizer_inf_le Q.isPGroup' hTQ ?_
    intro x ⟨hxQ, hxN⟩
    have hle : T ≤ (Q : Subgroup G) ⊓ Subgroup.normalizer (T : Set G) :=
      le_inf hTQ (Subgroup.le_normalizer)
    have heq := hT.eq_of_le hle (inf_le_right.trans hN) (Q.isPGroup'.to_le inf_le_left)
    have : x ∈ (Q : Subgroup G) ⊓ Subgroup.normalizer (T : Set G) := ⟨hxQ, hxN⟩
    rw [heq] at this
    exact this
  refine (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨le_top, hT.isPGroup, ?_⟩
  rw [Subgroup.relIndex_top_right, hTQeq]
  exact Q.not_dvd_index

theorem le_of_normalizer_inf_le {N T : Subgroup G} (hT : IsPGroup 2 T)
    (hN : Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) ≤ N) : T ≤ N := by
  have := eq_of_normalizer_inf_le hT (inf_le_left : T ⊓ N ≤ T) (fun x ⟨hxT, hxN⟩ => ⟨hxT, hN hxN⟩)
  exact this ▸ inf_le_right

end PGroup

section Natural

theorem card_specialLinearGroup_galoisField_two_one' :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
  let _ : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 1) = 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 1 one_ne_zero, pow_one]
  rw [Matrix.card_SL_field 2, hq, Fin.prod_univ_two]
  decide

theorem not_isPerfect_of_card_eq_six' {Q : Type*} [Group Q] (h : Nat.card Q = 6) :
    ¬ Group.IsPerfect Q := by
  intro hperf
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [h]; norm_num)
  have hN : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hN, h] at this
    omega
  have hle : commutator Q ≤ Subgroup.zpowers x := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have key : ⁅a, b⁆ = a * b * (a⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [key, Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
  have htop : Subgroup.zpowers x = ⊤ := top_le_iff.mp (hperf.commutator_eq_top ▸ hle)
  have hcard := congrArg (fun H : Subgroup Q => Nat.card H) htop
  simp only [Subgroup.card_top, hN, h] at hcard
  omega

theorem not_isNaturalSLTwoModule_one' {X : Type} [Group X] [Finite X] (hX : IsShortGroup X) :
    ¬ IsNaturalSLTwoModule X 1 := by
  rintro ⟨φ, -⟩
  have hcard : Nat.card (X ⧸ CFSG.pCore 2 X) = 6 :=
    (Nat.card_congr φ.toEquiv).trans card_specialLinearGroup_galoisField_two_one'
  rcases hX.quotient_type with hq | hq
  · exact not_isPerfect_of_card_eq_six' hcard hq.1
  · rw [hcard] at hq
    exact absurd hq (by decide)

end Natural

variable {G : Type} [Group G] [Finite G]

theorem exists_natural_of_inClassX (hE2 : SolomonAlternatingBlockK) {K N : Subgroup G}
    (hG : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (hs : IsSimpleGroup G)
    (hc : CFSG.Assembly.IsCharTwoType G)
    (hN : IsMaximalTwoLocal N) (hKN : K ≤ N) (hsub : (K.subgroupOf N).IsSubnormal)
    (hX : InClassX ↥K) (hu : maximalTwoLocalsContaining (K : Set G) = {N})
    (hnoG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4) :
    ∃ m : ℕ, 2 ≤ m ∧ IsNaturalSLTwoModule ↥K m := by
  obtain ⟨hshort, halt | ⟨m, hm, hnat⟩⟩ := hX
  · exact absurd (hE2 G hG hs hc N K hN hKN hsub ⟨hshort, Or.inl halt⟩ halt hu) hnoG4
  · refine ⟨m, ?_, hnat⟩
    by_contra hlt
    have hm1 : m = 1 := by omega
    subst hm1
    exact not_isNaturalSLTwoModule_one' hshort hnat

theorem T2Hyp.of_inClassX {L M : Subgroup G} {n : ℕ} (h : T2Hyp G L M n)
    (hE2 : SolomonAlternatingBlockK) {K N : Subgroup G} (hN : IsMaximalTwoLocal N)
    (hKN : K ≤ N) (hsub : (K.subgroupOf N).IsSubnormal) (hX : InClassX ↥K)
    (hu : maximalTwoLocalsContaining (K : Set G) = {N})
    (hnoG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4) : ∃ m : ℕ, T2Hyp G K N m := by
  obtain ⟨m, hm, hnat⟩ := exists_natural_of_inClassX hE2 h.kproper h.simple h.charTwo hN hKN
    hsub hX hu hnoG4
  exact ⟨m, ⟨h.kproper, h.simple, h.charTwo, hX, hN, hKN, hsub, hu, hm, hnat⟩⟩

@[expose] def Print53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ), T2Hyp G L M n →
    CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → T ≤ M →
    (∀ N : Subgroup G, IsMaximalTwoLocal N → T ≤ N → N = M) →
    ¬ CFSG.GH74.SectionalTwoRankLE G 4 →
    ∃ N K : Subgroup G, IsMaximalTwoLocal N ∧ N ≠ M ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ N) N ∧ InClassX ↥K ∧
      (K.subgroupOf N).IsSubnormal ∧ maximalTwoLocalsContaining (K : Set G) = {N}

namespace T2Hyp

variable {L M T : Subgroup G} {n : ℕ}

theorem isSylowOf_top (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (h47 : Subgroup.normalizer (thompsonJ T : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ :=
  isSylowOf_top_of_normalizer_le hT ((normalizer_le_normalizer_thompsonJ T).trans h47)

theorem five_three (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hE2 : SolomonAlternatingBlockK) (hE5 : Aschbacher78One) (h53 : Print53)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hTG : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hnG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4) :
    ∃ N : Subgroup G, IsMaximalTwoLocal N ∧ T ≤ N ∧ N ≠ M := by
  by_contra hcon
  have hall : ∀ N : Subgroup G, IsMaximalTwoLocal N → T ≤ N → N = M := by
    intro N hN hTN
    by_contra hNM
    exact hcon ⟨N, hN, hTN, hNM⟩
  obtain ⟨N, K, hN, hNM, hTN, hX, hsub, hu⟩ := h53 G L M T n h hTG hT.le hall hnG4
  have hKN : K ≤ N := by
    have : N ∈ maximalTwoLocalsContaining (K : Set G) := by rw [hu]; rfl
    exact fun x hx => this.2 hx
  obtain ⟨m, hK⟩ := h.of_inClassX hE2 hN hKN hsub hX hu hnG4
  have hNT : Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) ≤ N :=
    hK.four_six hE1 hE5 hTN hnG4
  have hTle : T ≤ N := le_of_normalizer_inf_le hTG.isPGroup hNT
  exact hNM (hall N hN hTle)

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
