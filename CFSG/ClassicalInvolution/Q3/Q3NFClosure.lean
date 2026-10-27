module

public import CFSG.ClassicalInvolution.Q3.Closure
public import CFSG.ClassicalInvolution.Q3.Q3NLFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL

section Closure

variable {G : Type} [Group G]

@[expose] def InvolutionLinkSpan3 (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G))
    (a : G) : Prop :=
  ∀ M ∈ centralizingMembers Ω {a}, ∀ z : G, IsClassicalMember3 M z →
    ∃ K ∈ S, ∃ z' ∈ A, IsClassicalMember3 K z' ∧ ∃ h ∈ rankTwoSpan A, z = h * z' * h⁻¹

structure FrameSideLayers3 (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) :
    Prop where
  subset : S ⊆ Ω
  nonempty : S.Nonempty
  involution : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z
  layer : ∀ a ∈ A, IsFrameInvolution3 S a → centralizingLayer Ω {a} ≤ rankTwoSpan A
  link : ∀ a ∈ A, IsFrameInvolution3 S a → InvolutionLinkSpan3 Ω A S a

variable [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G} {S : Set (Subgroup G)}

theorem le_rankTwoSpan_of_mem_omegaStarTwo3' (hΩ : InClass3 Ω) (hF : FrameSideLayers3 Ω A S)
    {L : Subgroup G} (hLs : L ∈ omegaStarTwo3 Ω A S) : L ≤ rankTwoSpan A := by
  obtain ⟨hLΩ, h, hh, K, hK, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember3_conj_inv hLa
  have hmem : conjSub h⁻¹ L ∈ centralizingMembers Ω {a} :=
    ⟨hconj _ _ hLΩ, isSubnormal_le hLa'.subnormal⟩
  have hY : conjSub h⁻¹ L ≤ rankTwoSpan A :=
    (le_centralizingLayer hmem).trans (hF.layer a haA ⟨K, hK, hKa⟩)
  intro x hx
  have h1 : h⁻¹ * x * h ∈ conjSub h⁻¹ L := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have h2 := hY h1
  have h3 : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

theorem mem_omegaStarTwo3_of_commutes' (hΩ : InClass3 Ω) (hF : FrameSideLayers3 Ω A S)
    {L L' : Subgroup G} (hLs : L ∈ omegaStarTwo3 Ω A S) (hL' : L' ∈ Ω) (hc : Commutes L L') :
    L' ∈ omegaStarTwo3 Ω A S := by
  obtain ⟨hLΩ, h₀, hh₀, K, hKS, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember3_conj_inv hLa
  have hc' : Commutes (conjSub h₀⁻¹ L) (conjSub h₀⁻¹ L') := hc.conjSub h₀⁻¹
  set M := conjSub h₀⁻¹ L' with hM
  have hMΩ : M ∈ Ω := hconj _ _ hL'
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc' a hLa'.mem x hx).symm
  have hMmem : M ∈ centralizingMembers Ω {a} := ⟨hMΩ, hMa⟩
  obtain ⟨z₀, hz₀⟩ := hΩ.classical M hMΩ
  obtain ⟨K', hK'S, z', hz'A, hK'z', h₁, hh₁Y, hz₀h₁⟩ :=
    hF.link a haA ⟨K, hKS, hKa⟩ M hMmem z₀ hz₀
  have hz₀' : IsClassicalMember3 M (h₁ * z' * h₁⁻¹) := by rwa [← hz₀h₁]
  have hL'z : IsClassicalMember3 L' (h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹) := by
    have := hz₀'.conj h₀
    rwa [hM, conjSub_conjSub_inv] at this
  refine ⟨hL', h₀ * h₁, mul_mem hh₀ hh₁Y, K', hK'S, z', hz'A, hK'z', ?_⟩
  have e : h₀ * h₁ * z' * (h₀ * h₁)⁻¹ = h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹ := by group
  rwa [e]

theorem mem_omegaStarTwo3_of_omegaConnected' (hΩ : InClass3 Ω) (hF : FrameSideLayers3 Ω A S)
    (hconn : OmegaConnected Ω) {L : Subgroup G} (hLΩ : L ∈ Ω) : L ∈ omegaStarTwo3 Ω A S := by
  obtain ⟨K₀, hK₀⟩ := hF.nonempty
  obtain ⟨z, hzA, hz⟩ := hF.involution K₀ hK₀
  have hK₀s : K₀ ∈ omegaStarTwo3 Ω A S :=
    ⟨hF.subset hK₀, 1, one_mem _, K₀, hK₀, z, hzA, hz, by simpa using hz⟩
  have key : ∀ L', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) K₀ L' →
      L' ∈ omegaStarTwo3 Ω A S := by
    intro L' hpath
    induction hpath with
    | refl => exact hK₀s
    | tail _ hbc ih => exact mem_omegaStarTwo3_of_commutes' hΩ hF ih hbc.1 hbc.2
  exact key L (hconn K₀ (hF.subset hK₀) L hLΩ)

theorem rankTwoSpan_eq_top3_of_layers (hΩ : InClass3 Ω) (hF : FrameSideLayers3 Ω A S)
    (hconn : OmegaConnected Ω) : rankTwoSpan A = ⊤ := by
  refine top_unique ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun _ hLΩ => le_rankTwoSpan_of_mem_omegaStarTwo3' hΩ hF
    (mem_omegaStarTwo3_of_omegaConnected' hΩ hF hconn hLΩ)

end Closure

section Normalizes

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem oddCoreIn_le_rankTwoSpan_of_normalizes {Y : Subgroup G} (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) (hnorm : A ≤ Subgroup.normalizer (oddCoreIn Y : Set G)) :
    oddCoreIn Y ≤ rankTwoSpan A := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A (oddCoreIn Y) hA (by simpa using h8) hnorm
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

theorem mem_normalizer_centralizingLayer_of_secData {Φ : Set (Subgroup G)} {a : G}
    (hΦ : SecData3 a Φ) {n : G} (hn : n ∈ Subgroup.centralizer ({a} : Set G)) :
    n ∈ Subgroup.normalizer (centralizingLayer Φ {a} : Set G) := by
  have key : ∀ m ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ centralizingLayer Φ {a},
      m * y * m⁻¹ ∈ centralizingLayer Φ {a} := by
    intro m hm y hy
    have hle : centralizingLayer Φ {a} ≤
        (centralizingLayer Φ {a}).comap (MulAut.conj m).toMonoidHom := by
      refine iSup₂_le fun L hL x hx => ?_
      have hmem : conjSub m L ∈ centralizingMembers Φ {a} := by
        refine ⟨hΦ.conj m hm L hL.1, fun x hx => ?_⟩
        rw [mem_conjSub_iff] at hx
        have hx' := hΦ.le L hL.1 hx
        have : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hx') ((Subgroup.inv_mem _) hm)
      exact le_centralizingLayer hmem (conj_mem_conjSub hx)
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key n hn y hy, fun hy => ?_⟩
  have := key n⁻¹ ((Subgroup.centralizer ({a} : Set G)).inv_mem hn) _ hy
  simpa [mul_assoc] using this

theorem normalizes_oddCoreIn_centralizingLayer_of_secData {Φ : Set (Subgroup G)} {a : G}
    (hΦ : SecData3 a Φ) (hA : IsElemAbelian 2 A) (ha : a ∈ A) :
    A ≤ Subgroup.normalizer (oddCoreIn (centralizingLayer Φ {a}) : Set G) := fun _ hg =>
  mem_normalizer_oddCoreIn_of_mem_normalizer
    (mem_normalizer_centralizingLayer_of_secData hΦ
      (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hA hg ha)))

theorem centralizingLayer_le_rankTwoSpan_of_secData {Φ : Set (Subgroup G)} {a : G}
    (hΦ : SecData3 a Φ) (hA : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A) (ha : a ∈ A)
    (hgen : centralizingLayer Φ {a} ≤ oddCoreIn (centralizingLayer Φ {a}) ⊔
      ⨆ F ∈ signalizerFunctorEk 2 2 A,
        (Subgroup.centralizer (F : Set G) ⊓ centralizingLayer Φ {a})) :
    centralizingLayer Φ {a} ≤ rankTwoSpan A :=
  hgen.trans (sup_le
    (oddCoreIn_le_rankTwoSpan_of_normalizes hA h8
      (normalizes_oddCoreIn_centralizingLayer_of_secData hΦ hA ha))
    (iSup₂_le fun _ hF => le_rankTwoSpan_of_le_centralizer hF inf_le_left))

end Normalizes

section Exact


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem exactLayer3_le_rankTwoSpan (hΩ : InClass3 Ω) (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) {a : G} (ha : a ∈ A)
    (hgen : exactLayer3 Ω a ≤ oddCoreIn (exactLayer3 Ω a) ⊔
      ⨆ F ∈ signalizerFunctorEk 2 2 A, (Subgroup.centralizer (F : Set G) ⊓ exactLayer3 Ω a)) :
    exactLayer3 Ω a ≤ rankTwoSpan A := by
  by_cases hne : (tqMembers3 Ω a).Nonempty
  · exact centralizingLayer_le_rankTwoSpan_of_secData
      (secData3_exactFamily hΩ (isPGroup_zpowers_of_mem_isElemAbelian3 hA ha) hne) hA h8 ha hgen
  · rw [exactLayer3_eq_bot_of_not_nonempty hne]
    exact bot_le

theorem centralizingLayer_le_rankTwoSpan_of_exact (hΩ : InClass3 Ω) (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) {a : G} (ha : a ∈ A)
    (hgen : exactLayer3 Ω a ≤ oddCoreIn (exactLayer3 Ω a) ⊔
      ⨆ F ∈ signalizerFunctorEk 2 2 A, (Subgroup.centralizer (F : Set G) ⊓ exactLayer3 Ω a)) :
    centralizingLayer Ω {a} ≤ rankTwoSpan A :=
  centralizingLayer_le_exactLayer3.trans (exactLayer3_le_rankTwoSpan hΩ hA h8 ha hgen)

end Exact

end CFSG.ClassicalInvolution.Q3.Q3NF
