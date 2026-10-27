module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39Both
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigQInv

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

section Transport

variable {Y Q : Type} [Group Y] [Finite Y] [Group Q]

theorem reflTransGen_commFourAdj_map (ψ : Y →* Q) (hker : Odd (Nat.card ψ.ker)) {E F : Subgroup Y}
    (h : Relation.ReflTransGen (CommFourAdj Y) E F) :
    Relation.ReflTransGen (CommFourAdj Q) (E.map ψ) (F.map ψ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨hb, hc, hbc'⟩ := hbc
    refine ih.tail ⟨isKleinFour_map_of_odd_ker ψ hker hb, isKleinFour_map_of_odd_ker ψ hker hc, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp (hbc' hx)) y hy]

theorem isTwoDisconnected_of_quot (ψ : Y →* Q) (hψ : Function.Surjective ψ)
    (hker : Odd (Nat.card ψ.ker)) (h : IsTwoDisconnected Q) : IsTwoDisconnected Y := by
  obtain ⟨Eb, Fb, hEb, hFb, hn⟩ := h
  have hrange : ∀ A : Subgroup Q, A ≤ ψ.range := fun A => by
    rw [MonoidHom.range_eq_top.mpr hψ]
    exact le_top
  obtain ⟨E, hE, hEm⟩ := exists_isKleinFour_map_eq_of_le_range ψ hker hEb (hrange Eb)
  obtain ⟨F, hF, hFm⟩ := exists_isKleinFour_map_eq_of_le_range ψ hker hFb (hrange Fb)
  refine ⟨E, F, hE, hF, fun hc => hn ?_⟩
  have h1 := reflTransGen_commFourAdj_map ψ hker hc
  rwa [hEm, hFm] at h1

end Transport

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isTwoDisconnected_of_le_of_mem {K Q : Subgroup G} (hKQ : K ≤ Q)
    (hinv : ∀ d ∈ Q, d * d = 1 → d ∈ K) (h : IsTwoDisconnected ↥K) : IsTwoDisconnected ↥Q := by
  obtain ⟨E, F, hE, hF, hn⟩ := h
  obtain ⟨ι, hι⟩ : ∃ ι : ↥K →* ↥Q, ι = Subgroup.inclusion hKQ := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := by
    rw [hι]
    exact Subgroup.inclusion_injective hKQ
  have hrange : ∀ A : Subgroup ↥Q, IsKleinFour A → A ≤ ι.range := fun A hA a ha => by
    have ha2 : (a : G) * a = 1 := by
      have h2 := congrArg Subtype.val (FooteLit.sq_eq_one_of_isKleinFour hA ha)
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two] at h2
      exact h2
    refine MonoidHom.mem_range.mpr ⟨⟨(a : G), hinv (a : G) a.2 ha2⟩, ?_⟩
    rw [hι]
    rfl
  have hfour : ∀ A : Subgroup ↥Q, IsKleinFour A → IsKleinFour (A.comap ι) := fun A hA => by
    have hmap : (A.comap ι).map ι = A := Subgroup.map_comap_eq_self (hrange A hA)
    refine FooteLit.isKleinFour_of_card_eq_four ?_ fun y hy => ?_
    · rw [← Subgroup.card_map_of_injective hιinj, hmap, hA.card_four]
    · apply hιinj
      rw [map_pow, map_one]
      exact FooteLit.sq_eq_one_of_isKleinFour hA (Subgroup.mem_comap.mp hy)
  have hmapfour : ∀ A : Subgroup ↥K, IsKleinFour A → IsKleinFour (A.map ι) := fun A hA => by
    refine FooteLit.isKleinFour_of_card_eq_four ?_ fun y hy => ?_
    · rw [Subgroup.card_map_of_injective hιinj, hA.card_four]
    · obtain ⟨e, he, rfl⟩ := hy
      rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hA he, map_one]
  refine ⟨E.map ι, F.map ι, hmapfour E hE, hmapfour F hF, fun hc => hn ?_⟩
  have key : ∀ A : Subgroup ↥Q, Relation.ReflTransGen (CommFourAdj ↥Q) (E.map ι) A →
      Relation.ReflTransGen (CommFourAdj ↥K) E (A.comap ι) := by
    intro A hA
    induction hA with
    | refl =>
      rw [Subgroup.comap_map_eq_self_of_injective hιinj]
    | tail _ hbc ih =>
      obtain ⟨hb, hc', hbc'⟩ := hbc
      refine ih.tail ⟨hfour _ hb, hfour _ hc', fun x hx => ?_⟩
      rw [mem_centralizer_iff]
      intro y hy
      apply hιinj
      rw [map_mul, map_mul]
      exact (mem_centralizer_iff.mp (hbc' (Subgroup.mem_comap.mp hx))) (ι y)
        (Subgroup.mem_comap.mp hy)
  have h1 := key _ hc
  rwa [Subgroup.comap_map_eq_self_of_injective hιinj] at h1

omit [Finite G] in
theorem eq_or_eq_of_mem_kStarComponents {N K K' M : Subgroup G}
    (hr : (kStarComponents N).ncard = 2) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (hM : M ∈ kStarComponents N) :
    M = K ∨ M = K' := by
  obtain ⟨x, y, hxy, hxyeq⟩ := Set.ncard_eq_two.mp hr
  rw [hxyeq] at hK hK' hM
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK hK' hM
  rcases hK with rfl | rfl <;> rcases hK' with rfl | rfl <;> rcases hM with rfl | rfl <;> simp_all

theorem mem_coreActionKernel_solomonKStarOf_of_mem {N K K' : Subgroup G}
    (hr : (kStarComponents N).ncard = 2) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {z : G}
    (hz : z ∈ ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ⊓ coreActionKernel K) :
    z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N) := by
  have hzM : z ∈ oddTwoCoreIn N ⊔ twoLayerIn N := (mem_inf.mp (mem_inf.mp hz).1).1
  have hMN : oddTwoCoreIn N ⊔ twoLayerIn N ≤ N := sup_le (map_subtype_le _) (map_subtype_le _)
  refine mem_inf.mpr ⟨hzM, mem_coreActionKernel_solomonKStarOf (hMN hzM) fun M hM => ?_⟩
  rcases eq_or_eq_of_mem_kStarComponents hr hK hK' hne hM with rfl | rfl
  · exact (mem_inf.mp hz).2
  · exact (mem_inf.mp (mem_inf.mp hz).1).2

@[expose] def Lemma39TwoDiscKZAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      (∃ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
        orderOf z = 2) →
      ¬ (IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)) ∧
          IsInvolutionCoreFree (coreQuot K' ⧸ center (coreQuot K'))) →
      K' ≤ normalizer (wGroup B V : Set G) →
        ((IsTwoDisconnected (coreQuot K) ∧ IsSolomonI (coreQuot K)) ∨
            CFSG.Open.pRank 2 K ≤ 2) →
        (center (coreQuot K) ≠ ⊥ ∨ ¬ (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)

theorem lemma39TwoDiscKBAt_of_KZ_of_le
    (hI : ∀ (X : Type) [Group X] [Finite X], IsSolomonI X → IsInvolutionCoreFree (X ⧸ center X))
    {R : SigOrientation}
    (hRle : ∀ (G : Type) [Group G] [Finite G] (N K K' : Subgroup G), R G N K K' →
      solRestricted G N K K')
    (h : Lemma39TwoDiscKZAt R) : Lemma39TwoDiscKBAt R := by
  intro G _ _ hG N hN hr K K' V B hP hR hW hnboth hK'H hcase hdisc hconn
  by_cases h3b : ∃ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
      orderOf z = 2
  · refine h G hG N hN hr K K' V B hP hR hW h3b hnboth hK'H hcase ?_ hconn
    rcases hdisc with hZ | hc | hno
    · exact Or.inl hZ
    · exact Or.inr hc
    · obtain ⟨z, hz, hz2⟩ := h3b
      exact absurd hz2 (hno z hz)
  exfalso
  apply hnboth
  obtain ⟨hK, hK', hne, -⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases exists_involution_or_three_le_of_ncard_eq_two hN hr hK hK' hne with
    ⟨z, hz, hz2⟩ | ⟨h3K, h3K', -⟩
  · exact (h3b ⟨z, hz, hz2⟩).elim
  obtain ⟨hKdisc, hKI⟩ : IsTwoDisconnected (coreQuot K) ∧ IsSolomonI (coreQuot K) := by
    rcases hcase with hc | hle
    · exact hc
    · omega
  have hKQ : K ≤ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' :=
    le_inf ((le_twoLayerIn_of_isTwoComponentIn hK.1).trans le_sup_right)
      (le_coreActionKernel_of_ne hK' hK hne.symm)
  have hodd : ∀ z ∈ ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ⊓ coreActionKernel K,
      orderOf z ≠ 2 := fun z hz hz2 =>
    h3b ⟨z, mem_coreActionKernel_solomonKStarOf_of_mem hr hK hK' hne hz, hz2⟩
  have hKdisc' : IsTwoDisconnected ↥K := by
    have hkerodd : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥K)).ker) := by
      rw [QuotientGroup.ker_mk']
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact isTwoDisconnected_of_quot (QuotientGroup.mk' (pPrimeCore 2 ↥K))
      (QuotientGroup.mk'_surjective _) hkerodd hKdisc
  have hQdisc : IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') :=
    isTwoDisconnected_of_le_of_mem hKQ
      (fun d hd hd2 => mem_of_mul_self_eq_one hK hK' hne hodd hd hd2) hKdisc'
  have hK'I : IsSolomonI (coreQuot K') := by
    by_contra hI'
    exact (hRle G N K K' hR hr).1 ⟨hQdisc, by omega, hI'⟩
  exact ⟨hI _ hKI, hI _ hK'I⟩

end CFSG.ComponentClassification.Sol76.Sig
