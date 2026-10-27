module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ThreeRed
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Central
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3SmallAut
public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlphaOut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open scoped Pointwise

@[expose] def Bal3IsLinThreeCover (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, d.1 = .A 2 q ∧ 3 ∣ q.card - 1) ∨
  (∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1)

@[expose] def Bal3ThreeCovers : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsCatalogGroup (K ⧸ center K) →
    center K ≠ ⊥ → IsPGroup 3 (center K) → IsCyclic (center K) →
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
    Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) ∨
    Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, Bal3IsLinThreeCover d ∧
      Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def Bal3ThreeCenter : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsCatalogGroup (K ⧸ center K) →
    center K ≠ ⊥ → IsPGroup 3 (center K) → CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
    IsCyclic (center K) ∧ Nat.card (center K) = 3

@[expose] def Bal3SmallCards : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → center K ≠ ⊥ →
    IsPGroup 3 (center K) → IsCyclic (center K) →
    (Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group)) →
    ∀ B : Subgroup (MulAut K), IsPGroup 3 B → Nat.card B ≤ 9

@[expose] def Bal3OnanComm : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → center K ≠ ⊥ →
    IsPGroup 3 (center K) → IsCyclic (center K) →
    Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) →
    CFSG.AGLEmbedding.KOutTwoGroup K ∧ (∀ T : Sylow 3 K, ∀ t ∈ (T : Subgroup K), t ^ 3 = 1) ∧
      ∀ T : Sylow 3 K, ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K),
        x * y * x⁻¹ * y⁻¹ ∈ center K

@[expose] def Bal3ThreeSL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ (P : Sylow 3 X) (z : X) (D : Subgroup X), RedConfig 3 P z D → z ∈ CFSG.pCore 3 X →
      ∀ K : Subgroup X, IsComponentOf K ⊤ → (∀ L : Subgroup X, IsComponentOf L ⊤ → L = K) →
        (∃ d : TauCeti.ValidLieTypeIndex, Bal3IsLinThreeCover d ∧
          Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.lie d).Group)) → False


section Glue

variable {X : Type} [Group X] [Finite X]

theorem mem_zpowers_of_center {K : Subgroup X} {z : X} (hzK : z ∈ K)
    (hzc : ∀ k ∈ K, z * k = k * z) (hzo : orderOf z = 3) (hZ : Nat.card (center K) = 3) :
    ∀ x ∈ K, (∀ k ∈ K, x * k = k * x) → x ∈ zpowers z := by
  intro x hxK hxc
  have hzZ : (⟨z, hzK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hzc k k.2).symm
  have hxZ : (⟨x, hxK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hxc k k.2).symm
  have hz3 : orderOf (⟨⟨z, hzK⟩, hzZ⟩ : center K) = 3 := by
    rw [← hzo, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  have hcard : Nat.card (zpowers (⟨⟨z, hzK⟩, hzZ⟩ : center K)) = Nat.card (center K) := by
    rw [Nat.card_zpowers, hz3, hZ]
  have htop : zpowers (⟨⟨z, hzK⟩, hzZ⟩ : center K) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ hcard
  have hmem : (⟨⟨x, hxK⟩, hxZ⟩ : center K) ∈ zpowers (⟨⟨z, hzK⟩, hzZ⟩ : center K) := by
    rw [htop]; exact mem_top _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  refine mem_zpowers_iff.2 ⟨k, ?_⟩
  have := congrArg (fun w : center K => ((w : K) : X)) hk
  simpa using this

end Glue

theorem bal3ThreeSingleRed_of_covers (hC : Bal3ThreeCovers) (hZ : Bal3ThreeCenter)
    (hS : Bal3SmallCards) (hO : Bal3OnanComm) (hL : Bal3ThreeSL3) : Bal3ThreeSingleRed := by
  classical
  intro X _ _ hcat P z D hred hz K hK huniq
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  haveI hKn : K.Normal :=
    Subgroup.Normal.of_conjugate_fixed (fun g => huniq _ (isComponentOf_conj_smul hK g))
  have hPn : (P : Subgroup X) ≤ normalizer (K : Set X) := by
    rw [normalizer_eq_top]; exact le_top
  have hzK : z ∈ K := hred.mem_component hK hPn
  have hzC : z ∈ centralizer (K : Set X) :=
    mem_centralizer_component_of_mem_pCore hp3 hred.core hz hK
  have hzc : ∀ k ∈ K, z * k = k * z := fun k hk => (mem_centralizer_iff.1 hzC k hk).symm
  have hzZ : (⟨z, hzK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hzc k k.2).symm
  have hZne : center K ≠ ⊥ := by
    intro hbot
    rw [hbot, mem_bot] at hzZ
    have hz1 : z = 1 := congrArg Subtype.val hzZ
    have := hred.ord
    rw [hz1, orderOf_one] at this
    exact hp3.one_lt.ne this
  have hZp : IsPGroup 3 (center K) := isPGroup_center_of_isComponentOf hp3 hred.core hK
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
    hK.2.2
  have hcatK : IsCatalogGroup (K ⧸ center K) :=
    hcat K (center K) inferInstance hK.2.2.2 hnonab
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    have hKX : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 hp3 K.subtype
        K.subtype_injective]
      exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp3 le_top
    rw [hred.pRank_top] at hKX
    exact hKX
  obtain ⟨hcyc, hcard⟩ := hZ K hK.2.2 hcatK hZne hZp hrk
  have hfam := hC K hK.2.2 hcatK hZne hZp hcyc hrk
  have hTnc : ¬ ∀ x ∈ (P : Subgroup X) ⊓ K, ∀ y ∈ (P : Subgroup X) ⊓ K, x * y = y * x := by
    intro hall
    refine not_isMulCommutative_inf (by norm_num) P hK hPn
      (hred.dvd_card_center_component hz hK hPn) ⟨⟨fun a b => Subtype.ext (hall a a.2 b b.2)⟩⟩
  have finish : (∀ u ∈ (P : Subgroup X), ∃ t ∈ (P : Subgroup X) ⊓ K,
        ∃ c ∈ (P : Subgroup X) ⊓ centralizer (K : Set X), t * c = u) →
      (∀ x ∈ (P : Subgroup X) ⊓ K, ∀ y ∈ (P : Subgroup X) ⊓ K,
        x * y * x⁻¹ * y⁻¹ ∈ zpowers z) → False := by
    intro hdec hcomm
    refine false_of_plane_in_central_product (P := (P : Subgroup X))
      (T := (P : Subgroup X) ⊓ K) (R := (P : Subgroup X) ⊓ centralizer (K : Set X)) (D := D)
      (z := z) P.isPGroup' inf_le_left inf_le_left
      (fun u hu => by
        obtain ⟨t, ht, c, hc, rfl⟩ := hdec u hu
        exact ⟨t, ht, c, hc, rfl⟩)
      (fun t ht r hr => (mem_centralizer_iff.1 hr.2 t ht.2))
      hred.ord ⟨hred.le hred.mem, hzK⟩ ⟨hred.le hred.mem, hzC⟩
      (fun y hy => mem_centralizer_iff.1 hred.central y hy)
      (fun x hx hxR => mem_zpowers_of_center hzK hzc hred.ord hcard x hx.2
        (fun k hk => (mem_centralizer_iff.1 hxR.2 k hk).symm))
      hcomm hTnc hred.le hred.elem hred.card hred.mem
      (fun x hxP hxC => hred.mem_of_mem_inf_centralizer hxP hxC) hred.rank
  rcases hfam with e | e | e | e | ⟨d, hd, e⟩
  ·
    obtain ⟨hdec, hcomm⟩ := sylow_eq_mul_of_small_aut P K hK.2.2 hzK hzc hred.ord hcard
      (hS K hK.2.2 hZne hZp hcyc (Or.inl e))
    exact finish hdec hcomm
  · obtain ⟨hdec, hcomm⟩ := sylow_eq_mul_of_small_aut P K hK.2.2 hzK hzc hred.ord hcard
      (hS K hK.2.2 hZne hZp hcyc (Or.inr (Or.inl e)))
    exact finish hdec hcomm
  · obtain ⟨hdec, hcomm⟩ := sylow_eq_mul_of_small_aut P K hK.2.2 hzK hzc hred.ord hcard
      (hS K hK.2.2 hZne hZp hcyc (Or.inr (Or.inr e)))
    exact finish hdec hcomm
  ·
    obtain ⟨hout, -, hab⟩ := hO K hK.2.2 hZne hZp hcyc e
    refine finish (fun u hu => exists_mul_eq_of_kOutTwoGroup hp3 (by norm_num) P hout hu) ?_
    intro x hx y hy
    obtain ⟨Q, hQ⟩ := (isSylowOf_inf_of_le_normalizer P hPn).exists_sylow_eq_subgroupOf
    have hxQ : (⟨x, hx.2⟩ : K) ∈ (Q : Subgroup K) := by
      rw [hQ]; exact Subgroup.mem_subgroupOf.2 hx
    have hyQ : (⟨y, hy.2⟩ : K) ∈ (Q : Subgroup K) := by
      rw [hQ]; exact Subgroup.mem_subgroupOf.2 hy
    have hcz := hab Q _ hxQ _ hyQ
    refine mem_zpowers_of_center hzK hzc hred.ord hcard _
      (K.mul_mem (K.mul_mem (K.mul_mem hx.2 hy.2) (K.inv_mem hx.2)) (K.inv_mem hy.2)) ?_
    intro k hk
    have := mem_center_iff.1 hcz ⟨k, hk⟩
    exact (congrArg Subtype.val this).symm
  · exact hL X hcat P z D hred hz K hK huniq ⟨d, hd, e⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
