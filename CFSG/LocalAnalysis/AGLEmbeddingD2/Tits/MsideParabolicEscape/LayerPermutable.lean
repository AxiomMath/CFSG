module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoPermute
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.LiftPermuting

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open scoped Pointwise

theorem lift_permuting_through {M : Type} [Group M] [Finite M] (D L U : Subgroup M) [D.Normal]
    [L.Normal] (hDL : D ≤ L) (hD3 : ¬ 3 ∣ Nat.card D) (hU2 : IsPGroup 2 U)
    (hUD : ¬ 2 ∣ ((U ⊓ D).subgroupOf D).index) (Pb : Subgroup (M ⧸ D))
    (hPbL : Pb ≤ L.map (QuotientGroup.mk' D)) (hPb3 : Nat.card Pb = 3)
    (hperm : (Pb : Set (M ⧸ D)) * (U.map (QuotientGroup.mk' D) : Set (M ⧸ D)) =
      (U.map (QuotientGroup.mk' D) : Set (M ⧸ D)) * Pb) :
    ∃ P₁ : Subgroup M, P₁ ≤ L ∧ Nat.card P₁ = 3 ∧ (P₁ : Set M) * U = (U : Set M) * P₁ := by
  set π : M →* M ⧸ D := QuotientGroup.mk' D with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : π.ker = D := QuotientGroup.ker_mk' D
  set V : Subgroup (M ⧸ D) := U.map π with hV
  set Ω : Subgroup (M ⧸ D) := V ⊔ Pb with hΩ
  set Γ : Subgroup M := Ω.comap π with hΓ
  have hDΓ : D ≤ Γ := by
    intro d hd
    show π d ∈ Ω
    have : π d = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hd
    rw [this]
    exact Ω.one_mem
  have hUΓ : U ≤ Γ := fun u hu => (le_sup_left : V ≤ Ω) ⟨u, hu, rfl⟩
  have hUpre : U ⊔ D = V.comap π := by
    apply le_antisymm
    · refine sup_le (fun u hu => ⟨u, hu, rfl⟩) (fun d hd => ?_)
      show π d ∈ V
      have : π d = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hd
      rw [this]
      exact V.one_mem
    · intro x hx
      obtain ⟨u, hu, hux⟩ := hx
      have hD : u⁻¹ * x ∈ D := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel]
      have : x = u * (u⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (le_sup_left (a := U) (b := D) hu) (le_sup_right (a := U) hD)
  have hV2 : IsPGroup 2 V := hU2.map π
  have hPbV : Pb ⊓ V = ⊥ := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    exact (Subgroup.disjoint_of_coprime_natCard (by
      rw [hPb3, hk]; exact Nat.Coprime.pow_right k (by norm_num))).eq_bot
  have hfac : ∀ x ∈ Pb ⊔ V, ∃ p ∈ Pb, ∃ r ∈ V, x = p * r := by
    intro x hx
    rw [← SetLike.mem_coe, CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.coe_sup_eq_mul_of_permutable hperm,
      Set.mem_mul] at hx
    obtain ⟨p, hp, r, hr, rfl⟩ := hx
    exact ⟨p, hp, r, hr, rfl⟩
  have hVΩ : V.relIndex Ω = 3 := by
    rw [hΩ, sup_comm]
    exact relIndex_sup_eq_three_of_mul hPb3 hPbV hfac
  have hrel : (U ⊔ D).relIndex Γ = 3 := by
    rw [hUpre, hΓ, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hsurj]
    exact hVΩ
  have hD3' : ¬ 3 ∣ Nat.card (D.subgroupOf Γ) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDΓ).toEquiv]
  have hU2' : IsPGroup 2 (U.subgroupOf Γ) :=
    hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUΓ).symm
  have hUD' : ¬ 2 ∣ (((U.subgroupOf Γ) ⊓ (D.subgroupOf Γ)).subgroupOf (D.subgroupOf Γ)).index := by
    have hinf : (U.subgroupOf Γ) ⊓ (D.subgroupOf Γ) = (U ⊓ D).subgroupOf Γ := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hinf]
    have h := Subgroup.relIndex_subgroupOf (H := U ⊓ D) hDΓ
    show ¬ 2 ∣ ((U ⊓ D).subgroupOf Γ).relIndex (D.subgroupOf Γ)
    rw [h]
    exact hUD
  have hidx' : ((U.subgroupOf Γ) ⊔ (D.subgroupOf Γ)).index = 3 := by
    rw [← Subgroup.subgroupOf_sup hUΓ hDΓ]
    exact hrel
  obtain ⟨P'', hP''3, hP''perm⟩ :=
    exists_order_three_permuting_of_normal_coprime (D.subgroupOf Γ) (U.subgroupOf Γ) hD3' hU2' hUD'
      hidx'
  set P₁ : Subgroup M := P''.map Γ.subtype with hP₁
  have hP₁Γ : P₁ ≤ Γ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨P₁, ?_, ?_, ?_⟩
  ·
    have hΓUL : Γ ≤ U ⊔ L := by
      have h1 : Ω ≤ (U ⊔ L).map π :=
        sup_le (Subgroup.map_mono le_sup_left) (hPbL.trans (Subgroup.map_mono le_sup_right))
      have h2 : π.ker ≤ U ⊔ L := by rw [hker]; exact hDL.trans le_sup_right
      calc Γ ≤ ((U ⊔ L).map π).comap π := Subgroup.comap_mono h1
        _ = U ⊔ L := Subgroup.comap_map_eq_self h2
    intro x hx
    have hxUL : x ∈ U ⊔ L := hΓUL (hP₁Γ hx)
    have hxm : x ∈ ((U : Set M) * (L : Set M)) := by
      have h : x ∈ ((U ⊔ L : Subgroup M) : Set M) := hxUL
      rwa [Subgroup.mul_normal] at h
    obtain ⟨u, hu, l, hl, rfl⟩ := Set.mem_mul.mp hxm
    have hx3 : (u * l) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥P₁) (x := ⟨u * l, hx⟩)
      rw [show Nat.card ↥P₁ = 3 by
        rw [hP₁, Subgroup.card_map_of_injective Γ.subtype_injective]; exact hP''3] at this
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := hU2 ⟨u, hu⟩
    have hu2 : u ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    set ρ : M →* M ⧸ L := QuotientGroup.mk' L with hρ
    have hρl : ρ l = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hl
    have h3 : (ρ u) ^ 3 = 1 := by
      have := congrArg ρ hx3
      rwa [map_pow, map_mul, hρl, mul_one, map_one] at this
    have h2 : (ρ u) ^ (2 ^ k) = 1 := by rw [← map_pow, hu2, map_one]
    have hg : (ρ u) ^ (Nat.gcd 3 (2 ^ k)) = 1 := pow_gcd_eq_one.mpr ⟨h3, h2⟩
    have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    rw [hcop, pow_one] at hg
    have huL : u ∈ L := by
      rw [← QuotientGroup.ker_mk' L, MonoidHom.mem_ker]
      exact hg
    exact L.mul_mem huL hl
  · rw [hP₁, Subgroup.card_map_of_injective Γ.subtype_injective]
    exact hP''3
  · have hUmap : (U.subgroupOf Γ).map Γ.subtype = U := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hUΓ]
    have h := congrArg (fun S : Set Γ => (Γ.subtype : Γ →* M) '' S) hP''perm
    simp only [Set.image_mul] at h
    have e1 : ((Γ.subtype : Γ →* M) '' (P'' : Set Γ)) = (P₁ : Set M) := by
      rw [hP₁, Subgroup.coe_map]
    have e2 : ((Γ.subtype : Γ →* M) '' ((U.subgroupOf Γ : Subgroup Γ) : Set Γ)) = (U : Set M) := by
      rw [← Subgroup.coe_map, hUmap]
    rw [e1, e2] at h
    exact h

@[expose] def D2L34BetaLayerSylow : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ U : Subgroup G, IsBetaBase H M U → A ≤ Subgroup.normalizer (U : Set G) →
      Subgroup.normalizer (U : Set G) ≤ H →
      IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) →
      IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) →
      ∀ L : Subgroup G, IsRankTwoLayer M L → IsSylowTwoOf (starImg M U ⊓ starImg M L) (starImg M L)

theorem normal_starImg {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hLn : (L.subgroupOf M).Normal) : (starImg M L).Normal :=
  Subgroup.Normal.map hLn _ (QuotientGroup.mk'_surjective _)

@[expose] def D2L34BetaLayerAutImage : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ L : Subgroup G, ∀ hlay : IsRankTwoLayer M L,
      haveI : (starImg M L).Normal := normal_starImg hlay.2.2.1
      AutImageOK (starImg M L)

theorem exists_permuting_of_rankTwoLayer {G : Type} [Group G] [Finite G]
    (hK : KFactRankTwoSylowPermute) {M U L : Subgroup G} (hU2 : IsPGroup 2 U) (hUM : U ≤ M)
    (hsylU : IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M)) (hlay : IsRankTwoLayer M L)
    (hVN : IsSylowTwoOf (starImg M U ⊓ starImg M L) (starImg M L))
    (hok : haveI : (starImg M L).Normal := normal_starImg hlay.2.2.1
      AutImageOK (starImg M L)) :
    ∃ P₁ : Subgroup G, P₁ ≤ L ∧ Nat.card P₁ = 3 ∧ (P₁ : Set G) * U = U * P₁ := by
  have ⟨hLM, hDL, hLn, hs, hnc, hty⟩ := hlay
  have hNs : (starImg M L).Normal := normal_starImg hLn
  have hU2' : IsPGroup 2 (U.subgroupOf M) := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUM).symm
  have hV2 : IsPGroup 2 (starImg M U) := hU2'.map _
  obtain ⟨Pb, hPbN, hPb3, hperm⟩ := exists_permuting_of_kfact hK hs hnc hty hV2 hVN hok
  have hDM : GLBPrimeCore 3 M ≤ M := glbPrimeCore_le 3 M
  have hD3 : ¬ 3 ∣ Nat.card ((GLBPrimeCore 3 M).subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
  have hUD : ¬ 2 ∣ (((U.subgroupOf M) ⊓ (GLBPrimeCore 3 M).subgroupOf M).subgroupOf
      ((GLBPrimeCore 3 M).subgroupOf M)).index := by
    have hinf : (U.subgroupOf M) ⊓ (GLBPrimeCore 3 M).subgroupOf M =
        (U ⊓ GLBPrimeCore 3 M).subgroupOf M := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hinf]
    have h := Subgroup.relIndex_subgroupOf (H := U ⊓ GLBPrimeCore 3 M) hDM
    show ¬ 2 ∣ ((U ⊓ GLBPrimeCore 3 M).subgroupOf M).relIndex ((GLBPrimeCore 3 M).subgroupOf M)
    rw [h]
    exact hsylU.2.2
  have hDL' : (GLBPrimeCore 3 M).subgroupOf M ≤ L.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hDL (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨P₁M, hP₁L, hP₁c, hP₁perm⟩ := lift_permuting_through (M := ↥M)
    ((GLBPrimeCore 3 M).subgroupOf M) (L.subgroupOf M) (U.subgroupOf M) hDL' hD3 hU2' hUD Pb hPbN
    hPb3 hperm
  refine ⟨P₁M.map M.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hP₁L hx)
  · rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hP₁c
  · have hUmap : (U.subgroupOf M).map M.subtype = U := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hUM]
    have h := congrArg (fun S : Set ↥M => (M.subtype : ↥M →* G) '' S) hP₁perm
    simp only [Set.image_mul] at h
    have e1 : ((M.subtype : ↥M →* G) '' (P₁M : Set ↥M)) =
        ((P₁M.map M.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map]
    have e2 : ((M.subtype : ↥M →* G) '' ((U.subgroupOf M : Subgroup ↥M) : Set ↥M)) =
        (U : Set G) := by
      rw [← Subgroup.coe_map, hUmap]
    rw [e1, e2] at h
    exact h

theorem d2L34BetaLayerPermutable_of (hK : KFactRankTwoSylowPermute) (hSyl : D2L34BetaLayerSylow)
    (hAut : D2L34BetaLayerAutImage) : D2L34BetaLayerPermutable := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax hcon U hU hAU hNHU hsylU hUQ L hlay
  exact exists_permuting_of_rankTwoLayer hK hU.1
    ((hUQ.1.trans (glbPrimeCore_le 3 _)).trans inf_le_right) hsylU hlay
    (hSyl d G P M A H R Rbar K hc hstr hAll hKmax hcon U hU hAU hNHU hsylU hUQ L hlay)
    (hAut d G P M A H R Rbar K hc hstr hAll hKmax hcon L hlay)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
