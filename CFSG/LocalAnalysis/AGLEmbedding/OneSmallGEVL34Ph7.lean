module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem L34Squeeze.le_of_normalizer_le {U J : Subgroup G} (hUJ : U ≤ J) (hJ : IsPGroup 2 J)
    (hN : J ⊓ Subgroup.normalizer (U : Set G) ≤ U) : J ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc : NormalizerCondition J := by
    have := hJ.isNilpotent
    exact Group.normalizerCondition_of_isNilpotent
  have hself : Subgroup.normalizer (U.subgroupOf J : Set J) = U.subgroupOf J := by
    refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
    have hxN : (x : G) ∈ Subgroup.normalizer (U : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨u, hUJ hu⟩).mp
          (Subgroup.mem_subgroupOf.mpr hu)
        simpa using Subgroup.mem_subgroupOf.mp h1
      · intro hu
        have huJ : u ∈ J := by
          have h2 : (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * (x : G) ∈ J :=
            J.mul_mem (J.mul_mem (J.inv_mem x.2) (hUJ hu)) x.2
          simpa [mul_assoc] using h2
        have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨u, huJ⟩).mpr
          (Subgroup.mem_subgroupOf.mpr (by simpa using hu))
        exact Subgroup.mem_subgroupOf.mp h1
    exact Subgroup.mem_subgroupOf.mpr (hN ⟨x.2, hxN⟩)
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp hnc _ hself
  intro q hq
  have : (⟨q, hq⟩ : J) ∈ U.subgroupOf J := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

omit [Finite G] in
theorem L34Squeeze.le_of_isSylowTwoOf {U V X : Subgroup G} (hsyl : IsSylowTwoOf U X) (hUV : U ≤ V)
    (hVX : V ≤ X) (hV : IsPGroup 2 V) : V ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU' : IsPGroup 2 (U.subgroupOf X) :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm
  let Pu : Sylow 2 X := hU'.toSylow hsyl.2.2
  have hV' : IsPGroup 2 (V.subgroupOf X) := hV.of_equiv (Subgroup.subgroupOfEquivOfLe hVX).symm
  have hle : (Pu : Subgroup X) ≤ V.subgroupOf X := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hUV (Subgroup.mem_subgroupOf.mp hx))
  have heq := Pu.is_maximal' hV' hle
  intro v hv
  have hvX : (⟨v, hVX hv⟩ : X) ∈ V.subgroupOf X := Subgroup.mem_subgroupOf.mpr hv
  rw [heq] at hvX
  exact Subgroup.mem_subgroupOf.mp hvX

theorem L34Squeeze.isSylowTwoOf_of_normalizer_le {U C X : Subgroup G} (hUC : U ≤ C)
    (hU : IsPGroup 2 U) (hNX : C ⊓ Subgroup.normalizer (U : Set G) ≤ X)
    (hsyl : IsSylowTwoOf U X) : IsSylowTwoOf U C := by
  obtain ⟨S₀, hS₀, hUS₀⟩ := EscapingLocal.exists_isSylowTwoOf_ge hUC hU
  have hS₀U : S₀ ≤ U := by
    refine L34Squeeze.le_of_normalizer_le hUS₀ hS₀.2.1 fun x hx => ?_
    obtain ⟨hxS, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxX : x ∈ X := hNX ⟨hS₀.1 hxS, hxN⟩
    have hz2 : IsPGroup 2 (Subgroup.zpowers x) :=
      hS₀.2.1.to_le (Subgroup.zpowers_le.mpr hxS)
    have hVp : IsPGroup 2 ↥((Subgroup.zpowers x) ⊔ U) :=
      hz2.to_sup_of_normal_right' hU (Subgroup.zpowers_le.mpr hxN)
    have hVX : (Subgroup.zpowers x) ⊔ U ≤ X :=
      sup_le (Subgroup.zpowers_le.mpr hxX) hsyl.1
    exact L34Squeeze.le_of_isSylowTwoOf hsyl le_sup_right hVX hVp
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hS₀eq : S₀ = U := le_antisymm hS₀U hUS₀
  exact hS₀eq ▸ hS₀

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_hasPrimeConstraint_of_isSylowTwoOf (hUE : KFactUPrimeExc)
    (hOrb : KFactSmallOrbits) (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime)
    (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (hcon : HasPrimeConstraint (G := M) 3) {V : Subgroup G}
    (hsyl : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)))
    (hNV : M ⊓ Subgroup.normalizer (V : Set G) ≤ H) : False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : (3 = 3 ∧ IsLinThreeFour K) ∨ (3 = 5 ∧ IsFi22 K) := Or.inl ⟨rfl, hL⟩
  obtain ⟨T₁, hT₁, -, -⟩ := hd.inf_eq_glbCore_of_exc hUE hE
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hU3 : ¬ IsSmallUnitary 3 K := fun h => (not_l34_and_not_a6_of_u33 hO h).1 hL
  have hA6 : ¬ IsAltTwoP 3 K := fun h => not_l34_of_a6 hO h hL
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
      hSh3 K hs hn hc T₁ hTnc hΓT hd.small hU3]
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
  have hexpR := hd.pow_eq_one_of_d1LiftX_decomp hExp hz hdec
  set C₀ := GLBPrimeCore 3 M with hC₀def
  have hV2 : IsPGroup 2 V := hsyl.2.1
  have hC₀M : C₀ ≤ M := glbPrimeCore_le 3 M
  have hMC : M ≤ Subgroup.normalizer (C₀ : Set G) := le_normalizer_glbPrimeCore 3 M
  have hcontains : ∀ x ∈ M, x ∈ Subgroup.centralizer (R : Set G) → orderOf x = 3 → x ∈ R := by
    intro x _ hxC hx3
    obtain ⟨Q, hQ⟩ := hB0
    have hxz : x ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz.1) hxC
    have h := sylow_contains_centralizing_order_prime Q x hxz (by rw [hQ]; exact hxC) hx3
    rwa [hQ] at h
  have hOC₀ : GLBPrimeCore 3 (H ⊓ M) ≤ C₀ :=
    signalizer_le_glbPrimeCore_of_contains hp (by decide) hcon hd.cfg.ext.isPGroup
      hd.cfg.ext.le_M hcontains ((glbPrimeCore_le 3 (H ⊓ M)).trans inf_le_right)
      (glbPrimeCore_coprime 3 (H ⊓ M))
      (hd.cfg.ext.le_inf.trans (le_normalizer_glbPrimeCore 3 (H ⊓ M)))
  have hVC₀ : V ≤ C₀ := hsyl.1.trans hOC₀
  have hNX : C₀ ⊓ Subgroup.normalizer (V : Set G) ≤ GLBPrimeCore 3 (H ⊓ M) := by
    have hle : C₀ ⊓ (H ⊓ M) ≤ GLBPrimeCore 3 (H ⊓ M) := by
      refine le_glbPrimeCore inf_le_right ?_ ?_
      · intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := Subgroup.mem_normalizer_iff.mp (hMC hx.2) y
        have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y
        simp only [Subgroup.mem_inf]
        exact and_congr h1 h2
      · exact (glbPrimeCore_coprime 3 M).coprime_dvd_right
          (Subgroup.card_dvd_of_le inf_le_left)
    intro x hx
    exact hle ⟨hx.1, hNV ⟨hC₀M hx.1, hx.2⟩, hC₀M hx.1⟩
  have hsyl' : IsSylowTwoOf V C₀ := L34Squeeze.isSylowTwoOf_of_normalizer_le hVC₀ hV2 hNX hsyl
  have hTC := hd.d1LiftX_le_of_squeeze hOrb hz hB0 hdec hexpR rfl hA6 hcard hC₀M hMC hsyl' hNV
  have hT3 : IsPGroup 3 (d1LiftX 3 H R K) := hd.cfg.ext.isPGroup.to_le (d1LiftX_le 3 H R K)
  have hTbot : d1LiftX 3 H R K = ⊥ := by
    rcases hT3.card_eq_or_dvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (h3.trans (Subgroup.card_dvd_of_le hTC))
        (Nat.Prime.coprime_iff_not_dvd hp |>.mp (glbPrimeCore_coprime 3 M))
  have hmap := hd.cfg.map_d1LiftX_eq_inf (K := K)
  rw [hTbot, Subgroup.bot_subgroupOf, Subgroup.map_bot] at hmap
  rw [← hmap, Subgroup.card_bot] at hcard
  norm_num at hcard

@[expose] def D1SmallGEVNormalL34Ph7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K → D1SmallU2Fails p M H K →
    GLBPrimeCore p (H ⊓ M) ≠ GLBPrimeCore p H → pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    Subgroup.centralizer ({z} : Set G) ≤ H →
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ GLBPrimeCore p H →
    (∀ hzH : z ∈ H,
      (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal) →
    (∀ H₁ : Subgroup G, GLBIsMaxTwoLocal H₁ → H ⊓ M ≤ H₁ → H₁ = H ∨ H₁ = M) →
    (∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)) →
    (∃ Y : Subgroup G, Y ≤ pCoreOf 2 (H ⊓ M) ∧ Y ≠ ⊥ ∧
      (Y.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧
      ¬ M ⊓ Subgroup.normalizer (Y : Set G) ≤ H) →
    (∀ A : Subgroup G, A ≤ centerOf (pCoreOf 2 H) → A ≠ ⊥ →
      H ≤ Subgroup.normalizer (A : Set G) →
      M ≤ Subgroup.normalizer
        ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G) →
      ¬ IsSylowTwoOf (pCoreOf 2 (H ⊓ M)) (M ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) ∧
        z ∉ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) →
    (HasPrimeConstraint (G := M) p → ∀ V : Subgroup G, IsSylowTwoOf V (GLBPrimeCore p (H ⊓ M)) →
      ¬ M ⊓ Subgroup.normalizer (V : Set G) ≤ H) →
    False

@[expose] def D1SmallGEVIbNormalAllRest11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    ¬ D1SmallOuterR p H Rbar K →
    ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    GLBIsMaxTwoLocal H →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    D1GEVStarSmall p P M R z K →
    (∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
      ∀ hzHs : z ∈ Hs, ¬ (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal) →
    p = 3 → IsLinThreeFour K → D1SmallU2Fails p M H K →
    GLBPrimeCore p (H ⊓ M) ≠ GLBPrimeCore p H → pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H →
    (∀ H₁ : Subgroup G, GLBIsMaxTwoLocal H₁ → H ⊓ M ≤ H₁ → H₁ = H ∨ H₁ = M) →
    (∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)) →
    (∃ Y : Subgroup G, Y ≤ pCoreOf 2 (H ⊓ M) ∧ Y ≠ ⊥ ∧
      (Y.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧
      ¬ M ⊓ Subgroup.normalizer (Y : Set G) ≤ H) →
    (∀ A : Subgroup G, A ≤ centerOf (pCoreOf 2 H) → A ≠ ⊥ →
      H ≤ Subgroup.normalizer (A : Set G) →
      M ≤ Subgroup.normalizer
        ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G) →
      ¬ IsSylowTwoOf (pCoreOf 2 (H ⊓ M)) (M ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) ∧
        z ∉ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) →
    (HasPrimeConstraint (G := M) p → ∀ V : Subgroup G, IsSylowTwoOf V (GLBPrimeCore p (H ⊓ M)) →
      ¬ M ⊓ Subgroup.normalizer (V : Set G) ≤ H) →
    False

theorem d1SmallGEVNormalL34Ph6_of_ph7 (hUE : KFactUPrimeExc) (hOrb : KFactSmallOrbits)
    (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hPh7 : D1SmallGEVNormalL34Ph7) : D1SmallGEVNormalL34Ph6 := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV hCz
    hcore hA hM hX hY hA6
  refine hPh7 G p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV
    hCz hcore hA hM hX hY hA6 fun hcon V hsyl hNV => ?_
  subst hp3
  exact hd.false_of_hasPrimeConstraint_of_isSylowTwoOf hUE hOrb hExp hOut hSh3 hO hz hB0 rfl hL
    hOR hcon hsyl hNV

theorem d1SmallGEVIbNormalAllRest10_of_rest11 (hUE : KFactUPrimeExc) (hOrb : KFactSmallOrbits)
    (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (h11 : D1SmallGEVIbNormalAllRest11) :
    D1SmallGEVIbNormalAllRest10 := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hp3 hL hU2 hcore hS hA hX hY hA6
  refine h11 G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hp3 hL hU2 hcore hS hA hX hY hA6 fun hcon V hsyl hNV => ?_
  subst hp3
  exact hd.false_of_hasPrimeConstraint_of_isSylowTwoOf hUE hOrb hExp hOut hSh3 hO hz hB0 rfl hL
    hOR hcon hsyl hNV

end CFSG.AGLEmbedding
