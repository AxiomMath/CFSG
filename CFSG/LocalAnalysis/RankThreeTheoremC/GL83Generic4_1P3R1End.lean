module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1End2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
import CFSG.LocalAnalysis.RankFourTheoremC.PPointMaxPair
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9B
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
  CFSG.LocalAnalysis.RankFourTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem endgame3_exists_centralizer_ne_bot (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    (hPab : IsMulCommutative (P : Subgroup G)) {x : G} {U : Subgroup G}
    (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2) (hUP : U ≤ (P : Subgroup G))
    (hxU : x ∈ U) (hx1 : x ≠ 1)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    {S R₀ : Subgroup G} (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hUS : U ≤ normalizer (S : Set G)) (hesc : ¬ normalizer (S : Set G) ≤ M)
    (hR₀O : R₀ ≤ GLBPrimeCore 3 M) (hR₀S : R₀ ≤ normalizer (S : Set G))
    (hUR₀ : U ≤ normalizer (R₀ : Set G))
    (hR₀n : ¬ R₀ ≤ GLBPrimeCore 3 (normalizer (S : Set G))) :
    R₀ ⊓ centralizer ({x} : Set G) ≠ ⊥ := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  set H : Subgroup G := normalizer (S : Set G) with hH
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hUM : U ≤ M := hUP.trans hPM
  have hUp : IsPGroup 3 U := elementary_isPGroup 3 U hU
  have hU2 : 2 ≤ Open.pRank 3 U := le_pRank_of_elemAbelian_card le_rfl hU hUc
  have hx3 : x ^ 3 = 1 := hU.2 x hxU
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxH : x ∈ H := hUS hxU
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hnormal : S.Normal := normalizer_eq_top_iff.mp htop
    have := hS.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
    · exact hSne h
    · obtain ⟨k, hk⟩ := hS2 ⟨x, h ▸ mem_top x⟩
      have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have := orderOf_dvd_of_pow_eq_one hxk
      rw [hxo] at this
      have h3 : 3 ∣ 2 ^ k := this
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      omega
  have hH2 : IsTwoLocal H := ⟨S, hSne, hS2, rfl⟩
  obtain ⟨F, hFH, hUF, hFM⟩ := exists_sylow_through3 hS hU0 hp hM hUp hU2 hUM hUS
  have hrkF : Open.pRank 3 F ≤ 2 := by
    by_contra hlt
    have h3 : 3 ≤ Open.pRank 3 F := by omega
    exact hesc (le_of_three_le_pRank_inf hD1 hp hM hH2
      (h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp3 (le_inf hFH.le hFM))))
  have hrk : Open.pRank 3 H ≤ 2 := (pRank_eq_of_isSylowOf3 hp3 hFH) ▸ hrkF
  have hyp := endgame3_hyp hS hU0 hp hM hPab hU hUc hUP hxU hx1 hwc hC hHtop hUS hrk hFH hUF hFM
  set O : Subgroup H := primeComplementCore (G := H) 3 with hO
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  set Ob : Subgroup (H ⧸ O) := ((GLBPrimeCore 3 M ⊓ H).subgroupOf H).map π with hOb
  set Γ : Subgroup (H ⧸ O) := ((H ⊓ M).subgroupOf H).map π with hΓ
  have hcore := primeComplementCore_quotient_eq_bot (G := H) 3
  have hObcop : Nat.Coprime 3 (Nat.card Ob) := by
    have h1 : Nat.card Ob ∣ Nat.card ((GLBPrimeCore 3 M ⊓ H).subgroupOf H) :=
      Subgroup.card_map_dvd _ π
    have h2 : Nat.card ((GLBPrimeCore 3 M ⊓ H).subgroupOf H) ∣ Nat.card (GLBPrimeCore 3 M) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        GLBPrimeCore 3 M ⊓ H ≤ H)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (glbPrimeCore_coprime 3 M).coprime_dvd_right (h1.trans h2)
  have hObΓ : ∀ g ∈ Γ, ∀ o ∈ Ob, g * o * g⁻¹ ∈ Ob := by
    rintro _ ⟨g₀, hg₀, rfl⟩ _ ⟨o₀, ho₀, rfl⟩
    have hg₀' : (g₀ : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hg₀
    have ho₀' : (o₀ : G) ∈ GLBPrimeCore 3 M ⊓ H := Subgroup.mem_subgroupOf.mp ho₀
    refine ⟨g₀ * o₀ * g₀⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, (g₀ * o₀ * g₀⁻¹).2⟩, ?_⟩
    · exact (mem_normalizer_iff.mp (le_normalizer_glbPrimeCore 3 M hg₀'.2) _).mp ho₀'.1
    · simp [map_mul, map_inv]
  have hxM : x ∈ M := hUM hxU
  have hxΓ : π ⟨x, hxH⟩ ∈ Γ := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr ⟨hxH, hxM⟩, rfl⟩
  have hxo' : orderOf (π ⟨x, hxH⟩) = 3 :=
    orderOf_mk_of_coprime hp3 O (primeComplementCore_coprime 3)
      (by rw [Subgroup.orderOf_mk]; exact hxo)
  have hRb : ∀ r ∈ R₀, ∃ hr : r ∈ H, π ⟨r, hr⟩ ∈ Ob := fun r hr =>
    ⟨hR₀S hr, ⟨r, hR₀S hr⟩, Subgroup.mem_subgroupOf.mpr ⟨hR₀O hr, hR₀S hr⟩, rfl⟩
  rcases gl83Generic4_9B_holds hInn hWC hyp with hΓtop | ⟨K, hKn, hKC, hKΓ⟩
  ·
    exfalso
    have hObbot : Ob = ⊥ := eq_bot_of_normalized_coprime3 hcore hObcop
      (fun g o ho => hObΓ g (by rw [hΓtop]; exact mem_top g) o ho)
    apply hR₀n
    intro r hr
    obtain ⟨hrH, hrb⟩ := hRb r hr
    rw [hObbot, Subgroup.mem_bot] at hrb
    exact mem_glbPrimeCore_of_mk_eq_one_three hrH hrb
  ·
    intro hbot
    have hcentr := centralizes_of_normal_centralizer3 hcore hxo' hObcop hObΓ hxΓ hKn hKC hKΓ
      (isSylowOf_top_map_mk hFH) (fun s hs hs3 => gen49_mem_of_pow_eq_one_three hyp hs hs3)
      (fun a ha ha1 hax => (hyp.others a ha ha1 hax).1)
    have hcomm : ∀ r ∈ R₀, r * x * r⁻¹ * x⁻¹ ∈ GLBPrimeCore 3 H := by
      intro r hr
      obtain ⟨hrH, hrb⟩ := hRb r hr
      have h1 := hcentr _ hrb
      have hmem : r * x * r⁻¹ * x⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (H.mul_mem hrH hxH) (H.inv_mem hrH)) (H.inv_mem hxH)
      refine mem_glbPrimeCore_of_mk_eq_one_three hmem ?_
      change π (⟨r, hrH⟩ * ⟨x, hxH⟩ * ⟨r, hrH⟩⁻¹ * ⟨x, hxH⟩⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, mul_inv_cancel_right, mul_inv_cancel]
    have hmaps : ∀ r ∈ R₀, r * x * r⁻¹ * x⁻¹ ∈ R₀ := by
      intro r hr
      have := R₀.mul_mem hr ((mem_normalizer_iff.mp (hUR₀ hxU) r⁻¹).mp (R₀.inv_mem hr))
      simpa [mul_assoc] using this
    let φ : R₀ → R₀ := fun r => ⟨r * x * r⁻¹ * x⁻¹, hmaps r r.2⟩
    have hφinj : Function.Injective φ := by
      intro r s hrs
      have h1 : (r : G) * x * (r : G)⁻¹ * x⁻¹ = (s : G) * x * (s : G)⁻¹ * x⁻¹ :=
        congrArg Subtype.val hrs
      have h2 : (r : G) * x * (r : G)⁻¹ = (s : G) * x * (s : G)⁻¹ := mul_right_cancel h1
      have h3 : ((s : G)⁻¹ * r) * x = x * ((s : G)⁻¹ * r) := by
        calc ((s : G)⁻¹ * r) * x = (s : G)⁻¹ * ((r : G) * x * (r : G)⁻¹) * r := by group
          _ = (s : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) * r := by rw [h2]
          _ = x * ((s : G)⁻¹ * r) := by group
      have h4 : (s : G)⁻¹ * r ∈ R₀ ⊓ centralizer ({x} : Set G) :=
        ⟨R₀.mul_mem (R₀.inv_mem s.2) r.2, mem_centralizer_singleton_iff.mpr h3⟩
      rw [hbot, Subgroup.mem_bot] at h4
      exact Subtype.ext (inv_mul_eq_one.mp h4).symm
    have hφsurj : Function.Surjective φ := Finite.surjective_of_injective hφinj
    apply hR₀n
    intro t ht
    obtain ⟨r, hr⟩ := hφsurj ⟨t, ht⟩
    have : t = (r : G) * x * (r : G)⁻¹ * x⁻¹ := (congrArg Subtype.val hr).symm
    rw [this]
    exact hcomm r r.2

theorem false_three_of_plane (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (_hxP : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hPab : IsMulCommutative (P : Subgroup G))
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    {U : Subgroup G} (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U)
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hL43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) → normalizer (Y : Set G) ≤ M)
    (hL45 : ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M)
    (hL44 : ¬ 2 ∣ Nat.card ↥(GLBPrimeCore 3 M ⊓ centralizer ({x} : Set G))) : False := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  set O : Subgroup G := GLBPrimeCore 3 M with hO
  have hOM : M ≤ normalizer (O : Set G) := le_normalizer_glbPrimeCore 3 M
  have hOle : O ≤ M := glbPrimeCore_le 3 M
  have hOcop : Nat.Coprime 3 (Nat.card O) := glbPrimeCore_coprime 3 M
  have hUp : IsPGroup 3 U := elementary_isPGroup 3 U hU
  have hUM : U ≤ M := hUP.trans hPM
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hCU : centralizer (U : Set G) ≤ M := by
    obtain ⟨u, huU, hux⟩ : ∃ u ∈ U, u ∉ zpowers x := by
      by_contra hno
      push Not at hno
      have hle : U ≤ zpowers x := fun u hu => hno u hu
      have := Subgroup.card_le_of_le hle
      rw [hUc, Nat.card_zpowers, hxo] at this
      omega
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU)).trans (hC u huU hux)
  obtain ⟨S₁, T, hS₁, hS₁M, hT, hTM, hTloc, hint, hne, hmax⟩ := exists_maximal_escaping_pair
    hS.charTwo hp3 (by norm_num) hU hUc hUM hxU hOle hOM hOcop hC hL43 hL45
  have hSO := isSylowOf_two_glbPrimeCore_of_maximal hp3 (by norm_num) hUp hCU hS₁ hS₁M hT hTM
    hint hmax
  obtain ⟨R₀, hR₀N, hR₀T, hR₀2, hR₀S, hUR₀, hR₀notS, hR₀notO⟩ := exists_R₀_of_maximal hp3
    (by norm_num) hUp hUM hOle hOM hOcop hL43 hS₁ hS₁M hTloc hint hSO
  have hS2 : IsPGroup 2 (S₁ ⊓ T : Subgroup G) := hS₁.1.to_inf_left
  have hUS : U ≤ normalizer ((S₁ ⊓ T : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U S₁ T hS₁.2.1 hT.2.1
  have hesc : ¬ normalizer ((S₁ ⊓ T : Subgroup G) : Set G) ≤ M :=
    relative_pair_intersection_normalizer_escapes M S₁ T hS₁.1 hS₁M hTM hint
  have hend := endgame3_exists_centralizer_ne_bot hS hU0 hD1 hInn hWC hp hM hPab hU hUc hUP
    hxU hx1 hwc hC hS2 hne hUS hesc hR₀N hR₀S hUR₀ hR₀notO
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hend
  have hcO : (c : G) ∈ O ⊓ centralizer ({x} : Set G) := ⟨hR₀N c.2.1, c.2.2⟩
  obtain ⟨k, hk⟩ := hR₀2 ⟨(c : G), c.2.1⟩
  have hck : (c : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf (c : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hc1
    exact Subtype.ext (orderOf_eq_one_iff.mp (by simpa using hci))
  have h2 : 2 ∣ orderOf (c : G) := hci ▸ dvd_pow_self 2 hi0
  have h3 : orderOf (c : G) ∣ Nat.card (O ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have := orderOf_dvd_natCard (⟨(c : G), hcO⟩ : (O ⊓ centralizer ({x} : Set G) : Subgroup G))
    rwa [Subgroup.orderOf_mk] at this
  exact hL44 (h2.trans h3)

end CFSG.LocalAnalysis.RankThreeTheoremC
