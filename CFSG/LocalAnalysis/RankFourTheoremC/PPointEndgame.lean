module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointEndgameAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9B
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9CoverAux
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gen49_mem_of_pow_eq_one {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    {S R Γ : Subgroup Y} {x : Y} (h : Gen49BHyp p S R Γ x) {s : Y} (hs : s ∈ S)
    (hsp : s ^ p = 1) : s ∈ R := by
  by_contra hsR
  have hprime : p.Prime := Fact.out
  have := h.abelian
  have hcomm : ∀ q ∈ R, q * s = s * q := fun q hq =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := S)).comm ⟨q, h.le_sylow hq⟩ ⟨s, hs⟩)
  have hcard : Nat.card (R ⊔ zpowers s : Subgroup Y) = p ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime R hsp hsR hcomm, h.card_eq]
    ring
  have hE : IsElemAbelian p (R ⊔ zpowers s : Subgroup Y) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p h.elemAbelian
      (isElemAbelian_zpowers hsp) (le_centralizer_iff.mpr (zpowers_le.mpr
        (mem_centralizer_iff.mpr fun q hq => hcomm q hq)))
  have h3 := le_pRank_of_elemAbelian_card (P := (⊤ : Subgroup Y)) le_top hE hcard
  have := h.pRank_le
  omega

theorem mem_glbPrimeCore_of_mk_eq_one {H : Subgroup G} {r : G} (hr : r ∈ H)
    (h : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨r, hr⟩ = 1) :
    r ∈ GLBPrimeCore 3 H := by
  have h1 : (⟨r, hr⟩ : H) ∈ primeComplementCore (G := H) 3 := (QuotientGroup.eq_one_iff _).mp h
  rw [← glbPrimeCore_subgroupOf] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem endgame_hyp (hS : D1Global G) (hFC : FullCoreLocality G) {P : Sylow 3 G}
    {M : Subgroup G} (hloc : D1Local 3 P M) (hPab : IsMulCommutative (P : Subgroup G))
    {x : G} {U H F : Subgroup G} (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (hx1 : x ≠ 1)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hHtop : H ≠ ⊤) (hUH : U ≤ H) (hrk : Open.pRank 3 H ≤ 2) (hFH : IsSylowOf 3 F H)
    (hUF : U ≤ F) (hFM : F ≤ M) :
    Gen49BHyp 3 ((F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      ((U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hUH hxU⟩) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hxH : x ∈ H := hUH hxU
  set O : Subgroup H := primeComplementCore (G := H) 3 with hO
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hUp : IsPGroup 3 U := elementary_isPGroup 3 U hU
  have hx3 : x ^ 3 = 1 := hU.2 x hxU
  have hxo : orderOf (⟨x, hxH⟩ : H) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hx3 hx1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxH⟩) = 3 :=
    orderOf_mk_of_coprime hp O (primeComplementCore_coprime 3) hxo
  have hab : ∀ S : Sylow 3 (H ⧸ O), IsMulCommutative (S : Subgroup (H ⧸ O)) :=
    isMulCommutative_sylow_quotient (N := H) fun _ hQ => isMulCommutative_of_isPGroup hPab hQ
  have hFab : IsMulCommutative F := isMulCommutative_of_isPGroup hPab hFH.isPGroup
  have hF2 : 2 ≤ Open.pRank 3 F := le_pRank_of_elemAbelian_card hUF hU hUc
  have hN₁ : normalizer (F : Set G) ≤ M :=
    normalizer_le_of_two_le_pRank hFC hloc hFH.isPGroup hFM hF2
  have hN₂ : normalizer (U : Set G) ≤ M :=
    normalizer_le_of_two_le_pRank hFC hloc hUp (hUP.trans hPM)
      (le_pRank_of_elemAbelian_card le_rfl hU hUc)
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 3 (H ⧸ O), (Q : Subgroup (H ⧸ O)) =
      (F.subgroupOf H).map (QuotientGroup.mk' O) := by
    obtain ⟨-, hp', hdvd⟩ := isSylowOf_iff.1 (isSylowOf_top_map_mk hFH)
    rw [Subgroup.relIndex_top_right] at hdvd
    exact ⟨hp'.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩
  have hxS : QuotientGroup.mk' O ⟨x, hxH⟩ ∈ (F.subgroupOf H).map (QuotientGroup.mk' O) :=
    ⟨⟨x, hxH⟩, hUF hxU, rfl⟩
  exact
    { ne_two := by norm_num
      core_eq_bot := primeComplementCore_quotient_eq_bot 3
      catalog := (catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
      sylow := isSylowOf_top_map_mk hFH
      abelian := by
        rw [← hQ]
        exact hab Q
      le_sylow := Subgroup.map_mono (Subgroup.subgroupOf_mono H hUF)
      elemAbelian := gen49q_isElemAbelian_map _ (isElemAbelian_subgroupOf hU H)
      card_eq := by
        rw [card_map_mk_of_isPGroup hp O (primeComplementCore_coprime 3)
          (show IsPGroup 3 (U.subgroupOf H) from hUp.comap_subtype),
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv]
        exact hUc
      pRank_le := gen49q_pRank_top_quotient_le hp hrk
      mem := ⟨⟨x, hxH⟩, hxU, rfl⟩
      ne_one := fun h => by
        rw [h, orderOf_one] at hxo'
        omega
      weakClosed := fun g hg => weaklyClosed_map_mk hxo hab
        (fun Q' hxQ' g' hg' => weakClosed_sylow hwc Q' hxQ' g' hg') Q (hQ ▸ hxS) g
        (by rw [hQ]; exact hg)
      normalizer_S := normalizer_map_mk_le hp
        (show IsPGroup 3 (F.subgroupOf H) from hFH.isPGroup.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hFH.le]; exact hN₁)
      normalizer_R := normalizer_map_mk_le hp
        (show IsPGroup 3 (U.subgroupOf H) from hUp.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hUH]; exact hN₂)
      others := by
        rintro _ ⟨r, hr, rfl⟩ hr1 hrx
        have hrU : (r : G) ∈ U := hr
        have hrP : (r : G) ∈ (P : Subgroup G) := hUP hrU
        have hr1' : (r : G) ≠ 1 := fun h => hr1 (by rw [show r = 1 from Subtype.ext h, map_one])
        have hrp : (r : G) ^ 3 = 1 := hU.2 _ hrU
        have hrx' : (r : G) ∉ zpowers x := by
          intro hmem
          obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
          have hrk' : r = (⟨x, hxH⟩ : H) ^ k := Subtype.ext (by rw [← hk]; rfl)
          have hmem' : QuotientGroup.mk' O r ∈ zpowers (QuotientGroup.mk' O ⟨x, hxH⟩) := by
            rw [hrk', map_zpow]
            exact zpow_mem (mem_zpowers _) k
          exact hrx (zpowers_eq_of_mem_zpowers_of_orderOf_eq_three hxo' hmem' hr1)
        have hCM : centralizer ({(r : G)} : Set G) ≤ M := hC _ hrU hrx'
        have hPC : (P : Subgroup G) ≤ centralizer ({(r : G)} : Set G) := fun g hg =>
          mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := (P : Subgroup G))).comm ⟨g, hg⟩ ⟨r, hrP⟩))
        have hNM : normalizer ((zpowers (r : G) : Subgroup G) : Set G) ≤ M :=
          normalizer_zpowers_le_of_centralizer_le hFC hloc hCM (by
            rw [inf_of_le_left hPC]
            have := four_le_pRank_sylow hloc.beta P
            omega)
        have hro : orderOf r = 3 := by
          rw [← Subgroup.orderOf_coe]
          exact orderOf_eq_prime hrp hr1'
        refine ⟨(centralizer_mk_le_map hp hro).trans (Subgroup.map_mono fun c hc => ?_), ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr ⟨c.2, hCM (mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)))⟩
        · rw [← MonoidHom.map_zpowers]
          refine normalizer_map_mk_le hp (D := zpowers r)
            (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hro, pow_one])) ?_
          rw [MonoidHom.map_zpowers]
          exact hNM }

theorem endgame_exists_centralizer_ne_bot (hS : D1Global G) (hD1 : D1For G)
    (hFC : FullCoreLocality G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    {P : Sylow 3 G} {M : Subgroup G} (hloc : D1Local 3 P M)
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
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set H : Subgroup G := normalizer (S : Set G) with hH
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
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
  obtain ⟨F, hFH, hUF, hFM⟩ := exists_sylow_through hFC hloc hUp hU2 hUM hUS
  have hrkF : Open.pRank 3 F ≤ 2 := by
    by_contra hlt
    have h3 : 3 ≤ Open.pRank 3 F := by omega
    exact hesc (hD1 3 hloc.beta P M hloc.maxLocal hloc.core H hH2
      (h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp (le_inf hFH.le hFM))))
  have hrk : Open.pRank 3 H ≤ 2 := (pRank_eq_of_isSylowOf hp hFH) ▸ hrkF
  have hyp := endgame_hyp hS hFC hloc hPab hU hUc hUP hxU hx1 hwc hC hHtop hUS hrk hFH hUF hFM
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
    orderOf_mk_of_coprime hp O (primeComplementCore_coprime 3)
      (by rw [Subgroup.orderOf_mk]; exact hxo)
  have hRb : ∀ r ∈ R₀, ∃ hr : r ∈ H, π ⟨r, hr⟩ ∈ Ob := fun r hr =>
    ⟨hR₀S hr, ⟨r, hR₀S hr⟩, Subgroup.mem_subgroupOf.mpr ⟨hR₀O hr, hR₀S hr⟩, rfl⟩
  rcases gl83Generic4_9B_holds hInn hWC hyp with hΓtop | ⟨K, hKn, hKC, hKΓ⟩
  ·
    exfalso
    have hObbot : Ob = ⊥ := eq_bot_of_normalized_coprime hcore hObcop
      (fun g o ho => hObΓ g (by rw [hΓtop]; exact mem_top g) o ho)
    apply hR₀n
    intro r hr
    obtain ⟨hrH, hrb⟩ := hRb r hr
    rw [hObbot, Subgroup.mem_bot] at hrb
    exact mem_glbPrimeCore_of_mk_eq_one hrH hrb
  ·
    intro hbot
    have hcentr := centralizes_of_normal_centralizer hcore hxo' hObcop hObΓ hxΓ hKn hKC hKΓ
      (isSylowOf_top_map_mk hFH) (fun s hs hs3 => gen49_mem_of_pow_eq_one hyp hs hs3)
      (fun a ha ha1 hax => (hyp.others a ha ha1 hax).1)
    have hcomm : ∀ r ∈ R₀, r * x * r⁻¹ * x⁻¹ ∈ GLBPrimeCore 3 H := by
      intro r hr
      obtain ⟨hrH, hrb⟩ := hRb r hr
      have h1 := hcentr _ hrb
      have hmem : r * x * r⁻¹ * x⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (H.mul_mem hrH hxH) (H.inv_mem hrH)) (H.inv_mem hxH)
      refine mem_glbPrimeCore_of_mk_eq_one hmem ?_
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

end CFSG.LocalAnalysis.RankFourTheoremC
