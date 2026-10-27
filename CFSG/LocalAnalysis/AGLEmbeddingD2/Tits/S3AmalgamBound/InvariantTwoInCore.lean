module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34CentralTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.TwoLocalN1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proved

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC

theorem le_centralizer_of_invariant_two
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {X : Type} [Group X] [Finite X] {K Ab Y : Subgroup X} (hKn : K.Normal)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hAK : Ab ≤ K) (hA9 : Nat.card Ab = 9)
    (hY2 : IsPGroup 2 Y) (hYN : Y ≤ Subgroup.normalizer (Ab : Set X))
    (hAY : Ab ≤ Subgroup.normalizer (Y : Set X)) : Y ≤ Subgroup.centralizer (Ab : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : IsLinThreeFour ↥K := isLinThreeFour_of_l34Index hd he
  have hK20 : Nat.card K = 20160 := (kFactSmallThreeOrders ↥K).2.1 hL
  have hrank : IsRankThreeL34 ↥K := by
    obtain ⟨q, hq2, hqe, hd'⟩ := hd
    obtain ⟨⟨d0, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
    simp only at hd'
    subst hd'
    exact ⟨q, hq2, hqe, hv, he⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup ↥K, P = Ab.subgroupOf K := ⟨_, rfl⟩
  have hPc : Nat.card P = 9 := by
    rw [hPdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA9]
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hPc]; norm_num)
  have hPidx : ¬ 3 ∣ P.index := by
    have h := P.index_mul_card
    rw [hPc, hK20] at h
    have : P.index = 2240 := by omega
    rw [this]
    norm_num
  have hPS : ((hPp.toSylow hPidx : Sylow 3 ↥K) : Subgroup ↥K) = P := IsPGroup.toSylow_coe _ _
  obtain ⟨-, -, -, hloc⟩ := kFactL34Three ↥K hrank (hPp.toSylow hPidx)
  rw [hPS] at hloc
  obtain ⟨u, huP, hu1⟩ : ∃ u ∈ P, u ≠ 1 := by
    by_contra h
    push Not at h
    have : P = ⊥ := eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx)
    rw [this, Subgroup.card_bot] at hPc
    omega
  have hYK : Y ⊓ K ≤ K := inf_le_right
  have hV2 : IsPGroup 2 ((Y ⊓ K).subgroupOf K) :=
    (hY2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe hYK).symm
  have hNP : Subgroup.normalizer (P : Set ↥K) = (Subgroup.normalizer (Ab : Set X)).subgroupOf K := by
    rw [hPdef, Subgroup.subgroupOf_normalizer_eq hAK]
  have hNV : Subgroup.normalizer (((Y ⊓ K).subgroupOf K : Subgroup ↥K) : Set ↥K) =
      (Subgroup.normalizer ((Y ⊓ K : Subgroup X) : Set X)).subgroupOf K := by
    rw [Subgroup.subgroupOf_normalizer_eq hYK]
  have hKN : ∀ x : X, x ∈ Subgroup.normalizer (K : Set X) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hKn.conj_mem k hk x, fun hk => by
        have h := hKn.conj_mem _ hk x⁻¹
        have e : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k := by group
        rwa [e] at h⟩
  have hV : (Y ⊓ K).subgroupOf K = ⊥ := by
    refine hloc u huP hu1 _ hV2 ?_ ?_
    · rw [hNP]
      intro v hv
      rw [Subgroup.mem_subgroupOf] at hv ⊢
      exact hYN hv.1
    · rw [hNV, Subgroup.mem_subgroupOf]
      have huA : (u : X) ∈ Ab := by
        have := huP
        rw [hPdef, Subgroup.mem_subgroupOf] at this
        exact this
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hAY huA, hKN _⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hc : y * (a * y⁻¹ * a⁻¹) ∈ Y ⊓ K := by
    refine ⟨Y.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hAY ha) y⁻¹).mp (Y.inv_mem hy)), ?_⟩
    have h1 : y * a * y⁻¹ ∈ K := hKn.conj_mem a (hAK ha) y
    have e : y * (a * y⁻¹ * a⁻¹) = (y * a * y⁻¹) * a⁻¹ := by group
    rw [e]
    exact K.mul_mem h1 (K.inv_mem (hAK ha))
  have h1 : y * (a * y⁻¹ * a⁻¹) = 1 := by
    have hmem : (⟨y * (a * y⁻¹ * a⁻¹), hc.2⟩ : ↥K) ∈ (Y ⊓ K).subgroupOf K :=
      Subgroup.mem_subgroupOf.2 hc
    rw [hV, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have : a * y = y * a := by
    have h2 : y * a * y⁻¹ * a⁻¹ = 1 := by rw [← h1]; group
    have h3 : y * a * y⁻¹ = a := mul_inv_eq_one.1 h2
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  exact this

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.le_glbPrimeCore_of_invariant_two
    (hK : KFactL34CentralTwo)
    {d : TauCeti.ValidLieTypeIndex} {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {X : Subgroup G} (hXHM : X ≤ H ⊓ M)
    (hX2 : IsPGroup 2 X) (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    X ≤ GLBPrimeCore 3 (H ⊓ M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := primeComplementCore (G := H) 3 with hW
  set π := QuotientGroup.mk' W with hπ
  set Xb : Subgroup (H ⧸ W) := (X.subgroupOf H).map π with hXb
  set Ab : Subgroup (H ⧸ W) := (A.subgroupOf H).map π with hAb
  have hKn : K.Normal := hc.almostSimple.normal
  have hX₀N : ((H ⊓ M).subgroupOf H).map π = Subgroup.normalizer (Ab : Set (H ⧸ W)) :=
    hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hAb9 : Nat.card Ab = 9 := by
    have := hc.almostSimple.card_A
    rw [this]
    norm_num
  have hXH : X ≤ H := hXHM.trans inf_le_left
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hXbN : Xb ≤ Subgroup.normalizer (Ab : Set (H ⧸ W)) := by
    rw [← hX₀N]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2
      (hXHM (Subgroup.mem_subgroupOf.1 hx)))
  have hXb2 : IsPGroup 2 Xb :=
    (hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm).map π
  have hkey : ∀ u ∈ Ab, ∀ z ∈ Xb, u * z * u⁻¹ ∈ Xb := by
    intro u hu z hz
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hz
    refine Subgroup.mem_map.2 ⟨a' * x' * a'⁻¹, ?_, by simp [map_mul]⟩
    rw [Subgroup.mem_subgroupOf] at ha' hx' ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hAX ha') (x' : G)).mp hx'
    simpa using this
  have hAbN : Ab ≤ Subgroup.normalizer (Xb : Set (H ⧸ W)) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hkey u hu z hz, fun hz => ?_⟩
    have := hkey u⁻¹ (Ab.inv_mem hu) _ hz
    simpa [mul_assoc] using this
  have hXbC : Xb ≤ Subgroup.centralizer (Ab : Set (H ⧸ W)) :=
    le_centralizer_of_invariant_two hc.l34 hKn hc.iso hc.le_K hAb9 hXb2 hXbN hAbN
  have hcent : ∀ t ∈ Xb, ∀ y ∈ Subgroup.normalizer (Ab : Set (H ⧸ W)), y * t = t * y := by
    intro t ht y hy
    obtain ⟨k, hk⟩ := hXb2 ⟨t, ht⟩
    exact hK d hc.l34 (H ⧸ W) K hKn hc.almostSimple.centralizer_eq_bot hc.iso Ab hc.le_K hAb9 t
      (hXbC ht) ⟨k, congrArg Subtype.val hk⟩ y hy
  set Y' : Subgroup ↥H := Xb.comap π with hY'
  set N : Subgroup G := Y'.map H.subtype with hN
  have hW₀e : W.map H.subtype = GLBPrimeCore 3 H := by
    rw [glbPrimeCore_eq_primeComplementCoreOf]
    rfl
  have hW₀HM : W.map H.subtype ≤ H ⊓ M :=
    hW₀e ▸ le_inf (glbPrimeCore_le 3 H) hc.esc.primeCore_le
  have hWHM : ∀ w ∈ W, (w : G) ∈ H ⊓ M := fun w hw => hW₀HM ⟨w, hw, rfl⟩
  have hNle : N ≤ H ⊓ M := by
    rintro g ⟨h, hh, rfl⟩
    refine ⟨h.2, ?_⟩
    have h1 : π h ∈ ((H ⊓ M).subgroupOf H).map π := hX₀N ▸ hXbN hh
    obtain ⟨h', hh', hhe⟩ := Subgroup.mem_map.1 h1
    have hw : h * h'⁻¹ ∈ W := by
      rw [← QuotientGroup.ker_mk' W, MonoidHom.mem_ker, map_mul, map_inv, ← hπ, hhe, mul_inv_cancel]
    have hwM : (h * h'⁻¹ : ↥H) ∈ (H ⊓ M).subgroupOf H := Subgroup.mem_subgroupOf.2 (hWHM _ hw)
    have : h ∈ (H ⊓ M).subgroupOf H := by
      have := ((H ⊓ M).subgroupOf H).mul_mem hwM hh'
      simpa using this
    exact (Subgroup.mem_subgroupOf.1 this).2
  have hNnorm : H ⊓ M ≤ Subgroup.normalizer (N : Set G) := by
    have key : ∀ m ∈ H ⊓ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
      rintro m hm _ ⟨h, hh, rfl⟩
      have hmH : m ∈ H := (Subgroup.mem_inf.1 hm).1
      have hh' : π h ∈ Xb := hh
      refine ⟨(⟨m, hmH⟩ : ↥H) * h * (⟨m, hmH⟩ : ↥H)⁻¹, ?_, by simp⟩
      show π ((⟨m, hmH⟩ : ↥H) * h * (⟨m, hmH⟩ : ↥H)⁻¹) ∈ Xb
      rw [map_mul, map_mul, map_inv]
      have hm' : π ⟨m, hmH⟩ ∈ Subgroup.normalizer (Ab : Set (H ⧸ W)) :=
        hX₀N ▸ Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hm)
      have := hcent _ hh' _ hm'
      have e : π ⟨m, hmH⟩ * π h * (π ⟨m, hmH⟩)⁻¹ = π h := by
        rw [this]; group
      rw [e]
      exact hh'

    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => key m hm n hn, fun hn => ?_⟩
    have := key m⁻¹ ((H ⊓ M).inv_mem hm) _ hn
    simpa [mul_assoc] using this
  have hcard : Nat.card N = Nat.card Xb * Nat.card W := by
    rw [hN, Subgroup.card_map_of_injective H.subtype_injective]
    have h1 := card_eq_card_map_mul_card_inf_ker π Y'
    have h2 : Y'.map π = Xb := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective W) Xb
    have h3 : Y' ⊓ π.ker = π.ker := inf_eq_right.2 (fun w hw => by
      rw [hY', Subgroup.mem_comap, MonoidHom.mem_ker.1 hw]
      exact Xb.one_mem)
    rw [h1, h2, h3, hπ, QuotientGroup.ker_mk']
  obtain ⟨n2, hn2⟩ := hXb2.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card N) := by
    rw [hcard, hn2]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right n2 (by norm_num))
      (primeComplementCore_coprime 3)
  have hNnormal : (N.subgroupOf (H ⊓ M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).2 hNnorm
  have hXN : X ≤ N := by
    intro x hx
    refine ⟨⟨x, hXH hx⟩, ?_, rfl⟩
    show π ⟨x, hXH hx⟩ ∈ Xb
    exact Subgroup.mem_map.2 ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  exact hXN.trans (le_sSup ⟨hNle, hNnormal, hcop⟩)

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape in
theorem d2L34BetaInvariantTwoInCore_of_kfact
    (hK : KFactL34CentralTwo) : D2L34BetaInvariantTwoInCore := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax X hXHM hX2 hAX
  exact hc.toConf3.le_glbPrimeCore_of_invariant_two hK hXHM hX2 hAX

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape in
theorem d2L34BetaInvariantTwoInCore :
    D2L34BetaInvariantTwoInCore :=
  d2L34BetaInvariantTwoInCore_of_kfact kFactL34CentralTwo

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
