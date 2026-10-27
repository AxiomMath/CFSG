module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_20b

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Parts

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem lin2_normalizer_R (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D) {m : G} (hm : m ∈ M)
    (hmL : m ∈ Subgroup.normalizer (L : Set G)) :
    m ∈ Subgroup.normalizer (thompsonJ S : Set G) := by
  obtain ⟨-, -, ⟨-, hRsyl, -⟩, -, ⟨B, hB⟩, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨hDB, -, -, -, -, hBR, -⟩ := hB
  have hDR : D ≤ Subgroup.normalizer (thompsonJ S : Set G) := fun d hd => hBR (hDB hd)
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hR2 : IsPGroup 2 (thompsonJ S) := hcfg.sylowT.isPGroup.to_le hRT
  obtain ⟨hDK, hDodd, k, hk⟩ := hcfg.hall
  have hRK : thompsonJ S ≤ L ⊓ M := le_inf hRsyl.le (hRT.trans hcfg.T_le_M)
  have hKcard : Nat.card (L ⊓ M : Subgroup G) = Nat.card D * 2 ^ k := by
    rw [card_eq_mul_of_relIndex hDK, hk]
  have hn2D : ¬ 2 ∣ Nat.card D := by obtain ⟨j, hj⟩ := hDodd; omega
  have htwoK : twoPart (L ⊓ M : Subgroup G) = 2 ^ k := by
    unfold twoPart
    rw [hKcard, Nat.factorization_mul Nat.card_pos.ne' (by positivity)]
    simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hn2D,
      Nat.Prime.factorization_self Nat.prime_two]
  have hRcard : Nat.card (thompsonJ S) = twoPart (L ⊓ M : Subgroup G) := by
    apply le_antisymm
    · exact card_le_twoPart hRK hR2
    · rw [hRsyl.card_eq]; exact twoPart_mono inf_le_left
  have hDinfR : D ⊓ thompsonJ S = ⊥ := by
    have hdvd1 : Nat.card (D ⊓ thompsonJ S : Subgroup G) ∣ Nat.card D :=
      Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card (D ⊓ thompsonJ S : Subgroup G) ∣ 2 ^ k := by
      rw [← htwoK, ← hRcard]; exact Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (Nat.card D) (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hn2D).symm
    have h1 : Nat.card (D ⊓ thompsonJ S : Subgroup G) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hdvd2
    exact Subgroup.card_eq_one.1 h1
  have hmul := card_sup_mul_card_inf hDR
  rw [hDinfR, Subgroup.card_bot, mul_one, hRcard, htwoK] at hmul
  have hKeq : D ⊔ thompsonJ S = L ⊓ M :=
    Subgroup.eq_of_le_of_card_ge (sup_le hDK hRK) (hKcard.trans hmul.symm).le
  have hKN : (L ⊓ M : Subgroup G) ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    rw [← hKeq]
    exact sup_le hDR Subgroup.le_normalizer
  have hmK : conjR (L ⊓ M) m = L ⊓ M := by
    rw [conjR_inf, conjR_eq_of_mem_normalizer hmL, conjR_eq_of_mem hm]
  have hX : conjR (thompsonJ S) m ≤ L ⊓ M :=
    calc conjR (thompsonJ S) m ≤ conjR (L ⊓ M) m := conjR_mono hRK m
      _ = L ⊓ M := hmK
  have hX2 : IsPGroup 2 (conjR (thompsonJ S) m) := (isPGroup_conjR_iff 2).2 hR2
  have hXcard : Nat.card (conjR (thompsonJ S) m) = twoPart (L ⊓ M : Subgroup G) := by
    rw [card_conjR, hRcard]
  have hXSyl : IsSylowTwoOf (conjR (thompsonJ S) m) (L ⊓ M) :=
    isSylowTwoOf_of_card_eq hX hX2 hXcard
  have hle : thompsonJ S ≤ conjR (thompsonJ S) m := hXSyl.le_of_normalizes hRK hKN hR2
  have heq : thompsonJ S = conjR (thompsonJ S) m :=
    Subgroup.eq_of_le_of_card_ge hle (card_conjR _ m).le
  exact conjR_eq_self_iff.1 heq.symm

theorem lin2_20_four (h8 : Lemma2_4_8) (h11 : Lemma2_4_11) (h16 : Lemma2_4_16)
    (h18 : Lemma2_4_18) (h19 : Lemma2_4_19) (hcfg : Lin2Cfg G T M H S L n D) {Z : Subgroup G}
    (hZ : Z = lin2Z L (thompsonJ S)) (hc : centerOf L ≠ ⊥) :
    M ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  obtain ⟨⟨-, -, hTnR⟩, ⟨hOL, -⟩, ⟨-, -, h3⟩, -, -, -, h7, -, hirr⟩ := h8 G T M H S L D n hcfg
  obtain ⟨h111, -, h113⟩ := h11 G T M H S L D n hcfg
  obtain ⟨hZ1, hZ2, -⟩ := h16 G T M H S L D n hcfg Z hZ
  obtain ⟨hZel, hZcard, -⟩ := hZ1
  obtain ⟨hTIZ, -, -⟩ := h18 G T M H S L D n hcfg Z hZ
  have h19' : thompsonJ S = weakClosure Z T := h19 G T M H S L D n hcfg Z hZ
  obtain ⟨x, hxT, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hZR, hZZ'⟩ := ((hZ2 x hxT hxS).resolve_left fun h => hc h.1).2
  have hZe : Z = centerOf L := lin2_Z_eq_centerOf hc hZ
  have hset := hcfg.cs.setting
  have hxM : x ∈ M := hset.le hxT
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := by
    rw [← hOL]
    exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  have hPN : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hPT : pCoreOf 2 M ≤ T := hset.isSylowTwoOf_M.pCoreOf_le
  have hZcT : T ⊓ Subgroup.centralizer (T : Set G) ≤ pCoreOf 2 M :=
    hset.center_le_pCoreOf_M hset.isSylowTwoOf_M
  have htwo := lin2_20_two h8 h16 h18 hcfg hZ hc hxT hxS
  have hZR_le : Z ≤ centerOf (thompsonJ S) := lin2Z_le_centerOf h16 hcfg hZ
  have hZne : Z ≠ ⊥ := lin2Z_ne_bot h16 hcfg hZ
  have hZ'ne : conjR Z x ≠ ⊥ := fun h => hZne (conjR_eq_bot_iff.1 h)
  have hZgt : 2 < Nat.card Z := by
    rw [hZcard]
    have := hcfg.four_le_two_pow
    omega
  have hZ'gt : 2 < Nat.card (conjR Z x) := by rw [card_conjR]; exact hZgt
  have hΔP : ∀ u ∈ lin2Delta (thompsonJ S) Z x, u ∈ pCoreOf 2 M := by
    intro u hu
    obtain ⟨⟨m, hm, hmu⟩, -, -⟩ := htwo u hu
    have h1 : m⁻¹ * u * m ∈ pCoreOf 2 M := hZcT hmu
    have h2 := (Subgroup.mem_normalizer_iff.1 (hPN hm) _).1 h1
    have e : m * (m⁻¹ * u * m) * m⁻¹ = u := by group
    rwa [e] at h2
  have hZP : Z ≤ pCoreOf 2 M :=
    le_of_mem_sdiff hZZ' hZgt hZ'ne fun u hu hu1 hu2 =>
      hΔP u ⟨by rw [hZR]; exact hu, hu1, hu2⟩
  have hZ'P : conjR Z x ≤ pCoreOf 2 M :=
    le_of_mem_sdiff (by rw [inf_comm]; exact hZZ') hZ'gt hZne fun u hu hu1 hu2 =>
      hΔP u ⟨by rw [hZR, sup_comm]; exact hu, hu2, hu1⟩
  have hWR : weakClosure Z (pCoreOf 2 M) ≤ thompsonJ S :=
    (weakClosure_mono hPT).trans h19'.ge
  have hZW : Z ≤ weakClosure Z (pCoreOf 2 M) := by
    have := le_weakClosure (A := Z) (T := pCoreOf 2 M) (g := 1) (by rw [conjR_one]; exact hZP)
    rwa [conjR_one] at this
  have hZ'W : conjR Z x ≤ weakClosure Z (pCoreOf 2 M) :=
    le_weakClosure (A := Z) (T := pCoreOf 2 M) (g := x) hZ'P
  have hWM : ∀ m ∈ M, conjR (weakClosure Z (pCoreOf 2 M)) m = weakClosure Z (pCoreOf 2 M) := by
    intro m hm
    rw [conjR_weakClosure, conjR_eq_of_mem_normalizer (hPN hm)]
  have hWN : M ≤ Subgroup.normalizer ((weakClosure Z (pCoreOf 2 M) : Subgroup G) : Set G) :=
    fun m hm => conjR_eq_self_iff.1 (hWM m hm)
  have hWsplit : weakClosure Z (pCoreOf 2 M) ≤
      (weakClosure Z (pCoreOf 2 M) ⊓ blockU L) ⊔
        (weakClosure Z (pCoreOf 2 M) ⊓ conjR (blockU L) x) := by
    refine iSup₂_le fun g hg => ?_
    have hgW : conjR Z g ≤ weakClosure Z (pCoreOf 2 M) := le_weakClosure hg
    have hgR : conjR Z g ≤ thompsonJ S := hgW.trans hWR
    rcases (h7 x hxT hxS).2.2 _ hgR ((isElemAbelian_conjR_iff Z g).2 hZel) with h | h
    · exact (le_inf hgW h).trans le_sup_left
    · exact (le_inf hgW h).trans le_sup_right
  have hDN : D ≤ Subgroup.normalizer
      ((weakClosure Z (pCoreOf 2 M) ⊓ blockU L : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hWN (hcfg.D_le_M hg), hLU (hcfg.D_le_L hg)⟩
  have hZRWU : centerOf (thompsonJ S) ≤ weakClosure Z (pCoreOf 2 M) ⊓ blockU L := by
    refine le_inf (by rw [hZR]; exact sup_le hZW hZ'W) ?_
    rw [← (h3 x hxT hxS).2.1]
    exact inf_le_left
  rcases hirr _ hZRWU inf_le_right hDN with hWU | hWU
  ·
    have hWUx : weakClosure Z (pCoreOf 2 M) ⊓ conjR (blockU L) x = centerOf (thompsonJ S) := by
      have := congrArg (fun K => conjR K x) hWU
      simp only [conjR_inf, hWM x hxM] at this
      rw [this]
      exact centerOf_normalized (hTnR hxT)
    have hWeq : weakClosure Z (pCoreOf 2 M) = centerOf (thompsonJ S) := by
      apply le_antisymm
      · calc weakClosure Z (pCoreOf 2 M) ≤
              (weakClosure Z (pCoreOf 2 M) ⊓ blockU L) ⊔
                (weakClosure Z (pCoreOf 2 M) ⊓ conjR (blockU L) x) := hWsplit
          _ = centerOf (thompsonJ S) := by rw [hWU, hWUx, sup_idem]
      · rw [hZR]; exact sup_le hZW hZ'W
    have hMN : M ≤ Subgroup.normalizer ((centerOf (thompsonJ S) : Subgroup G) : Set G) := by
      intro m hm
      rw [← conjR_eq_self_iff, ← hWeq]
      exact hWM m hm
    have hTIZ' := fusionIsTI_conjR hTIZ x
    have hcase : ∀ m ∈ M, conjR Z m = Z ∨ conjR Z m = conjR Z x := by
      intro m hm
      by_contra hcon
      push Not at hcon
      obtain ⟨hne1, hne2⟩ := hcon
      have hsub : conjR Z m ≤ centerOf (thompsonJ S) :=
        calc conjR Z m ≤ conjR (centerOf (thompsonJ S)) m := conjR_mono hZR_le m
          _ = centerOf (thompsonJ S) := conjR_eq_of_mem_normalizer (hMN hm)
      have hI1 : Z ⊓ conjR Z m = ⊥ := fusionIsTI_iff_conjR.1 hTIZ m hne1
      have hI2 : conjR Z x ⊓ conjR Z m = ⊥ := by
        have h := fusionIsTI_iff_conjR.1 hTIZ' (x⁻¹ * m)
          (by rwa [conjR_conjR, mul_inv_cancel_left])
        rwa [conjR_conjR, mul_inv_cancel_left] at h
      have hmne : conjR Z m ≠ ⊥ := fun h => hZne (conjR_eq_bot_iff.1 h)
      obtain ⟨⟨v, hv⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hmne
      have hv1 : v ≠ 1 := fun h => hv1' (Subtype.ext h)
      have hvΔ : v ∈ lin2Delta (thompsonJ S) Z x := by
        refine ⟨hsub hv, fun hvZ => ?_, fun hvZ' => ?_⟩
        · have : v ∈ Z ⊓ conjR Z m := ⟨hvZ, hv⟩
          rw [hI1, Subgroup.mem_bot] at this
          exact hv1 this
        · have : v ∈ conjR Z x ⊓ conjR Z m := ⟨hvZ', hv⟩
          rw [hI2, Subgroup.mem_bot] at this
          exact hv1 this
      have hmv : m⁻¹⁻¹ * v * m⁻¹ ∈ Z := by rw [inv_inv]; exact mem_conjR.1 hv
      exact (htwo v hvΔ).2.2 m⁻¹ hmv
    have hNZ : ∀ m ∈ M, m ∈ Subgroup.normalizer (Z : Set G) →
        m ∈ Subgroup.normalizer (thompsonJ S : Set G) := by
      intro m hm hmZ
      have h1 : m ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) := by
        rw [(h113 hc).2, ← hZe]; exact hmZ
      rw [h111] at h1
      exact lin2_normalizer_R h8 hcfg hm h1
    intro m hm
    rcases hcase m hm with h | h
    · exact hNZ m hm (conjR_eq_self_iff.1 h)
    · have hmx : m * x⁻¹ ∈ Subgroup.normalizer (Z : Set G) := by
        rw [← conjR_eq_self_iff, ← conjR_conjR, h, conjR_conjR]
        simp
      have h2 := hNZ _ (M.mul_mem hm (M.inv_mem hxM)) hmx
      have h3' := (Subgroup.normalizer (thompsonJ S : Set G)).mul_mem h2 (hTnR hxT)
      simpa using h3'
  ·
    have hUW : blockU L ≤ weakClosure Z (pCoreOf 2 M) := by
      rw [← hWU]; exact inf_le_left
    have hUxW : conjR (blockU L) x ≤ weakClosure Z (pCoreOf 2 M) := by
      have := conjR_mono hUW x
      rwa [hWM x hxM] at this
    have hRW : thompsonJ S ≤ weakClosure Z (pCoreOf 2 M) := by
      rw [(h3 x hxT hxS).1]; exact sup_le hUW hUxW
    have hWeq : weakClosure Z (pCoreOf 2 M) = thompsonJ S := le_antisymm hWR hRW
    intro m hm
    rw [← conjR_eq_self_iff, ← hWeq]
    exact hWM m hm

theorem lin2_20_six (h8 : Lemma2_4_8) (h11 : Lemma2_4_11) (h16 : Lemma2_4_16)
    (h18 : Lemma2_4_18) (h19 : Lemma2_4_19) (hcfg : Lin2Cfg G T M H S L n D) {Z : Subgroup G}
    (hZ : Z = lin2Z L (thompsonJ S)) (hc : centerOf L ≠ ⊥) {x : G} (hxT : x ∈ T) (hxS : x ∉ S) :
    ∀ u ∈ lin2Delta (thompsonJ S) Z x, ∀ X : Subgroup G,
      X ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 X → X = weakClosure Z X →
        X ≤ thompsonJ S := by
  intro u hu X hXC hX2 hXw
  have hset := hcfg.cs.setting
  have h4 := lin2_20_four h8 h11 h16 h18 h19 hcfg hZ hc
  have h2 := lin2_20_two h8 h16 h18 hcfg hZ hc hxT hxS
  have hXM : X ≤ M := hXC.trans (h2 u hu).2.1
  obtain ⟨g, hgM, hXg⟩ := exists_le_conjR_of_isSylowTwoOf hset.isSylowTwoOf_M hXM hX2
  have h19' : thompsonJ S = weakClosure Z T := h19 G T M H S L D n hcfg Z hZ
  calc X = weakClosure Z X := hXw
    _ ≤ weakClosure Z (conjR T g) := weakClosure_mono hXg
    _ = conjR (weakClosure Z T) g := (conjR_weakClosure Z T g).symm
    _ = conjR (thompsonJ S) g := by rw [← h19']
    _ = thompsonJ S := conjR_eq_of_mem_normalizer (h4 hgM)

theorem lemma2_4_20 (h8 : Lemma2_4_8) (h11 : Lemma2_4_11) (h16 : Lemma2_4_16)
    (h18 : Lemma2_4_18) (h19 : Lemma2_4_19) : Lemma2_4_20 := by
  intro G _ _ T M H S L D n hcfg Z hZ hc
  refine ⟨fun B hB x hxN hxS => lin2_20_reg h8 h16 hcfg hZ hc hB hxN hxS, fun x hxT hxS => ?_⟩
  have h4 := lin2_20_four h8 h11 h16 h18 h19 hcfg hZ hc
  have h2 := lin2_20_two h8 h16 h18 hcfg hZ hc hxT hxS
  exact ⟨h2, lin2_20_three h8 h16 hcfg hZ hc hxT hxS, h4, fun u hu => (h2 u hu).2.1.trans h4,
    lin2_20_five h16 h18 hcfg hZ hc, lin2_20_six h8 h11 h16 h18 h19 hcfg hZ hc hxT hxS⟩

end Parts

end CFSG.QuasithinUnique.Lin2
