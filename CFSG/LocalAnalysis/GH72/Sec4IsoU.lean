module

public import CFSG.LocalAnalysis.GH72.Sec4Lemma45

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.GorensteinWalter (HasDihedralSylowTwo IsOddPrimePower PSL2 PGL2)

namespace G4b

section Dihedral

variable {Z : Type} [Group Z] [Finite Z]

theorem hasDihedralSylowTwo_bar {U : Subgroup Z} (hD : HasDihedralSylowTwo U) :
    HasDihedralSylowTwo (Bar U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T'
  obtain ⟨T, rfl⟩ :=
    Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective (CFSG.oddCore U)) 2 T'
  obtain ⟨m, hm, ⟨e⟩⟩ := hD T
  set K : Subgroup Z := (T : Subgroup U).map U.subtype with hK
  have hKU : K ≤ U := map_subtype_le _
  have hK2 : IsPGroup 2 K := T.isPGroup'.map _
  obtain ⟨eb⟩ := nonempty_mulEquiv_bar hKU hK2
  have hT : K.subgroupOf U = (T : Subgroup U) := by
    rw [hK, subgroupOf, comap_map_eq_self_of_injective U.subtype_injective]
  have heq : bar U K = ((T.mapSurjective (QuotientGroup.mk'_surjective _) : Sylow 2 (Bar U)) :
      Subgroup (Bar U)) := by
    rw [Sylow.coe_mapSurjective, bar, hT]
  have eT : (T : Subgroup U) ≃* K := (T : Subgroup U).equivMapOfInjective U.subtype
    U.subtype_injective
  exact ⟨m, hm, ⟨(MulEquiv.subgroupCongr heq.symm).trans (eb.symm.trans (eT.symm.trans e))⟩⟩

omit [Finite Z] in
theorem le_of_isPGroup_of_odd_index {L W : Subgroup Z} [L.Normal] (hL : Odd L.index)
    (hW : IsPGroup 2 W) : W ≤ L := by
  intro w hw
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (QuotientGroup.mk' L w) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk', map_one])
  have h2 : orderOf (QuotientGroup.mk' L w) ∣ L.index := orderOf_dvd_natCard _
  have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hL)) h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem eq_bot_of_card_twelve {X : Type} [Group X] [Finite X] (hO : CFSG.oddCore X = ⊥)
    {L V R : Subgroup X} (hLn : L.Normal) (hL12 : Nat.card L = 12) (hV : IsKleinFour V)
    (hVL : V ≤ L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hRL : R ≤ L) (hR : IsPGroup p R)
    (hVR : V ≤ normalizer (R : Set X)) : R = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have hRodd := odd_card_of_isPGroup hp hp2 hR
  have hRV : R ⊓ V = ⊥ := eq_bot_iff.2 fun x hx =>
    (mem_bot).2 (eq_one_of_mem_of_mem hV2 hRodd (mem_inf.1 hx).2 (mem_inf.1 hx).1)
  have hcard : Nat.card ↥(R ⊔ V) = Nat.card R * 4 := by
    rw [CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hVR hRV, hV.card_four]
  have hdvd : Nat.card R * 4 ∣ 12 := hcard ▸ hL12 ▸ card_dvd_of_le (sup_le hRL hVL)
  have h3 : Nat.card R ∣ 3 :=
    Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 4)
      (by rw [show (3 : ℕ) * 4 = 12 by norm_num]; exact hdvd)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 h3 with h1 | h3'
  · exact (card_eq_one).1 h1
  ·
    have hRVL : R ⊔ V = L := eq_of_le_of_card_ge (sup_le hRL hVL) (by rw [hcard, h3', hL12])
    have hLR : L ≤ normalizer (R : Set X) := hRVL ▸ sup_le le_normalizer hVR
    have h3p : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hR3 : IsPGroup 3 R := IsPGroup.of_card (n := 1) (by rw [h3', pow_one])
    have hsyl : ABGLocalTools.IsSylowOf 3 R L := by
      rw [ABGLocalTools.isSylowOf_iff]
      refine ⟨hRL, hR3, fun h => ?_⟩
      have h1 := relIndex_mul_card R L
      rw [inf_eq_left.2 hRL, h3', hL12] at h1
      omega
    have hRn : R.Normal := by
      rw [← normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have h1 := isSylowOf_map_hom hsyl (MulAut.conj g).toMonoidHom
      have hLg : L.map (MulAut.conj g).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq'.1 (by rw [normalizer_eq_top_iff.2 hLn]; exact mem_top g)
      rw [hLg] at h1
      obtain ⟨l, hl, hlR⟩ := exists_map_conj_eq_of_isSylowOf hsyl h1
      rw [mem_normalizer_iff_map_conj_eq', ← hlR]
      exact mem_normalizer_iff_map_conj_eq'.1 (hLR hl)
    have hle : R ≤ CFSG.oddCore X := le_sSup ⟨hRn, hRodd⟩
    rw [hO] at hle
    exact eq_bot_iff.2 hle


theorem factor_facts {X : Type} [Group X] [Finite X] (hO : CFSG.oddCore X = ⊥)
    {L V : Subgroup X} (hLn : L.Normal) (hV : IsKleinFour V) (hVL : V ≤ L)
    {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hM : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (∀ Q, IsMaxInvIn p V L Q →
      normalizer (L : Set X) ⊓ centralizer (V : Set X) ≤ normalizer (Q : Set X)) ∧
    (∀ Q Q', IsMaxInvIn p V L Q → IsMaxInvIn p V L Q' →
      ∃ g ∈ L ⊓ normalizer (V : Set X), Q.map (MulAut.conj g).toMonoidHom = Q') := by
  have hK' := hK
  obtain ⟨r, n, hr, hrodd, hn, hq⟩ := hK
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd hrodd (by decide)
  obtain ⟨eK⟩ := nonempty_ringEquiv_galoisField (p := r) (n := n) (by omega) hq
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    rcases Nat.lt_or_ge r 3 with h | h
    · omega
    · exact h
  have hq3 : 3 ≤ r ^ n := le_trans hr3 (Nat.le_self_pow (by omega) r)
  have good : IsL2PGL2OrA7OrV4 L →
      (∀ Q, IsMaxInvIn p V L Q →
        normalizer (L : Set X) ⊓ centralizer (V : Set X) ≤ normalizer (Q : Set X)) ∧
      (∀ Q Q', IsMaxInvIn p V L Q → IsMaxInvIn p V L Q' →
        ∃ g ∈ L ⊓ normalizer (V : Set X), Q.map (MulAut.conj g).toMonoidHom = Q') := fun hL =>
    ⟨fun Q hQ => normalizer_inf_centralizer_le_normalizer_of_isMaxInvIn hL hV hVL hp hp2 hQ,
      fun Q Q' hQ hQ' => exists_conj_eq_of_isMaxInvIn hL hV hVL hp hp2 hQ hQ'⟩
  rcases hM with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · by_cases h5 : 5 ≤ r ^ n
    · exact good (Or.inl (Or.inr ⟨r, n, ⟨hr⟩, hr2, h5,
        ⟨e.trans (CFSG.GorensteinWalter.psl2RingEquiv eK)⟩⟩))
    ·
      have hq3' : Nat.card K = 3 := by
        obtain ⟨k, hk⟩ := hrodd.pow (n := n)
        omega
      have hL12 : Nat.card L = 12 := by
        rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula K hK', hq3']
        norm_num
      have hbot : ∀ Q, IsMaxInvIn p V L Q → Q = ⊥ := fun Q hQ =>
        eq_bot_of_card_twelve hO hLn hL12 hV hVL hp hp2 hQ.1 hQ.2.1 hQ.2.2.1
      refine ⟨fun Q hQ => ?_, fun Q Q' hQ hQ' => ?_⟩
      · rw [hbot Q hQ]
        intro g _
        rw [normalizer_eq_top_iff.2 (inferInstance : (⊥ : Subgroup X).Normal)]
        exact mem_top g
      · refine ⟨1, mem_inf.2 ⟨one_mem _, one_mem _⟩, ?_⟩
        rw [map_conj_one, hbot Q hQ, hbot Q' hQ']
  · exact good (Or.inr (Or.inl ⟨r, n, ⟨hr⟩, hr2, hq3,
      ⟨e.trans (CFSG.GorensteinWalter.pgl2RingEquiv eK)⟩⟩))


theorem exists_conj_of_hasDihedralSylowTwo {U V : Subgroup Z} (hVU : V ≤ U)
    (hV : IsKleinFour V) (hD : HasDihedralSylowTwo U) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P₁ P₂ : Subgroup Z} (h₁ : IsMaxInvIn p V U P₁) (h₂ : IsMaxInvIn p V U P₂) :
    ∃ g ∈ U ⊓ normalizer (V : Set Z), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have hD' := hasDihedralSylowTwo_bar hD
  have hO : CFSG.oddCore (Bar U) = ⊥ := oddCore_quotient_oddCore_eq_bot U
  set W : Subgroup (Bar U) := bar U V with hWdef
  have hW : IsKleinFour W := isKleinFour_bar hVU hV
  have hbar : ∀ {P : Subgroup Z}, IsMaxInvIn p V U P → IsMaxInvIn p (W ⊔ ⊥) ⊤ (bar U P) := by
    intro P hP
    have h := isMaxInvIn_bar hp hp2 le_rfl hVU hV2 hP
    rw [bar_self] at h
    rw [sup_bot_eq]
    exact h
  suffices hy : ∃ y ∈ normalizer (W : Set (Bar U)),
      (bar U P₁).map (MulAut.conj y).toMonoidHom = bar U P₂ by
    obtain ⟨y, hy, hyP⟩ := hy
    refine exists_conj_of_bar hp hp2 le_rfl hVU hV2 h₁ h₂ (y := y) ?_ hyP
    rw [bar_self]
    exact mem_inf.2 ⟨mem_top y, hy⟩
  have one : ∀ {L : Subgroup (Bar U)}, L.Normal → W ≤ L →
      (∀ Q, IsMaxInvIn p W L Q →
        normalizer (L : Set (Bar U)) ⊓ centralizer (W : Set (Bar U)) ≤ normalizer (Q : Set (Bar U))) →
      (∀ Q Q', IsMaxInvIn p W L Q → IsMaxInvIn p W L Q' →
        ∃ g ∈ L ⊓ normalizer (W : Set (Bar U)), Q.map (MulAut.conj g).toMonoidHom = Q') →
      ∃ y ∈ normalizer (W : Set (Bar U)),
        (bar U P₁).map (MulAut.conj y).toMonoidHom = bar U P₂ := by
    intro L hLn hWL F9 F10
    have hJL : (⊤ : Subgroup (Bar U)) ≤ normalizer (L : Set (Bar U)) := by
      rw [normalizer_eq_top_iff.2 hLn]
    obtain ⟨y, hy, hyP⟩ := exists_conj_of_factors (J := ⊤) (L₂ := ⊥) (V₂ := ⊥) hp hp2 hWL le_rfl
      le_top bot_le hJL (by rw [normalizer_eq_top_iff.2 inferInstance]) bot_le (inf_bot_eq _)
      (by rw [sup_bot_eq]; exact isPGroup_bar hV2) F9
      (fun Q hQ => by
        rw [isMaxInvIn_bot_eq hQ, normalizer_eq_top_iff.2 inferInstance]
        exact le_top)
      F10
      (fun Q Q' hQ hQ' => ⟨1, mem_inf.2 ⟨one_mem _, one_mem _⟩, by
        rw [map_conj_one, isMaxInvIn_bot_eq hQ, isMaxInvIn_bot_eq hQ']⟩)
      (hbar h₁) (hbar h₂) le_top le_top
    rw [sup_bot_eq] at hy
    exact ⟨y, (mem_inf.1 hy).2, hyP⟩
  rcases CFSG.QuasiDihedralFusion.gw_cases hD' hO with h2 | ⟨⟨e7⟩⟩ |
    ⟨K, _, _, hK, L, hLn, hLodd, hM⟩
  ·
    have hbot : ∀ {P : Subgroup Z}, IsMaxInvIn p V U P → bar U P = ⊥ := by
      intro P hP
      have hP' := hbar hP
      refine eq_bot_iff.2 fun y hy => (mem_bot).2 ?_
      exact eq_one_of_mem_of_mem (A := ⊤) (h2.to_subgroup ⊤)
        (odd_card_of_isPGroup hp hp2 hP'.2.1) (mem_top y) hy
    exact ⟨1, one_mem _, by rw [map_conj_one, hbot h₁, hbot h₂]⟩
  ·
    have hL : IsL2PGL2OrA7OrV4 (⊤ : Subgroup (Bar U)) := Or.inl (Or.inl ⟨topEquiv.trans e7⟩)
    exact one inferInstance le_top
      (fun Q hQ => normalizer_inf_centralizer_le_normalizer_of_isMaxInvIn hL hW le_top hp hp2 hQ)
      (fun Q Q' hQ hQ' => exists_conj_eq_of_isMaxInvIn hL hW le_top hp hp2 hQ hQ')
  ·
    have hWL : W ≤ L := le_of_isPGroup_of_odd_index hLodd (isPGroup_bar hV2)
    obtain ⟨F9, F10⟩ := factor_facts hO hLn hW hWL hK hM hp hp2
    exact one hLn hWL F9 F10

end Dihedral

end G4b

end CFSG.GH72
