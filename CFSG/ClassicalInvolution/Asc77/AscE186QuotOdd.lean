module

public import CFSG.ClassicalInvolution.Asc77.AscE186Quot
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.Asc77.AscE184Dich

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime]

theorem exists_W_of_hypOmega (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaMod p f Ω) (S : Sylow 2 G) :
    ∃ W ∈ WSet Ω, W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W := by
  obtain ⟨η, hη, hinv⟩ := (l6_9_proved p f hp hq G Ω hΩ S).1
  have hS : ∀ U ∈ η, U ≤ (S : Subgroup G) := fun U hU => (hη.1 hU).2
  have hle : ∀ t ∈ (S : Subgroup G), conjSub t (⨆ U ∈ η, U) ≤ ⨆ U ∈ η, U := by
    intro t ht
    rw [conjSub_iSup]
    refine iSup_le fun U => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hU => ?_
    exact le_iSup₂_of_le (conjSub t U) (hinv t ht U hU) le_rfl
  refine ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le hS, fun s hs => ?_⟩
  apply le_antisymm (hle s hs)
  have := conjSub_mono (n := s) (hle s⁻¹ ((S : Subgroup G).inv_mem hs))
  rwa [conjSub_conjSub_inv] at this

abbrev E186Cent2 (Ω : Set (Subgroup G)) (K H : Subgroup G) : Prop :=
  CentralizersSylowPairs Ω K H

theorem exists_involution_lift_of_isPGroup {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N))
    {P : Subgroup G} (hP : IsPGroup 2 P) {a : G ⧸ N} (ha : a ∈ P.map (QuotientGroup.mk' N))
    (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    ∃ b ∈ P, b ≠ 1 ∧ b * b = 1 ∧ QuotientGroup.mk' N b = a := by
  obtain ⟨b, hb, rfl⟩ := ha
  have hbb : b * b ∈ N := by
    have : QuotientGroup.mk' N (b * b) = 1 := by rw [map_mul]; exact ha2
    exact (QuotientGroup.eq_one_iff _).mp this
  have hPN : P ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hP le_rfl
      (hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hbb' : b * b = 1 := by
    have : b * b ∈ P ⊓ N := ⟨P.mul_mem hb hb, hbb⟩
    rw [hPN, Subgroup.mem_bot] at this
    exact this
  refine ⟨b, hb, fun h => ha1 ?_, hbb', rfl⟩
  rw [h, map_one]

theorem isSylow2In_sup_of_odd {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) {R : Subgroup G}
    (hR : IsPGroup 2 R) : IsSylow2In R (R ⊔ N) := by
  refine ⟨le_sup_left, hR, fun V hVle hV2 hRV => ?_⟩
  have hodd : ∀ P : Subgroup G, Odd (Nat.card ↥(N ⊓ P)) := fun P =>
    hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hRN : R ⊓ N = ⊥ := AscQuot.inf_eq_bot_of_isPGroup_of_odd N hR le_rfl (hodd R)
  have hVN : V ⊓ N = ⊥ := AscQuot.inf_eq_bot_of_isPGroup_of_odd N hV2 le_rfl (hodd V)
  have hmap : V.map (QuotientGroup.mk' N) ≤ R.map (QuotientGroup.mk' N) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨r, hr, n, hn, hrn⟩ := Subgroup.mem_sup_of_normal_right.mp (hVle hv)
    refine ⟨r, hr, ?_⟩
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    rw [← hrn, map_mul, hn1, mul_one]
  have hcard : Nat.card V ≤ Nat.card R := by
    have h1 : Nat.card V = Nat.card ↥(V.map (QuotientGroup.mk' N)) :=
      Nat.card_congr (AscQuot.quotRestrictEquiv hVN).toEquiv
    have h2 : Nat.card R = Nat.card ↥(R.map (QuotientGroup.mk' N)) :=
      Nat.card_congr (AscQuot.quotRestrictEquiv hRN).toEquiv
    rw [h1, h2]
    exact Subgroup.card_le_of_le hmap
  exact (Subgroup.eq_of_le_of_card_ge hRV hcard).symm

theorem E186Cent2.quot_odd {Ω : Set (Subgroup G)} (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {N : Subgroup G} [N.Normal] (hΩ' : HypOmegaMod p f (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {K H : Subgroup G} (hK : K ∈ Ω) (h : E186Cent2 Ω K H) :
    E186Cent2 (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N)) := by
  set mk := QuotientGroup.mk' N with hmk
  intro Lb hLb Jb hJb Rb₁ Rb₂ hRb₁ hRb₁L hRb₂ hRb₂J hc a ha ha1 ha2
  obtain ⟨L, hLtw, rfl⟩ := exists_lift_twin hp hq hΩ hN hK hLb
  have hLΩ : L ∈ Ω := hLtw.1
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hLΩ
  obtain ⟨R₁, hR₁, hR₁L, rfl⟩ := exists_lift_RSet hp hΩ' hN hLΩ hRb₁ hRb₁L
  have hR₁syl : IsSylow2In R₁ L := hΩ.isSylow2In_of_mem_RSet_of_le hp hLΩ hR₁ hR₁L
  have hR₁2 : IsPGroup 2 R₁ := hR₁syl.2.1
  have hR₁8 := hΩ.eight_le_of_mem_RSet hp hR₁
  have hJbΩ : Jb ∈ quotFamily Ω N := by
    rcases hJb with rfl | hJb'
    · exact map_mem_quotFamily hLΩ
    · exact hJb'.1
  obtain ⟨J₀, hJ₀, rfl⟩ := hJbΩ
  obtain ⟨R₂, hR₂, hR₂J, rfl⟩ := exists_lift_RSet hp hΩ' hN hJ₀ hRb₂ hRb₂J
  have hR₂syl : IsSylow2In R₂ J₀ := hΩ.isSylow2In_of_mem_RSet_of_le hp hJ₀ hR₂ hR₂J
  have final : ∀ (J R₂' : Subgroup G), J ∈ KPerp Ω L → R₂' ∈ RSet Ω → R₂' ≤ J →
      (Commutes R₁ R₂' ∨ R₂' = R₁) → R₂'.map mk = R₂.map mk → IsPGroup 2 ↥(R₁ ⊔ R₂') →
        Subgroup.centralizer ({a} : Set (G ⧸ N)) ≤ H.map mk := by
    intro J R₂' hJ hR₂' hR₂'J hcomm hmap hP
    have haP : a ∈ (R₁ ⊔ R₂').map mk := by
      rw [Subgroup.map_sup, hmap]
      exact ha
    obtain ⟨b, hbP, hb1, hb2, rfl⟩ := exists_involution_lift_of_isPGroup hN hP haP ha1 ha2
    exact (centralizer_map_le hN hb2).trans
      (Subgroup.map_mono (h L hLtw J hJ R₁ R₂' hR₁ hR₁L hR₂' hR₂'J hcomm b hbP hb1 hb2))
  rcases hc with hcomm | heq
  ·
    have hperm : ∀ x ∈ R₁, ∃ n ∈ N, conjSub x R₂ = conjSub n R₂ := by
      intro x hx
      have hxb : conjSub (mk x) (R₂.map mk) = R₂.map mk :=
        conjSub_eq_of_mem_of_commutes (Subgroup.mem_map_of_mem _ hx) hcomm
      have hmapx : (conjSub x R₂).map mk = R₂.map mk := by rw [AscQuot.map_conjSub, hxb]
      have hxle : conjSub x R₂ ≤ R₂ ⊔ N := by
        intro y hy
        have hy' : mk y ∈ R₂.map mk := hmapx ▸ Subgroup.mem_map_of_mem _ hy
        obtain ⟨r, hr, hry⟩ := hy'
        have hrn : r⁻¹ * y ∈ N := by
          have : QuotientGroup.mk' N (r⁻¹ * y) = 1 := by
            rw [map_mul, map_inv, hry, inv_mul_cancel]
          exact (QuotientGroup.eq_one_iff _).mp this
        have : y = r * (r⁻¹ * y) := by group
        rw [this]
        exact (R₂ ⊔ N).mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hrn)
      have hS₁ := isSylow2In_sup_of_odd hN hR₂syl.2.1
      have hS₂ : IsSylow2In (conjSub x R₂) (R₂ ⊔ N) :=
        hS₁.of_natCard_le (hR₂syl.2.1.map _) hxle (by
          rw [Nat.card_congr (Subgroup.equivMapOfInjective R₂ (MulAut.conj x).toMonoidHom
            (MulAut.conj x).injective).toEquiv]
          rfl)
      obtain ⟨p', hp', hpx⟩ := exists_conjSub_eq_of_isSylow2In hS₁ hS₂
      obtain ⟨r, hr, n, hn, hrn⟩ := Subgroup.mem_sup_of_normal_right.mp hp'
      refine ⟨r * n * r⁻¹, ‹N.Normal›.conj_mem n hn r, ?_⟩
      rw [← hpx, ← hrn]
      calc conjSub (r * n) R₂ = conjSub ((r * n * r⁻¹) * r) R₂ := by congr 1; group
        _ = conjSub (r * n * r⁻¹) (conjSub r R₂) := conjSub_mul _ _ _
        _ = conjSub (r * n * r⁻¹) R₂ := by rw [conjSub_eq_self_of_mem hr]
    obtain ⟨m, hm, hmN⟩ := exists_conj_normalizer_of_perm hN R₂ hR₁2 hperm
    have hmk1 : mk m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    have hJ'Ω : conjSub m J₀ ∈ Ω := hΩ.conjInvariant m J₀ hJ₀
    have hR₂'mem : conjSub m R₂ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₂ m
    have hR₂'J' : conjSub m R₂ ≤ conjSub m J₀ := conjSub_mono hR₂J
    have hmap : (conjSub m R₂).map mk = R₂.map mk := by
      rw [AscQuot.map_conjSub, hmk1, conjSub_one]
    have hR₂'syl : IsSylow2In (conjSub m R₂) (conjSub m J₀) :=
      hΩ.isSylow2In_of_mem_RSet_of_le hp hJ'Ω hR₂'mem hR₂'J'
    have hP : IsPGroup 2 ↥(R₁ ⊔ conjSub m R₂) := hR₁2.to_sup_of_normal_right' hR₂'syl.2.1 hmN
    by_cases hJL : conjSub m J₀ = L
    ·
      have hle : R₁ ⊔ conjSub m R₂ ≤ L := sup_le hR₁L (hJL ▸ hR₂'J')
      have hsyl : IsSylow2In (conjSub m R₂) L := hJL ▸ hR₂'syl
      have h1 : R₁ ⊔ conjSub m R₂ = conjSub m R₂ := hsyl.2.2 _ hle hP le_sup_right
      have h2 : R₁ ≤ conjSub m R₂ := h1 ▸ le_sup_left
      have heq' : conjSub m R₂ = R₁ :=
        (Subgroup.eq_of_le_of_card_ge h2 (hR₁syl.natCard_eq hsyl).ge).symm
      exact final L R₁ (Set.mem_insert _ _) hR₁ hR₁L (Or.inr rfl) (by rw [← heq', hmap])
        (by rw [sup_idem]; exact hR₁2)
    · have hLJ : L ≠ conjSub m J₀ := fun h' => hJL h'.symm
      have hne : R₁ ≠ conjSub m R₂ := by
        intro h'
        exact hLJ (hΩ.eq_of_le_of_le hLΩ hJ'Ω hR₁2 (by omega) hR₁L (h' ▸ hR₂'J'))
      obtain ⟨S, hS⟩ := hP.exists_le_sylow
      have hcomm' : Commutes R₁ (conjSub m R₂) :=
        l6_7_proved p f hp hq G Ω hΩ S R₁ hR₁ _ hR₂'mem (le_sup_left.trans hS)
          (le_sup_right.trans hS) hne
      have hzR₁ : z ∈ R₁ := AscL62.mem_of_uniqueInvolution_of_pGroup hz hR₁L hR₁2 (by omega)
      have hAc : conjSub m R₂ ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' z hzR₁ y hy).symm
      have hR₂'8 := hΩ.eight_le_of_mem_RSet hp hR₂'mem
      have hN' : conjSub m R₂ ≤ Subgroup.normalizer (L : Set G) :=
        hΩ.le_normalizer_of_le_centralizer hp hq hLΩ hJ'Ω hLJ hz hR₂'J' hR₂'syl.2.1 (by omega) hAc
      exact final (conjSub m J₀) (conjSub m R₂)
        (Set.mem_insert_of_mem _ ⟨hJ'Ω, hJL, conjSub m R₂, hR₂'mem, hR₂'J', hN'⟩) hR₂'mem hR₂'J'
        (Or.inl hcomm') hmap hP
  ·
    exact final L R₁ (Set.mem_insert _ _) hR₁ hR₁L (Or.inr rfl) heq.symm
      (by rw [sup_idem]; exact hR₁2)

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem natCard_quotient_le (N : Subgroup G) [N.Normal] : Nat.card (G ⧸ N) ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N)

theorem E187C.odd_quot_trans_of {G : Type} [Group G] {Ω : Set (Subgroup G)} {K H N : Subgroup G}
    [N.Normal] (hc : ConjInvariant Ω)
    (hexn : ∀ {L L' : Subgroup G}, L ∈ Ω → L' ∈ Ω →
      L'.map (QuotientGroup.mk' N) ∈
        omegaStarNbr (quotFamily Ω N) (L.map (QuotientGroup.mk' N)) →
      ∃ n ∈ N, L' ∈ omegaStarNbr Ω (conjSub n L))
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) (hK : K ∈ Ω) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb := by
  intro Jb hJb
  obtain ⟨M, hM, hMeq, hMgood⟩ := exists_good_lift (N := N)
    (fun L : Subgroup G => L ∈ dstarComp Ω K) hK Relation.ReflTransGen.refl
    (E187C.good_lift_step_of _ hc hexn (fun L hL L' hL' hgood hadj => hgood.tail hadj)) hJb
  obtain ⟨h, hhH, hh⟩ := htrans M hMgood
  refine ⟨QuotientGroup.mk' N h, Subgroup.mem_map_of_mem _ hhH, ?_⟩
  rw [← hMeq, ← hh, AscQuot.map_conjSub]

theorem MinCex.odd_quot_trans (c : MinCex p f Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hΩ' : HypOmegaMod p f (quotFamily Ω N)) (hN : Odd (Nat.card N)) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  exact E187C.odd_quot_trans_of hΩ.conjInvariant
    (fun hL hL' hadj => exists_conj_omegaStarNbr hp hq hΩ hΩ' hN hL hL' hadj) c.hyp.trans
    c.stand.mem

theorem MinCex.odd_quot_stand (c : MinCex p f Ω K S R W H) {N : Subgroup G} [N.Normal]
    (hΩ' : HypOmegaMod p f (quotFamily Ω N)) (hN : Odd (Nat.card N)) :
    ∃ (Sb : Sylow 2 (G ⧸ N)) (Rb Wb : Subgroup (G ⧸ N)),
      EStand p f (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) Sb Rb Wb := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have h3 : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3 p f (l6_7_proved p f) G Ω K S R W H c
  have hAΩ : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant h3 c.stand.aEmpty
  set Sb : Sylow 2 (G ⧸ N) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S with hSbdef
  have hSb : (Sb : Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S
  obtain ⟨Wb, hWb, hWbS, hWbn⟩ := exists_W_of_hypOmega hp hq hΩ' Sb
  have hRsyl : IsSylow2In R K := hΩ.isSylow2In_of_mem_RSet_of_le hp hK hRR hRK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'tw
  have hR'syl : IsSylow2In R' K' := hΩ.isSylow2In_of_mem_RSet_of_le hp hK'Ω hR' hR'K'
  refine ⟨Sb, R.map (QuotientGroup.mk' N), Wb, ?_⟩
  exact
    { odd := hp
      five := hq
      hyp := hΩ'
      below := CITBelowU.mono p f (natCard_quotient_le N) c.stand.below
      mem := map_mem_quotFamily hK
      aEmpty := aEmpty_quotFamily hp hq hΩ hΩ' hN hAΩ _ (map_mem_quotFamily hK)
      twin := ⟨K'.map (QuotientGroup.mk' N),
        ⟨map_mem_quotFamily hK'Ω, QuotientGroup.mk' N z,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hzK,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K') hzK'⟩,
        map_ne_of_twin hp hq hΩ hN hK ⟨hK'Ω, z, hzK, hzK'⟩ hK'ne,
        R'.map (QuotientGroup.mk' N),
        mem_RSet_of_isSylow2In (map_mem_quotFamily hK'Ω) (isSylow2In_map_mk hN hR'syl),
        Subgroup.map_mono hR'K', hSb ▸ Subgroup.map_mono hR'S⟩
      hR := ⟨mem_RSet_of_isSylow2In (map_mem_quotFamily hK) (isSylow2In_map_mk hN hRsyl),
        Subgroup.map_mono hRK, hSb ▸ Subgroup.map_mono hRS⟩
      hW := ⟨hWb, hWbS, hWbn⟩ }

end CFSG.ClassicalInvolution.Asc77
