module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Core
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem Sp62Block.commute_commutator {c s y : Y} (h1 : Commute y s)
    (h2 : Commute (c⁻¹ * y * c) s) : Commute y (c * s * c⁻¹ * s⁻¹) := by
  refine Commute.mul_right ?_ h1.inv_right
  have h3 : y * (c * s * c⁻¹) = c * ((c⁻¹ * y * c) * s) * c⁻¹ := by group
  have h4 : (c * s * c⁻¹) * y = c * (s * (c⁻¹ * y * c)) * c⁻¹ := by group
  show y * (c * s * c⁻¹) = (c * s * c⁻¹) * y
  rw [h3, h4, h2.eq]

theorem Sp62Block.centralizer_le_centralizer_of_component (hY : CFSG.pCore 2 Y = ⊥)
    {L T : Subgroup Y} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set Y))
    (hTO : CFSG.pPrimeCore 2 Y ≤ Subgroup.centralizer (T : Set Y))
    (hTJ : ∀ J : Subgroup Y, IsComponentOf J ⊤ → J ≠ L →
      T ≤ Subgroup.centralizer (J : Set Y)) :
    Subgroup.centralizer (L : Set Y) ≤ Subgroup.centralizer (T : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  set w := c * s * c⁻¹ * s⁻¹ with hw
  have hO : ∀ y ∈ CFSG.pPrimeCore 2 Y, Commute y w := by
    intro y hy
    refine Sp62Block.commute_commutator
      ((Subgroup.mem_centralizer_iff.mp (hTO hy) s hs).symm) ?_
    have hy' : c⁻¹ * y * c ∈ CFSG.pPrimeCore 2 Y := by
      simpa using (CFSG.pPrimeCore_normal (p := 2) (G := Y)).conj_mem y hy c⁻¹
    exact (Subgroup.mem_centralizer_iff.mp (hTO hy') s hs).symm
  have hLw : ∀ y ∈ L, Commute y w := by
    intro y hy
    have hcy : Commute y c := (Subgroup.mem_centralizer_iff.mp hc y hy)
    have hsy : s⁻¹ * y * s ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem hs)) y).mp hy
      simpa using this
    have hcy' : Commute (s⁻¹ * y * s) c := Subgroup.mem_centralizer_iff.mp hc _ hsy
    have h1 : Commute y (s * c⁻¹ * s⁻¹) := by
      have e : y = s * (s⁻¹ * y * s) * s⁻¹ := by group
      rw [e]
      have := hcy'.inv_right
      show s * (s⁻¹ * y * s) * s⁻¹ * (s * c⁻¹ * s⁻¹) =
        (s * c⁻¹ * s⁻¹) * (s * (s⁻¹ * y * s) * s⁻¹)
      have h5 : s * (s⁻¹ * y * s) * s⁻¹ * (s * c⁻¹ * s⁻¹) =
          s * ((s⁻¹ * y * s) * c⁻¹) * s⁻¹ := by group
      have h6 : (s * c⁻¹ * s⁻¹) * (s * (s⁻¹ * y * s) * s⁻¹) =
          s * (c⁻¹ * (s⁻¹ * y * s)) * s⁻¹ := by group
      rw [h5, h6, this.eq]
    have e : w = c * (s * c⁻¹ * s⁻¹) := by rw [hw]; group
    rw [e]
    exact hcy.mul_right h1
  have hJw : ∀ J : Subgroup Y, IsComponentOf J ⊤ → ∀ y ∈ J, Commute y w := by
    intro J hJ y hy
    by_cases hJL : J = L
    · exact hLw y (hJL ▸ hy)
    have hJc : IsComponentOf (J.map (MulAut.conj c⁻¹).toMonoidHom) ⊤ :=
      (CFSG.ComponentClassification.LocalComponents.equiv_iff _ _).mpr hJ
    have hJcL : J.map (MulAut.conj c⁻¹).toMonoidHom ≠ L := by
      intro heq
      apply hJL
      have hLc : L.map (MulAut.conj c).toMonoidHom = L := by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨l, hl, rfl⟩
          have := (Subgroup.mem_centralizer_iff.mp hc l hl)
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [← this, mul_inv_cancel_right]; exact hl
        · intro l hl
          refine ⟨l, hl, ?_⟩
          have := (Subgroup.mem_centralizer_iff.mp hc l hl)
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [← this, mul_inv_cancel_right]
      calc J = (J.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
            rw [Subgroup.map_map]
            ext x
            simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
              Function.comp_apply, MulAut.conj_apply]
            constructor
            · intro hx
              exact ⟨x, hx, by group⟩
            · rintro ⟨x', hx', rfl⟩
              simpa [mul_assoc] using hx'
        _ = L := by rw [heq, hLc]
    refine Sp62Block.commute_commutator
      (Subgroup.mem_centralizer_iff.mp (hTJ J hJ hJL hs) y hy) ?_
    have hy' : c⁻¹ * y * c ∈ J.map (MulAut.conj c⁻¹).toMonoidHom :=
      ⟨y, hy, by simp⟩
    exact Subgroup.mem_centralizer_iff.mp (hTJ _ hJc hJcL hs) _ hy'
  have hwF : w ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup Y : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : CFSG.ComponentClassification.GeneralizedFitting.subgroup Y ≤
        Subgroup.centralizer ({w} : Set Y) := by
      refine sup_le ((fitting_le_pPrimeCore_two hY).trans fun y hy => ?_)
        (sSup_le fun J hJ => fun y hy => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hO y hy).eq
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hJw J hJ y hy).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hwO : w ∈ CFSG.pPrimeCore 2 Y := fitting_le_pPrimeCore_two hY
    (CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting Y hwF)
  have hsw : Commute w s := (Subgroup.mem_centralizer_iff.mp (hTO hwO) s hs).symm
  obtain ⟨k, hk⟩ := hT ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcs : c * s * c⁻¹ = w * s := by rw [hw]; group
  have hw1 : w ^ 2 ^ k = 1 := by
    have h1 : (c * s * c⁻¹) ^ 2 ^ k = 1 := by rw [conj_pow, hk']; group
    rw [hcs, hsw.mul_pow, hk', mul_one] at h1
    exact h1
  have hodd : Nat.Coprime 2 (orderOf w) := by
    have hdvd : orderOf w ∣ Nat.card (CFSG.pPrimeCore 2 Y) :=
      Subgroup.orderOf_dvd_natCard _ hwO
    exact Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card
  have hw : w = 1 := by
    have hdvd : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hw1
    have h1 : orderOf w = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hodd).symm hdvd
    exact orderOf_eq_one_iff.mp h1
  have : c * s * c⁻¹ * s⁻¹ = 1 := hw
  calc s * c = (c * s * c⁻¹ * s⁻¹)⁻¹ * (c * s) := by group
    _ = c * s := by rw [this, inv_one, one_mul]

end Abstract

section Block

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R V L : Subgroup G}

theorem Sp62Block.le_centralizer_component
    (hL : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    {J : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hJ : IsComponentOf J ⊤) (hJL : J ≠ barM M L) :
    barM M (pCoreOf 2 H) ≤ Subgroup.centralizer (J : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨J', hJ', hbar⟩ := exists_isTwoPrimeComponent hJ
  by_cases hJS : J' ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)
  · have hT : IsPGroup 2 (barM M (pCoreOf 2 H)) :=
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_subtype).map _
    have hn : J ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      hbar ▸ barM_le_normalizer_barM hJS
    have hc := commutator_eq_bot_of_le_normalizer hJ hT hn
    rw [Subgroup.commutator_comm] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  · exact absurd (hbar ▸ hL J' ⟨hJ', hJS⟩) hJL

theorem D1Sp62Data.blockCentralizer_le_primeCore (h : D1Sp62Data P M H R V)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hL : Sp62BlockShape M H R L) :
    blockCentralizer M L ≤ GLBPrimeCore 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := h.surv.ph3
  obtain ⟨-, huniq, hLn, hRL, hO3, -⟩ := hL
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Cb := Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have : (barM M L).Normal := hLn
  have hCS : Cb ≤ Subgroup.centralizer (barM M (pCoreOf 2 H) : Set _) :=
    Sp62Block.centralizer_le_centralizer_of_component (pCore_quotient_pCore_eq_bot' 2)
      (((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_subtype).map _)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (h3.oddCore_le_centralizer h84 hD2)
      (fun J hJ hJL => Sp62Block.le_centralizer_component huniq hJ hJL)
  have hCK : blockCentralizer M L ≤ H ⊓ M :=
    h3.preimage_le_inf (h3.le_barM_inf_of_le_centralizer hCS)
  have hCn : H ⊓ M ≤ Subgroup.normalizer (blockCentralizer M L : Set G) :=
    inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.AGLEmbedding.blockCentralizer_le M L)).mp (normal_preimage_subgroupOf Cb))
  rcases h.surv.normal_dichotomy _ hCK hCn with h1 | hRC
  · exact h1
  exfalso
  have hR3 : IsPGroup 3 R := h3.isPGroup_R
  have hRne : R ≠ ⊥ := h.surv.ne_bot
  have h3R : 3 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR3
    rcases k with _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq R (by simpa using hk)) hRne
    · rw [hk, pow_succ]; exact dvd_mul_left 3 _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3R
  have hxM : (x : G) ∈ M := h3.le_M x.2
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨xb, hxb⟩ : ∃ xb, xb = mk ⟨x, hxM⟩ := ⟨_, rfl⟩
  have hxbo : orderOf xb = 3 := by
    have hdvd : orderOf xb ∣ 3 := by
      rw [← hxo, ← Subgroup.orderOf_mk (x : G) hxM, hxb]
      exact orderOf_map_dvd _ _
    rcases (Nat.prime_three.eq_one_or_self_of_dvd _ hdvd) with h1 | h1
    · exfalso
      have hx1 : xb = 1 := orderOf_eq_one_iff.mp h1
      have hxQ : (x : G) ∈ pCoreOf 2 M := coe_mem_pCoreOf_two_of_mk_eq_one _ (hxb ▸ hx1)
      obtain ⟨k, hk⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
        ⟨(x : G), hxQ⟩
      have hk' : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h32 : 3 ∣ 2 ^ k := hxo ▸ orderOf_dvd_of_pow_eq_one hk'
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32) (by norm_num)
    · exact h1
  have hxR' : (⟨(x : G), hxM⟩ : M) ∈ R.subgroupOf M := Subgroup.mem_subgroupOf.mpr x.2
  have hxL : xb ∈ barM M L := by
    rw [hxb]; exact hRL (Subgroup.mem_map_of_mem mk hxR')
  have hxC : xb ∈ Cb := by
    rw [hxb]
    exact (mem_blockCentralizer_iff (M := M) (L := L) ⟨(x : G), hxM⟩).mp (hRC x.2)
  have hzZ : (⟨xb, hxL⟩ : ↥(barM M L)) ∈ Subgroup.center ↥(barM M L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
  have hzo : orderOf (⟨xb, hxL⟩ : ↥(barM M L)) = 3 := by
    rw [← Subgroup.orderOf_coe]; exact hxbo
  have hdvd := (Subgroup.center ↥(barM M L)).orderOf_dvd_natCard hzZ
  rw [hzo] at hdvd
  exact not_dvd_card_center_of_normal hO3 hdvd

end Block

end CFSG.AGLEmbedding
