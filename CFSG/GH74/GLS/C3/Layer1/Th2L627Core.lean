module

public import CFSG.GH74.GLS.C3.Layer1.Th2L627
public import CFSG.GH74.GLS.C3.Layer1.Th2L627E4
public import CFSG.GH74.GLS.C3.Layer1.Th2L627Z
public import CFSG.GH74.GLS.C3.Layer1.Th2L627Wr
public import CFSG.GH74.GLS.C3.Layer1.Th2L627Aut
public import CFSG.GH74.GLS.C3.Layer1.Th2L627Bal

public section

namespace CFSG.GH74.GLS.Th2.L627

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.IVK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_CxK_self {t : G} {J : Subgroup G} (hJC : J ≤ centralizer ({t} : Set G)) :
    t ∈ CxK t J := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl, C3.Layer1.Back.mem_centralizerSection_of_centralizes ?_ ?_⟩
  · intro k hk
    exact (mem_centralizer_singleton_iff.1 (hJC hk)).symm
  · unfold pPrimeCoreOf
    intro z hz
    obtain ⟨z', -, rfl⟩ := hz
    exact z'.2

theorem core_of_data
    (hG4 : pRank 2 G ≤ 4)
    {t u : G} {J : Subgroup G} (hmax : IsEStarUnbalMax t u J)
    (hJ5 : HasL2Model (kBar J) (fun q => q = 5)) (hJs : IsSimpleGroup (kBar J))
    (hnorm : ∀ c ∈ centralizer ({t} : Set G), ∀ k ∈ J, c * k * c⁻¹ ∈ J)
    (h8 : twoPartCard (centralizer ({t} : Set G)) = 8 * twoPartCard (CxK t J))
    (hout : ∀ hu : u ∈ centralizer ({t} : Set G), Back.actHom hnorm ⟨u, hu⟩ ∉ innAut (kBar J))
    (hAut : ∀ X : Subgroup (MulAut (kBar J)), Nat.card ↥X = 8 → IsD8 X)
    (hbound : ∀ A : Subgroup G, A ≤ NxK t J → CFSG.IsElementaryAbelian 2 ↥A →
      (∀ a ∈ A, a * u = u * a) → Nat.card ↥A ≤ 4 * Nat.card ↥(A ⊓ CxK t J))
    {t' : G} {J' : Subgroup G} (ht'2 : orderOf t' = 2) (hJ'C : J' ≤ centralizer ({t'} : Set G))
    (hJ'norm : ∀ c ∈ centralizer ({t'} : Set G), ∀ k ∈ J', c * k * c⁻¹ ∈ J')
    (hJ'5 : HasL2Model (kBar J') (fun q => q = 5)) (hJ's : IsSimpleGroup (kBar J'))
    (hgt : twoPartCard (centralizer ({t} : Set G)) < twoPartCard (centralizer ({t'} : Set G))) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  obtain ⟨hunb, B, hB, htB, huB⟩ := hmax.1
  have ht2 : orderOf t = 2 := hunb.1.1
  have hu2 : orderOf u = 2 := hunb.2.1
  have hJC : J ≤ C := hunb.1.2.1
  have huC : u ∈ C := hunb.2.2.1
  have hJcard : Nat.card (kBar J) = 60 := Th2.L625.card_of_l2_five hJ5
  have hJe : Even (Nat.card (kBar J)) := by rw [hJcard]; decide
  have hcen : CenterlessBar J :=
    centerlessBar_of_hasL2Model (fun q hq => by rw [hq]; decide) hJ5
  have hCN : ∀ g ∈ C, g ∈ normalizer (J : Set G) := fun g hg => U1a.mem_normalizer_of_norm hnorm hg
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hB.2.1
  have hB16 : 16 ≤ Nat.card ↥B := by
    have := Th2Sig6.two_pow_le_card hB.2.1 hB.2.2
    simpa using this
  have hBC : B ≤ C := fun b hb =>
    mem_centralizer_singleton_iff.2 (Th2Sig6.mul_comm_of_isElementaryAbelian hB.2.1 hb htB)
  have hBu : ∀ b ∈ B, b * u = u * b := fun b hb =>
    Th2Sig6.mul_comm_of_isElementaryAbelian hB.2.1 hb huB
  obtain ⟨T, hTsyl, hBT⟩ := exists_isSylowOf_ge (CFSG.IsElementaryAbelian.isPGroup 2 ↥B) hBC
  have hTp : IsPGroup 2 ↥T := hTsyl.isPGroup
  have hTC : T ≤ C := hTsyl.le
  obtain ⟨S, hSsyl, hTS⟩ := exists_isSylowOf_ge hTp (le_top : T ≤ ⊤)
  have hSp : IsPGroup 2 ↥S := hSsyl.isPGroup
  have hTcard : Nat.card ↥T = twoPartCard C := (Th2.twoPartCard_eq_card_of_isSylowOf hTsyl).symm
  have hScard : Nat.card ↥S = twoPartCard (⊤ : Subgroup G) :=
    (Th2.twoPartCard_eq_card_of_isSylowOf hSsyl).symm
  have hgtS : Nat.card ↥T < Nat.card ↥S := by
    rw [hTcard, hScard]
    exact lt_of_lt_of_le hgt (twoPartCard_mono le_top)
  have hTS' : T ≠ S := fun h => by rw [h] at hgtS; exact lt_irrefl _ hgtS
  obtain ⟨a, haS, haN, haT, ha2⟩ := exists_normalizer_sq_mem hSp hTS hTS'
  have hnormT : ∀ m ∈ T, ∀ l ∈ J, m * l * m⁻¹ ∈ J := fun m hm => hnorm m (hTC hm)
  set Q : Subgroup G := T ⊓ CxK t J with hQ
  have hT8 : Nat.card ↥T = 8 * Nat.card ↥Q := card_T_eq_eight_mul hnorm h8 hTsyl
  have hQT : Q ≤ T := inf_le_left
  have hQn : ∀ τ ∈ T, ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q := fun τ hτ q hq =>
    ⟨mul_mem (mul_mem hτ hq.1) (Subgroup.inv_mem _ hτ), CxK_conj_mem hnorm (hTC hτ) hq.2⟩
  have hD8 : IsD8 (Back.actHom hnormT).range := isD8_range_actHom hTC hnormT hAut hT8
  have htT : t ∈ T := hBT htB
  have huT : u ∈ T := hBT huB
  have hBN : B ≤ NxK t J := fun b hb => ⟨hBC hb, hCN b (hBC hb)⟩
  have hB0 : 4 ≤ Nat.card ↥(B ⊓ CxK t J) := by
    have := hbound B hBN hB.2.1 hBu
    omega
  have hB0Q : B ⊓ CxK t J ≤ Q := fun b hb => ⟨hBT hb.1, hb.2⟩
  have hQ4 : 4 ≤ Nat.card ↥Q := hB0.trans (Subgroup.card_le_of_le hB0Q)
  by_cases hdisj : Q ⊓ conjugate Q a = ⊥
  ·
    have haT' : ∀ τ ∈ T, a * τ * a⁻¹ ∈ T := fun τ hτ => (Subgroup.mem_normalizer_iff.1 haN τ).1 hτ
    have haT'' : ∀ τ ∈ T, a⁻¹ * τ * a ∈ T := fun τ hτ => by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem haN) τ).1 hτ
      simpa using this
    have hQaT : conjugate Q a ≤ T := by
      intro y hy
      have h1 : a * y * a⁻¹ ∈ T := hQT (mem_conjugate_iff'.1 hy)
      have := haT'' _ h1
      have e : a⁻¹ * (a * y * a⁻¹) * a = y := by group
      rwa [e] at this
    have hQan : ∀ τ ∈ T, ∀ y ∈ conjugate Q a, τ * y * τ⁻¹ ∈ conjugate Q a := by
      intro τ hτ y hy
      rw [mem_conjugate_iff'] at hy ⊢
      have h1 := hQn (a * τ * a⁻¹) (haT' τ hτ) _ hy
      have e : a * τ * a⁻¹ * (a * y * a⁻¹) * (a * τ * a⁻¹)⁻¹ = a * (τ * y * τ⁻¹) * a⁻¹ := by group
      rwa [e] at h1
    have hcomm : ∀ p ∈ Q, ∀ g ∈ conjugate Q a, p * g = g * p := fun p hp g hg =>
      comm_of_normal_disjoint hQT hQaT hQn hQan hdisj hp hg
    have hcardsup : Nat.card ↥(Q ⊔ conjugate Q a) = Nat.card ↥Q * Nat.card ↥Q := by
      rw [card_sup_of_commute_of_disjoint hcomm hdisj, card_conjugate']
    have hsupT : Nat.card ↥(Q ⊔ conjugate Q a) ≤ Nat.card ↥T :=
      Subgroup.card_le_of_le (sup_le hQT hQaT)
    have hQp : IsPGroup 2 ↥Q := hTp.to_le hQT
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have hk8 : Nat.card ↥Q ≤ 8 := by
      rw [hcardsup, hT8] at hsupT
      exact Nat.le_of_mul_le_mul_right (by linarith) (Nat.card_pos : 0 < Nat.card ↥Q)
    have hk' : Nat.card ↥Q = 4 ∨ Nat.card ↥Q = 8 := by
      rw [hk] at hk8 hQ4 ⊢
      have h1 : 2 ≤ k := by
        by_contra h
        push Not at h
        interval_cases k <;> omega
      have h2 : k ≤ 3 := by
        by_contra h
        push Not at h
        have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
        omega
      interval_cases k <;> simp
    have hCN' : C ≤ normalizer (J : Set G) := fun g hg => hCN g hg
    rcases hk' with hQ4' | hQ8'
    ·
      exfalso
      have hT32 : Nat.card ↥T = 32 := by rw [hT8, hQ4']
      have hPsyl : IsSylowOf 2 (T ⊓ J) J := hTsyl.inf_of_le_normalizer hJC hCN'
      have hPJ : 4 ≤ Nat.card ↥(T ⊓ J) := by
        rw [← Th2.twoPartCard_eq_card_of_isSylowOf hPsyl, Th2.L625.twoPartCard_of_l2_five hJ5]
      have hQeq : B ⊓ CxK t J = Q := Subgroup.eq_of_le_of_card_ge hB0Q (by omega)
      have hQB : ∀ q ∈ Q, q ∈ B := fun q hq => by
        have : q ∈ B ⊓ CxK t J := by rw [hQeq]; exact hq
        exact this.1
      exact e4_false hTp hcen hTC hnormT hD8 hT32 hQ4' hPJ huT
        (fun q hq q' hq' => Th2Sig6.mul_comm_of_isElementaryAbelian hBel (hQB q hq) (hQB q' hq'))
        (fun q hq => hBu q (hQB q hq)) (hout huC) haN hdisj
    ·
      have hT64 : Nat.card ↥T = 64 := by rw [hT8, hQ8']
      have hQa8 : Nat.card ↥(conjugate Q a) = 8 := by rw [card_conjugate', hQ8']
      have hD8a : IsD8 (conjugate Q a) := by
        refine isD8_of_inj_range (Back.actHom hnormT) hD8 hQaT hQa8 ?_
        intro n hn h1
        have hnT : n ∈ T := hQaT hn
        have hCx : n ∈ CxK t J := (actHom_eq_one_iff_mem hTC hnormT hnT).1 h1
        have : n ∈ Q ⊓ conjugate Q a := ⟨⟨hnT, hCx⟩, hn⟩
        rw [hdisj, Subgroup.mem_bot] at this
        exact this
      have hQD8 : IsD8 Q := by
        have := hD8a.conjugate a⁻¹
        rwa [conjugate_inv_conjugate'] at this
      have htQ : t ∈ Q := ⟨htT, mem_CxK_self hJC⟩
      have ht1 : t ≠ 1 := by
        intro h
        rw [h, orderOf_one] at ht2
        omega
      have htc : ∀ q ∈ Q, q * t = t * q := fun q hq => mem_centralizer_singleton_iff.1 (hTC hq.1)
      have hCS : ∀ s ∈ S, s * t = t * s → s ∈ T := by
        intro s hs hst
        have hSC : IsPGroup 2 ↥(S ⊓ C) := hSp.to_inf_left
        have heq : S ⊓ C = T := hTsyl.eq_of_le (le_inf hTS hTC) inf_le_right hSC
        have : s ∈ S ⊓ C := ⟨hs, mem_centralizer_singleton_iff.2 hst⟩
        rwa [heq] at this
      obtain ⟨-, hS2, hZ⟩ := wr_core (fun E hE => card_le_sixteen hG4 hE) hTp hSp hTS haS haN haT
        ha2 hT64.le hQT hQn hQD8 hdisj htQ ht1 htc hCS
      set C' : Subgroup G := centralizer ({t'} : Set G) with hC'
      have hC'S : twoPartCard C' ≤ Nat.card ↥S := by
        rw [hScard]
        exact twoPartCard_mono le_top
      obtain ⟨j, hj⟩ := hTp.exists_card_eq
      have hC'pow : twoPartCard C' = 2 ^ ((Nat.card ↥C').factorization 2) := rfl
      have hlt' : 2 ^ j < 2 ^ ((Nat.card ↥C').factorization 2) := by
        rw [← hj, ← hC'pow, hTcard]
        exact hgt
      have hle' : 2 ^ ((Nat.card ↥C').factorization 2) ≤ 2 ^ (j + 1) := by
        rw [← hC'pow, pow_succ, ← hj]
        calc twoPartCard C' ≤ Nat.card ↥S := hC'S
          _ = 2 * Nat.card ↥T := hS2
          _ = Nat.card ↥T * 2 := mul_comm _ _
      have hm : (Nat.card ↥C').factorization 2 = j + 1 := by
        have h1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt'
        have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle'
        omega
      have hC'eq : Nat.card ↥S = twoPartCard C' := by
        rw [hS2, hC'pow, hm, pow_succ, ← hj, mul_comm]
      have hzt' : IsPGroup 2 ↥(zpowers t') := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, ht'2]
        norm_num
      have hzC' : zpowers t' ≤ C' := zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
      obtain ⟨S', hS'syl, hzS'⟩ := exists_isSylowOf_ge hzt' hzC'
      have ht'S' : t' ∈ S' := hzS' (mem_zpowers t')
      have hS'card : Nat.card ↥S' = Nat.card ↥S := by
        rw [hC'eq, ← Th2.twoPartCard_eq_card_of_isSylowOf hS'syl]
      have hS'top : IsSylowOf 2 S' ⊤ :=
        isSylowOf_of_card le_top (by rw [hS'card]; exact hSsyl.card_eq)
      have hJ'card : Nat.card (kBar J') = 60 := Th2.L625.card_of_l2_five hJ'5
      obtain ⟨z, hzS', -, hz1, hzt, hzc⟩ :=
        exists_central_ne_of_isSylowOf ht'2 hJ'C hJ'norm hJ's hJ'card hS'syl ht'S'
      obtain ⟨k, -, hk⟩ := hSsyl.exists_mem_conj hS'top
      have hconj : ∀ y ∈ S', (∀ s ∈ S', s * y = y * s) →
          k⁻¹ * y * k ∈ S ∧ ∀ s ∈ S, s * (k⁻¹ * y * k) = (k⁻¹ * y * k) * s := by
        intro y hy hyc
        refine ⟨(hk y).1 hy, fun s hs => ?_⟩
        have hks : k * s * k⁻¹ ∈ S' := (hk _).2 (by
          have e : k⁻¹ * (k * s * k⁻¹) * k = s := by group
          rw [e]; exact hs)
        have := hyc _ hks
        calc s * (k⁻¹ * y * k) = k⁻¹ * ((k * s * k⁻¹) * y) * k := by group
          _ = k⁻¹ * (y * (k * s * k⁻¹)) * k := by rw [this]
          _ = (k⁻¹ * y * k) * s := by group
      have ht'1 : t' ≠ 1 := by
        intro h
        rw [h, orderOf_one] at ht'2
        omega
      have hS'c : ∀ s ∈ S', s * t' = t' * s := fun s hs =>
        mem_centralizer_singleton_iff.1 (hS'syl.le hs)
      have hne1 : ∀ y : G, y ≠ 1 → k⁻¹ * y * k ≠ 1 := by
        intro y hy h
        apply hy
        have : y = k * (k⁻¹ * y * k) * k⁻¹ := by group
        rw [this, h]
        group
      have h1 := hZ _ (hconj z hzS' hzc).1 (hconj z hzS' hzc).2 (hne1 z hz1)
      have h2 := hZ _ (hconj t' ht'S' hS'c).1 (hconj t' ht'S' hS'c).2 (hne1 t' ht'1)
      apply hzt
      have h3 : k⁻¹ * z * k = k⁻¹ * t' * k := h1.trans h2.symm
      exact mul_left_cancel (mul_right_cancel h3)
  ·
    have hHS : T ⊔ zpowers a ≤ S := sup_zpowers_le hTS haS
    have hHp : IsPGroup 2 ↥(T ⊔ zpowers a) := hSp.to_le hHS
    have hWn := inf_conj_normal haN ha2 hQn
    have hWH : Q ⊓ conjugate Q a ≤ T ⊔ zpowers a := inf_le_left.trans (hQT.trans le_sup_left)
    obtain ⟨v, hvW, hv2, hvc⟩ := exists_central_involution_of_normal hHp hWn hWH hdisj
    have hvCxK : v ∈ CxK t J := hvW.1.2
    have hvu : v * u = u * v := (hvc u (Subgroup.mem_sup_left huT)).symm
    have hv22 : v * v = 1 := by rw [← sq]; exact hv2 ▸ pow_orderOf_eq_one v
    have hvB : v ∈ B := by
      have hcomm : ∀ b ∈ B, ∀ y ∈ zpowers v, b * y = y * b := by
        intro b hb y hy
        rcases mem_zpowers_of_sq hv22 hy with rfl | rfl
        · simp
        · exact hvc b (Subgroup.mem_sup_left (hBT hb))
      have hel : CFSG.IsElementaryAbelian 2 ↥(B ⊔ zpowers v) :=
        C3.Layer1.Bk.isElementaryAbelian_sup_of_commute hB.2.1
          (isElementaryAbelian_zpowers_of_sq hv22) hcomm
      have hle16 := card_le_sixteen hG4 hel
      have heq : B = B ⊔ zpowers v := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
      rw [heq]
      exact Subgroup.mem_sup_right (mem_zpowers v)
    have hnb := not_balanced_of_commuting hunb hnorm hJs hJe hv2 hvCxK hvu
    obtain ⟨L, hL⟩ := exists_isUnbalancingTriple_of_not_le hv2 hu2 hvu hnb
    have hE : IsEStarUnbal v u L := ⟨hL, B, hB, hvB, huB⟩
    have hle : twoPartCard (centralizer ({v} : Set G)) ≤ twoPartCard C := hmax.2 v u L hE
    have hHC : T ⊔ zpowers a ≤ centralizer ({v} : Set G) :=
      fun h hh => mem_centralizer_singleton_iff.2 (hvc h hh)
    have h1 : Nat.card ↥(T ⊔ zpowers a) ≤ twoPartCard (centralizer ({v} : Set G)) :=
      card_le_twoPartCard hHp hHC
    have hne : T ≠ T ⊔ zpowers a := fun h => haT (by
      have : a ∈ T ⊔ zpowers a := Subgroup.mem_sup_right (mem_zpowers a)
      rwa [← h] at this)
    have h2 : 2 * Nat.card ↥T ≤ Nat.card ↥(T ⊔ zpowers a) := two_mul_card_le hHp le_sup_left hne
    have hpos : 0 < Nat.card ↥T := Nat.card_pos
    omega

end CFSG.GH74.GLS.Th2.L627

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2.L625 CFSG.GH74.GLS.C3.Layer1

theorem b_lemma627_core_proved

        (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hfm : ClassFM9) : B_lemma627_core := by
  intro G _ _ hG x y K hV hK5 hCx t u J hmax hterm hV2 t' u' J' hV2'
  have hlu : IsLocallyUnbalancing t u J := hmax.1.1.isLocallyUnbalancing
  have hdata := v2triple_data h102 hL34 hfm hG hV hK5 hV2
  have hdata' := v2triple_data h102 hL34 hfm hG hV hK5 hV2'
  obtain ⟨hJ5, -, hnorm, h8, -⟩ := hdata
  obtain ⟨hJ'5, -, hnorm', -, -⟩ := hdata'
  have hfive : IsFM9 5 := Th2Tstar.isFM9_five
  obtain ⟨hnotInn, -⟩ := Bk.ivk10_bridge IVK.Proofs2.b_ivk_10_2L hlu hfive hJ5
  refine not_lt.1 fun hgt => ?_
  exact Th2.L627.core_of_data hG.pRank_eq_four.le hmax hJ5 (C3.Layer1.Back.isSimpleGroup_of_hasL2Model hJ5) hnorm h8
    (fun hu h => hnotInn h) (Th2.L627.autD8_of_hasL2Model_five hJ5).2
    (fun A hAN hAel hyA => card_le_four_mul_inf_CxK hlu hfive hJ5 A hAN hAel hyA)
    hV2'.1.1.1 hV2'.1.1.2.1 hnorm' hJ'5 (C3.Layer1.Back.isSimpleGroup_of_hasL2Model hJ'5) hgt

end CFSG.GH74.GLS
