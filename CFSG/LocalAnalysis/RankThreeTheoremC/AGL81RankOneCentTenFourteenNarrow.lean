module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneSylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

@[expose] noncomputable def narrowGamma (p : ℕ) {K : Type*} [Group K] [Finite K]
    (T : Subgroup K) : Subgroup K :=
  (⨆ (A : Subgroup K) (_ : A ≤ T ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2),
      Subgroup.normalizer (A : Set K)) ⊔
  ⨆ (x : K) (_ : x ∈ T ∧ orderOf x = p ∧
      2 ≤ Open.pRank p (T ⊓ Subgroup.centralizer ({x} : Set K))),
    Subgroup.centralizer ({x} : Set K)

section Gamma

variable {p : ℕ} {K : Type*} [Group K] [Finite K] {T : Subgroup K}

theorem normalizer_le_narrowGamma {A : Subgroup K} (hAT : A ≤ T) (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) : Subgroup.normalizer (A : Set K) ≤ narrowGamma p T :=
  le_sup_of_le_left (le_iSup₂_of_le A ⟨hAT, hA, hAc⟩ le_rfl)

theorem centralizer_le_narrowGamma {x : K} (hx : x ∈ T) (hxo : orderOf x = p)
    (h2 : 2 ≤ Open.pRank p (T ⊓ Subgroup.centralizer ({x} : Set K))) :
    Subgroup.centralizer ({x} : Set K) ≤ narrowGamma p T :=
  le_sup_of_le_right (le_iSup₂_of_le x ⟨hx, hxo, h2⟩ le_rfl)

end Gamma

@[expose] def KFactTenFourteenNarrowGamma : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K), p.Prime → p ≠ 2 →
    (∃ i : TauCeti.CFSGIndex, IsNineThreeIndex p i ∧ Nonempty (K ≃* i.Group)) →
    Subgroup.center K = ⊥ → Open.pRank p (T : Subgroup K) ≤ 2 → narrowGamma p (T : Subgroup K) ≠ ⊤ →
    TenFourteenOneGroup p K

theorem isElemAbelian_map {p : ℕ} {X Z : Type*} [Group X] [Group Z] (f : X →* Z)
    {E : Subgroup X} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  obtain ⟨hc, hpow⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    change (a : Z) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
  · obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_pow, hpow y' hy', map_one]

theorem isElemAbelian_zpowers {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X] {x : X}
    (hx : orderOf x = p) :
    IsElemAbelian p (Subgroup.zpowers x) ∧ Nat.card (Subgroup.zpowers x) = p := by
  have hx1 : x ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hx, h, orderOf_one])
  have hbot : IsElemAbelian p (⊥ : Subgroup X) :=
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun y hy => by
      rw [Subgroup.mem_bot.mp hy, one_pow]⟩
  have h := OtherCfg.isElemAbelian_sup_zpowers_gen hp hbot (hx ▸ pow_orderOf_eq_one x)
    (by rwa [Subgroup.mem_bot]) (fun e he => by rw [Subgroup.mem_bot.mp he, one_mul, mul_one])
  rw [bot_sup_eq, Subgroup.card_bot, one_mul] at h
  exact h

theorem exists_mem_sylow_inf_orderOf {p : ℕ} [hp : Fact p.Prime] {K : Type} [Group K]
    [Finite K] (T : Sylow p K) (N : Subgroup K) [N.Normal] {g : K} (hg : g ∈ N)
    (hgo : orderOf g = p) : ∃ x ∈ (T : Subgroup K) ⊓ N, orderOf x = p := by
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal T N
  have hdvd : p ∣ Nat.card N := by
    rw [← hgo, ← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_natCard _
  have hne : (T : Subgroup K) ⊓ N ≠ ⊥ := by
    rw [← hP]
    intro h
    exact P.ne_bot_of_dvd_card hdvd
      ((Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h)
  obtain ⟨z, hz, hzo, -⟩ := RankOneSylow.exists_central_orderOf T.isPGroup' hne
  exact ⟨z, hz, hzo⟩

theorem narrowGamma_eq_top_of_mulEquiv_prod {p : ℕ} (hp : p.Prime) {K D : Type} [Group K]
    [Finite K] [Group D] (e : K ≃* D × D) (hpD : p ∣ Nat.card D) (T : Sylow p K) :
    narrowGamma p (T : Subgroup K) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite D := Finite.of_injective (fun d => e.symm (d, 1))
    (fun a b h => by simpa using e.symm.injective h)
  set D₁ : Subgroup K := (Subgroup.prod ⊤ ⊥ : Subgroup (D × D)).comap e.toMonoidHom with hD₁
  set D₂ : Subgroup K := (Subgroup.prod ⊥ ⊤ : Subgroup (D × D)).comap e.toMonoidHom with hD₂
  have hm₁ : ∀ k, k ∈ D₁ ↔ (e k).2 = 1 := fun k => by
    simp [hD₁, Subgroup.mem_prod]
  have hm₂ : ∀ k, k ∈ D₂ ↔ (e k).1 = 1 := fun k => by
    simp [hD₂, Subgroup.mem_prod]
  haveI : D₁.Normal := Subgroup.normal_comap _
  haveI : D₂.Normal := Subgroup.normal_comap _
  have hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb => by
    apply e.injective
    rw [map_mul, map_mul]
    rw [hm₁] at ha
    rw [hm₂] at hb
    ext <;> simp [ha, hb]
  have hdisj : ∀ k ∈ D₁, k ∈ D₂ → k = 1 := fun k h₁ h₂ => by
    apply e.injective
    rw [hm₁] at h₁
    rw [hm₂] at h₂
    ext <;> simp [h₁, h₂]
  have htop : D₁ ⊔ D₂ = ⊤ := by
    refine eq_top_iff.mpr fun k _ => ?_
    have hk : k = e.symm ((e k).1, 1) * e.symm (1, (e k).2) := by
      apply e.injective
      simp
    rw [hk]
    exact Subgroup.mul_mem_sup ((hm₁ _).mpr (by simp)) ((hm₂ _).mpr (by simp))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpD
  have hgo : ∀ g : D × D, orderOf (e.symm g) = orderOf g := fun g => e.symm.orderOf_eq g
  obtain ⟨x₁, hx₁, hx₁o⟩ := exists_mem_sylow_inf_orderOf T D₁ (g := e.symm (y, 1))
    ((hm₁ _).mpr (by simp)) (by rw [hgo, Prod.orderOf_mk, orderOf_one, Nat.lcm_one_right, hy])
  obtain ⟨x₂, hx₂, hx₂o⟩ := exists_mem_sylow_inf_orderOf T D₂ (g := e.symm (1, y))
    ((hm₂ _).mpr (by simp)) (by rw [hgo, Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left, hy])
  have hrank : ∀ (u v : K), u ∈ (T : Subgroup K) → v ∈ (T : Subgroup K) → orderOf u = p →
      orderOf v = p → u * v = v * u → v ∉ Subgroup.zpowers u →
      2 ≤ Open.pRank p ((T : Subgroup K) ⊓ Subgroup.centralizer ({u} : Set K)) := by
    intro u v hu hv huo hvo huv hvu
    obtain ⟨hE, hEc⟩ := isElemAbelian_zpowers hp huo
    have hcomm' : ∀ w ∈ Subgroup.zpowers u, w * v = v * w := fun w hw => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact ((Commute.zpow_left huv n))
    obtain ⟨hF, hFc⟩ :=
      OtherCfg.isElemAbelian_sup_zpowers_gen hp hE (hvo ▸ pow_orderOf_eq_one v) hvu hcomm'
    refine CFSG.SectionRank.le_pRank hp.one_lt (sup_le ?_ ?_) hF (by rw [hFc, hEc, sq])
    · rw [Subgroup.zpowers_le]
      exact ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr huv.symm⟩
  have hx₁1 : x₁ ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hx₁o, h, orderOf_one])
  have hx₂1 : x₂ ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hx₂o, h, orderOf_one])
  have hz₁ : Subgroup.zpowers x₁ ≤ D₁ := (Subgroup.zpowers_le).mpr hx₁.2
  have hz₂ : Subgroup.zpowers x₂ ≤ D₂ := (Subgroup.zpowers_le).mpr hx₂.2
  have h12 := hcomm x₁ hx₁.2 x₂ hx₂.2
  have hC₂ : D₂ ≤ Subgroup.centralizer ({x₁} : Set K) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x₁ hx₁.2 k hk).symm
  have hC₁ : D₁ ≤ Subgroup.centralizer ({x₂} : Set K) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm k hk x₂ hx₂.2)
  have hΓ₂ : D₂ ≤ narrowGamma p (T : Subgroup K) := le_trans hC₂
    (centralizer_le_narrowGamma hx₁.1 hx₁o (hrank x₁ x₂ hx₁.1 hx₂.1 hx₁o hx₂o h12
      fun h => hx₂1 (hdisj x₂ (hz₁ h) hx₂.2)))
  have hΓ₁ : D₁ ≤ narrowGamma p (T : Subgroup K) := le_trans hC₁
    (centralizer_le_narrowGamma hx₂.1 hx₂o (hrank x₂ x₁ hx₂.1 hx₁.1 hx₂o hx₁o h12.symm
      fun h => hx₁1 (hdisj x₁ hx₁.2 (hz₂ h))))
  exact eq_top_iff.mpr (htop ▸ sup_le hΓ₁ hΓ₂)

theorem dvd_card_of_isCaseTwoGroup
    {p : ℕ} {L : Type} [Group L] (hL : IsCaseTwoGroup p L) : p ∣ Nat.card L := by
  rcases RankOneSylow.eq_three_or_five_of_isCaseTwoGroup hL with rfl | rfl
  · obtain ⟨e⟩ := KFactProofs.L28Local.nonempty_equiv_G8 hL
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.F6.L28Res.card_G8]
    norm_num
  · obtain ⟨⟨x, hv⟩, hd, ⟨e⟩⟩ := hL
    rcases hd with ⟨h53, -⟩ | ⟨-, hs⟩
    · omega
    · obtain rfl : x = TauCeti.LieTypeIndex.suzuki 2 := hs
      rw [(CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie (S := L) ⟨hv, ⟨e⟩⟩).card]
      norm_num

@[expose] def KFactTenFourteenNarrow : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (K Y₀ : Subgroup Y) (R : Sylow p Y) (c : Y),
    p.Prime → p ≠ 2 → K.Normal → NineThreeListGroup p ↥K → Subgroup.center ↥K = ⊥ →
    ¬ K ≤ Y₀ → c ∈ Subgroup.center Y → orderOf c = p → Open.pRank p (R : Subgroup Y) ≤ 3 →
    (∀ A : Subgroup Y, A ≤ R → IsElemAbelian p A → Nat.card A = p ^ 2 →
      3 ≤ Open.pRank p ((R : Subgroup Y) ⊓ Subgroup.centralizer (A : Set Y)) →
      Subgroup.normalizer (A : Set Y) ≤ Y₀) →
    TenFourteenOneGroup p ↥K

theorem kFactTenFourteenNarrow_of_gamma
    (hG : KFactTenFourteenNarrowGamma) :
    KFactTenFourteenNarrow := by
  intro p Y _ _ K Y₀ R c hp hp2 hKn hL hZ hKY hc hco hR3 hN
  haveI : Fact p.Prime := ⟨hp⟩
  have hcK : c ∉ K := fun hcK => by
    have h1 : (⟨c, hcK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hc g)
    rw [hZ, Subgroup.mem_bot] at h1
    have : c = 1 := congrArg Subtype.val h1
    exact hp.one_lt.ne' (by rw [← hco, this, orderOf_one])
  have hzc : Subgroup.zpowers c ≤ Subgroup.center Y := Subgroup.zpowers_le.mpr hc
  haveI : (Subgroup.zpowers c).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hzc hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hcR : c ∈ (R : Subgroup Y) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hco, pow_one])).le_sylow_of_normal R
      (Subgroup.mem_zpowers c)
  have hcp : c ^ p = 1 := hco ▸ pow_orderOf_eq_one c
  have hcc : ∀ y : Y, y * c = c * y := fun y => (Subgroup.mem_center_iff.mp hc y)
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hTR : ∀ B : Subgroup K, B ≤ T → B.map K.subtype ≤ R := fun B hB =>
    (Subgroup.map_mono hB).trans (hT ▸ inf_le_left)
  have hadj : ∀ {E : Subgroup K} {k : ℕ}, IsElemAbelian p E → Nat.card E = p ^ k →
      IsElemAbelian p (E.map K.subtype ⊔ Subgroup.zpowers c) ∧
        Nat.card ↥(E.map K.subtype ⊔ Subgroup.zpowers c) = p ^ (k + 1) := by
    intro E k hE hEc
    obtain ⟨h1, h2⟩ := OtherCfg.isElemAbelian_sup_zpowers_gen hp (isElemAbelian_map K.subtype hE)
      hcp (fun h => hcK (Subgroup.map_subtype_le E h)) (fun e _ => hcc e)
    refine ⟨h1, ?_⟩
    rw [h2, Subgroup.card_map_of_injective K.subtype_injective, hEc, pow_succ]
  have hrank : Open.pRank p (T : Subgroup K) ≤ 2 := by
    by_contra h3
    obtain ⟨E, hET, hE, hEc⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (H := (T : Subgroup K))
        (k := 3)
        (by omega)
    obtain ⟨hF, hFc⟩ := hadj hE hEc
    have := CFSG.SectionRank.le_pRank hp.one_lt
      (sup_le (hTR E hET) (Subgroup.zpowers_le.mpr hcR)) hF hFc
    omega
  have hΓ : narrowGamma p (T : Subgroup K) ≤ Y₀.comap K.subtype := by
    refine sup_le (iSup₂_le fun A ⟨hAT, hA, hAc⟩ => ?_) (iSup₂_le fun x ⟨hx, hxo, h2⟩ => ?_)
    · set Ah := A.map K.subtype
      have hAhc : Nat.card Ah = p ^ 2 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hAc]
      obtain ⟨hF, hFc⟩ := hadj hA hAc
      have hAhcomm : Ah ≤ Subgroup.centralizer (Ah : Set Y) := fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb =>
          congrArg Subtype.val ((isElemAbelian_map K.subtype hA).1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
      have h3 : 3 ≤ Open.pRank p ((R : Subgroup Y) ⊓ Subgroup.centralizer (Ah : Set Y)) :=
        CFSG.SectionRank.le_pRank hp.one_lt
          (sup_le (le_inf (hTR A hAT) hAhcomm) (Subgroup.zpowers_le.mpr
            ⟨hcR, Subgroup.center_le_centralizer _ hc⟩)) hF hFc
      have hNY := hN Ah (hTR A hAT) (isElemAbelian_map K.subtype hA) hAhc h3
      intro k hk
      exact hNY (Subgroup.le_normalizer_map K.subtype ⟨k, hk, rfl⟩)
    · set xh : Y := (x : Y)
      have hxhR : xh ∈ (R : Subgroup Y) := hTR _ (Subgroup.zpowers_le.mpr hx) ⟨x, by simp, rfl⟩
      have hxho : orderOf xh = p := by rw [Subgroup.orderOf_coe, hxo]
      obtain ⟨hX, hXc⟩ := isElemAbelian_zpowers hp hxho
      have hcx : c ∉ Subgroup.zpowers xh := fun h => hcK
        ((Subgroup.zpowers_le.mpr x.2) h)
      obtain ⟨hAh, hAhc⟩ := OtherCfg.isElemAbelian_sup_zpowers_gen hp hX hcp hcx
        (fun e _ => hcc e)
      set Ah := Subgroup.zpowers xh ⊔ Subgroup.zpowers c
      have hAhR : Ah ≤ R := sup_le (Subgroup.zpowers_le.mpr hxhR) (Subgroup.zpowers_le.mpr hcR)
      obtain ⟨E, hET, hE, hEc⟩ :=
        CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
          (H := (T : Subgroup K) ⊓ Subgroup.centralizer ({x} : Set K)) (k := 2) h2
      obtain ⟨hF, hFc⟩ := hadj hE hEc
      have hFx : E.map K.subtype ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer ({xh} : Set Y) := by
        refine sup_le ?_ (hzc.trans (Subgroup.center_le_centralizer _))
        rintro _ ⟨e, he, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hET he).2))
      have hFAh : E.map K.subtype ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer (Ah : Set Y) := by
        rw [← Subgroup.le_centralizer_iff]
        refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun f hf =>
          Subgroup.mem_centralizer_singleton_iff.mp (hFx hf)))
          (hzc.trans (Subgroup.center_le_centralizer _))
      have h3 : 3 ≤ Open.pRank p ((R : Subgroup Y) ⊓ Subgroup.centralizer (Ah : Set Y)) :=
        CFSG.SectionRank.le_pRank hp.one_lt
          (le_inf (sup_le (hTR E (hET.trans inf_le_left)) (Subgroup.zpowers_le.mpr hcR)) hFAh)
          hF hFc
      have hNY := hN Ah hAhR hAh (by rw [hAhc, hXc, sq]) h3
      intro k hk
      refine hNY (Subgroup.centralizer_le_normalizer _ ?_)
      have hAk : Ah ≤ Subgroup.centralizer ({(k : Y)} : Set Y) :=
        sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk)).symm))
          (hzc.trans (Subgroup.center_le_centralizer _))
      exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
        Subgroup.mem_centralizer_singleton_iff.mp (hAk hh)
  have hΓne : narrowGamma p (T : Subgroup K) ≠ ⊤ := fun htop =>
    hKY fun y hy => (htop ▸ hΓ) (Subgroup.mem_top (⟨y, hy⟩ : K))
  rcases hL with hL | ⟨d, hd, ⟨e⟩⟩
  · exact hG p K T hp hp2 hL hZ hrank hΓne
  · exact absurd (narrowGamma_eq_top_of_mulEquiv_prod hp e
      (dvd_card_of_isCaseTwoGroup ⟨d, hd, ⟨MulEquiv.refl _⟩⟩) T) hΓne

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
