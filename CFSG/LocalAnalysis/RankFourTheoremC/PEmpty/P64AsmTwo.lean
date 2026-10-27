module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoZ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmThree
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmRank1

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup

namespace P64Asm

theorem exists_conj_of_map_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (O : Subgroup G) [O.Normal] (hO : Nat.Coprime p (Nat.card O)) {K₁ K₂ : Subgroup G}
    (h₁ : IsPGroup p K₁) (h₂ : IsPGroup p K₂)
    (h : K₁.map (QuotientGroup.mk' O) = K₂.map (QuotientGroup.mk' O)) :
    ∃ c : G, c ∈ K₂ ⊔ O ∧ K₁.map (MulAut.conj c).toMonoidHom = K₂ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hK₁X : K₁ ≤ K₂ ⊔ O := by
    intro a ha
    have hmem : QuotientGroup.mk' O a ∈ K₂.map (QuotientGroup.mk' O) :=
      h ▸ Subgroup.mem_map_of_mem _ ha
    obtain ⟨b, hb, hba⟩ := hmem
    have hker : b⁻¹ * a ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' O (b⁻¹ * a) = 1
      rw [map_mul, map_inv, hba, inv_mul_cancel]
    have e : a = b * (b⁻¹ * a) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hb hker
  have hK₂X : K₂ ≤ K₂ ⊔ O := le_sup_left
  have hXmap : (K₂ ⊔ O).map (QuotientGroup.mk' O) = K₂.map (QuotientGroup.mk' O) := by
    rw [Subgroup.map_sup]
    have : O.map (QuotientGroup.mk' O) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, sup_bot_eq]
  have hXcard : Nat.card (K₂ ⊔ O : Subgroup G) = Nat.card K₂ * Nat.card O := by
    have h1 := Subgroup.relIndex_mul_card (H := (QuotientGroup.mk' O).ker) (K := K₂ ⊔ O)
    rw [Subgroup.relIndex_ker, QuotientGroup.ker_mk', inf_eq_left.mpr le_sup_right, hXmap,
      CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp O hO h₂] at h1
    exact h1.symm
  have hK₂'p : IsPGroup p (K₂.subgroupOf (K₂ ⊔ O)) := h₂.comap_subtype
  have hidx : ¬ p ∣ (K₂.subgroupOf (K₂ ⊔ O)).index := by
    have h2 : Nat.card (K₂.subgroupOf (K₂ ⊔ O)) = Nat.card K₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₂X).toEquiv
    have h3 := Subgroup.card_mul_index (K₂.subgroupOf (K₂ ⊔ O))
    rw [h2, hXcard] at h3
    have hpos : 0 < Nat.card K₂ := Nat.card_pos
    have h4 : (K₂.subgroupOf (K₂ ⊔ O)).index = Nat.card O := Nat.eq_of_mul_eq_mul_left hpos h3
    rw [h4]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hO
  set S₂ : Sylow p ↥(K₂ ⊔ O) := hK₂'p.toSylow hidx with hS₂
  have hK₁'p : IsPGroup p (K₁.subgroupOf (K₂ ⊔ O)) := h₁.comap_subtype
  obtain ⟨S₁, hS₁⟩ := hK₁'p.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(K₂ ⊔ O) S₂ S₁
  have hle : ∀ k ∈ K₁, (c : G)⁻¹ * k * c ∈ K₂ := by
    intro k hk
    have hmem : (⟨k, hK₁X hk⟩ : ↥(K₂ ⊔ O)) ∈
        ((c • S₂ : Sylow p ↥(K₂ ⊔ O)) : Subgroup ↥(K₂ ⊔ O)) := by
      rw [hc]
      exact hS₁ hk
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
    have hmem' : (c : G)⁻¹ * k * c ∈ K₂ := by
      have := hmem
      simpa [hS₂, MulAut.smul_def, MulAut.conj_apply, Subgroup.mem_subgroupOf] using this
    exact hmem'
  have hle' : K₁.map (MulAut.conj (c : G)⁻¹).toMonoidHom ≤ K₂ := by
    rintro _ ⟨k, hk, rfl⟩
    have := hle k hk
    simpa [MulAut.conj_apply] using this
  have hcard : Nat.card K₂ ≤ Nat.card (K₁.map (MulAut.conj (c : G)⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (c : G)⁻¹).injective,
      ← CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp O hO h₁, h,
      CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp O hO h₂]
  exact ⟨(c : G)⁻¹, (K₂ ⊔ O).inv_mem c.2, Subgroup.eq_of_le_of_card_ge hle' hcard⟩

variable {A : Type} [Group A] [Finite A] {p : ℕ}

theorem XBar.not_conj (hp : p.Prime) {X B U : Subgroup A} (hBX : B ≤ X) (hUX : U ≤ X)
    (hBp : IsPGroup p B) (hUp : IsPGroup p U)
    (hBU : ∀ g ∈ X, B.map (MulAut.conj g).toMonoidHom ≠ U) (g : XBar p X) :
    ((B.subgroupOf X).map (XBar.mk p X)).map (MulAut.conj g).toMonoidHom ≠
      (U.subgroupOf X).map (XBar.mk p X) := by
  intro h
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hB'p : IsPGroup p (B.subgroupOf X) := hBp.comap_subtype
  have hU'p : IsPGroup p (U.subgroupOf X) := hUp.comap_subtype
  have hK₁p : IsPGroup p ((B.subgroupOf X).map (MulAut.conj g₀).toMonoidHom) := hB'p.map _
  have hmap : ((B.subgroupOf X).map (MulAut.conj g₀).toMonoidHom).map (XBar.mk p X) =
      (U.subgroupOf X).map (XBar.mk p X) := by
    rw [← h, Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨c, -, hc⟩ := exists_conj_of_map_eq hp (primeComplementCore (G := ↥X) p)
    (XBar.coprime p X) hK₁p hU'p hmap
  rw [map_conj_map_conj] at hc
  apply hBU ((c * g₀ : ↥X) : A) (c * g₀).2
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : (⟨b, hBX hb⟩ : ↥X) ∈ B.subgroupOf X := hb
    have : (MulAut.conj (c * g₀)).toMonoidHom ⟨b, hBX hb⟩ ∈ U.subgroupOf X := by
      rw [← hc]
      exact Subgroup.mem_map_of_mem _ hb'
    exact this
  · intro hy
    have hy' : (⟨y, hUX hy⟩ : ↥X) ∈ U.subgroupOf X := hy
    rw [← hc] at hy'
    obtain ⟨b', hb', hb'y⟩ := hy'
    exact ⟨(b' : A), hb', congrArg Subtype.val hb'y⟩

theorem XBar.weak_closed (hp : p.Prime) {X Q B : Subgroup A} (hQX : Q ≤ X) (hQp : IsPGroup p Q)
    (hBQ : B ≤ Q) (hBel : IsElemAbelian p B)
    (hw : ∀ w ∈ Q, orderOf w = p → (∀ q ∈ Q, q * w = w * q) → ∀ g ∈ X, g * w * g⁻¹ ∈ B →
      g * w * g⁻¹ ∈ zpowers w)
    (Qb : Sylow p (XBar p X))
    (hQb : (Qb : Subgroup (XBar p X)) = (Q.subgroupOf X).map (XBar.mk p X)) :
    ∀ w ∈ (Qb : Subgroup (XBar p X)), orderOf w = p →
      (∀ q ∈ (Qb : Subgroup (XBar p X)), q * w = w * q) → ∀ g : XBar p X,
        g * w * g⁻¹ ∈ (B.subgroupOf X).map (XBar.mk p X) → g * w * g⁻¹ ∈ zpowers w := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro w hwQ hwo hwc g hg
  have hQ'p : IsPGroup p (Q.subgroupOf X) := hQp.comap_subtype
  have hinj := injOn_mk_of_isPGroup hp (primeComplementCore (G := ↥X) p) (XBar.coprime p X) hQ'p
  have hB'Q' : B.subgroupOf X ≤ Q.subgroupOf X := fun b hb => hBQ hb
  rw [hQb] at hwQ
  obtain ⟨w', hw'Q', rfl⟩ := hwQ
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hw'p : w' ^ p = 1 := by
    have h1 : XBar.mk p X (w' ^ p) = 1 := by
      rw [map_pow]
      have := pow_orderOf_eq_one (XBar.mk p X w')
      rwa [hwo] at this
    exact hinj (Subgroup.pow_mem _ hw'Q' p) (one_mem _) (by rw [h1, map_one])
  have hw'1 : w' ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hwo
    exact hp.one_lt.ne hwo
  have hw'o : orderOf w' = p := orderOf_eq_prime hw'p hw'1
  have hAo : orderOf (w' : A) = p := by
    rw [Subgroup.orderOf_coe, hw'o]
  have hAc : ∀ q ∈ Q, q * (w' : A) = (w' : A) * q := by
    intro q hq
    have hq' : (⟨q, hQX hq⟩ : ↥X) ∈ Q.subgroupOf X := hq
    have h1 := hwc (XBar.mk p X ⟨q, hQX hq⟩) (by
      rw [hQb]
      exact Subgroup.mem_map_of_mem _ hq')
    have h2 : (⟨q, hQX hq⟩ : ↥X) * w' = w' * ⟨q, hQX hq⟩ :=
      hinj (Q.subgroupOf X |>.mul_mem hq' hw'Q') (Q.subgroupOf X |>.mul_mem hw'Q' hq')
        (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  have hw'A : (w' : A) ∈ Q := hw'Q'
  obtain ⟨b', hb'B, hb'v⟩ := hg
  obtain ⟨v, hvdef⟩ : ∃ v : ↥X, v = g₀ * w' * g₀⁻¹ := ⟨_, rfl⟩
  have hπv : XBar.mk p X v =
      XBar.mk p X g₀ * XBar.mk p X w' * (XBar.mk p X g₀)⁻¹ := by
    rw [hvdef, map_mul, map_mul, map_inv]
  have hb'v' : XBar.mk p X b' = XBar.mk p X v := hb'v.trans hπv.symm
  have hvp : v ^ p = 1 := by
    rw [hvdef, conj_pow, hw'p]
    simp
  have hb'p : b' ^ p = 1 := by
    apply Subtype.ext
    simpa using hBel.2 (b' : A) hb'B
  have hK₁p : IsPGroup p (zpowers v) :=
    CFSG.Open.IsElemAbelian.isPGroup (SU1.isElemAbelian_zpowers hvp)
  have hK₂p : IsPGroup p (zpowers b') :=
    CFSG.Open.IsElemAbelian.isPGroup (SU1.isElemAbelian_zpowers hb'p)
  have hmapz : (zpowers v).map (XBar.mk p X) = (zpowers b').map (XBar.mk p X) := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, hb'v']
  obtain ⟨c, hcmem, hc⟩ := exists_conj_of_map_eq hp (primeComplementCore (G := ↥X) p)
    (XBar.coprime p X) hK₁p hK₂p hmapz
  have hcv : c * v * c⁻¹ ∈ zpowers b' := by
    rw [← hc]
    exact ⟨v, mem_zpowers v, by simp⟩
  have hcB : ((c * g₀ : ↥X) : A) * (w' : A) * ((c * g₀ : ↥X) : A)⁻¹ ∈ B := by
    have h1 : c * v * c⁻¹ ∈ B.subgroupOf X := (zpowers_le.mpr hb'B) hcv
    have h2 : (((c * v * c⁻¹ : ↥X)) : A) ∈ B := h1
    have e : (((c * v * c⁻¹ : ↥X)) : A) =
        ((c * g₀ : ↥X) : A) * (w' : A) * ((c * g₀ : ↥X) : A)⁻¹ := by
      rw [hvdef]
      simp [mul_assoc]
    rwa [e] at h2
  have hz := hw (w' : A) hw'A hAo hAc ((c * g₀ : ↥X) : A) (c * g₀).2 hcB
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
  have hk' : w' ^ k = c * v * c⁻¹ := by
    apply Subtype.ext
    rw [hvdef]
    simpa [mul_assoc] using hk
  have hπc : XBar.mk p X c ∈ zpowers (XBar.mk p X v) := by
    obtain ⟨x, hx, o, ho, hxo⟩ := Subgroup.mem_sup_of_normal_right.mp hcmem
    have h1 : XBar.mk p X o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    have h2 : XBar.mk p X c = XBar.mk p X x := by
      rw [← hxo, map_mul, h1, mul_one]
    rw [h2]
    have h3 : XBar.mk p X x ∈ (zpowers b').map (XBar.mk p X) := Subgroup.mem_map_of_mem _ hx
    rw [← hmapz, MonoidHom.map_zpowers] at h3
    exact h3
  have hcomm : XBar.mk p X c * XBar.mk p X v = XBar.mk p X v * XBar.mk p X c := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hπc
    rw [← hn]
    exact (Commute.zpow_self (XBar.mk p X v) n).eq
  have h1 := congrArg (XBar.mk p X) hk'
  rw [map_zpow, map_mul, map_mul, map_inv] at h1
  have h2 : XBar.mk p X c * XBar.mk p X v * (XBar.mk p X c)⁻¹ = XBar.mk p X v := by
    rw [hcomm]
    group
  rw [h2] at h1
  have h3 : XBar.mk p X g₀ * XBar.mk p X w' * (XBar.mk p X g₀)⁻¹ ∈ zpowers (XBar.mk p X w') := by
    rw [← hπv]
    exact ⟨k, h1⟩
  exact h3

theorem XBar.cyclic_center (hp : p.Prime) {X Q : Subgroup A} (hQX : Q ≤ X) (hQp : IsPGroup p Q)
    (hcyc : IsCyclic (center ↥Q)) (Qb : Sylow p (XBar p X))
    (hQb : (Qb : Subgroup (XBar p X)) = (Q.subgroupOf X).map (XBar.mk p X)) :
    IsCyclic (center ↥(Qb : Subgroup (XBar p X))) := by
  have hQ'p : IsPGroup p (Q.subgroupOf X) := hQp.comap_subtype
  have hinj := injOn_mk_of_isPGroup hp (primeComplementCore (G := ↥X) p) (XBar.coprime p X) hQ'p
  have hbij : Function.Bijective ((XBar.mk p X).subgroupMap (Q.subgroupOf X)) :=
    ⟨fun x y hxy => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy)),
      (XBar.mk p X).subgroupMap_surjective _⟩
  let e₂ : ↥(Q.subgroupOf X) ≃* ↥((Q.subgroupOf X).map (XBar.mk p X)) :=
    MulEquiv.ofBijective _ hbij
  let e : ↥Q ≃* ↥(Qb : Subgroup (XBar p X)) :=
    ((Subgroup.subgroupOfEquivOfLe hQX).symm.trans e₂).trans (MulEquiv.subgroupCongr hQb.symm)
  haveI := hcyc
  exact isCyclic_of_surjective (Subgroup.centerCongr e).toMonoidHom
    (Subgroup.centerCongr e).surjective

theorem XBar.rank_top (hp : p.Prime) {X : Subgroup A} (hX : Open.pRank p X ≤ 2) :
    Open.pRank p (⊤ : Subgroup (XBar p X)) ≤ 2 := by
  have hker : ¬ p ∣ Nat.card (XBar.mk p X).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (XBar.coprime p X)
  have h1 := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp (XBar.mk p X) hker ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  have h2 : Open.pRank p (⊤ : Subgroup ↥X) = Open.pRank p X := by
    rw [← pRank_map_subtype hp.one_lt, Subgroup.map_top, Subgroup.range_subtype]
  exact h1.trans (h2 ▸ hX)

theorem XBar.normalizer_map {X H W : Subgroup A} (hHW : H ≤ normalizer (W : Set A)) :
    (H.subgroupOf X).map (XBar.mk p X) ≤
      normalizer (((W.subgroupOf X).map (XBar.mk p X) : Subgroup (XBar p X)) :
        Set (XBar p X)) := by
  refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map _)
  intro h hh
  rw [mem_normalizer_iff]
  intro w
  exact (mem_normalizer_iff.mp (hHW hh)) (w : A)

theorem XBar.coprime_map {X W : Subgroup A} (hWX : W ≤ X)
    (hcop : Nat.Coprime (Nat.card W) (2 * p)) :
    Nat.Coprime (Nat.card ((W.subgroupOf X).map (XBar.mk p X))) (2 * p) := by
  have hdvd : Nat.card ((W.subgroupOf X).map (XBar.mk p X)) ∣ Nat.card (W.subgroupOf X) :=
    Subgroup.card_map_dvd _ _
  have hW'c : Nat.card (W.subgroupOf X) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv
  rw [hW'c] at hdvd
  exact Nat.Coprime.coprime_dvd_left hdvd hcop

theorem XBar.le_of_map_eq_bot {X W : Subgroup A} (hWX : W ≤ X)
    (h : (W.subgroupOf X).map (XBar.mk p X) = ⊥) : W ≤ rankThreePrimeCore p X := by
  intro w hw
  have hwX : w ∈ X := hWX hw
  have hmem : XBar.mk p X ⟨w, hwX⟩ ∈ (W.subgroupOf X).map (XBar.mk p X) :=
    Subgroup.mem_map_of_mem _ (show (⟨w, hwX⟩ : ↥X) ∈ W.subgroupOf X from hw)
  rw [h, Subgroup.mem_bot] at hmem
  have hwO : (⟨w, hwX⟩ : ↥X) ∈ primeComplementCore (G := ↥X) p :=
    (QuotientGroup.eq_one_iff _).mp hmem
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.rankThreePrimeCore_eq_map_primeComplementCore]
  exact ⟨_, hwO, rfl⟩

end P64Asm

theorem kFactP65RankTwo_of_kdata (hI713 : GL83.I_7_13_1) (hChevP : KDI278ChevP)
    (hL3 : KDI278L3) (hChevQ : KDI278ChevQ) (hSpor : KDI278Spor) (hSporB : KDI278SporB)
    (hSporC : KDI278SporC) (hI204 : KDL64I204U3) : KFactP65RankTwo := by
  intro A _ _ p X Q B U hp hp5 hX hrk hQX hQp hQs hZc hBQ hBel hBc hUQ hUel hUc hBU hw
    ⟨Y, hYX, hYne, hΓU, hΓ2⟩ W hWX hBUW hcop
  haveI : Fact p.Prime := ⟨hp⟩
  have hBX : B ≤ X := hBQ.trans hQX
  have hUX : U ≤ X := hUQ.trans hQX
  have hXY : ¬ X ≤ Y := fun h => hYne (le_antisymm hYX h)
  have hOY : rankThreePrimeCore p X ≤ Y :=
    P64Free.rankThreePrimeCore_le_of_gammaOne_plane hp hUX hUel hUc hΓU
  have hQ'p : IsPGroup p (Q.subgroupOf X) := hQp.comap_subtype
  obtain ⟨Qb, hQb⟩ := P64Asm.XBar.exists_sylow hQ'p hQs
  have hBpl := P64Asm.XBar.plane hp hQX hQp hBQ hBel hBc
  have hUpl := P64Asm.XBar.plane hp hQX hQp hUQ hUel hUc
  have hB'p : IsPGroup p (B.subgroupOf X) := hQ'p.to_le (fun b hb => hBQ hb)
  have hU'p : IsPGroup p (U.subgroupOf X) := hQ'p.to_le (fun u hu => hUQ hu)
  have hZ := P64Asm.two_Z (kdI278Rank1_of_i713 hI713) kdI278Alt_holds hChevP kdI278L2p2_holds hL3
    hChevQ hSpor hSporB hSporC hI204 hp hp5
    (hX.quotient _) (primeComplementCore_quotient_eq_bot p) Qb
    (P64Asm.XBar.rank_top hp hrk.le)
    (P64Asm.XBar.cyclic_center hp hQX hQp hZc Qb hQb)
    ((B.subgroupOf X).map (P64Asm.XBar.mk p X)) ((U.subgroupOf X).map (P64Asm.XBar.mk p X))
    (by rw [hQb]; exact hBpl.1) hBpl.2.1 hBpl.2.2 (by rw [hQb]; exact hUpl.1) hUpl.2.1 hUpl.2.2
    (P64Asm.XBar.not_conj hp hBX hUX (hQp.to_le hBQ) (hQp.to_le hUQ) hBU)
    (P64Asm.XBar.weak_closed hp hQX hQp hBQ hBel hw Qb hQb)
    ((Y.subgroupOf X).map (P64Asm.XBar.mk p X)) (P64Asm.XBar.not_top_le hOY hXY)
    (fun S hS hk => P64Asm.normalizer_le_map_of_gamma hp (primeComplementCore (G := ↥X) p)
      (P64Asm.XBar.coprime p X) hU'p (k := 1)
      (fun S' hS'U hS'1 => P64Asm.normalizer_subgroupOf_le S' (hΓU _ (by
        rintro _ ⟨s, hs, rfl⟩
        exact hS'U hs) (by rw [pRank_map_subtype hp.one_lt]; exact hS'1))) hS hk)
    (fun S hS hk => P64Asm.XBar.gamma2 hp hQ'p hΓ2 (by rw [← hQb]; exact hS) hk)
  have hBW : B ≤ normalizer (W : Set A) := le_sup_left.trans hBUW
  have hUW : U ≤ normalizer (W : Set A) := le_sup_right.trans hBUW
  exact P64Asm.XBar.le_of_map_eq_bot hWX
    (hZ _ (sup_le (P64Asm.XBar.normalizer_map hBW) (P64Asm.XBar.normalizer_map hUW))
      (P64Asm.XBar.coprime_map hWX hcop))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
