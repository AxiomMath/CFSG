module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuOddCore
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSzAut
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315SzR
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Setup

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def DempwolffOddCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SzMinCounter G L 1 →
    ∀ T₀ : Subgroup G, IsSylowOf 2 T₀ (centralizer (L : Set G)) → Nat.card T₀ = 4 →
      standardComponentOddCore (centralizer (L : Set G)) = ⊥

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCoreIn_eq_bot_of {K : Subgroup G} (h : standardComponentOddCore K = ⊥) :
    AS76b.oddCoreIn K = ⊥ := by
  have : CFSG.Assembly.oddCore K = standardComponentOddCore K := rfl
  rw [AS76b.oddCoreIn, this, h, Subgroup.map_bot]

omit [Finite G] in
theorem quotAutHom_mem_inner_of_mem {L : Subgroup G} {l : G} (hlL : l ∈ L) :
    quotAutHom L ⟨l, le_normalizer hlL⟩ ∈ inner (rankTwoQuot L) := by
  refine ⟨QuotientGroup.mk' (center L) ⟨l, hlL⟩, ?_⟩
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) q
  rw [quotAutHom_apply_mk, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  rfl

theorem isSylowOf_map_conj {p : ℕ} [Fact p.Prime] {P L : Subgroup G} (hP : IsSylowOf p P L)
    {g : G} (hg : g ∈ normalizer (L : Set G)) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) L := by
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hle, hp, hdvd⟩ := hP
  refine ⟨?_, hp.map _, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (mem_normalizer_iff.mp hg z).mp (hle hz)
  · have hcard : Nat.card (P.map (MulAut.conj g).toMonoidHom) = Nat.card P :=
      card_map_of_injective (MulAut.conj g).injective
    have h1 := relIndex_mul_card P L
    have h2 := relIndex_mul_card (P.map (MulAut.conj g).toMonoidHom) L
    rw [inf_eq_left.mpr hle] at h1
    have hle' : P.map (MulAut.conj g).toMonoidHom ≤ L := by
      rintro _ ⟨z, hz, rfl⟩
      exact (mem_normalizer_iff.mp hg z).mp (hle hz)
    rw [inf_eq_left.mpr hle', hcard] at h2
    have hpos : 0 < Nat.card P := Nat.card_pos
    have : (P.map (MulAut.conj g).toMonoidHom).relIndex L = P.relIndex L := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1, h2]
    rwa [this]

namespace SzMinCounter

variable {L T : Subgroup G}

theorem inf_centralizer_eq
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥) {e : G}
    (he : e ∈ T ⊓ centralizer (L : Set G)) (he1 : e ≠ 1) :
    centralizer (L : Set G) ⊓ centralizer ({e} : Set G) = T ⊓ centralizer (L : Set G) := by
  have hstd := hM.hyp.standard
  refine AS76b.inf_centralizer_eq_of_oddCoreIn_eq_bot hF.asc75Theorem4
    (AS76b.tightlyEmbedded_centralizer hstd) h3.isSylowOf_T₀ (h3.isElemAbelian_T₀ hF) h4
    (AS76b.asc08Lemma34 G L hM.hyp.hyp31).2 ?_ (oddCoreIn_eq_bot_of hO) he he1
  intro hn
  apply hM.hyp.not_normal
  rw [← normalizer_eq_top_iff, ← AS76b.normalizer_centralizer_eq hstd]
  exact normalizer_eq_top_iff.mpr hn

theorem center_eq_bot
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥) : center L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h3.T₀_ne_bot
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have hCK := hM.inf_centralizer_eq h3 hF h4 hO he he1'
  refine eq_bot_iff.mpr fun z hz => ?_
  have hzK : (z : G) ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)
  have hze : (z : G) ∈ centralizer ({e} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp he.2 z z.2)
  have hzT₀ : (z : G) ∈ T ⊓ centralizer (L : Set G) := by
    rw [← hCK]
    exact ⟨hzK, hze⟩
  have hP : IsPGroup 2 (T ⊓ centralizer (L : Set G) : Subgroup G) := h3.isSylowOf_T₀.isPGroup
  obtain ⟨k, hk⟩ := hP ⟨z, hzT₀⟩
  have hz2 : z ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hzodd : Odd (orderOf z) := hZ.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz)
  have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hz2
  have h1 : orderOf z = 1 :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hzodd)).eq_one_of_dvd hdvd
  rw [mem_bot]
  exact orderOf_eq_one_iff.mp h1

theorem quotAutHom_mem_inner
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥) (s : G)
    (hs : s ∈ normalizer (L : Set G)) (hsA : ∀ a ∈ gmsA L T, s * a = a * s) :
    quotAutHom L ⟨s, hs⟩ ∈ inner (rankTwoQuot L) := by
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  obtain ⟨hA₁card, -, -⟩ := hX.sylow h3
  have hZL := hM.center_eq_bot h3 hF hZ h4 hO
  have hA₁L : gmsA L T ≤ L := inf_le_left.trans inf_le_right
  set Ā := ((gmsA L T).subgroupOf L).map (QuotientGroup.mk' (center L)) with hĀ
  have hinj : Function.Injective (QuotientGroup.mk' (center L)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZL]
  have hcard : Nat.card Ā = 8 := by
    rw [hĀ, card_map_of_injective hinj, Nat.card_congr (subgroupOfEquivOfLe hA₁L).toEquiv,
      hA₁card]
    norm_num
  refine mem_inner_of_card_eight eS _ hcard ?_
  rintro _ ⟨⟨a, haL⟩, ha, rfl⟩
  rw [quotAutHom_apply_mk]
  congr 1
  apply Subtype.ext
  simp only [normalizerMonoidHom_apply_apply_coe]
  rw [hsA a (mem_subgroupOf.mp ha), mul_inv_cancel_right]

theorem isPGroup_inf_centralizer
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥) {a : G} (haL : a ∈ L)
    (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hZL := hM.center_eq_bot h3 hF hZ h4 hO
  set π := QuotientGroup.mk' (center L) with hπ
  have hinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk', hZL]
  have hπa : orderOf (π ⟨a, haL⟩) = 2 := by
    rw [orderOf_injective π hinj, Subgroup.orderOf_mk]
    exact orderOf_eq_prime ha2 ha1
  have hC := isPGroup_centralizer_of_sz_one eS hπa
  rintro ⟨x, hxL, hxa⟩
  obtain ⟨k, hk⟩ := hC ⟨π ⟨x, hxL⟩, by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hxa)⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : π (⟨x, hxL⟩ ^ 2 ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have h2 : (⟨x, hxL⟩ : L) ^ 2 ^ k = 1 := hinj (by rw [h1, map_one])
  simpa using congrArg Subtype.val h2

theorem centralizer_eq_sup_of_aut
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥)
    (hAut : ∀ (s : G) (hs : s ∈ normalizer (L : Set G)), (∀ a ∈ gmsA L T, s * a = a * s) →
      quotAutHom L ⟨s, hs⟩ ∈ inner (rankTwoQuot L))
    {e : G} (he : e ∈ T ⊓ centralizer (L : Set G)) (he1 : e ≠ 1) :
    centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  have hstd := hM.hyp.standard
  have hLp : commutator L = ⊤ := hstd.1.1
  have hRe : IsElemAbelian 2 T₀ := h3.isElemAbelian_T₀ hF
  have hCK : K ⊓ centralizer ({e} : Set G) = T₀ := hM.inf_centralizer_eq h3 hF h4 hO he he1
  have hNK : normalizer (K : Set G) = normalizer (L : Set G) :=
    AS76b.normalizer_centralizer_eq hstd
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  have h313 := h3.lemma313_of_sz_of_odd hF hZ hM.one_le eS
  obtain ⟨y, hy⟩ := hX.exists_isTorus h3
  have he2 : e ^ 2 = 1 := hRe.2 e he
  refine le_antisymm ?_ (sup_le (fun t ht => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hRe.1.is_comm.comm ⟨t, ht⟩ ⟨e, he⟩)))
    (Sec3.le_centralizer he))
  intro x hx
  have hxe : x * e = e * x := mem_centralizer_singleton_iff.mp hx
  have hc : Commute x e := hxe
  have hxN : x ∈ normalizer (L : Set G) := by
    rw [← hNK]
    have hzK : zpowers e ≤ K := zpowers_le.mpr he.2
    have hev : Even (Nat.card (zpowers e)) := by
      rw [Nat.card_zpowers, orderOf_eq_prime he2 he1]
      exact even_two
    refine AS76b.Lemma37.normalizer_le_of_le_of_even
      (AS76b.tightlyEmbedded_centralizer hstd) hzK hev ?_
    refine mem_normalizer_of_conj_mem_of_finite fun z hz => ?_
    obtain ⟨k, rfl⟩ := hz
    refine ⟨k, ?_⟩
    simp only
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  have hxK : x ∈ normalizer (K : Set G) := hNK ▸ hxN
  have hxT₀ : ∀ t ∈ T₀, x * t * x⁻¹ ∈ T₀ := by
    intro t ht
    rw [← hCK]
    have hte : t * e = e * t :=
      congrArg Subtype.val (hRe.1.is_comm.comm ⟨t, ht⟩ ⟨e, he⟩)
    have ht' : t ∈ K ⊓ centralizer ({e} : Set G) := by rw [hCK]; exact ht
    refine ⟨(mem_normalizer_iff.mp hxK t).mp ht'.1, mem_centralizer_singleton_iff.mpr ?_⟩
    have hxe' : x * e * x⁻¹ = e := by rw [hxe, mul_inv_cancel_right]
    calc x * t * x⁻¹ * e = x * t * x⁻¹ * (x * e * x⁻¹) := by rw [hxe']
      _ = x * (t * e) * x⁻¹ := by group
      _ = x * (e * t) * x⁻¹ := by rw [hte]
      _ = (x * e * x⁻¹) * (x * t * x⁻¹) := by group
      _ = e * (x * t * x⁻¹) := by rw [hxe']
  have hxe' : x * e * x⁻¹ = e := by rw [hxe, mul_inv_cancel_right]
  by_cases hin : quotAutHom L ⟨x, hxN⟩ ∈ inner (rankTwoQuot L)
  ·
    have hxLK := mem_sup_centralizer_of_quotAut_mem_inner hLp hxN hin
    obtain ⟨l, hl, k, hk, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer
      (le_normalizer.trans (AS76b.normalizer_centralizer_eq hstd).ge) hxLK
    have hkT₀ : k ∈ T₀ := by
      rw [← hCK]
      refine ⟨hk, mem_centralizer_singleton_iff.mpr ?_⟩
      have hle : l * e = e * l := mem_centralizer_iff.mp he.2 l hl
      have h1 : l * k * e = e * (l * k) := hxe
      calc k * e = l⁻¹ * (l * k * e) := by group
        _ = l⁻¹ * (e * (l * k)) := by rw [h1]
        _ = l⁻¹ * (e * l) * k := by group
        _ = l⁻¹ * (l * e) * k := by rw [hle]
        _ = e * k := by group
    exact mul_mem (mem_sup_right hl) (mem_sup_left hkT₀)
  · exfalso
    set Q := rankTwoQuot L with hQ
    have hOutodd : Odd (Nat.card (Outer Q)) := odd_card_outer_of_sz hM.one_le eS
    have hb1 : (QuotientGroup.mk (quotAutHom L ⟨x, hxN⟩) : Outer Q) ≠ 1 := fun h =>
      hin ((QuotientGroup.eq_one_iff _).mp h)
    have hb2 : (QuotientGroup.mk (quotAutHom L ⟨x, hxN⟩) : Outer Q) ^ 2 ≠ 1 := by
      intro h
      apply hb1
      have h1 : orderOf (QuotientGroup.mk (quotAutHom L ⟨x, hxN⟩) : Outer Q) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one h
      have h2 : orderOf (QuotientGroup.mk (quotAutHom L ⟨x, hxN⟩) : Outer Q) ∣
          Nat.card (Outer Q) := _root_.orderOf_dvd_natCard _
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hOutodd) h1 h2)
    have hx2 : ∀ t ∈ T₀, x ^ 2 * t = t * x ^ 2 := fun t ht => by
      have h := AS76b.sq_conj_eq_of_card_four hRe h4 he he1 hxT₀ hxe' ht
      calc x ^ 2 * t = x ^ 2 * t * (x ^ 2)⁻¹ * x ^ 2 := by group
        _ = t * x ^ 2 := by rw [h]
    have hx2N : x ^ 2 ∈ normalizer (L : Set G) := pow_mem hxN 2
    obtain ⟨k, hkL, hk⟩ := h3.isSylowOf_T₁.exists_mem_conj (isSylowOf_map_conj h3.isSylowOf_T₁ hx2N)
    set n := k⁻¹ * x ^ 2 with hn
    have hnT₁ : n ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      refine mem_normalizer_of_conj_mem_of_finite fun t ht => ?_
      have hmem : x ^ 2 * t * (x ^ 2)⁻¹ ∈ (T ⊓ L).map (MulAut.conj (x ^ 2)).toMonoidHom :=
        ⟨t, ht, rfl⟩
      have := (hk _).mp hmem
      rw [hn]
      convert this using 1
      group
    have hnT₀ : ∀ t ∈ T₀, n * t = t * n := by
      intro t ht
      have hkt : k⁻¹ * t = t * k⁻¹ := (mem_centralizer_iff.mp ht.2 _ (inv_mem hkL))
      calc n * t = k⁻¹ * (x ^ 2 * t) := by rw [hn, mul_assoc]
        _ = k⁻¹ * (t * x ^ 2) := by rw [hx2 t ht]
        _ = (k⁻¹ * t) * x ^ 2 := by group
        _ = (t * k⁻¹) * x ^ 2 := by rw [hkt]
        _ = t * n := by rw [hn]; group
    have hnA : n ∈ normalizer ((gmsA L T : Subgroup G) : Set G) :=
      mem_normalizer_inf hnT₁ (mem_normalizer_centralizer hnT₁)
    have hnV : n ∈ normalizer ((gmsV L T : Subgroup G) : Set G) :=
      mem_normalizer_sup hnA (centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun t ht => (hnT₀ t ht).symm))
    have hp : (2 ^ (2 * 1 + 1) - 1).Prime := by norm_num
    obtain ⟨j, hj⟩ := hy.exists_aut_eq_of_prime h313 hX h3 hF hp hnV hnT₀
    have hyL : y ∈ L := (mem_inf.mp hy.mem).1
    set s := y ^ j * n with hs
    have hsA : ∀ a ∈ gmsA L T, s * a = a * s := by
      intro a ha
      have h := hj a ha
      calc s * a = y ^ j * (n * a * n⁻¹) * n := by rw [hs]; group
        _ = y ^ j * ((y ^ j)⁻¹ * a * y ^ j) * n := by rw [h]
        _ = a * s := by rw [hs]; group
    have hyjN : y ^ j ∈ normalizer (L : Set G) := le_normalizer (pow_mem hyL j)
    have hkN : k⁻¹ ∈ normalizer (L : Set G) := le_normalizer (inv_mem hkL)
    have hsN : s ∈ normalizer (L : Set G) := mul_mem hyjN (mul_mem hkN hx2N)
    have hsin := hAut s hsN hsA
    have hdecomp : (⟨s, hsN⟩ : normalizer (L : Set G)) =
        ⟨y ^ j, hyjN⟩ * (⟨k⁻¹, hkN⟩ * ⟨x, hxN⟩ ^ 2) := Subtype.ext (by
      simp only [coe_mul, SubmonoidClass.coe_pow, hs, hn])
    have h1 : (QuotientGroup.mk (quotAutHom L ⟨y ^ j, hyjN⟩) : Outer Q) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (quotAutHom_mem_inner_of_mem (pow_mem hyL j))
    have h2 : (QuotientGroup.mk (quotAutHom L ⟨k⁻¹, hkN⟩) : Outer Q) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (quotAutHom_mem_inner_of_mem (inv_mem hkL))
    have h3' : (QuotientGroup.mk (quotAutHom L ⟨s, hsN⟩) : Outer Q) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hsin
    apply hb2
    rw [hdecomp, map_mul, map_mul, map_pow, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_pow, h1, h2, one_mul, one_mul] at h3'
    exact h3'

theorem centralizer_gmsV_eq_of_aut
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥)
    (hAut : ∀ (s : G) (hs : s ∈ normalizer (L : Set G)), (∀ a ∈ gmsA L T, s * a = a * s) →
      quotAutHom L ⟨s, hs⟩ ∈ inner (rankTwoQuot L))
    (hInv : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 → IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G)) :
    centralizer (gmsV L T : Set G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  have hTW : T = gmsW L T := h3.eq_sup_of_sz hM.one_le eS
  obtain ⟨hVcard, hVel, hVW, hVC, -⟩ := hX.vFacts h3 hF
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h3.T₀_ne_bot
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    have hxe : x ∈ centralizer ({e} : Set G) := mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hx e (mem_sup_right he)).symm
    rw [hM.centralizer_eq_sup_of_aut h3 hF hZ h4 hO hAut he he1'] at hxe
    obtain ⟨t, ht, l, hl, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer
      (inf_le_right.trans h3.centralizer_le_normalizer) hxe
    obtain ⟨hA₁card, -, -⟩ := hX.sylow h3
    have hA₁1 : gmsA L T ≠ ⊥ := by
      intro hb
      rw [hb, card_bot] at hA₁card
      have := hX.four_le
      omega
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA₁1
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have haL : a ∈ L := ha.1.2
    have ha2 : a ^ 2 = 1 := hVel.2 a (mem_sup_left ha)
    have hla : l * a = a * l := by
      have h1 : (t * l) * a = a * (t * l) :=
        (mem_centralizer_iff.mp hx a (mem_sup_left ha)).symm
      have h2 : t * a = a * t := (mem_centralizer_iff.mp ht.2 a haL).symm
      calc l * a = t⁻¹ * ((t * l) * a) := by group
        _ = t⁻¹ * (a * (t * l)) := by rw [h1]
        _ = t⁻¹ * (a * t) * l := by group
        _ = t⁻¹ * (t * a) * l := by rw [h2]
        _ = a * l := by group
    have hCa : L ⊓ centralizer ({a} : Set G) = T ⊓ L := by
      refine (h3.isSylowOf_T₁.eq_of_le (fun z hz => ⟨hz.2, mem_centralizer_singleton_iff.mpr
        ?_⟩) inf_le_left (hInv a haL ha1' ha2))
      exact mem_centralizer_iff.mp ha.2 z hz
    have hlT₁ : l ∈ T ⊓ L := by
      rw [← hCa]
      exact ⟨hl, mem_centralizer_singleton_iff.mpr hla⟩
    exact mul_mem ht.1 hlT₁.1
  · have h := le_centralizer_iff.mp hVC
    rwa [← hTW] at h

theorem centralizer_eq_sup
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥) {e : G}
    (he : e ∈ T ⊓ centralizer (L : Set G)) (he1 : e ≠ 1) :
    centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L :=
  hM.centralizer_eq_sup_of_aut h3 hF hZ h4 hO (hM.quotAutHom_mem_inner h3 hF hZ h4 hO) he he1

theorem centralizer_gmsV_eq
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hO : standardComponentOddCore (centralizer (L : Set G)) = ⊥) :
    centralizer (gmsV L T : Set G) = T :=
  hM.centralizer_gmsV_eq_of_aut h3 hF hZ h4 hO (hM.quotAutHom_mem_inner h3 hF hZ h4 hO)
    fun _ haL ha1 ha2 => hM.isPGroup_inf_centralizer h3 hF hZ h4 hO haL ha1 ha2

end SzMinCounter

end CFSG.ComponentClassification.GMS78
