module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma45
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitNormalFour
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalGrowth

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G]


theorem isPGroup_center_quotient (X : Type*) [Group X] [Finite X] :
    IsPGroup 2 (center (X ⧸ pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (X ⧸ pPrimeCore 2 X) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  intro z
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨k, ?_⟩
  set w := z ^ (2 ^ k) with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (by positivity) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hwc : ((w : center _) : X ⧸ pPrimeCore 2 X) ∈ center (X ⧸ pPrimeCore 2 X) := w.2
  have hn : (zpowers ((w : center _) : X ⧸ pPrimeCore 2 X)).Normal :=
    ⟨fun n hn g => by
      have hnc : n ∈ center (X ⧸ pPrimeCore 2 X) := zpowers_le.mpr hwc hn
      rw [mem_center_iff.mp hnc g, mul_inv_cancel_right]
      exact hn⟩
  have hcop : Nat.Coprime 2 (Nat.card (zpowers ((w : center _) : X ⧸ pPrimeCore 2 X))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hwo]
    exact Nat.coprime_two_left.mpr hm
  have hle : zpowers ((w : center _) : X ⧸ pPrimeCore 2 X) ≤ pPrimeCore 2 (X ⧸ pPrimeCore 2 X) :=
    le_sSup ⟨hn, hcop⟩
  rw [hO] at hle
  have := hle (mem_zpowers _)
  rw [mem_bot] at this
  exact Subtype.ext this


theorem fusionZStar_eq_comap_pPrimeCore (L : Type*) [Group L] :
    Open.fusionZStar L =
      (center (L ⧸ pPrimeCore 2 L)).comap (QuotientGroup.mk' (pPrimeCore 2 L)) := by
  have h : Open.fusionOddCore L = pPrimeCore 2 L := GSThmB.fusionOddCore_eq_pPrimeCore L
  have key : ∀ (N N' : Subgroup L) [N.Normal] [N'.Normal], N = N' →
      (center (L ⧸ N)).comap (QuotientGroup.mk' N) =
        (center (L ⧸ N')).comap (QuotientGroup.mk' N') := by
    intro N N' _ _ hNN'
    subst hNN'
    rfl
  exact key _ _ h

theorem card_fusionZStar (L : Type*) [Group L] [Finite L] :
    Nat.card (Open.fusionZStar L) = Nat.card (pPrimeCore 2 L) *
      Nat.card (center (L ⧸ pPrimeCore 2 L)) := by
  rw [fusionZStar_eq_comap_pPrimeCore]
  set N := pPrimeCore 2 L
  set H := center (L ⧸ N)
  have hidx : (H.comap (QuotientGroup.mk' N)).index = H.index :=
    index_comap_of_surjective H (QuotientGroup.mk'_surjective N)
  have h1 := card_mul_index (H.comap (QuotientGroup.mk' N))
  have h2 := card_mul_index H
  have h3 := card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < H.index := Nat.pos_of_ne_zero (index_ne_zero_of_finite)
  rw [hidx] at h1
  have : Nat.card ↥(H.comap (QuotientGroup.mk' N)) * H.index =
      Nat.card N * Nat.card H * H.index := by
    rw [h1, h3, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [this])

theorem exists_card_zStarIn [Finite G] (J : Subgroup G) :
    ∃ e : ℕ, Nat.card (zStarIn J) = Nat.card (oddIn J) * 2 ^ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := (IsPGroup.iff_card (p := 2)).mp (isPGroup_center_quotient ↥J)
  refine ⟨e, ?_⟩
  rw [zStarIn, oddIn, card_map_of_injective J.subtype_injective,
    card_map_of_injective J.subtype_injective, card_fusionZStar, he]


theorem isSylowTwoIn_of_le [Finite G] {P K J : Subgroup G} (hP : IsSylowTwoIn P J) (hPK : P ≤ K)
    (hKJ : K ≤ J) : IsSylowTwoIn P K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := isPGroup_of_isSylowTwoIn hP
  obtain ⟨-, T, hT⟩ := hP
  refine ⟨hPK, ⟨P.subgroupOf K, hP2.of_equiv (subgroupOfEquivOfLe hPK).symm, ?_⟩, rfl⟩
  intro Q hQ hPQ
  have hQ' : IsPGroup 2 ((Q.map K.subtype).subgroupOf J) :=
    (hQ.map K.subtype).of_equiv (subgroupOfEquivOfLe ((map_subtype_le Q).trans hKJ)).symm
  have hle : (T : Subgroup J) ≤ (Q.map K.subtype).subgroupOf J := by
    rw [hT]
    intro y hy
    exact ⟨⟨y, hPK hy⟩, hPQ hy, rfl⟩
  have heq := T.is_maximal' hQ' hle
  rw [hT] at heq
  ext ⟨y, hyK⟩
  constructor
  · intro hy
    have : (⟨y, hKJ hyK⟩ : J) ∈ (Q.map K.subtype).subgroupOf J := ⟨⟨y, hyK⟩, hy, rfl⟩
    rw [heq] at this
    exact this
  · intro hy
    exact hPQ hy

theorem exists_eq_map_conj_of_isSylowTwoIn [Finite G] {P K Q : Subgroup G}
    (hP : IsSylowTwoIn P K) (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) (hcard : Nat.card Q = Nat.card P) :
    ∃ k ∈ K, Q = P.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨h, hhK, hh⟩ := exists_conj_mem_of_isSylowTwoIn hP hQK hQ
  refine ⟨h, hhK, ?_⟩
  have hle : Q.map (MulAut.conj h⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using hh y hy
  have heq : Q.map (MulAut.conj h⁻¹).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hcard])
  rw [← heq, Subgroup.map_map]
  ext y
  simp only [mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, inv_inv]
  constructor
  · intro hy
    exact ⟨y, hy, by group⟩
  · rintro ⟨z, hz, rfl⟩
    rwa [show h * (h⁻¹ * z * h) * h⁻¹ = z by group]

theorem exists_mul_mem_normalizer_of_isSylowTwoIn [Finite G] {P K : Subgroup G}
    (hP : IsSylowTwoIn P K) {c : G} (hc : c ∈ normalizer (K : Set G)) :
    ∃ m ∈ K, ∃ n ∈ normalizer (P : Set G), c = m * n := by
  have hP2 : IsPGroup 2 P := isPGroup_of_isSylowTwoIn hP
  have hQK : P.map (MulAut.conj c).toMonoidHom ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hc y).mp (hP.1 hy)
  obtain ⟨k, hk, hkP⟩ := exists_eq_map_conj_of_isSylowTwoIn hP hQK (hP2.map _)
    (Subgroup.card_map_of_injective (MulAut.conj c).injective)
  refine ⟨k, hk, k⁻¹ * c, ?_, by group⟩
  rw [mem_normalizer_iff_map_conj_eq]
  have h1 : P.map (MulAut.conj (k⁻¹ * c)).toMonoidHom =
      (P.map (MulAut.conj c).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  show P.map (MulAut.conj (k⁻¹ * c)).toMonoidHom = P
  rw [h1, hkP, Subgroup.map_map]
  ext y
  simp only [mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [show k⁻¹ * (k * z * k⁻¹) * k = z by group]
  · intro hy
    exact ⟨y, hy, by group⟩


theorem oddIn_le_zStarIn (J : Subgroup G) : oddIn J ≤ zStarIn J := by
  rintro _ ⟨o, ho, rfl⟩
  refine ⟨o, ?_, rfl⟩
  show QuotientGroup.mk' (Open.fusionOddCore ↥J) o ∈ center _
  have h : Open.fusionOddCore ↥J = pPrimeCore 2 ↥J := GSThmB.fusionOddCore_eq_pPrimeCore ↥J
  have hmk : QuotientGroup.mk' (Open.fusionOddCore ↥J) o = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, h]
    exact ho
  rw [hmk]
  exact one_mem _

theorem zStarIn_le_oddIn_sup [Finite G] {J P : Subgroup G} (hP : IsSylowTwoIn P J) :
    zStarIn J ≤ oddIn J ⊔ (P ⊓ zStarIn J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Zs := zStarIn J with hZs
  set X := oddIn J ⊔ (P ⊓ Zs) with hX
  have hOZ : oddIn J ≤ Zs := oddIn_le_zStarIn J
  have hZJ : Zs ≤ J := map_subtype_le _
  obtain ⟨e, he⟩ := exists_card_zStarIn J
  have h1 : X.relIndex Zs ∣ (oddIn J).relIndex Zs := relIndex_dvd_of_le_left Zs le_sup_left
  have h2 : (oddIn J).relIndex Zs = 2 ^ e := by
    have h := relIndex_mul_card (H := oddIn J) (K := Zs)
    rw [inf_of_le_left hOZ, hZs, he] at h
    have hpos : 0 < Nat.card (oddIn J) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  have hZn : J ≤ normalizer (Zs : Set G) := fun j hj =>
    mem_normalizer_iff.mpr fun y => ⟨fun hy => conj_mem_zStarIn (le_normalizer hj) hy,
      fun hy => by
        have := conj_mem_zStarIn (le_normalizer (inv_mem hj)) hy
        rwa [show j⁻¹ * (j * y * j⁻¹) * j⁻¹⁻¹ = y by group] at this⟩
  obtain ⟨T, hT⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer hP.1 hP.2 hZJ hZn
  have h3 : X.relIndex Zs ∣ (P ⊓ Zs).relIndex Zs := relIndex_dvd_of_le_left Zs le_sup_right
  have h4 : ¬ 2 ∣ (P ⊓ Zs).relIndex Zs := by
    have := Sylow.not_dvd_index T
    rwa [hT] at this
  have h5 : X.relIndex Zs = 1 := by
    rw [h2] at h1
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases k with _ | k
    · simpa using hk'
    · exact absurd ((show 2 ∣ X.relIndex Zs by
        rw [hk']; exact dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h3) h4
  exact relIndex_eq_one.mp h5


theorem card_eq_card_map_mul_card_inf_ker {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (K : Subgroup A) :
    Nat.card K = Nat.card (K.map f) * Nat.card ↥(K ⊓ f.ker) := by
  set g := f.comp K.subtype with hg
  have hr : g.range = K.map f := by
    rw [hg, MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hk : Nat.card g.ker = Nat.card ↥(K ⊓ f.ker) := by
    have h1 : g.ker = f.ker.subgroupOf K := by
      rw [hg, ← MonoidHom.comap_ker]
      rfl
    rw [h1, ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hr, hk]


theorem exists_card_eq_of_le_zStarIn [Finite G] {J H : Subgroup G} (hH : H ≤ zStarIn J) :
    ∃ e : ℕ, Nat.card H = Nat.card ↥(H ⊓ oddIn J) * 2 ^ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHJ : H ≤ J := hH.trans (map_subtype_le _)
  set f := QuotientGroup.mk' (pPrimeCore 2 ↥J) with hf
  set K := H.subgroupOf J with hK
  have himg : K.map f ≤ center (↥J ⧸ pPrimeCore 2 ↥J) := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨z, hz, hzk⟩ := hH (show (k : G) ∈ H from hk)
    have : z = k := Subtype.ext hzk
    rw [← this]
    have hz' := hz
    rw [fusionZStar_eq_comap_pPrimeCore] at hz'
    exact hz'
  obtain ⟨e, he⟩ := (IsPGroup.iff_card (p := 2)).mp
    ((isPGroup_center_quotient ↥J).to_le himg)
  refine ⟨e, ?_⟩
  have h1 := card_eq_card_map_mul_card_inf_ker f K
  have h2 : Nat.card ↥(K ⊓ f.ker) = Nat.card ↥(H ⊓ oddIn J) := by
    rw [hf, QuotientGroup.ker_mk', ← Subgroup.card_map_of_injective J.subtype_injective,
      Subgroup.map_inf _ _ _ J.subtype_injective, hK, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hHJ]
    rfl
  rw [← Nat.card_congr (subgroupOfEquivOfLe hHJ).toEquiv, h1, he, h2, mul_comm]

theorem nine_dvd_card_image [Finite G] {J : Subgroup G} {x : G}
    (h72 : Nat.card ↥(J ⊓ centralizer ({x} : Set G)) =
      72 * Nat.card ↥(oddIn J ⊓ centralizer ({x} : Set G))) :
    9 ∣ Nat.card ↥(((J ⊓ centralizer ({x} : Set G)).subgroupOf J).map
      (QuotientGroup.mk' (Open.fusionZStar ↥J))) := by
  set K := (J ⊓ centralizer ({x} : Set G)).subgroupOf J with hK
  set π := QuotientGroup.mk' (Open.fusionZStar ↥J) with hπ
  have h1 := card_eq_card_map_mul_card_inf_ker π K
  have hHle : J ⊓ centralizer ({x} : Set G) ⊓ zStarIn J ≤ zStarIn J := inf_le_right
  obtain ⟨e, he⟩ := exists_card_eq_of_le_zStarIn hHle
  have hOZ := oddIn_le_zStarIn J
  have hOJ : oddIn J ≤ J := map_subtype_le _
  have h2 : Nat.card ↥(K ⊓ π.ker) = Nat.card ↥(J ⊓ centralizer ({x} : Set G) ⊓ zStarIn J) := by
    rw [hπ, QuotientGroup.ker_mk', ← Subgroup.card_map_of_injective J.subtype_injective,
      Subgroup.map_inf _ _ _ J.subtype_injective, hK, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left inf_le_left]
    rfl
  have h3 : J ⊓ centralizer ({x} : Set G) ⊓ zStarIn J ⊓ oddIn J =
      oddIn J ⊓ centralizer ({x} : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans inf_le_right))
    · exact le_inf (le_inf (le_inf (inf_le_left.trans hOJ) inf_le_right)
        (inf_le_left.trans hOZ)) inf_le_left
  rw [h3] at he
  have hK' : Nat.card K = Nat.card ↥(J ⊓ centralizer ({x} : Set G)) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hK', h2, he, h72] at h1
  have hpos : 0 < Nat.card ↥(oddIn J ⊓ centralizer ({x} : Set G)) := Nat.card_pos
  have h4 : Nat.card ↥(K.map π) * 2 ^ e = 72 := by
    have := h1
    rw [show Nat.card ↥(K.map π) *
        (Nat.card ↥(oddIn J ⊓ centralizer ({x} : Set G)) * 2 ^ e) =
        (Nat.card ↥(K.map π) * 2 ^ e) * Nat.card ↥(oddIn J ⊓ centralizer ({x} : Set G)) by
      ring] at this
    exact (Nat.eq_of_mul_eq_mul_right hpos this).symm
  have h9 : 9 ∣ Nat.card ↥(K.map π) * 2 ^ e := by rw [h4]; norm_num
  exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right e (by norm_num)) h9)


theorem mem_sup_zStarIn_of_mk_mem {J X : Subgroup G} {w : J}
    (hw : QuotientGroup.mk' (Open.fusionZStar ↥J) w ∈
      (X.subgroupOf J).map (QuotientGroup.mk' (Open.fusionZStar ↥J))) :
    (w : G) ∈ X ⊔ zStarIn J := by
  obtain ⟨t, ht, hte⟩ := hw
  have h1 : t⁻¹ * w ∈ Open.fusionZStar ↥J := by
    rw [← QuotientGroup.eq]
    exact hte
  have h2 : ((t⁻¹ * w : J) : G) ∈ zStarIn J := ⟨_, h1, rfl⟩
  rw [show (w : G) = (t : G) * ((t⁻¹ * w : J) : G) by simp]
  exact mul_mem (mem_sup_left (show (t : G) ∈ X from ht)) (mem_sup_right h2)

theorem le_zStarIn_sup_of_parabolic (hPar : L34ParabolicFact) [Finite G] {J P : Subgroup G}
    {x : G} (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hP : IsSylowTwoIn P J)
    (h72 : Nat.card ↥(J ⊓ centralizer ({x} : Set G)) =
      72 * Nat.card ↥(oddIn J ⊓ centralizer ({x} : Set G))) :
    J ≤ ((J ⊓ normalizer (P : Set G)) ⊔ (J ⊓ centralizer ({x} : Set G))) ⊔ zStarIn J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := (J ⊓ normalizer (P : Set G)) ⊔ (J ⊓ centralizer ({x} : Set G)) with hW
  have hWJ : W ≤ J := sup_le inf_le_left inf_le_left
  set π := QuotientGroup.mk' (Open.fusionZStar ↥J) with hπ
  set W' : Subgroup (J ⧸ Open.fusionZStar ↥J) := (W.subgroupOf J).map π with hW'
  have hPJ : P ≤ J := hP.1
  obtain ⟨-, T₀, hT₀⟩ := hP
  set T := T₀.mapSurjective (QuotientGroup.mk'_surjective (Open.fusionZStar ↥J)) with hT
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hPZn : P ≤ normalizer ((zStarIn J : Subgroup G) : Set G) := fun p hp =>
    mem_normalizer_iff.mpr fun y => ⟨fun hy => conj_mem_zStarIn
      (le_normalizer (hPJ hp)) hy, fun hy => by
        have := conj_mem_zStarIn (le_normalizer (inv_mem (hPJ hp))) hy
        rwa [show p⁻¹ * (p * y * p⁻¹) * p⁻¹⁻¹ = y by group] at this⟩
  have hsupJ : P ⊔ zStarIn J ≤ J := sup_le hPJ hZJ
  set TT : Subgroup (↥J ⧸ Open.fusionZStar ↥J) := ↑T with hTT
  have himT : ∀ y : J, (y : G) ∈ P ⊔ zStarIn J → π y ∈ TT := by
    intro y hy
    have hy' : (y : G) ∈ (P : Set G) * (zStarIn J : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right P (zStarIn J) hPZn]
      exact hy
    obtain ⟨p, hp, z, hz, hpz⟩ := hy'
    obtain ⟨z', hz', hzz⟩ := hz
    have hyeq : y = ⟨p, hPJ hp⟩ * z' := Subtype.ext (by rw [← hpz, ← hzz]; rfl)
    rw [hyeq, map_mul, show π z' = 1 from (QuotientGroup.eq_one_iff z').mpr hz', mul_one]
    exact ⟨⟨p, hPJ hp⟩, by rw [hT₀]; exact hp, rfl⟩
  have hTinv : ∀ y : J, π y ∈ TT → (y : G) ∈ P ⊔ zStarIn J := by
    intro y hy
    have hy' : π y ∈ (T₀ : Subgroup J).map π := hy
    rw [hT₀] at hy'
    exact mem_sup_zStarIn_of_mk_mem hy'
  have hN : normalizer (TT : Set (↥J ⧸ Open.fusionZStar ↥J)) ≤ W' := by
    intro kt hkt
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ kt
    have hconj : ∀ k : J, π k ∈ normalizer (TT : Set (↥J ⧸ Open.fusionZStar ↥J)) →
        ∀ y ∈ P ⊔ zStarIn J, (k : G) * y * (k : G)⁻¹ ∈ P ⊔ zStarIn J := by
      intro k hk y hy
      have hyJ : y ∈ J := hsupJ hy
      have h1 := (mem_normalizer_iff.mp hk (π ⟨y, hyJ⟩)).mp (himT ⟨y, hyJ⟩ hy)
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      exact hTinv _ h1
    have hkN : (k : G) ∈ normalizer ((P ⊔ zStarIn J : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · exact hconj k hkt y
      · intro hy
        have h2 := hconj k⁻¹ (by rw [map_inv]; exact inv_mem hkt) _ hy
        simp only [InvMemClass.coe_inv, inv_inv] at h2
        rwa [show (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * (k : G) = y by group] at h2
    obtain ⟨m, hm, n, hn, hkmn⟩ := exists_mul_mem_normalizer_of_isSylowTwoIn
      (isSylowTwoIn_of_le ⟨hPJ, T₀, hT₀⟩ le_sup_left hsupJ) hkN
    have hmJ : m ∈ J := hsupJ hm
    have hnJ : n ∈ J := by
      rw [show n = m⁻¹ * k by rw [hkmn]; group]
      exact mul_mem (inv_mem hmJ) k.2
    have hkeq : k = ⟨m, hmJ⟩ * ⟨n, hnJ⟩ := Subtype.ext hkmn
    rw [hkeq, map_mul]
    refine mul_mem ?_ ⟨⟨n, hnJ⟩, mem_sup_left (mem_inf.mpr ⟨hnJ, hn⟩), rfl⟩
    obtain ⟨t, ht, hte⟩ := himT ⟨m, hmJ⟩ hm
    refine ⟨t, ?_, hte⟩
    rw [hT₀] at ht
    exact mem_sup_left (mem_inf.mpr ⟨hPJ ht, le_normalizer ht⟩)
  have h9 : 9 ∣ Nat.card W' := by
    refine (nine_dvd_card_image h72).trans (Subgroup.card_dvd_of_le ?_)
    exact Subgroup.map_mono (fun y hy => mem_sup_right hy)
  have htop := hPar _ hL34 T W' hN h9
  intro j hj
  have hj' : π ⟨j, hj⟩ ∈ W' := by rw [htop]; exact mem_top _
  exact mem_sup_zStarIn_of_mk_mem hj'


theorem exists_two_involutions [Finite G] {Z : Subgroup G} (hZ2 : IsPGroup 2 Z)
    (hcomm : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u) (hnc : ¬ IsCyclic ↥Z) :
    ∃ u ∈ Z, ∃ v ∈ Z, u * u = 1 ∧ v * v = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  let _ : CommGroup ↥Z :=
    { (inferInstance : Group ↥Z) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  by_contra h
  push Not at h
  apply hnc
  refine FooteLit.isCyclic_of_unique_involution hZ2 fun a b ha hb => ?_
  by_contra hab
  push Not at hab
  obtain ⟨ha1, hb1, hab'⟩ := hab
  have ha2 : (a : G) * a = 1 := by
    have := congrArg Subtype.val ha
    simpa [pow_two] using this
  have hb2 : (b : G) * b = 1 := by
    have := congrArg Subtype.val hb
    simpa [pow_two] using this
  exact hab' (Subtype.ext (h a a.2 b b.2 ha2 hb2 (fun h' => ha1 (Subtype.ext h'))
    (fun h' => hb1 (Subtype.ext h'))))

theorem isSylowTwoIn_sup_odd [Finite G] {E O : Subgroup G} (hE : IsPGroup 2 E)
    (hEO : E ≤ normalizer (O : Set G)) (hO : Odd (Nat.card O)) : IsSylowTwoIn E (E ⊔ O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_sup_left, ⟨E.subgroupOf (E ⊔ O),
    hE.of_equiv (subgroupOfEquivOfLe le_sup_left).symm, ?_⟩, rfl⟩
  intro Q hQ hEQ
  apply le_antisymm _ hEQ
  intro q hq
  have hq' : (q : G) ∈ (E : Set G) * (O : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right E O hEO]
    exact q.2
  obtain ⟨e, he, o, ho, heo⟩ := hq'
  have heQ : (⟨e, mem_sup_left he⟩ : ↥(E ⊔ O)) ∈ Q := hEQ he
  have hoQ : (⟨o, mem_sup_right ho⟩ : ↥(E ⊔ O)) ∈ Q := by
    have : (⟨o, mem_sup_right ho⟩ : ↥(E ⊔ O)) = (⟨e, mem_sup_left he⟩ : ↥(E ⊔ O))⁻¹ * q :=
      Subtype.ext (by simp [← heo])
    rw [this]
    exact mul_mem (inv_mem heQ) hq
  have hQ2 : IsPGroup 2 (Q.map (E ⊔ O).subtype) := hQ.map _
  have ho1 : o = 1 := by
    have hbot := UnbalancedLayer.eq_bot_of_le_two_group_of_le_odd hQ2 hO
      (zpowers_le.mpr ⟨_, hoQ, rfl⟩) (zpowers_le.mpr ho)
    have h := mem_zpowers ((E ⊔ O).subtype ⟨o, mem_sup_right ho⟩)
    rw [hbot, mem_bot] at h
    simpa using h
  have heo' : e * o = q := heo
  have hqe : q = ⟨e, mem_sup_left he⟩ := Subtype.ext (by rw [← heo', ho1, mul_one])
  rw [hqe]
  exact he


theorem centralizer_le_oddIn_sup_normalizer [Finite G] {J V : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (J : Set G)) (hVZ : V ≤ zStarIn J) (hE : IsElemTwo (V ⊔ zpowers x)) :
    J ⊓ centralizer ({x} : Set G) ≤
      oddIn J ⊔ (J ⊓ normalizer ((V ⊔ zpowers x : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E₀ : Subgroup G := V ⊔ zpowers x with hE₀
  set O : Subgroup G := oddIn J with hO
  have hVJ : V ≤ J := hVZ.trans (map_subtype_le _)
  have hOJ : O ≤ J := map_subtype_le _
  have hJO : J ≤ normalizer (O : Set G) := fun j hj => mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => conj_mem_oddIn hj hy, fun hy => by
      have := conj_mem_oddIn (inv_mem hj) hy
      rwa [show j⁻¹ * (j * y * j⁻¹) * j⁻¹⁻¹ = y by group] at this⟩
  have hxO : x ∈ normalizer (O : Set G) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J) hxN
  have hEO : E₀ ≤ normalizer (O : Set G) := sup_le (hVJ.trans hJO) (zpowers_le.mpr hxO)
  have hOodd : Odd (Nat.card O) := odd_card_map_pPrimeCore J
  have hSyl := isSylowTwoIn_sup_odd hE.isPGroup hEO hOodd
  have hx2 : x * x = 1 := hE.2 x (mem_sup_right (mem_zpowers x))
  have hxV : ∀ v ∈ V, v * x = x * v := fun v hv => hE.1 v (mem_sup_left hv) x
    (mem_sup_right (mem_zpowers x))
  intro c hc
  have hcJ : c ∈ J := (mem_inf.mp hc).1
  have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
  have hconj : ∀ d : G, d ∈ J → d * x * d⁻¹ = x → ∀ y ∈ E₀ ⊔ O, d * y * d⁻¹ ∈ E₀ ⊔ O := by
    intro d hdJ hdx y hy
    have hy' : y ∈ (E₀ : Set G) * (O : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right E₀ O hEO]
      exact hy
    obtain ⟨e, he, o, ho, rfl⟩ := hy'
    have hdo : d * o * d⁻¹ ∈ O := conj_mem_oddIn hdJ ho
    rw [show d * (e * o) * d⁻¹ = (d * e * d⁻¹) * (d * o * d⁻¹) by group]
    refine mul_mem ?_ (mem_sup_right hdo)
    rcases mem_or_mul_of_mem_sup_zpowers hx2 hxV he with hev | ⟨v, hv, rfl⟩
    ·
      have hvK : e ∈ coreActionKernel J := by
        have h := (GSThmB.map_fusionZStar_eq J ▸ hVZ hev : e ∈ J ⊓ coreActionKernel J)
        exact (mem_inf.mp h).2
      have h1 := (mem_coreActionKernel.mp hvK).2 d⁻¹ (inv_mem hdJ)
      rw [inv_inv] at h1
      rw [show d * e * d⁻¹ = e * (e⁻¹ * d * e * d⁻¹) by group]
      refine mul_mem (mem_sup_left (mem_sup_left hev)) (mem_sup_right ?_)
      have := inv_mem h1
      rwa [show (d * e⁻¹ * d⁻¹ * e)⁻¹ = e⁻¹ * d * e * d⁻¹ by group] at this
    · have hvK : v ∈ coreActionKernel J := by
        have h := (GSThmB.map_fusionZStar_eq J ▸ hVZ hv : v ∈ J ⊓ coreActionKernel J)
        exact (mem_inf.mp h).2
      have h1 := (mem_coreActionKernel.mp hvK).2 d⁻¹ (inv_mem hdJ)
      rw [inv_inv] at h1
      rw [show d * (v * x) * d⁻¹ = v * (v⁻¹ * d * v * d⁻¹) * (d * x * d⁻¹) by group, hdx]
      refine mul_mem (mul_mem (mem_sup_left (mem_sup_left hv)) (mem_sup_right ?_))
        (mem_sup_left (mem_sup_right (mem_zpowers x)))
      have := inv_mem h1
      rwa [show (d * v⁻¹ * d⁻¹ * v)⁻¹ = v⁻¹ * d * v * d⁻¹ by group] at this
  have hcN : c ∈ normalizer ((E₀ ⊔ O : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · exact hconj c hcJ (by rw [hcx]; group) y
    · intro hy
      have h2 := hconj c⁻¹ (inv_mem hcJ) (by
        calc c⁻¹ * x * c⁻¹⁻¹ = c⁻¹ * (x * c) := by group
          _ = c⁻¹ * (c * x) := by rw [hcx]
          _ = x := by group) _ hy
      rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h2
  obtain ⟨m, hm, n, hn, hcmn⟩ := exists_mul_mem_normalizer_of_isSylowTwoIn hSyl hcN
  have hm' : m ∈ (E₀ : Set G) * (O : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right E₀ O hEO]
    exact hm
  obtain ⟨e, he, o, ho, rfl⟩ := hm'
  have heo : e * o * e⁻¹ ∈ O := by
    have := (mem_normalizer_iff.mp (hEO he) o).mp ho
    exact this
  have hen : e * n ∈ normalizer (E₀ : Set G) := mul_mem (le_normalizer he) hn
  have henJ : e * n ∈ J := by
    rw [show e * n = (e * o * e⁻¹)⁻¹ * c by rw [hcmn]; group]
    exact mul_mem (inv_mem (hOJ heo)) hcJ
  rw [hcmn, show e * o * n = (e * o * e⁻¹) * (e * n) by group]
  exact mul_mem (mem_sup_left heo) (mem_sup_right (mem_inf.mpr ⟨henJ, hen⟩))


end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise
open GrS4

theorem l34Lemma44_of_inputs (hU : L34UnbalancingUnitaryStep) (hC : L34UnitaryCentralizerFact)
    (hBor : L34BorelGenerationFact) (hPar : L34ParabolicFact) : L34Lemma44 := by
  intro G _ _ a x J S A hset _ hZnc
  obtain ⟨-, hU3, hL34, -, hS, -, hxS⟩ := hset
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := isSylowTwoIn_inf hS
  have hxU : IsL34Unitary J x := hU G a x J hU3 hL34
  have hJper : ⁅J, J⁆ = J :=
    UnbalancedCorr.commutator_eq_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1
  have hxN : x ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) :=
    UnbalancedLayer.normalizer_inf_mem (le_normalizer hxS) hxU.1
  obtain ⟨hinv, hcard8, h72, -, -, hE8, -, -⟩ := hC G J (S ⊓ J) x hJper hL34 hxU hP hxN
  have hzJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by rw [inf_assoc, inf_eq_right.mpr hzJ]
  have hnc : ¬ IsCyclic ↥(S ⊓ J ⊓ zStarIn J) := by rwa [hZP]
  have hRel : IsElemTwo (S ⊓ J ⊓ centralizer ({x} : Set G)) := hE8 hnc
  have hx2 : x * x = 1 := hxU.2.1
  have hxJ : x ∉ J := fun h => hxU.2.2.1 (mem_sup_left h)
  have hxR : x ∉ S ⊓ J ⊓ centralizer ({x} : Set G) := fun h =>
    hxJ (mem_inf.mp (mem_inf.mp h).1).2
  have hRx : ∀ r ∈ S ⊓ J ⊓ centralizer ({x} : Set G), r * x = x * r := fun r hr =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp hr).2
  obtain ⟨hBel, hBc⟩ := isElemTwo_sup_zpowers hRel hx2 hxR hRx
  refine ⟨⟨hBel, by rw [hBc, hcard8]⟩, ?_⟩
  intro C hCP hCel hC16 hRC hCdef
  set B : Subgroup G := S ⊓ J ⊓ centralizer ({x} : Set G) ⊔ zpowers x with hB
  set Y : Subgroup G := ⨆ (E : Subgroup G) (_ : E ≤ B ∨ E ≤ C) (_ : IsEightGroup E),
    J ⊓ normalizer (E : Set G) with hY
  have hYJ : Y ≤ J := iSup_le fun E => iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hmemY : ∀ E : Subgroup G, (E ≤ B ∨ E ≤ C) → IsEightGroup E →
      J ⊓ normalizer (E : Set G) ≤ Y := fun E hE h8 =>
    le_iSup₂_of_le (f := fun (E : Subgroup G) (_ : E ≤ B ∨ E ≤ C) =>
      ⨆ (_ : IsEightGroup E), J ⊓ normalizer (E : Set G)) E hE (le_iSup_of_le h8 le_rfl)
  refine le_antisymm ?_ hYJ
  have hJO : J ≤ normalizer ((oddIn J : Subgroup G) : Set G) := fun j hj =>
    mem_normalizer_iff.mpr fun y => ⟨fun hy => conj_mem_oddIn hj hy, fun hy => by
      have := conj_mem_oddIn (inv_mem hj) hy
      rwa [show j⁻¹ * (j * y * j⁻¹) * j⁻¹⁻¹ = y by group] at this⟩
  have hxO : x ∈ normalizer ((oddIn J : Subgroup G) : Set G) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J) hxU.1
  have hOY : oddIn J ≤ Y := by
    have hBN : B ≤ normalizer ((oddIn J : Subgroup G) : Set G) :=
      sup_le (fun r hr => hJO (mem_inf.mp (mem_inf.mp hr).1).2) (zpowers_le.mpr hxO)
    have hBea : Open.IsElemAbelian 2 B := by
      refine ⟨⟨⟨fun u v => Subtype.ext (hBel.1 u u.2 v v.2)⟩⟩, fun u hu => ?_⟩
      rw [pow_two]
      exact hBel.2 u hu
    have hgen := SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 3
      Nat.prime_two B (oddIn J) hBea (by rw [hBc, hcard8]; norm_num) hBN
      (Nat.coprime_two_left.mpr (odd_card_map_pPrimeCore J))
    rw [← hgen]
    refine iSup₂_le fun F hF => ?_
    obtain ⟨hFB, hF8⟩ := hF
    refine (le_inf (inf_le_left.trans (map_subtype_le _)) ?_).trans
      (hmemY F (Or.inl hFB) ⟨hBel.mono hFB, hF8⟩)
    intro y hy
    exact mem_normalizer_of_le_centralizer fun f hf =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (mem_inf.mp hy).2 f hf)
  have hPeq : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := hZP
  have hNY : J ⊓ normalizer ((S ⊓ J : Subgroup G) : Set G) ≤ Y := by
    have h := hBor G J (S ⊓ J) C hJper hL34 hP hnc hCP hCel hC16 (by rw [hPeq]; exact hCdef)
    refine h.trans (sup_le hOY ?_)
    exact iSup_le fun E => iSup_le fun hEC => iSup_le fun h8 => hmemY E (Or.inr hEC) h8
  have hZ2 : IsPGroup 2 ↥(S ⊓ J ⊓ zStarIn J) := hS2.to_le (inf_le_left.trans inf_le_left)
  have hZcomm : ∀ u ∈ S ⊓ J ⊓ zStarIn J, ∀ v ∈ S ⊓ J ⊓ zStarIn J, u * v = v * u := by
    intro u hu v hv
    have hvK : v ∈ coreActionKernel J := by
      have h := (GSThmB.map_fusionZStar_eq J ▸ (mem_inf.mp hv).2 : v ∈ J ⊓ coreActionKernel J)
      exact (mem_inf.mp h).2
    have hc := (mem_coreActionKernel.mp hvK).2 u (mem_inf.mp (mem_inf.mp hu).1).2
    have huS := (mem_inf.mp (mem_inf.mp hu).1).1
    have hvS := (mem_inf.mp (mem_inf.mp hv).1).1
    have hcS : u⁻¹ * v⁻¹ * u * v ∈ S :=
      mul_mem (mul_mem (mul_mem (inv_mem huS) (inv_mem hvS)) huS) hvS
    have hbot := UnbalancedLayer.eq_bot_of_le_two_group_of_le_odd hS2 (odd_card_map_pPrimeCore J)
      (zpowers_le.mpr hcS) (zpowers_le.mpr hc)
    have h1 : u⁻¹ * v⁻¹ * u * v = 1 := by
      have := mem_zpowers (u⁻¹ * v⁻¹ * u * v)
      rw [hbot, mem_bot] at this
      exact this
    calc u * v = (v * u) * (u⁻¹ * v⁻¹ * u * v) := by group
      _ = v * u := by rw [h1, mul_one]
  obtain ⟨u, hu, v, hv, hu2, hv2, hu1, hv1, huv⟩ := exists_two_involutions hZ2 hZcomm hnc
  have hcomx : ∀ z ∈ S ⊓ J ⊓ zStarIn J, z * z = 1 → z * x = x * z := by
    intro z hz hz2
    have h1 := hinv z hz
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rw [hzi] at h1
    calc z * x = x * (x⁻¹ * z * x) := by group
      _ = x * z := by rw [h1]
  have hux := hcomx u hu hu2
  have hvx := hcomx v hv hv2
  have hvu : v ∉ zpowers u := fun h => (eq_one_or_eq_of_mem_zpowers hu2 h).elim hv1 huv.symm
  obtain ⟨hVel, hVc⟩ := isElemTwo_sup_zpowers (isElemTwo_zpowers hu2) hv2 hvu fun e he => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact Commute.zpow_left (hZcomm u hu v hv) k
  set V : Subgroup G := zpowers u ⊔ zpowers v with hV
  have hVZ : V ≤ zStarIn J :=
    sup_le (zpowers_le.mpr (mem_inf.mp hu).2) (zpowers_le.mpr (mem_inf.mp hv).2)
  have hVR : V ≤ S ⊓ J ⊓ centralizer ({x} : Set G) :=
    sup_le (zpowers_le.mpr (mem_inf.mpr ⟨(mem_inf.mp hu).1,
        mem_centralizer_singleton_iff.mpr hux⟩))
      (zpowers_le.mpr (mem_inf.mpr ⟨(mem_inf.mp hv).1, mem_centralizer_singleton_iff.mpr hvx⟩))
  have hxV : x ∉ V := fun h => hxR (hVR h)
  obtain ⟨hE₀el, hE₀c⟩ := isElemTwo_sup_zpowers hVel hx2 hxV fun e he => hRx e (hVR he)
  have hcardu : Nat.card (zpowers u) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1]
  have hE₀8 : IsEightGroup (V ⊔ zpowers x) := ⟨hE₀el, by rw [hE₀c, hVc, hcardu]⟩
  have hE₀B : V ⊔ zpowers x ≤ B := sup_le (hVR.trans le_sup_left) le_sup_right
  have hE₀Y := hmemY _ (Or.inl hE₀B) hE₀8
  have hCxY : J ⊓ centralizer ({x} : Set G) ≤ Y :=
    (centralizer_le_oddIn_sup_normalizer hxU.1 hVZ hE₀el).trans (sup_le hOY hE₀Y)
  have hPY : S ⊓ J ≤ Y := fun p hp => hNY (mem_inf.mpr ⟨(mem_inf.mp hp).2, le_normalizer hp⟩)
  have hZY : zStarIn J ≤ Y :=
    (zStarIn_le_oddIn_sup hP).trans (sup_le hOY (inf_le_left.trans hPY))
  exact (le_zStarIn_sup_of_parabolic hPar hL34 hP h72).trans
    (sup_le (sup_le hNY hCxY) hZY)

end CFSG.ComponentClassification.GrSLit
