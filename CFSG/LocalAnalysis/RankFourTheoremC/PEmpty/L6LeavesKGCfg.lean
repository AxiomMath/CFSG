module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGQuot
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC

open CFSG.Open CFSG.GH74.Uniqueness.SU Subgroup

@[expose] def KGStrongEmb {G : Type} [Group G] [Finite G] (p : ℕ) (M : Subgroup G) (z : G) :
    Prop :=
  ∀ f : ℕ, f.Prime → f ≠ 2 → f ≠ p → ∀ Y : Subgroup G, Y ≤ M → z ∈ Y →
    S622IsSimpleSection Y (rankThreePrimeCore p Y) →
    f ∣ (rankThreePrimeCore p Y).relIndex Y → CFSG.Open.GLBStronglyEmbedded f M

structure KGData {G : Type} [Group G] [Finite G] (p : ℕ) (H D S B L M : Subgroup G) (z : G) :
    Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  D_le_H : D ≤ H
  H_le_D : H ≤ normalizer (D : Set G)
  D_two : IsPGroup 2 D
  D_le_M : D ≤ M
  D_lt_S : D < S
  S_le_H : S ≤ H
  S_le_M : S ≤ M
  S_two : IsPGroup 2 S
  B_le_H : B ≤ H
  B_le_M : B ≤ M
  B_elem : IsElemAbelian p B
  B_card : Nat.card B = p ^ 2
  z_mem_B : z ∈ B
  z_order : orderOf z = p
  B_le_S : B ≤ normalizer (S : Set G)
  max_S : ∀ S' : Subgroup G, S' ≤ H → IsPGroup 2 S' → B ≤ normalizer (S' : Set G) → S ≤ S' →
    S' = S
  cover : ∀ S₀ : Subgroup G, D < S₀ → S₀ ≤ S → S ⊔ B ≤ normalizer (S₀ : Set G) →
    normalizer (S₀ : Set G) ≤ M
  cover_Z : normalizer (zpowers z : Set G) ≤ M
  L_sec : S622IsSimpleSection L D
  L_le_H : L ≤ H
  z_mem_L : z ∈ L
  L_rank : CFSG.Open.pRank p L ≤ 1
  L_not_le : ¬ L ≤ M
  M_le_L : M ⊓ H ≤ normalizer (L : Set G)

structure KGData3 {G : Type} [Group G] [Finite G] (p : ℕ) (H D S B L M : Subgroup G) (z : G) :
    Prop where
  toData : KGData p H D S B L M z
  charTwo : H ⊓ centralizer (D : Set G) ≤ D
  rank_H : CFSG.Open.pRank p H ≤ 2
  catalog : ∀ X : Subgroup G, X ≤ H → CFSG.AGLEmbedding.CatalogSimpleSections ↥X
  char_le : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
    normalizer (S₀ : Set G) ≤ M

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}

theorem mem_normalizer_zpowers_coe {H : Subgroup G} {z' n : ↥H}
    (hn : n ∈ normalizer ((zpowers z' : Subgroup ↥H) : Set ↥H)) :
    (n : G) ∈ normalizer ((zpowers (z' : G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hn ⊢
  intro g
  constructor
  · intro hg
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
    have h1 := (hn (z' ^ i)).mp (zpow_mem_zpowers z' i)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h1
    refine mem_zpowers_iff.mpr ⟨j, ?_⟩
    have h2 := congrArg Subtype.val hj
    simpa using h2
  · intro hg
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hg
    have hmem : n⁻¹ * z' ^ j * n ∈ zpowers z' := by
      refine (hn _).mpr ?_
      have e : n * (n⁻¹ * z' ^ j * n) * n⁻¹ = z' ^ j := by group
      rw [e]
      exact zpow_mem_zpowers z' j
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hmem
    refine mem_zpowers_iff.mpr ⟨i, ?_⟩
    have h2 := congrArg Subtype.val hi
    have h3 : (z' : G) ^ i = (n : G)⁻¹ * (z' : G) ^ j * n := by simpa using h2
    rw [h3, hj]
    group

namespace KGData

variable (d : KGData p H D S B L M z)

include d

theorem z_mem_H : z ∈ H := d.B_le_H d.z_mem_B

theorem not_dvd_D : ¬ p ∣ Nat.card D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp d.D_two
  intro h
  rw [hk] at h
  have := (Nat.prime_dvd_prime_iff_eq d.prime Nat.prime_two).mp (d.prime.dvd_of_dvd_pow h)
  have := d.five_le
  omega

theorem normal_subgroupOf : (D.subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer d.D_le_H).mpr d.H_le_D

variable [hDn : (D.subgroupOf H).Normal]

theorem coprime_D' : Nat.Coprime p (Nat.card (D.subgroupOf H)) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.D_le_H).toEquiv]
  exact (Nat.Prime.coprime_iff_not_dvd d.prime).mpr d.not_dvd_D

theorem z_not_mem_D : z ∉ D := by
  intro hz
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : p ∣ Nat.card D := by
    have : orderOf (⟨z, hz⟩ : D) = p := by rw [Subgroup.orderOf_mk]; exact d.z_order
    rw [← this]
    exact orderOf_dvd_natCard _
  exact d.not_dvd_D h1

theorem zb_order : orderOf (qmk H D ⟨z, d.z_mem_H⟩) = p := by
  haveI : Fact p.Prime := ⟨d.prime⟩
  have hzp : z ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rwa [d.z_order] at this
  have hp : (qmk H D ⟨z, d.z_mem_H⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨z, d.z_mem_H⟩ : ↥H) ^ p = 1 := Subtype.ext (by simpa using hzp)
    rw [this, map_one]
  refine orderOf_eq_prime hp ?_
  intro h1
  exact d.z_not_mem_D (qmk_eq_one_iff.mp h1)

theorem simple_img : IsSimpleGroup ↥(img H D L) := by
  obtain ⟨hDL, -, hne, hmin, -⟩ := d.L_sec
  obtain ⟨l₀, hl₀L, hl₀D⟩ : ∃ l ∈ L, l ∉ D := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hDL fun l hl => hcon l hl)
  have hl₀H : l₀ ∈ H := d.L_le_H hl₀L
  let k₀ : ↥(img H D L) :=
    ⟨qmk H D ⟨l₀, hl₀H⟩, mem_img.mpr ⟨⟨l₀, hl₀H⟩, hl₀L, rfl⟩⟩
  have hk₀ : k₀ ≠ 1 := by
    intro h
    exact hl₀D (qmk_eq_one_iff.mp (congrArg Subtype.val h))
  refine { toNontrivial := ⟨⟨k₀, 1, hk₀⟩⟩, eq_bot_or_eq_top_of_normal := ?_ }
  intro V hV
  set V' : Subgroup (QA H D) := V.map (img H D L).subtype with hV'
  set N : Subgroup G := pre H D V' ⊓ L with hN
  have hDN : D ≤ N := le_inf (D_le_pre d.D_le_H V') hDL
  have hNL : N ≤ L := inf_le_right
  have hNn : (N.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNL]
    intro n k hn hk
    obtain ⟨hnV, hnL⟩ := hn
    obtain ⟨h, rfl, hh⟩ := mem_pre.mp hnV
    have hkH : k ∈ H := d.L_le_H hk
    refine ⟨?_, L.mul_mem (L.mul_mem hk hnL) (L.inv_mem hk)⟩
    refine mem_pre.mpr ⟨⟨k, hkH⟩ * h * ⟨k, hkH⟩⁻¹, by simp, ?_⟩
    rw [map_mul, map_mul, map_inv]
    obtain ⟨v, hvV, hvh⟩ := Subgroup.mem_map.mp hh
    have hkL' : qmk H D ⟨k, hkH⟩ ∈ img H D L := mem_img.mpr ⟨⟨k, hkH⟩, hk, rfl⟩
    have hnorm := hV.conj_mem v hvV ⟨qmk H D ⟨k, hkH⟩, hkL'⟩
    have hvh' : (v : QA H D) = qmk H D h := hvh
    exact ⟨_, hnorm, by simp [hvh']⟩
  rcases hmin N hDN hNL hNn with hND | hNL'
  · left
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨h, hhL, hhq⟩ := mem_img.mp v.2
    have hvV : v.1 ∈ V' := ⟨v, hv, rfl⟩
    have hmemN : (h : G) ∈ N := by
      refine ⟨mem_pre.mpr ⟨h, rfl, ?_⟩, hhL⟩
      rw [hhq]
      exact hvV
    rw [hND] at hmemN
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by rw [← hhq]; exact qmk_eq_one_iff.mpr hmemN)
  · right
    rw [eq_top_iff]
    intro v _
    obtain ⟨h, hhL, hhq⟩ := mem_img.mp v.2
    have hmemN : (h : G) ∈ N := by rw [hNL']; exact hhL
    obtain ⟨h', hh', hmem'⟩ := mem_pre.mp hmemN.1
    have : h' = h := Subtype.ext hh'
    subst this
    obtain ⟨w, hwV, hwv⟩ := Subgroup.mem_map.mp (hhq ▸ hmem')
    have : w = v := Subtype.ext hwv
    rw [← this]
    exact hwV

theorem nonab_img : ∃ a b : ↥(img H D L), a * b ≠ b * a := by
  obtain ⟨hDL, -, -, -, hnab⟩ := d.L_sec
  push Not at hnab
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  have haH := d.L_le_H ha
  have hbH := d.L_le_H hb
  refine ⟨⟨qmk H D ⟨a, haH⟩, mem_img.mpr ⟨⟨a, haH⟩, ha, rfl⟩⟩,
    ⟨qmk H D ⟨b, hbH⟩, mem_img.mpr ⟨⟨b, hbH⟩, hb, rfl⟩⟩, fun h => hab ?_⟩
  have h1 := congrArg Subtype.val h
  have h2 : qmk H D ⟨a, haH⟩ * qmk H D ⟨b, hbH⟩ = qmk H D ⟨b, hbH⟩ * qmk H D ⟨a, haH⟩ := h1
  have h3 : qmk H D (⟨a, haH⟩ * ⟨b, hbH⟩ * ⟨a, haH⟩⁻¹ * ⟨b, hbH⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
    group
  exact qmk_eq_one_iff.mp h3

theorem rank_img : CFSG.Open.pRank p (img H D L) ≤ 1 := by
  have hp := d.prime
  have hker : ¬ p ∣ Nat.card (qmk H D).ker := by
    have : (qmk H D).ker = D.subgroupOf H := QuotientGroup.ker_mk' _
    rw [this]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp d.coprime_D'
  have h1 := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp (qmk H D) hker
    (L.subgroupOf H)
  have h2 : CFSG.Open.pRank p (L.subgroupOf H) ≤ CFSG.Open.pRank p L := by
    refine SU1.pRank_le_of fun E hEL hEel k hk => ?_
    have hle : E.map H.subtype ≤ L := by
      rintro _ ⟨e, he, rfl⟩
      exact hEL he
    have hcard : Nat.card (E.map H.subtype) = p ^ k := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hk]
    exact SU1.le_pRank hp.one_lt hle (CFSG.Open.IsElemAbelian.map hEel _) hcard
  exact h1.trans (h2.trans d.L_rank)

theorem B_isElemAbelian_subgroupOf : IsElemAbelian p (B.subgroupOf H) := by
  obtain ⟨hc, hp⟩ := SU1.isElemAbelian_iff.mp d.B_elem
  refine SU1.isElemAbelian_iff.mpr ⟨fun a ha b hb => Subtype.ext (hc _ ha _ hb), fun a ha => ?_⟩
  exact Subtype.ext (by simpa using hp _ ha)

theorem img_B_isElemAbelian : IsElemAbelian p (img H D B) :=
  CFSG.Open.IsElemAbelian.map d.B_isElemAbelian_subgroupOf (qmk H D)

theorem img_B_card : Nat.card (img H D B) = p ^ 2 := by
  have hBp : IsPGroup p (B.subgroupOf H) :=
    CFSG.Open.IsElemAbelian.isPGroup d.B_isElemAbelian_subgroupOf
  have h1 : Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' (D.subgroupOf H))) =
      Nat.card (B.subgroupOf H) :=
    CFSG.AGLEmbedding.card_map_mk_of_isPGroup d.prime (D.subgroupOf H) d.coprime_D' hBp
  have h2 : Nat.card (img H D B) = Nat.card (B.subgroupOf H) := h1
  rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.B_le_H).toEquiv, d.B_card]

theorem img_S_two : IsPGroup 2 (img H D S) :=
  (d.S_two.comap_subtype).map (qmk H D)

theorem img_S_ne : img H D S ≠ ⊥ := by
  obtain ⟨s, hsS, hsD⟩ := SetLike.exists_of_lt d.D_lt_S
  intro h
  have hmem : qmk H D ⟨s, d.S_le_H hsS⟩ ∈ img H D S := mem_img.mpr ⟨⟨s, _⟩, hsS, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hsD (qmk_eq_one_iff.mp hmem)

theorem img_B_le_S : img H D B ≤ normalizer ((img H D S : Subgroup (QA H D)) : Set (QA H D)) := by
  intro x hx
  obtain ⟨b, hbB, rfl⟩ := mem_img.mp hx
  exact qmk_mem_normalizer_img (d.B_le_S hbB)

theorem img_S_le_K : img H D S ≤ normalizer ((img H D L : Subgroup (QA H D)) : Set (QA H D)) := by
  intro x hx
  obtain ⟨s, hsS, rfl⟩ := mem_img.mp hx
  exact qmk_mem_normalizer_img (d.M_le_L ⟨d.S_le_M hsS, s.2⟩)

theorem img_B_le_K : img H D B ≤ normalizer ((img H D L : Subgroup (QA H D)) : Set (QA H D)) := by
  intro x hx
  obtain ⟨b, hbB, rfl⟩ := mem_img.mp hx
  exact qmk_mem_normalizer_img (d.M_le_L ⟨d.B_le_M hbB, b.2⟩)

theorem isPGroup_pre {T : Subgroup (QA H D)} (hT : IsPGroup 2 T) : IsPGroup 2 (pre H D T) := by
  intro g
  obtain ⟨h, hh, hmem⟩ := mem_pre.mp g.2
  obtain ⟨a, ha⟩ := hT ⟨qmk H D h, hmem⟩
  have ha' : (qmk H D h) ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have hd : (h : G) ^ (2 ^ a) ∈ D := by
    have : qmk H D (h ^ (2 ^ a)) = 1 := by rw [map_pow]; exact ha'
    simpa using qmk_eq_one_iff.mp this
  obtain ⟨b, hb⟩ := d.D_two ⟨(h : G) ^ (2 ^ a), hd⟩
  have hb' : ((h : G) ^ (2 ^ a)) ^ (2 ^ b) = 1 := by simpa using congrArg Subtype.val hb
  refine ⟨a + b, Subtype.ext ?_⟩
  show (g : G) ^ (2 ^ (a + b)) = 1
  rw [← hh, pow_add, pow_mul]
  exact hb'

theorem max_S_img : ∀ T : Subgroup (QA H D), IsPGroup 2 T →
    img H D B ≤ normalizer (T : Set (QA H D)) → img H D S ≤ T → T = img H D S := by
  intro T hT hBT hST
  have hTpre : pre H D T = S := by
    refine d.max_S (pre H D T) (pre_le T) (d.isPGroup_pre hT) ?_ ?_
    · intro b hb
      exact mem_normalizer_pre (a := ⟨b, d.B_le_H hb⟩)
        (hBT (mem_img.mpr ⟨⟨b, d.B_le_H hb⟩, hb, rfl⟩))
    · intro s hs
      exact mem_pre.mpr ⟨⟨s, d.S_le_H hs⟩, rfl,
        hST (mem_img.mpr ⟨⟨s, d.S_le_H hs⟩, hs, rfl⟩)⟩
  rw [← img_pre T, hTpre]

theorem cover_img : ∀ T : Subgroup (QA H D), T ≤ img H D S → T ≠ ⊥ →
    img H D S ≤ normalizer (T : Set (QA H D)) → img H D B ≤ normalizer (T : Set (QA H D)) →
    normalizer (T : Set (QA H D)) ≤ img H D M := by
  intro T hTS hT1 hSN hBN
  set T' := pre H D T with hT'
  have hDT : D ≤ T' := D_le_pre d.D_le_H T
  have hT'S : T' ≤ S := by
    intro g hg
    obtain ⟨h, rfl, hmem⟩ := mem_pre.mp hg
    obtain ⟨u, huS, hqu⟩ := mem_img.mp (hTS hmem)
    have hdu : (u : G)⁻¹ * h ∈ D := qmk_eq_iff.mp hqu
    have : (h : G) = u * ((u : G)⁻¹ * h) := by group
    rw [this]
    exact S.mul_mem huS (d.D_lt_S.le hdu)
  have hDlt : D < T' := by
    refine lt_of_le_of_ne hDT fun heq => hT1 ?_
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨h, rfl⟩ := qmk_surjective t
    have hh : (h : G) ∈ T' := mem_pre.mpr ⟨h, rfl, ht⟩
    rw [← heq] at hh
    rw [Subgroup.mem_bot]
    exact qmk_eq_one_iff.mpr hh
  have hSN' : S ⊔ B ≤ normalizer (T' : Set G) := by
    refine sup_le (fun s hs => ?_) (fun b hb => ?_)
    · exact mem_normalizer_pre (a := ⟨s, d.S_le_H hs⟩)
        (hSN (mem_img.mpr ⟨⟨s, d.S_le_H hs⟩, hs, rfl⟩))
    · exact mem_normalizer_pre (a := ⟨b, d.B_le_H hb⟩)
        (hBN (mem_img.mpr ⟨⟨b, d.B_le_H hb⟩, hb, rfl⟩))
  have hNM := d.cover T' hDlt hT'S hSN'
  intro x hx
  obtain ⟨a, rfl⟩ := qmk_surjective x
  exact mem_img.mpr ⟨a, hNM (mem_normalizer_pre hx), rfl⟩

theorem cover_Z_img : normalizer ((zpowers (qmk H D ⟨z, d.z_mem_H⟩) : Subgroup (QA H D)) :
    Set (QA H D)) ≤ img H D M := by
  set z' : ↥H := ⟨z, d.z_mem_H⟩ with hz'
  have hzo : orderOf z' = p := by rw [hz', Subgroup.orderOf_mk]; exact d.z_order
  haveI : Fact p.Prime := ⟨d.prime⟩
  have hzp : IsPGroup p (zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hmap : (zpowers z').map (qmk H D) = zpowers (qmk H D z') := MonoidHom.map_zpowers _ _
  intro x hx
  obtain ⟨a, rfl⟩ := qmk_surjective x
  have hfr := CFSG.AGLEmbedding.comap_normalizer_map_le_sup d.prime (D.subgroupOf H)
    d.coprime_D' hzp
  have hmap' : (zpowers z').map (QuotientGroup.mk' (D.subgroupOf H)) = zpowers (qmk H D z') :=
    hmap
  have ha : a ∈ (normalizer (((zpowers z').map (QuotientGroup.mk' (D.subgroupOf H)) :
      Subgroup (QA H D)) : Set (QA H D))).comap (QuotientGroup.mk' (D.subgroupOf H)) := by
    rw [Subgroup.mem_comap, hmap']
    exact hx
  obtain ⟨y, hy, n, hn, hyn⟩ := Subgroup.mem_sup_of_normal_left.mp (hfr ha)
  have hnM : (n : G) ∈ M := d.cover_Z (mem_normalizer_zpowers_coe hn)
  have hyM : (y : G) ∈ M := d.D_le_M hy
  refine mem_img.mpr ⟨a, ?_, rfl⟩
  rw [← hyn]
  exact M.mul_mem hyM hnM

theorem not_le_img : ¬ img H D L ≤ img H D M := by
  intro h
  apply d.L_not_le
  intro l hl
  have hlH := d.L_le_H hl
  have : l ∈ pre H D (img H D M) :=
    mem_pre.mpr ⟨⟨l, hlH⟩, rfl, h (mem_img.mpr ⟨⟨l, hlH⟩, hl, rfl⟩)⟩
  exact ((mem_pre_img d.D_le_M).mp this).1

end KGData

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC
