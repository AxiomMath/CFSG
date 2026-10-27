module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83Alt
public import CFSG.LocalAnalysis.GLTheoremA.I32One
public import CFSG.GH74.Uniqueness.SU.SU13TA9PermE
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma82
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace S8

structure Inputs83 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1016HN : L83.I1016HNAt G
  i1016Co1 : L83.I1016Co1At G
  i1423 : L83.I1423At G
  i112 : L83.I112SingleAt G
  i1415 : L83.I1415NineAt G
  i2013 : I2013At
  i2014 : L83.I2014UsedAt G

namespace L83

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_inf {A C : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hC ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hC h]

theorem mem_normalizer_commutator {Q I : Subgroup G} {g : G}
    (hQ : g ∈ Subgroup.normalizer (Q : Set G)) (hI : g ∈ Subgroup.normalizer (I : Set G)) :
    g ∈ Subgroup.normalizer ((⁅Q, I⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hQ hI ⊢
  unfold GLBConj at hQ hI ⊢
  rw [Subgroup.map_commutator, hQ, hI]

theorem commutator_le_of_le_normalizer {Q I : Subgroup G}
    (h : I ≤ Subgroup.normalizer (Q : Set G)) : (⁅Q, I⁆ : Subgroup G) ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq i hi
  rw [commutatorElement_def]
  have h1 : i * q⁻¹ * i⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (h hi) q⁻¹).1 (Q.inv_mem hq)
  simpa [mul_assoc] using Q.mul_mem hq h1

theorem orderOf_eq_of_mem {p : ℕ} (hp : p.Prime) {B : Subgroup G} (hB : IsElemAbelian p B) {x : G}
    (hx : x ∈ B) (hx1 : x ≠ 1) : orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (hB.2 x hx) hx1

theorem isElemAbelian_altDxy {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y = y * x) :
    IsElemAbelian 3 (altDxy x y) := by
  unfold altDxy
  refine IsElemAbelian.sup_of_commute (isElemAbelian_zpowers hx) (isElemAbelian_zpowers hy) ?_
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact (Commute.zpow_zpow (hxy : Commute x y) i j).eq

theorem false_of_le_of_odd {S H : Subgroup G} (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hSH : S ≤ H)
    (hH : Odd (Nat.card H)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hS
  obtain ⟨n, hn, hcard⟩ := hS2.nontrivial_iff_card.1 inferInstance
  have h2 : 2 ∣ Nat.card S := hcard ▸ dvd_pow_self 2 (by omega)
  exact (Nat.not_even_iff_odd.2 hH) (even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hSH)))

theorem not_isPGroup_two_of_alt8 {I : Subgroup G} (hI : IsAltPType 3 I 8) : ¬ IsPGroup 2 I := by
  intro h2
  obtain ⟨e⟩ := hI
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsPGroup 2 (PQuot 3 I) := h2.to_quotient _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hq
  have hA : Nat.card (PQuot 3 I) = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  rw [hA] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 20160)
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem comp_centralizer_of_inf {L D J : Subgroup G} {x : G}
    (hLn : cx x ≤ Subgroup.normalizer (L : Set G)) (hxD : x ∈ D)
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer (D : Set G)) J) :
    GLAPComponent 3 (Subgroup.centralizer (D : Set G)) J := by
  have hCx : Subgroup.centralizer (D : Set G) ≤ cx x :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD)
  refine glaPComponent_of_isSubnormal' Nat.prime_three
    (IsSubnormal.step inf_le_right ?_ (IsSubnormal.refl _)) hJ
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
  intro g hg
  exact mem_normalizer_inf (hLn (hCx hg)) (Subgroup.le_normalizer hg)

theorem exists_gen_of_index {A D : Subgroup G} (hAD : A ≤ D) (hD : Nat.card D = 3 ^ 2)
    (hi : (A.subgroupOf D).index = 3) : ∃ a : G, a ∈ A ∧ a ≠ 1 ∧ A = Subgroup.zpowers a := by
  have hA3 : Nat.card A = 3 := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf D)
    have h2 : Nat.card (A.subgroupOf D) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv
    rw [h2, hi, hD] at h1
    omega
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA3
    omega
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hdvd : orderOf a ∣ 3 := hA3 ▸ Subgroup.orderOf_dvd_natCard A haA
  have hord : orderOf a = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1'
    · exact h
  refine ⟨a, haA, ha1', ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haA)
    (by rw [hA3, Nat.card_zpowers, hord])).symm

theorem exists_second_gen {D : Subgroup G} {a : G} (haD : a ∈ D) (ha1 : a ≠ 1)
    (hDel : IsElemAbelian 3 D) (hD : Nat.card D = 3 ^ 2) :
    ∃ d ∈ D, d ∉ Subgroup.zpowers a ∧ D ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
  have hord : orderOf a = 3 := orderOf_eq_of_mem Nat.prime_three hDel haD ha1
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have hzD : Subgroup.zpowers a ≤ D := Subgroup.zpowers_le.2 haD
  obtain ⟨d, hdD, hda⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have h := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers a from hcon)
    rw [hD, hza] at h
    omega
  refine ⟨d, hdD, hda, ?_⟩
  have hHD : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤ D := sup_le hzD (Subgroup.zpowers_le.2 hdD)
  have hdvd : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers d) ∣ 3 ^ 2 :=
    hD ▸ Subgroup.card_dvd_of_le hHD
  have h3 : 3 ∣ Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers d) :=
    hza ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers d) ≠ 3 := by
    intro h
    have e : Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hza])
    exact hda (e ▸ (le_sup_right : Subgroup.zpowers d ≤ _) (Subgroup.mem_zpowers d))
  have h9 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers d) = 3 ^ 2 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    interval_cases k
    · rw [hk'] at h3; norm_num at h3
    · exact absurd hk' (by simpa using hne)
    · exact hk'
  exact le_of_eq (Subgroup.eq_of_le_of_card_ge hHD (by rw [h9, hD])).symm

theorem inf_cx_le_centralizer {D : Subgroup G} {a d : G}
    (hD : D ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers d) :
    cx a ⊓ cx d ≤ Subgroup.centralizer (D : Set G) := by
  intro g hg
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤ cx g := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).1).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2).symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hD hh))

theorem le_of_isSubnormal_of_commutator_eq {S I K X : Subgroup G} (hK : IsSubnormal K X)
    (hSX : S ≤ X) (hIK : I ≤ K) (hS : (⁅S, I⁆ : Subgroup G) = S) : S ≤ K := by
  induction hK with
  | refl => exact hSX
  | @step H M X' hHM hn _ ih =>
    have hSM : S ≤ M := ih hSX (hIK.trans hHM)
    have hMN : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn
    rw [← hS, Subgroup.commutator_le]
    intro s hs i hi
    rw [commutatorElement_def]
    have h1 : s * i * s⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 (hMN (hSM hs)) i).1 (hIK hi)
    exact H.mul_mem h1 (H.inv_mem (hIK hi))

theorem rank_step {p : ℕ} (hc : S8Ctx G p) (h1016 : I1016HNAt G) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h82 : Sp82 G p B x L) (hHN : catalogIs (PSimple p L) (sporIs .HN)) :
    p = 3 ∧ Nat.card B = 3 ^ 4 ∧ GLATwoLocalRank 3 G = 4 := by
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  have hm4 := hc.ctx.rank_ge
  obtain ⟨T, hTL, hT2, hBT, -, hTc⟩ := h82.hT
  have hxp : orderOf x = p := orderOf_eq_of_mem hp h82.hB.1 h82.hxB h82.hx1
  have hLn : cx x ≤ Subgroup.normalizer (L : Set G) := normalizer_of_unique h82.hL h82.huniq
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_inf (Subgroup.le_normalizer h82.hxB)
      (hLn (Subgroup.mem_centralizer_singleton_iff.2 rfl))
  have hprod := card_sup_mul_card_inf_of_le_normalizer hxN
  have hzx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxp]
  rw [hzx] at hprod
  have hpos : 0 < Nat.card ↥((B ⊓ L) ⊓ Subgroup.zpowers x) := Nat.card_pos
  have hBle : Nat.card B ≤ Nat.card ↥(B ⊓ L) * p :=
    calc Nat.card B ≤ Nat.card ↥((B ⊓ L) ⊔ Subgroup.zpowers x) := Subgroup.card_le_of_le h82.hBL
      _ ≤ Nat.card ↥((B ⊓ L) ⊔ Subgroup.zpowers x) * Nat.card ↥((B ⊓ L) ⊓ Subgroup.zpowers x) :=
        Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card ↥(B ⊓ L) * p := hprod
  have hBc : Nat.card B = p ^ GLATwoLocalRank p G := h82.hB.2.1
  have h3 : p ^ 3 ≤ Nat.card ↥(B ⊓ L) := by
    have h4 : p ^ 3 * p ≤ Nat.card ↥(B ⊓ L) * p :=
      calc p ^ 3 * p = p ^ 4 := by ring
        _ ≤ p ^ GLATwoLocalRank p G := Nat.pow_le_pow_right hp.pos hm4
        _ = Nat.card B := hBc.symm
        _ ≤ Nat.card ↥(B ⊓ L) * p := hBle
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  obtain ⟨rfl, h27⟩ := h1016 p hp hp2 (cx x) L (B ⊓ L) T h82.hL hHN inf_le_right
    (isElemAbelian_mono h82.hB.1 inf_le_left) hTL hT2 hTc (inf_le_left.trans hBT) h3
  have hm : GLATwoLocalRank 3 G ≤ 4 := by
    have h81 : 3 ^ GLATwoLocalRank 3 G ≤ 3 ^ 4 := by
      rw [← hBc]
      calc Nat.card B ≤ Nat.card ↥(B ⊓ L) * 3 := hBle
        _ ≤ 3 ^ 3 * 3 := Nat.mul_le_mul_right 3 h27
        _ = 3 ^ 4 := by ring
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h81
  have hm' : GLATwoLocalRank 3 G = 4 := le_antisymm hm hm4
  exact ⟨rfl, by rw [hBc, hm'], hm'⟩

theorem alt9_elemAbelian :
    ∃ E : Subgroup ↥(alternatingGroup (Fin 9)), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  open CFSG.GH74.Uniqueness.SU.SU13.TA.L9 in
  refine ⟨Ebar, ⟨⟨⟨fun a b => Subtype.ext (Ebar_comm a a.2 b b.2).eq⟩⟩, ?_⟩, by rw [card_Ebar]; norm_num⟩
  open CFSG.GH74.Uniqueness.SU.SU13.TA.L9 in
  intro x hx
  obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.1 hx
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  show toP i j k ^ 3 = 1
  clear hx
  revert i j k
  decide

theorem lift_elemAbelian {p k : ℕ} (hp : p.Prime) {L : Subgroup G} {E' : Subgroup (PQuot p L)}
    (hE' : IsElemAbelian p E') (hc : Nat.card E' = p ^ k) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  set φ : ↥L →* PQuot p L := QuotientGroup.mk' (GLAPPrimeCore p ↥L) with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  set Y : Subgroup ↥L := E'.comap φ with hY
  let π : ↥Y →* ↥E' := (φ.comp Y.subtype).codRestrict E' (fun y => y.2)
  have hπ : Function.Surjective π := by
    intro r
    obtain ⟨y, hy⟩ := hφs r
    exact ⟨⟨y, by show φ y ∈ E'; rw [hy]; exact r.2⟩, Subtype.ext hy⟩
  obtain ⟨P⟩ : Nonempty (Sylow p ↥Y) := inferInstance
  have hRtop : IsPGroup p ↥(⊤ : Subgroup ↥E') :=
    (isPGroup_of_isElemAbelian hE').of_equiv Subgroup.topEquiv.symm
  have hmap : (P : Subgroup ↥Y).map π = ⊤ := by
    have := (P.mapSurjective hπ).is_maximal' hRtop le_top
    rw [Sylow.coe_mapSurjective] at this
    exact this.symm
  set ψ : ↥(P : Subgroup ↥Y) →* ↥E' := π.comp (P : Subgroup ↥Y).subtype with hψ
  have hψs : Function.Surjective ψ := by
    intro r
    have hr : r ∈ (P : Subgroup ↥Y).map π := hmap ▸ Subgroup.mem_top r
    obtain ⟨z, hz, rfl⟩ := hr
    exact ⟨⟨z, hz⟩, rfl⟩
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p L)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp L
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hw : ((z : ↥Y) : ↥L) ∈ GLAPPrimeCore p ↥L := by
      have : φ ((z : ↥Y) : ↥L) = 1 := congrArg Subtype.val hz
      exact (QuotientGroup.eq_one_iff _).1 this
    have hwG : (((z : ↥Y) : ↥L) : G) ∈ GLAPPrimeCoreOf p L := ⟨_, hw, rfl⟩
    obtain ⟨n, hn⟩ := P.isPGroup' z
    have h1 : orderOf (((z : ↥Y) : ↥L) : G) = orderOf z := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    have h2 : orderOf z ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn
    have h3 : orderOf z ∣ Nat.card (GLAPPrimeCoreOf p L) :=
      h1 ▸ Subgroup.orderOf_dvd_natCard _ hwG
    have h4 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes (hcop.pow_left n) h2 h3
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h4)
  set ι : ↥(P : Subgroup ↥Y) →* G :=
    L.subtype.comp (Y.subtype.comp (P : Subgroup ↥Y).subtype) with hι
  have hιi : Function.Injective ι :=
    L.subtype_injective.comp (Y.subtype_injective.comp (P : Subgroup ↥Y).subtype_injective)
  refine ⟨ι.range, ?_, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact ((z : ↥Y) : ↥L).2
  · rintro ⟨_, z₁, rfl⟩ ⟨_, z₂, rfl⟩
    apply Subtype.ext
    show ι z₁ * ι z₂ = ι z₂ * ι z₁
    rw [← map_mul, ← map_mul]
    congr 1
    apply hψi
    rw [map_mul, map_mul]
    exact hE'.1.1.comm (ψ z₁) (ψ z₂)
  · rintro _ ⟨z, rfl⟩
    have hz : z ^ p = 1 := by
      apply hψi
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using hE'.2 _ (ψ z).2)
    rw [← map_pow, hz, map_one]
  · rw [← hc, ← Nat.card_congr (MulEquiv.ofBijective ψ ⟨hψi, hψs⟩).toEquiv]
    exact (Nat.card_congr (MonoidHom.ofInjective hιi).toEquiv).symm

theorem exists_elemAbelian_of_alt9 {J : Subgroup G} (hJ : IsAltPType 3 J 9) :
    ∃ E : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  obtain ⟨e⟩ := hJ
  obtain ⟨E₉, hE₉, hc₉⟩ := alt9_elemAbelian
  refine lift_elemAbelian Nat.prime_three (E' := E₉.map e.symm.toMonoidHom) ?_ ?_
  · refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      apply Subtype.ext
      change e.symm a * e.symm b = e.symm b * e.symm a
      rw [← map_mul, ← map_mul, isElemAbelian_commute hE₉ ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      change (e.symm a) ^ 3 = 1
      rw [← map_pow, hE₉.2 a ha, map_one]
  · rw [← hc₉]
    exact Nat.card_congr (Subgroup.equivMapOfInjective E₉ e.symm.toMonoidHom e.symm.injective).toEquiv.symm

theorem inf_eq_bot_of_alt9 {J E₀ D : Subgroup G} (hJ9 : IsAltPType 3 J 9) (hE₀J : E₀ ≤ J)
    (hJD : J ≤ Subgroup.centralizer (D : Set G)) (hDel : IsElemAbelian 3 D) : E₀ ⊓ D = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgE, hgD⟩
  have hgJ : g ∈ J := hE₀J hgE
  obtain ⟨e⟩ := hJ9
  set gJ : ↥J := ⟨g, hgJ⟩
  have hcen : (QuotientGroup.mk gJ : PQuot 3 J) ∈ Subgroup.center (PQuot 3 J) := by
    rw [Subgroup.mem_center_iff]
    intro z
    induction z using QuotientGroup.induction_on with
    | H j =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show (j : G) * g = g * (j : G)
      exact (Subgroup.mem_centralizer_iff.1 (hJD j.2) g hgD).symm
  have hc2 : e (QuotientGroup.mk gJ) ∈ Subgroup.center ↥(alternatingGroup (Fin 9)) := by
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro z
    have := hcen (e.symm z)
    rw [← e.apply_symm_apply z, ← map_mul, ← map_mul, this]
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc2
  have h1 : (QuotientGroup.mk gJ : PQuot 3 J) = 1 := e.injective (hc2.trans (map_one e).symm)
  have hcore : gJ ∈ GLAPPrimeCore 3 ↥J := (QuotientGroup.eq_one_iff gJ).1 h1
  have hgO : g ∈ GLAPPrimeCoreOf 3 J := ⟨gJ, hcore, rfl⟩
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 J)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf Nat.prime_three J
  have hd1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hDel.2 g hgD)
  have hd2 : orderOf g ∣ Nat.card (GLAPPrimeCoreOf 3 J) := Subgroup.orderOf_dvd_natCard _ hgO
  have : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 this)

theorem exists_rank_five {J D : Subgroup G} (hJ9 : IsAltPType 3 J 9)
    (hJD : J ≤ Subgroup.centralizer (D : Set G)) (hDel : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2) :
    ∃ E : Subgroup G, D ≤ E ∧ E ≤ J ⊔ D ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  obtain ⟨E₀, hE₀J, hE₀, hE₀c⟩ := exists_elemAbelian_of_alt9 hJ9
  have hbot : E₀ ⊓ D = ⊥ := inf_eq_bot_of_alt9 hJ9 hE₀J hJD hDel
  have hDE₀ : D ≤ Subgroup.centralizer (E₀ : Set G) := Subgroup.le_centralizer_iff.1 (hE₀J.trans hJD)
  refine ⟨E₀ ⊔ D, le_sup_right, sup_le_sup_right hE₀J D, ?_, ?_⟩
  · refine IsElemAbelian.sup_of_commute hE₀ hDel (fun e he g hg => ?_)
    exact Subgroup.mem_centralizer_iff.1 (hDE₀ hg) e he
  · have hN : D ≤ Subgroup.normalizer (E₀ : Set G) :=
      hDE₀.trans (Subgroup.centralizer_le_normalizer _)
    have h := card_sup_mul_card_inf_of_le_normalizer hN
    rw [hbot, Subgroup.card_bot, mul_one, hE₀c, hDc] at h
    rw [h]
    norm_num

theorem co1_contra {K E V : Subgroup G} {a : G} (hrk : GLATwoLocalRank 3 G = 4) (hKa : K ≤ cx a)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hEK : E ≤ K) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 4)
    (hVK : V ≤ K) (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hEV : E ≤ Subgroup.normalizer (V : Set G))
    (hEC : E ⊓ Subgroup.centralizer (K : Set G) = ⊥) : False := by
  have haK : a ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.1 (hKa hk)
  have hcomm : ∀ e ∈ E, ∀ b ∈ Subgroup.zpowers a, e * b = b * e := by
    intro e he b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hKa (hEK he))) i)).eq
  have hF : IsElemAbelian 3 (E ⊔ Subgroup.zpowers a) :=
    IsElemAbelian.sup_of_commute hE (isElemAbelian_zpowers ha3) hcomm
  have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hcomm e he a (Subgroup.mem_zpowers a)
  have hinf : E ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff, ← hEC]
    exact inf_le_inf_left E (Subgroup.zpowers_le.2 haK)
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime ha3 ha1
  have hFc : Nat.card ↥(E ⊔ Subgroup.zpowers a) = 3 ^ 5 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hzN
    rw [hinf, Subgroup.card_bot, mul_one, hEc, hza] at h
    rw [h]
    norm_num
  have hFV : E ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (V : Set G) := by
    refine sup_le hEV (Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ ?_))
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.1 (hKa (hVK hv))
  have h := card_le_pow_glaTwoLocalRank Nat.prime_three hF hV1 hV2 hFV
  rw [hFc, hrk] at h
  norm_num at h

end L83

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lemma83 (hc : S8Ctx G p) (hin : Inputs83 G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (h82 : Sp82 G p B x L) :
    ¬ catalogIs (PSimple p L) (sporIs .HN) := by
  intro hHN
  obtain ⟨rfl, hBc, hrk⟩ := L83.rank_step hc hin.i1016HN h82 hHN
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx3 : orderOf x = 3 := L83.orderOf_eq_of_mem hp3 h82.hB.1 h82.hxB h82.hx1
  have hLn : cx x ≤ Subgroup.normalizer (L : Set G) := normalizer_of_unique h82.hL h82.huniq
  obtain ⟨y, T, J, I, hyL, hy3, hDc, -, hT1, hT2, hDT, -, hJ, hJ9, -, hI, hIJ, hI8⟩ :=
    hin.i1423 x L hx3 h82.hL hHN
  set D : Subgroup G := altDxy x y with hDdef
  have hxD : x ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 (h82.hL.1 hyL)).symm
  have hDel : IsElemAbelian 3 D :=
    L83.isElemAbelian_altDxy (hx3 ▸ pow_orderOf_eq_one x) (hy3 ▸ pow_orderOf_eq_one y) hxy
  have hD1 : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hDc
    norm_num at hDc
  have hJC : GLAPComponent 3 (Subgroup.centralizer (D : Set G)) J :=
    L83.comp_centralizer_of_inf hLn hxD hJ
  have hJD : J ≤ Subgroup.centralizer (D : Set G) := hJC.1
  have hDJ : D ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.le_centralizer_iff.1 hJD).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨E, hDE, hEJD, hEel, hEc⟩ := L83.exists_rank_five hJ9 hJD hDel hDc
  have hIN : I ≤ Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (D : Set G) := fun g hg =>
    ⟨(hI.1 hg).2, (hI.1 hg).1.2⟩
  obtain ⟨A, hAD, hAi, hne⟩ := GL83.I_33_3_proved G hc.ctx.charTwo 3 hp3 (by norm_num)
    (Subgroup.normalizer (T : Set G)) D I ⟨T, hT1, hT2, rfl⟩ hD1 hDel hDT hIN
    (L83.not_isPGroup_two_of_alt8 hI8)
  obtain ⟨a, haA, ha1, rfl⟩ := L83.exists_gen_of_index hAD hDc hAi
  have haD : a ∈ D := hAD haA
  have hcz : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) = cx a := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcz] at hne
  have hCDa : Subgroup.centralizer (D : Set G) ≤ cx a :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD)
  have hDa : D ≤ cx a := isElemAbelian_le_centralizer hDel haD
  set Q : Subgroup G := pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ cx a with hQdef
  set S : Subgroup G := ⁅Q, I⁆ with hSdef
  have hSne : S ≠ ⊥ := by
    rw [hSdef, Subgroup.commutator_comm]
    exact hne
  have hQ2 : IsPGroup 2 Q := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hIQ : I ≤ Subgroup.normalizer (Q : Set G) := fun g hg =>
    L83.mem_normalizer_inf (le_normalizer_pCoreOf 2 _ (hIN hg).1)
      (Subgroup.le_normalizer (hCDa (hIN hg).2))
  have hSI : ⁅S, I⁆ = S := commutator_commutator_eq_of_perfect hQ2 (glaPComponent_perfect hI) hIQ
  have hSQ : S ≤ Q := L83.commutator_le_of_le_normalizer hIQ
  have hS2 : IsPGroup 2 S := hQ2.to_le hSQ
  have hIS : I ≤ Subgroup.normalizer (S : Set G) := Subgroup.normalizer_commutator_ge_right Q I
  have hSa : S ≤ cx a := hSQ.trans inf_le_right
  have hKa : CFSG.Open.IsKGroup ↥(cx a) := isKGroup_cx hc.ctx ha1
  have hEa : E ≤ cx a := hEJD.trans (sup_le (hJD.trans hCDa) hDa)
  have hEJ : E ≤ Subgroup.normalizer (J : Set G) := hEJD.trans (sup_le Subgroup.le_normalizer hDJ)
  have hrkX : 3 ^ GLATwoLocalRank 3 ↥(cx a) ≤ Nat.card E := by
    have h1 : GLATwoLocalRank 3 ↥(cx a) ≤ 4 :=
      hrk ▸ glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) (cx a)
    calc 3 ^ GLATwoLocalRank 3 ↥(cx a) ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) h1
      _ ≤ Nat.card E := by rw [hEc]; norm_num
  obtain ⟨d, hdD, -, hDad⟩ := L83.exists_second_gen haD ha1 hDel hDc
  have hCad : cx a ⊓ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) =
      Subgroup.centralizer (D : Set G) := by
    have hcd : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) = cx d := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcd]
    exact le_antisymm (L83.inf_cx_le_centralizer hDad)
      (le_inf hCDa (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD)))
  have hJX : GLAPComponent 3
      (cx a ⊓ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G)) J := by
    rw [hCad]
    exact hJC
  obtain ⟨K, hK, hJK, hEK⟩ := hin.i112 3 hp3 (by norm_num) (cx a) E J d hKa (hDE hdD) hEa hEel hrkX
    hJX hEJ ⟨9, by norm_num, hJ9⟩
  have hSK : S ≤ K := L83.le_of_isSubnormal_of_commutator_eq hK.2.1 hSa (hIJ.trans hJK) hSI
  have hdK : d ∈ Subgroup.normalizer (K : Set G) := hEK (hDE hdD)
  have hd3 : d ^ 3 = 1 := hDel.2 d hdD
  have hJd : GLAPComponent 3 (K ⊓ cx d) J :=
    glaPComponent_of_le hp3 hJC
      (le_inf hJK (hJD.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD))))
      ((inf_le_inf_right _ hK.1).trans (L83.inf_cx_le_centralizer hDad))
  have hdS : d ∈ Subgroup.normalizer (S : Set G) := by
    refine L83.mem_normalizer_commutator ?_ ?_
    · exact L83.mem_normalizer_inf (le_normalizer_pCoreOf 2 _ (hDT hdD)) (Subgroup.le_normalizer (hDa hdD))
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.le_centralizer_iff.1 (hIN.trans inf_le_right) hdD)
  have hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 (cx a))) :=
    odd_core_of_big_rank hp3 h82.hB hEa hEel (by rw [hBc, hEc]; norm_num)
  have hcore : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 (cx a) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp3 hK.2.1
  have hfin : (⁅S, I⁆ : Subgroup G) ≤ GLAPPrimeCoreOf 3 K → False := fun hle =>
    L83.false_of_le_of_odd hSne hS2 ((hSI.symm.le.trans hle).trans hcore) hodd
  rcases hin.i1415 (cx a) K J d hKa hK hdK hd3 hJd hJ9 with ⟨k, hk⟩ | hHNK | hCo1
  · exact hfin (L83.alt_case hin.i2013 hk hdK hd3 hJd hJ9 hIJ hI8 hSK hS2 hIS)
  · exact hfin (hin.i2014 (cx a) K J I S d hK hHNK hdK hd3 hJd hJ9 hIJ hI8 hSK hS2 hIS hdS)
  · obtain ⟨E', V, hE'K, hE'el, hE'c, hVK, hV1, hV2, hE'V, hE'C⟩ := hin.i1016Co1 (cx a) K hK hCo1
    exact L83.co1_contra hrk hK.1 (hDel.2 a haD) ha1 hE'K hE'el hE'c hVK hV1 hV2 hE'V hE'C

end S8

end CFSG.LocalAnalysis.GLTheoremA

