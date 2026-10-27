module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P4Setup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools582
public import CFSG.LocalAnalysis.ComponentClassification.Foote47Inner

public section

namespace CFSG.ComponentClassification.Foote47

open scoped MatrixGroups

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

theorem isConj_of_simple_of_hasDihedralSylowTwo {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : GorensteinWalter.HasDihedralSylowTwo X) (hnab : ∃ a b : X, a * b ≠ b * a) {x y : X}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : ∃ g : X, g * x * g⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ {u : X}, orderOf u = 2 → BenderSuzuki.PFAppendixIII.IsInvolution u := by
    intro u hu
    refine ⟨fun h1 => by rw [h1, orderOf_one] at hu; omega, ?_⟩
    rw [← hu]
    exact pow_orderOf_eq_one u
  have hno : ∀ k : ℕ, k = 2 ∨ k = 4 → ¬ ∃ N : Subgroup X, N.Normal ∧ N.index = k := by
    rintro k hk ⟨N, hN, hidx⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · rw [h1, Subgroup.index_bot] at hidx
      have hp : IsPGroup 2 X := by
        rcases hk with rfl | rfl
        · exact IsPGroup.of_card (n := 1) (by rw [hidx, pow_one])
        · exact IsPGroup.of_card (n := 2) (by rw [hidx]; norm_num)
      have hZ := hp.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h2 | h2
      · exact (nontrivial_iff_ne_bot _).mp hZ h2
      · obtain ⟨a, b, hab⟩ := hnab
        exact hab (mem_center_iff.mp (h2 ▸ mem_top b) a)
    · rw [h1, Subgroup.index_top] at hidx
      omega
  rcases GorensteinWalter.gw_lemma_2_1 hX with h1 | h2 | h3
  · exact h1.2.1 x y (hinv hx) (hinv hy)
  · exact (hno 2 (Or.inl rfl) h2.1).elim
  · exact (hno 4 (Or.inr rfl) h3.1).elim

variable {G : Type} [Group G]

theorem oddBarConj_eq_conj (X : Subgroup G) {x : G} (hx : x ∈ X) :
    GSThmB.oddBarConj X ⟨x, le_normalizer hx⟩ =
      MulAut.conj ((⟨x, hx⟩ : X) : X ⧸ pPrimeCore 2 X) := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [GSThmB.oddBarConj_apply_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  rfl

variable [Finite G] {L : Subgroup G}

theorem exists_mul_of_mem_innerAct_of_isSylowOf {P F : Subgroup G}
    (hP : IsPGroup 2 P) (hR : IsSylowOf 2 (P ⊓ F) F)
    (hZ : center (F ⧸ pPrimeCore 2 F) = ⊥) {x : G}
    (hxP : x ∈ P) (hxI : x ∈ innerAct F) :
    ∃ q ∈ P ⊓ coreActionKernel F, ∃ r ∈ P ⊓ F, x = q * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := F ⧸ pPrimeCore 2 F with hX
  set N := normalizer (F : Set G) with hN
  obtain ⟨hxN, a, ha⟩ := mem_innerAct_iff.mp hxI
  obtain ⟨R₀, hR₀⟩ := hR.exists_sylow_eq_subgroupOf
  set Rbar := R₀.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 F)) with hRbar
  set PN := P.subgroupOf N with hPN
  set Wbar := (PN.map (GSThmB.oddBarConj F)).comap (MulAut.conj : X →* MulAut X) with hWbar
  have hinj := injective_mulAut_conj hZ
  have hWp : IsPGroup 2 Wbar := by
    have h1 : IsPGroup 2 (PN.map (GSThmB.oddBarConj F)) :=
      (hP.comap_subtype (K := N)).map _
    have h2 : Wbar.map (MulAut.conj : X →* MulAut X) ≤ PN.map (GSThmB.oddBarConj F) :=
      map_comap_le _ _
    exact (h1.to_le h2).of_equiv (Wbar.equivMapOfInjective _ hinj).symm
  have hRW : (Rbar : Subgroup X) ≤ Wbar := by
    rintro _ ⟨⟨r, hrF⟩, hr, rfl⟩
    have hr' : r ∈ P ⊓ F := by
      have := hR₀ ▸ hr
      exact this
    refine ⟨⟨r, le_normalizer hrF⟩, (mem_inf.mp hr').1, ?_⟩
    rw [oddBarConj_eq_conj F hrF]
    rfl
  have hWR : Wbar = Rbar := Rbar.is_maximal' hWp hRW
  have haW : a ∈ Wbar := ⟨⟨x, hxN⟩, hxP, ha.symm⟩
  rw [hWR] at haW
  obtain ⟨⟨r, hrF⟩, hr, hra⟩ := haW
  have hr' : r ∈ P ⊓ F := by
    have := hR₀ ▸ hr
    exact this
  have hra' : ((⟨r, hrF⟩ : F) : X) = a := hra
  have hq : r⁻¹ * x ∈ coreActionKernel F := by
    have hrxN : r⁻¹ * x ∈ N := mul_mem (inv_mem (le_normalizer hrF)) hxN
    apply GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one (g := ⟨r⁻¹ * x, hrxN⟩)
    have h1 : (⟨r⁻¹ * x, hrxN⟩ : N) = (⟨r, le_normalizer hrF⟩ : N)⁻¹ * ⟨x, hxN⟩ := rfl
    rw [h1, map_mul, map_inv, oddBarConj_eq_conj F hrF, ← ha, hra', inv_mul_cancel]
  have hqQ : r⁻¹ * x ∈ P ⊓ coreActionKernel F :=
    ⟨mul_mem (P.inv_mem hr'.1) hxP, hq⟩
  refine ⟨r⁻¹ * x, hqQ, r, hr', ?_⟩
  rw [GrSLit.GrS5.commute_of_mem_coreActionKernel hP hqQ.1 hqQ.2 hr'.1 hr'.2]
  group

theorem eq_one_of_mem_inf_coreActionKernel_of_isPGroup {P Q F : Subgroup G}
    (hP : IsPGroup 2 P) (hQ : Q ≤ P) (hQK : Q ≤ coreActionKernel F)
    (hZ : center (F ⧸ pPrimeCore 2 F) = ⊥) {x : G}
    (hxQ : x ∈ Q) (hxF : x ∈ F) : x = 1 :=
  FooteLit.eq_one_of_mem_of_odd hP (odd_card_oddCoreIn F) (hQ hxQ)
    (FooteLit.mem_oddCoreIn_of_mem_coreActionKernel hZ hxF (hQK hxQ))

namespace P4Data

variable {M T S P : Subgroup G} {t z w : G}

theorem footeF_t (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    FootePointedMaximal t (footeF L t) ∧ footeF L t ∈ footeFamilyOf L := by
  obtain ⟨-, -, h1, h2⟩ := foote_lemma_4_5_i h d.c.hv.hM d.c.hv.ht d.c.hv.htC
  exact ⟨h1, h2⟩

theorem centralizer_le_normalizer_t (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    centralizer ({t} : Set G) ≤ normalizer (footeF L t : Set G) :=
  le_normalizer_of_mem_footeFamilyOf h.huniq (d.footeF_t h).1.1 (d.footeF_t h).2

theorem footeF_t_le (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    footeF L t ≤ centralizer ({t} : Set G) :=
  (d.footeF_t h).1.1.2.1

theorem P_le_normalizer (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    P ≤ normalizer (footeF L t : Set G) :=
  d.c.hPsyl.le.trans (d.centralizer_le_normalizer_t h)

theorem isSylowOf_R (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    IsSylowOf 2 (P ⊓ footeF L t) (footeF L t) :=
  d.c.hPsyl.inf_of_le_normalizer (d.footeF_t_le h) (d.centralizer_le_normalizer_t h)

theorem quotient_t (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    IsSimpleGroup (footeF L t ⧸ pPrimeCore 2 (footeF L t)) ∧
      Nonempty (footeF L t ⧸ pPrimeCore 2 (footeF L t) ≃* L ⧸ Open.fusionZStar L) :=
  isSimpleGroup_quotient_of_mem_footeFamilyOf h.hGA h.hGC h.hSA h.footeFamilyType h.hrank2
    (d.footeF_t h).1.1 (d.footeF_t h).2

theorem exists_mul_ne_t (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    ∃ a b : footeF L t ⧸ pPrimeCore 2 (footeF L t), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := d.c.hv.hM.exists_mul_ne h
  obtain ⟨-, ⟨e₁⟩⟩ := d.c.hv.hM.quotient h
  obtain ⟨-, ⟨e₂⟩⟩ := d.quotient_t h
  set e := e₁.trans e₂.symm
  exact ⟨e a, e b, fun h1 => hab (e.injective (by rw [map_mul, map_mul, h1]))⟩

theorem center_eq_bot_t (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    center (footeF L t ⧸ pPrimeCore 2 (footeF L t)) = ⊥ := by
  obtain ⟨hs, -⟩ := d.quotient_t h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (footeF L t ⧸
    pPrimeCore 2 (footeF L t))) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := d.exists_mul_ne_t h
    exact hab (mem_center_iff.mp (h1 ▸ mem_top b) a)

omit [Finite G] in
theorem Q_le (d : P4Data L M T S P t z w) :
    T ⊓ centralizer ({t} : Set G) ≤ coreActionKernel (footeF L t) := d.c.hQF

omit [Finite G] in
theorem Q_le_P (d : P4Data L M T S P t z w) : T ⊓ centralizer ({t} : Set G) ≤ P := by
  rw [d.c.hP, d.c.hT]
  exact inf_le_inf_right _ inf_le_left

theorem eq_one_of_mem_Q_Ft (h : FooteSec4 G L) (d : P4Data L M T S P t z w) {x : G}
    (hxQ : x ∈ T ⊓ centralizer ({t} : Set G)) (hxF : x ∈ footeF L t) : x = 1 := by
  have hxO := mem_oddCoreIn_of_mem_coreActionKernel (d.center_eq_bot_t h) hxF (d.Q_le hxQ)
  exact eq_one_of_mem_of_odd (d.c.hPsyl.isPGroup.to_le d.Q_le_P) (odd_card_oddCoreIn _) hxQ hxO

theorem comm_QR (d : P4Data L M T S P t z w) {q r : G}
    (hq : q ∈ T ⊓ centralizer ({t} : Set G)) (hr : r ∈ P ⊓ footeF L t) : q * r = r * q := by
  have hqP := d.Q_le_P hq
  have hqC := d.Q_le hq
  have h1 : r⁻¹ * q⁻¹ * r * q ∈ oddCoreIn (footeF L t) := hqC.2 r (mem_inf.mp hr).2
  have h2 : r⁻¹ * q⁻¹ * r * q ∈ P ⊓ footeF L t := by
    have h3 : q⁻¹ * r * q ∈ P ⊓ footeF L t := by
      have h4 := (mem_normalizer_iff.mp (inv_mem hqC.1) r).mp (mem_inf.mp hr).2
      rw [inv_inv] at h4
      exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hqP) (mem_inf.mp hr).1) hqP, h4⟩
    rw [show r⁻¹ * q⁻¹ * r * q = r⁻¹ * (q⁻¹ * r * q) by group]
    exact mul_mem (inv_mem hr) h3
  have h5 := eq_one_of_mem_of_odd (d.c.hPsyl.isPGroup.to_le inf_le_left)
    (odd_card_oddCoreIn _) h2 h1
  calc q * r = q * r * (r⁻¹ * q⁻¹ * r * q) := by rw [h5, mul_one]
    _ = r * q := by group

omit [Finite G] in
theorem w_mem_R (d : P4Data L M T S P t z w) : w ∈ P ⊓ footeF L t := by
  refine mem_inf.mpr ⟨?_, d.hwF⟩
  rw [d.c.hP]
  have hTS : T ≤ S := d.c.hT ▸ inf_le_left
  exact mem_inf.mpr ⟨d.hwS, mem_centralizer_singleton_iff.mpr (d.hwc t (hTS d.c.htT)).symm⟩

omit [Finite G] in
theorem w_comm (d : P4Data L M T S P t z w) {q : G} (hq : q ∈ T ⊓ centralizer ({t} : Set G)) :
    q * w = w * q := by
  have hTS : T ≤ S := d.c.hT ▸ inf_le_left
  exact d.hwc q (hTS (mem_inf.mp hq).1)

end P4Data

theorem exists_conj_mem_inf_centralizer_of_isConj_oddQuotient {F Q : Subgroup G}
    (hQp : IsPGroup 2 Q) (hQK : Q ≤ coreActionKernel F) {w r : G}
    (hwF : w ∈ F) (hrF : r ∈ F) (hw : orderOf w = 2) (hr : orderOf r = 2)
    (hwC : w ∈ centralizer (Q : Set G)) (hrC : r ∈ centralizer (Q : Set G))
    (hconj : IsConj (QuotientGroup.mk (⟨w, hwF⟩ : F) : F ⧸ pPrimeCore 2 F)
      (QuotientGroup.mk (⟨r, hrF⟩ : F))) :
    ∃ y ∈ F, y ∈ centralizer (Q : Set G) ∧ r = y * w * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X := F ⧸ pPrimeCore 2 F
  obtain ⟨ybar, hy⟩ := isConj_iff.mp hconj
  obtain ⟨⟨y₀, hy₀F⟩, rfl⟩ := QuotientGroup.mk_surjective ybar
  have hQN : Q ≤ normalizer ((oddCoreIn F : Subgroup G) : Set G) := fun q hq =>
    mem_normalizer_oddCoreIn (hQK hq).1
  have hm : ∀ q ∈ Q, y₀⁻¹ * (q * y₀ * q⁻¹) ∈ oddCoreIn F := by
    intro q hq
    have h1 := (inv_mem (hQK hq)).2 y₀ hy₀F
    rw [inv_inv] at h1
    have h2 : y₀⁻¹ * (q * y₀ * q⁻¹) = y₀⁻¹ * q * y₀ * q⁻¹ := by group
    rw [h2]
    exact h1
  obtain ⟨o, hoO, hy₁⟩ := exists_mem_centralizer_of_isPGroup hQp hQN (odd_card_oddCoreIn F) hm
  have hoF : o ∈ F := map_subtype_le _ hoO
  set y₁ := y₀ * o with hy₁def
  have hy₁F : y₁ ∈ F := mul_mem hy₀F hoF
  set b := y₁ * w * y₁⁻¹ with hb
  have hbF : b ∈ F := mul_mem (mul_mem hy₁F hwF) (inv_mem hy₁F)
  have hrb : r⁻¹ * b ∈ oddCoreIn F := by
    have h1 : ((⟨r, hrF⟩ : F) : X) = ((⟨b, hbF⟩ : F) : X) := by
      rw [← hy]
      have ho1 : ((⟨o, hoF⟩ : F) : X) = 1 := by
        rw [QuotientGroup.eq_one_iff, mem_pPrimeCore_iff_mem_oddCoreIn]
        exact hoO
      have h2 : (⟨b, hbF⟩ : F) = ⟨y₀, hy₀F⟩ * ⟨o, hoF⟩ * ⟨w, hwF⟩ * (⟨y₀, hy₀F⟩ * ⟨o, hoF⟩)⁻¹ :=
        Subtype.ext (by simp [hb, hy₁def])
      rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_mul, ho1, mul_one]
    rw [QuotientGroup.eq, mem_pPrimeCore_iff_mem_oddCoreIn] at h1
    simpa using h1
  have hr2 : r * r = 1 := by rw [← sq, ← hr]; exact pow_orderOf_eq_one r
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hw2 : w * w = 1 := by rw [← sq, ← hw]; exact pow_orderOf_eq_one w
  have hb2 : b * b = 1 := by
    rw [hb]
    calc y₁ * w * y₁⁻¹ * (y₁ * w * y₁⁻¹) = y₁ * (w * w) * y₁⁻¹ := by group
      _ = 1 := by rw [hw2, mul_one, mul_inv_cancel]
  have hodd : Odd (orderOf (r * b)) := by
    rw [← hri]
    exact odd_orderOf_of_mem_of_odd (odd_card_oddCoreIn F) hrb
  obtain ⟨u, hu, hbu⟩ := exists_conj_of_odd_orderOf_mul hr2 hb2 hodd
  have hbC : b ∈ centralizer (Q : Set G) := mul_mem (mul_mem hy₁ hwC) (inv_mem hy₁)
  have huC : u ∈ centralizer (Q : Set G) := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    exact zpow_mem (mul_mem hrC hbC) k
  have huF : u ∈ F := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    refine zpow_mem ?_ k
    rw [← hri]
    exact map_subtype_le _ hrb
  refine ⟨u * y₁, mul_mem huF hy₁F, mul_mem huC hy₁, ?_⟩
  calc r = u * (u⁻¹ * r * u) * u⁻¹ := by group
    _ = u * b * u⁻¹ := by rw [← hbu]
    _ = u * y₁ * w * (u * y₁)⁻¹ := by rw [hb]; group

theorem inv_cases_of_isSylowOf {T P F : Subgroup G} {t z w : G} {Q0 : Subgroup G}
    (hP : IsPGroup 2 P) (hR : IsSylowOf 2 (P ⊓ F) F)
    (hZ : center (F ⧸ pPrimeCore 2 F) = ⊥)
    (hQP : P ⊓ coreActionKernel F = T ⊓ centralizer ({t} : Set G))
    (hd : TwoData T t z Q0) (ht : orderOf t = 2)
    (hconj : ∀ r ∈ P ⊓ F, orderOf r = 2 →
      ∃ y ∈ F, y ∈ centralizer ((T ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ∧
        r = y * w * y⁻¹)
    {x : G} (hxP : x ∈ P) (hxI : x ∈ innerAct F) (hx : orderOf x = 2) :
    (x = z ∨ x = t ∨ x = t * z) ∨
      ∃ q r : G, (q = 1 ∨ q = z ∨ q = t ∨ q = t * z) ∧ r ∈ P ⊓ F ∧ orderOf r = 2 ∧
        x = q * r ∧ ∃ y ∈ F,
          y ∈ centralizer ((T ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ∧
            x = y * (q * w) * y⁻¹ := by
  have htt : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hQleP : T ⊓ centralizer ({t} : Set G) ≤ P := by
    rw [← hQP]; exact inf_le_left
  have hQK : T ⊓ centralizer ({t} : Set G) ≤ coreActionKernel F := by
    rw [← hQP]; exact inf_le_right
  obtain ⟨q, hqPK, r, hrR, hxqr⟩ :=
    exists_mul_of_mem_innerAct_of_isSylowOf hP hR hZ hxP hxI
  have hqQ : q ∈ T ⊓ centralizer ({t} : Set G) := hQP ▸ hqPK
  have hqP : q ∈ P := hQleP hqQ
  have hqK : q ∈ coreActionKernel F := hQK hqQ
  have hrP : r ∈ P := (mem_inf.mp hrR).1
  have hrF : r ∈ F := (mem_inf.mp hrR).2
  have hqr : q * r = r * q :=
    GrSLit.GrS5.commute_of_mem_coreActionKernel hP hqP hqK hrP hrF
  have hx2 : (q * r) * (q * r) = 1 := by
    rw [← hxqr, ← sq, ← hx]; exact pow_orderOf_eq_one x
  have hsq : q * q * (r * r) = 1 := by
    calc q * q * (r * r) = q * (q * r) * r := by group
      _ = q * (r * q) * r := by rw [hqr]
      _ = (q * r) * (q * r) := by group
      _ = 1 := hx2
  have hq2 : q * q = 1 := by
    have h1 : q * q = (r * r)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    have h2 : q * q ∈ F := by
      rw [h1]
      exact inv_mem (mul_mem hrF hrF)
    exact eq_one_of_mem_inf_coreActionKernel_of_isPGroup hP hQleP hQK hZ
      (mul_mem hqQ hqQ) h2
  have hr2 : r * r = 1 := by
    rw [hq2, one_mul] at hsq
    exact hsq
  have hq4 : q = 1 ∨ q = z ∨ q = t ∨ q = t * z := by
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · exact Or.inr (hd.inv_cases htt hqQ
        (orderOf_eq_prime (by rw [sq]; exact hq2) hq1))
  by_cases hr1 : r = 1
  · left
    have hxq : x = q := by rw [hxqr, hr1, mul_one]
    rw [hxq] at hx ⊢
    rcases hq4 with h1 | h1 | h1 | h1
    · rw [h1, orderOf_one] at hx; omega
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · right
    have hro : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
    obtain ⟨y, hyF, hyC, hry⟩ := hconj r hrR hro
    refine ⟨q, r, hq4, hrR, hro, hxqr, y, hyF, hyC, ?_⟩
    have hyq : y * q = q * y := (mem_centralizer_iff.mp hyC q hqQ).symm
    rw [hxqr, hry]
    calc q * (y * w * y⁻¹) = (q * y) * w * y⁻¹ := by group
      _ = (y * q) * w * y⁻¹ := by rw [hyq]
      _ = y * (q * w) * y⁻¹ := by group

namespace P4Data

variable {M T S P : Subgroup G} {t z w : G}

theorem exists_conj_w (h : FooteSec4 G L) (d : P4Data L M T S P t z w) {r : G}
    (hrR : r ∈ P ⊓ footeF L t) (hr : orderOf r = 2) :
    ∃ y ∈ footeF L t, y ∈ centralizer ((T ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ∧
      r = y * w * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := footeF L t with hF
  set X := F ⧸ pPrimeCore 2 F with hX
  set Q := T ⊓ centralizer ({t} : Set G) with hQ
  obtain ⟨hs, ⟨ε⟩⟩ := d.quotient_t h
  have hrF : r ∈ F := (mem_inf.mp hrR).2
  have hwF : w ∈ F := d.hwF
  have himg : ∀ {u : G} (huR : u ∈ P ⊓ F), orderOf u = 2 →
      orderOf ((⟨u, (mem_inf.mp huR).2⟩ : F) : X) = 2 := by
    intro u huR hu
    exact UnbalancedLayer.orderOf_mk_eq_two
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (by rw [Subgroup.orderOf_mk]; exact hu)
  have hdih : GorensteinWalter.HasDihedralSylowTwo X :=
    OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv ε
      (hasDihedralSylowTwo_of_footeFamilyType h.footeFamilyType)
  obtain ⟨ybar, hy⟩ := isConj_of_simple_of_hasDihedralSylowTwo hdih (d.exists_mul_ne_t h)
    (himg d.w_mem_R d.hw) (himg hrR hr)
  exact exists_conj_mem_inf_centralizer_of_isConj_oddQuotient
    (d.c.hPsyl.isPGroup.to_le d.Q_le_P) d.Q_le d.hwF hrF d.hw hr
    (mem_centralizer_iff.mpr fun q hq => d.w_comm hq)
    (mem_centralizer_iff.mpr fun q hq => d.comm_QR hq hrR)
    (isConj_iff.mpr ⟨ybar, hy⟩)

theorem inv_cases (h : FooteSec4 G L) (d : P4Data L M T S P t z w) {x : G} (hxP : x ∈ P)
    (hxI : x ∈ innerAct (footeF L t)) (hx : orderOf x = 2) :
    (x = z ∨ x = t ∨ x = t * z) ∨
      ∃ q r : G, (q = 1 ∨ q = z ∨ q = t ∨ q = t * z) ∧ r ∈ P ⊓ footeF L t ∧ orderOf r = 2 ∧
        x = q * r ∧ ∃ y ∈ footeF L t,
          y ∈ centralizer ((T ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ∧
            x = y * (q * w) * y⁻¹ := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  exact inv_cases_of_isSylowOf d.c.hPsyl.isPGroup (d.isSylowOf_R h)
    (d.center_eq_bot_t h) d.c.hQP hd d.c.hv.ht
    (fun r hr hro => d.exists_conj_w h hr hro) hxP hxI hx

end P4Data

end CFSG.ComponentClassification.Foote47
