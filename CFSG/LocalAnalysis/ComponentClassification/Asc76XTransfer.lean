module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XSetting
public import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingMap

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76

variable {G : Type} [Group G] [Finite G]

theorem oddCore_quotient_oddCore (H : Type*) [Group H] [Finite H] :
    CFSG.oddCore (H ⧸ CFSG.oddCore H) = ⊥ := by
  set N := (CFSG.oddCore (H ⧸ CFSG.oddCore H)).comap (QuotientGroup.mk' (CFSG.oddCore H))
  have hNn : N.Normal := (CFSG.oddCore_normal _).comap _
  have hNodd : Odd (Nat.card N) := by
    have h := QuotientGroup.card_preimage_mk (CFSG.oddCore H)
      ((CFSG.oddCore (H ⧸ CFSG.oddCore H) : Subgroup _) : Set (H ⧸ CFSG.oddCore H))
    have h' : Nat.card N = Nat.card (CFSG.oddCore H) *
        Nat.card (CFSG.oddCore (H ⧸ CFSG.oddCore H)) := h
    rw [h']
    exact (CFSG.ComponentClassification.OddCore.odd_card H).mul
      (CFSG.ComponentClassification.OddCore.odd_card _)
  have hNO : N ≤ CFSG.oddCore H := le_sSup ⟨hNn, hNodd⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have : h ∈ CFSG.oddCore H := hNO hx
  rw [mem_bot, QuotientGroup.eq_one_iff]
  exact this

abbrev BarGroup (X : Subgroup G) : Type := X ⧸ CFSG.oddCore X

abbrev barMk (X : Subgroup G) : X →* BarGroup X := QuotientGroup.mk' (CFSG.oddCore X)

@[expose] def bar (X J : Subgroup G) : Subgroup (BarGroup X) := (J.subgroupOf X).map (barMk X)

omit [Finite G] in
theorem ker_barMk (X : Subgroup G) : (barMk X).ker = CFSG.oddCore X := QuotientGroup.ker_mk' _

theorem odd_card_ker_barMk (X : Subgroup G) : Odd (Nat.card (barMk X).ker) := by
  rw [ker_barMk]
  exact CFSG.ComponentClassification.OddCore.odd_card X

theorem odd_card_oddCoreIn (X : Subgroup G) : Odd (Nat.card (oddCoreIn X)) := by
  rw [oddCoreIn, card_map_of_injective X.subtype_injective]
  exact CFSG.ComponentClassification.OddCore.odd_card X

omit [Finite G] in
theorem oddCoreIn_le (X : Subgroup G) : oddCoreIn X ≤ X := map_subtype_le _

omit [Finite G] in
theorem le_normalizer_oddCoreIn (X : Subgroup G) :
    X ≤ normalizer ((oddCoreIn X : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹, (CFSG.oddCore_normal X).conj_mem z hz _, by simp⟩
  · rintro ⟨z, hz, hzy⟩
    have hyX : y ∈ X := by
      have h1 : x * y * x⁻¹ ∈ X := hzy ▸ z.2
      have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hx) h1) hx
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    have h2 := (CFSG.oddCore_normal X).conj_mem z hz ⟨x, hx⟩⁻¹
    have e : (⟨x, hx⟩⁻¹ * z * (⟨x, hx⟩⁻¹)⁻¹ : X) = ⟨y, hyX⟩ := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv, inv_inv]
      rw [show (z : G) = x * y * x⁻¹ from hzy]
      group
    rwa [e] at h2

omit [Finite G] in
theorem barMk_eq_one_iff {X : Subgroup G} (y : X) :
    barMk X y = 1 ↔ (y : G) ∈ oddCoreIn X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [show y = z from Subtype.ext hzy.symm]

omit [Finite G] in
theorem barMk_mem_bar {X J : Subgroup G} {x : X} (hx : (x : G) ∈ J) : barMk X x ∈ bar X J :=
  ⟨x, hx, rfl⟩

section Sylow

variable {H : Type*} [Group H]

theorem isSylowOf_iff_card [Finite H] {p : ℕ} [Fact p.Prime] {P K : Subgroup H} :
    IsSylowOf p P K ↔ P ≤ K ∧ Nat.card P = p ^ (Nat.card K).factorization p := by
  constructor
  · rintro ⟨Q, rfl⟩
    refine ⟨map_subtype_le _, ?_⟩
    rw [card_map_of_injective K.subtype_injective]
    exact Q.card_eq_multiplicity
  · rintro ⟨hPK, hcard⟩
    have hc : Nat.card (P.subgroupOf K) = p ^ (Nat.card K).factorization p := by
      rw [← hcard]
      exact Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv
    exact ⟨Sylow.ofCard _ hc, by rw [Sylow.coe_ofCard, map_subgroupOf_eq_of_le hPK]⟩

theorem isElemAbelian_of_mulEquiv {H' : Type*} [Group H'] {A : Subgroup H} {B : Subgroup H'}
    {p : ℕ} (e : A ≃* B) (h : IsElemAbelian p A) : IsElemAbelian p B := by
  refine ⟨⟨⟨fun a b => e.symm.injective (by
    rw [map_mul, map_mul, h.1.is_comm.comm])⟩⟩, fun x hx => ?_⟩
  have h1 : ((e.symm ⟨x, hx⟩ : A) : H) ^ p = 1 := h.2 _ (e.symm ⟨x, hx⟩).2
  have h2 : (e.symm ⟨x, hx⟩) ^ p = 1 := Subtype.ext (by simpa using h1)
  have h3 : (⟨x, hx⟩ : B) ^ p = 1 := by
    rw [← e.apply_symm_apply ⟨x, hx⟩, ← map_pow, h2, map_one]
  simpa using congrArg Subtype.val h3

end Sylow

theorem card_bar_mul {X J : Subgroup G} (hJX : J ≤ X) :
    ∃ m : ℕ, Odd m ∧ Nat.card (bar X J) * m = Nat.card J := by
  refine ⟨Nat.card ((barMk X).ker ⊓ J.subgroupOf X : Subgroup X), ?_, ?_⟩
  · exact (odd_card_ker_barMk X).of_dvd_nat (card_dvd_of_le inf_le_left)
  · rw [bar, card_map_mul_card_inf_ker]
    exact Nat.card_congr (subgroupOfEquivOfLe hJX).toEquiv

theorem factorization_card_bar {X J : Subgroup G} (hJX : J ≤ X) :
    (Nat.card (bar X J)).factorization 2 = (Nat.card J).factorization 2 := by
  obtain ⟨m, hm, h⟩ := card_bar_mul hJX
  rw [← h, Nat.factorization_mul Nat.card_pos.ne' hm.pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat, add_zero]

theorem card_bar_of_pGroup {X P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup 2 P) :
    Nat.card (bar X P) = Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, h⟩ := card_bar_mul hPX
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hdvd : m ∣ 2 ^ n := ⟨Nat.card (bar X P), by rw [← hn, ← h, mul_comm]⟩
  have hcop : Nat.Coprime m (2 ^ n) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  rw [← h, Nat.Coprime.eq_one_of_dvd hcop hdvd, mul_one]

omit [Finite G] in
theorem isPGroup_bar {X P : Subgroup G} (hP : IsPGroup 2 P) : IsPGroup 2 (bar X P) :=
  (hP.comap_of_injective X.subtype X.subtype_injective).map _

omit [Finite G] in
theorem bar_mono {X J L : Subgroup G} (h : J ≤ L) : bar X J ≤ bar X L :=
  map_mono fun _ hx => h hx

omit [Finite G] in
theorem bar_rightConjugate (X J : Subgroup G) (x : X) :
    bar X (rightConjugate J x) = rightConjugate (bar X J) (barMk X x) := by
  have h1 : (rightConjugate J x).subgroupOf X = rightConjugate (J.subgroupOf X) x := by
    ext y
    rw [mem_subgroupOf, mem_rightConjugate_iff, mem_rightConjugate_iff, mem_subgroupOf]
    simp
  rw [bar, h1, bar]
  unfold rightConjugate
  rw [map_map, map_map]
  congr 1

theorem exists_pGroup_lift {X J : Subgroup G} {P : Subgroup (BarGroup X)}
    (hP : IsPGroup 2 P) (hPJ : P ≤ bar X J) :
    ∃ P' : Subgroup G, P' ≤ J ∧ IsPGroup 2 P' ∧ bar X P' = P ∧ Nat.card P' = Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ : Subgroup X := P.comap (barMk X) ⊓ J.subgroupOf X with hP₀
  have hmap : P₀.map (barMk X) = P := by
    apply le_antisymm
    · exact (map_mono inf_le_left).trans (map_comap_le _ _)
    · intro y hy
      obtain ⟨j, hj, rfl⟩ := hPJ hy
      exact ⟨j, ⟨hy, hj⟩, rfl⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 P₀))
  set S₀ : Subgroup X := (Q : Subgroup P₀).map P₀.subtype with hS₀
  have hS₀P₀ : S₀ ≤ P₀ := map_subtype_le _
  have hS₀2 : IsPGroup 2 S₀ := Q.isPGroup'.map _
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  have hcardP₀ := card_map_mul_card_inf_ker (barMk X) P₀
  rw [hmap, ha] at hcardP₀
  have hoddk : Odd (Nat.card ((barMk X).ker ⊓ P₀ : Subgroup X)) :=
    (odd_card_ker_barMk X).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hfac : (Nat.card P₀).factorization 2 = a := by
    rw [← hcardP₀, Nat.factorization_mul (by positivity) hoddk.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hoddk.not_two_dvd_nat, add_zero,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hS₀card : Nat.card S₀ = Nat.card P := by
    rw [hS₀, card_map_of_injective P₀.subtype_injective, Q.card_eq_multiplicity, hfac, ha]
  have hinj : Nat.card (S₀.map (barMk X)) = Nat.card S₀ := by
    obtain ⟨m, hm, h⟩ : ∃ m : ℕ, Odd m ∧ Nat.card (S₀.map (barMk X)) * m = Nat.card S₀ :=
      ⟨_, (odd_card_ker_barMk X).of_dvd_nat (card_dvd_of_le inf_le_left),
        card_map_mul_card_inf_ker _ _⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS₀2
    have hdvd : m ∣ 2 ^ n := ⟨Nat.card (S₀.map (barMk X)), by rw [← hn, ← h, mul_comm]⟩
    have hcop : Nat.Coprime m (2 ^ n) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
    rw [← h, Nat.Coprime.eq_one_of_dvd hcop hdvd, mul_one]
  have hSP : S₀.map (barMk X) = P := by
    refine eq_of_le_of_card_ge ((map_mono hS₀P₀).trans hmap.le) ?_
    rw [hinj, hS₀card]
  refine ⟨S₀.map X.subtype, ?_, hS₀2.map _, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hS₀P₀ hy).2
  · rw [bar, ← hSP]
    congr 1
    exact comap_map_eq_self_of_injective X.subtype_injective S₀
  · rw [card_map_of_injective X.subtype_injective, hS₀card]

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem oddCoreIn_le_normalizer (hΩ : Sec3Setting Ω) {X L : Subgroup G} (hL : L ∈ Ω)
    (hLX : L ≤ X) : oddCoreIn X ≤ normalizer (L : Set G) :=
  hΩ.le_normalizer_of_odd hL (odd_card_oddCoreIn X) (hLX.trans (le_normalizer_oddCoreIn X))

theorem mem_of_barMk_mem (hΩ : Sec3Setting Ω) {X L : Subgroup G} (hL : L ∈ Ω) (hLX : L ≤ X)
    {x : X} {k : ℕ} (hxk : (x : G) ^ (2 ^ k) = 1) (hx : barMk X x ∈ bar X L) : (x : G) ∈ L := by
  obtain ⟨l, hl, hlx⟩ := hx
  have hlx' : (l⁻¹ * x : X) ∈ (barMk X).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]
  rw [ker_barMk] at hlx'
  have hO : ((l : G)⁻¹ * x) ∈ oddCoreIn X := ⟨_, hlx', rfl⟩
  have hmem : (x : G) ∈ L ⊔ oddCoreIn X := by
    have : (x : G) = (l : G) * ((l : G)⁻¹ * x) := by group
    rw [this]
    exact mul_mem (mem_sup_left hl) (mem_sup_right hO)
  exact mem_of_two_element (hΩ.oddCoreIn_le_normalizer hL hLX) (odd_card_oddCoreIn X) hmem
    hxk

theorem eq_of_bar_eq (hΩ : Sec3Setting Ω) {X J L : Subgroup G} (hJ : J ∈ Ω) (hL : L ∈ Ω)
    (hJX : J ≤ X) (hLX : L ≤ X) (h : bar X J = bar X L) : J = L := by
  obtain ⟨x, hxJ, hx⟩ := hΩ.exists_involution_mem hJ
  have hxL : x ∈ L := by
    have h1 : barMk X ⟨x, hJX hxJ⟩ ∈ bar X L := h ▸ barMk_mem_bar hxJ
    exact hΩ.mem_of_barMk_mem hL hLX (k := 1) (by rw [pow_one, ← hx]; exact pow_orderOf_eq_one x)
      h1
  exact hΩ.eq_of_mem_of_mem hJ hL hxJ hxL hx

end CFSG.ComponentClassification.Asc76.Sec3Setting

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76

variable {G : Type} [Group G] [Finite G]

theorem even_card_of_two_element {H : Type*} [Group H] [Finite H] {A : Subgroup H} {y : H}
    (hy : y ∈ A) (hy1 : y ≠ 1) {i : ℕ} (hyi : y ^ (2 ^ i) = 1) : Even (Nat.card A) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hyi)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.mp (by rw [hj, pow_zero]))
  rw [even_iff_two_dvd]
  exact (dvd_pow_self 2 hj0).trans (hj ▸ orderOf_dvd_natCard A hy)

theorem isPGroup_zpowers_of_two_element {H : Type*} [Group H] {y : H} {i : ℕ}
    (hyi : y ^ (2 ^ i) = 1) : IsPGroup 2 (zpowers y) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  refine ⟨i, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyi, one_zpow]

theorem zpowers_ne_bot_of_ne_one' {H : Type*} [Group H] {y : H} (hy : y ≠ 1) :
    zpowers y ≠ ⊥ := fun h => hy (by
  have : y ∈ zpowers y := mem_zpowers y
  rwa [h, mem_bot] at this)

noncomputable def barEquiv {X R : Subgroup G} (hRX : R ≤ X) (hR : IsPGroup 2 R) :
    R ≃* bar X R :=
  (subgroupOfEquivOfLe hRX).symm.trans
    (MulEquiv.ofBijective ((barMk X).subgroupMap (R.subgroupOf X))
      ⟨(injective_iff_map_eq_one _).mpr fun r hr => by
        have hr' : barMk X (r : X) = 1 := congrArg Subtype.val hr
        obtain ⟨k, hk⟩ := hR ⟨((r : X) : G), r.2⟩
        have hk' : ((r : X) : G) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
        have h1 : (r : X) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk')
        exact Subtype.ext (eq_one_of_two_element_of_ker (barMk X) (odd_card_ker_barMk X) h1 hr'),
        (barMk X).subgroupMap_surjective _⟩)

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_normalizer_of_barMk (hΩ : Sec3Setting Ω) {X L : Subgroup G} (hL : L ∈ Ω)
    (hLX : L ≤ X) {x : X} (hx : barMk X x ∈ normalizer ((bar X L : Subgroup _) : Set _)) :
    (x : G) ∈ normalizer (L : Set G) := by
  have h1 : bar X (rightConjugate L x) = bar X L := by
    rw [bar_rightConjugate]
    exact (rightConjugate_eq_self_iff _ _).mpr hx
  have hLx : rightConjugate L x ≤ X := fun y hy => by
    rw [mem_rightConjugate_iff] at hy
    have h2 : (x : G) * y * (x : G)⁻¹ ∈ X := hLX hy
    have : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem x.2) h2) x.2
  have h3 := hΩ.eq_of_bar_eq (hΩ.conj_mem L hL x) hL hLx hLX h1
  exact (rightConjugate_eq_self_iff L x).mp h3

theorem barSetting (hΩ : Sec3Setting Ω) {α : Set (Subgroup G)} (hαΩ : α ⊆ Ω)
    (hαinv : ∀ J ∈ α, ∀ x ∈ sSup α, rightConjugate J x ∈ α) :
    Sec3Setting (bar (sSup α) '' α) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := sSup α with hX
  have hJX : ∀ J ∈ α, J ≤ X := fun J hJ => le_sSup hJ
  refine ⟨oddCore_quotient_oddCore _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨J, hJ, rfl⟩ g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore X) g
    exact ⟨rightConjugate J x, hαinv J hJ x x.2, bar_rightConjugate _ _ _⟩
  ·
    have hC : sSup ((fun J : Subgroup G => J.subgroupOf X) '' α) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hle : X ≤ (sSup ((fun J : Subgroup G => J.subgroupOf X) '' α)).map X.subtype := by
        refine sSup_le fun J hJ => ?_
        rw [← map_subgroupOf_eq_of_le (hJX J hJ)]
        exact map_mono (le_sSup ⟨J, hJ, rfl⟩)
      obtain ⟨z, hz, hzy⟩ := hle y.2
      rwa [show y = z from Subtype.ext hzy.symm]
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore X) q
    have hy : y ∈ sSup ((fun J : Subgroup G => J.subgroupOf X) '' α) := hC ▸ mem_top y
    have hmap : (sSup ((fun J : Subgroup G => J.subgroupOf X) '' α)).map (barMk X) ≤
        sSup (bar X '' α) := by
      rw [map_le_iff_le_comap]
      refine sSup_le ?_
      rintro _ ⟨J, hJ, rfl⟩
      rw [← map_le_iff_le_comap]
      exact le_sSup ⟨J, hJ, rfl⟩
    exact hmap (mem_map_of_mem _ hy)
  ·
    rintro _ ⟨J, hJ, rfl⟩ _ ⟨L, hL, rfl⟩ hne heven
    have hJL : J ≠ L := fun h => hne (h ▸ rfl)
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    have hy'L : (y' : BarGroup X) ∈ bar X L := (mem_inf.mp y'.2).1
    have hy'N := (mem_inf.mp y'.2).2
    have hy'o : orderOf (y' : BarGroup X) = 2 := by rw [orderOf_coe]; exact hy'
    have hy'2 : (y' : BarGroup X) ^ (2 ^ 1) = 1 := by
      rw [pow_one, ← hy'o]
      exact pow_orderOf_eq_one _
    obtain ⟨y, hyL, ⟨i, hyi⟩, hyy'⟩ := exists_two_element_preimage (barMk X) hy'L hy'2
    have hyN : (y : G) ∈ normalizer (J : Set G) :=
      hΩ.mem_normalizer_of_barMk (hαΩ hJ) (hJX J hJ) (by rw [hyy']; exact hy'N)
    have hy1 : (y : G) ≠ 1 := by
      intro h
      have h1 : y = 1 := Subtype.ext h
      rw [h1, map_one] at hyy'
      rw [← hyy', orderOf_one] at hy'o
      exact absurd hy'o (by decide)
    have hyi' : (y : G) ^ (2 ^ i) = 1 := by simpa using congrArg Subtype.val hyi
    have hevenG : Even (Nat.card (L ⊓ normalizer (J : Set G) : Subgroup G)) :=
      even_card_of_two_element (mem_inf.mpr ⟨hyL, hyN⟩) hy1 hyi'
    obtain ⟨T, hT, hTN⟩ := hΩ.sylow J (hαΩ hJ) L (hαΩ hL) hJL hevenG
    rw [isSylowOf_iff_card] at hT
    have hT2 : IsPGroup 2 T := IsPGroup.of_card hT.2
    refine ⟨bar X T, isSylowOf_iff_card.mpr ⟨bar_mono hT.1, ?_⟩, ?_⟩
    · rw [card_bar_of_pGroup (hT.1.trans (hJX L hL)) hT2, hT.2,
        factorization_card_bar (hJX L hL)]
    · rintro _ ⟨t, ht, rfl⟩
      rw [← rightConjugate_eq_self_iff, ← bar_rightConjugate,
        (rightConjugate_eq_self_iff J t).mpr (hTN ht)]
  ·
    rintro _ ⟨J, hJ, rfl⟩ R' hR'
    rw [isSylowOf_iff_card] at hR'
    have hR'2 : IsPGroup 2 R' := IsPGroup.of_card hR'.2
    obtain ⟨R, hRJ, hR2, hRbar, hRcard⟩ := exists_pGroup_lift hR'2 hR'.1
    have hRsyl : IsSylowOf 2 R J := isSylowOf_iff_card.mpr
      ⟨hRJ, by rw [hRcard, hR'.2, factorization_card_bar (hJX J hJ)]⟩
    obtain ⟨h1, h2⟩ := hΩ.rank J (hαΩ hJ) R hRsyl
    have e : R ≃* R' :=
      (barEquiv (hRJ.trans (hJX J hJ)) hR2).trans (MulEquiv.subgroupCongr hRbar)
    refine ⟨?_, fun h => h2 (isElemAbelian_of_mulEquiv e.symm h)⟩
    obtain ⟨E, hER, hE, hE4⟩ := exists_fourGroup_le h1
    have hEX : E ≤ sSup α := hER.trans (hRJ.trans (hJX J hJ))
    refine one_lt_pRank_of_fourGroup (E := bar (sSup α) E) (hRbar ▸ bar_mono hER) ?_ ?_
    · exact isElemAbelian_of_mulEquiv (barEquiv hEX (hR2.to_le hER)) hE
    · rw [card_bar_of_pGroup hEX (hR2.to_le hER), hE4]
  ·
    rintro _ ⟨J, hJ, rfl⟩ _ ⟨L, hL, rfl⟩ hne
    have hJL : J ≠ L := fun h => hne (h ▸ rfl)
    refine ⟨?_, ?_⟩
    · rw [factorization_card_bar (hJX J hJ), factorization_card_bar (hJX L hL)]
      exact (hΩ.twoPart J (hαΩ hJ) L (hαΩ hL) hJL).1
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
    have hy'J : (y' : BarGroup X) ∈ bar X J := (mem_inf.mp y'.2).1
    have hy'L : (y' : BarGroup X) ∈ bar X L := (mem_inf.mp y'.2).2
    have hy'o : orderOf (y' : BarGroup X) = 2 := by rw [orderOf_coe]; exact hy'
    have hy'2 : (y' : BarGroup X) ^ (2 ^ 1) = 1 := by
      rw [pow_one, ← hy'o]
      exact pow_orderOf_eq_one _
    obtain ⟨y, hyL, ⟨i, hyi⟩, hyy'⟩ := exists_two_element_preimage (barMk X) hy'L hy'2
    have hyi' : (y : G) ^ (2 ^ i) = 1 := by simpa using congrArg Subtype.val hyi
    have hyJ : (y : G) ∈ J :=
      hΩ.mem_of_barMk_mem (hαΩ hJ) (hJX J hJ) hyi' (by rw [hyy']; exact hy'J)
    have hy1 : (y : G) ≠ 1 := by
      intro h
      have h1 : y = 1 := Subtype.ext h
      rw [h1, map_one] at hyy'
      rw [← hyy', orderOf_one] at hy'o
      exact absurd hy'o (by decide)
    apply hJL
    refine hΩ.eq_of_pGroup_le (hαΩ hJ) (hαΩ hL) (isPGroup_zpowers_of_two_element hyi')
      (zpowers_ne_bot_of_ne_one' hy1) ?_ ?_
    · exact (zpowers_le).mpr hyJ
    · exact (zpowers_le).mpr hyL
  ·
    rintro _ ⟨J, hJ, rfl⟩
    apply le_antisymm
    · exact (closure_le _).mpr fun x hx => hx.1
    · have hJ2 := hΩ.perfect J (hαΩ hJ)
      have hSJ : closure {x | x ∈ J ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1} ≤ J :=
        (closure_le _).mpr fun x hx => hx.1
      rintro _ ⟨y, hy, rfl⟩
      have hyJ : (y : G) ∈ closure {x | x ∈ J ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1} := by
        have : (y : G) ∈ oUpperTwoPrime J := hJ2.symm ▸ hy
        exact this
      have key := closure_induction
        (p := fun z hz => barMk X ⟨z, hJX J hJ (hSJ hz)⟩ ∈ oUpperTwoPrime (bar X J))
        (fun x hx => by
          obtain ⟨hxJ, k, hxk⟩ := hx
          refine subset_closure ⟨⟨⟨x, hJX J hJ hxJ⟩, hxJ, rfl⟩, k, ?_⟩
          rw [← map_pow]
          have : (⟨x, hJX J hJ hxJ⟩ : X) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hxk)
          rw [this, map_one])
        (by
          have : (⟨1, hJX J hJ (hSJ (one_mem _))⟩ : X) = 1 := rfl
          rw [this, map_one]
          exact one_mem _)
        (fun x y hx hy hpx hpy => by
          have : (⟨x * y, hJX J hJ (hSJ (mul_mem hx hy))⟩ : X) =
              ⟨x, hJX J hJ (hSJ hx)⟩ * ⟨y, hJX J hJ (hSJ hy)⟩ := rfl
          rw [this, map_mul]
          exact mul_mem hpx hpy)
        (fun x hx hpx => by
          have : (⟨x⁻¹, hJX J hJ (hSJ (inv_mem hx))⟩ : X) = (⟨x, hJX J hJ (hSJ hx)⟩)⁻¹ := rfl
          rw [this, map_inv]
          exact inv_mem hpx)
        hyJ
      exact key

end CFSG.ComponentClassification.Asc76.Sec3Setting
