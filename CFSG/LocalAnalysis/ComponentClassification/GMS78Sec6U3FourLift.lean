module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6MainC
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313U
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Prelim
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6KFacts

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

section Lift

variable {H : Type} [Group H] [Finite H]

theorem inf_standardComponentOddCore_eq_bot {P : Subgroup H} (hP : IsPGroup 2 P) :
    P ⊓ standardComponentOddCore H = ⊥ :=
  two_subgroup_of_odd_eq_bot _ _ hP.to_inf_left odd_card_standardComponentOddCore' inf_le_right

theorem card_map_mk_of_isPGroup {P : Subgroup H} (hP : IsPGroup 2 P) :
    Nat.card (P.map (QuotientGroup.mk' (standardComponentOddCore H))) = Nat.card P := by
  set π := QuotientGroup.mk' (standardComponentOddCore H) with hπ
  have hinj : Function.Injective (π.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : H) ∈ standardComponentOddCore H := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx
    have h1 : (x : H) ∈ P ⊓ standardComponentOddCore H := mem_inf.mpr ⟨x.2, hxO⟩
    rw [inf_standardComponentOddCore_eq_bot hP, mem_bot] at h1
    exact Subtype.ext h1
  have h2 : (π.comp P.subtype).range = P.map π := by rw [MonoidHom.range_comp, range_subtype]
  rw [← h2]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isSylowOf_comap_map_mk {P : Subgroup H} (hP : IsPGroup 2 P) :
    IsSylowOf 2 P ((P.map (QuotientGroup.mk' (standardComponentOddCore H))).comap
      (QuotientGroup.mk' (standardComponentOddCore H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (standardComponentOddCore H) with hπ
  rw [isSylowOf_iff]
  refine ⟨le_comap_map _ _, hP, ?_⟩
  have hM := card_comap_of_surjective' π (QuotientGroup.mk'_surjective _) (P.map π)
  rw [card_map_mk_of_isPGroup hP, QuotientGroup.ker_mk'] at hM
  have hrel := Subgroup.relIndex_mul_card P ((P.map π).comap π)
  rw [inf_eq_left.mpr (le_comap_map _ _), hM] at hrel
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hrel' : P.relIndex ((P.map π).comap π) = Nat.card (standardComponentOddCore H) := by
    have := hrel.trans (mul_comm _ _)
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [hrel']
  exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp odd_card_standardComponentOddCore')

theorem exists_isPGroup_map_eq {W : Subgroup H} (hW : IsPGroup 2 W)
    {Pb : Subgroup (H ⧸ standardComponentOddCore H)} (hPb : IsPGroup 2 Pb)
    (hWP : W.map (QuotientGroup.mk' (standardComponentOddCore H)) ≤ Pb) :
    ∃ P : Subgroup H, W ≤ P ∧ IsPGroup 2 P ∧
      P.map (QuotientGroup.mk' (standardComponentOddCore H)) = Pb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (standardComponentOddCore H) with hπ
  set M := Pb.comap π with hMdef
  have hWM : W ≤ M := fun w hw => hWP (mem_map_of_mem π hw)
  obtain ⟨P, hP, hWP'⟩ := AS76b.exists_isSylowOf_le hWM hW
  refine ⟨P, hWP', hP.isPGroup, ?_⟩
  have hle : P.map π ≤ Pb := map_le_iff_le_comap.mpr hP.le
  refine eq_of_le_of_card_ge hle ?_
  rw [card_map_mk_of_isPGroup hP.isPGroup]
  obtain ⟨a, ha⟩ := hPb.exists_card_eq
  have hM := card_comap_of_surjective' π (QuotientGroup.mk'_surjective _) Pb
  rw [QuotientGroup.ker_mk'] at hM
  have hrel := Subgroup.relIndex_mul_card P M
  rw [inf_eq_left.mpr hP.le] at hrel
  have hodd : ¬ 2 ∣ P.relIndex M := (isSylowOf_iff.mp hP).2.2
  have hdvd : Nat.card Pb ∣ P.relIndex M * Nat.card P := by
    rw [hrel, hM]
    exact Dvd.intro _ rfl
  have hcop : Nat.Coprime (Nat.card Pb) (P.relIndex M) := by
    rw [ha]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_left hdvd)

theorem le_normalizer_of_map_le_normalizer {P S : Subgroup H} (hS : IsPGroup 2 S) (hPS : P ≤ S)
    (hSN : S.map (QuotientGroup.mk' (standardComponentOddCore H)) ≤
      normalizer ((P.map (QuotientGroup.mk' (standardComponentOddCore H)) : Subgroup _) :
        Set (H ⧸ standardComponentOddCore H))) :
    S ≤ normalizer (P : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (standardComponentOddCore H) with hπ
  set M := (P.map π).comap π with hMdef
  have hP := isSylowOf_comap_map_mk (hS.to_le hPS)
  have hSM : S ⊓ M = P :=
    hP.eq_of_le (le_inf hPS (le_comap_map _ _)) inf_le_right (hS.to_le inf_le_left)
  intro s hs
  have hsN : π s ∈ normalizer ((P.map π : Subgroup _) : Set (H ⧸ standardComponentOddCore H)) :=
    hSN (mem_map_of_mem π hs)
  have hle : P.map (MulAut.conj s).toMonoidHom ≤ P := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← hSM]
    refine mem_inf.mpr ⟨mul_mem (mul_mem hs (hPS hp)) (inv_mem hs), ?_⟩
    show π (s * p * s⁻¹) ∈ P.map π
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hsN (π p)).mp (mem_map_of_mem π hp)
  exact mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj s).injective]))

theorem exists_isPGroup_le_normalizer {P : Subgroup H} (hP : IsPGroup 2 P)
    {Sb : Subgroup (H ⧸ standardComponentOddCore H)} (hSb : IsPGroup 2 Sb)
    (hPS : P.map (QuotientGroup.mk' (standardComponentOddCore H)) ≤ Sb)
    (hSN : Sb ≤ normalizer ((P.map (QuotientGroup.mk' (standardComponentOddCore H)) :
      Subgroup _) : Set (H ⧸ standardComponentOddCore H))) :
    ∃ S : Subgroup H, P ≤ S ∧ IsPGroup 2 S ∧
      S.map (QuotientGroup.mk' (standardComponentOddCore H)) = Sb ∧
      S ≤ normalizer (P : Set H) := by
  obtain ⟨S, hPS', hS, hSmap⟩ := exists_isPGroup_map_eq hP hSb hPS
  exact ⟨S, hPS', hS, hSmap, le_normalizer_of_map_le_normalizer hS hPS' (hSmap ▸ hSN)⟩

theorem exists_conj_mem_of_map {A : Subgroup H} (hA : IsPGroup 2 A) {t : H}
    (ht : IsPGroup 2 (zpowers t)) {yb : H ⧸ standardComponentOddCore H}
    (hy : yb * QuotientGroup.mk' (standardComponentOddCore H) t * yb⁻¹ ∈
      A.map (QuotientGroup.mk' (standardComponentOddCore H))) :
    ∃ y : H, y * t * y⁻¹ ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (standardComponentOddCore H) with hπ
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective (standardComponentOddCore H) yb
  set M := (A.map π).comap π with hMdef
  have hAM := isSylowOf_comap_map_mk hA
  have hzM : zpowers (y₀ * t * y₀⁻¹) ≤ M := by
    rw [zpowers_le]
    show π (y₀ * t * y₀⁻¹) ∈ A.map π
    rw [map_mul, map_mul, map_inv]
    exact hy
  have hz2 : IsPGroup 2 (zpowers (y₀ * t * y₀⁻¹)) := by
    have h1 : (zpowers t).map (MulAut.conj y₀).toMonoidHom = zpowers (y₀ * t * y₀⁻¹) := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [← h1]
    exact ht.map _
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hAM hzM hz2
  refine ⟨k * y₀, ?_⟩
  have h1 := hk _ (mem_zpowers _)
  simpa [mul_assoc] using h1

omit [Finite H] in
theorem isPGroup_zpowers_of_sq_eq_one {x : H} (hx : x ^ 2 = 1) : IsPGroup 2 (zpowers x) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  show (x ^ n) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

end Lift

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G}

omit [Finite G] in
theorem gmsA_le_centralizer_K {K : Subgroup G}
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    gmsA L T ≤ centralizer (K : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  exact fun k hk => (mem_inf.mp ((hKH ▸ (le_sup_right : K ≤ (T ⊓ L) ⊔ K)) hk)).2

omit [Finite G] in
theorem u3X₀_le_centralizer (L K : Subgroup G) : u3X₀ L K ≤ centralizer (K : Set G) := by
  refine (commutator_le).mpr fun x hx y hy => ?_
  exact mul_mem (mul_mem (mul_mem (mem_inf.mp hx).2 (mem_inf.mp hy).2)
    (inv_mem (mem_inf.mp hx).2)) (inv_mem (mem_inf.mp hy).2)

omit [Finite G] in
theorem T₀_le_centralizer_K {K : Subgroup G} (hKL : K ≤ L) :
    T ⊓ centralizer (L : Set G) ≤ centralizer (K : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le hKL)

theorem isSylowOf_gmsA_u3X₀_four (h3 : Sec3 G L T) (e : rankTwoQuot L ≃* PSU3 2 2)
    {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    IsSylowOf 2 (gmsA L T) (u3X₀ L K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 h3.hyp.standard.1.1 le_rfl e
  obtain ⟨-, hAc, -⟩ := sylow_of_psu3 hZ le_rfl e h3.isSylowOf_T₁
  obtain ⟨-, -, hAX', -, hZX, -, ⟨eX⟩, -⟩ := u3K_facts h3 le_rfl e hKL hKo hKH
  have hAX : gmsA L T ≤ u3X₀ L K := hAX'.trans (Subgroup.commutator_le_self _)
  have hA4 : Nat.card (gmsA L T) = 4 := by simpa using hAc
  rw [isSylowOf_iff]
  refine ⟨hAX, IsPGroup.of_card (n := 2) (by rw [hA4]; norm_num), ?_⟩
  have hX : Nat.card (u3X₀ L K) = 60 * Nat.card (center (u3X₀ L K)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(u3X₀ L K))]
    congr 1
    rw [Nat.card_congr eX.toEquiv, u3_card_SL2, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hrel := Subgroup.relIndex_mul_card (gmsA L T) (u3X₀ L K)
  rw [inf_eq_left.mpr hAX, hX, hA4] at hrel
  obtain ⟨m, hm⟩ := hZX
  rw [hm] at hrel
  intro h2
  obtain ⟨n, hn⟩ := h2
  rw [hn] at hrel
  omega

theorem isSylowOf_oddQuotImageC_four (h3 : Sec3 G L T) (e : rankTwoQuot L ≃* PSU3 2 2)
    {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    IsSylowOf 2 (oddQuotImageC K (gmsA L T)) (oddQuotImageC K (u3X₀ L K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₁ := centralizer (K : Set G) with hG₁
  have hS := isSylowOf_gmsA_u3X₀_four h3 e hKL hKo hKH
  have hS' : IsSylowOf 2 ((gmsA L T).subgroupOf G₁) ((u3X₀ L K).subgroupOf G₁) := by
    rw [← isSylowOf_map_subtype_iff G₁, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr (gmsA_le_centralizer_K hKH), inf_eq_left.mpr (u3X₀_le_centralizer L K)]
    exact hS
  exact AschbacherTheorem3.IsSylowOf.map hS' _

theorem not_conj_mem_oddQuotImageC_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G)) (ht1 : t ≠ 1) (xb : u3G₁Bar K) :
    xb * QuotientGroup.mk' _ (⟨t, T₀_le_centralizer_K hKL ht⟩ : centralizer (K : Set G)) *
      xb⁻¹ ∉ oddQuotImageC K (u3X₀ L K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hmem
  set G₁ := centralizer (K : Set G) with hG₁
  set π := QuotientGroup.mk' (standardComponentOddCore G₁) with hπ
  set t' : G₁ := ⟨t, T₀_le_centralizer_K hKL ht⟩ with ht'
  have ht2 : t ^ 2 = 1 := (h3.isElemAbelian_T₀ hF).2 t ht
  have ht'2 : t' ^ 2 = 1 := Subtype.ext (by simpa [ht'] using ht2)
  have hub2 : (xb * π t' * xb⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ← map_pow, ht'2, map_one, mul_one, mul_inv_cancel]
  have hsyl := isSylowOf_oddQuotImageC_four h3 e hKL hKo hKH
  obtain ⟨w, -, hw⟩ := exists_conj_le_of_isSylowOf hsyl (zpowers_le.mpr hmem)
    (isPGroup_zpowers_of_sq_eq_one hub2)
  have hw' := hw _ (mem_zpowers _)
  have hA2 : IsPGroup 2 ((gmsA L T).subgroupOf G₁) := by
    have hp := (h3.isSylowOf_T₁.isPGroup.to_le (inf_le_left : gmsA L T ≤ T ⊓ L))
    exact hp.comap_subtype
  have hw'' : (w * xb) * π t' * (w * xb)⁻¹ ∈ ((gmsA L T).subgroupOf G₁).map π := by
    have e1 : (w * xb) * π t' * (w * xb)⁻¹ = w * (xb * π t' * xb⁻¹) * w⁻¹ := by group
    rw [e1]
    exact hw'
  obtain ⟨y, hy⟩ := exists_conj_mem_of_map hA2 (isPGroup_zpowers_of_sq_eq_one ht'2) hw''
  have hyA : (y : G) * t * (y : G)⁻¹ ∈ gmsA L T := hy
  have h313 := h3.lemma313_of_psu3 hF le_rfl e
  have hV : (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) * (y : G)⁻¹⁻¹ ∈ gmsV L T := by
    rw [show (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) * (y : G)⁻¹⁻¹ = t by group]
    exact mem_sup_right ht
  have htA := h313.stronglyClosed _ hyA _ hV
  rw [show (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) * (y : G)⁻¹⁻¹ = t by group] at htA
  have h1 : t ∈ (T ⊓ centralizer (L : Set G)) ⊓ gmsA L T := mem_inf.mpr ⟨ht, htA⟩
  rw [h313.inf_gmsA_eq_bot mem_delta_T₀, mem_bot] at h1
  exact ht1 h1

theorem oddQuotImageC_facts_four (h3 : Sec3 G L T)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    Nonempty (rankTwoQuot (oddQuotImageC K (u3X₀ L K)) ≃* alternatingGroup (Fin 5)) ∧
      Odd (Nat.card (center (oddQuotImageC K (u3X₀ L K)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hZX, -, ⟨eX⟩, -⟩ := u3K_facts h3 le_rfl e hKL hKo hKH
  set G₁ := centralizer (K : Set G) with hG₁
  set X₀ := u3X₀ L K with hX₀
  set X₀' : Subgroup G₁ := X₀.subgroupOf G₁ with hX₀'
  have hX₀G₁ : X₀ ≤ G₁ := u3X₀_le_centralizer L K
  set F := GaloisField 2 2
  have hF4 : Nat.card F = 4 := by rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have eX' : rankTwoQuot X₀' ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (quotCenterCongr (subgroupOfEquivOfLe hX₀G₁)).trans eX
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    exact ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF4]⟩
  have hsimp : IsSimpleGroup (rankTwoQuot X₀') := by
    have := u3_isSimpleGroup_SL2 F h4
    exact eX'.isSimpleGroup
  have hcen : center (rankTwoQuot X₀') = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eX' z ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := eX'.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) w]
    rw [u3_center_SL2_eq_bot, mem_bot] at h1
    rw [mem_bot]
    exact eX'.injective (h1.trans (map_one eX').symm)
  have hSL60 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [u3_card_SL2, hF4]
    norm_num
  have heven : Even (Nat.card (rankTwoQuot X₀')) := by
    rw [Nat.card_congr eX'.toEquiv, hSL60]
    decide
  obtain ⟨eq⟩ := nonempty_quotCenter_map_equiv (N := standardComponentOddCore G₁)
    odd_card_standardComponentOddCore' hsimp hcen heven
  obtain ⟨eP⟩ := nonempty_SL2_equiv_galois F (f := 2) (by norm_num) (by rw [hF4]; norm_num)
  obtain ⟨eA⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hF4)
  refine ⟨⟨((eq.symm.trans eX').trans eP).trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 2)).trans eA)⟩, ?_⟩
  set Xb := oddQuotImageC K X₀ with hXb
  have hXb : Nat.card Xb = 60 * Nat.card (center Xb) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥Xb)]
    congr 1
    rw [← Nat.card_congr eq.toEquiv, Nat.card_congr eX'.toEquiv, hSL60]
  have hX : Nat.card X₀ = 60 * Nat.card (center X₀) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥X₀)]
    congr 1
    rw [Nat.card_congr eX.toEquiv, hSL60]
  have hdvd : Nat.card Xb ∣ Nat.card X₀ := by
    have h1 := Subgroup.card_map_dvd X₀' (QuotientGroup.mk' (standardComponentOddCore G₁))
    rwa [show Nat.card X₀' = Nat.card X₀ from Nat.card_congr (subgroupOfEquivOfLe hX₀G₁).toEquiv]
      at h1
  rw [hXb, hX] at hdvd
  exact Odd.of_dvd_nat hZX (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd)

end Sec3

end CFSG.ComponentClassification.GMS78
