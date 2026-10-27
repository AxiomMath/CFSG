module

public import CFSG.GH74.GLS.C3.Layer1.PU3Basic
public import CFSG.GH74.GLS.C3.Layer1.PU3Pack
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L128Cop
public import CFSG.GH74.GLS.C3.Layer1.Th2PU3Q

public section

namespace CFSG.GH74.GLS.PU3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem isPerfect_of_simple_nonab {H : Type*} [Group H] [IsSimpleGroup H]
    (hn : ∃ a b : H, a * b ≠ b * a) : Group.IsPerfect H := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator H) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    apply hab
    have : ⁅a, b⁆ ∈ commutator H := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · exact ⟨h⟩

omit [Finite G] in
theorem subgroupOf_sup_eq_comap {M L : Subgroup G} (hLM : L ≤ M) :
    (L ⊔ pPrimeCoreOf 2 M).subgroupOf M = (imgM M L).comap (barMk ↥M) := by
  ext x
  have hLN : L ≤ normalizer (pPrimeCoreOf 2 M : Set G) := fun l hl =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hLM hl))
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_imgM_iff]
  constructor
  · intro hx
    obtain ⟨l, hl, o, ho, hlo⟩ := (Th2.HY.mem_sup_iff_mul_of_le_normalizer hLN).1 hx
    refine ⟨⟨l, hLM hl⟩, hl, ?_⟩
    have h1 : barMk ↥M ⟨o, TwoThin.pPrimeCoreOf_le M ho⟩ = 1 :=
      (barMk_eq_one_iff_mem_pPrimeCoreOf _).2 ho
    have h2 : x = ⟨l, hLM hl⟩ * ⟨o, TwoThin.pPrimeCoreOf_le M ho⟩ := Subtype.ext hlo
    rw [h2, map_mul, h1, mul_one]
  · rintro ⟨m, hm, hmx⟩
    have h1 : barMk ↥M (m⁻¹ * x) = 1 := by rw [map_mul, map_inv, hmx, inv_mul_cancel]
    have h2 : ((m⁻¹ * x : ↥M) : G) ∈ pPrimeCoreOf 2 M := (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h1
    have h3 : (x : G) = (m : G) * ((m⁻¹ * x : ↥M) : G) := by simp
    rw [h3]
    exact Subgroup.mul_mem_sup hm h2

omit [Finite G] in
theorem isSubnormalIn_sup_pPrimeCoreOf {M L : Subgroup G} (h : IsPCompIn 2 M L) :
    ((L ⊔ pPrimeCoreOf 2 M).subgroupOf M).IsSubnormal := by
  rw [subgroupOf_sup_eq_comap h.1]
  have h1 : (imgM M L).IsSubnormal :=
    Subgroup.IsSubnormal.map (barMk_surjective (Y := ↥M)) (isSubnormalIn_of_comp h).2
  exact h1.comap _

theorem exists_cover_core {M L : Subgroup G} (h : Good M L) {N X : Subgroup G} (hX : X ≤ N)
    (hcov : Covers X L (pPrimeCoreOf 2 M)) :
    ∃ X₀ : Subgroup G, X₀ ≤ L ∧ X₀ ≤ N ∧ ⁅X₀, X₀⁆ = X₀ ∧
      (X₀.subgroupOf (M ⊓ N)).IsSubnormal ∧ Covers X₀ L (pPrimeCoreOf 2 M) := by
  set O := pPrimeCoreOf 2 M with hO
  set A := L ⊔ O with hA
  set J := A ⊓ N with hJ
  have hOM : O ≤ M := TwoThin.pPrimeCoreOf_le M
  have hAM : A ≤ M := sup_le h.comp.1 hOM
  have hJMN : J ≤ M ⊓ N := le_inf (inf_le_left.trans hAM) inf_le_right
  let X₀ : Subgroup G := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf J
  have hX₀J : X₀ ≤ J := Subgroup.map_subtype_le _
  have hperfX₀ : ⁅X₀, X₀⁆ = X₀ := Subgroup.isPerfect_iff.mp (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect J)
  have hX₀A : X₀ ≤ A := hX₀J.trans inf_le_left
  have hX₀L : X₀ ≤ L := h.perf_le hX₀A hperfX₀
  refine ⟨X₀, hX₀L, hX₀J.trans inf_le_right, hperfX₀, ?_, ?_⟩
  ·
    have hchar : (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥J).Characteristic :=
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
    have hnormal : (X₀.subgroupOf J).Normal := by
      have : X₀.subgroupOf J = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥J :=
        Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
      rw [this]
      infer_instance
    have hJsub : (J.subgroupOf (M ⊓ N)).IsSubnormal := by
      have h1 := (isSubnormalIn_sup_pPrimeCoreOf h.comp).comap (Subgroup.inclusion (inf_le_left : M ⊓ N ≤ M))
      convert h1 using 1
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hJ, Subgroup.mem_inf, Subgroup.inclusion]
      constructor
      · rintro ⟨hA', -⟩; exact hA'
      · intro hA'; exact ⟨hA', x.2.2⟩
    exact Th2.PU3Q.isSubnormal_subgroupOf_trans' hX₀J hJMN hnormal.isSubnormal hJsub
  ·
    have hLO : L ⊔ O = A := rfl
    have hJM : J ≤ M := hJMN.trans inf_le_left
    have hmemA : ∀ x : ↥M, (x : G) ∈ A → barMk ↥M x ∈ imgM M L := by
      intro x hx
      have := (Subgroup.ext_iff.1 (subgroupOf_sup_eq_comap h.comp.1) x).1 hx
      exact this
    let ψ : ↥J →* ↥(imgM M L) :=
      ((barMk ↥M).comp (Subgroup.inclusion hJM)).codRestrict (imgM M L) fun x =>
        hmemA (Subgroup.inclusion hJM x) x.2.1
    have hψ : Function.Surjective ψ := by
      rintro ⟨w, hw⟩
      obtain ⟨m, hmL, rfl⟩ := mem_imgM_iff.1 hw
      obtain ⟨x, hxX, o, hoO, hmxo⟩ := hcov (m : G) hmL
      have hxA : x ∈ A := by
        have : x = (m : G) * o⁻¹ := by rw [hmxo]; group
        rw [this]
        exact A.mul_mem (Subgroup.mem_sup_left hmL) (A.inv_mem (Subgroup.mem_sup_right hoO))
      have hxJ : x ∈ J := ⟨hxA, hX hxX⟩
      refine ⟨⟨x, hxJ⟩, Subtype.ext ?_⟩
      show barMk ↥M ⟨x, hJM hxJ⟩ = barMk ↥M m
      have h1 : barMk ↥M ⟨o, hOM hoO⟩ = 1 := (barMk_eq_one_iff_mem_pPrimeCoreOf _).2 hoO
      have h2 : m = ⟨x, hJM hxJ⟩ * ⟨o, hOM hoO⟩ := Subtype.ext hmxo
      rw [h2, map_mul, h1, mul_one]
    have : IsSimpleGroup ↥(imgM M L) := h.imgM_simple
    have hperf : Group.IsPerfect ↥(imgM M L) := by
      obtain ⟨a, ha, b, hb, hab⟩ := h.imgM_nonab
      exact isPerfect_of_simple_nonab ⟨⟨a, ha⟩, ⟨b, hb⟩, fun hc => hab (congrArg Subtype.val hc)⟩
    have htop := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image ψ hψ
    intro a ha
    have haM : a ∈ M := h.comp.1 ha
    have hmem : (⟨barMk ↥M ⟨a, haM⟩, mem_imgM_iff.2 ⟨⟨a, haM⟩, ha, rfl⟩⟩ : ↥(imgM M L)) ∈
        (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥J).map ψ := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyψ⟩ := hmem
    have hxX₀ : (y : G) ∈ X₀ := ⟨y, hy, rfl⟩
    refine ⟨y, hxX₀, (y : G)⁻¹ * a, ?_, by group⟩
    have h1 : barMk ↥M (⟨(y : G), hJM y.2⟩⁻¹ * ⟨a, haM⟩) = 1 := by
      rw [map_mul, map_inv]
      have := congrArg Subtype.val hyψ
      change barMk ↥M ⟨(y : G), hJM y.2⟩ = barMk ↥M ⟨a, haM⟩ at this
      rw [this, inv_mul_cancel]
    exact (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h1



omit [Finite G] in
theorem covers_iff_imgM_eq {M X L : Subgroup G} (hXL : X ≤ L) (hLM : L ≤ M) :
    Covers X L (pPrimeCoreOf 2 M) ↔ imgM M X = imgM M L := by
  constructor
  · intro hcov
    refine le_antisymm (imgM_mono hXL) ?_
    intro w hw
    obtain ⟨m, hmL, rfl⟩ := mem_imgM_iff.1 hw
    obtain ⟨x, hx, o, ho, hmxo⟩ := hcov m hmL
    have hxM : x ∈ M := hLM (hXL hx)
    have hoM : o ∈ M := TwoThin.pPrimeCoreOf_le M ho
    refine mem_imgM_iff.2 ⟨⟨x, hxM⟩, hx, ?_⟩
    have h1 : barMk ↥M ⟨o, hoM⟩ = 1 := (barMk_eq_one_iff_mem_pPrimeCoreOf _).2 ho
    have h2 : m = ⟨x, hxM⟩ * ⟨o, hoM⟩ := Subtype.ext hmxo
    rw [h2, map_mul, h1, mul_one]
  · intro h a ha
    have haM : a ∈ M := hLM ha
    have hmem : barMk ↥M ⟨a, haM⟩ ∈ imgM M X := by
      rw [h]
      exact mem_imgM_iff.2 ⟨⟨a, haM⟩, ha, rfl⟩
    obtain ⟨m, hmX, hm⟩ := mem_imgM_iff.1 hmem
    refine ⟨m, hmX, (m : G)⁻¹ * a, ?_, by group⟩
    have h1 : barMk ↥M (m⁻¹ * ⟨a, haM⟩) = 1 := by
      rw [map_mul, map_inv, hm, inv_mul_cancel]
    exact (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h1

theorem factorization_eq_of_imgM_eq {M X L : Subgroup G} (hXL : X ≤ L) (hLM : L ≤ M)
    (h : imgM M X = imgM M L) :
    (Nat.card ↥X).factorization 2 = (Nat.card ↥L).factorization 2 := by
  rw [← factorization_card_imgM (hXL.trans hLM), ← factorization_card_imgM hLM, h]

theorem isSylowOf_of_imgM_eq {M X L P : Subgroup G} (hXL : X ≤ L) (hLM : L ≤ M)
    (h : imgM M X = imgM M L) (hP : IsSylowOf 2 P X) : IsSylowOf 2 P L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card (hP.le.trans hXL) ?_
  rw [hP.card_eq, factorization_eq_of_imgM_eq hXL hLM h]

theorem exists_four_group_of_sylow {L P : Subgroup G} (hP : IsSylowOf 2 P L)
    (hrank : 2 ≤ pRank 2 ↥L) :
    ∃ E : Subgroup G, E ≤ P ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ 2 ^ 2 ≤ Nat.card ↥E := by
  obtain ⟨E', hE'L, hE', hcard⟩ := Th2.CaseI.exists_elemAbelian_four hrank
  have hE'2 : IsPGroup 2 ↥E' := CFSG.IsElementaryAbelian.isPGroup 2 ↥E'
  obtain ⟨g, -, hg⟩ := Th2.exists_cj_le_of_isSylowOf hP hE'L hE'2
  refine ⟨cj g E', hg, isElementaryAbelian_cj g hE', ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hcard

omit [Finite G] in
theorem isSubnormal_restrict {S H K : Subgroup G} (h : (S.subgroupOf H).IsSubnormal) (hKH : K ≤ H) :
    (S.subgroupOf K).IsSubnormal := by
  have := h.comap (Subgroup.inclusion hKH)
  convert this using 1
  ext x
  simp [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.inclusion]

omit [Finite G] in
theorem centralizer_singleton_le_normalizer_zpowers (e : G) :
    centralizer ({e} : Set G) ≤ normalizer ((zpowers e : Subgroup G) : Set G) := by
  intro c hc
  apply Subgroup.centralizer_le_normalizer ((zpowers e : Subgroup G) : Set G)
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact hc

theorem eq_of_alpha {M N L B X₀ : Subgroup G} (hL : Good M L) (hB : Good N B)
    (hX₀L : X₀ ≤ L) (hX₀N : X₀ ≤ N) (hperf : ⁅X₀, X₀⁆ = X₀)
    (hcov : Covers X₀ L (pPrimeCoreOf 2 M))
    (hα : imgM N X₀ = imgM N B) : L = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ M := hL.comp.1
  have hBN : B ≤ N := hB.comp.1
  have hLimg : imgM M X₀ = imgM M L := (covers_iff_imgM_eq hX₀L hLM).1 hcov
  have hX₀B : X₀ ≤ B := by
    have h1 : X₀ ≤ B ⊔ pPrimeCoreOf 2 N := by
      intro x hx
      have hxN : x ∈ N := hX₀N hx
      have hmem : barMk ↥N ⟨x, hxN⟩ ∈ imgM N B := by
        rw [← hα]
        exact mem_imgM_iff.2 ⟨⟨x, hxN⟩, hx, rfl⟩
      obtain ⟨m, hmB, hm⟩ := mem_imgM_iff.1 hmem
      have h2 : barMk ↥N (m⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hm, inv_mul_cancel]
      have h3 : ((m⁻¹ * ⟨x, hxN⟩ : ↥N) : G) ∈ pPrimeCoreOf 2 N :=
        (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h2
      have h4 : x = (m : G) * ((m⁻¹ * ⟨x, hxN⟩ : ↥N) : G) := by simp
      rw [h4]
      exact Subgroup.mul_mem_sup hmB h3
    exact hB.perf_le h1 hperf
  have hBcov : Covers X₀ B (pPrimeCoreOf 2 N) := (covers_iff_imgM_eq hX₀B hBN).2 hα
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥X₀) := inferInstance
  have hPX : IsSylowOf 2 ((Q : Subgroup ↥X₀).map X₀.subtype) X₀ := ⟨Q, rfl⟩
  have hPL : IsSylowOf 2 ((Q : Subgroup ↥X₀).map X₀.subtype) L := isSylowOf_of_imgM_eq hX₀L hLM hLimg hPX
  obtain ⟨E, hEP, hE, hEcard⟩ := exists_four_group_of_sylow hPL hL.rank
  have hEX₀ : E ≤ X₀ := hEP.trans hPX.le
  have hEL : E ≤ L := hEX₀.trans hX₀L
  have hEB : E ≤ B := hEX₀.trans hX₀B
  have hEcent : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ M ⊓ N := by
    intro e he he1
    have := hE
    have he2 : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian e he
    have hzp : IsPGroup 2 ↥(zpowers e) :=
      (IsElementaryAbelian.zpowers_of_pow_eq_one he2).isPGroup 2 _ |> fun h => h
    have hz1 : zpowers e ≠ ⊥ := fun h => he1 (Subgroup.zpowers_eq_bot.1 h)
    have hzL : zpowers e ≤ L := Subgroup.zpowers_le.2 (hEL he)
    have hzB : zpowers e ≤ B := Subgroup.zpowers_le.2 (hEB he)
    have h1 := hL.normalizer_le _ hzL hzp hz1
    have h2 := hB.normalizer_le _ hzB hzp hz1
    have hc := centralizer_singleton_le_normalizer_zpowers e
    exact le_inf (hc.trans h1) (hc.trans h2)
  have hodd : ∀ K : Subgroup G, Odd (Nat.card ↥K) → ¬ 2 ∣ Nat.card ↥K := by
    intro K hK hd
    obtain ⟨k, hk⟩ := hK
    obtain ⟨m, hm⟩ := hd
    omega
  have hLgen : pPrimeCoreOf 2 L ≤ N := by
    refine CFSG.Asc75.le_of_forall_inf_centralizer_le' hE hEcard
      (hodd _ (TwoThin.card_pPrimeCoreOf_odd L)) (fun e he => ?_) ?_
    · exact TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hEL he))
    · intro b hb hb1
      exact inf_le_right.trans ((hEcent b hb hb1).trans inf_le_right)
  have hBgen : pPrimeCoreOf 2 B ≤ M := by
    refine CFSG.Asc75.le_of_forall_inf_centralizer_le' hE hEcard
      (hodd _ (TwoThin.card_pPrimeCoreOf_odd B)) (fun e he => ?_) ?_
    · exact TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hEB he))
    · intro b hb hb1
      exact inf_le_right.trans ((hEcent b hb hb1).trans inf_le_left)
  have hLN : L ≤ N := by
    intro a ha
    obtain ⟨x, hx, o, ho, hxo⟩ := hcov a ha
    have hoL : o ∈ L := by
      have : o = x⁻¹ * a := by rw [hxo]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (hX₀L hx)) ha
    have hoO : o ∈ pPrimeCoreOf 2 L := by
      rw [← inf_pPrimeCoreOf_eq hL.comp]
      exact ⟨hoL, ho⟩
    rw [hxo]
    exact N.mul_mem (hX₀N hx) (hLgen hoO)
  have hBM : B ≤ M := by
    intro a ha
    obtain ⟨x, hx, o, ho, hxo⟩ := hBcov a ha
    have hoB : o ∈ B := by
      have : o = x⁻¹ * a := by rw [hxo]; group
      rw [this]
      exact B.mul_mem (B.inv_mem (hX₀B hx)) ha
    have hoO : o ∈ pPrimeCoreOf 2 B := by
      rw [← inf_pPrimeCoreOf_eq hB.comp]
      exact ⟨hoB, ho⟩
    rw [hxo]
    exact M.mul_mem (hLM (hX₀L hx)) (hBgen hoO)
  have hLsub : (L.subgroupOf (M ⊓ N)).IsSubnormal :=
    isSubnormal_restrict (isSubnormalIn_of_comp hL.comp).2 inf_le_left
  have hBsub : (B.subgroupOf (M ⊓ N)).IsSubnormal :=
    isSubnormal_restrict (isSubnormalIn_of_comp hB.comp).2 inf_le_right
  have hSsub : ((L ⊓ B).subgroupOf (M ⊓ N)).IsSubnormal := by
    have h1 := hLsub.inf hBsub
    have h2 : (L ⊓ B).subgroupOf (M ⊓ N) = L.subgroupOf (M ⊓ N) ⊓ B.subgroupOf (M ⊓ N) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rwa [h2]
  have hLMN : L ≤ M ⊓ N := le_inf hLM hLN
  have hBMN : B ≤ M ⊓ N := le_inf hBM hBN
  have hSL : ((L ⊓ B).subgroupOf L).IsSubnormal := isSubnormal_restrict hSsub hLMN
  have hSB : ((L ⊓ B).subgroupOf B).IsSubnormal := isSubnormal_restrict hSsub hBMN
  have hSM : IsSubnormalIn (L ⊓ B) M :=
    ⟨inf_le_left.trans hLM, Th2.PU3Q.isSubnormal_subgroupOf_trans' inf_le_left hLM hSL
      (isSubnormalIn_of_comp hL.comp).2⟩
  have hSN : IsSubnormalIn (L ⊓ B) N :=
    ⟨inf_le_right.trans hBN, Th2.PU3Q.isSubnormal_subgroupOf_trans' inf_le_right hBN hSB
      (isSubnormalIn_of_comp hB.comp).2⟩
  have hX₀S : X₀ ≤ L ⊓ B := le_inf hX₀L hX₀B
  have himgM : imgM M (L ⊓ B) = imgM M L :=
    le_antisymm (imgM_mono inf_le_left) (hLimg ▸ imgM_mono hX₀S)
  have himgN : imgM N (L ⊓ B) = imgM N B :=
    le_antisymm (imgM_mono inf_le_right) (hα ▸ imgM_mono hX₀S)
  have h1 : L ⊓ B = L := eq_of_imgM_eq hL.comp inf_le_left hSM himgM
  have h2 : L ⊓ B = B := eq_of_imgM_eq hB.comp inf_le_right hSN himgN
  rw [← h1, h2]

theorem exists_central_involution {P : Subgroup G} (hP : IsPGroup 2 ↥P) (hP1 : P ≠ ⊥) :
    ∃ u ∈ P, orderOf u = 2 ∧ ∀ p ∈ P, u * p = p * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥P := by
    rw [Subgroup.nontrivial_iff_ne_bot]; exact hP1
  have hC : IsPGroup 2 ↥(Subgroup.center ↥P) := hP.to_subgroup _
  have hCnt : Nontrivial ↥(Subgroup.center ↥P) := hP.center_nontrivial
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥P) := by
    rcases hC.card_eq_or_dvd with h1 | h2
    · exfalso
      have := (Subgroup.card_eq_one (H := Subgroup.center ↥P)).1 h1
      rw [Subgroup.eq_bot_iff_forall] at this
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
      exact hx (Subtype.ext (this x x.2))
    · exact h2
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥P)) 2 h2
  refine ⟨((c : ↥P) : G), (c : ↥P).2, ?_, fun p hp => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  · have := Subgroup.mem_center_iff.1 c.2 ⟨p, hp⟩
    exact congrArg Subtype.val this.symm

theorem imgM_comm_of_ne {N B₁ B₂ : Subgroup G} (h₁ : IsPCompIn 2 N B₁) (h₂ : IsPCompIn 2 N B₂)
    (hne : B₁ ≠ B₂) : ∀ a ∈ imgM N B₁, ∀ b ∈ imgM N B₂, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m₁, hm₁, rfl⟩ := mem_imgM_iff.1 ha
  obtain ⟨m₂, hm₂, rfl⟩ := mem_imgM_iff.1 hb
  have hle := Stage1.Thm2.Recip.le_cSec_of_ne h₁ h₂ hne
  have h1 : ⁅(m₂ : G), (m₁ : G)⁆ ∈ pPrimeCoreOf 2 B₂ := (hle hm₁).2.2 m₂ hm₂
  have h1' : ⁅(m₂ : G), (m₁ : G)⁆ ∈ pPrimeCoreOf 2 N := pPrimeCoreOf_le_of_comp h₂ h1
  have h2 : barMk ↥N ⁅m₂, m₁⁆ = 1 := by
    rw [barMk_eq_one_iff_mem_pPrimeCoreOf]
    have : ((⁅m₂, m₁⁆ : ↥N) : G) = ⁅(m₂ : G), (m₁ : G)⁆ := by simp [commutatorElement_def]
    rw [this]
    exact h1'
  rw [map_commutatorElement] at h2
  exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm

theorem false_of_diag {M N L B₁ B₂ X₀ : Subgroup G} (hL : Good M L) (hB₁ : Good N B₁)
    (hB₂ : Good N B₂) (hne : B₁ ≠ B₂) (hX₀L : X₀ ≤ L) (hX₀N : X₀ ≤ N)
    (hsub : (X₀.subgroupOf (M ⊓ N)).IsSubnormal)
    (hcov : Covers X₀ L (pPrimeCoreOf 2 M))
    (hYle : imgM N X₀ ≤ imgM N B₁ ⊔ imgM N B₂)
    (hdiag : Pack.IsDiag (imgM N B₁) (imgM N B₂) (imgM N X₀)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ M := hL.comp.1
  have hLimg : imgM M X₀ = imgM M L := (covers_iff_imgM_eq hX₀L hLM).1 hcov
  have hX₀M : X₀ ≤ M := hX₀L.trans hLM
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥X₀) := inferInstance
  set P : Subgroup G := (Q : Subgroup ↥X₀).map X₀.subtype with hPdef
  have hPX : IsSylowOf 2 P X₀ := ⟨Q, rfl⟩
  have hPL : IsSylowOf 2 P L := isSylowOf_of_imgM_eq hX₀L hLM hLimg hPX
  have hP1 : P ≠ ⊥ := by
    intro hbot
    have hcard := hPL.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos : 0 < Nat.card ↥L := Nat.card_pos
    have hf : 1 ≤ (Nat.card ↥L).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos.ne').1 hL.two_dvd_card
    have h2lt : 1 < 2 ^ (Nat.card ↥L).factorization 2 := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨u, huP, hu2, huc⟩ := exists_central_involution hPX.isPGroup hP1
  have huX₀ : u ∈ X₀ := hPX.le huP
  have huN : u ∈ N := hX₀N huX₀
  have huL : u ∈ L := hX₀L huX₀
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu2
    omega
  have huu : u * u = 1 := by
    have : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    rwa [pow_two] at this
  have hCu : centralizer ({u} : Set G) ≤ M := by
    have hzp : IsPGroup 2 ↥(zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2]; simp)
    have hz1 : zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.1 h)
    have hzL : zpowers u ≤ L := Subgroup.zpowers_le.2 huL
    exact (centralizer_singleton_le_normalizer_zpowers u).trans
      (hL.normalizer_le _ hzL hzp hz1)
  have hPhat : IsSylowOf 2 (imgM N P) (imgM N X₀) := isSylowOf_imgM_of_le hX₀N hPX
  set z : Mb N := barMk ↥N ⟨u, huN⟩ with hz
  have hzP : z ∈ imgM N P := mem_imgM_iff.2 ⟨⟨u, huN⟩, huP, rfl⟩
  have hzc : ∀ p ∈ imgM N P, z * p = p * z := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hp
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (huc m hm)
  have hX₀MN : X₀ ≤ M ⊓ N := le_inf hX₀M hX₀N
  have hYH : imgM N X₀ ≤ imgM N (M ⊓ N) := imgM_mono hX₀MN
  have hCH : centralizer ({z} : Set (Mb N)) ≤ imgM N (M ⊓ N) := by
    intro w hw
    have hx : (QuotientGroup.mk (⟨u, huN⟩ : ↥N) : Mb N) * w = w * QuotientGroup.mk (⟨u, huN⟩ : ↥N) :=
      (Subgroup.mem_centralizer_singleton_iff.1 hw).symm
    obtain ⟨c, hcC, hcw⟩ :=
      Stage2.Bender.Thm2.L128.exists_centralizer_preimage huN huu w hx
    exact mem_imgM_iff.2 ⟨c, ⟨hCu hcC, c.2⟩, hcw⟩
  have hsn' : ((imgM N X₀).subgroupOf (imgM N (M ⊓ N))).IsSubnormal := by
    have h1 := Subgroup.IsSubnormal.map (toImgM_surjective (inf_le_right : M ⊓ N ≤ N)) hsub
    convert h1 using 1
    ext w
    obtain ⟨y0, rfl⟩ := toImgM_surjective (inf_le_right : M ⊓ N ≤ N) w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro h
      obtain ⟨m, hmX, hm⟩ := mem_imgM_iff.1 h
      have hmMN : (m : G) ∈ M ⊓ N := hX₀MN hmX
      refine ⟨⟨m, hmMN⟩, hmX, Subtype.ext ?_⟩
      exact hm
    · rintro ⟨y, hy, hyw⟩
      refine mem_imgM_iff.2 ⟨Subgroup.inclusion inf_le_right y, hy, ?_⟩
      exact congrArg Subtype.val hyw
  exact Pack.not_subnormal_diag ⟨hB₁.imgM_simple, hB₁.imgM_nonab⟩ ⟨hB₂.imgM_simple, hB₂.imgM_nonab⟩
    (imgM_comm_of_ne hB₁.comp hB₂.comp hne) hdiag hYle hPhat hzP hzc hYH hCH hsn'




omit [Finite G] in
theorem imgM_sup {N B₁ B₂ : Subgroup G} (h₁ : B₁ ≤ N) (h₂ : B₂ ≤ N) :
    imgM N (B₁ ⊔ B₂) = imgM N B₁ ⊔ imgM N B₂ := by
  unfold imgM
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

omit [Finite G] in
theorem imgM_pPrimeCoreOf (N : Subgroup G) : imgM N (pPrimeCoreOf 2 N) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hw
  rw [Subgroup.mem_bot]
  exact (barMk_eq_one_iff_mem_pPrimeCoreOf m).2 hm

omit [Finite G] in
theorem imgM_le_sup_of_le {N B₁ B₂ X : Subgroup G} (hB₁ : B₁ ≤ N) (hB₂ : B₂ ≤ N)
    (hX : X ≤ B₁ ⊔ B₂ ⊔ pPrimeCoreOf 2 N) : imgM N X ≤ imgM N B₁ ⊔ imgM N B₂ := by
  have h1 : imgM N X ≤ imgM N (B₁ ⊔ B₂ ⊔ pPrimeCoreOf 2 N) := imgM_mono hX
  have hOB : pPrimeCoreOf 2 N ≤ N := TwoThin.pPrimeCoreOf_le N
  rw [imgM_sup (sup_le hB₁ hB₂) hOB, imgM_sup hB₁ hB₂, imgM_pPrimeCoreOf, sup_bot_eq] at h1
  exact h1


theorem Good.card_imgM_cj {M L : Subgroup G} (h : Good M L) (g : G) :
    Nat.card ↥(imgM (cj g M) (cj g L)) = Nat.card ↥(imgM M L) := by
  obtain ⟨e₁⟩ := imgM_equiv_kBar_self (h.conj g).comp
  obtain ⟨e₂⟩ := imgM_equiv_kBar_self h.comp
  exact Nat.card_congr (e₁.toEquiv.trans ((Th2.Obs.kBarConjEquiv g L).symm.toEquiv.trans e₂.symm.toEquiv))

theorem Good.imgM_simple_of_eq {M X L : Subgroup G} (h : Good M L) (hXL : imgM M X = imgM M L) :
    IsSimpleGroup ↥(imgM M X) ∧ ∃ a b : ↥(imgM M X), a * b ≠ b * a := by
  rw [hXL]
  obtain ⟨a, ha, b, hb, hab⟩ := h.imgM_nonab
  exact ⟨h.imgM_simple, ⟨a, ha⟩, ⟨b, hb⟩, fun hc => hab (congrArg Subtype.val hc)⟩

theorem covering {M L₁ L₂ : Subgroup G} (h : Cfg M L₁ L₂) {g : G} {X : Subgroup G}
    (hX : X ≤ cj g⁻¹ M) (hcov : Covers X L₁ (pPrimeCoreOf 2 M)) : g ∈ M := by
  have hCN : Cfg (cj g⁻¹ M) (cj g⁻¹ L₁) (cj g⁻¹ L₂) := h.conj g⁻¹
  obtain ⟨X₀, hX₀L, hX₀N, hperf, hsub, hcov₀⟩ := exists_cover_core h.good₁ hX hcov
  have hLM : L₁ ≤ M := h.good₁.comp.1
  have hX₀M : X₀ ≤ M := hX₀L.trans hLM
  have hLimg : imgM M X₀ = imgM M L₁ := (covers_iff_imgM_eq hX₀L hLM).1 hcov₀
  have hB₁N : cj g⁻¹ L₁ ≤ cj g⁻¹ M := hCN.good₁.comp.1
  have hB₂N : cj g⁻¹ L₂ ≤ cj g⁻¹ M := hCN.good₂.comp.1
  let f : ↥X₀ →* Mb (cj g⁻¹ M) := (imgM (cj g⁻¹ M) X₀).subtype.comp (toImgM hX₀N)
  have hfr : f.range = imgM (cj g⁻¹ M) X₀ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (toImgM_surjective hX₀N),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfker : f.ker = (toImgM hX₀N).ker :=
    MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _)
  have hYle : imgM (cj g⁻¹ M) X₀ ≤ imgM (cj g⁻¹ M) (cj g⁻¹ L₁) ⊔ imgM (cj g⁻¹ M) (cj g⁻¹ L₂) :=
    imgM_le_sup_of_le hB₁N hB₂N (hCN.perf X₀ hX₀N hperf)
  have hA : Pack.NonabSimple (imgM (cj g⁻¹ M) (cj g⁻¹ L₁)) :=
    ⟨hCN.good₁.imgM_simple, hCN.good₁.imgM_nonab⟩
  have hB : Pack.NonabSimple (imgM (cj g⁻¹ M) (cj g⁻¹ L₂)) :=
    ⟨hCN.good₂.imgM_simple, hCN.good₂.imgM_nonab⟩
  have hcomm := imgM_comm_of_ne hCN.good₁.comp hCN.good₂.comp hCN.ne
  obtain ⟨hS₀, hS₀n⟩ := h.good₁.imgM_simple_of_eq hLimg
  have hcardA : Nat.card ↥(imgM (cj g⁻¹ M) (cj g⁻¹ L₁)) = Nat.card ↥(imgM M X₀) := by
    rw [hLimg]; exact h.good₁.card_imgM_cj g⁻¹
  have hcardB : Nat.card ↥(imgM (cj g⁻¹ M) (cj g⁻¹ L₂)) = Nat.card ↥(imgM M X₀) := by
    rw [hLimg]
    obtain ⟨s, hsM, hsL⟩ := h.swap
    have h1 := h.good₂.card_imgM_cj g⁻¹
    have h2 := h.good₁.card_imgM_cj s
    have hcjM : cj s M = M := C3.Layer1.Thm1.map_conj_eq_self_of_mem hsM
    rw [hcjM, hsL] at h2
    rw [h1, h2]
  rcases Pack.perfect_trichotomy hA hB hcomm f (hfr ▸ hYle) (Subgroup.isPerfect_iff.mpr hperf).commutator_eq_top
      hS₀ hS₀n (toImgM hX₀M) (toImgM_surjective hX₀M) (odd_card_ker_toImgM hX₀M)
      (hfker ▸ odd_card_ker_toImgM hX₀N) hcardA.le hcardB.le with hα₁ | hα₂ | hdiag
  · have hL := eq_of_alpha h.good₁ hCN.good₁ hX₀L hX₀N hperf hcov₀ (hfr.symm.trans hα₁)
    have h1 : g⁻¹ ∈ normalizer (L₁ : Set G) := mem_normalizer_of_cj_eq hL.symm
    exact inv_mem_iff.1 (h.good₁.normalizer_le_M h1)
  · have hL := eq_of_alpha h.good₁ hCN.good₂ hX₀L hX₀N hperf hcov₀ (hfr.symm.trans hα₂)
    obtain ⟨s, hsM, hsL⟩ := h.swap
    have h1 : cj (g⁻¹ * s) L₁ = L₁ := by
      rw [← cj_cj, hsL]
      exact hL.symm
    have h2 : g⁻¹ * s ∈ normalizer (L₁ : Set G) := mem_normalizer_of_cj_eq h1
    have h3 : g⁻¹ * s ∈ M := h.good₁.normalizer_le_M h2
    have h4 : g⁻¹ ∈ M := by
      have := M.mul_mem h3 (M.inv_mem hsM)
      simpa using this
    exact inv_mem_iff.1 h4
  · exact (false_of_diag h.good₁ hCN.good₁ hCN.good₂ hCN.ne hX₀L hX₀N hsub hcov₀ hYle
      (hfr ▸ hdiag)).elim

end CFSG.GH74.GLS.PU3
