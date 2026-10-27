module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.NotCentralEven
public import CFSG.LocalAnalysis.EvenBN.Common.Endgames
public import CFSG.LocalAnalysis.SteinbergBNPerfectFirstTransferExclusion
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.NotCentralFusion

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped commutatorElement

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem isPerfect (h : Setup G L f t) : Group.IsPerfect G := by
  have := h.simple
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonab
    have h1 := commutator_mem_commutator (mem_top a) (mem_top b)
    rw [← _root_.commutator_def, hb, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab h1
  · exact ht

theorem exists_sylow_eq_of_le (_h : Setup G L f t) {P : Sylow 2 G}
    (hP : (P : Subgroup G) ≤ centralizer ({t} : Set G)) {Q : Subgroup G}
    (hQ : IsSylowOf 2 Q (centralizer ({t} : Set G))) : ∃ T : Sylow 2 G, (T : Subgroup G) = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card Q = 2 ^ (Nat.card G).factorization 2 := by
    rw [hQ.card_eq]
    congr 1
    apply le_antisymm
    · exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
        ((Nat.ordProj_dvd _ _).trans (Subgroup.card_subgroup_dvd_card _))
    · refine (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 ?_
      rw [← Sylow.card_eq_multiplicity P]
      exact Subgroup.card_dvd_of_le hP
  exact ⟨Sylow.ofCard Q hcard, rfl⟩

theorem not_twoCentral_of_odd (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : Odd f) :
    ∀ P : Sylow 2 G, ¬ (P : Subgroup G) ≤ centralizer ({t} : Set G) := by
  intro P hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hRQ⟩ := h.exists_isSylowOf_le d
  have hQR : Q = yamadaR d t := (h.isSylowOf_yamadaR d).eq_of_le hRQ
    (h.le_sup_kernel_of_isPGroup d hf hQ.isPGroup hQ.le) hQ.isPGroup
  obtain ⟨T, hT⟩ := h.exists_sylow_eq_of_le hP hQ
  rw [hQR] at hT
  set S := d.S.map L.subtype with hS
  set R := yamadaR d t with hR
  have hSR : S ≤ R := le_sup_left
  have hcomm := S_commute_kernel d t
  have hRN : R ≤ normalizer (S : Set G) := by
    refine sup_le le_normalizer fun c hc => mem_normalizer_of_conj_mem_D4 fun s hs => ?_
    rw [← hcomm s hs c hc, mul_inv_cancel_right]
    exact hs
  have : (S.subgroupOf R).Normal := (normal_subgroupOf_iff_le_normalizer hSR).2 hRN
  have hcyc : IsCyclic (R ⧸ S.subgroupOf R) := by
    have := h.kernel.1
    refine isCyclic_of_surjective ((QuotientGroup.mk' (S.subgroupOf R)).comp
      (inclusion (le_sup_right : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) ≤ R)))
      fun y => ?_
    obtain ⟨⟨r, hr⟩, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hr' : r ∈ ((R : Subgroup G) : Set G) := hr
    rw [h.coe_yamadaR d] at hr'
    obtain ⟨s, hs, c, hc, rfl⟩ := hr'
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    change (c : G)⁻¹ * (s * c) ∈ S
    rw [hcomm s hs c hc, inv_mul_cancel_left]
    exact hs
  have hFT := CFSG.LocalAnalysis.EvenBN.Common.firstTransferData_of_isCyclic ⟨T, hT⟩ hSR hcyc
    (mem_sup_right h.t_mem_kernel) (fun hS' => h.t_not_mem_L (map_subtype_le _ hS')) h.ht
    fun g hg => h.conj_not_mem_L d g⁻¹ (by rw [inv_inv]; exact map_subtype_le _ hg)
  have := h.isPerfect
  exact CFSG.LocalAnalysis.perfect_first_transfer_exclusion ⟨_, _, _, hFT⟩

theorem exists_conj_eq_mul_V (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hq : 4 ≤ 2 ^ f)
    {v : L} (hv : v ∈ d.V) : ∃ a : G, a * t * a⁻¹ = t * (v : G) := by
  by_cases hv1 : v = 1
  · exact ⟨1, by rw [hv1]; simp⟩
  obtain ⟨a, haY, hat⟩ := h.exists_conj_mem_Y_sup d hq
  have hYL : d.Y.map L.subtype ≤ L := map_subtype_le _
  rcases (h.mem_sup_zpowers_iff hYL).1 haY with hY | hY
  · exact absurd (hYL hY) (h.conj_not_mem_L d a)
  obtain ⟨y, hy, hyt⟩ := hY
  have hy1 : y ≠ 1 := fun h1 => hat (by
    rw [h1, map_one] at hyt
    calc a * t * a⁻¹ = t * (t * (a * t * a⁻¹)) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      _ = t := by rw [← hyt, mul_one])
  have hay : a * t * a⁻¹ = t * (y : G) := by
    rw [show (y : G) = t * (a * t * a⁻¹) from hyt, ← mul_assoc, h.t_mul_t, one_mul]
  obtain ⟨c, hc⟩ := hv
  have hc0 : c ≠ 0 := fun h0 => hv1 (by rw [← hc, h0, d.x₆_zero])
  obtain ⟨m, hm⟩ : ∃ m : L, m * y * m⁻¹ = d.x₆ c := by
    obtain ⟨e, g, rfl⟩ := d.mem_Y_coords hy
    simp only [TrialityD4Data.nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero,
      one_mul] at hy1 ⊢
    by_cases he : e = 0
    · rw [he, d.x₅_zero, one_mul] at hy1 ⊢
      have hg : g ≠ 0 := fun h0 => hy1 (by rw [h0, d.x₆_zero])
      obtain ⟨j, -, hj⟩ := d.exists_J_conj_x₆ hg hc0
      exact ⟨j, hj⟩
    · obtain ⟨j, -, hj⟩ := d.exists_J_conj_x₆ he hc0
      have h1 : d.x₂ (g / e) * d.x₅ e * (d.x₂ (g / e))⁻¹ = d.x₅ e * d.x₆ g := by
        rw [show d.x₂ (g / e) * d.x₅ e * (d.x₂ (g / e))⁻¹ =
          ⁅d.x₂ (g / e), d.x₅ e⁆ * d.x₅ e by rw [commutatorElement_def]; group, d.comm₂₅,
          div_mul_cancel₀ g he]
        exact (d.commute₅₆ e g).symm.eq
      have h2 : d.v * d.x₅ e * d.v⁻¹ = d.x₆ e := by rw [d.v_inv]; exact d.v_x₅ e
      refine ⟨j * d.v * (d.x₂ (g / e))⁻¹, ?_⟩
      rw [← h1]
      calc j * d.v * (d.x₂ (g / e))⁻¹ * (d.x₂ (g / e) * d.x₅ e * (d.x₂ (g / e))⁻¹) *
            (j * d.v * (d.x₂ (g / e))⁻¹)⁻¹ = j * (d.v * d.x₅ e * d.v⁻¹) * j⁻¹ := by group
        _ = d.x₆ c := by rw [h2, hj]
  have hmt : (m : G) * t = t * m := mem_centralizer_singleton_iff.1 (h.L_le_centralizer m.2)
  refine ⟨(m : G) * a, ?_⟩
  have hm' : (m : G) * y * (m : G)⁻¹ = (d.x₆ c : G) := by rw [← hm]; simp
  calc (m : G) * a * t * ((m : G) * a)⁻¹ = m * (a * t * a⁻¹) * (m : G)⁻¹ := by group
    _ = (m : G) * t * y * (m : G)⁻¹ := by rw [hay]; group
    _ = t * ((m : G) * y * (m : G)⁻¹) := by rw [hmt]; group
    _ = t * (v : G) := by rw [hm', hc]

theorem conj_set_normalizer_yamadaR_eq_of_four_le (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hq : 4 ≤ 2 ^ f) :
    {x | ∃ n ∈ normalizer (yamadaR d t : Set G), n * t * n⁻¹ = x} =
      (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G) := by
  obtain ⟨a, ha⟩ := h.exists_conj_eq_mul_V d hq (d.x₆_mem_V 1)
  have hcL : (d.x₆ 1 : G) ∈ L := (d.x₆ 1).2
  have htc : ∀ r ∈ yamadaR d t, r * (a * t * a⁻¹) = a * t * a⁻¹ * r := by
    intro r hr
    rw [ha]
    have hrt : r * t = t * r := mem_centralizer_singleton_iff.1 (h.yamadaR_le_centralizer d hr)
    have hr' : r ∈ ((yamadaR d t : Subgroup G) : Set G) := hr
    rw [h.coe_yamadaR d] at hr'
    obtain ⟨_, ⟨s, hs, rfl⟩, c, hc, rfl⟩ := hr'
    have hsx : (s : G) * d.x₆ 1 = d.x₆ 1 * s :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 (d.S_le_centralizer_x₆_one hs))
    have hcx : c * (d.x₆ 1 : G) = d.x₆ 1 * c :=
      (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).1 _ hcL).symm
    beta_reduce at hrt ⊢
    have hrt' : (s : G) * c * t = t * ((s : G) * c) := hrt
    calc (s : G) * c * (t * d.x₆ 1) = ((s : G) * c * t) * d.x₆ 1 := by group
      _ = t * ((s : G) * c) * d.x₆ 1 := by rw [hrt']
      _ = t * ((s : G) * (c * d.x₆ 1)) := by group
      _ = t * ((s : G) * d.x₆ 1 * c) := by rw [hcx]; group
      _ = t * (d.x₆ 1 * s * c) := by rw [hsx]
      _ = t * d.x₆ 1 * ((s : G) * c) := by group
  obtain ⟨n, hn, hnt⟩ := h.exists_normalizer_yamadaR_conj_eq d (g := a) htc
  refine h.conj_set_normalizer_yamadaR d hn fun h1 => ?_
  rw [hnt, ha] at h1
  have h2 : (d.x₆ 1 : G) = 1 := by
    calc (d.x₆ 1 : G) = t⁻¹ * (t * d.x₆ 1) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]
  exact one_ne_zero (d.x₆_eq_one_iff.1 (Subtype.ext h2))

theorem not_twoCentral_of_conj_set (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hN : {x | ∃ n ∈ normalizer (yamadaR d t : Set G), n * t * n⁻¹ = x} =
      (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G)) :
    ∀ P : Sylow 2 G, ¬ (P : Subgroup G) ≤ centralizer ({t} : Set G) := by
  intro P hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hRQ⟩ := h.exists_isSylowOf_le d
  obtain ⟨T, hT⟩ := h.exists_sylow_eq_of_le hP hQ
  have hQG : IsSylowOf 2 Q ⊤ := CFSG.ABGLocalTools.isSylowOf_of_card le_top (by
    rw [← hT, Sylow.card_eq_multiplicity, Subgroup.card_top])
  have hQN : Q ≤ normalizer (yamadaR d t : Set G) :=
    le_normalizer.trans (h.normalizer_le_normalizer_yamadaR d hQ.isPGroup hQ.le hRQ)
  have hodd := odd_ncard_conj_D4 (hQG.of_le hQN le_top) hQ.le
  have hV : ((d.V.map L.subtype : Subgroup G) : Set G).ncard = 2 ^ f := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, card_map_of_injective L.subtype_injective,
      d.card_V]
  rw [hN, Set.ncard_image_of_injective _ (mul_right_injective t), hV] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩)

theorem not_twoCentral_of_four_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hq : 4 ≤ 2 ^ f) : ∀ P : Sylow 2 G, ¬ (P : Subgroup G) ≤ centralizer ({t} : Set G) :=
  h.not_twoCentral_of_conj_set d (h.conj_set_normalizer_yamadaR_eq_of_four_le d hq)

theorem not_twoCentral_of_data (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ∀ P : Sylow 2 G, ¬ (P : Subgroup G) ≤ centralizer ({t} : Set G) := by
  rcases Nat.even_or_odd f with hf | hf
  · refine h.not_twoCentral_of_four_le d ?_
    obtain ⟨e, rfl⟩ := hf
    have he : 1 ≤ e := by have := h.one_le; omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e + e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact h.not_twoCentral_of_odd d hf

theorem conj_set_normalizer_yamadaR_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    {x | ∃ n ∈ normalizer (yamadaR d t : Set G), n * t * n⁻¹ = x} =
      (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hnt⟩ : ∃ n ∈ normalizer (yamadaR d t : Set G), n * t * n⁻¹ ≠ t := by
    by_contra hcon
    push Not at hcon
    obtain ⟨Q, hQ, hRQ⟩ := h.exists_isSylowOf_le d
    have hN : normalizer (Q : Set G) ≤ centralizer ({t} : Set G) := fun n hn => by
      have h1 := hcon n (h.normalizer_le_normalizer_yamadaR d hQ.isPGroup hQ.le hRQ hn)
      rw [mem_centralizer_singleton_iff]
      calc n * t = n * t * n⁻¹ * n := by group
        _ = t * n := by rw [h1]
    obtain ⟨P, hP⟩ :=
      CFSG.LocalAnalysis.EvenBN.Common.exists_sylow_eq_of_isSylowOf_of_normalizer_le hQ hN
    exact h.not_twoCentral_of_data d P (hP ▸ hQ.le)
  exact h.conj_set_normalizer_yamadaR d hn hnt

theorem centralizer_L_inf_of_data (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := centralizer (L : Set G) ⊓ centralizer ({t} : Set G) with hT
  obtain ⟨hTcyc, hT2, hTinv, -⟩ := h.kernel
  have hsq : ∀ c ∈ T, c * c ≠ t := by
    intro c hc hct
    have hmem : t * (d.x₆ 1 : G) ∈ (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) :
        Set G) := ⟨_, ⟨_, d.x₆_mem_V 1, rfl⟩, rfl⟩
    rw [← h.conj_set_normalizer_yamadaR_eq d] at hmem
    obtain ⟨n, hn, hnt⟩ := hmem
    have hcR : c ∈ yamadaR d t := mem_sup_right hc
    have hcc : ∀ r ∈ yamadaR d t, c * r = r * c := by
      intro r hr
      have hr' : r ∈ ((yamadaR d t : Subgroup G) : Set G) := hr
      rw [h.coe_yamadaR d] at hr'
      obtain ⟨s, hs, c', hc', rfl⟩ := hr'
      beta_reduce
      have hc'' : c' ∈ T := hc'
      rw [← mul_assoc, (S_commute_kernel d t s hs c hc).symm, mul_assoc, h.kernel_comm hc hc'',
        mul_assoc]
    obtain ⟨hnR, hnc⟩ := conj_mem_center_of_mem_normalizer_D4 hn hcR hcc
    obtain ⟨v, hv, c', hc', hnvc⟩ := h.exists_mul_of_mem_center_yamadaR d hnR hnc
    have hvc : (v : G) * c' = c' * v := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc').1 v v.2
    have hv2 : (v : G) * v = 1 :=
      congrArg Subtype.val (d.mul_self_eq_one_of_mem_W (d.Y_le_W (d.V_le_Y hv)))
    have htxT : t * (d.x₆ 1 : G) ∈ T := by
      rw [← hnt, ← hct]
      rw [show n * (c * c) * n⁻¹ = (n * c * n⁻¹) * (n * c * n⁻¹) by group, hnvc]
      rw [show (v : G) * c' * (v * c') = v * (c' * v) * c' by group, ← hvc,
        show (v : G) * (v * c') * c' = (v * v) * (c' * c') by group, hv2, one_mul]
      exact mul_mem hc' hc'
    have hxT : (d.x₆ 1 : G) ∈ T := by
      have := mul_mem (inv_mem h.t_mem_kernel) htxT
      rwa [inv_mul_cancel_left] at this
    have hx : (d.x₆ 1 : G) ∈ L ⊓ centralizer (L : Set G) :=
      Subgroup.mem_inf.2 ⟨(d.x₆ 1).2, (Subgroup.mem_inf.1 hxT).1⟩
    rw [h.inf_centralizer_eq_bot, mem_bot] at hx
    exact one_ne_zero (d.x₆_eq_one_iff.1 (Subtype.ext hx))
  have hcard : Nat.card T ≤ 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT2
    by_contra hlt
    push Not at hlt
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> simp_all
    obtain ⟨g₀, hg₀⟩ := hTcyc.exists_generator
    have hord : orderOf g₀ = 2 ^ k := by rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, hk]
    have hdvd : 2 ^ (k - 1) ∣ orderOf g₀ := by
      rw [hord]
      exact pow_dvd_pow 2 (Nat.sub_le k 1)
    have ho2 : orderOf (g₀ ^ 2 ^ (k - 1)) = 2 := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, hord]
      have e : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      rw [e, Nat.mul_div_cancel_left 2 (by positivity : 0 < 2 ^ (k - 1))]
    have ht' := hTinv _ (g₀ ^ 2 ^ (k - 1)).2 (by rw [orderOf_coe]; exact ho2)
    have e' : 2 ^ (k - 2) + 2 ^ (k - 2) = 2 ^ (k - 1) := by
      rw [← two_mul, ← pow_succ']; congr 1; omega
    have hc2 : ((g₀ ^ 2 ^ (k - 2) : T) : G) * ((g₀ ^ 2 ^ (k - 2) : T) : G) =
        ((g₀ ^ 2 ^ (k - 1) : T) : G) := by
      rw [← Subgroup.coe_mul, ← pow_add, e']
    exact hsq _ (g₀ ^ 2 ^ (k - 2)).2 (hc2.trans ht')
  have hle : zpowers t ≤ T := (zpowers_le).2 h.t_mem_kernel
  exact (Subgroup.eq_of_le_of_card_ge hle (hcard.trans h.card_zpowers_t.ge)).symm

omit [Finite G] in
theorem yamadaR_eq_of_eq {q : ℕ} (d : TrialityD4Data L q)
    (hT : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    yamadaR d t = d.S.map L.subtype ⊔ zpowers t := by
  rw [yamadaR, hT]

theorem center_yamadaR_of_eq (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q)
    (hT : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    yamadaR d t ⊓ centralizer (yamadaR d t : Set G) = d.V.map L.subtype ⊔ zpowers t := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzR, hzc⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨v, hv, c, hc, rfl⟩ := h.exists_mul_of_mem_center_yamadaR d hzR
      fun r hr => (mem_centralizer_iff.1 hzc r hr).symm
    rw [hT] at hc
    exact mul_mem (mem_sup_left ⟨v, hv, rfl⟩) (mem_sup_right hc)
  · refine sup_le ?_ ((zpowers_le).2 (Subgroup.mem_inf.2 ⟨mem_sup_right h.t_mem_kernel,
      mem_centralizer_iff.2 fun r hr =>
        mem_centralizer_singleton_iff.1 (h.yamadaR_le_centralizer d hr)⟩))
    rintro _ ⟨v, hv, rfl⟩
    refine Subgroup.mem_inf.2 ⟨mem_sup_left ⟨v, d.V_le_S hv, rfl⟩,
      mem_centralizer_iff.2 fun r hr => ?_⟩
    have hr' : r ∈ ((yamadaR d t : Subgroup G) : Set G) := hr
    rw [h.coe_yamadaR d] at hr'
    obtain ⟨_, ⟨s, hs, rfl⟩, c, hc, rfl⟩ := hr'
    beta_reduce
    have hc' : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hc
    have hsv : (s : G) * v = v * s :=
      congrArg Subtype.val (mem_centralizer_iff.1 (d.S_le_centralizer_V hs) v hv).symm
    have hcv : (v : G) * c = c * v := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc').1 v v.2
    calc (s : G) * c * v = s * (c * v) := by group
      _ = s * (v * c) := by rw [hcv]
      _ = ((s : G) * v) * c := by group
      _ = v * (s * c) := by rw [hsv]; group

theorem conj_t_eq_tV (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    {x | ∃ n ∈ normalizer (yamadaR d t : Set G), n * t * n⁻¹ = x} =
        (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G) ∧
      {x | ∃ n ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G),
          n * t * n⁻¹ = x} =
        (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G) := by
  refine ⟨h.conj_set_normalizer_yamadaR_eq d, ?_⟩
  have hVL : d.V.map L.subtype ≤ L := map_subtype_le _
  have hT := h.centralizer_L_inf_of_data d
  have hNR : normalizer (yamadaR d t : Set G) ≤
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
    intro n hn
    refine mem_normalizer_of_conj_mem_D4 fun x hx => ?_
    have hxZ := (h.center_yamadaR_of_eq d hT).ge hx
    obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.1 hxZ
    obtain ⟨hnR, hnc⟩ := conj_mem_center_of_mem_normalizer_D4 hn hxR
      fun r hr => (mem_centralizer_iff.1 hxc r hr).symm
    rw [← h.center_yamadaR_of_eq d hT]
    exact Subgroup.mem_inf.2 ⟨hnR, mem_centralizer_iff.2 fun r hr => (hnc r hr).symm⟩
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    have htV : t ∈ d.V.map L.subtype ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    rcases (h.mem_sup_zpowers_iff hVL).1 ((mem_normalizer_iff.1 hn t).1 htV) with hV | hV
    · exact absurd (hVL hV) (h.conj_not_mem_L d n)
    · exact ⟨_, hV, by beta_reduce; rw [← mul_assoc, h.t_mul_t, one_mul]⟩
  · intro hx
    rw [← h.conj_set_normalizer_yamadaR_eq d] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact ⟨n, hNR hn, rfl⟩

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
