module

public import CFSG.GH74.Generic.S45.LTransfer
public import CFSG.GH74.Generic.S1.RNormalizer

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace Thm9S45Fusion

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.L5U5 CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.GH74.GLS Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {x : G}

theorem eq_one_of_proj_one_sq {g : G} (hg : g ∈ centralizer ({x} : Set G))
    (h1 : proj x ⟨g, hg⟩ = 1) (hsq : g * g = 1) : g = 1 := by
  have hodd := proj_odd x ⟨g, hg⟩ h1
  have h2 : orderOf (⟨g, hg⟩ : ↥(centralizer ({x} : Set G))) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Subtype.ext hsq)
  have h3 : orderOf (⟨g, hg⟩ : ↥(centralizer ({x} : Set G))) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · exact absurd (h ▸ hodd) (by decide)
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)

theorem piC_ne_one {g : G} (hg : g ∈ centralizer ({x} : Set G)) (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    piC x g ≠ 1 := by
  intro h
  rw [piC_of_mem x hg] at h
  exact hg1 (eq_one_of_proj_one_sq hg h hg2)

theorem exists_conj_lift {a b : G} (ha : a ∈ centralizer ({x} : Set G))
    (hb : b ∈ centralizer ({x} : Set G)) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (ν : CentralizerBar x) (hν : ν * piC x a * ν⁻¹ = piC x b) :
    ∃ c ∈ centralizer ({x} : Set G), c * a * c⁻¹ = b := by
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk'_surjective _ ν
  set a' : ↥(centralizer ({x} : Set G)) := c₀ * ⟨a, ha⟩ * c₀⁻¹ with ha'
  have ha'2 : a' * a' = 1 := by
    have : (⟨a, ha⟩ : ↥(centralizer ({x} : Set G))) * ⟨a, ha⟩ = 1 := Subtype.ext ha2
    calc a' * a' = c₀ * (⟨a, ha⟩ * ⟨a, ha⟩) * c₀⁻¹ := by rw [ha']; group
      _ = 1 := by rw [this]; group
  have hb2' : (⟨b, hb⟩ : ↥(centralizer ({x} : Set G))) * ⟨b, hb⟩ = 1 := Subtype.ext hb2
  have hproj : proj x a' = proj x ⟨b, hb⟩ := by
    rw [piC_of_mem x ha, piC_of_mem x hb] at hν
    rw [ha', map_mul, map_mul, map_inv]
    exact hν
  obtain ⟨r, -, hr⟩ := S1.exists_conj_of_proj_eq ha'2 hb2' hproj
  refine ⟨((r * c₀ : ↥(centralizer ({x} : Set G))) : G), (r * c₀).2, ?_⟩
  have := congrArg Subtype.val hr
  rw [ha'] at this
  simpa [mul_assoc] using this

theorem exists_conj_mem_of_card {Z : Type} [Group Z] [Finite Z] {R : Subgroup Z}
    (hR : IsPGroup 2 ↥R) (hmax : ∀ Q : Sylow 2 Z, Nat.card ↥(Q : Subgroup Z) ≤ Nat.card ↥R) {z : Z}
    (hz : z * z = 1) : ∃ g : Z, g * z * g⁻¹ ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : IsPGroup 2 ↥(zpowers z) :=
    isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hz)
  obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
  obtain ⟨Q', hQ'⟩ := hR.exists_le_sylow
  have hQ'R : (Q' : Subgroup Z) = R :=
    (Subgroup.eq_of_le_of_card_ge hQ' (hmax Q')).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Z Q Q'
  refine ⟨g, ?_⟩
  have h1 : ((g • Q : Sylow 2 Z) : Subgroup Z) = MulAut.conj g • (Q : Subgroup Z) :=
    Sylow.coe_subgroup_smul
  have h2 : g * z * g⁻¹ ∈ ((g • Q : Sylow 2 Z) : Subgroup Z) := by
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨z, hQ (mem_zpowers z), by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [hg, hQ'R] at h2
  exact h2

structure Conf9 (x : G) (Kb : Subgroup (CentralizerBar x)) (T : Subgroup G) : Prop where
  sylow : IsSylowOf 2 T (centralizer ({x} : Set G))
  comm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
  sq : ∀ a ∈ T, a * a = 1
  x_mem : x ∈ T
  x_notin : x ∉ Pre x Kb
  fusion : ∀ t ∈ T, (∃ g : G, g * x * g⁻¹ = t) ↔ t ∉ Pre x Kb
  not_sylow : ¬ IsSylowOf 2 T ⊤
  trans : ∀ r ∈ T ⊓ Pre x Kb, ∀ s ∈ T ⊓ Pre x Kb, r ≠ 1 → s ≠ 1 →
    ∃ c ∈ centralizer ({x} : Set G), c * r * c⁻¹ = s
  hit : ∀ y ∈ Pre x Kb, y * y = 1 →
    ∃ c ∈ centralizer ({x} : Set G), c * y * c⁻¹ ∈ T ⊓ Pre x Kb

theorem exists_conf9 (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hx : orderOf x = 2)
    {Kb : Subgroup (CentralizerBar x)} (hd : KData (CentralizerBar x) Kb (xbar x)) :
    ∃ T : Subgroup G, Conf9 x Kb T := by
  classical
  obtain ⟨R₀, T, hR₀K, hc⟩ := hd.exists_conf2 (card_D_eq_two hs hn hx hd)
  have hcard : Nat.card ↥T = 16 := hc.lift.card_eq.trans hc.S_card
  have h315 : ∀ A' : Subgroup (MulAut ↥T), Nat.card ↥A' ≠ 315 :=
    fun A' => no_subgroup_card_315 ↥T hcard A'
  have hRg : Rg x R₀ T = T ⊓ Pre x Kb := hd.Rg_eq hR₀K hc
  have hfus := hc.fusion_iff hs hn hx h315
  have hxnot : x ∉ Pre x Kb := fun h => hd.notin (by have := h.2; rwa [piC_x] at this)
  refine ⟨T, ⟨hc.lift.sylow, fun a ha b hb => hc.lift.comm hc.S_comm ha hb,
    fun a ha => hc.lift.sq_eq_one hc.S_sq ha, hc.lift.x_mem hx, hxnot, ?_,
    hc.not_isSylowOf_top hs hn hx h315, ?_, ?_⟩⟩
  · intro t ht
    rw [hfus t ht, hRg]
    simp [Subgroup.mem_inf, ht]
  · intro r hr s hs' hr1 hs1
    have hrR : r ∈ Rg x R₀ T := by rw [hRg]; exact hr
    have hsR : s ∈ Rg x R₀ T := by rw [hRg]; exact hs'
    have hrC : r ∈ centralizer ({x} : Set G) := hr.2.1
    have hsC : s ∈ centralizer ({x} : Set G) := hs'.2.1
    have hr2 : r * r = 1 := hc.lift.sq_eq_one hc.S_sq hr.1
    have hs2 : s * s = 1 := hc.lift.sq_eq_one hc.S_sq hs'.1
    obtain ⟨ν, -, hν⟩ := hc.trans (piC x r) (mem_Rg.1 hrR).2.2 (piC_ne_one hrC hr2 hr1)
      (piC x s) (mem_Rg.1 hsR).2.2 (piC_ne_one hsC hs2 hs1)
    exact exists_conj_lift hrC hsC hr2 hs2 ν hν
  · intro y hy hy2
    by_cases hy1 : y = 1
    · exact ⟨1, one_mem _, by rw [hy1]; simp⟩
    · have hyC : y ∈ centralizer ({x} : Set G) := hy.1
      have hyb : piC x y ∈ Kb := hy.2
      have hR₀p : IsPGroup 2 ↥(R₀.subgroupOf Kb) := by
        have hc8 : Nat.card ↥(R₀.subgroupOf Kb) = 2 ^ 3 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀K).toEquiv, hc.R_card]; norm_num
        exact IsPGroup.of_card hc8
      have hmax : ∀ Q : Sylow 2 ↥Kb,
          Nat.card ↥(Q : Subgroup ↥Kb) ≤ Nat.card ↥(R₀.subgroupOf Kb) := by
        intro Q
        obtain ⟨-, -, hQc, -⟩ := hd.facts.2.2 Q
        rw [hQc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀K).toEquiv, hc.R_card]
      have hsq : (⟨piC x y, hyb⟩ : ↥Kb) * ⟨piC x y, hyb⟩ = 1 :=
        Subtype.ext (by
          show piC x y * piC x y = 1
          rw [← piC_mul x hyC hyC, hy2, piC_one])
      obtain ⟨g, hg⟩ := exists_conj_mem_of_card hR₀p hmax hsq
      have hgR : (g : CentralizerBar x) * piC x y * (g : CentralizerBar x)⁻¹ ∈ R₀ := hg
      obtain ⟨t, htT, hπt⟩ := (hc.lift.image _).1 (hc.R_le hgR)
      have htC : t ∈ centralizer ({x} : Set G) := hc.lift.le_C htT
      have ht2 : t * t = 1 := hc.lift.sq_eq_one hc.S_sq htT
      obtain ⟨c, hcC, hct⟩ := exists_conj_lift hyC htC hy2 ht2 (g : CentralizerBar x) hπt.symm
      refine ⟨c, hcC, ?_⟩
      rw [hct]
      exact ⟨htT, htC, by rw [hπt]; exact mul_mem (mul_mem g.2 hyb) (inv_mem g.2)⟩

section Fusion

variable {Kb : Subgroup (CentralizerBar x)} {T : Subgroup G}

omit [Finite G] in
theorem card_centralizer_conj (x g : G) :
    Nat.card ↥(centralizer ({g * x * g⁻¹} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
  apply Nat.card_congr
  refine ⟨fun a => ⟨g⁻¹ * (a : G) * g, ?_⟩, fun b => ⟨g * (b : G) * g⁻¹, ?_⟩, ?_, ?_⟩
  · have ha := Subgroup.mem_centralizer_singleton_iff.1 a.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * (a : G) * g * x = g⁻¹ * ((a : G) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (a : G)) * g := by rw [ha]
      _ = x * (g⁻¹ * (a : G) * g) := by group
  · have hb := Subgroup.mem_centralizer_singleton_iff.1 b.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * (b : G) * g⁻¹ * (g * x * g⁻¹) = g * ((b : G) * x) * g⁻¹ := by group
      _ = g * (x * (b : G)) * g⁻¹ := by rw [hb]
      _ = (g * x * g⁻¹) * (g * (b : G) * g⁻¹) := by group
  · intro a
    apply Subtype.ext
    show g * (g⁻¹ * (a : G) * g) * g⁻¹ = a
    group
  · intro b
    apply Subtype.ext
    show g⁻¹ * (g * (b : G) * g⁻¹) * g = b
    group

theorem Conf9.exists_two_central_T (h : Conf9 x Kb T) {v : G} (hv : v ∈ T ⊓ Pre x Kb)
    (hv1 : v ≠ 1) :
    ∃ Q : Sylow 2 G, v ∈ (Q : Subgroup G) ∧ ∀ s ∈ (Q : Subgroup G), s * v = v * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := h.sylow.isPGroup.exists_le_sylow
  have hS₀syl : IsSylowOf 2 (Q : Subgroup G) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  have hTne : T ≠ (Q : Subgroup G) := fun hTS => h.not_sylow (hTS ▸ hS₀syl)
  have hx1 : x ≠ 1 := fun h1 => h.x_notin (h1 ▸ one_mem (Pre x Kb))
  have hnt : Nontrivial ↥(Q : Subgroup G) :=
    ⟨⟨⟨x, hTQ h.x_mem⟩, 1, fun h1 => hx1 (congrArg Subtype.val h1)⟩⟩
  have hcn : Nontrivial ↥(Subgroup.center ↥(Q : Subgroup G)) := Q.isPGroup'.center_nontrivial
  have hZ2 : 2 ∣ Nat.card ↥(Subgroup.center ↥(Q : Subgroup G)) := by
    have hZp : IsPGroup 2 ↥(Subgroup.center ↥(Q : Subgroup G)) := Q.isPGroup'.to_subgroup _
    obtain ⟨m, hm⟩ := hZp.exists_card_eq
    rcases m with _ | m
    · exfalso
      rw [pow_zero] at hm
      have := Nat.card_eq_one_iff_unique.1 hm
      obtain ⟨a, b, hab⟩ := hcn.1
      exact hab (this.1.elim a b)
    · rw [hm]
      exact dvd_pow_self 2 (Nat.succ_ne_zero m)
  obtain ⟨zz, hzz⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(Q : Subgroup G))) 2 hZ2
  set z : G := ((zz : ↥(Q : Subgroup G)) : G) with hz
  have hzQ : z ∈ (Q : Subgroup G) := (zz : ↥(Q : Subgroup G)).2
  have hzc : ∀ s ∈ (Q : Subgroup G), s * z = z * s := by
    intro s hs
    have := Subgroup.mem_center_iff.1 zz.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hz2 : z * z = 1 := by
    have h1 : orderOf (zz : ↥(Subgroup.center ↥(Q : Subgroup G))) = 2 := hzz
    have h2 : (zz : ↥(Subgroup.center ↥(Q : Subgroup G))) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (zz : ↥(Subgroup.center ↥(Q : Subgroup G)))
      rwa [h1] at this
    have h3 := congrArg
      (fun a : ↥(Subgroup.center ↥(Q : Subgroup G)) => ((a : ↥(Q : Subgroup G)) : G)) h2
    simpa [pow_two] using h3
  have hz1 : z ≠ 1 := by
    intro h1
    have : (zz : ↥(Subgroup.center ↥(Q : Subgroup G))) = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    rw [this, orderOf_one] at hzz
    omega
  have hzC : z ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hzc x (hTQ h.x_mem)).symm
  have hzT : z ∈ T := by
    set U : Subgroup G := T ⊔ zpowers z with hU
    have hUQ : U ≤ (Q : Subgroup G) := sup_le hTQ ((zpowers_le).2 hzQ)
    have hUC : U ≤ centralizer ({x} : Set G) :=
      sup_le h.sylow.le ((zpowers_le).2 hzC)
    have hU2 : IsPGroup 2 ↥U := Q.isPGroup'.to_le hUQ
    have := h.sylow.eq_of_le le_sup_left hUC hU2
    rw [← this]
    exact Subgroup.mem_sup_right (mem_zpowers z)
  have hzR : z ∈ Pre x Kb := by
    by_contra hzn
    obtain ⟨g, hg⟩ := (h.fusion z hzT).2 hzn
    have hcard1 :
        Nat.card ↥(centralizer ({z} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
      rw [← hg]
      exact card_centralizer_conj x g
    have hQC : (Q : Subgroup G) ≤ centralizer ({z} : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzc s hs
    have hdvd : Nat.card ↥(Q : Subgroup G) ∣ Nat.card ↥(centralizer ({x} : Set G)) := by
      rw [← hcard1]
      exact Subgroup.card_dvd_of_le hQC
    obtain ⟨m, hm⟩ := Q.isPGroup'.exists_card_eq
    have hcx : Nat.card ↥T = 2 ^ (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 :=
      h.sylow.card_eq
    have hmle : m ≤ (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 := by
      rw [hm] at hdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
    have hcardle : Nat.card ↥(Q : Subgroup G) ≤ Nat.card ↥T := by
      rw [hm, hcx]
      exact Nat.pow_le_pow_right (by norm_num) hmle
    exact hTne (Subgroup.eq_of_le_of_card_ge hTQ hcardle)
  obtain ⟨c, -, hcz⟩ := h.trans z ⟨hzT, hzR⟩ v hv hz1 hv1
  refine ⟨c • Q, ?_, ?_⟩
  · have h1 : ((c • Q : Sylow 2 G) : Subgroup G) = MulAut.conj c • (Q : Subgroup G) :=
      Sylow.coe_subgroup_smul
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨z, hzQ, by simpa [MulAut.smul_def, MulAut.conj_apply] using hcz⟩
  · intro s hs
    have h1 : ((c • Q : Sylow 2 G) : Subgroup G) = MulAut.conj c • (Q : Subgroup G) :=
      Sylow.coe_subgroup_smul
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists] at hs
    obtain ⟨q, hq, rfl⟩ := hs
    rw [← hcz]
    simp only [MulAut.smul_def, MulAut.conj_apply]
    have := hzc q hq
    calc c * q * c⁻¹ * (c * z * c⁻¹) = c * (q * z) * c⁻¹ := by group
      _ = c * (z * q) * c⁻¹ := by rw [this]
      _ = c * z * c⁻¹ * (c * q * c⁻¹) := by group

omit [Finite G] in
theorem Conf9.controls_fusion_T (h : Conf9 x Kb T) {v : G} (hv : v ∈ T ⊓ Pre x Kb)
    (hv1 : v ≠ 1) :
    ∀ g : G, g * v * g⁻¹ ∈ T → ∃ c ∈ centralizer ({x} : Set G), c * v * c⁻¹ = g * v * g⁻¹ := by
  intro g hgT
  set u : G := g * v * g⁻¹ with hu
  have hu1 : u ≠ 1 := by
    intro h1
    apply hv1
    have : v = g⁻¹ * u * g := by rw [hu]; group
    rw [this, h1]
    group
  have huR : u ∈ Pre x Kb := by
    by_contra hun
    obtain ⟨g', hg'⟩ := (h.fusion u hgT).2 hun
    refine ((h.fusion v hv.1).1 ⟨g⁻¹ * g', ?_⟩) hv.2
    calc g⁻¹ * g' * x * (g⁻¹ * g')⁻¹ = g⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g⁻¹ * u * g := by rw [hg']
      _ = v := by rw [hu]; group
  exact h.trans v hv u ⟨hgT, huR⟩ hv1 hu1

theorem Conf9.x_mem_commutator_T (h : Conf9 x Kb T) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hx : orderOf x = 2) {v : G} (hv : v ∈ T ⊓ Pre x Kb)
    (hv1 : v ≠ 1) :
    ∃ hxv : x ∈ centralizer ({v} : Set G),
      (⟨x, hxv⟩ : ↥(centralizer ({v} : Set G))) ∈ _root_.commutator ↥(centralizer ({v} : Set G)) := by
  have hv2 : v * v = 1 := h.sq v hv.1
  have hvord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  obtain ⟨Q, hvQ, hQc⟩ := h.exists_two_central_T hv hv1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQsyl : IsSylowOf 2 (Q : Subgroup G) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  exact b_III8_6_3 G hs hn x hx T h.sylow v hv.1 (fun p hp => h.comm p hp v hv.1) hvord
    ⟨(Q : Subgroup G), hQsyl, hvQ, hQc⟩ (fun g hg _ => h.controls_fusion_T hv hv1 g hg)

theorem Conf9.x_mem_commutator (h : Conf9 x Kb T) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hx : orderOf x = 2) {y : G} (hy : y ∈ Pre x Kb)
    (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ hxy : x ∈ centralizer ({y} : Set G),
      (⟨x, hxy⟩ : ↥(centralizer ({y} : Set G))) ∈ _root_.commutator ↥(centralizer ({y} : Set G)) := by
  obtain ⟨c, hcC, hcv⟩ := h.hit y hy hy2
  set v : G := c * y * c⁻¹ with hv
  have hv1 : v ≠ 1 := by
    intro h1
    apply hy1
    have : y = c⁻¹ * v * c := by rw [hv]; group
    rw [this, h1]
    group
  obtain ⟨hxv, hcomm⟩ := h.x_mem_commutator_T hs hn hx hcv hv1
  have hxc : c⁻¹ * x * c = x := by
    have : c * x = x * c := mem_centralizer_singleton_iff.1 hcC
    calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
      _ = c⁻¹ * (c * x) := by rw [this]
      _ = x := by group
  have hyv : y = c⁻¹ * v * c := by rw [hv]; group
  have hxv' : x * v = v * x := mem_centralizer_singleton_iff.1 hxv
  have hxy : x ∈ centralizer ({y} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc x * y = (c⁻¹ * x * c) * (c⁻¹ * v * c) := by rw [hxc, ← hyv]
      _ = c⁻¹ * (x * v) * c := by group
      _ = c⁻¹ * (v * x) * c := by rw [hxv']
      _ = (c⁻¹ * v * c) * (c⁻¹ * x * c) := by group
      _ = y * x := by rw [← hyv, hxc]
  refine ⟨hxy, ?_⟩
  have hφmem : ∀ g : ↥(centralizer ({v} : Set G)),
      c⁻¹ * (g : G) * c ∈ centralizer ({y} : Set G) := by
    intro g
    have hg : (g : G) * v = v * (g : G) := mem_centralizer_singleton_iff.1 g.2
    rw [mem_centralizer_singleton_iff]
    calc c⁻¹ * (g : G) * c * y = c⁻¹ * ((g : G) * v) * c := by rw [hyv]; group
      _ = c⁻¹ * (v * (g : G)) * c := by rw [hg]
      _ = y * (c⁻¹ * (g : G) * c) := by rw [hyv]; group
  let φ : ↥(centralizer ({v} : Set G)) →* ↥(centralizer ({y} : Set G)) :=
    MonoidHom.mk' (fun g => ⟨c⁻¹ * (g : G) * c, hφmem g⟩) (fun a b => by
      apply Subtype.ext
      show c⁻¹ * ((a : G) * (b : G)) * c = c⁻¹ * (a : G) * c * (c⁻¹ * (b : G) * c)
      group)
  have hmem : (⟨x, hxy⟩ : ↥(centralizer ({y} : Set G))) = φ ⟨x, hxv⟩ := Subtype.ext hxc.symm
  rw [hmem]
  have hle : (_root_.commutator ↥(centralizer ({v} : Set G))).map φ ≤
      _root_.commutator ↥(centralizer ({y} : Set G)) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hle ⟨_, hcomm, rfl⟩

omit [Finite G] in
theorem Conf9.exists_conj_x (h : Conf9 x Kb T) {y : G} (hyC : y ∈ centralizer ({x} : Set G))
    (hy2 : y * y = 1) (hxy : x * y ∈ Pre x Kb) : ∃ g : G, g * x * g⁻¹ = y := by
  have hx2 : x * x = 1 := h.sq x h.x_mem
  have hcomm : x * y = y * x := (mem_centralizer_singleton_iff.1 hyC).symm
  set k : G := x * y with hk
  have hk2 : k * k = 1 := by
    calc k * k = x * y * (x * y) := rfl
      _ = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcomm]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]
  obtain ⟨c, hcC, hck⟩ := h.hit k hxy hk2
  have hcx : c * x = x * c := mem_centralizer_singleton_iff.1 hcC
  have hcxc : c * x * c⁻¹ = x := by
    calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [hcx]
      _ = x := by group
  have hyk : y = x * k := by
    calc y = (x * x) * y := by rw [hx2, one_mul]
      _ = x * k := by rw [hk]; group
  have hcyc : c * y * c⁻¹ = x * (c * k * c⁻¹) := by
    calc c * y * c⁻¹ = c * (x * k) * c⁻¹ := by rw [← hyk]
      _ = (c * x * c⁻¹) * (c * k * c⁻¹) := by group
      _ = x * (c * k * c⁻¹) := by rw [hcxc]
  have hTmem : x * (c * k * c⁻¹) ∈ T := mul_mem h.x_mem hck.1
  have hnot : x * (c * k * c⁻¹) ∉ Pre x Kb := by
    intro hmem
    apply h.x_notin
    have h' := mul_mem hmem (inv_mem hck.2)
    rwa [show x * (c * k * c⁻¹) * (c * k * c⁻¹)⁻¹ = x by group] at h'
  obtain ⟨g, hg⟩ := (h.fusion _ hTmem).2 hnot
  refine ⟨c⁻¹ * g, ?_⟩
  calc c⁻¹ * g * x * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
    _ = c⁻¹ * (c * y * c⁻¹) * c := by rw [hg, hcyc]
    _ = y := by group

end Fusion

end Thm9S45Fusion

end CFSG.GH74.Generic.BProg.B3
