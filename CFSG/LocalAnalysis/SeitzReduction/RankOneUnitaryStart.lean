module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStart
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
public import CFSG.GH74.Uniqueness.Bender.Sylow2Special

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender

structure U3Start (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T : Subgroup G) : Prop where
  setting : SeitzSetting G L
  model : LieModel L .PSU 3 2 f
  two_le : 2 ≤ f
  inv : orderOf t = 2
  mem : t ∈ centralizer (L : Set G)
  le : T ≤ centralizer ({t} : Set G)
  sylow : ∃ P : Sylow 2 (centralizer ({t} : Set G)),
    (P : Subgroup _) = T.subgroupOf (centralizer ({t} : Set G))

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem card_sylow
    (h : U3Start G L f t T) : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2 :=
  rankOneKernel G L h.setting (Or.inr (Or.inl ⟨f, h.two_le, h.model⟩))

theorem sq_eq_one (h : U3Start G L f t T) : t ^ 2 = 1 := by
  rw [← h.inv]
  exact pow_orderOf_eq_one t

theorem mem_centralizer_szT₁ (h : U3Start G L f t T) : t ∈ centralizer (szT₁ L T : Set G) :=
  centralizer_le (szT₁_le_right L T) h.mem

theorem isPGroup (h : U3Start G L f t T) : IsPGroup 2 T := by
  obtain ⟨P, hP⟩ := h.sylow
  have hP' := P.isPGroup'
  rw [hP] at hP'
  exact hP'.of_equiv (subgroupOfEquivOfLe h.le)

theorem le_normalizer (h : U3Start G L f t T) : T ≤ normalizer (L : Set G) :=
  h.le.trans (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    h.setting.standardSetting.standard h.mem h.inv).1

theorem start_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    t ∈ T ∧ T ⊓ centralizer (L : Set G) = zpowers t ∧
      (∃ Q : Sylow 2 L, (Q : Subgroup L) = (szT₁ L T).subgroupOf L) ∧
      T ≤ normalizer (szT₁ L T : Set G) ∧ szT₁ L T ⊓ zpowers t = ⊥ ∧
      ((szT₁ L T ⊔ zpowers t).subgroupOf T).Normal ∧
      ∀ x ∈ T, ∀ l ∈ L, (∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) → x ∈ szT₁ L T ⊔ zpowers t := by
  have hst := h.setting.standardSetting
  obtain ⟨-, htT, hTC, -, ⟨U, hU⟩, hTU, hUt, hUtn, hinner⟩ :=
    sylow_centralizer_start_of_card_sylow_eq_two hst.standard h.setting.center_eq_bot hS2 h.mem
      h.inv (hst.core t h.inv) h.le h.sylow
  exact ⟨htT, hTC, ⟨U, by rw [hU, szT₁, inf_subgroupOf_right]⟩, hTU, hUt, hUtn, hinner⟩

theorem exists_bender_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (e : ℕ) (Q : Sylow 2 L), BenderType L f 3 e ∧
      (∀ y : L, y ∈ (Q : Subgroup L) ↔ (y : G) ∈ szT₁ L T) ∧
      ∀ y : L, y ∈ rootCenter (Q : Subgroup L) ↔ (y : G) ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, -, ⟨Q, hQ⟩, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨e, hB⟩ := exists_benderType_of_lieModel_psu3 h.two_le h.model
  have hmemQ : ∀ y : L, y ∈ (Q : Subgroup L) ↔ (y : G) ∈ szT₁ L T := fun y => by
    rw [hQ, mem_subgroupOf]
  refine ⟨e, Q, hB, hmemQ, fun y => ?_⟩
  rw [rootCenter, mem_inf, mem_szA₁, hmemQ, mem_centralizer_iff, mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun hc x hx => ?_, fun hc x hx => ?_⟩
  · exact congrArg Subtype.val (hc ⟨x, szT₁_le_right L T hx⟩ ((hmemQ _).mpr hx))
  · exact Subtype.ext (hc x ((hmemQ x).mp hx))

omit [Finite G] in
theorem map_subtype_eq_of_mem_iff {L T₁ : Subgroup G} {Q : Subgroup L} (hT₁ : T₁ ≤ L)
    (hmem : ∀ y : L, y ∈ Q ↔ (y : G) ∈ T₁) : Q.map L.subtype = T₁ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hmem y).mp hy
  · intro hx
    exact ⟨⟨x, hT₁ hx⟩, (hmem _).mpr hx, rfl⟩

theorem facts_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (szT₁ L T) = (2 ^ f) ^ 3 ∧ Nat.card (szA₁ (szT₁ L T)) = 2 ^ f ∧
      szA₁ (szT₁ L T) = ⁅szT₁ L T, szT₁ L T⁆ ∧
      (∀ x ∈ szT₁ L T, x ^ 2 ∈ szA₁ (szT₁ L T)) ∧
      (∀ x ∈ szT₁ L T, x ^ 2 = 1 → x ∈ szA₁ (szT₁ L T)) ∧
      (∀ x ∈ szA₁ (szT₁ L T), x ^ 2 = 1) ∧
      ∀ x ∈ szT₁ L T ⊔ zpowers t, x ^ 2 = 1 → x ∈ szA L T t := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  have hT₁ : (Q : Subgroup L).map L.subtype = szT₁ L T :=
    map_subtype_eq_of_mem_iff (szT₁_le_right L T) hmemQ
  have hA₁ : (rootCenter (Q : Subgroup L)).map L.subtype = szA₁ (szT₁ L T) :=
    map_subtype_eq_of_mem_iff ((szA₁_le _).trans (szT₁_le_right L T)) hmemZ
  have hsq : ∀ x ∈ szT₁ L T, x ^ 2 ∈ szA₁ (szT₁ L T) := by
    intro x hx
    have h1 := hB.sq_mem_rootCenter_unitary Q ((hmemQ ⟨x, szT₁_le_right L T hx⟩).mpr hx)
    have h2 := (hmemZ _).mp h1
    rwa [coe_mul, ← sq] at h2
  have hinv : ∀ x ∈ szT₁ L T, x ^ 2 = 1 → x ∈ szA₁ (szT₁ L T) := by
    intro x hx hx2
    have h1 := hc.mem_rootCenter_of_mul_self ((hmemQ ⟨x, szT₁_le_right L T hx⟩).mpr hx)
      (Subtype.ext (by rw [coe_mul, ← sq, hx2]; rfl))
    exact (hmemZ _).mp h1
  refine ⟨?_, ?_, ?_, hsq, hinv, fun x hx => ?_, fun x hx hx2 => ?_⟩
  · rw [← hT₁, card_map_of_injective L.subtype_injective]
    exact hc.card_eq
  · rw [← hA₁, card_map_of_injective L.subtype_injective]
    exact hc.card_center
  · rw [← hA₁, ← (hB.lemma_3_5_a_unitary Q).1, map_commutator, hT₁]
  · have hxL : x ∈ L := szT₁_le_right L T (szA₁_le _ hx)
    have h1 := hc.center_sq ⟨x, hxL⟩ ((hmemZ ⟨x, hxL⟩).mpr hx)
    have h2 := congrArg Subtype.val h1
    rwa [coe_mul, ← sq] at h2
  · obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hx
    have hyz : Commute y z :=
      commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy)
    have hz2 : z ^ 2 = 1 := by
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
      · exact one_pow 2
      · exact h.sq_eq_one
    rw [hyz.mul_pow, hz2, mul_one] at hx2
    exact mul_mem (mem_sup_left (hinv y hy hx2)) (mem_sup_right hz)

theorem szA_facts_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (szA L T t) = 2 * 2 ^ f ∧ (∀ x ∈ szA L T t, x ^ 2 = 1) ∧
      szA L T t ≤ centralizer ((szT₁ L T ⊔ zpowers t : Subgroup G) : Set G) ∧
      ∀ x ∈ szA L T t, ∀ y ∈ szA L T t, x * y = y * x := by
  obtain ⟨-, -, -, -, hdisj, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, hA₁card, -, -, -, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  have htC := h.mem_centralizer_szT₁
  have hAC : szA L T t ≤ centralizer ((szT₁ L T ⊔ zpowers t : Subgroup G) : Set G) :=
    sup_le (szA₁_le_centralizer_sup_zpowers htC)
      (zpowers_le.mpr (mem_centralizer_sup_zpowers htC))
  have hAle : szA L T t ≤ szT₁ L T ⊔ zpowers t := sup_le_sup_right (szA₁_le _) _
  refine ⟨?_, fun x hx => ?_, hAC, fun x hx y hy => ?_⟩
  · rw [szA, card_szA₁_sup htC h.inv hdisj, hA₁card, mul_comm]
  · obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers
      (centralizer_le (szA₁_le _) htC) hx
    have hbz : Commute b z := commute_of_mem_zpowers hz
      (mem_centralizer_iff.mp htC b (szA₁_le _ hb))
    have hz2 : z ^ 2 = 1 := by
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
      · exact one_pow 2
      · exact h.sq_eq_one
    rw [hbz.mul_pow, hA₁sq b hb, hz2, one_mul]
  · exact (mem_centralizer_iff.mp (hAC hx) y (hAle hy)).symm

theorem outer_facts_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} (hxT : x ∈ T)
    (hx2 : x ^ 2 = 1) (hx : x ∉ szT₁ L T ⊔ zpowers t) :
    (¬ ∃ l ∈ L, ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) ∧
      (∀ a ∈ szA₁ (szT₁ L T), x * a = a * x) ∧
      (∀ y ∈ szT₁ L T, x * y = y * x → y ∈ szA₁ (szT₁ L T)) ∧
      ∃ w ∈ szT₁ L T, w ∉ szA₁ (szT₁ L T) ∧ x * w * x⁻¹ = w⁻¹ := by
  obtain ⟨-, -, -, hTN₁, -, -, hinner⟩ := h.start_of_card_sylow hS2
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  have hout : ¬ ∃ l ∈ L, ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹ := fun ⟨l, hl, hxl⟩ =>
    hx (hinner x hxT l hl hxl)
  set σ := L.normalizerMonoidHom ⟨x, h.le_normalizer hxT⟩ with hσdef
  have hσ : ∀ y : L, ((σ y : L) : G) = x * y * x⁻¹ := fun y =>
    normalizerMonoidHom_apply_apply_coe L _ y
  have hxx : x * x = 1 := by rw [← sq, hx2]
  have hσσ : σ * σ = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hσ, hσ]
    calc x * (x * (y : G) * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = y := by rw [hxx]; group
  have hσout : ¬ ∃ g : L, ∀ y : L, σ y = g * y * g⁻¹ := by
    rintro ⟨g, hg⟩
    refine hout ⟨g, g.2, fun y hy => ?_⟩
    have := congrArg Subtype.val (hg ⟨y, hy⟩)
    rw [hσ] at this
    simpa using this
  have hσQ : ∀ y ∈ (Q : Subgroup L), σ y ∈ (Q : Subgroup L) := by
    intro y hy
    rw [hmemQ, hσ]
    exact (mem_normalizer_iff.mp (hTN₁ hxT) y).mp ((hmemQ y).mp hy)
  have hfix : ∀ {y : L}, y ∈ (Q : Subgroup L) → (σ y = y ↔ y ∈ rootCenter (Q : Subgroup L)) :=
    fun hy => hB.fixed_iff_rootCenter_unitary Q σ hσσ hσout hσQ hy
  refine ⟨hout, fun a ha => ?_, fun y hy hxy => ?_, ?_⟩
  · have haL : a ∈ L := szT₁_le_right L T (szA₁_le _ ha)
    have h1 := (hfix ((hmemQ ⟨a, haL⟩).mpr (szA₁_le _ ha))).mpr ((hmemZ ⟨a, haL⟩).mpr ha)
    have h2 := congrArg Subtype.val h1
    rw [hσ] at h2
    calc x * a = x * a * x⁻¹ * x := by group
      _ = a * x := by rw [h2]
  · have hyL : y ∈ L := szT₁_le_right L T hy
    refine (hmemZ ⟨y, hyL⟩).mp ((hfix ((hmemQ ⟨y, hyL⟩).mpr hy)).mp (Subtype.ext ?_))
    rw [hσ]
    show x * y * x⁻¹ = y
    rw [hxy, mul_inv_cancel_right]
  · obtain ⟨hWQ, -, hWcard, -, hWinv, -⟩ := hB.lemma_3_4_d5_unitary Q σ hσσ hσout hσQ
    have hex : ∃ w ∈ commutatorAut (Q : Subgroup L) σ, w ∉ rootCenter (Q : Subgroup L) := by
      by_contra hne
      push Not at hne
      have hle : Nat.card (commutatorAut (Q : Subgroup L) σ) ≤
          Nat.card (rootCenter (Q : Subgroup L)) := card_le_of_le hne
      rw [hWcard, hc.card_center] at hle
      have h4 : 4 ≤ 2 ^ f :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
      have : 2 ^ f < (2 ^ f) ^ 2 := by nlinarith
      omega
    obtain ⟨w, hwW, hwZ⟩ := hex
    refine ⟨w, (hmemQ w).mp (hWQ hwW), fun hw => hwZ ((hmemZ w).mpr hw), ?_⟩
    have := congrArg Subtype.val (hWinv w hwW)
    rw [hσ] at this
    simpa using this

theorem mem_szA_iff_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} :
    x ∈ szA L T t ↔ x ∈ T ∧ x ^ 2 = 1 ∧ ∀ y ∈ T, y ^ 2 = 1 → x * y = y * x := by
  obtain ⟨htT, -, -, -, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, hinvT₁, -, hinvA⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, hAsq, hAC, -⟩ := h.szA_facts_of_card_sylow hS2
  have hAle : szA L T t ≤ szT₁ L T ⊔ zpowers t := sup_le_sup_right (szA₁_le _) _
  have hsupT : szT₁ L T ⊔ zpowers t ≤ T := sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)
  constructor
  · intro hx
    refine ⟨hsupT (hAle hx), hAsq x hx, fun y hy hy2 => ?_⟩
    by_cases hyS : y ∈ szT₁ L T ⊔ zpowers t
    · exact mem_centralizer_iff.mp (hAC hx) y hyS |>.symm
    · obtain ⟨-, hyA₁, -, -⟩ := h.outer_facts_of_card_sylow hS2 hy hy2 hyS
      have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp (h.le hy)
      have hle : szA L T t ≤ centralizer ({y} : Set G) := by
        refine sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (hyA₁ a ha).symm) ?_
        rw [zpowers_le]
        exact mem_centralizer_singleton_iff.mpr hyt.symm
      exact mem_centralizer_singleton_iff.mp (hle hx)
  · rintro ⟨hxT, hx2, hxc⟩
    by_cases hxS : x ∈ szT₁ L T ⊔ zpowers t
    · exact hinvA x hxS hx2
    · exfalso
      obtain ⟨-, -, -, w, hwT₁, hwA₁, hxw⟩ := h.outer_facts_of_card_sylow hS2 hxT hx2 hxS
      have hxx : x * x = 1 := by rw [← sq, hx2]
      have hxw' : x * w = w⁻¹ * x := by
        calc x * w = x * w * x⁻¹ * x := by group
          _ = w⁻¹ * x := by rw [hxw]
      have hwx2 : (w * x) ^ 2 = 1 := by
        calc (w * x) ^ 2 = w * (x * w) * x := by rw [sq]; group
          _ = x * x := by rw [hxw']; group
          _ = 1 := hxx
      have hc := hxc (w * x) (mul_mem (szT₁_le_left L T hwT₁) hxT) hwx2
      have hcw : x * w = w * x := by
        have : x * w * x = w * x * x := by rw [← hc]; group
        exact mul_right_cancel this
      have hww : w ^ 2 = 1 := by
        have h1 : w⁻¹ = w := by
          calc w⁻¹ = x * w * x⁻¹ := hxw.symm
            _ = w := by rw [hcw, mul_inv_cancel_right]
        calc w ^ 2 = w * w := sq w
          _ = w * w⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel w
      exact hwA₁ (hinvT₁ w hwT₁ hww)

theorem normalizer_le_normalizer_szA_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    normalizer (T : Set G) ≤ normalizer (szA L T t : Set G) := by
  have key : ∀ n ∈ normalizer (T : Set G), ∀ x ∈ szA L T t, n * x * n⁻¹ ∈ szA L T t := by
    intro n hn x hx
    obtain ⟨hxT, hx2, hxc⟩ := (h.mem_szA_iff_of_card_sylow hS2).mp hx
    refine (h.mem_szA_iff_of_card_sylow hS2).mpr ⟨(mem_normalizer_iff.mp hn x).mp hxT, ?_,
      fun y hy hy2 => ?_⟩
    · calc (n * x * n⁻¹) ^ 2 = n * x ^ 2 * n⁻¹ := by rw [sq, sq]; group
        _ = 1 := by rw [hx2]; group
    · have hy' : n⁻¹ * y * n ∈ T := (mem_normalizer_iff''.mp hn y).mp hy
      have hy2' : (n⁻¹ * y * n) ^ 2 = 1 := by
        calc (n⁻¹ * y * n) ^ 2 = n⁻¹ * y ^ 2 * n := by rw [sq, sq]; group
          _ = 1 := by rw [hy2]; group
      have e := hxc _ hy' hy2'
      calc n * x * n⁻¹ * y = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by rw [e]
        _ = y * (n * x * n⁻¹) := by group
  intro n hn
  refine mem_normalizer_iff.mpr fun x => ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

end U3Start

end CFSG.SeitzReduction.RankOne
