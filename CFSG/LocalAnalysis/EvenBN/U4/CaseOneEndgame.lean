module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneFusion
public import CFSG.LocalAnalysis.EvenBN.Common.Endgames
public import CFSG.LocalAnalysis.EvenBN.Common.FreeSeries
public import CFSG.LocalAnalysis.SteinbergBNPerfectFirstTransferExclusion

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup)
open scoped MatrixGroups

theorem isElementaryAbelian_quotient_of_exists {G : Type*} [Group G] {H K X : Subgroup G}
    [(K.subgroupOf H).Normal] (hXH : X ≤ H) (hX : ∀ x ∈ H, ∃ w ∈ X, w⁻¹ * x ∈ K)
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hsq : ∀ a ∈ X, a * a = 1) :
    IsElementaryAbelian 2 (H ⧸ K.subgroupOf H) := by
  have hmk : ∀ z : H ⧸ K.subgroupOf H, ∃ w : G, ∃ hw : w ∈ X,
      z = QuotientGroup.mk (⟨w, hXH hw⟩ : H) := by
    intro z
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨w, hw, hwx⟩ := hX x hx
    refine ⟨w, hw, ?_⟩
    rw [QuotientGroup.eq, mem_subgroupOf]
    have := inv_mem hwx
    rwa [mul_inv_rev, inv_inv] at this
  exact
    { is_comm := ⟨fun a b => by
        obtain ⟨u, hu, rfl⟩ := hmk a
        obtain ⟨v, hv, rfl⟩ := hmk b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (hcomm u hu v hv)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨u, hu, rfl⟩ := hmk a
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
        change u ^ 2 ∈ K
        rw [sq, hsq u hu]
        exact one_mem _ }

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓡" => miyamotoRG h L η t Q

local notation "𝓟" => miyamotoPG h L η

local notation "𝓕" => miyamotoF1G h L η t

theorem of_sylow (hS : Setting h L η t Q T) {T' : Subgroup G}
    (hT' : IsSylowOf 2 T' (centralizer ({t} : Set G))) (hQT' : Q ≤ T') :
    Setting h L η t Q T' := by
  obtain ⟨hf, hL, hLn, hpp, hcyc, ht, ht2, hQ, hQs, htQ, hPQ, -, -, -⟩ := hS.setup
  exact ⟨hS.simple, hS.nonabelian, hS.oddCore, hf, hL, hLn, hpp, hcyc, ht, ht2, hQ, hQs, htQ, hPQ,
    hT'.le, hT'.exists_sylow_eq_subgroupOf, hQT'⟩

theorem T_le_normalizer_RG (hS : Setting h L η t Q T) : T ≤ normalizer (𝓡 : Set G) :=
  hS.T_le_normalizer_Q1.trans hS.normalizer_Q1_le_normalizer_RG

theorem PG_le_RG (hS : Setting h L η t Q T) : 𝓟 ≤ 𝓡 :=
  le_sup_right.trans hS.P1_le_miyamotoRG

theorem T_inf_RG (hS : Setting h L η t Q T) : T ⊓ 𝓡 = 𝓟 := by
  refine le_antisymm ?_ (le_inf hS.P_le_T hS.PG_le_RG)
  rw [← hS.RG_inf_C, inf_comm]
  exact inf_le_inf_left _ hS.T_le

theorem commutator_mem_PG_of_mem_T (hS : Setting h L η t Q T) {x y : G} (hx : x ∈ T)
    (hy : y ∈ T) : x * y * x⁻¹ * y⁻¹ ∈ 𝓟 := by
  have := isCyclic_ringEquiv_of_unitaryFieldData h
  have : ((𝓟 : Subgroup G).subgroupOf T).Normal :=
    (normal_subgroupOf_iff_le_normalizer hS.P_le_T).2 hS.T_le_normalizer_P
  have hker : (𝓟 : Subgroup G).subgroupOf T ≤ (hS.fieldFactor.comp (inclusion hS.T_le)).ker :=
    fun p hp => hS.fieldFactor_of_mem_L (miyamotoPull_le h L η _ (mem_subgroupOf.1 hp))
  set σ := QuotientGroup.lift ((𝓟 : Subgroup G).subgroupOf T)
    (hS.fieldFactor.comp (inclusion hS.T_le)) hker with hσ
  have hcen : σ.ker ≤ center (T ⧸ (𝓟 : Subgroup G).subgroupOf T) := by
    intro z hz
    obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MonoidHom.mem_ker, hσ, QuotientGroup.lift_mk, MonoidHom.comp_apply] at hz
    obtain ⟨l, hl, c, hc, e⟩ := (hS.fieldFactor_eq_one_iff _).1 hz
    have hlP := hS.mem_P_of_mul ha hl hc e
    have hcT := hS.kernel_le_T hc
    have hcomm : ∀ b ∈ centralizer ({t} : Set G), c * b = b * c := by
      intro b hb
      rw [hS.kernel_eq_zpowers'] at hc
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      exact (Commute.zpow_left (mem_centralizer_singleton_iff.1 hb).symm k).eq
    have e' : (QuotientGroup.mk ⟨a, ha⟩ : T ⧸ (𝓟 : Subgroup G).subgroupOf T) =
        QuotientGroup.mk ⟨c, hcT⟩ := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      change a⁻¹ * c ∈ 𝓟
      have hlc : l * c = c * l := (hcomm l (hS.L_le_centralizer hl)).symm
      rw [show a = l * c from e, hlc, mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem hlP
    rw [e', mem_center_iff]
    intro w
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcomm b (hS.T_le hb)).symm
  have hab := σ.isMulCommutative_of_isCyclic_of_ker_le_center hcen
  have e := hab.is_comm.comm
    (QuotientGroup.mk ⟨y⁻¹, inv_mem hy⟩ : T ⧸ (𝓟 : Subgroup G).subgroupOf T)
    (QuotientGroup.mk ⟨x⁻¹, inv_mem hx⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at e
  have e2 : (((⟨y⁻¹, inv_mem hy⟩ * ⟨x⁻¹, inv_mem hx⟩ : T)⁻¹ *
      (⟨x⁻¹, inv_mem hx⟩ * ⟨y⁻¹, inv_mem hy⟩) : T) : G) = x * y * x⁻¹ * y⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rwa [e2] at e

theorem exists_conj_eq_of_mem_RG (hS : Setting h L η t Q T) {r : G} (hr : r ∈ 𝓡)
    (hx : orderOf (t * r) = 2) : ∃ m ∈ 𝓡, t * r = m⁻¹ * t * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFR : 𝓕 ≤ 𝓡 := le_sup_left.trans hS.P1_le_miyamotoRG
  have hFn : ((𝓕 : Subgroup G).subgroupOf 𝓡).Normal :=
    (normal_subgroupOf_iff_le_normalizer hFR).2 hS.RG_le_normalizer_F1
  have : ∀ i : Fin 2, (((![⊥, 𝓕, 𝓡] : Fin 3 → Subgroup G) i.castSucc).subgroupOf
      ((![⊥, 𝓕, 𝓡] : Fin 3 → Subgroup G) i.succ)).Normal := by
    intro i
    fin_cases i
    · show ((⊥ : Subgroup G).subgroupOf 𝓕).Normal
      infer_instance
    · exact hFn
  have : ∀ i : Fin 2, IsElementaryAbelian 2 ((![⊥, 𝓕, 𝓡] : Fin 3 → Subgroup G) i.succ ⧸
      ((![⊥, 𝓕, 𝓡] : Fin 3 → Subgroup G) i.castSucc).subgroupOf
        ((![⊥, 𝓕, 𝓡] : Fin 3 → Subgroup G) i.succ)) := by
    intro i
    fin_cases i
    · exact isElementaryAbelian_quotient_of_exists (H := 𝓕) (K := ⊥) (X := 𝓕) le_rfl
        (fun x hx => ⟨x, hx, by rw [inv_mul_cancel]; exact one_mem _⟩)
        (fun a ha b hb => hS.F1_comm ha hb) hS.F1_mul_self
    · refine isElementaryAbelian_quotient_of_exists (H := 𝓡) (K := 𝓕)
        (X := 𝓡 ⊓ centralizer (miyamotoI1G h L η : Set G)) inf_le_left (fun x hx => ?_)
        (fun a ha b hb => hS.W_comm ha hb) (fun a ha => hS.W_mul_self ha)
      obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hx
      exact ⟨w, hw, by rwa [inv_mul_cancel_left]⟩
  refine Common.involution_coset_conj_of_card_sq (W := 𝓡) hS.t_two ![⊥, 𝓕, 𝓡] rfl rfl ?_ ?_ ?_
    hr hx
  · intro i
    fin_cases i
    · exact bot_le
    · exact hFR
  · intro i
    fin_cases i
    · show t ∈ normalizer ((⊥ : Subgroup G) : Set G)
      refine mem_normalizer_fintype fun n hn => ?_
      rw [SetLike.mem_coe, mem_bot] at hn ⊢
      rw [hn, mul_one, mul_inv_cancel]
    · exact hS.t_mem_normalizer_F1
    · exact hS.t_mem_normalizer_RG
  · intro i
    fin_cases i
    · show Nat.card (𝓕 ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 = Nat.card 𝓕
      rw [hS.F1_inf_C, card_miyamotoA1G, hS.card_F1]
      ring
    · show Nat.card (𝓡 ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 = Nat.card 𝓡
      rw [hS.RG_inf_C, card_miyamotoPG, hS.card_miyamotoRG]
      ring

theorem exists_sylow_eq_RG_sup (hS : Setting h L η t Q T)
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ 𝓡 ⊔ T → t⁻¹ * (g⁻¹ * t * g) ∈ 𝓡) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = 𝓡 ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 (𝓡 ⊔ T : Subgroup G) :=
    hS.isPGroup_RG.to_sup_of_normal_left' hS.isPGroup_T hS.T_le_normalizer_RG
  obtain ⟨S', hSS'⟩ := hSp.exists_le_sylow
  refine ⟨S', le_antisymm ?_ hSS'⟩
  by_contra hne
  have hlt : (𝓡 ⊔ T : Subgroup G).subgroupOf (S' : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun x hx => ?_
    have hx' : (⟨x, hx⟩ : (S' : Subgroup G)) ∈ (𝓡 ⊔ T : Subgroup G).subgroupOf S' := by
      rw [htop]
      exact mem_top _
    exact hx'
  have := S'.isPGroup'.isNilpotent
  obtain ⟨g, hgN, hgS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hgN' : ∀ s ∈ 𝓡 ⊔ T, (g : G)⁻¹ * s * g ∈ 𝓡 ⊔ T := by
    intro s hs
    have h1 := (mem_normalizer_iff.1 (inv_mem hgN) ⟨s, hSS' hs⟩).1 hs
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hy := hfus g (hgN' t (mem_sup_right hS.t_mem_T))
  have hord : orderOf (t * (t⁻¹ * ((g : G)⁻¹ * t * g))) = 2 := by
    rw [mul_inv_cancel_left]
    have := MulEquiv.orderOf_eq (MulAut.conj (g : G)⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, hS.t_two]
  obtain ⟨m, hm, hmt⟩ := hS.exists_conj_eq_of_mem_RG hy hord
  rw [mul_inv_cancel_left] at hmt
  have hcC : (g : G) * m⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc (g : G) * m⁻¹ * t = g * (m⁻¹ * t * m) * m⁻¹ := by group
      _ = g * ((g : G)⁻¹ * t * g) * m⁻¹ := by rw [hmt]
      _ = t * (g * m⁻¹) := by group
  have hCS : centralizer ({t} : Set G) ⊓ S' = T :=
    hS.T_sylow.eq_of_le (le_inf hS.T_le (le_sup_right.trans hSS')) inf_le_left
      (S'.isPGroup'.to_le inf_le_right)
  have hcT : (g : G) * m⁻¹ ∈ T := by
    have hmS : m ∈ (S' : Subgroup G) := hSS' (mem_sup_left hm)
    rw [← hCS]
    exact mem_inf.2 ⟨hcC, mul_mem g.2 (inv_mem hmS)⟩
  apply hgS
  rw [mem_subgroupOf, show (g : G) = (g * m⁻¹) * m by group]
  exact mul_mem (mem_sup_right hcT) (mem_sup_left hm)

theorem isPerfect (hS : Setting h L η t Q T) : Group.IsPerfect G := by
  have := hS.simple
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := hS.nonabelian
    have h1 := commutator_mem_commutator (mem_top a) (mem_top b)
    rw [← _root_.commutator_def, hb, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab h1
  · exact ht

theorem false_of_forall_conj_ne (hS : Setting h L η t Q T) (hR : ∀ g : G, g⁻¹ * t * g ∉ 𝓡)
    (hT : ∀ x (hx : x ∈ T), x * x ∈ 𝓟 → hS.fieldFactor ⟨x, hS.T_le hx⟩ ≠ 1 →
      ∀ r ∈ 𝓡, ∀ g : G, g⁻¹ * t * g ≠ r * x) : False := by
  have hTN := hS.T_le_normalizer_RG
  have hPR := hS.PG_le_RG
  have hfus : ∀ g : G, g⁻¹ * t * g ∈ 𝓡 ⊔ T → t⁻¹ * (g⁻¹ * t * g) ∈ 𝓡 := by
    intro g hg
    obtain ⟨r, hr, x, hx, hrx⟩ := exists_mul_of_mem_sup_of_le_normalizer' hTN hg
    have hyy : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
      rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, hS.t_mul_t]
      group
    have hxx : x * x ∈ 𝓟 := by
      rw [← hS.T_inf_RG]
      refine mem_inf.2 ⟨mul_mem hx hx, ?_⟩
      have h1 : x * r * x⁻¹ ∈ 𝓡 := (mem_normalizer_iff.1 (hTN hx) r).1 hr
      rw [show x * x = (x * r * x⁻¹)⁻¹ * r⁻¹ * ((r * x) * (r * x)) by group, ← hrx, hyy,
        mul_one]
      exact mul_mem (inv_mem h1) (inv_mem hr)
    by_cases hσ : hS.fieldFactor ⟨x, hS.T_le hx⟩ = 1
    · obtain ⟨l, hl, c, hc, e⟩ := (hS.fieldFactor_eq_one_iff _).1 hσ
      have hlP := hS.mem_P_of_mul hx hl hc e
      rw [hS.kernel_eq_zpowers'] at hc
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      have e' : x = l * t ^ k := e
      rcases hS.zpow_t_eq k with h1 | h1
      · exfalso
        apply hR g
        rw [hrx, e', h1, mul_one]
        exact mul_mem hr (hPR hlP)
      · rw [hrx, e', h1]
        have h2 := (mem_normalizer_iff.1 (inv_mem hS.t_mem_normalizer_RG) (r * l)).1
          (mul_mem hr (hPR hlP))
        rw [inv_inv] at h2
        rwa [show t⁻¹ * (r * (l * t)) = t⁻¹ * (r * l) * t by group]
    · exact absurd hrx (hT x hx hxx hσ r hr g)
  obtain ⟨S, hS'⟩ := hS.exists_sylow_eq_RG_sup hfus
  have hRS : 𝓡 ≤ 𝓡 ⊔ T := le_sup_left
  have : ((𝓡 : Subgroup G).subgroupOf (𝓡 ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRS).2 (sup_le le_normalizer hTN)
  have hmk : ∀ z : (𝓡 ⊔ T : Subgroup G) ⧸ (𝓡 : Subgroup G).subgroupOf (𝓡 ⊔ T), ∃ x : G,
      ∃ hx : x ∈ T, z = QuotientGroup.mk ⟨x, mem_sup_right hx⟩ := by
    intro z
    obtain ⟨⟨s, hs⟩, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨r, hr, x, hx, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hTN hs
    refine ⟨x, hx, ?_⟩
    rw [QuotientGroup.eq, mem_subgroupOf]
    change (r * x)⁻¹ * x ∈ 𝓡
    have h1 := (mem_normalizer_iff.1 (inv_mem (hTN hx)) r⁻¹).1 (inv_mem hr)
    rw [inv_inv] at h1
    rwa [show (r * x)⁻¹ * x = x⁻¹ * r⁻¹ * x by group]
  have hab : IsMulCommutative ((𝓡 ⊔ T : Subgroup G) ⧸ (𝓡 : Subgroup G).subgroupOf (𝓡 ⊔ T)) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx, rfl⟩ := hmk a
    obtain ⟨y, hy, rfl⟩ := hmk b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    change (x * y)⁻¹ * (y * x) ∈ 𝓡
    rw [show (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ by group]
    exact hPR (hS.commutator_mem_PG_of_mem_T (inv_mem hy) (inv_mem hx))
  have hFT := Common.firstTransferData_of_forall_conj_mem ⟨S, hS'⟩ hRS hab
    (mem_sup_right hS.t_mem_T) hS.t_not_mem_miyamotoRG hS.t_two hfus
  have := hS.isPerfect
  exact perfect_first_transfer_exclusion ⟨_, _, _, hFT⟩

theorem exists_act_eq_fieldAut (hS : Setting h L η t Q T) (x : centralizer ({t} : Set G)) :
    ∃ u : centralizer ({t} : Set G), hS.act u = miyamotoFieldAut h (hS.fieldFactor x) := by
  obtain ⟨s, hs⟩ := hS.exists_act_eq x
  have hm : ((η.symm s : L) : G) ∈ L := (η.symm s).2
  refine ⟨⟨(η.symm s : G), hS.L_le_centralizer hm⟩⁻¹ * x, ?_⟩
  rw [map_mul, map_inv, hS.act_of_mem hm, hs, Subtype.coe_eta, MulEquiv.apply_symm_apply,
    inv_mul_cancel_left]

theorem mem_normalizer_PG_of_act_eq_fieldAut (hS : Setting h L η t Q T)
    (u : centralizer ({t} : Set G)) {φ : K ≃+* K} (hu : hS.act u = miyamotoFieldAut h φ) :
    (u : G) ∈ normalizer (𝓟 : Set G) := by
  refine mem_normalizer_fintype fun p hp => ?_
  rw [SetLike.mem_coe] at hp ⊢
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hp
  rw [← hS.coe_symm_act_apply, hu]
  exact (symm_mem_miyamotoPull_iff h L η).2 (glAut_mem_P h φ hg)

theorem mul_self_eq_one_or_eq_t_of_act_eq_bar (hS : Setting h L η t Q T)
    (u : centralizer ({t} : Set G))
    (hu : hS.act u = miyamotoFieldAut h (miyamotoBarEquiv h)) :
    (u : G) * u = 1 ∨ (u : G) * u = t := by
  have hbb : miyamotoBarEquiv h * miyamotoBarEquiv h = 1 := RingEquiv.ext fun c => h.bar_bar c
  have h1 : hS.act (u * u) = 1 := by
    rw [map_mul, hu, ← miyamotoFieldHom_apply, ← map_mul, hbb, map_one]
  have h2 : (u : G) * u ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :=
    mem_inf.2 ⟨(hS.act_eq_one_iff _).1 h1, (u * u).2⟩
  rw [hS.kernel_eq_zpowers'] at h2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
  rw [← hk]
  exact hS.zpow_t_eq k

theorem mul_self_eq_one_of_mul_inv_mem_PG (hS : Setting h L η t Q T) {u x : G}
    (huN : u ∈ normalizer (𝓟 : Set G)) (hu2 : u * u = 1 ∨ u * u = t) (hxx : x * x ∈ 𝓟)
    (hxu : x * u⁻¹ ∈ 𝓟) : u * u = 1 := by
  refine hu2.resolve_right fun hut => hS.t_not_mem_L (miyamotoPull_le h L η
    (miyamotoUnipotent h false false) ?_)
  have h1 : u * (x * u⁻¹) * u⁻¹ ∈ 𝓟 := (mem_normalizer_iff.1 huN _).1 hxu
  rw [show t = ((x * u⁻¹) * (u * (x * u⁻¹) * u⁻¹))⁻¹ * (x * x) by rw [← hut, ← sq]; group]
  exact mul_mem (inv_mem (mul_mem hxu h1)) hxx

theorem exists_setting_mem_of_mem_normalizer_PG (hS : Setting h L η t Q T) {u : G}
    (huC : u ∈ centralizer ({t} : Set G)) (huN : u ∈ normalizer (𝓟 : Set G))
    (hu2 : u * u = 1 ∨ u * u = t) : ∃ T' : Subgroup G, Setting h L η t Q T' ∧ u ∈ T' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu4 : u ^ 2 ^ 2 = 1 := by
    rw [show u ^ 2 ^ 2 = (u * u) * (u * u) by norm_num [pow_succ, mul_assoc]]
    rcases hu2 with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, hS.t_mul_t]
  have hZ : IsPGroup 2 (zpowers u) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hu4)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hZN : zpowers u ≤ normalizer (Q : Set G) := by
    rw [zpowers_le, hS.Q_eq]
    exact mem_normalizer_sup huN
      (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1 huC))
  have hX : IsPGroup 2 (Q ⊔ zpowers u : Subgroup G) :=
    hS.isPGroup_Q.to_sup_of_normal_left' hZ hZN
  have hXC : Q ⊔ zpowers u ≤ centralizer ({t} : Set G) :=
    sup_le hS.Q_le_centralizer ((zpowers_le).2 huC)
  obtain ⟨T₀, hT₀⟩ := (hX.comap_subtype (K := centralizer ({t} : Set G))).exists_le_sylow
  refine ⟨(T₀ : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype,
    hS.of_sylow ⟨T₀, rfl⟩ fun q hq => ⟨⟨q, hXC (mem_sup_left hq)⟩,
      hT₀ (show q ∈ Q ⊔ zpowers u from mem_sup_left hq), rfl⟩,
    ⟨⟨u, huC⟩, hT₀ (show u ∈ Q ⊔ zpowers u from mem_sup_right (mem_zpowers u)), rfl⟩⟩

theorem exists_mul_inv_mem_PG_of_fieldFactor_ne_one (hS : Setting h L η t Q T) {u₀ : G}
    (hu₀ : u₀ ∈ T)
    (hact : hS.act ⟨u₀, hS.T_le hu₀⟩ = miyamotoFieldAut h (miyamotoBarEquiv h)) {x : G}
    (hx : x ∈ T) (hxx : x * x ∈ 𝓟) (hσ : hS.fieldFactor ⟨x, hS.T_le hx⟩ ≠ 1) :
    ∃ u, ∃ hu : u ∈ centralizer ({t} : Set G), u * u = 1 ∧
      hS.act ⟨u, hu⟩ = miyamotoFieldAut h (miyamotoBarEquiv h) ∧ x * u⁻¹ ∈ 𝓟 := by
  have hu₀C := hS.T_le hu₀
  have hxC := hS.T_le hx
  have h2 : hS.fieldFactor ⟨x, hxC⟩ * hS.fieldFactor ⟨x, hxC⟩ = 1 := by
    rw [← map_mul]
    exact hS.fieldFactor_of_mem_L (miyamotoPull_le h L η _ hxx)
  have hσx := (hS.fieldFactor_eq_one_or_bar _ h2).resolve_left hσ
  have hσu : hS.fieldFactor ⟨u₀, hu₀C⟩ = miyamotoBarEquiv h := by
    change miyamotoFieldFactor h (hS.act ⟨u₀, hu₀C⟩) = _
    rw [hact, miyamotoFieldFactor_fieldAut]
  have hσ1 : hS.fieldFactor (⟨x, hxC⟩ * (⟨u₀, hu₀C⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, hσx, hσu, mul_inv_cancel]
  obtain ⟨l, hl, c, hc, e⟩ := (hS.fieldFactor_eq_one_iff _).1 hσ1
  have e' : x * u₀⁻¹ = l * c := e
  have hlP := hS.mem_P_of_mul (mul_mem hx (inv_mem hu₀)) hl hc e'
  rw [hS.kernel_eq_zpowers'] at hc
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  rcases hS.zpow_t_eq k with h1 | h1
  ·
    rw [h1, mul_one] at e'
    have hxu : x * u₀⁻¹ ∈ 𝓟 := e' ▸ hlP
    exact ⟨u₀, hu₀C, hS.mul_self_eq_one_of_mul_inv_mem_PG
      (hS.mem_normalizer_PG_of_act_eq_fieldAut ⟨u₀, hu₀C⟩ hact)
      (hS.mul_self_eq_one_or_eq_t_of_act_eq_bar ⟨u₀, hu₀C⟩ hact) hxx hxu, hact, hxu⟩
  ·
    rw [h1] at e'
    have huC : t * u₀ ∈ centralizer ({t} : Set G) := mul_mem hS.t_mem_centralizer hu₀C
    have hxu : x * (t * u₀)⁻¹ ∈ 𝓟 := by
      rw [show x * (t * u₀)⁻¹ = x * u₀⁻¹ * t⁻¹ by group, e', mul_inv_cancel_right]
      exact hlP
    have hact' : hS.act ⟨t * u₀, huC⟩ = miyamotoFieldAut h (miyamotoBarEquiv h) := by
      have e2 : (⟨t * u₀, huC⟩ : centralizer ({t} : Set G)) =
          ⟨t, hS.t_mem_centralizer⟩ * ⟨u₀, hu₀C⟩ := rfl
      rw [e2, map_mul, (hS.act_eq_one_iff _).2 hS.t_mem, one_mul, hact]
    exact ⟨t * u₀, huC, hS.mul_self_eq_one_of_mul_inv_mem_PG
      (hS.mem_normalizer_PG_of_act_eq_fieldAut ⟨t * u₀, huC⟩ hact')
      (hS.mul_self_eq_one_or_eq_t_of_act_eq_bar ⟨t * u₀, huC⟩ hact') hxx hxu, hact', hxu⟩

theorem false_of_conj_not_mem_RG_of_outer (hS : Setting h L η t Q T)
    (hR : ∀ g : G, g⁻¹ * t * g ∉ 𝓡)
    (houter : ∀ (u : G) (hu : u ∈ centralizer ({t} : Set G)), u * u = 1 →
      miyamotoAct h L η ⟨u, hS.centralizer_le_normalizer hu⟩ =
        miyamotoFieldAut h (miyamotoBarEquiv h) →
      ∀ r ∈ 𝓡, ∀ g : G, g⁻¹ * t * g ≠ u * r) : False := by
  by_cases hbar : ∃ x : centralizer ({t} : Set G), hS.fieldFactor x = miyamotoBarEquiv h
  · obtain ⟨x, hx⟩ := hbar
    obtain ⟨u, hu⟩ := hS.exists_act_eq_fieldAut x
    rw [hx] at hu
    obtain ⟨T', hS', huT'⟩ := hS.exists_setting_mem_of_mem_normalizer_PG u.2
      (hS.mem_normalizer_PG_of_act_eq_fieldAut u hu) (hS.mul_self_eq_one_or_eq_t_of_act_eq_bar u hu)
    refine hS'.false_of_forall_conj_ne hR fun y hy hyy hσ r hr g hg => ?_
    obtain ⟨v, hvC, hvv, hvact, hvP⟩ :=
      hS'.exists_mul_inv_mem_PG_of_fieldFactor_ne_one huT' hu hy hyy hσ
    have hvN : v ∈ normalizer (𝓡 : Set G) := by
      rw [show v = (y * v⁻¹)⁻¹ * y by group]
      exact mul_mem (inv_mem (le_normalizer (hS'.PG_le_RG hvP))) (hS'.T_le_normalizer_RG hy)
    have hr' : v⁻¹ * (r * (y * v⁻¹)) * v ∈ 𝓡 := by
      have h1 := (mem_normalizer_iff.1 (inv_mem hvN) _).1 (mul_mem hr (hS'.PG_le_RG hvP))
      rwa [inv_inv] at h1
    apply houter v hvC hvv hvact _ hr' g
    rw [hg]
    group
  · push Not at hbar
    refine hS.false_of_forall_conj_ne hR fun x hx hxx hσ => ?_
    exfalso
    have h2 : hS.fieldFactor ⟨x, hS.T_le hx⟩ * hS.fieldFactor ⟨x, hS.T_le hx⟩ = 1 := by
      rw [← map_mul]
      exact hS.fieldFactor_of_mem_L (miyamotoPull_le h L η _ hxx)
    exact hbar _ ((hS.fieldFactor_eq_one_or_bar _ h2).resolve_left hσ)


theorem false_of_case_one_of_outer (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    [Fintype k₂] (hk₂ : Fintype.card k₂ = (2 ^ f) ^ 2)
    (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂))
    (houter : ∀ (u : G) (hu : u ∈ centralizer ({t} : Set G)), u * u = 1 →
      miyamotoAct h L η ⟨u, hS.centralizer_le_normalizer hu⟩ =
        miyamotoFieldAut h (miyamotoBarEquiv h) →
      ∀ r ∈ miyamotoRG h L η t Q, ∀ g : G, g⁻¹ * t * g ≠ u * r) : False :=
  hS.false_of_conj_not_mem_RG_of_outer (hS.conj_t_not_mem_RG_of_case_one hk₂ ψ₂) houter

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
