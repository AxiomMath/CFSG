module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsInv
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveClasses

public section

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open CFSG.GH74.GLS.Bg.Thompson

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

theorem exists_extremal_conj (hGs : IsSimpleGroup G) (hG2 : ¬ IsPGroup 2 G) {T U : Subgroup G}
    (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2)
    {x : G} (hxT : x ∈ T) (hxU : x ∉ U) (hx2 : x * x = 1) :
    ∃ g : G, g⁻¹ * x * g ∈ U ∧ IsExtremalIn 2 T (g⁻¹ * x * g) ∧
      ∀ c ∈ T ⊓ centralizer ({x} : Set G),
        g⁻¹ * c * g ∈ T ⊓ centralizer ({g⁻¹ * x * g} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUidx
  have hQn : ∀ t ∈ T, ∀ q ∈ U, t * q * t⁻¹ ∈ U := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hUT hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ U := by
    refine ⟨x, hxT, fun t ht => ?_⟩
    by_cases htU : t ∈ U
    · exact ⟨0, by simpa using htU⟩
    · exact ⟨1, by simpa using CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUidx hxT ht hxU htU⟩
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ T → g⁻¹ * x ^ (2 * k) * g ∈ U := by
    intro g k _
    rw [pow_mul, sq, hx2, one_pow, mul_one, inv_mul_cancel]
    exact one_mem U
  have hc : ∀ g : G, g⁻¹ * x * g ∈ T → IsExtremalIn 2 T (g⁻¹ * x * g) →
      g⁻¹ * x * g ∈ U ∨ x⁻¹ * (g⁻¹ * x * g) ∈ U := by
    intro g hgT _
    by_cases hgU : g⁻¹ * x * g ∈ U
    · exact Or.inl hgU
    · exact Or.inr (CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUidx hxT hgT hxU hgU)
  rcases thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc hxT hxU hb hc with
    ⟨N, hN, -, hNp, hxN⟩ | hg
  · exfalso
    have := hGs
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN1 | hN1
    · apply hG2
      intro a
      obtain ⟨n, hn⟩ := hNp (a : G ⧸ N)
      refine ⟨n, ?_⟩
      have h1 : a ^ 2 ^ n ∈ N := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        exact hn
      rw [hN1] at h1
      exact mem_bot.mp h1
    · exact hxN (by rw [hN1]; exact mem_top x)
  · exact hg

theorem le_centralizer_of_isExtremalIn {T : Subgroup G} (hT : IsPGroup 2 T) {y z : G}
    (hzT : ∀ t ∈ T, t * z = z * t) (hzy : IsConj z y) (hext : IsExtremalIn 2 T y) :
    T ≤ centralizer ({y} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hzy
  have hS : IsSylowOf 2 (T ⊓ centralizer ({y} : Set G)) (centralizer ({y} : Set G)) :=
    isSylowOf_iff.mpr hext
  have hle : rightConjugate T c⁻¹ ≤ centralizer ({y} : Set G) := by
    intro a ha
    rw [mem_rightConjugate_iff, inv_inv] at ha
    have ht := hzT _ ha
    rw [mem_centralizer_singleton_iff]
    calc a * y = c * ((c⁻¹ * a * c) * z) * c⁻¹ := by rw [← hc]; group
      _ = c * (z * (c⁻¹ * a * c)) * c⁻¹ := by rw [ht]
      _ = y * a := by rw [← hc]; group
  obtain ⟨Q, hQ, hTQ⟩ := exists_isSylowOf_le hle (hT.map (MulAut.conj c⁻¹⁻¹).toMonoidHom)
  have hcard : Nat.card T ≤ Nat.card (T ⊓ centralizer ({y} : Set G) : Subgroup G) := by
    rw [hS.card_eq, ← hQ.card_eq, ← rightConjugate_card T c⁻¹]
    exact card_le_of_le hTQ
  exact inf_eq_left.mp (eq_of_le_of_card_ge inf_le_left hcard)

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

variable {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

omit [Finite G] h hP hPC in
theorem outer_mem_sup_iff {s : G} : s ∈ P ⊔ zpowers x ↔ s ∈ P ∨ x * s ∈ P := by
  have hxN : zpowers x ≤ normalizer (P : Set G) := zpowers_le.mpr hx.normP
  constructor
  · intro hs
    have hs' : s ∈ ((P ⊔ zpowers x : Subgroup G) : Set G) := hs
    rw [coe_mul_of_right_le_normalizer_left P (zpowers x) hxN] at hs'
    obtain ⟨p, hp, k, hk, rfl⟩ := hs'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
    change p * x ^ n ∈ P ∨ x * (p * x ^ n) ∈ P
    have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx.sq
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
    · left
      rw [hm, zpow_mul, hx2, one_zpow, mul_one]
      exact hp
    · right
      rw [hm, zpow_add_one, zpow_mul, hx2, one_zpow, one_mul]
      have := (mem_normalizer_iff.mp hx.normP p).mp hp
      rw [outer_inv hx] at this
      rwa [← mul_assoc]
  · rintro (hs | hs)
    · exact mem_sup_left hs
    · have e : s = x * (x * s) := by rw [← mul_assoc, hx.sq, one_mul]
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers x)) (mem_sup_left hs)

omit [Finite G] h hP hPC in
theorem outer_relIndex_sup : P.relIndex (P ⊔ zpowers x) = 2 := by
  change (P.subgroupOf (P ⊔ zpowers x)).index = 2
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨⟨x, mem_sup_right (mem_zpowers x)⟩, hx.not_mem, fun b => ?_⟩
  rcases (outer_mem_sup_iff hx).mp b.2 with hb | hb
  · exact Or.inr hb
  · left
    change (b : G) * x ∈ P
    have := (mem_normalizer_iff.mp hx.normP _).mp hb
    rwa [outer_inv hx, ← mul_assoc, hx.sq, one_mul] at this

omit [Finite G] h hP hPC in
theorem outer_card_sup (hP64 : Nat.card P = 64) :
    Nat.card (P ⊔ zpowers x : Subgroup G) = 128 := by
  have h1 := Subgroup.relIndex_mul_card P (P ⊔ zpowers x)
  rw [outer_relIndex_sup hx, inf_eq_left.mpr le_sup_left, hP64] at h1
  omega

theorem outer_isSylowOf_sup (hP64 : Nat.card P = 64) :
    IsSylowOf 2 (P ⊔ zpowers x) (normalizer ((R ⊔ T : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁N : P ⊔ zpowers x ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) :=
    sup_le (fun n hn => (hP.le hn).1) (zpowers_le.mpr hx.normV)
  have hS₁2 : IsPGroup 2 (P ⊔ zpowers x : Subgroup G) :=
    IsPGroup.of_card (n := 7) (by rw [outer_card_sup hx hP64]; norm_num)
  obtain ⟨Q, hQ, hS₁Q⟩ := exists_isSylowOf_le hS₁N hS₁2
  have hQ128 := h.card_le_of_le_normalizer_V hP hPC hP64 hQ.isPGroup hQ.le
    (le_sup_left.trans hS₁Q)
  have hQS₁ : P ⊔ zpowers x = Q :=
    eq_of_le_of_card_ge hS₁Q (by rw [outer_card_sup hx hP64]; exact hQ128)
  rw [hQS₁]
  exact hQ

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
  {V' : Subgroup G} (hV' : IsVprime (R ⊔ T) V₀ P V')
include hIIa hV'

theorem outer_eq_or_eq_of_elemAbelian {E : Subgroup G} (hE : E ≤ P ⊔ zpowers x)
    (hEe : IsElemAbelian 2 E) (hE16 : Nat.card E = 16) : E = R ⊔ T ∨ E = V' := by
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  by_cases hEP : E ≤ P
  · exact h.eq_or_eq_of_elemAbelian hP hPC hV'.inv hV₀V' hV'.card hEP hEe hE16
  exfalso
  obtain ⟨u, huE, huP⟩ := IsConcreteLE.not_le_iff_exists.mp hEP
  have hxu : x * u ∈ P := ((outer_mem_sup_iff hx).mp (hE huE)).resolve_left huP
  have hle : P.relIndex E ≤ 2 := by
    have h1 := Subgroup.relIndex_le_of_le_right (H := P) hE (by
      rw [outer_relIndex_sup hx]
      norm_num)
    exact h1.trans (le_of_eq (outer_relIndex_sup hx))
  have h8 : 8 ≤ Nat.card (P ⊓ E : Subgroup G) := by
    have h1 := Subgroup.relIndex_mul_card P E
    rw [hE16] at h1
    have h2 : 16 ≤ 2 * Nat.card (P ⊓ E : Subgroup G) := h1 ▸ Nat.mul_le_mul_right _ hle
    omega
  have hXC : P ⊓ E ≤ centralizer ({u} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hEe.1.is_comm.comm ⟨e, (mem_inf.mp he).2⟩ ⟨u, huE⟩))
  rcases h.le_or_le_of_elemAbelian hP hPC hV'.inv hV₀V' inf_le_left
    (isElemAbelian_of_le hEe inf_le_right) with h1 | h1
  · have := h.outer_card_le_four_V hP hPC hx hxu h1 hXC
    omega
  · have := h.outer_card_le_four_V' hP hPC hx hIIa hV' hxu h1 hXC
    omega

omit hIIa in
theorem outer_eq_or_eq_of_elemAbelian_of_isVprime {E : Subgroup G} (hE : E ≤ P ⊔ zpowers x)
    (hEe : IsElemAbelian 2 E) (hE16 : Nat.card E = 16) : E = R ⊔ T ∨ E = V' := by
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  by_cases hEP : E ≤ P
  · exact h.eq_or_eq_of_elemAbelian hP hPC hV'.inv hV₀V' hV'.card hEP hEe hE16
  exfalso
  obtain ⟨u, huE, huP⟩ := IsConcreteLE.not_le_iff_exists.mp hEP
  have hxu : x * u ∈ P := ((outer_mem_sup_iff hx).mp (hE huE)).resolve_left huP
  have hle : P.relIndex E ≤ 2 := by
    have h1 := Subgroup.relIndex_le_of_le_right (H := P) hE (by
      rw [outer_relIndex_sup hx]
      norm_num)
    exact h1.trans (le_of_eq (outer_relIndex_sup hx))
  have h8 : 8 ≤ Nat.card (P ⊓ E : Subgroup G) := by
    have h1 := Subgroup.relIndex_mul_card P E
    rw [hE16] at h1
    have h2 : 16 ≤ 2 * Nat.card (P ⊓ E : Subgroup G) := h1 ▸ Nat.mul_le_mul_right _ hle
    omega
  have hXC : P ⊓ E ≤ centralizer ({u} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hEe.1.is_comm.comm ⟨e, (mem_inf.mp he).2⟩ ⟨u, huE⟩))
  rcases h.le_or_le_of_elemAbelian hP hPC hV'.inv hV₀V' inf_le_left
    (isElemAbelian_of_le hEe inf_le_right) with h1 | h1
  · have := h.outer_card_le_four_V hP hPC hx hxu h1 hXC
    omega
  · have := h.outer_card_le_four_V'_of_isVprime hP hPC hx hV' hxu h1 hXC
    omega

omit hIIa in
theorem outer_eq_of_comm {y : G} (hyP : y ∈ P) (hyV : ∀ v ∈ R ⊔ T, y * v = v * y)
    (hyV' : ∀ v ∈ V', y * v = v * y) (hyx : y * x = x * y) : y = 1 ∨ y = z := by
  have hyV₀ : y ∈ R ⊔ T :=
    hPC ▸ mem_inf.mpr ⟨hyP, mem_centralizer_iff.mpr fun v hv => (hyV v hv).symm⟩
  obtain ⟨v, hvV', hvV⟩ : ∃ v ∈ V', v ∉ R ⊔ T := by
    by_contra hcon
    push Not at hcon
    have hle : V' ≤ V₀ := fun v hv => hV'.inf ▸ mem_inf.mpr ⟨hcon v hv, hv⟩
    have := card_le_of_le hle
    rw [hV'.card, h.card_V₀] at this
    omega
  have hy0 : y ∈ V₀ := h.P_fixed hP hPC (hV'.le hvV') hvV hyV₀ (by rw [← hyV' v hvV']; group)
  exact hx.fix_V₀ y hy0 hyx.symm

omit hIIa in
theorem outer_sup_ne_sylow (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (S : Sylow 2 G) : (S : Subgroup G) ≠ P ⊔ zpowers x := by
  intro hSS
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  have hzV₀ := hx.z_mem
  have hz1 := hx.z_ne
  by_cases hxz : IsConj z x
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hS₁2 : IsPGroup 2 (P ⊔ zpowers x : Subgroup G) := by
      rw [← hSS]
      exact S.isPGroup'
    have hS₁idx : ¬ 2 ∣ (P ⊔ zpowers x).index := by
      rw [← hSS]
      exact S.not_dvd_index
    obtain ⟨k, hkP, hkext, hkC⟩ := exists_extremal_conj hGs h.not_isPGroup_two hS₁2 hS₁idx
      le_sup_left (outer_relIndex_sup hx) (mem_sup_right (mem_zpowers x)) hx.not_mem hx.sq
    have hzS₁ : ∀ t ∈ P ⊔ zpowers x, t * z = z * t := by
      intro t ht
      rcases (outer_mem_sup_iff hx).mp ht with h1 | h1
      · exact P_comm_V₀ hP hzV₀ h1
      · obtain ⟨p, hp, rfl⟩ : ∃ p ∈ P, t = x * p :=
          ⟨x * t, h1, by rw [← mul_assoc, hx.sq, one_mul]⟩
        calc x * p * z = x * (p * z) := mul_assoc _ _ _
          _ = x * (z * p) := by rw [P_comm_V₀ hP hzV₀ hp]
          _ = x * z * p := (mul_assoc _ _ _).symm
          _ = z * x * p := by rw [hx.z_comm]
          _ = z * (x * p) := mul_assoc _ _ _
    have hxy : IsConj x (k⁻¹ * x * k) := isConj_iff.mpr ⟨k⁻¹, by group⟩
    have hS₁y : P ⊔ zpowers x ≤ centralizer ({k⁻¹ * x * k} : Set G) :=
      le_centralizer_of_isExtremalIn hS₁2 hzS₁ (hxz.trans hxy) hkext
    have hcomm : ∀ v ∈ P ⊔ zpowers x, k⁻¹ * x * k * v = v * (k⁻¹ * x * k) := fun v hv =>
      (mem_centralizer_singleton_iff.mp (hS₁y hv)).symm
    have hyz : k⁻¹ * x * k = z := by
      rcases h.outer_eq_of_comm hP hPC hx hV' hkP
        (fun v hv => hcomm v (mem_sup_left (hVP hv)))
        (fun v hv => hcomm v (mem_sup_left (hV'.le hv)))
        (hcomm x (mem_sup_right (mem_zpowers x))) with h1 | h1
      · exfalso
        apply hx.not_mem
        have hx1 : x = 1 := by
          calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
            _ = 1 := by rw [h1]; group
        rw [hx1]
        exact one_mem P
      · exact h1
    have hr₁C : r₁ ∈ (P ⊔ zpowers x) ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨mem_sup_left (hVP (mem_sup_left hx.r_mem)),
        mem_centralizer_singleton_iff.mpr hx.r_comm.symm⟩
    obtain ⟨hdS, hdC⟩ := mem_inf.mp (hkC r₁ hr₁C)
    rw [hyz] at hdC
    have hdz : k⁻¹ * r₁ * k * z = z * (k⁻¹ * r₁ * k) := mem_centralizer_singleton_iff.mp hdC
    have hd2 : k⁻¹ * r₁ * k * (k⁻¹ * r₁ * k) = 1 := by
      calc k⁻¹ * r₁ * k * (k⁻¹ * r₁ * k) = k⁻¹ * (r₁ * r₁) * k := by group
        _ = 1 := by rw [h.mul_self (mem_sup_left hx.r_mem)]; group
    have hd1 : k⁻¹ * r₁ * k ≠ 1 := by
      intro h1
      apply hx.r_ne
      calc r₁ = k * (k⁻¹ * r₁ * k) * k⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hdroot : IsRootInv A (k⁻¹ * r₁ * k) := (h.isRootInv_of_mem_R hx.r_mem).conj k
    have hzd : ¬ IsRootInv A (z * (k⁻¹ * r₁ * k)) := by
      apply h.not_isRootInv_of_isConj hzV₀ hz1
      obtain ⟨r, -, hr⟩ := h.outer_exists_conj_mul_r hx
      have e : z * (k⁻¹ * r₁ * k) = k⁻¹ * (x * r₁) * k := by rw [← hyz]; group
      rw [e]
      refine hxz.trans (isConj_iff.mpr ⟨k⁻¹ * r⁻¹, ?_⟩)
      rw [← hr]
      group
    apply hzd
    have hdV₀ : k⁻¹ * r₁ * k ∉ V₀ := fun h0 =>
      h.not_isRootInv_of_isConj h0 hd1 (IsConj.refl _) hdroot
    rcases (outer_mem_sup_iff hx).mp hdS with hdP | hdP
    · by_cases hdV : k⁻¹ * r₁ * k ∈ R ⊔ T
      · refine h.isRootInv_of_mem_V (mul_mem (h.V₀_le hzV₀) hdV) fun h0 => hdV₀ ?_
        have := mul_mem (inv_mem hzV₀) h0
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
      · have hzdP : z * (k⁻¹ * r₁ * k) ∈ P := mul_mem (hVP (h.V₀_le hzV₀)) hdP
        have hzdV : z * (k⁻¹ * r₁ * k) ∉ R ⊔ T := fun h0 => hdV (by
          have := mul_mem (inv_mem (h.V₀_le hzV₀)) h0
          rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
        have hzd2 : z * (k⁻¹ * r₁ * k) * (z * (k⁻¹ * r₁ * k)) = 1 := by
          calc z * (k⁻¹ * r₁ * k) * (z * (k⁻¹ * r₁ * k)) =
              z * (k⁻¹ * r₁ * k * z) * (k⁻¹ * r₁ * k) := by group
            _ = z * (z * (k⁻¹ * r₁ * k)) * (k⁻¹ * r₁ * k) := by rw [hdz]
            _ = z * z * ((k⁻¹ * r₁ * k) * (k⁻¹ * r₁ * k)) := by group
            _ = 1 := by rw [h.mul_self (h.V₀_le hzV₀), hd2, one_mul]
        obtain ⟨c, hc⟩ := h.P_invol_conj hP hPC hdP hdV hd2 hzdP hzdV hzd2
        exact hdroot.of_isConj (isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hc⟩)
    · obtain ⟨w, -, hw⟩ := h.outer_exists_conj_mul_z hP hx hdP hd2
      rw [← hdz]
      exact hdroot.of_isConj (isConj_iff.mpr ⟨w⁻¹, by rw [inv_inv]; exact hw⟩)
  ·
    have hconjP : ∀ a ∈ V₀, a ≠ 1 → ∀ y : G, y⁻¹ * a * y ∈ P ⊔ zpowers x →
        y⁻¹ * a * y ∈ P := by
      intro a ha ha1 y hy
      rcases (outer_mem_sup_iff hx).mp hy with h1 | h1
      · exact h1
      · exfalso
        have ha2 : y⁻¹ * a * y * (y⁻¹ * a * y) = 1 := by
          calc y⁻¹ * a * y * (y⁻¹ * a * y) = y⁻¹ * (a * a) * y := by group
            _ = 1 := by rw [h.mul_self (h.V₀_le ha)]; group
        obtain ⟨q, -, hq⟩ := h.outer_exists_conj_eq hP hPC hx hP64 h1 ha2
        apply hxz
        refine (h.isConj_of_mem_V₀ hzV₀ hz1 ha ha1).trans (isConj_iff.mpr ⟨q * y⁻¹, ?_⟩)
        calc q * y⁻¹ * a * (q * y⁻¹)⁻¹ = q * (y⁻¹ * a * y) * q⁻¹ := by group
          _ = q * (q⁻¹ * x * q) * q⁻¹ := by rw [hq]
          _ = x := by group
    have hV₀1 : V₀ ≠ ⊥ := fun he => by
      have := h.card_V₀
      rw [he, card_bot] at this
      omega
    have hinvol : ∀ v ∈ R ⊔ T, v ^ 2 = 1 := fun v hv => by rw [sq]; exact h.mul_self hv
    have hVS : R ⊔ T ≤ (S : Subgroup G) := by
      rw [hSS]
      exact hVP.trans le_sup_left
    by_cases hcase : ∃ c ∈ P, c ∉ R ⊔ T ∧ c * c = 1 ∧
        ∃ w ∈ V₀, w ≠ 1 ∧ ∃ y : G, y⁻¹ * w * y = c
    ·
      obtain ⟨c, hcP, hcV, hc2, w, hw, hw1, y₀, hy₀⟩ := hcase
      have hcl : ∀ a ∈ V', ∀ y : G, y⁻¹ * a * y ∈ (S : Subgroup G) → y⁻¹ * a * y ∈ V' := by
        intro a ha y hy
        by_cases ha1 : a = 1
        · rw [ha1]
          simp
        have ha2 : a * a = 1 := by rw [← sq]; exact hV'.elem.2 a ha
        obtain ⟨w', hw', hw'1, y', hy'⟩ : ∃ w' ∈ V₀, w' ≠ 1 ∧ ∃ y' : G, y'⁻¹ * w' * y' = a := by
          by_cases haV : a ∈ R ⊔ T
          · exact ⟨a, hV'.inf ▸ mem_inf.mpr ⟨haV, ha⟩, ha1, 1, by group⟩
          · obtain ⟨u, hu⟩ := h.P_invol_conj hP hPC hcP hcV hc2 (hV'.le ha) haV ha2
            exact ⟨w, hw, hw1, y₀ * u, by rw [← hu, ← hy₀]; group⟩
        have hb : y⁻¹ * a * y = (y' * y)⁻¹ * w' * (y' * y) := by rw [← hy']; group
        rw [hSS] at hy
        rw [hb] at hy ⊢
        have hbP := hconjP w' hw' hw'1 (y' * y) hy
        by_cases hbV : (y' * y)⁻¹ * w' * (y' * y) ∈ R ⊔ T
        · by_cases hb0 : (y' * y)⁻¹ * w' * (y' * y) ∈ V₀
          · exact hV₀V' hb0
          · exact absurd rfl (h.conj_V₀_ne hw' hw'1 hbV hb0 (y' * y))
        · refine hV'.inv _ hbP ?_ hbV
          calc (y' * y)⁻¹ * w' * (y' * y) * ((y' * y)⁻¹ * w' * (y' * y)) =
              (y' * y)⁻¹ * (w' * w') * (y' * y) := by group
            _ = 1 := by rw [h.mul_self (h.V₀_le hw')]; group
      have hall : ∀ v ∈ R ⊔ T, v ∈ V' := fun v hv =>
        mem_of_goldschmidt hGold hGs h.oddCore h.not_isPGroup_two S
          (by rw [hSS]; exact hV'.le.trans le_sup_left) hV'.elem.1 hcl
          (fun he => hV₀1 (le_bot_iff.mp (he ▸ hV₀V'))) (hVS hv) (hinvol v hv)
      have hVV₀ : R ⊔ T ≤ V₀ := fun v hv => hV'.inf ▸ mem_inf.mpr ⟨hv, hall v hv⟩
      have := Subgroup.card_le_of_le hVV₀
      rw [h.loc.card, h.card_V₀] at this
      omega
    ·
      push Not at hcase
      have hcl : ∀ a ∈ V₀, ∀ y : G, y⁻¹ * a * y ∈ (S : Subgroup G) → y⁻¹ * a * y ∈ V₀ := by
        intro a ha y hy
        by_cases ha1 : a = 1
        · rw [ha1]
          simp
        rw [hSS] at hy
        have hyP := hconjP a ha ha1 y hy
        by_cases hbV : y⁻¹ * a * y ∈ R ⊔ T
        · by_contra hb0
          exact h.conj_V₀_ne ha ha1 hbV hb0 y rfl
        · exfalso
          refine hcase _ hyP hbV ?_ a ha ha1 y rfl
          calc y⁻¹ * a * y * (y⁻¹ * a * y) = y⁻¹ * (a * a) * y := by group
            _ = 1 := by rw [h.mul_self (h.V₀_le ha)]; group
      have hab : IsMulCommutative V₀ :=
        ⟨⟨fun a b => Subtype.ext (h.comm (h.V₀_le a.2) (h.V₀_le b.2))⟩⟩
      have hall : ∀ v ∈ R ⊔ T, v ∈ V₀ := fun v hv =>
        mem_of_goldschmidt hGold hGs h.oddCore h.not_isPGroup_two S
          (h.V₀_le.trans hVS) hab hcl hV₀1 (hVS hv) (hinvol v hv)
      have := Subgroup.card_le_of_le (show R ⊔ T ≤ V₀ from hall)
      rw [h.loc.card, h.card_V₀] at this
      omega

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
