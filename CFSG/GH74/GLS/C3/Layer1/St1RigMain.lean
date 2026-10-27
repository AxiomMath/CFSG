module

public import CFSG.GH74.GLS.C3.Layer1.St1RigDiag3
public import CFSG.GH74.GLS.C3.Layer1.St1RigTwoGrp
public import CFSG.GH74.GLS.C3.Layer1.St1RigStep4
public import CFSG.GH74.GLS.C3.Layer1.St1P41L42
public import CFSG.GH74.GLS.TwoThin.Rank
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSwapRank
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpRigid

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.C3.Layer1.PumpCalc
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G]

structure Setup (x y : G) (K Q : Subgroup G) (t : G) (K' Λ : Subgroup G)
    (hxY : x ∈ centralizer ({t} : Set G)) : Prop where
  hR : ∀ z : G, orderOf z = 2 → 3 ≤ pRank 2 ↥(centralizer ({z} : Set G))
  hILo : IsILo 2 x K
  hyo : orderOf y = 2
  hQ : IsSylowOf 2 Q (CxK x K)
  hxQ : x ∈ Q
  htQ : t ∈ Q
  hlt : PumpUpLT 2 x K t K'
  h : DiagData x t K K' Λ hxY
  hyQ : y ∈ normalizer (Q : Set G)
  hty : t * y = y * t
  hyR0 : y ∈ normalizer ((Q ⊓ CxK t K' : Subgroup G) : Set G)
  hhat : ∀ (w : G) (M : Subgroup G), PumpUpLT 2 x K w M → w * y = y * w →
    hatCard M ≤ hatCard K
  hlex : pRank 2 ↥(CxK t K') < pRank 2 ↥(CxK x K) ∨
    (pRank 2 ↥(CxK t K') = pRank 2 ↥(CxK x K) ∧ sylVal t K' ≤ sylVal x K)
  hmaxAt : ∀ w ∈ Q, orderOf w = 2 → w * y = y * w →
    (∃ M : Subgroup G, PumpUpLT 2 x K w M ∧ x ∉ normalizer (M : Set G)) →
    Nat.card ↥(Q ⊓ centralizer ({w} : Set G)) ≤ Nat.card ↥(Q ⊓ centralizer ({t} : Set G))

namespace Setup

variable {x y t : G} {K Q K' Λ : Subgroup G} {hxY : x ∈ centralizer ({t} : Set G)}

omit [Finite G] in
theorem Q_le_C (S : Setup x y K Q t K' Λ hxY) : Q ≤ CxK x K := S.hQ.le

omit [Finite G] in
theorem hQp (S : Setup x y K Q t K' Λ hxY) : IsPGroup 2 Q := S.hQ.isPGroup

omit [Finite G] in
theorem x_central (S : Setup x y K Q t K' Λ hxY) : ∀ q ∈ Q, q * x = x * q := fun _ hq =>
  mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (S.Q_le_C hq)).1

omit [Finite G] in
theorem htC (S : Setup x y K Q t K' Λ hxY) : t ∈ CxK x K := mem_CxK_of_pumpUpLT S.hlt

omit [Finite G] in
theorem hxR₀ (S : Setup x y K Q t K' Λ hxY) : x ∉ Q ⊓ CxK t K' := fun hx => S.h.x_not_mem_CxK hx.2

theorem hcov (S : Setup x y K Q t K' Λ hxY) : ∀ r ∈ Q ⊓ centralizer ({t} : Set G),
    r ∈ Q ⊓ CxK t K' ∨ x * r ∈ Q ⊓ CxK t K' := by
  intro r hr
  rcases S.h.step1 hr.2 (S.Q_le_C hr.1) with h1 | h1
  · exact Or.inl ⟨hr.1, h1⟩
  · exact Or.inr ⟨mul_mem S.hxQ hr.1, h1⟩

theorem hyR (S : Setup x y K Q t K' Λ hxY) :
    y ∈ normalizer ((Q ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  have hyCt : y ∈ normalizer ((centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : (centralizer ({t} : Set G)).map (MulAut.conj y).toMonoidHom =
        centralizer ({t} : Set G) := by
      rw [CFSG.GH74.GLS.Stage1.Thm2.Recip.map_centralizer_singleton_conj t y]
      have hyt : y * t * y⁻¹ = t := by
        calc y * t * y⁻¹ = t * y * y⁻¹ := by rw [S.hty.symm]
          _ = t := by group
      rw [hyt]
    change (centralizer ({t} : Set G)).map (MulAut.conj y).toMonoidHom =
      centralizer ({t} : Set G)
    exact hmap
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨S.hyQ, hyCt⟩

theorem hmax_C (S : Setup x y K Q t K' Λ hxY) : ∀ w ∈ Q ⊓ CxK t K', orderOf w = 2 →
    (∀ r ∈ Q ⊓ centralizer ({t} : Set G), w * r = r * w) →
    w * y = y * w →
    ∀ g ∈ Q, g * w = w * g → g ∈ Q ⊓ centralizer ({t} : Set G) := by
  intro w hw hwo hwc hwy g hgQ hgw
  have hbound : ∀ M : Subgroup G, PumpUpLT 2 x K w M → hatCard M ≤ hatCard K :=
    fun M hM => S.hhat w M hM hwy
  obtain ⟨M, hM, hdiag⟩ := S.h.exists_diag_of_mem S.hILo hbound S.htC hwo
    (S.Q_le_C hw.1) hw.2 (S.hR w hwo)
  have hcard := S.hmaxAt w hw.1 hwo hwy ⟨M, hM, hdiag⟩
  have hle : Q ⊓ centralizer ({t} : Set G) ≤ Q ⊓ centralizer ({w} : Set G) := by
    intro r hr
    exact ⟨hr.1, mem_centralizer_singleton_iff.mpr (hwc r hr).symm⟩
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact ⟨hgQ, mem_centralizer_singleton_iff.mpr hgw⟩

theorem L₁_rank_card (S : Setup x y K Q t K' Λ hxY) :
    1 ≤ pRank 2 ↥(bar t K') ∧ 2 ≤ (Nat.card ↥(bar t K')).factorization 2 := by
  have h4 : 4 ∣ Nat.card ↥(bar t K') := four_dvd_card_of_isQuasisimple S.h.isComponent_L₁.1
  refine ⟨?_, ?_⟩
  · rw [pRank_two_subgroup_eq_open]
    exact one_le_pRank_of_two_dvd (dvd_trans (by norm_num) h4)
  · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
      (by simpa using h4)

theorem R_ne_Q (S : Setup x y K Q t K' Λ hxY) : Q ⊓ centralizer ({t} : Set G) ≠ Q := by
  intro hRQ
  set R₀ : Subgroup G := Q ⊓ CxK t K' with hR₀
  have hR₀R : R₀ ≤ Q ⊓ centralizer ({t} : Set G) := fun r hr =>
    ⟨hr.1, (Subgroup.mem_inf.mp hr.2).1⟩
  have hR₀p : IsPGroup 2 R₀ := S.hQp.to_le inf_le_left
  obtain ⟨hrk, hfac⟩ := S.h.gilman_bounds hR₀p (fun r hr => hr.2) (fun r hr => S.x_central r hr.1)
  obtain ⟨hL1rk, hL1card⟩ := S.L₁_rank_card
  have hidx : R₀.relIndex Q = 2 := by
    have := relIndex_eq_two_of_cov (R := Q ⊓ centralizer ({t} : Set G)) (R₀ := R₀) (x := x)
      ⟨S.hxQ, hxY⟩ (fun r hr => S.x_central r hr.1) S.hxR₀ S.hcov
    rw [hRQ] at this
    exact this
  have hR₀card : Nat.card ↥Q = 2 * Nat.card ↥R₀ := by
    have h := Subgroup.relIndex_mul_card R₀ Q
    rw [inf_eq_left.mpr (inf_le_left : R₀ ≤ Q), hidx] at h
    exact h.symm
  have hQrk : pRank 2 ↥Q ≤ pRank 2 ↥R₀ + 1 :=
    ComponentClassification.UnbalancedCorr.pRank_le_add_one_of_relIndex_eq_two hidx
  have hrkC : pRank 2 ↥Q = pRank 2 ↥(CxK x K) := pRank_of_isSylowOf S.hQ
  have hsyl : Nat.card ↥Q = 2 ^ sylVal x K := S.hQ.card_eq
  have hsyl' : sylVal x K = 1 + (Nat.card ↥R₀).factorization 2 := by
    have h := congrArg (fun n : ℕ => n.factorization 2) (hsyl.symm.trans hR₀card)
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h
    rw [Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two] at h
    simpa using h
  rcases S.hlex with hlt' | ⟨-, hle'⟩
  · omega
  · have : sylVal t K' = (Nat.card ↥(CxK t K')).factorization 2 := rfl
    omega

theorem card_R (S : Setup x y K Q t K' Λ hxY) :
    Nat.card ↥(Q ⊓ centralizer ({t} : Set G)) = 4 ∧ ∀ r ∈ Q ⊓ CxK t K', r = 1 ∨ r = t := by
  have htR₀ : t ∈ Q ⊓ CxK t K' := ⟨S.htQ, x_mem_CxK S.h.hK'c.1⟩
  exact card_R_eq_four_of_actorInvolution S.hQp inf_le_left S.R_ne_Q
    (fun r hr => ⟨hr.1, (Subgroup.mem_inf.mp hr.2).1⟩) ⟨S.hxQ, hxY⟩ S.hILo.1
    S.x_central S.hxR₀ S.hcov htR₀ S.h.hto S.hyo S.hyQ S.hyR S.hyR0 S.hmax_C

theorem pRank_Q_le (S : Setup x y K Q t K' Λ hxY) : pRank 2 ↥Q ≤ 2 :=
  pRank_le_two_of_centralizer_card_four S.hQp S.htQ S.h.hto S.card_R.1

theorem t_not_central (S : Setup x y K Q t K' Λ hxY) : ¬ ∀ q ∈ Q, q * t = t * q := by
  intro hc
  apply S.R_ne_Q
  refine le_antisymm inf_le_left (fun q hq => ⟨hq, mem_centralizer_singleton_iff.mpr (hc q hq)⟩)

theorem center_inv_eq_x (S : Setup x y K Q t K' Λ hxY) {z : G} (hzQ : z ∈ Q) (hzo : orderOf z = 2)
    (hzc : ∀ q ∈ Q, q * z = z * q) : z = x := by
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [S.h.hxo, sq] at this
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hzo
    omega
  have hzR : z ∈ Q ⊓ centralizer ({t} : Set G) :=
    ⟨hzQ, mem_centralizer_singleton_iff.mpr (hzc t S.htQ).symm⟩
  rcases S.hcov z hzR with h1 | h1
  · rcases S.card_R.2 z h1 with h | h
    · exact absurd h hz1
    · exfalso
      exact S.t_not_central (fun q hq => by rw [← h]; exact hzc q hq)
  · rcases S.card_R.2 (x * z) h1 with h | h
    · have : z = x⁻¹ := by
        have h2 : x * z = 1 := h
        exact eq_inv_of_mul_eq_one_right h2
      rw [this, inv_eq_of_mul_eq_one_left hxx]
    · exfalso
      refine S.t_not_central (fun q hq => ?_)
      rw [← h]
      calc q * (x * z) = (q * x) * z := by group
        _ = (x * q) * z := by rw [S.x_central q hq]
        _ = x * (q * z) := by group
        _ = x * (z * q) := by rw [hzc q hq]
        _ = x * z * q := by group

theorem x_not_mem_K (S : Setup x y K Q t K' Λ hxY) : x ∉ K := by
  intro hxK
  have hx2 : x ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one x
    rwa [S.h.hxo, ← pow_one 2] at this
  have hxΛ : x ∈ Λ := S.h.lam.twoElt x (Subgroup.mem_inf.mpr ⟨hxK, hxY⟩) ⟨1, hx2⟩
  have hs : sbar x hxY ∈ bar t Λ := ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hxΛ, rfl⟩
  have hs' : sbar x hxY ∈ bar t K' ⊔ conjSub (sbar x hxY)⁻¹ (bar t K') := S.h.hDle hs
  exact S.h.ne (conjSub_eq_of_mem_sup S.h.hAB (inv_mem hs'))

theorem exists_N (S : Setup x y K Q t K' Λ hxY) (hZ : center ↥(bar t K') ≠ ⊥) :
    ∃ N : Subgroup G, N ≤ K ∧ N ≤ CxK x K ∧ CxK x K ≤ normalizer (N : Set G) ∧
      2 ∣ Nat.card ↥N := by
  obtain ⟨e1⟩ := kBar_equiv_bar S.h.hK'c
  obtain ⟨e2⟩ := hat_equiv_of_pumpUpLT S.hlt (S.hhat t K' S.hlt S.hty)
  let e : kBar K ≃* ↥(bar t K') := e2.symm.trans e1
  set T : Subgroup (barQ ↥K) := center (kBar K) with hT
  have hTne : T ≠ ⊥ := by
    intro hT0
    apply hZ
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ center (kBar K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have := hz (e g)
      apply e.injective
      simpa using this
    rw [← hT, hT0, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e.symm.injective (by simpa using hz')
  set P : Subgroup ↥K := T.comap (barMk ↥K) with hP
  set N : Subgroup G := P.map K.subtype with hN
  have hNK : N ≤ K := Subgroup.map_subtype_le P
  have hKx : K ≤ centralizer ({x} : Set G) := S.h.hKc.1
  have hNmem : ∀ n ∈ N, ∃ k : ↥K, (k : G) = n ∧ barMk ↥K k ∈ T := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, rfl, hk⟩
  refine ⟨N, hNK, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl, hkT⟩ := hNmem n hn
    refine Subgroup.mem_inf.mpr ⟨hKx k.2, Subgroup.le_normalizer k.2,
      mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer k.2), fun m hm => ?_⟩
    have hc : barMk ↥K ⁅(⟨m, hm⟩ : ↥K), k⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp hkT _
    refine ⟨⁅(⟨m, hm⟩ : ↥K), k⁆, (QuotientGroup.eq_one_iff _).mp hc, ?_⟩
    simp [commutatorElement_def]
  · intro g hg
    refine mem_normalizer_of_forall fun y hy => ?_
    obtain ⟨k, rfl, hkT⟩ := hNmem y hy
    have hgK : g ∈ normalizer (K : Set G) := (Subgroup.mem_inf.mp hg).2.1
    have hgcomm := (Subgroup.mem_inf.mp hg).2.2.2
    have hk2K : g * (k : G) * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgK k).mp k.2
    have hdiff : g * (k : G) * g⁻¹ * (k : G)⁻¹ ∈ pPrimeCoreOf 2 K := by
      have := Subgroup.inv_mem _ (hgcomm k k.2)
      have e : g * (k : G) * g⁻¹ * (k : G)⁻¹ = ⁅(k : G), g⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact this
    obtain ⟨o', ho', ho'eq⟩ := hdiff
    have hk₂ : (⟨g * (k : G) * g⁻¹, hk2K⟩ : ↥K) = o' * k := by
      apply Subtype.ext
      have : (o' : G) = g * (k : G) * g⁻¹ * (k : G)⁻¹ := ho'eq
      show g * (k : G) * g⁻¹ = (o' : G) * (k : G)
      rw [this]
      group
    refine ⟨⟨g * (k : G) * g⁻¹, hk2K⟩, ?_, rfl⟩
    show barMk ↥K ⟨g * (k : G) * g⁻¹, hk2K⟩ ∈ T
    have h1 : barMk ↥K o' = 1 := (QuotientGroup.eq_one_iff _).mpr ho'
    rw [hk₂, map_mul, h1, one_mul]
    exact hkT
  · have hcard : Nat.card ↥N = Nat.card ↥T * Nat.card ↥(barMk ↥K).ker := by
      rw [hN, Subgroup.card_map_of_injective K.subtype_injective, hP]
      exact card_comap_barMk T
    have hp : IsPGroup 2 ↥T := isPGroup_two_center_hat ↥K
    have h2 : 2 ∣ Nat.card ↥T := by
      have := Nat.fact_prime_two
      rcases hp.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hTne
      · exact h
    rw [hcard]
    exact h2.mul_right _

theorem center_L₁_eq_bot (S : Setup x y K Q t K' Λ hxY) : center ↥(bar t K') = ⊥ := by
  by_contra hZ
  obtain ⟨N, hNK, hNC, hCN, hdvd⟩ := S.exists_N hZ
  have hQC : Q ≤ CxK x K := S.Q_le_C
  have hS : IsSylowOf 2 (Q ⊓ N) N := S.hQ.inf_of_le_normalizer hNC hCN
  have hcard : Nat.card ↥(Q ⊓ N) = 2 ^ (Nat.card ↥N).factorization 2 := hS.card_eq
  have hpos : 1 ≤ (Nat.card ↥N).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp (by simpa using hdvd)
  have hne : Q ⊓ N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 2 ≤ 2 ^ (Nat.card ↥N).factorization 2 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hpos
    omega
  have hQnil : Group.IsNilpotent ↥Q := S.hQp.isNilpotent
  have hQN : Q ≤ normalizer (N : Set G) := hQC.trans hCN
  have hnormal : (N.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQN
  obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one (Q ⊓ N)).resolve_left hne
  have hne' : N.subgroupOf Q ≠ ⊥ := by
    intro h
    have : (⟨y, hy.1⟩ : ↥Q) ∈ N.subgroupOf Q := hy.2
    rw [h, Subgroup.mem_bot] at this
    exact hy1 (congrArg Subtype.val this)
  obtain ⟨q, hq, hq1⟩ :=
    (Subgroup.bot_or_exists_ne_one _).resolve_left
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  obtain ⟨k, hk⟩ := S.hQp q
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hq1 hj
  have hv2 : orderOf (q ^ (orderOf q / 2)) = 2 :=
    orderOf_pow_orderOf_div (by rw [hj]; positivity) (by rw [hj]; exact dvd_pow_self 2 hj0)
  set v := q ^ (orderOf q / 2) with hv
  have hvc : v ∈ center ↥Q := Subgroup.pow_mem _ hq.2 _
  have hvN : (v : G) ∈ N := by
    rw [hv, Subgroup.coe_pow]
    exact Subgroup.pow_mem N hq.1 _
  have hvo : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hv2
  have hvx := S.center_inv_eq_x v.2 hvo (fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hvc ⟨g, hg⟩))
  exact S.x_not_mem_K (hNK (hvx ▸ hvN))

theorem false_of_setup (S : Setup x y K Q t K' Λ hxY) : False := by
  have hL1rk : 2 ≤ pRank 2 ↥(bar t K') :=
    CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center
      S.h.isComponent_L₁.1 (by rw [S.center_L₁_eq_bot, Subgroup.card_bot]; exact odd_one)
  set R₀ : Subgroup G := Q ⊓ CxK t K' with hR₀
  have hR₀p : IsPGroup 2 R₀ := S.hQp.to_le inf_le_left
  obtain ⟨hrk, -⟩ := S.h.gilman_bounds hR₀p (fun r hr => hr.2) (fun r hr => S.x_central r hr.1)
  have htR₀ : t ∈ R₀ := ⟨S.htQ, x_mem_CxK S.h.hK'c.1⟩
  have hR₀rk : 1 ≤ pRank 2 ↥R₀ := by
    rw [pRank_two_subgroup_eq_open]
    exact one_le_pRank_of_involution htR₀ S.h.hto
  have hrkC : pRank 2 ↥Q = pRank 2 ↥(CxK x K) := pRank_of_isSylowOf S.hQ
  have hQ2 := S.pRank_Q_le
  rcases S.hlex with hlt' | ⟨heq, -⟩
  · omega
  · omega

end Setup

omit [Finite G] in
theorem exists_sylow_with {x t : G} {K : Subgroup G} (hxC : x ∈ CxK x K) (htC : t ∈ CxK x K)
    (hxo : orderOf x = 2) (hto : orderOf t = 2) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q (CxK x K) ∧ t ∈ Q ∧ x ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCx : CxK x K ≤ centralizer ({x} : Set G) := inf_le_left
  have hZ : Subgroup.zpowers (⟨t, htC⟩ : ↥(CxK x K)) ≤ ⊤ := le_top
  have hpt : IsPGroup 2 (Subgroup.zpowers (⟨t, htC⟩ : ↥(CxK x K))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hto]; norm_num)
  obtain ⟨S, hS⟩ := hpt.exists_le_sylow
  have hxcenter : (⟨x, hxC⟩ : ↥(CxK x K)) ∈ Subgroup.center ↥(CxK x K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hCx g.2))
  have hxn : (Subgroup.zpowers (⟨x, hxC⟩ : ↥(CxK x K))).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hxcenter)
  have hpx : IsPGroup 2 (Subgroup.zpowers (⟨x, hxC⟩ : ↥(CxK x K))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hxo]; norm_num)
  have hxS : (⟨x, hxC⟩ : ↥(CxK x K)) ∈ (S : Subgroup ↥(CxK x K)) :=
    hpx.le_sylow_of_normal S (Subgroup.mem_zpowers _)
  have htS : (⟨t, htC⟩ : ↥(CxK x K)) ∈ (S : Subgroup ↥(CxK x K)) := hS (Subgroup.mem_zpowers _)
  exact ⟨(S : Subgroup ↥(CxK x K)).map (CxK x K).subtype, ⟨S, rfl⟩, ⟨_, htS, rfl⟩, ⟨_, hxS, rfl⟩⟩

private theorem x_normalizes_actorR0 {x t : G} {K Q K' Λ : Subgroup G}
    {hxY : x ∈ centralizer ({t} : Set G)}
    (hQ : IsSylowOf 2 Q (CxK x K)) (hxQ : x ∈ Q)
    (hlt : PumpUpLT 2 x K t K') (h : DiagData x t K K' Λ hxY)
    (hxR0 : x ∉ (Q ⊓ CxK t K' : Subgroup G)) :
    x ∈ normalizer ((Q ⊓ CxK t K' : Subgroup G) : Set G) := by
  let R : Subgroup G := Q ⊓ centralizer ({t} : Set G)
  let R₀ : Subgroup G := Q ⊓ CxK t K'
  have hty : t * x = x * t := mem_centralizer_singleton_iff.mp hlt.2.2.1
  have hxR : x ∈ R := by
    exact ⟨hxQ, mem_centralizer_singleton_iff.mpr hty.symm⟩
  have hR₀R : R₀ ≤ R := by
    intro r hr
    exact ⟨hr.1, (Subgroup.mem_inf.mp hr.2).1⟩
  have hcov : ∀ r ∈ R, r ∈ R₀ ∨ x * r ∈ R₀ := by
    intro r hr
    have hrC : r ∈ CxK x K := hQ.le hr.1
    rcases h.step1 hr.2 hrC with h1 | h1
    · exact Or.inl ⟨hr.1, h1⟩
    · exact Or.inr ⟨mul_mem hxQ hr.1, h1⟩
  have hxc : ∀ r ∈ R, r * x = x * r := by
    intro r hr
    exact mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hQ.le hr.1)).1
  have hidx : R₀.relIndex R = 2 :=
    relIndex_eq_two_of_cov hxR hxc (by simpa [R₀] using hxR0) (by simpa [R, R₀] using hcov)
  have hR₀n : (R₀.subgroupOf R).Normal := Subgroup.normal_of_index_eq_two hidx
  have hRN : R ≤ normalizer (R₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR₀R).mp hR₀n
  exact hRN hxR

theorem noDiag_of_rigid_gilman_of_immediate
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    {x : G} {K : Subgroup G} (hILo : IsILo 2 x K)
    (hrig_imm : ∀ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' →
      Nonempty (kBar K' ≃* kBar K))
    (hgm_imm : ∀ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' →
      pRank 2 ↥(CxK t K') < pRank 2 ↥(CxK x K) ∨
        (pRank 2 ↥(CxK t K') = pRank 2 ↥(CxK x K) ∧ sylVal t K' ≤ sylVal x K)) :
    ∀ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' → x ∈ normalizer (K' : Set G) := by
  intro t₀ K₀ hlt₀
  by_contra hdiag₀
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hxC : x ∈ CxK x K := x_mem_CxK hKc.1
  have ht₀C : t₀ ∈ CxK x K := mem_CxK_of_pumpUpLT hlt₀
  obtain ⟨Q, hQ, ht₀Q, hxQ⟩ := exists_sylow_with hxC ht₀C hILo.1 hlt₀.2.1.1
  let 𝒟 : Set G := {w | w ∈ Q ∧ orderOf w = 2 ∧
    ∃ M : Subgroup G, PumpUpLT 2 x K w M ∧ x ∉ normalizer (M : Set G)}
  have h𝒟 : t₀ ∈ 𝒟 := ⟨ht₀Q, hlt₀.2.1.1, K₀, hlt₀, hdiag₀⟩
  have : Nonempty ↥𝒟 := ⟨⟨t₀, h𝒟⟩⟩
  obtain ⟨⟨t, ht𝒟⟩, hmaxt⟩ :=
    Finite.exists_max (fun w : ↥𝒟 => Nat.card ↥(Q ⊓ centralizer ({(w : G)} : Set G)))
  obtain ⟨htQ, hto, K', hlt, hdiag⟩ := ht𝒟
  have hxY : x ∈ centralizer ({t} : Set G) := mem_centralizer_symm hlt.2.2.1
  obtain ⟨e⟩ := hrig_imm t K' hlt
  have hle : hatCard K' ≤ hatCard K := (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ⟩ := diagData_of_diag hlt hxY hle hdiag
  have hxR0 : x ∉ (Q ⊓ CxK t K' : Subgroup G) := fun hx => hΛ.x_not_mem_CxK hx.2
  have htyx : t * x = x * t := mem_centralizer_singleton_iff.mp hlt.2.2.1
  have hxR0norm : x ∈ normalizer ((Q ⊓ CxK t K' : Subgroup G) : Set G) :=
    x_normalizes_actorR0 hQ hxQ hlt hΛ hxR0
  have hhatx : ∀ (w : G) (M : Subgroup G), PumpUpLT 2 x K w M → w * x = x * w →
      hatCard M ≤ hatCard K := by
    intro w M hltw _
    obtain ⟨e⟩ := hrig_imm w M hltw
    exact (Nat.card_congr e.toEquiv).le
  have hlexx : pRank 2 ↥(CxK t K') < pRank 2 ↥(CxK x K) ∨
      (pRank 2 ↥(CxK t K') = pRank 2 ↥(CxK x K) ∧ sylVal t K' ≤ sylVal x K) :=
    hgm_imm t K' hlt
  have hmaxAt : ∀ w ∈ Q, orderOf w = 2 → w * x = x * w →
      (∃ M : Subgroup G, PumpUpLT 2 x K w M ∧ x ∉ normalizer (M : Set G)) →
      Nat.card ↥(Q ⊓ centralizer ({w} : Set G)) ≤
        Nat.card ↥(Q ⊓ centralizer ({t} : Set G)) :=
    fun w hwQ hwo _ hdw => hmaxt ⟨w, hwQ, hwo, hdw⟩
  exact (Setup.mk hR hILo hILo.1 hQ hxQ htQ hlt hΛ
    (Subgroup.le_normalizer hxQ) htyx hxR0norm hhatx hlexx hmaxAt).false_of_setup

theorem noDiag_of_rigid_gilman
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    {x : G} {K : Subgroup G} (hrig : IsPRigid 2 x K) (hgm : IsGilmanMax x K) :
    ∀ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' → x ∈ normalizer (K' : Set G) := by
  refine noDiag_of_rigid_gilman_of_immediate hR hrig.1 ?_ ?_
  · intro t K' hlt
    exact hrig.2 t K' (LongPumpUp.single' hlt)
  · intro t K' hlt
    exact hgm t K' (LongPumpUp.single' hlt)

theorem exists_twoTerminal
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    {x : G} {K : Subgroup G} (h : IsILo 2 x K) :
    ∃ (x' : G) (K' : Subgroup G), LongPumpUp 2 x K x' K' ∧ IsTwoTerminal x' K' :=
  exists_twoTerminal_of_noDiag (fun _ _ hrig hgm => noDiag_of_rigid_gilman hR hrig hgm) h

end Main

end CFSG.GH74.GLS.C3.Layer1.PumpRigid
