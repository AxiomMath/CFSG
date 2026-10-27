module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FEC
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FB
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot trivialOnQuot_conjSub)
open scoped commutatorElement

section EC


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem inf_S₁_eq (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W
    S₁ R₁ R₂ t t₁ u₁ u₂) :
    tightCore R ⊓ (S₁ : Subgroup Y) = R₁ ∧ K' ⊓ (S₁ : Subgroup Y) = R₂ := by
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hs.hK'.1
  have hR₁ : IsSylow2In R₁ (tightCore R) :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR₂ : IsSylow2In R₂ K' :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hyp.hR'.1 hyp.hR'.2.1
  exact ⟨hR₁.2.2 _ inf_le_left (S₁.isPGroup'.to_le inf_le_right) (le_inf hR₁.1 hyp.hR.2.2),
    hR₂.2.2 _ inf_le_left (S₁.isPGroup'.to_le inf_le_right) (le_inf hR₂.1 hyp.hR'.2.2)⟩

theorem comm_of_mem_tq {J P : Subgroup Y} (hP2 : IsPGroup 2 ↥P) (hPJ : P ≤ J) {s : Y}
    (hs : s ∈ trivialOnQuot J) (hsP : conjSub s P = P) : ∀ p ∈ P, s * p = p * s := by
  intro p hp
  have h1 : ⁅s, p⁆ ∈ Balance.oddCoreIn J := hs.2 p (hPJ hp)
  have h2 : s * p * s⁻¹ ∈ P := by
    have := conj_mem_conjSub (n := s) hp
    rwa [hsP] at this
  have h3 : ⁅s, p⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem h2 (P.inv_mem hp)
  have h4 : P ⊓ Balance.oddCoreIn J = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgP, hgO⟩
    rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
    obtain ⟨k, hk⟩ := hP2 ⟨g, hgP⟩
    have h5 : orderOf g ∣ 2 ^ k := by
      have h := orderOf_dvd_of_pow_eq_one hk
      rwa [Subgroup.orderOf_mk] at h
    have h6 : Odd (orderOf g) :=
      Odd.of_dvd_nat (Balance.odd_card_oddCoreIn J)
        (by
          have := Subgroup.orderOf_dvd_natCard (Balance.oddCoreIn J) hgO
          exact this)
    have h7 : Nat.Coprime (orderOf g) (2 ^ k) := Nat.Coprime.pow_right k (Odd.coprime_two_right h6)
    exact Nat.Coprime.eq_one_of_dvd h7 h5
  have h8 : ⁅s, p⁆ = 1 := by
    have : ⁅s, p⁆ ∈ P ⊓ Balance.oddCoreIn J := ⟨h3, h1⟩
    rwa [h4, Subgroup.mem_bot] at this
  have := commutatorElement_eq_one_iff_mul_comm.mp h8
  exact this

theorem ec_twin_both (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
      Subgroup.zpowers t) :
    (∀ x ∈ Subgroup.centralizer ({t} : Set Y), Odd (orderOf x) →
      x ∈ Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y))) ∧
    ∀ k ∈ Subgroup.centralizer ({t} : Set Y), ∃ o ∈ Balance.oddCoreIn
      (Subgroup.centralizer ({t} : Set Y)), ∃ s ∈ (S₁ : Subgroup Y), k = o * s := by
  classical
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  have hs := hyp.std.setting
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hzK : IsUniqueInvolution (tightCore R) t := hs.hz
  have hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := hs.hK'
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hK'.1
  have hne : K' ≠ tightCore R := hs.hne
  have hKtw : tightCore R ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    mem_twinSet_self hK hzK
  have hpair := twinSet_eq hP hyp
  have hconjK : ∀ c ∈ C, conjSub c (tightCore R) = tightCore R ∨ conjSub c (tightCore R) = K' := by
    intro c hc
    have := hP.conj_mem_twinSet hKtw hc
    rw [hpair] at this
    exact this
  have hconjK' : ∀ c ∈ C, conjSub c K' = tightCore R ∨ conjSub c K' = K' := by
    intro c hc
    have := hP.conj_mem_twinSet hK' hc
    rw [hpair] at this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hinj : ∀ c : Y, conjSub c (tightCore R) ≠ conjSub c K' := fun c h =>
    hne (Generic.conjSub_injective c h).symm
  let D : Subgroup Y := C ⊓ trivialOnQuot (tightCore R) ⊓ trivialOnQuot K'
  have hDC : D ≤ C := fun d hd => hd.1.1
  have hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D := by
    intro c hc d hd
    obtain ⟨⟨hdC, hdK⟩, hdK'⟩ := hd
    refine ⟨⟨C.mul_mem (C.mul_mem hc hdC) (C.inv_mem hc), ?_⟩, ?_⟩
    · have h1 := trivialOnQuot_conjSub hdK c
      have h2 := trivialOnQuot_conjSub hdK' c
      rcases hconjK c hc with e | e
      · rwa [e] at h1
      · rcases hconjK' c hc with e' | e'
        · rwa [e'] at h2
        · exact absurd (e.trans e'.symm) (hinj c)
    · have h1 := trivialOnQuot_conjSub hdK c
      have h2 := trivialOnQuot_conjSub hdK' c
      rcases hconjK' c hc with e | e
      · rcases hconjK c hc with e' | e'
        · exact absurd (e'.trans e.symm) (hinj c)
        · rwa [e'] at h1
      · rwa [e] at h2
  have hodd : ∀ x ∈ C, Odd (orderOf x) → x ∈ D := by
    intro x hx hxo
    have hxK : conjSub x (tightCore R) = tightCore R := by
      rcases hconjK x hx with e | e
      · exact e
      · exfalso
        have e2 : conjSub x K' = tightCore R := by
          rcases hconjK' x hx with e' | e'
          · exact e'
          · exact absurd (e.trans e'.symm) (hinj x)
        have hxx : conjSub (x * x) (tightCore R) = tightCore R := by
          rw [Generic.conjSub_mul, e, e2]
        obtain ⟨k, hk⟩ := hxo
        have hxpow : x = (x * x) ^ (k + 1) := by
          have h1 : x ^ (2 * k + 2) = x := by
            have : 2 * k + 2 = orderOf x + 1 := by omega
            rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
          rw [← sq, ← pow_mul, show 2 * (k + 1) = 2 * k + 2 by ring, h1]
        have hxN : x ∈ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) := by
          rw [hxpow]
          exact Subgroup.pow_mem _ (mem_normalizer_iff_conjSub_eq.mpr hxx) _
        have := mem_normalizer_iff_conjSub_eq.mp hxN
        rw [e] at this
        exact hne this
    have hxK' : conjSub x K' = K' := by
      rcases hconjK' x hx with e | e
      · exact absurd (hxK.trans e.symm) (hinj x)
      · exact e
    exact ⟨⟨hx, hP.odd_mem_trivialOnQuot hr hK (mem_normalizer_iff_conjSub_eq.mpr hxK) hxo⟩,
      hP.odd_mem_trivialOnQuot hr hK'Ω (mem_normalizer_iff_conjSub_eq.mpr hxK') hxo⟩
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have htD : t ∈ D := by
    have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hzK hK'
    refine ⟨⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩, ?_⟩
    · refine ⟨Subgroup.le_normalizer hzK.mem, fun x hx => ?_⟩
      have : ⁅t, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (hzK.commute_of_mem hx)
      rw [this]
      exact Subgroup.one_mem _
    · refine ⟨Subgroup.le_normalizer hzK'.mem, fun x hx => ?_⟩
      have : ⁅t, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (hzK'.commute_of_mem hx)
      rw [this]
      exact Subgroup.one_mem _
  obtain ⟨hKS, hK'S⟩ := inf_S₁_eq hyp
  have hnormR : ∀ (J R' : Subgroup Y), J ⊓ (S₁ : Subgroup Y) = R' → R' ≤ J →
      ∀ s ∈ (S₁ : Subgroup Y), s ∈ trivialOnQuot J → conjSub s R' = R' := by
    intro J R' hJR hR'J s hsS hsJ
    have hR'S : R' ≤ (S₁ : Subgroup Y) := hJR ▸ inf_le_right
    have hle : ∀ s' ∈ (S₁ : Subgroup Y), s' ∈ trivialOnQuot J → conjSub s' R' ≤ R' := by
      intro s' hs'S hs'J
      have h1 : conjSub s' R' ≤ J := by
        have := conjSub_mono (n := s') hR'J
        rwa [mem_normalizer_iff_conjSub_eq.mp hs'J.1] at this
      have h2 : conjSub s' R' ≤ (S₁ : Subgroup Y) := by
        intro y hy
        have h3 : s'⁻¹ * y * s' ∈ R' := mem_conjSub_iff.mp hy
        have h4 := (S₁ : Subgroup Y).mul_mem ((S₁ : Subgroup Y).mul_mem hs'S (hR'S h3))
          ((S₁ : Subgroup Y).inv_mem hs'S)
        simpa [mul_assoc] using h4
      have h5 : conjSub s' R' ≤ J ⊓ (S₁ : Subgroup Y) := le_inf h1 h2
      rwa [hJR] at h5
    refine Subgroup.eq_of_le_of_card_ge (hle s hsS hsJ) ?_
    rw [AscL62.natCard_conjSub]
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hR₁ : IsSylow2In R₁ (tightCore R) :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR₂ : IsSylow2In R₂ K' :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hyp.hR'.1 hyp.hR'.2.1
  have htR₁ : t ∈ R₁ := T7F25.Asc77.T7C.mem_of_isSylow2In hΩ hK hR₁ hzK
  have hSD : (S₁ : Subgroup Y) ⊓ D = Subgroup.zpowers t := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hyp.hR.2.2 htR₁, htD⟩)
    rintro s ⟨hsS, ⟨hsC, hsK⟩, hsK'⟩
    have hn₁ := hnormR (tightCore R) R₁ hKS hR₁.1 s hsS hsK
    have hn₂ := hnormR K' R₂ hK'S hR₂.1 s hsS hsK'
    have hc₁ := comm_of_mem_tq hR₁.2.1 hR₁.1 hsK hn₁
    have hc₂ := comm_of_mem_tq hR₂.2.1 hR₂.1 hsK' hn₂
    have hle : R₁ ⊔ R₂ ≤ Subgroup.centralizer ({s} : Set Y) :=
      sup_le (fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hc₁ p hp).symm)
        (fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hc₂ p hp).symm)
    have hcent : s ∈ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    have : s ∈ (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) :=
      ⟨hsS, hcent⟩
    rwa [h11] at this
  exact ⟨odd_mem_oddCoreIn_of_normal S₁ C D
    (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS s hs)) hDC hDn hodd ht2
    htD hSD, exists_oddCore_mul_of_normal S₁ C D
    (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS s hs)) hDC hDn hodd ht2
    htD hSD⟩

theorem ec_twin (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
      Subgroup.zpowers t) :
    ∀ k ∈ Subgroup.centralizer ({t} : Set Y), ∃ o ∈ Balance.oddCoreIn
      (Subgroup.centralizer ({t} : Set Y)), ∃ s ∈ (S₁ : Subgroup Y), k = o * s :=
  (ec_twin_both hr hP hyp h11).2

theorem ec_twin_odd (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
      Subgroup.zpowers t) :
    ∀ x ∈ Subgroup.centralizer ({t} : Set Y), Odd (orderOf x) →
      x ∈ Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
  (ec_twin_both hr hP hyp h11).1

end EC

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
