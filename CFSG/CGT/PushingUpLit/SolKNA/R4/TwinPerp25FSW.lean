module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FEC2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FPsiB
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FQa
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FQb

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

section SW


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ t' : Y}

theorem exists_coord_setting (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (hT : T7F25.Asc77.T7F2.Hyp25T (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁
      R₂ t t₁ u₁ u₂ t') :
    ∃ (x y : Y) (m : ℕ), T7F2.Out.Setting R₁ (T7F2.Nsub S₁ R₁) x y m ∧ 2 ≤ m := by
  have hN2 : IsPGroup 2 ↥(T7F2.Nsub S₁ R₁) := S₁.isPGroup'.to_le inf_le_left
  have hNR : ∀ y ∈ T7F2.Nsub S₁ R₁, conjSub y R₁ = R₁ := fun y hy => (T7F2.mem_Nsub.mp hy).2
  obtain ⟨x, y, m, c, hNa⟩ := T7F2.exists_coord hT.hqR hT.hzR hN2 hNR
  refine ⟨x, y, m, ⟨c, hT.R_le_N, hNR, hNa⟩, ?_⟩
  have h1 := c.natCard
  rw [card_R₁ hr hP hyp] at h1
  have := Nat.pow_right_injective (le_refl 2) h1
  omega

theorem swap_R_of_ff (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) (hb2 : b * b = 1) (hF₁ : IsFAut R₁ b)
    {s : Y} (hsS : s ∈ (S₁ : Subgroup Y)) (hs2 : s * s = 1) (hst : s ≠ t)
    (hconj : ∃ y : Y, y * t * y⁻¹ = s) (hsb : s * b = b * s) : conjSub s R₁ = R₂ := by
  obtain ⟨t', hT⟩ := T7F25.Asc77.T7T.exists_hyp25T hyp
  rcases hT.perm_R hsS with h | h
  · exfalso
    obtain ⟨x, y, m, st, hm2⟩ := exists_coord_setting hr hP hyp hT
    have c := st.coord
    have hsN : s ∈ T7F2.Nsub S₁ R₁ := T7F2.mem_Nsub.mpr ⟨hsS, h⟩
    have hbN : b ∈ T7F2.Nsub S₁ R₁ :=
      T7F2.mem_Nsub.mpr ⟨hbS, mem_normalizer_iff_conjSub_eq.mp hF₁.1⟩
    obtain ⟨is, js, -, hxs, hys⟩ := st.coord_of_mem hsN
    obtain ⟨ib, jb, -, hxb, hyb⟩ := st.coord_of_mem hbN
    have hs := hyp.std.setting
    have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
    have hzK : IsUniqueInvolution (tightCore R) t := hs.hz
    obtain ⟨y₀, hy₀⟩ := hconj
    have hno : ¬ ∃ w ∈ R₁, orderOf w = 4 ∧ w * s = s * w := by
      rintro ⟨w, hwR, hw4, hwc⟩
      exact not_commute_ord4 hyp hK hzK (y := y₀) (by rw [hy₀]; exact hst)
        (hyp.hR.2.1 hwR) hw4 (by rw [hy₀]; exact hwc.symm)
    obtain ⟨hsd, hsd'⟩ := sd_coord c hm2 hs2 hxs hys hno
    have hb2' : b * b ∈ Subgroup.zpowers t := by
      rw [hb2]; exact Subgroup.one_mem _
    obtain ⟨-, hxb', j, hyb', hj⟩ := T7U.coord_of_isFAut hT.hqR hT.hzR st hbN hF₁ hb2'
    have hxbi : (2 : ℤ) ^ (m + 1) ∣ ib - (1 + 2 ^ m) := by
      rw [hxb'] at hxb
      exact c.zpow_eq_iff.mp hxb.symm
    have hyj : (2 : ℤ) ^ (m + 1) ∣ jb - j := by
      have := hyb.symm.trans hyb'
      exact c.zpow_eq_iff.mp (mul_left_cancel this)
    have hjb : (2 : ℤ) ^ m ∣ jb := by
      have h2 : (2 : ℤ) ^ m ∣ j := by
        rcases hj with h0 | h0
        · have h1 : x ^ j = x ^ (0 : ℤ) := by rw [h0, zpow_zero]
          have := c.zpow_eq_iff.mp h1
          rw [sub_zero] at this
          exact (pow_dvd_pow 2 (Nat.le_succ m)).trans this
        · have h1 : x ^ j = x ^ ((2 ^ m : ℕ) : ℤ) := by rw [h0, zpow_natCast]
          have := c.zpow_eq_iff.mp h1
          have h3 : (2 : ℤ) ^ m ∣ j - ((2 ^ m : ℕ) : ℤ) :=
            (pow_dvd_pow 2 (Nat.le_succ m)).trans this
          have h4 : (2 : ℤ) ^ m ∣ ((2 ^ m : ℕ) : ℤ) := by push_cast; exact dvd_rfl
          have := dvd_add h3 h4
          simpa using this
      have h5 : (2 : ℤ) ^ m ∣ jb - j := (pow_dvd_pow 2 (Nat.le_succ m)).trans hyj
      have := dvd_add h5 h2
      simpa using this
    exact ff_not_commute c hm2 hxb hyb hxs hys hxbi hjb hsd hsd' hsb.symm
  · exact h

theorem inf_odd_two_eq_bot {P O : Subgroup Y} (hP : IsPGroup 2 ↥P) (hO : Odd (Nat.card ↥O)) :
    P ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgP, hgO⟩
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
  obtain ⟨k, hk⟩ := hP ⟨g, hgP⟩
  have h5 : orderOf g ∣ 2 ^ k := by
    have h := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at h
  have h6 : Odd (orderOf g) :=
    Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hgO)
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Odd.coprime_two_right h6)) h5

theorem odd_fixes_twins (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) {x : Y} (hxC : x ∈ Subgroup.centralizer ({t} : Set Y)) (hxo : Odd (orderOf x)) :
    conjSub x (tightCore R) = tightCore R ∧ conjSub x K' = K' := by
  have hs := hyp.std.setting
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hzK : IsUniqueInvolution (tightCore R) t := hs.hz
  have hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := hs.hK'
  have hne : K' ≠ tightCore R := hs.hne
  have hKtw : tightCore R ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    mem_twinSet_self hK hzK
  have hpair := twinSet_eq hP hyp
  have hconjK : conjSub x (tightCore R) = tightCore R ∨ conjSub x (tightCore R) = K' := by
    have := hP.conj_mem_twinSet hKtw hxC
    rw [hpair] at this
    exact this
  have hconjK' : conjSub x K' = tightCore R ∨ conjSub x K' = K' := by
    have := hP.conj_mem_twinSet hK' hxC
    rw [hpair] at this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hinj : conjSub x (tightCore R) ≠ conjSub x K' := fun h =>
    hne (Generic.conjSub_injective x h).symm
  have hxK : conjSub x (tightCore R) = tightCore R := by
    rcases hconjK with e | e
    · exact e
    · exfalso
      have e2 : conjSub x K' = tightCore R := by
        rcases hconjK' with e' | e'
        · exact e'
        · exact absurd (e.trans e'.symm) hinj
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
  refine ⟨hxK, ?_⟩
  rcases hconjK' with e | e
  · exact absurd (hxK.trans e.symm) hinj
  · exact e

theorem adjust_to_S₁ (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
      Subgroup.zpowers t) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) {s : Y} (hsC : s * t = t * s)
    (hsb : s * b = b * s) (hs2 : s * s = 1) :
    ∃ o : Y, o ∈ Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) ∧ o * b = b * o ∧
      o * s * o⁻¹ ∈ (S₁ : Subgroup Y) := by
  classical
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  have hS₁C : (S₁ : Subgroup Y) ≤ C := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS u hu)
  have hsC' : s ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hsC
  obtain ⟨o₀, ho₀, s₀, hs₀, hse⟩ := ec_twin hr hP hyp h11 s hsC'
  have hbC : b ∈ C := hS₁C hbS
  have hOS : Balance.oddCoreIn C ⊓ (S₁ : Subgroup Y) = ⊥ := by
    rw [inf_comm]
    exact inf_odd_two_eq_bot S₁.isPGroup' (Balance.odd_card_oddCoreIn C)
  have hbo : b * o₀ * b⁻¹ ∈ Balance.oddCoreIn C := Balance.conj_mem_oddCoreIn hbC ho₀
  have hbs₀ : b * s₀ * b⁻¹ ∈ (S₁ : Subgroup Y) :=
    (S₁ : Subgroup Y).mul_mem ((S₁ : Subgroup Y).mul_mem hbS hs₀) ((S₁ : Subgroup Y).inv_mem hbS)
  have hprod : (b * o₀ * b⁻¹) * (b * s₀ * b⁻¹) = o₀ * s₀ := by
    have : b * s * b⁻¹ = s := by
      calc b * s * b⁻¹ = (s * b) * b⁻¹ := by rw [hsb]
        _ = s := by group
    rw [hse] at this
    calc (b * o₀ * b⁻¹) * (b * s₀ * b⁻¹) = b * (o₀ * s₀) * b⁻¹ := by group
      _ = o₀ * s₀ := this
  have hxy : o₀⁻¹ * (b * o₀ * b⁻¹) = s₀ * (b * s₀ * b⁻¹)⁻¹ := by
    have h1 : o₀⁻¹ * ((b * o₀ * b⁻¹) * (b * s₀ * b⁻¹)) * (b * s₀ * b⁻¹)⁻¹ =
        s₀ * (b * s₀ * b⁻¹)⁻¹ := by
      rw [hprod]; group
    rw [← h1]; group
  have hx1 : o₀⁻¹ * (b * o₀ * b⁻¹) = 1 := by
    have hmem : o₀⁻¹ * (b * o₀ * b⁻¹) ∈ Balance.oddCoreIn C ⊓ (S₁ : Subgroup Y) :=
      ⟨(Balance.oddCoreIn C).mul_mem ((Balance.oddCoreIn C).inv_mem ho₀) hbo, by
        rw [hxy]
        exact (S₁ : Subgroup Y).mul_mem hs₀ ((S₁ : Subgroup Y).inv_mem hbs₀)⟩
    rwa [hOS, Subgroup.mem_bot] at hmem
  have hbo₀ : o₀ * b = b * o₀ := by
    have : b * o₀ * b⁻¹ = o₀ := (inv_mul_eq_one.mp hx1).symm
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hbs₀' : s₀ * b = b * s₀ := by
    have h2 : s₀ * (b * s₀ * b⁻¹)⁻¹ = 1 := by rw [← hxy, hx1]
    have h3 : b * s₀ * b⁻¹ = s₀ := (mul_inv_eq_one.mp h2).symm
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hsq : o₀ * s₀ * (o₀ * s₀) = 1 := by rw [← hse]; exact hs2
  have hq : s₀ * o₀ * s₀⁻¹ ∈ Balance.oddCoreIn C :=
    Balance.conj_mem_oddCoreIn (hS₁C hs₀) ho₀
  have hs₀2 : s₀ * s₀ = 1 := by
    have h1 : s₀ * s₀ = (o₀ * (s₀ * o₀ * s₀⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_right (by
        calc o₀ * (s₀ * o₀ * s₀⁻¹) * (s₀ * s₀) = o₀ * s₀ * (o₀ * s₀) := by group
          _ = 1 := hsq)
    have hmem : s₀ * s₀ ∈ Balance.oddCoreIn C ⊓ (S₁ : Subgroup Y) :=
      ⟨by rw [h1]; exact (Balance.oddCoreIn C).inv_mem ((Balance.oddCoreIn C).mul_mem ho₀ hq),
        (S₁ : Subgroup Y).mul_mem hs₀ hs₀⟩
    rwa [hOS, Subgroup.mem_bot] at hmem
  have hso : s₀ * o₀ * s₀⁻¹ = o₀⁻¹ := by
    have : o₀ * (s₀ * o₀ * s₀⁻¹) = 1 := by
      have h1 : o₀ * s₀ * (o₀ * s₀) = o₀ * (s₀ * o₀ * s₀⁻¹) * (s₀ * s₀) := by group
      rw [hs₀2, mul_one] at h1
      rw [← h1]; exact hsq
    exact eq_inv_of_mul_eq_one_right this
  have hodd : Odd (orderOf o₀) :=
    Odd.of_dvd_nat (Balance.odd_card_oddCoreIn C) (Subgroup.orderOf_dvd_natCard _ ho₀)
  obtain ⟨w, hw, hws⟩ := exists_conj_of_inv_odd hs₀2 hodd hso
  have hwO : w ∈ Balance.oddCoreIn C := (Subgroup.zpowers_le.mpr ho₀) hw
  refine ⟨w⁻¹, (Balance.oddCoreIn C).inv_mem hwO, ?_, ?_⟩
  · have hcom : Commute w b := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_left (show Commute o₀ b from hbo₀) k)
    exact (hcom.inv_left).eq
  · have : w⁻¹ * s * w = s₀ := by
      rw [hse, hws]; group
    have e : w⁻¹ * s * w⁻¹⁻¹ = s₀ := by simpa using this
    rw [e]; exact hs₀


end SW

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
