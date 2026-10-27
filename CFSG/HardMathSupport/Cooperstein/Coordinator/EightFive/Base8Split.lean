module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.EightSplit
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.EightFactor
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Fac
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.EightCoprime

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

variable {V : Type*} [CommGroup V]

@[expose] def ThreeCycleFixFreeOn (K : Subgroup (MulAut V)) {L : Subgroup (MulAut V)} {n : ℕ}
    (ι : ↥L ≃* alternatingGroup (Fin n)) : Prop :=
  ∀ Y₀ Y₁ : Subgroup V, IsChiefFac K Y₀ Y₁ → ¬ IsCentralSec L Y₀ Y₁ →
    ∀ (x : MulAut V) (hx : x ∈ L), (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle →
      fixV (autSec (Subgroup.zpowers x) Y₁ Y₀) = ⊥

variable [Finite V]

theorem inf_fixV_zpowers_le_of_commute_on (hV : ∀ v : V, v ^ 2 = 1)
    {K L : Subgroup (MulAut V)} {a b : MulAut V}
    (ha : ∀ Y₀ Y₁ : Subgroup V, IsChiefFac K Y₀ Y₁ → ¬ IsCentralSec L Y₀ Y₁ →
      fixV (autSec (Subgroup.zpowers a) Y₁ Y₀) = ⊥)
    (hb : b ∈ L) {m : ℕ} (hm : Odd m) (hbm : b ^ m = 1) (hab : a * b = b * a)
    {Y : Subgroup V} (hY : K ≤ stabSub Y) :
    Y ⊓ fixV (Subgroup.zpowers a) ≤ fixV (Subgroup.zpowers b) := by
  suffices h : ∀ k : ℕ, ∀ Y : Subgroup V, Nat.card Y = k → K ≤ stabSub Y →
      Y ⊓ fixV (Subgroup.zpowers a) ≤ fixV (Subgroup.zpowers b) from h _ Y rfl hY
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Y hk hY
  rcases eq_or_ne Y ⊥ with rfl | hbot
  · rintro c ⟨hc, -⟩
    rw [Subgroup.mem_bot.1 hc]
    exact (fixV _).one_mem
  obtain ⟨Y₀, -, hch⟩ := exists_isChiefFac_of_lt (bot_lt_iff_ne_bot.2 hbot) (le_stabSub_bot K) hY
  have ih₀ : Y₀ ⊓ fixV (Subgroup.zpowers a) ≤ fixV (Subgroup.zpowers b) :=
    ih _ (hk ▸ Subgroup.card_lt_of_lt hch.lt) Y₀ rfl hch.stab₀
  by_cases hcen : IsCentralSec L Y₀ Y
  · intro c hc
    obtain ⟨hcY, hca⟩ := Subgroup.mem_inf.1 hc
    rw [mem_fixV_zpowers_iff] at hca ⊢
    have hab' : a (b c) = b (a c) := by
      have := congrArg (fun g : MulAut V => g c) hab
      simpa only [MulAut.mul_apply] using this
    have hd₀ : b c * c⁻¹ ∈ Y₀ := hcen b hb c hcY
    have hda : a (b c * c⁻¹) = b c * c⁻¹ := by rw [map_mul, map_inv, hab', hca]
    have hdb : b (b c * c⁻¹) = b c * c⁻¹ :=
      mem_fixV_zpowers_iff.1 (ih₀ ⟨hd₀, mem_fixV_zpowers_iff.2 hda⟩)
    have hbc : b c = (b c * c⁻¹) * c := (inv_mul_cancel_right _ _).symm
    have hpow : ∀ j : ℕ, (b ^ j) c = (b c * c⁻¹) ^ j * c := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        rw [pow_succ', MulAut.mul_apply, ihj, map_mul, map_pow, hdb, pow_succ, mul_assoc,
          ← hbc]
    have h1 := hpow m
    rw [hbm, MulAut.one_apply, pow_odd_eq_self hV hm] at h1
    have hd1 : b c * c⁻¹ = 1 := by
      have h2 := congrArg (· * c⁻¹) h1
      simp only [mul_inv_cancel, mul_assoc] at h2
      rw [mul_one] at h2
      exact h2.symm
    rw [hbc, hd1, one_mul]
  · intro c hc
    exact ih₀ ⟨inf_fixV_le_of_fixV_autSec_eq_bot (ha Y₀ Y hch hcen) hc, hc.2⟩

section ThreeCycles

variable {K L : Subgroup (MulAut V)} {n : ℕ} (ι : ↥L ≃* alternatingGroup (Fin n))

theorem fixV_eq_and_commV_eq_of_commute_on (hV : ∀ v : V, v ^ 2 = 1)
    (hι : ThreeCycleFixFreeOn K ι) {x z : MulAut V} (hx : x ∈ L) (hz : z ∈ L)
    (h3x : (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle)
    (h3z : (ι ⟨z, hz⟩ : Perm (Fin n)).IsThreeCycle) (hxz : x * z = z * x) :
    fixV (Subgroup.zpowers x) = fixV (Subgroup.zpowers z) ∧
      commV (Subgroup.zpowers x) = commV (Subgroup.zpowers z) := by
  have hx3 := pow_three_eq_one_of_isThreeCycle ι hx h3x
  have hz3 := pow_three_eq_one_of_isThreeCycle ι hz h3z
  have h1 := inf_fixV_zpowers_le_of_commute_on hV
    (fun Y₀ Y₁ hch hnc => hι Y₀ Y₁ hch hnc x hx h3x) hz (by decide : Odd 3) hz3 hxz
    (le_stabSub_top K)
  have h2 := inf_fixV_zpowers_le_of_commute_on hV
    (fun Y₀ Y₁ hch hnc => hι Y₀ Y₁ hch hnc z hz h3z) hx (by decide : Odd 3) hx3 hxz.symm
    (le_stabSub_top K)
  rw [top_inf_eq] at h1 h2
  have hf := le_antisymm h1 h2
  have ox := odd_card_zpowers_of_pow_three hx3
  have oz := odd_card_zpowers_of_pow_three hz3
  exact ⟨hf, le_antisymm (commV_zpowers_le_of_commute hV ox oz hxz hf.ge)
    (commV_zpowers_le_of_commute hV oz ox hxz.symm hf.le)⟩

theorem fixV_eq_and_commV_eq_of_isThreeCycle_on (hn : 8 ≤ n) (hV : ∀ v : V, v ^ 2 = 1)
    (hι : ThreeCycleFixFreeOn K ι) {x y : MulAut V} (hx : x ∈ L) (hy : y ∈ L)
    (h3x : (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle)
    (h3y : (ι ⟨y, hy⟩ : Perm (Fin n)).IsThreeCycle) :
    fixV (Subgroup.zpowers x) = fixV (Subgroup.zpowers y) ∧
      commV (Subgroup.zpowers x) = commV (Subgroup.zpowers y) := by
  obtain ⟨z, hz, h3z, hzx, hzy⟩ := exists_isThreeCycle_commute_mem hn ι hx hy h3x h3y
  obtain ⟨e1, e2⟩ := fixV_eq_and_commV_eq_of_commute_on ι hV hι hx hz h3x h3z hzx.symm
  obtain ⟨e3, e4⟩ := fixV_eq_and_commV_eq_of_commute_on ι hV hι hz hy h3z h3y hzy
  exact ⟨e1.trans e3, e2.trans e4⟩

theorem fixV_zpowers_eq_fixV_on (hn : 8 ≤ n) (hV : ∀ v : V, v ^ 2 = 1)
    (hι : ThreeCycleFixFreeOn K ι) {x : MulAut V} (hx : x ∈ L)
    (h3x : (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle) :
    fixV (Subgroup.zpowers x) = fixV L := by
  refine le_antisymm (fun c hc => ?_) fun v hv g hg => hv g (Subgroup.zpowers_le.2 hx hg)
  have hle : L ≤ MulAction.stabilizer (MulAut V) c := le_of_isThreeCycle_mem ι fun y hy h3y => by
    have hcy : c ∈ fixV (Subgroup.zpowers y) :=
      (fixV_eq_and_commV_eq_of_isThreeCycle_on ι hn hV hι hx hy h3x h3y).1 ▸ hc
    exact MulAction.mem_stabilizer_iff.2 (mem_fixV_zpowers_iff.1 hcy)
  exact fun g hg => MulAction.mem_stabilizer_iff.1 (hle hg)

theorem commV_eq_commV_zpowers_on (hn : 8 ≤ n) (hV : ∀ v : V, v ^ 2 = 1)
    (hι : ThreeCycleFixFreeOn K ι) {x : MulAut V} (hx : x ∈ L)
    (h3x : (ι ⟨x, hx⟩ : Perm (Fin n)).IsThreeCycle) :
    commV L = commV (Subgroup.zpowers x) := by
  have hWL : L ≤ stabSub (commV (Subgroup.zpowers x)) :=
    le_of_isThreeCycle_mem ι fun y hy h3y => by
      rw [(fixV_eq_and_commV_eq_of_isThreeCycle_on ι hn hV hι hx hy h3x h3y).2]
      exact le_stabSub_commV (Subgroup.le_normalizer) (Subgroup.mem_zpowers y)
  have hx3 := pow_three_eq_one_of_isThreeCycle ι hx h3x
  have hfix := fixV_zpowers_eq_fixV_on ι hn hV hι hx h3x
  refine le_antisymm ?_ (Subgroup.closure_mono fun _ ⟨g, hg, v, h⟩ =>
    ⟨g, Subgroup.zpowers_le.2 hx hg, v, h⟩)
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨l, hl, v, rfl⟩
  have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ commV (Subgroup.zpowers x) := by
    rw [fixV_sup_commV_zpowers_eq_top hV hx3]
    exact Subgroup.mem_top v
  obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
  have hlc : l c = c := (hfix ▸ hc) l hl
  have hlw : l w ∈ commV (Subgroup.zpowers x) := (hWL hl w).2 hw
  have h1 : l (c * w) * (c * w)⁻¹ = l w * w⁻¹ := by
    rw [map_mul, hlc, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  rw [SetLike.mem_coe, h1]
  exact Subgroup.mul_mem _ hlw (Subgroup.inv_mem _ hw)

theorem commV_sup_fixV_eq_top_on (hn : 8 ≤ n) (hV : ∀ v : V, v ^ 2 = 1)
    (hι : ThreeCycleFixFreeOn K ι) : commV L ⊔ fixV L = ⊤ := by
  obtain ⟨x, hx, h3x⟩ := exists_isThreeCycle_mem (by omega) ι
  rw [commV_eq_commV_zpowers_on ι hn hV hι hx h3x,
    ← fixV_zpowers_eq_fixV_on ι hn hV hι hx h3x, sup_comm]
  exact fixV_sup_commV_zpowers_eq_top hV (pow_three_eq_one_of_isThreeCycle ι hx h3x)

theorem commV_inf_fixV_eq_bot_on (hn : 8 ≤ n) (hV : ∀ v : V, v ^ 2 = 1)
    (hι : ThreeCycleFixFreeOn K ι) : commV L ⊓ fixV L = ⊥ := by
  obtain ⟨x, hx, h3x⟩ := exists_isThreeCycle_mem (by omega) ι
  rw [commV_eq_commV_zpowers_on ι hn hV hι hx h3x,
    ← fixV_zpowers_eq_fixV_on ι hn hV hι hx h3x, inf_comm]
  exact fixV_inf_commV_zpowers_eq_bot hV (pow_three_eq_one_of_isThreeCycle ι hx h3x)

end ThreeCycles

theorem fixV_autSec_eq_bot_of_split (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V} (hx3 : x ^ 3 = 1)
    {Y₀ Y' Y₁ : Subgroup V} (h0 : Y₀ ≤ Y') (h1 : Y' ≤ Y₁) (hx₀ : x ∈ stabSub Y₀)
    (hx' : x ∈ stabSub Y') (hx₁ : x ∈ stabSub Y₁)
    (hA : fixV (autSec (Subgroup.zpowers x) Y' Y₀) = ⊥)
    (hB : fixV (autSec (Subgroup.zpowers x) Y₁ Y') = ⊥) :
    fixV (autSec (Subgroup.zpowers x) Y₁ Y₀) = ⊥ := by
  have ho := odd_card_zpowers_of_pow_three hx3
  rw [fixV_autSec_eq_bot_iff hV ho (h0.trans h1) (Subgroup.zpowers_le.2 hx₀)
    (Subgroup.zpowers_le.2 hx₁)]
  have hA' := (fixV_autSec_eq_bot_iff hV ho h0 (Subgroup.zpowers_le.2 hx₀)
    (Subgroup.zpowers_le.2 hx')).1 hA
  have hB' := (fixV_autSec_eq_bot_iff hV ho h1 (Subgroup.zpowers_le.2 hx')
    (Subgroup.zpowers_le.2 hx₁)).1 hB
  intro c hc
  exact hA' ⟨hB' hc, hc.2⟩

section AltPre

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 8)}

theorem threeCycleFixFreeOn_of_not_natSec (hB42 : B42L42Core) (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 8) ≤ ψ.range)
    {A : Subgroup (MulAut V)} (hAoff : IsFFStarOffender H A)
    (hII : ∀ Y₀ Y₁ : Subgroup V, IsChiefFac H Y₀ Y₁ → ¬ IsCentralSec (altPre ψ) Y₀ Y₁ →
      ¬ NatSec ψ Y₀ Y₁) :
    ThreeCycleFixFreeOn H (altPreEquiv hψ hA) := by
  intro Y₀ Y₁ hY hL x hx h3
  have hLY₀ : altPre ψ ≤ stabSub Y₀ := altPre_le.trans hY.stab₀
  have hLY₁ : altPre ψ ≤ stabSub Y₁ := altPre_le.trans hY.stab₁
  rcases chief_cases hB42 hV hψ hA hAoff hY hL with ⟨h16, -⟩ | hN | ⟨Y', g, hS, h16, h16'⟩
  · exact fixV_autSec_zpowers_eq_bot_of_card_sec_eq_sixteen _ hLY₀ hLY₁ hL h16 hx h3
  · exact absurd hN (hII Y₀ Y₁ hY hL)
  · exact fixV_autSec_eq_bot_of_split hV (pow_three_eq_one_of_isThreeCycle _ hx h3) hS.le₀ hS.le₁
      (hLY₀ hx) (hS.stab hx) (hLY₁ hx)
      (fixV_autSec_zpowers_eq_bot_of_card_sec_eq_sixteen _ hLY₀ hS.stab hS.nc₀ h16 hx h3)
      (fixV_autSec_zpowers_eq_bot_of_card_sec_eq_sixteen _ hS.stab hLY₁ hS.nc₁ h16' hx h3)

theorem exotic_one_two (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 8) ≤ ψ.range) (hι : ThreeCycleFixFreeOn H (altPreEquiv hψ hA)) :
    commV (altPre ψ) ⊔ fixV (altPre ψ) = ⊤ ∧
      ∀ x : ↥H, (ψ x).IsThreeCycle →
        fixV (Subgroup.zpowers (x : MulAut V)) ⊓ commV (altPre ψ) = ⊥ := by
  refine ⟨commV_sup_fixV_eq_top_on _ le_rfl hV hι, fun x h3 => ?_⟩
  have hxL : (x : MulAut V) ∈ altPre ψ := coe_mem_altPre_iff.2 h3.mem_alternatingGroup
  have h3' : ((altPreEquiv hψ hA) ⟨x, hxL⟩ : Perm (Fin 8)).IsThreeCycle := by
    rw [coe_altPreEquiv]
    exact h3
  rw [fixV_zpowers_eq_fixV_on _ le_rfl hV hι hxL h3', inf_comm]
  exact commV_inf_fixV_eq_bot_on _ le_rfl hV hι

end AltPre

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
