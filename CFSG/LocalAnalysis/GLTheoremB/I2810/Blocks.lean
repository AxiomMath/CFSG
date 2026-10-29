module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksChief
import CFSG.GroupTheory.PCore.OpenTransport

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

open BlocksAux BlocksChief

section Shared
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem centre_trivial (h : Setup28 W K S) (hR : Red28 W K S)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S)
    (hz : ∀ z ∈ zPre W K, ∀ v ∈ vOf W K S, z * v * z⁻¹ = v) :
    Subgroup.center ↥(bar W K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  obtain ⟨k, rfl⟩ := toBar_surjective W K c
  have hkz : (k : X) ∈ zPre W K := zPre_of_center hc
  obtain ⟨e, b, hb, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (k : X)).ne'
  set z : X := (k : X) ^ (2 ^ e) with hzdef
  have hzK : z ∈ K := K.pow_mem k.2 _
  have hzz : z ∈ zPre W K := (zPre W K).pow_mem hkz _
  have hzodd : Odd (orderOf z) := by
    have hdvd : 2 ^ e ∣ orderOf (k : X) := hord ▸ dvd_mul_right _ _
    rw [hzdef, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hord,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hb
  have hP : IsPGroup 2 ↥(kerAct W K S) := h.hS.to_le hR.w1_S
  have hcent := odd_trivial hzodd hP hR.v_le (hz z hzz) (fun x hx => hE z hzK x hx)
  have hzW1 : z ∈ kerAct W K S := by
    apply hR.w1_cent
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hcent x hx
    calc x * z = (z * x * z⁻¹) * z := by rw [this]
      _ = z * x := by group
  have hz1 : z = 1 := eq_one_of_odd_of_mem hP hzW1 hzodd
  have hc1 : toBar W K k ^ (2 ^ e) = 1 := by
    rw [← map_pow, toBar_eq_one_iff]
    show (k : X) ^ (2 ^ e) ∈ W
    rw [← hzdef, hz1]
    exact W.one_mem
  have hdvd : orderOf (toBar W K k) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hc1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hc2 : IsPGroup 2 ↥(Subgroup.zpowers (toBar W K k)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  have hnorm : (Subgroup.zpowers (toBar W K k)).Normal :=
    Subgroup.normal_of_le_center (by rw [Subgroup.zpowers_le]; exact hc)
  have hle : Subgroup.zpowers (toBar W K k) ≤ CFSG.pCore 2 ↥(bar W K) := le_sSup ⟨hnorm, hc2⟩
  rw [h.hO] at hle
  exact Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))

theorem block_residual (h : Setup28 W K S) :
    ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 (↥K ⧸ N) → N = ⊤ := by
  intro N _ hN
  have hLt : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective (f := K.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, hLt, h.hK.2.1]
  haveI : Finite (↥K ⧸ N) := inferInstance
  haveI : Group.IsNilpotent (↥K ⧸ N) := hN.isNilpotent
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hcomm : commutator (↥K ⧸ N) = ⊤ := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ (QuotientGroup.mk' N)
    rw [hKtop, Subgroup.map_top_of_surjective _ hsurj] at h1
    exact h1.symm
  have hsub : Subsingleton (↥K ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K ⧸ N)).ne hcomm
  rw [eq_top_iff]
  intro x _
  exact (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)

theorem block_simple (h : Setup28 W K S) (hR : Red28 W K S)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
  haveI : IsSimpleGroup (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) := hR.quasi.2.1
  haveI : IsSimpleGroup ↥(bar W K) :=
    (isoOfCenterBot hZ (MulEquiv.refl (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)))).isSimpleGroup
  have hker : (toBar W K).ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker, toBar_eq_one_iff, ← CFSG.mem_openPCoreOf_iff, hR.o2K]
    exact ⟨fun hk => ⟨k.2, hk⟩, fun hk => hk.2⟩
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(bar W K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (toBar W K) (toBar_surjective W K))
  exact e.isSimpleGroup

theorem block_commutator_le (h : Setup28 W K S) (hR : Red28 W K S)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S) :
    ∀ x ∈ ⁅K, pCoreOf 2 K⁆, x ∈ pCoreOf 2 K ∧ x ^ 2 = 1 ∧ ∀ r ∈ pCoreOf 2 K, x * r = r * x := by
  intro x hx
  have hxV : x ∈ vOf W K S :=
    (Subgroup.commutator_le.2 (fun k hk r hr => hE k hk r (pCoreOf_le_w1 hR hr))) hx
  have hxR : x ∈ pCoreOf 2 K := by
    have hle : ⁅K, pCoreOf 2 K⁆ ≤ pCoreOf 2 K := by
      rw [hR.o2K, Subgroup.commutator_le]
      intro k hk r hr
      refine ⟨Subgroup.commutator_mem_commutator hk hr.1 |> fun h' => ?_, ?_⟩
      · have : ⁅k, r⁆ ∈ ⁅K, K⁆ := Subgroup.commutator_mem_commutator hk hr.1
        rwa [h.hK.2.1] at this
      · have : ⁅k, r⁆ = (k * r * k⁻¹) * r⁻¹ := rfl
        rw [this]
        exact W.mul_mem (Subgroup.Normal.conj_mem inferInstance r hr.2 k) (W.inv_mem hr.2)
    exact hle hx
  exact ⟨hxR, hxV.2.2, fun r hr => V_central hxV r (pCoreOf_le_w1 hR hr)⟩

theorem block_exists_noncentral (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S) :
    ∀ (n : ℕ) (T : Fin (n + 1) → Subgroup X), IsChiefSeriesIn K (pCoreOf 2 K) T →
      ∃ i : Fin n, ¬ ⁅T i.succ, K⁆ ≤ T i.castSucc := by
  intro n T hT
  by_contra hcon
  push Not at hcon
  have hind : ∀ j : Fin (n + 1), ⁅T j, K⁆ = ⊥ := by
    intro j
    induction j using Fin.induction with
    | zero => rw [hT.1]; exact Subgroup.commutator_bot_left K
    | succ i ih =>
      have h2 : ⁅⁅T i.succ, K⁆, K⁆ = ⊥ := by
        refine le_bot_iff.1 ?_
        rw [← ih]
        exact Subgroup.commutator_mono_left (hcon i)
      exact comm_eq_bot_of_perfect h.hK.2.1 h2
  have hRK : ⁅pCoreOf 2 K, K⁆ = ⊥ := by
    have := hind (Fin.last n)
    rwa [hT.2.1] at this
  have hVV : ⁅⁅vOf W K S, K⁆, K⁆ = ⊥ :=
    le_bot_iff.1 (hRK ▸ Subgroup.commutator_mono_left (comm_V_le_pCore h hR))
  have hVK : ⁅vOf W K S, K⁆ = ⊥ := comm_eq_bot_of_perfect h.hK.2.1 hVV
  apply hR.v_nt
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hVK

theorem block_unique_noncentral (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S) :
    ∀ (n : ℕ) (T : Fin (n + 1) → Subgroup X), IsChiefSeriesIn K (pCoreOf 2 K) T →
      ∀ i j : Fin n, ¬ ⁅T i.succ, K⁆ ≤ T i.castSucc → ¬ ⁅T j.succ, K⁆ ≤ T j.castSucc → i = j := by
  intro n T hT
  have key : ∀ i j : Fin n, i < j → ¬ ⁅T i.succ, K⁆ ≤ T i.castSucc →
      ¬ ⁅T j.succ, K⁆ ≤ T j.castSucc → False := by
    intro i j hij hi hj
    have hUiR := series_le hT i.succ
    have hUjR := series_le hT j.succ
    have hUjK : T j.succ ≤ K := hUjR.trans (CFSG.openPCoreOf_le 2 K)
    obtain ⟨-, -, -, -, hsupU, -, -, hcU₂⟩ := chief_core h hR sf hE ⟨hT.2.2 i, hUiR, hi⟩
    obtain ⟨-, hYjU₁, -⟩ := chief_core h hR sf hE ⟨hT.2.2 j, hUjR, hj⟩
    have hTjK : ⁅T j.castSucc, K⁆ ≤ T j.castSucc :=
      Subgroup.le_normalizer_iff_commutator_le_left.1 (hT.2.2 j).2.1
    have hUiTj : T i.succ ≤ T j.castSucc := series_mono hT (Fin.succ_le_castSucc_iff.2 hij)
    have step2 : ∀ u ∈ U₁, ∀ k ∈ K, ⁅u, k⁆ ∈ T j.castSucc := by
      intro u hu k hk
      rw [← hsupU] at hu
      obtain ⟨a, ha, w, hw, rfl⟩ := mem_sup_of_commute (H := ⁅T i.succ, K⁆) (L := U₂) hcU₂ hu
      rw [commutatorElement_mul_left, comm_eq_one_of_fix (sf.triv₂ k hk w hw)]
      have : ⁅a, k⁆ ∈ T j.castSucc :=
        hTjK (Subgroup.commutator_mem_commutator (hUiTj (chief_comm_le (hT.2.2 i) ha)) hk)
      simpa using this
    apply noncentral_comm_comm (hT.2.2 j) hUjK hj
    rw [Subgroup.commutator_le]
    intro y hy k hk
    exact step2 y (hYjU₁ hy) k hk
  intro i j hi hj
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij hi hj).elim
  · exact hij
  · exact (key j i hij hj hi).elim

theorem chief_transfer (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S)
    {A N : Type*} [Group A] [AddCommGroup N] (ρ : ↥K →* A) (act : A → N → N)
    (hiso : ChiefFactorIso K U₁ U₂ ρ act) {V' U : Subgroup X}
    (hU : IsNoncentralChiefFactor K (pCoreOf 2 K) V' U) : ChiefFactorIso K U V' ρ act := by
  obtain ⟨hYU, hYU₁, hYK, hsupV, hsupU, hinf, hcV, hcU⟩ := chief_core h hR sf hE hU
  obtain ⟨φ₁, hsurj, hker, hequiv⟩ := hiso
  have hUK : U ≤ K := hU.2.1.trans (CFSG.openPCoreOf_le 2 K)
  have hV'U : V' ≤ U := hU.1.1.le
  have hdec := chief_dec hU.1 hUK hU.2.2
  let θ : ↥⁅U, K⁆ →* Multiplicative N := φ₁.comp (Subgroup.inclusion hYU₁)
  have hθ : ∀ y : ↥⁅U, K⁆, (y : X) ∈ V' → θ y = 1 := by
    intro y hy
    have hyinf : (y : X) ∈ ⁅U, K⁆ ⊓ V' := ⟨y.2, hy⟩
    rw [hinf] at hyinf
    exact (hker ⟨y, hYU₁ y.2⟩).2 hyinf.2
  obtain ⟨Φ, hΦY, hΦV⟩ := exists_hom_of_prod hYU hV'U hdec hcV θ hθ
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro n'
    obtain ⟨u₁, hu₁⟩ := hsurj n'
    have hu₁mem : (u₁ : X) ∈ ⁅U, K⁆ ⊔ U₂ := by rw [hsupU]; exact u₁.2
    obtain ⟨a, ha, w, hw, hu⟩ :=
      mem_sup_of_commute (H := ⁅U, K⁆) (L := U₂) hcU hu₁mem
    refine ⟨Subgroup.inclusion hYU ⟨a, ha⟩, ?_⟩
    rw [hΦY]
    have h1 : u₁ = ⟨a, hYU₁ ha⟩ * ⟨w, sf.le.1 hw⟩ := Subtype.ext hu
    have h2 : φ₁ ⟨w, sf.le.1 hw⟩ = 1 := (hker _).2 hw
    rw [h1, map_mul, h2, mul_one] at hu₁
    exact hu₁
  · intro u
    constructor
    · intro hΦu
      obtain ⟨y, hy, v, hv, huv⟩ := hdec u u.2
      have hu : u = Subgroup.inclusion hYU ⟨y, hy⟩ * Subgroup.inclusion hV'U ⟨v, hv⟩ :=
        Subtype.ext huv
      rw [hu, map_mul, hΦY, hΦV, mul_one] at hΦu
      have hyU₂ : y ∈ U₂ := (hker ⟨y, hYU₁ hy⟩).1 hΦu
      have hyV' : y ∈ V' := by
        have : y ∈ ⁅U, K⁆ ⊓ U₂ := ⟨hy, hyU₂⟩
        rw [← hinf] at this
        exact this.2
      rw [huv]
      exact V'.mul_mem hyV' hv
    · intro hu
      exact hΦV ⟨u, hu⟩
  · intro ℓ u u' hu'
    obtain ⟨y, hy, v, hv, huv⟩ := hdec u u.2
    have hu : u = Subgroup.inclusion hYU ⟨y, hy⟩ * Subgroup.inclusion hV'U ⟨v, hv⟩ :=
      Subtype.ext huv
    have hy' : (ℓ : X) * y * (ℓ : X)⁻¹ ∈ ⁅U, K⁆ := hYK ℓ ℓ.2 y hy
    have hv' : (ℓ : X) * v * (ℓ : X)⁻¹ ∈ V' := Subgroup.le_normalizer_iff.1 hU.1.2.1 ℓ ℓ.2 v hv
    have hu'eq : u' = Subgroup.inclusion hYU ⟨_, hy'⟩ * Subgroup.inclusion hV'U ⟨_, hv'⟩ := by
      apply Subtype.ext
      rw [hu', huv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
      group
    rw [hu'eq, map_mul, hΦY, hΦV, mul_one, hu, map_mul, hΦY, hΦV, mul_one]
    exact hequiv ℓ ⟨y, hYU₁ hy⟩ ⟨_, hYU₁ hy'⟩ rfl

theorem chief_card_transfer (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S) {V' U : Subgroup X}
    (hU : IsNoncentralChiefFactor K (pCoreOf 2 K) V' U) :
    Nat.card ↥U * Nat.card ↥U₂ = Nat.card ↥U₁ * Nat.card ↥V' := by
  obtain ⟨-, -, -, hsupV, hsupU, hinf, hcV, hcU⟩ := chief_core h hR sf hE hU
  have h1 := card_sup_mul_card_inf_of_commute hcV
  have h2 := card_sup_mul_card_inf_of_commute hcU
  rw [hsupV, hinf] at h1
  rw [hsupU] at h2
  have hpos : 0 < Nat.card ↥(⁅U, K⁆ ⊓ U₂) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card ↥U * Nat.card ↥U₂ * Nat.card ↥(⁅U, K⁆ ⊓ U₂)
      = (Nat.card ↥U * Nat.card ↥(⁅U, K⁆ ⊓ U₂)) * Nat.card ↥U₂ := by ring
    _ = Nat.card ↥⁅U, K⁆ * Nat.card ↥V' * Nat.card ↥U₂ := by rw [h1]
    _ = (Nat.card ↥⁅U, K⁆ * Nat.card ↥U₂) * Nat.card ↥V' := by ring
    _ = (Nat.card ↥U₁ * Nat.card ↥(⁅U, K⁆ ⊓ U₂)) * Nat.card ↥V' := by rw [h2]
    _ = Nat.card ↥U₁ * Nat.card ↥V' * Nat.card ↥(⁅U, K⁆ ⊓ U₂) := by ring

end Shared

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
