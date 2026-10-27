module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3C4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3HexB
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement


open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Frame

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem KW_inf_JW : (W ⊓ K) ⊓ (W ⊓ J) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨hxW, hxK⟩, -, hxJ⟩ := hx
  rw [Subgroup.mem_bot]
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hxS : x ∈ (S : Subgroup G) := d.hWS hxW
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)
  have hKJ : K ≠ J := fun h => d.viol.ne h.symm
  have hcard := Sec6Gen.card_le_two_of_le_inf d.late_hΩ hKΩ d.viol.mem hKJ hx2
    (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hxJ)
  have hsq : x * x = 1 := mul_self_eq_one_of_card_zpowers_le_two hcard
  by_contra hne
  rcases d.viol.hzK.unique x hxK hsq with h1 | h1
  · exact hne h1
  · rcases d.viol.hzJ.unique x hxJ hsq with h2 | h2
    · exact hne h2
    · exact d.t_ne_z (h2.symm.trans h1)

theorem eq_t_of_invol_mem_V {x : G} (hx : x ∈ V) (hsq : x * x = 1) (hx1 : x ≠ 1) : x = t := by
  obtain ⟨L₀, hL₀, hVL₀⟩ := Sec6Gen.exists_member_of_mem_USet d.late_hΩ d.hV
  obtain ⟨a₀, ha₀⟩ := Sec6Gen.exists_uniqueInvolution d.late_hΩ hL₀
  rcases ha₀.unique x (hVL₀ hx) hsq with h | h
  · exact absurd h hx1
  · rcases ha₀.unique t (hVL₀ d.htV) d.viol.hzJ.sq with h' | h'
    · exact absurd h' d.viol.hzJ.ne_one
    · exact h.trans h'.symm

theorem W_le_V_sup_K (hex : Hex20 (CoreAssembly.conjClass K) K J W) : W ≤ V ⊔ (W ⊓ K) := by
  have hΩ := d.late_hΩ
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hWc := d.late_hWc
  have hJWK : W ⊓ J ≤ Subgroup.normalizer ((W ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_of_commutes fun x hx y hy => hWc x hx.1 y hy.1
  have hcV := Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet hΩ d.hV hKΩ d.hR
  have hcJ := Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet hΩ hex.JW hKΩ d.hR
  have hcard : Nat.card ↥(J ⊓ W) = Nat.card ↥V := by omega
  obtain ⟨-, -, -, -, -, -, hVcyc, -, hV4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ d.hV
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet hΩ d.hV
  obtain ⟨g, hg⟩ := hVcyc.exists_generator
  have hgord : orderOf g = Nat.card V := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, hm⟩ := hV2.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set v₀ : G := (g : G) with hv₀
  have hv₀V : v₀ ∈ V := g.2
  have hv₀ord : orderOf v₀ = 2 ^ m := by rw [hv₀, Subgroup.orderOf_coe, hgord, hm]
  have hv₀W : v₀ ∈ W := d.hVW hv₀V
  have hv₀' : v₀ ∈ (W ⊓ K) ⊔ (W ⊓ J) := hex.hW ▸ hv₀W
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (W ⊓ K) (W ⊓ J) hJWK]
    at hv₀'
  obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := hv₀'
  have hcomm : a₁ * b₁ = b₁ * a₁ := hWc a₁ ha₁.1 b₁ hb₁.1
  have hpow : ∀ n : ℕ, v₀ ^ n = a₁ ^ n * b₁ ^ n := by
    intro n
    rw [← hab]
    exact (Commute.mul_pow (a := a₁) (b := b₁) hcomm) n
  have hpow_mem : ∀ n : ℕ, a₁ ^ n = 1 → b₁ ^ n = 1 → v₀ ^ n = 1 := by
    intro n h1 h2
    rw [hpow, h1, h2, one_mul]
  have hbot := d.KW_inf_JW
  have hb1e : b₁ ^ (2 ^ m) = 1 := by
    have h1 : v₀ ^ (2 ^ m) = 1 := by
      rw [← hv₀ord]
      exact pow_orderOf_eq_one v₀
    rw [hpow] at h1
    have h2 : a₁ ^ (2 ^ m) = (b₁ ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a₁ ^ (2 ^ m) ∈ (W ⊓ K) ⊓ (W ⊓ J) :=
      ⟨(W ⊓ K).pow_mem ha₁ _, by rw [h2]; exact (W ⊓ J).inv_mem ((W ⊓ J).pow_mem hb₁ _)⟩
    rw [hbot, Subgroup.mem_bot] at h3
    rw [h3] at h2
    exact inv_eq_one.mp h2.symm
  have hb1h : ¬ b₁ ^ (2 ^ (m - 1)) = 1 := by
    intro hb
    have hm1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hx : v₀ ^ (2 ^ (m - 1)) = a₁ ^ (2 ^ (m - 1)) := by
      rw [hpow, hb, mul_one]
    have hxV : v₀ ^ (2 ^ (m - 1)) ∈ V := V.pow_mem hv₀V _
    have hsq : v₀ ^ (2 ^ (m - 1)) * v₀ ^ (2 ^ (m - 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← hm1, ← hv₀ord]
      exact pow_orderOf_eq_one v₀
    have hx1 : v₀ ^ (2 ^ (m - 1)) ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hv₀ord] at this
      have h2 := Nat.le_of_dvd (by positivity) this
      have h3 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hxt := d.eq_t_of_invol_mem_V hxV hsq hx1
    have htK : t ∈ K := by
      rw [← hxt, hx]
      exact K.pow_mem ha₁.2 _
    have htsq : t * t = 1 := d.viol.hzJ.sq
    rcases d.viol.hzK.unique t htK htsq with h | h
    · exact d.viol.hzJ.ne_one h
    · exact d.t_ne_z h
  have hb1ord : orderOf b₁ = 2 ^ m := by
    have h := orderOf_eq_prime_pow (p := 2) (n := m - 1) hb1h (by
      rw [show m - 1 + 1 = m by omega]; exact hb1e)
    rwa [show m - 1 + 1 = m by omega] at h
  have hb₁J : Subgroup.zpowers b₁ ≤ J ⊓ W := by
    rw [Subgroup.zpowers_le]
    exact ⟨hb₁.2, hb₁.1⟩
  have hzeq : Subgroup.zpowers b₁ = J ⊓ W := by
    refine Subgroup.eq_of_le_of_card_ge hb₁J ?_
    rw [Nat.card_zpowers, hb1ord, hcard, ← hm]
  intro w hw
  have hw' : w ∈ (W ⊓ K) ⊔ (W ⊓ J) := hex.hW ▸ hw
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (W ⊓ K) (W ⊓ J) hJWK]
    at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := hw'
  have hbz : b ∈ Subgroup.zpowers b₁ := by
    rw [hzeq]
    exact ⟨hb.2, hb.1⟩
  have hb₁V : b₁ ∈ V ⊔ (W ⊓ K) := by
    have : b₁ = a₁⁻¹ * v₀ := by
      rw [← hab]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right ha₁))
      (Subgroup.mem_sup_left hv₀V)
  have hbV : b ∈ V ⊔ (W ⊓ K) := by
    have := (Subgroup.zpowers_le (H := V ⊔ (W ⊓ K))).mpr hb₁V
    exact this hbz
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) hbV

theorem exists_conj_le_S {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUC : U ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c U ≤ (S : Subgroup G) := by
  obtain ⟨V₂, hV₂, hUV₂⟩ := IsSylow2In.exists_ge hU2 hUC
  obtain ⟨x, hx, hxS⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In d.late_isSylow2In_S hV₂
  refine ⟨x⁻¹, (Subgroup.centralizer _).inv_mem hx, ?_⟩
  have := conjSub_mono (n := x⁻¹) hUV₂
  rwa [← hxS, conjSub_inv_conjSub] at this

theorem U_cases {U : Subgroup G} (hU : U ∈ USet (CoreAssembly.conjClass K))
    (hUS : U ≤ (S : Subgroup G)) : U ≤ W ∨ U ≤ K ∨ U ≤ K' := by
  obtain ⟨η, hη, hWη⟩ := d.hW
  have hηW : ∀ V' ∈ η, V' ≤ W := fun V' hV' => by
    rw [hWη]
    exact le_iSup₂ (f := fun U (_ : U ∈ η) => U) V' hV'
  have hηS' : ∀ V' ∈ η, V' ≤ (S : Subgroup G) := fun V' hV' => (hηW V' hV').trans d.hWS
  obtain ⟨V', ⟨hV'η, hcase⟩, -⟩ := Sec6Gen.six_eight d.late_hΩ S hU hUS hη hηS'
  rcases hcase with h | h
  · exact Or.inl (h ▸ hηW V' hV'η)
  · have hle : U ⊔ V' ≤ (S : Subgroup G) := sup_le hUS (hηS' V' hV'η)
    rcases d.hRG _ h hle with h2 | h2
    · exact Or.inr (Or.inl ((le_sup_left.trans h2.le).trans d.hR.1))
    · exact Or.inr (Or.inr ((le_sup_left.trans h2.le).trans d.hR'.1))

end Std20Frame

end Std


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
