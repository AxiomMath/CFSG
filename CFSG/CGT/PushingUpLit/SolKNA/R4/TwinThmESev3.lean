module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOrb7
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEConfig
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf9Sev3

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

namespace ThmE

section Sev3


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem exists_orderOf_eight_of_quat {P : Subgroup G} (hr : 4 ≤ r)
    (e : ↥P ≃* QuaternionGroup (2 ^ (r - 2))) : ∃ v ∈ P, orderOf v = 8 := by
  have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hN : 2 * 2 ^ (r - 2) = 2 ^ 3 * 2 ^ (r - 4) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have h1 : orderOf (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (r - 2))) = 2 ^ 3 * 2 ^ (r - 4) := by
    rw [QuaternionGroup.orderOf_a_one, hN]
  have h2 : orderOf ((QuaternionGroup.a 1 : QuaternionGroup (2 ^ (r - 2))) ^ 2 ^ (r - 4)) = 8 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [h1]; exact dvd_mul_left _ _), h1]
    rw [Nat.mul_div_cancel _ (by positivity)]
    norm_num
  refine ⟨((e.symm ((QuaternionGroup.a 1 : QuaternionGroup (2 ^ (r - 2))) ^ 2 ^ (r - 4)) : ↥P) : G),
    (e.symm _).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact h2

theorem exists_fixed_or_orderFour_of_orderEight {K₁ R₁ Y : Subgroup G} {t δ v : G}
    (ht : IsUniqueInvolution K₁ t) (hR₁K : R₁ ≤ K₁) (hR₁2 : IsPGroup 2 ↥R₁)
    (hδ : ∀ x ∈ R₁, δ * x * δ⁻¹ ∈ R₁) (hv : v ∈ R₁) (hv8 : orderOf v = 8)
    (hY : ∀ x ∈ R₁, x * (δ * x * δ⁻¹)⁻¹ ∈ Y) :
    (∃ x ∈ R₁, orderOf x = 4 ∧ δ * x * δ⁻¹ = x) ∨ ∃ y ∈ R₁ ⊓ Y, orderOf y = 4 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hfix, hno⟩ := hcon
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht.sq
  obtain ⟨w, hwdef⟩ : ∃ w : G, w = v * (δ * v * δ⁻¹)⁻¹ := ⟨_, rfl⟩
  have hwR : w ∈ R₁ := hwdef ▸ R₁.mul_mem hv (R₁.inv_mem (hδ v hv))
  have hwY : w ∈ Y := hwdef ▸ hY v hv
  have hww : w * w = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR₁2 ⟨w, hwR⟩
    rw [Subgroup.orderOf_mk] at hk
    by_cases hk2 : 2 ≤ k
    · exfalso
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hy : orderOf (w ^ 2 ^ j) = 4 := by
        rw [orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk,
          pow_add, Nat.mul_div_cancel_left _ (by positivity)]
        norm_num
      exact hno _ ⟨R₁.pow_mem hwR _, Y.pow_mem hwY _⟩ hy
    · have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · rw [pow_zero, orderOf_eq_one_iff] at hk
        rw [hk]
        exact one_mul 1
      · rw [pow_one] at hk
        have := pow_orderOf_eq_one w
        rwa [hk, pow_two] at this
  have hu4 : orderOf (v * v) = 4 := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hv8]; norm_num), hv8]
  have hvvR : v * v ∈ R₁ := R₁.mul_mem hv hv
  have hvt : t * v = v * t := ht.commute_of_mem (hR₁K hv)
  refine hfix _ hvvR hu4 ?_
  have hc : (δ * v * δ⁻¹) * (δ * v * δ⁻¹) = v * v := by
    rcases ht.unique w (hR₁K hwR) hww with h1 | h1
    · have : δ * v * δ⁻¹ = v := by
        rw [h1] at hwdef
        exact (mul_inv_eq_one.mp hwdef.symm).symm
      rw [this]
    · have h2 : (δ * v * δ⁻¹)⁻¹ = v⁻¹ * t := by
        rw [h1] at hwdef
        calc (δ * v * δ⁻¹)⁻¹ = v⁻¹ * (v * (δ * v * δ⁻¹)⁻¹) := by group
          _ = v⁻¹ * t := by rw [← hwdef]
      have h3 : δ * v * δ⁻¹ = t * v := by
        calc δ * v * δ⁻¹ = ((δ * v * δ⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
          _ = (v⁻¹ * t)⁻¹ := by rw [h2]
          _ = t * v := by rw [mul_inv_rev, hti, inv_inv]
      rw [h3]
      calc t * v * (t * v) = t * (v * t) * v := by group
        _ = t * (t * v) * v := by rw [hvt]
        _ = (t * t) * (v * v) := by group
        _ = v * v := by rw [ht.sq, one_mul]
  calc δ * (v * v) * δ⁻¹ = (δ * v * δ⁻¹) * (δ * v * δ⁻¹) := by group
    _ = v * v := hc

theorem endgame_one (hΩ : HypOmegaGen Ω)
    {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {S₁ R₁ : Subgroup G}
    (hS₁ : IsPGroup 2 S₁) (hR₁ : IsSylow2In R₁ K₁) (hR₁S : R₁ ≤ S₁)
    (hv8 : ∃ v ∈ R₁, orderOf v = 8) {δ₀ δ₁ : G}
    (hδ₀S : δ₀ ∈ S₁) (hδ₁S : δ₁ ∈ S₁)
    (g₀ : GoodInv H t δ₀) (g₁ : GoodInv H t δ₁) (g₂ : GoodInv H t (δ₀ * δ₁))
    (hc : δ₀ * δ₁ = δ₁ * δ₀) (n₀ : conjSub δ₀ K₁ = K₁) (m₁ : conjSub δ₁ K₁ ≠ K₁) : False := by
  obtain ⟨hK₂Ω, hK₂t⟩ := TwinThmE.twin_conj_gen hΩ hK₁ ht g₁.comm_t
  have hR₁N : conjSub δ₀ R₁ = R₁ := TwinThmE.conjSub_sylow_eq hS₁ hR₁ hR₁S hδ₀S n₀
  set R₂ : Subgroup G := conjSub δ₁ R₁ with hR₂
  have hR₂S : R₂ ≤ S₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact S₁.mul_mem (S₁.mul_mem hδ₁S (hR₁S hx)) (S₁.inv_mem hδ₁S)
  have hR₂K : R₂ ≤ conjSub δ₁ K₁ := conjSub_mono hR₁.1
  have c12 : Commutes R₁ R₂ :=
    hΩ.commutes_of_twin_of_isPGroup hK₁ hK₂Ω (Ne.symm m₁) ht hK₂t hR₁.1 hR₂K
      (hS₁.to_le (sup_le hR₁S hR₂S))
  have hφ : ∀ x ∈ R₁, δ₀ * x * δ₀⁻¹ ∈ R₁ := by
    intro x hx
    have := conj_mem_conjSub (n := δ₀) hx
    rwa [hR₁N] at this
  have key : ∀ x ∈ R₁, δ₁ * (x * (δ₀ * x * δ₀⁻¹)⁻¹) * δ₁⁻¹ ∈ H := by
    intro x hx
    have hx₂ : δ₁ * x * δ₁⁻¹ ∈ R₂ := conj_mem_conjSub hx
    have hy₂ : δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹ ∈ R₂ := conj_mem_conjSub (hφ x hx)
    have hxx₂ : x * (δ₁ * x * δ₁⁻¹) = (δ₁ * x * δ₁⁻¹) * x := c12 x hx _ hx₂
    have hxy₂ : x * (δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹) = (δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹) * x :=
      c12 x hx _ hy₂
    have n₁ : x * (δ₁ * x * δ₁⁻¹) ∈ H :=
      g₁.cent (mul_mem_centralizer_of_swap g₁.sq rfl hxx₂)
    have hswap : (δ₀ * δ₁) * x * (δ₀ * δ₁)⁻¹ = δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹ := by
      rw [hc]
      group
    have n₂ : x * (δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹) ∈ H :=
      g₂.cent (mul_mem_centralizer_of_swap g₂.sq hswap hxy₂)
    set a := δ₁ * x * δ₁⁻¹ with ha
    set b := δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹ with hb
    have e1 : x * a * (x * b)⁻¹ = a * b⁻¹ := by
      have hxi : x * b⁻¹ = b⁻¹ * x := (Commute.inv_right (show Commute x b from hxy₂)).eq
      calc x * a * (x * b)⁻¹ = x * a * b⁻¹ * x⁻¹ := by group
        _ = a * x * b⁻¹ * x⁻¹ := by rw [hxx₂]
        _ = a * (x * b⁻¹) * x⁻¹ := by group
        _ = a * (b⁻¹ * x) * x⁻¹ := by rw [hxi]
        _ = a * b⁻¹ := by group
    have e2 : δ₁ * (x * (δ₀ * x * δ₀⁻¹)⁻¹) * δ₁⁻¹ = a * b⁻¹ := by
      rw [ha, hb]
      group
    rw [e2, ← e1]
    exact H.mul_mem n₁ (H.inv_mem n₂)
  obtain ⟨v, hvR, hv8⟩ := hv8
  rcases exists_fixed_or_orderFour_of_orderEight (Y := conjSub δ₁⁻¹ H) ht hR₁.1 hR₁.2.1 hφ hvR hv8
      (fun x hx => by rw [mem_conjSub_iff, inv_inv]; exact key x hx) with
    ⟨x, hxQ, hx4, hfix⟩ | ⟨y, ⟨hyQ, hyY⟩, hy4⟩
  · apply hbad K₁ hK₁ ht x (hR₁.1 hxQ) hx4
    apply g₀.cent
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  · have hyY' : y ∈ conjSub δ₁⁻¹ H := hyY
    rw [mem_conjSub_iff, inv_inv] at hyY'
    have hmem2 : δ₁ * y * δ₁⁻¹ ∈ conjSub δ₁ K₁ := conj_mem_conjSub (hR₁.1 hyQ)
    have hord' : orderOf (δ₁ * y * δ₁⁻¹) = 4 := by
      rw [orderOf_conj_mul_inv_eq]
      exact hy4
    exact hbad _ hK₂Ω hK₂t _ hmem2 hord' hyY'

theorem endgame_cases (hΩ : HypOmegaGen Ω)
    {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {S₁ R₁ : Subgroup G}
    (hS₁ : IsPGroup 2 S₁) (hR₁ : IsSylow2In R₁ K₁) (hR₁S : R₁ ≤ S₁)
    (hv8 : ∃ v ∈ R₁, orderOf v = 8) {d₁ d₂ : G}
    (hd₁S : d₁ ∈ S₁) (hd₂S : d₂ ∈ S₁)
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) :
    conjSub d₁ K₁ ≠ K₁ ∧ conjSub d₂ K₁ ≠ K₁ ∧ conjSub (d₁ * d₂) K₁ ≠ K₁ := by
  have hbadK : ∀ u ∈ K₁, orderOf u = 4 → u ∉ H := fun u hu hu4 => hbad K₁ hK₁ ht u hu hu4
  have hdd : d₁ * d₂ * d₁ = d₂ := by
    calc d₁ * d₂ * d₁ = d₁ * (d₂ * d₁) := mul_assoc _ _ _
      _ = d₁ * (d₁ * d₂) := by rw [hc]
      _ = d₂ := by rw [← mul_assoc, g₁.sq, one_mul]
  have hdd' : d₁ * (d₁ * d₂) = d₂ := by rw [← mul_assoc, g₁.sq, one_mul]
  have hd₃S : d₁ * d₂ ∈ S₁ := S₁.mul_mem hd₁S hd₂S
  by_cases n₁ : conjSub d₁ K₁ = K₁
  · by_cases n₂ : conjSub d₂ K₁ = K₁
    · exact (TwinThmE.endgame_all hΩ hK₁ ht hbadK g₁ g₂ g₃ hc n₁ n₂).elim
    · exact (endgame_one hΩ hbad hK₁ ht hS₁ hR₁ hR₁S hv8 hd₁S hd₂S g₁ g₂ g₃ hc n₁ n₂).elim
  · by_cases n₂ : conjSub d₂ K₁ = K₁
    · have g₃' : GoodInv H t (d₂ * d₁) := by rw [← hc]; exact g₃
      exact (endgame_one hΩ hbad hK₁ ht hS₁ hR₁ hR₁S hv8 hd₂S hd₁S g₂ g₁ g₃' hc.symm n₂ n₁).elim
    · by_cases n₃ : conjSub (d₁ * d₂) K₁ = K₁
      · have g₂' : GoodInv H t (d₁ * d₂ * d₁) := by rw [hdd]; exact g₂
        exact (endgame_one hΩ hbad hK₁ ht hS₁ hR₁ hR₁S hv8 hd₃S hd₁S g₃ g₁ g₂'
          (by rw [hdd, hdd']) n₃ n₁).elim
      · exact ⟨n₁, n₂, n₃⟩

theorem MinCex.part2 (hr : 4 ≤ r) (h : E18_6 r) (h4 : E18_4C r)
    (c : MinCex r Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) :
    ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := TwinThmEW.etaAbelian_of_gen hΩ
  have hv8 : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → ∃ v ∈ P, orderOf v = 8 := by
    intro M hM P hP
    obtain ⟨e⟩ := TwinDisc.forall_sylow_iso_of_exists (c.stand.quat M hM) P hP
    exact exists_orderOf_eight_of_quat hr e
  obtain ⟨S', W', c', hSylz⟩ := c.exists_config_sylow_centralizer hz
  have hSH : (S' : Subgroup G) ≤ H := c'.sylow_le hA
  have hzW' : z ∈ W' := by
    obtain ⟨z', hz'K, hz'W, -⟩ := c'.exists_z
    rwa [hz'K.eq hz] at hz'W
  intro g hgt
  by_contra hg
  have hz2' : orderOf (g * z * g⁻¹) = 2 := by
    rw [orderOf_conj_mul_inv_eq]
    exact orderOf_eq_two_of_sq hz.ne_one hz.sq
  have hv : IsPGroup 2 (Subgroup.zpowers (g * z * g⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2']; norm_num)
  obtain ⟨h₁, hh₁H, hh₁⟩ := exists_conj_mem_of_sylow_le hSH hgt hv
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = h₁⁻¹ * g := ⟨_, rfl⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t, t = g₁ * z * g₁⁻¹ := ⟨_, rfl⟩
  have ht₀S : t₀ ∈ (S' : Subgroup G) := by
    have : t₀ = h₁⁻¹ * (g * z * g⁻¹) * h₁ := by rw [ht₀, hg₁]; group
    rw [this]
    exact hh₁
  have hg₁H : g₁ ∉ H := by
    intro hh
    apply hg
    have : g = h₁ * g₁ := by rw [hg₁]; group
    rw [this]
    exact H.mul_mem hh₁H hh
  obtain ⟨g₃, hg₃H, ht₃S, hCSyl⟩ := TwinThmEW.exists_good_t hSH hg₁H (ht₀ ▸ ht₀S)
  obtain ⟨t, ht₃⟩ : ∃ t, t = g₃ * z * g₃⁻¹ := ⟨_, rfl⟩
  rw [← ht₃] at ht₃S hCSyl
  obtain ⟨g₂, hg₂H, ht, hCS⟩ := TwinThmE.exists_g_hCS hSylz ht₃ hzH hg₃H
  have hgood : TwinThmEW.GoodFourWD (S' : Subgroup G) H W' t := by
    by_cases hcomm : t * z = z * t
    · exact c'.goodFourD_of_commute hz hzH hg₂H ht ht₃S hcomm
    · exact c'.goodFourD_of_noncommute h h4 hz hzW' hzH hSylz hg₂H ht ht₃S hcomm
  obtain ⟨d₁, d₂, g₁', g₂', g₃', hc, hW₁, hW₂, hshape⟩ := hgood
  have hK₁ : conjSub g₂ K ∈ Ω := hΩ.conjInvariant g₂ K c.stand.mem
  have hK₁t : IsUniqueInvolution (conjSub g₂ K) t := by rw [ht]; exact hz.conj g₂
  have hbad := c'.hbad_of_conj hz hg₂H
  rw [← ht] at hbad
  obtain ⟨hRR, hRK, hRS⟩ := c'.stand.hR
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ c.stand.mem hRR hRK
  have hWS : W' ≤ (S' : Subgroup G) := c'.stand.hW.2.1
  have hdS : ∀ d : G, d ∈ W' → GoodInv H t d → d ∈ conjSub g₂ (S' : Subgroup G) :=
    fun d hd gd => hCS d (hWS hd) gd.comm_t.symm
  obtain ⟨m₁, m₂, m₃⟩ := endgame_cases hΩ hbad hK₁ hK₁t
    (isPGroup_conjSub g₂ S'.isPGroup') (hRsyl.conj g₂) (conjSub_mono hRS)
    (hv8 _ hK₁ _ (hRsyl.conj g₂)) (hdS d₁ hW₁ g₁') (hdS d₂ hW₂ g₂') g₁' g₂' g₃' hc
  exact c'.orbit4_false hz hg₂H ht hCS hCSyl g₁' g₂' g₃' hc hW₁ hW₂ hshape m₁ m₂ m₃

theorem e18_7_of (hr : 4 ≤ r) (h6 : E18_6 r) (h4 : E18_4C r) : E18_7 r := by
  intro G _ _ Ω K S R W H c a ha1 ha2 haH g hgt
  obtain ⟨z, hz, hzW, hzH⟩ := c.exists_z
  exact c.part1 h6 h4 hz hzW (c.part2 hr h6 h4 hz hzH) ha2 ha1 haH hgt

end Sev3

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
