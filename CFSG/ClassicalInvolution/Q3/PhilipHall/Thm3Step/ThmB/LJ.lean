module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WR1Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.Sporadic.Schreier.J4SSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {G : Type} [Group G]

set_option hygiene false in
local notation "𝕌𝕍" => (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G)
set_option hygiene false in
local notation "𝕏𝕏" =>
  ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) : Subgroup G)
set_option hygiene false in
local notation "𝕐𝕐" => (pairNormalizers K J z j)
set_option hygiene false in
local notation "ℤℤ" => (Subgroup.closure ({z, j} : Set G) : Subgroup G)

section Basic

theorem isSylow2In_self' {L : Subgroup G} (hL : IsPGroup 2 ↥L) : IsSylow2In L L :=
  ⟨le_rfl, hL, fun _ hVL _ hLV => le_antisymm hVL hLV⟩

private theorem mem_closure_pair_cases {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hba : b * a = a * b := hab.symm
  have ha' : ∀ w : G, a * (a * w) = w := fun w => by rw [← mul_assoc, ha, one_mul]
  have hb' : ∀ w : G, b * (b * w) = w := fun w => by rw [← mul_assoc, hb, one_mul]
  have hba' : ∀ w : G, b * (a * w) = a * (b * w) := fun w => by
    rw [← mul_assoc, hba, mul_assoc]
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · right; left; exact hx
    · right; right; left; exact Set.mem_singleton_iff.mp hx
  | one => left; rfl
  | mul x y _ _ h1 h2 =>
    rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;> rw [h1, h2] <;>
      simp only [mul_assoc, ha, hb, ha', hb', hba, hba', one_mul, mul_one, true_or, or_true]
  | inv x _ h =>
    rcases h with h | h | h | h <;> rw [h]
    · left; simp
    · right; left; exact inv_eq_of_mul_eq_one_right ha
    · right; right; left; exact inv_eq_of_mul_eq_one_right hb
    · right; right; right
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, hba]

private theorem eq_one_or_eq_of_mem_zpowers {ρ x : G} (hρ : ρ * ρ = 1)
    (hx : x ∈ Subgroup.zpowers ρ) : x = 1 ∨ x = ρ := by
  have hS : Subgroup.zpowers ρ ≤ Subgroup.closure ({ρ, ρ} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  rcases mem_closure_pair_cases hρ hρ rfl (hS hx) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr h
  · exact Or.inl (h.trans hρ)

variable [Finite G]

private theorem sq_eq_of_quat {M : Subgroup G} (hM : Nonempty (↥M ≃* QuaternionGroup 2)) {m x : G}
    (hm : IsUniqueInvolution M m) (hx : x ∈ M) (hx1 : x ≠ 1) (hxm : x ≠ m) : x * x = m := by
  obtain ⟨e⟩ := hM
  have h4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have hx4 : x ^ 4 = 1 := by
    have h := congrArg (fun q => ((e.symm q : M) : G)) (h4 (e ⟨x, hx⟩))
    simp only [map_pow, MulEquiv.symm_apply_apply, map_one] at h
    simpa using h
  have hxx : x * x ≠ 1 := by
    intro h
    rcases hm.unique x hx h with h' | h'
    · exact hx1 h'
    · exact hxm h'
  have hsq : (x * x) * (x * x) = 1 := by
    rw [← hx4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact (hm.unique (x * x) (M.mul_mem hx hx) hsq).resolve_left hxx

theorem mul_self_eq_involution_of_orderOf_four {M : Subgroup G} {m x : G}
    (hm : IsUniqueInvolution M m) (hx : x ∈ M) (h4 : orderOf x = 4) : x * x = m := by
  have hx4 : x ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one x
  have hxx : x * x ≠ 1 := by
    intro h
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [h4] at h2
    norm_num at h2
  have hsq : (x * x) * (x * x) = 1 := by
    rw [← hx4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact (hm.unique (x * x) (M.mul_mem hx hx) hsq).resolve_left hxx

theorem card_of_mem_USet {Ω : Set (Subgroup G)} (hΩ : TypeRHyp Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : Nat.card U = 4 := by
  obtain ⟨R, -, M, hM, hRM, -, -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ.hyp hU
  obtain ⟨e⟩ := hΩ.sylow M hM R hRM
  have h8 : Nat.card R = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  omega

private theorem card_le_two_mul_of_mem_or' {A C : Subgroup G} {a₀ : G}
    (h : ∀ a ∈ A, a ∈ C ∨ a₀⁻¹ * a ∈ C) : Nat.card A ≤ 2 * Nat.card C := by
  classical
  let f : ↥A → Bool × ↥C := fun a =>
    if ha : (a : G) ∈ C then (false, ⟨a, ha⟩) else (true, ⟨a₀⁻¹ * a, (h a a.2).resolve_left ha⟩)
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : (a : G) ∈ C <;> by_cases hb : (b : G) ∈ C <;>
      simp only [f, ha, hb, dite_true, dite_false, Prod.mk.injEq, Subtype.mk.injEq,
        Bool.false_eq_true, Bool.true_eq_false, false_and, true_and] at hab
    · exact Subtype.ext hab
    · exact Subtype.ext (mul_left_cancel hab)
  calc Nat.card A ≤ Nat.card (Bool × ↥C) := Nat.card_le_card_of_injective f hf
    _ = 2 * Nat.card C := by rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
        Fintype.card_bool]

theorem twinSet_conjSub {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G)
    (L : Subgroup G) : twinSet Ω (conjSub g L) = conjSub g '' twinSet Ω L := by
  ext M
  constructor
  · rintro ⟨hM, w, hwL, hwM⟩
    refine ⟨conjSub g⁻¹ M, ⟨hΩ g⁻¹ M hM, g⁻¹ * w * g⁻¹⁻¹, ?_, hwM.conj g⁻¹⟩,
      conjSub_conjSub_inv g M⟩
    have h := hwL.conj g⁻¹
    rwa [conjSub_inv_conjSub] at h
  · rintro ⟨M₀, ⟨hM₀, w, hwL, hwM₀⟩, rfl⟩
    exact ⟨hΩ g M₀ hM₀, g * w * g⁻¹, hwL.conj g, hwM₀.conj g⟩

theorem twinSet_eq_twinSet_of_mem {Ω : Set (Subgroup G)} {B C : Subgroup G}
    (hC : C ∈ twinSet Ω B) : twinSet Ω C = twinSet Ω B := by
  obtain ⟨-, w, hwB, hwC⟩ := hC
  ext M
  constructor
  · rintro ⟨hM, w', hw'C, hw'M⟩
    exact ⟨hM, w, hwB, (hw'C.eq hwC) ▸ hw'M⟩
  · rintro ⟨hM, w', hw'B, hw'M⟩
    exact ⟨hM, w, hwC, (hw'B.eq hwB) ▸ hw'M⟩

theorem aViol_symm' {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {K J : Subgroup G} {zK zJ : G}
    (hK : K ∈ Ω) (hv : AViol Ω K J zK zJ) : AViol Ω J K zJ zK where
  star := Q3.Q3T6.Mu.omegaStarNbr_symm hΩ hK hv.mem hv.star
  not_nbr := fun hn => hv.not_nbr (Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hv.mem hK hn)
  hzK := hv.hzJ
  hzJ := hv.hzK
  no_conj := by
    intro g hg hgJ
    have hg' : g ∈ pairNormalizers K J zK zJ := Sec6Gen.pairNormalizers_comm K J zK zJ ▸ hg
    exact hv.no_conj g⁻¹ ((pairNormalizers K J zK zJ).inv_mem hg')
      (by rw [← hgJ, conjSub_inv_conjSub])

end Basic

structure LJ (Ω : Set (Subgroup G)) (K J K' : Subgroup G) (z j u v : G) : Prop where
  tor : Sec7.Tor98 Ω K J K' z j u v K K' J
  typeR : TypeRHyp Ω
  twoK : IsPGroup 2 K
  twoJ : IsPGroup 2 J
  twoK' : IsPGroup 2 K'
  conj : ∃ y ∈ 𝕐𝕐, conjSub y J = K'
  quot : ∃ φ : ↥𝕐𝕐 →* DihedralGroup 6, Function.Surjective φ ∧ φ.ker = Subgroup.subgroupOf 𝕏𝕏 𝕐𝕐
  vv : v * v ∈ K ⊔ K'

variable [Finite G] {Ω : Set (Subgroup G)}

theorem exists_LJ (hΩ : TypeRHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hA : InA Ω K J) {z j : G} (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j)
    (h2 : ∀ L ∈ Ω, IsPGroup 2 L) : ∃ (K' : Subgroup G) (u v : G), LJ Ω K J K' z j u v := by
  obtain ⟨u, v, R, T, c⟩ := Sec6Gen.exists_cfg64 hΩ.hyp hK hJ hz hj hA.1 hA.2.1
  have hRK : K = R := c.hR.eq_of_le (h2 K hK) le_rfl c.hR.1
  have hTJ : J = T := c.hT.eq_of_le (h2 J hJ) le_rfl c.hT.1
  subst hRK hTJ
  obtain ⟨⟨hXeq, hRTY⟩, ⟨hXY, hYX, hYZ, hφ⟩, ⟨Ks, hKs, htw, hy, hvv, ⟨R₀, hR₀, hR₀N⟩, hall⟩,
    ⟨he1, he2, he3⟩, ⟨hf, -⟩⟩ := Sec6Gen.l6_4ThreeGenAll G Ω hΩ.hyp K hK J hJ hA z j hz hj _ _
      rfl rfl u v c.hU c.hUK c.hV c.hVJ c.hUV K J c.hR c.hT c.huR c.hvT c.hRN c.hTN
  have hKsT : Ks ∈ twinSet Ω K := by
    rw [htw]
    exact Or.inr rfl
  have hKsΩ : Ks ∈ Ω := hKsT.1
  have hKs2 : IsPGroup 2 Ks := h2 Ks hKsΩ
  have hR₀Ks : Ks = R₀ := hR₀.eq_of_le hKs2 le_rfl hR₀.1
  subst hR₀Ks
  have hzKs : IsUniqueInvolution Ks z := by
    obtain ⟨-, z', hz', hKsz'⟩ := hKsT
    rwa [← hz.eq hz'] at hKsz'
  have hzj : z ≠ j := Sec6Gen.ne_of_not_mem_omegaNbr hΩ.hyp hK hJ (Ne.symm hA.1.2.1) hz hj
    hA.2.1 c.hT
  obtain ⟨hKsY, hU', hcent⟩ := hall Ks hR₀ hR₀N
  have hRY : ∀ R₁ : Subgroup G, IsSylow2In R₁ K → Subgroup.zpowers u ≤ R₁ →
      R₁ ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) :
        Set G) → R₁ ≤ pairNormalizers K J z j := by
    intro R₁ hR₁ _ _
    have hKR₁ : K = R₁ := hR₁.eq_of_le (h2 K hK) le_rfl hR₁.1
    subst hKR₁
    exact le_sup_left.trans hRTY
  have tor : Sec7.Tor98 Ω K J Ks z j u v K Ks J :=
    { hΩ := hΩ.hyp, hK := hK, hJ := hJ, hK' := hKsΩ, hz := hz, hj := hj, hzK' := hzKs,
      hne := hKs, htw := htw, hzj := hzj, hU := c.hU, hUK := c.hUK, hV := c.hV, hVJ := c.hVJ,
      hcomm := c.hUV, hR := c.hR, huR := c.huR, hRN := c.hRN, hR' := hR₀, hR'N := hR₀N,
      hT := c.hT, hvT := c.hvT, hTN := c.hTN, hXeq := hXeq, hRY := hRY,
      hTY := le_sup_right.trans hRTY, hXY := hXY, hYX := hYX, hYZ := hYZ,
      hR'Y := fun R₁ hR₁ hR₁N => (hall R₁ hR₁ hR₁N).1, hU' := hU', hcent := hcent,
      he1 := he1, he2 := he2, he3 := he3, hf := hf }
  exact ⟨Ks, u, v, tor, hΩ, h2 K hK, h2 J hJ, hKs2, hy, hφ, hvv⟩

namespace LJ

variable {K J K' : Subgroup G} {z j u v : G} (d : LJ Ω K J K' z j u v)
include d

theorem K_le_Y : K ≤ 𝕐𝕐 := d.tor.R_le_Y

theorem K'_le_Y : K' ≤ 𝕐𝕐 := d.tor.R'_le_Y

theorem J_le_Y : J ≤ 𝕐𝕐 := d.tor.hTY

theorem X_isPGroup : IsPGroup 2 𝕏𝕏 := by
  have hA : IsPGroup 2 ↥(J ⊓ Subgroup.normalizer (K : Set G)) := d.twoJ.to_le inf_le_left
  have hB : IsPGroup 2 ↥(K ⊓ Subgroup.normalizer (J : Set G)) := d.twoK.to_le inf_le_left
  refine IsPGroup.to_sup_of_normal_right' hA hB ?_
  intro a ha
  exact Sec6Gen.mem_normalizer_inf' ha.2
    (Subgroup.le_normalizer (Subgroup.le_normalizer ha.1))

theorem X_eq : 𝕏𝕏 = 𝕌𝕍 := by
  have hO : oddCoreOf 𝕏𝕏 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hx
      (d.X_isPGroup.to_le (Subgroup.zpowers_le.mpr (oddCoreOf_le_self _ hx)))
  have h := d.tor.hXeq
  rw [hO, bot_sup_eq] at h
  exact h

theorem card_U : Nat.card (Subgroup.zpowers u) = 4 := card_of_mem_USet d.typeR d.tor.hU

theorem card_V : Nat.card (Subgroup.zpowers v) = 4 := card_of_mem_USet d.typeR d.tor.hV

theorem u_sq : u * u = z :=
  mul_self_eq_involution_of_orderOf_four d.tor.hz (d.tor.hUK (Subgroup.mem_zpowers u))
    (by rw [← Nat.card_zpowers]; exact d.card_U)

theorem v_sq : v * v = j :=
  mul_self_eq_involution_of_orderOf_four d.tor.hj (d.tor.hVJ (Subgroup.mem_zpowers v))
    (by rw [← Nat.card_zpowers]; exact d.card_V)

theorem j_mem_KK' : j ∈ K ⊔ K' := d.v_sq ▸ d.vv

theorem card_UV : Nat.card 𝕌𝕍 = 16 := by
  have h := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer
    (AscL62.le_normalizer_of_commutes d.tor.hcomm)
  rw [d.tor.U_inf_V, Subgroup.card_bot, mul_one, d.card_U, d.card_V] at h
  exact h

theorem card_Y : Nat.card 𝕐𝕐 = 192 := by
  obtain ⟨φ, hφ, hker⟩ := d.quot
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
    DihedralGroup.nat_card, hker] at h1
  have h2 : Nat.card ↥(Subgroup.subgroupOf 𝕏𝕏 𝕐𝕐) = Nat.card 𝕏𝕏 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.tor.hXY).toEquiv
  rw [h2, d.X_eq, d.card_UV] at h1
  exact h1

theorem Y_le_N_UV : 𝕐𝕐 ≤ Subgroup.normalizer (𝕌𝕍 : Set G) := d.X_eq ▸ d.tor.hYX

theorem Y_le_N_Z : 𝕐𝕐 ≤ Subgroup.normalizer (ℤℤ : Set G) := d.tor.hYZ

theorem commutes_KK' : Commutes K K' := by
  have hN := Sec6Gen.le_normalizer_of_twin d.tor.hΩ d.tor.hK d.tor.hK' d.tor.hne.symm d.tor.hz
    d.tor.hzK'
  exact Sec6Gen.commutes_of_twin_of_isPGroup d.tor.hΩ d.tor.hK d.tor.hK' d.tor.hne.symm d.tor.hz
    d.tor.hzK' le_rfl le_rfl (IsPGroup.to_sup_of_normal_right' d.twoK d.twoK' hN)

theorem exists_rho : ∃ ρ : G, ρ ∈ 𝕐𝕐 ∧ ρ ∈ Subgroup.normalizer (𝕌𝕍 : Set G) ∧ ρ * ρ = 1 ∧
    (∀ x ∈ 𝕌𝕍, ρ * x * ρ⁻¹ = x⁻¹) ∧
    𝕐𝕐 ⊓ Subgroup.centralizer (ℤℤ : Set G) = 𝕌𝕍 ⊔ Subgroup.zpowers ρ := by
  obtain ⟨r, hr, hru⟩ := d.tor.exists_r
  obtain ⟨r', hr', hr'j⟩ := d.tor.exists_r'
  obtain ⟨hinv, hYC⟩ := d.tor.hcent r hr hru r' hr' hr'j
  refine ⟨r * r', Subgroup.mul_mem _ (d.K_le_Y hr) (d.K'_le_Y hr'),
    Subgroup.mul_mem _ (d.tor.hRN hr) (d.tor.hR'N hr'), ?_, hinv, by rw [hYC, d.X_eq]⟩
  have hK8 : Nonempty (↥K ≃* QuaternionGroup 2) :=
    d.typeR.sylow K d.tor.hK K (isSylow2In_self' d.twoK)
  have hK'8 : Nonempty (↥K' ≃* QuaternionGroup 2) :=
    d.typeR.sylow K' d.tor.hK' K' (isSylow2In_self' d.twoK')
  have hr1 : r ≠ 1 := fun h => hru (h ▸ Subgroup.one_mem _)
  have hrz : r ≠ z := fun h => hru (h ▸ d.tor.z_mem_U)
  have hr'1 : r' ≠ 1 := fun h => hr'j (h ▸ Subgroup.one_mem _)
  have hr'z : r' ≠ z := by
    intro h
    apply hr'j
    rw [h, Subgroup.mem_centralizer_singleton_iff]
    exact d.tor.zj_comm
  have hrr := sq_eq_of_quat hK8 d.tor.hz hr hr1 hrz
  have hrr' := sq_eq_of_quat hK'8 d.tor.hzK' hr' hr'1 hr'z
  have hc : r * r' = r' * r := d.commutes_KK' r hr r' hr'
  calc r * r' * (r * r') = (r * r) * (r' * r') := by
        rw [show r * r' * (r * r') = r * (r' * r) * r' by group, ← hc]; group
    _ = 1 := by rw [hrr, hrr', d.tor.hz.sq]

theorem rho_spec : ∃ ρ : G, ρ ∈ 𝕐𝕐 ∧ ρ ∈ Subgroup.normalizer (𝕌𝕍 : Set G) ∧ ρ * ρ = 1 ∧
    (∀ x ∈ 𝕌𝕍, ρ * x * ρ⁻¹ = x⁻¹) ∧ ∀ c : G, c ∈ 𝕐𝕐 →
      c ∈ Subgroup.centralizer (ℤℤ : Set G) → c ∉ 𝕌𝕍 → ∃ x ∈ 𝕌𝕍, c = x * ρ := by
  obtain ⟨ρ, hρY, hρN, hρρ, hρinv, hYC⟩ := d.exists_rho
  refine ⟨ρ, hρY, hρN, hρρ, hρinv, fun c hcY hcZ hc => ?_⟩
  have hc' : c ∈ 𝕌𝕍 ⊔ Subgroup.zpowers ρ := by
    rw [← hYC]
    exact ⟨hcY, hcZ⟩
  obtain ⟨x, hx, b, hb, rfl⟩ :=
    Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer (Subgroup.zpowers_le.mpr hρN) hc'
  rcases eq_one_or_eq_of_mem_zpowers hρρ hb with rfl | rfl
  · exact absurd (by rw [mul_one]; exact hx) hc
  · exact ⟨x, hx, rfl⟩

theorem inv_of_not_mem {c : G} (hcY : c ∈ 𝕐𝕐) (hcZ : c ∈ Subgroup.centralizer (ℤℤ : Set G))
    (hc : c ∉ 𝕌𝕍) : (∀ w ∈ 𝕌𝕍, c * w * c⁻¹ = w⁻¹) ∧ c * c = 1 := by
  obtain ⟨ρ, -, -, hρρ, hρinv, hmul⟩ := d.rho_spec
  obtain ⟨x, hx, rfl⟩ := hmul c hcY hcZ hc
  refine ⟨fun w hw => ?_, ?_⟩
  · have h1 := hρinv w hw
    have h2 : x * w⁻¹ = w⁻¹ * x := d.tor.UV_comm x hx _ (Subgroup.inv_mem _ hw)
    calc x * ρ * w * (x * ρ)⁻¹ = x * (ρ * w * ρ⁻¹) * x⁻¹ := by group
      _ = x * w⁻¹ * x⁻¹ := by rw [h1]
      _ = w⁻¹ := by rw [h2]; group
  · have h1 := hρinv x hx
    calc x * ρ * (x * ρ) = x * (ρ * x * ρ⁻¹) * (ρ * ρ) := by group
      _ = 1 := by rw [h1, hρρ, mul_one, mul_inv_cancel]

theorem conj_of_not_mem {c w : G} (hcY : c ∈ 𝕐𝕐) (hcZ : c ∈ Subgroup.centralizer (ℤℤ : Set G))
    (hc : c ∉ 𝕌𝕍) (hw : w ∈ 𝕌𝕍) : w * c * w⁻¹ = (w * w) * c := by
  have h1 := (d.inv_of_not_mem hcY hcZ hc).1 w⁻¹ (Subgroup.inv_mem _ hw)
  rw [inv_inv] at h1
  calc w * c * w⁻¹ = w * (c * w⁻¹ * c⁻¹) * c := by group
    _ = (w * w) * c := by rw [h1]

theorem inv_mul_mem_of_not_mem {c c' : G} (hcY : c ∈ 𝕐𝕐)
    (hcZ : c ∈ Subgroup.centralizer (ℤℤ : Set G)) (hc : c ∉ 𝕌𝕍) (hc'Y : c' ∈ 𝕐𝕐)
    (hc'Z : c' ∈ Subgroup.centralizer (ℤℤ : Set G)) (hc' : c' ∉ 𝕌𝕍) : c⁻¹ * c' ∈ 𝕌𝕍 := by
  obtain ⟨ρ, -, hρN, -, -, hmul⟩ := d.rho_spec
  obtain ⟨x, hx, rfl⟩ := hmul c hcY hcZ hc
  obtain ⟨x', hx', rfl⟩ := hmul c' hc'Y hc'Z hc'
  have h1 : ρ⁻¹ * (x⁻¹ * x') * ρ⁻¹⁻¹ ∈ 𝕌𝕍 :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hρN) _).mp
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hx')
  have h2 : (x * ρ)⁻¹ * (x' * ρ) = ρ⁻¹ * (x⁻¹ * x') * ρ⁻¹⁻¹ := by group
  rw [h2]
  exact h1

theorem z_ne_one : z ≠ 1 := d.tor.hz.ne_one

theorem j_ne_one : j ≠ 1 := d.tor.hj.ne_one

theorem mem_Z_cases {x : G} (hx : x ∈ ℤℤ) : x = 1 ∨ x = z ∨ x = j ∨ x = z * j :=
  mem_closure_pair_cases d.tor.hz.sq d.tor.hj.sq d.tor.zj_comm hx

theorem zj_mem_Z : z * j ∈ ℤℤ :=
  Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem card_Z : Nat.card ℤℤ = 4 := by
  classical
  have hset : (ℤℤ : Set G) = {1, z, j, z * j} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · exact d.mem_Z_cases
    · rintro (rfl | rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact d.zj_mem_Z
  have hz1 := d.z_ne_one
  have hj1 := d.j_ne_one
  have hzj := d.tor.hzj
  have hzj1 : z * j ≠ 1 := by
    intro h
    apply hzj
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right d.tor.hj.sq]
  have hzjz : z * j ≠ z := fun h => hj1 (by simpa using h)
  have hzjj : z * j ≠ j := fun h => hz1 (by simpa using h)
  show Nat.card ↥(ℤℤ : Set G) = 4
  rw [hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair hzjj.symm]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hzj, hzjz.symm⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz1.symm, hj1.symm, hzj1.symm⟩

theorem card_le_eight {B : Subgroup G} (hBY : B ≤ 𝕐𝕐)
    (hBZ : B ≤ Subgroup.centralizer (ℤℤ : Set G)) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB : ¬ B ≤ 𝕌𝕍) : Nat.card B ≤ 8 := by
  obtain ⟨b₀, hb₀, hb₀X⟩ := Set.not_subset.mp hB
  have hin : ∀ b ∈ B, b ∈ 𝕌𝕍 → b ∈ B ⊓ ℤℤ := by
    intro b hb hbX
    refine ⟨hb, d.tor.mem_Z_of_sq hbX ?_⟩
    have h1 := (d.inv_of_not_mem (hBY hb₀) (hBZ hb₀) hb₀X).1 b hbX
    have h2 : b₀ * b * b₀⁻¹ = b := by rw [hab b₀ hb₀ b hb]; group
    rw [h2] at h1
    calc b * b = b * b⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel b
  have key : ∀ b ∈ B, b ∈ B ⊓ ℤℤ ∨ b₀⁻¹ * b ∈ B ⊓ ℤℤ := by
    intro b hb
    by_cases hbX : b ∈ 𝕌𝕍
    · exact Or.inl (hin b hb hbX)
    · exact Or.inr (hin _ (B.mul_mem (B.inv_mem hb₀) hb)
        (d.inv_mul_mem_of_not_mem (hBY hb₀) (hBZ hb₀) hb₀X (hBY hb) (hBZ hb) hbX))
  have h1 := card_le_two_mul_of_mem_or' key
  have h2 : Nat.card ↥(B ⊓ ℤℤ) ≤ Nat.card ℤℤ := Subgroup.card_le_of_le inf_le_right
  rw [d.card_Z] at h2
  omega

theorem exists_conj_z {l : G} (hl : l = z ∨ l = j ∨ l = z * j) :
    ∃ y ∈ 𝕐𝕐, y * l * y⁻¹ = z := by
  obtain ⟨r, hr, hru⟩ := d.tor.exists_r
  obtain ⟨t, ht, htv⟩ := d.tor.exists_t
  have hrj := d.tor.he1 r hr hru
  have htz := d.tor.he2 t ht htv
  have hrY := d.K_le_Y hr
  have htY := d.J_le_Y ht
  rcases hl with rfl | rfl | rfl
  · exact ⟨1, Subgroup.one_mem _, by group⟩
  · refine ⟨t⁻¹ * r, Subgroup.mul_mem _ (Subgroup.inv_mem _ htY) hrY, ?_⟩
    calc t⁻¹ * r * l * (t⁻¹ * r)⁻¹ = t⁻¹ * (r * l * r⁻¹) * t := by group
      _ = t⁻¹ * (t * z * t⁻¹) * t := by rw [hrj, htz]
      _ = z := by group
  · refine ⟨t⁻¹, Subgroup.inv_mem _ htY, ?_⟩
    calc t⁻¹ * (z * j) * t⁻¹⁻¹ = t⁻¹ * (t * z * t⁻¹) * t := by rw [htz, inv_inv]
      _ = z := by group

theorem K_inf_UV : K ⊓ 𝕌𝕍 = Subgroup.zpowers u := by
  have hle : Subgroup.zpowers u ≤ K ⊓ 𝕌𝕍 := le_inf d.tor.hUK le_sup_left
  have h4 := WR1.card_le_four_of_abelian d.typeR d.tor.hK (inf_le_left : K ⊓ 𝕌𝕍 ≤ K)
    (d.twoK.to_le inf_le_left) (fun a ha b hb => d.tor.UV_comm a ha.2 b hb.2)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [d.card_U]; exact h4)).symm

theorem J_inf_UV : J ⊓ 𝕌𝕍 = Subgroup.zpowers v := by
  have hle : Subgroup.zpowers v ≤ J ⊓ 𝕌𝕍 := le_inf d.tor.hVJ le_sup_right
  have h4 := WR1.card_le_four_of_abelian d.typeR d.tor.hJ (inf_le_left : J ⊓ 𝕌𝕍 ≤ J)
    (d.twoJ.to_le inf_le_left) (fun a ha b hb => d.tor.UV_comm a ha.2 b hb.2)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [d.card_V]; exact h4)).symm

theorem hzK' : IsUniqueInvolution K' z := d.tor.hzK'

theorem twinSet_K' : twinSet Ω K' = {K, K'} := by
  have h : K' ∈ twinSet Ω K := by
    rw [d.tor.htw]
    exact Or.inr rfl
  rw [twinSet_eq_twinSet_of_mem h, d.tor.htw]

theorem twin_J : (∀ L ∈ twinSet Ω J, L ≤ 𝕐𝕐) ∧ ∃ L ∈ twinSet Ω J, z ∈ L ⊔ J := by
  obtain ⟨y, hy, hyJ⟩ := d.conj
  have hJ : J = conjSub y⁻¹ K' := by rw [← hyJ, conjSub_inv_conjSub]
  have htw : twinSet Ω J = conjSub y⁻¹ '' {K, K'} := by
    rw [hJ, twinSet_conjSub d.tor.hΩ.conjInvariant, d.twinSet_K']
  have hyi : y⁻¹ ∈ 𝕐𝕐 := Subgroup.inv_mem _ hy
  have hYY : conjSub y⁻¹ 𝕐𝕐 = 𝕐𝕐 := conjSub_eq_self_of_mem hyi
  refine ⟨fun L hL => ?_, ?_⟩
  · rw [htw] at hL
    obtain ⟨L₀, hL₀, rfl⟩ := hL
    rw [← hYY]
    refine conjSub_mono ?_
    rcases hL₀ with rfl | rfl
    · exact d.K_le_Y
    · exact d.K'_le_Y
  · refine ⟨conjSub y⁻¹ K, by rw [htw]; exact ⟨K, Or.inl rfl, rfl⟩, ?_⟩
    have hZ : ℤℤ ≤ K ⊔ K' := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_sup_left d.tor.hz.mem
      · exact d.j_mem_KK'
    have h1 : y * z * y⁻¹ ∈ K ⊔ K' :=
      hZ ((Subgroup.mem_normalizer_iff.mp (d.Y_le_N_Z hy) z).mp (Subgroup.subset_closure (by simp)))
    have h2 : z ∈ conjSub y⁻¹ (K ⊔ K') := by
      rw [mem_conjSub_iff]
      simpa [mul_assoc] using h1
    rwa [Sec7.conjSub_sup_eq, ← hJ] at h2

end LJ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
