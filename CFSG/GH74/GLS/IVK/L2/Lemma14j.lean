module

public import CFSG.GH74.GLS.IVK.L2.Lemma13f
public import CFSG.GH74.GLS.IVK.L2.FixedCentralizer
public import CFSG.GH74.GLS.IVK.L2.Hilbert90
public import CFSG.GH74.GLS.IVK.L2.TwoAdic
public import CFSG.GH74.GLS.IVK.L2.DihedralAux

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section H90

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)

theorem exists_conj_fieldAutHom (x : MulAut K) (hx : x ^ orderOf (fieldProj e x) = 1) :
    ∃ c ∈ innDiagSub e, c⁻¹ * x * c = fieldAutHom e (fieldProj e x) := by
  have hX : (thetaAut e x) ^ orderOf (thetaAut e x).right = 1 := by
    rw [← fieldProj_apply, ← map_pow, hx, map_one]
  obtain ⟨C, hC⟩ := H90.pgammaL2_conj_inr_of_pow_eq_one (thetaAut e x) hX
  refine ⟨innDiagHom e C, ⟨C, rfl⟩, ?_⟩
  apply (thetaAut e).injective
  rw [map_mul, map_mul, map_inv, thetaAut_innDiagHom, thetaAut_fieldAutHom, fieldProj_apply]
  exact hC

end H90

section PFacts

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] {e : K ≃* L2 F}

omit [Finite K] in
theorem centralizer_P_inf_innDiagSub
    (hF : L2Field F) (N : L2Notation e) :
    centralizer (N.P : Set (MulAut K)) ⊓ innDiagSub e = (center ↥N.P).map N.P.subtype := by
  obtain ⟨U, hUle, hU4, -⟩ := N.four_cent
  have hUP : U ≤ N.P := hUle
  have hUinn : U ≤ innAut K := hUle.trans inf_le_right
  have hcU := centralizer_four_inf_innDiagSub e hF U hUinn hU4
  have hPinn : N.P ≤ innAut K := inf_le_right
  ext x
  constructor
  · rintro ⟨hxC, hxD⟩
    have hxU : x ∈ U := by
      rw [← hcU]
      exact ⟨Subgroup.centralizer_le (fun u hu => hUP hu) hxC, hxD⟩
    have hxP : x ∈ N.P := hUP hxU
    refine ⟨⟨x, hxP⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro p
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC p p.2)
  · rintro ⟨c, hc, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, innAut_le_innDiagSub e (hPinn c.2)⟩
    intro p hp
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨p, hp⟩)

theorem center_P_sq_eq_one (hF : L2Field F) (N : L2Notation e) (hR : ∃ f ∈ N.R, orderOf f = 2) :
    ∀ c ∈ center ↥N.P, c * c = 1 := by
  obtain ⟨f, hfR, hf2⟩ := hR
  obtain ⟨n, -, k, hk, hk2, ⟨φP⟩⟩ := ivk_1_2c F hF K e N
  have hcardP : Nat.card N.P = 2 ^ n := by
    rw [Nat.card_congr φP.toEquiv, DihedralGroup.nat_card, ← hk]
  have hRle := (ivk_1_2f F hF K e N).2 n hcardP
  have hR2le : 2 ≤ Nat.card N.R := by
    have h1 : orderOf f ∣ Nat.card ↥N.R := Subgroup.orderOf_dvd_natCard _ hfR
    rw [hf2] at h1
    exact Nat.le_of_dvd Nat.card_pos h1
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have h0 : n - 2 = 0 := by omega
    rw [h0, pow_zero] at hRle
    omega
  have hkeven : Even k := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    refine ⟨2 ^ (j + 1), ?_⟩
    have h8 : (2 : ℕ) ^ (j + 3) = 8 * 2 ^ j := by ring
    have : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
    omega
  have hk4 : k ≠ 2 := by
    intro h2
    subst h2
    have : (2 : ℕ) ^ n = 4 := hk
    have : (2 : ℕ) ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  intro c hc
  by_cases hc1 : c = 1
  · rw [hc1, one_mul]
  · have hφc : φP c ∈ Subgroup.center (DihedralGroup k) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := φP.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc x]
    have h1 : φP c ≠ 1 := fun h => hc1 (φP.injective (by rw [h, map_one]))
    have := DihedralAux.eq_r_half_of_central hkeven hk4 hφc h1
    apply φP.injective
    rw [map_mul, this, DihedralGroup.r_mul_r, map_one, DihedralGroup.one_def]
    congr 1
    obtain ⟨h, hh⟩ := hkeven
    have hdiv : k / 2 = h := by omega
    rw [hdiv, ← Nat.cast_add, ← hh, ZMod.natCast_self]

omit [Finite K] in
include e in
theorem not_card_P_dvd_of_orderOf_four [Finite K] (hF : L2Field F) (N : L2Notation e) (σ : F ≃+* F)
    (hσ : orderOf σ = 4) :
    ¬ Nat.card N.P ∣
      Nat.card ↥(centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e) := by
  rw [card_P_eq e N, card_centralizer_fieldAut e σ]
  have hq : Nat.card (fixedField σ) ^ 4 = Nat.card F := by
    have := fixedField_card_pow σ
    rwa [hσ] at this
  have hq0odd : Odd (Nat.card (fixedField σ)) := odd_card_fixedField σ hF.1
  have h1 := one_lt_card_fixedField σ
  have hK := card_eq_of_L2Field e hF
  rw [← hq] at hK
  exact not_two_pow_dvd_of_pow_four hq0odd h1 hK

theorem orderOf_fieldProj_dvd_two
    (hF : L2Field F) (N : L2Notation e) (x : MulAut K)
    (hxC : x ∈ centralizer (N.P : Set (MulAut K))) {k : ℕ} (hxk : orderOf x = 2 ^ k) :
    orderOf (fieldProj e x) ∣ 2 := by
  have hdvd : orderOf (fieldProj e x) ∣ 2 ^ k := hxk ▸ orderOf_map_dvd (fieldProj e) x
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  by_contra hna
  have ha2 : 2 ≤ a := by
    by_contra h
    apply hna
    have : a = 0 ∨ a = 1 := by omega
    rcases this with rfl | rfl <;> simp [ha]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : MulAut K, y = x ^ (2 ^ b) := ⟨_, rfl⟩
  have hyC : y ∈ centralizer (N.P : Set (MulAut K)) := hy ▸ Subgroup.pow_mem _ hxC _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : F ≃+* F, ψ = fieldProj e y := ⟨_, rfl⟩
  have hψord : orderOf ψ = 4 := by
    rw [hψ, hy, map_pow, orderOf_pow' _ (by positivity), ha,
      Nat.gcd_eq_right (pow_dvd_pow 2 (by omega)), pow_add,
      Nat.mul_div_cancel_left _ (by positivity)]
    norm_num
  obtain ⟨f, hf⟩ : ∃ f : MulAut K, f = fieldAutHom e (ψ ^ 2) := ⟨_, rfl⟩
  have hf2 : orderOf f = 2 := by
    rw [hf, orderOf_injective _ (fieldAutHom_injective e), orderOf_pow' _ (by norm_num), hψord]
    norm_num
  have hfF : f ∈ fieldAutSub e := hf ▸ ⟨_, rfl⟩
  have hfT : f ∈ (N.T : Subgroup (MulAut K)) :=
    fieldAut_two_elt_mem_T N hfF 1 (by simpa using hf2)
  have hfR : f ∈ N.R := ⟨hfT, hfF⟩
  have hRcomm : ∀ p ∈ N.P, p * f = f * p := fun p hp => N.R_cent f hfR hf2 p hp
  have hfC : f ∈ centralizer (N.P : Set (MulAut K)) := Subgroup.mem_centralizer_iff.mpr hRcomm
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : MulAut K, g₁ = y ^ 2 * f⁻¹ := ⟨_, rfl⟩
  have hg₁C : g₁ ∈ centralizer (N.P : Set (MulAut K)) :=
    hg₁ ▸ Subgroup.mul_mem _ (Subgroup.pow_mem _ hyC 2) (Subgroup.inv_mem _ hfC)
  have hg₁D : g₁ ∈ innDiagSub e := by
    rw [mem_innDiagSub_iff, hg₁, map_mul, map_inv, map_pow, ← hψ, hf, fieldProj_fieldAutHom,
      mul_inv_cancel]
  have hg₁Z : g₁ ∈ (center ↥N.P).map N.P.subtype := by
    rw [← centralizer_P_inf_innDiagSub hF N]
    exact ⟨hg₁C, hg₁D⟩
  obtain ⟨c, hc, hcg⟩ := hg₁Z
  have hsq := center_P_sq_eq_one hF N ⟨f, hfR, hf2⟩ c hc
  have hg₁sq : g₁ * g₁ = 1 := by
    have := congrArg N.P.subtype hsq
    rw [map_mul, map_one] at this
    rw [← hcg]
    exact this
  have hg₁P : g₁ ∈ N.P := hcg ▸ c.2
  have hcomm1 : g₁ * f = f * g₁ := hRcomm g₁ hg₁P
  have hff : f * f = 1 := by
    rw [← pow_two, ← hf2]
    exact pow_orderOf_eq_one f
  have hy2 : y ^ 2 = g₁ * f := by rw [hg₁]; group
  have hy4 : y ^ 4 = 1 := by
    have h4 : y ^ 4 = (y ^ 2) ^ 2 := by rw [← pow_mul]
    rw [h4, hy2, pow_two]
    calc (g₁ * f) * (g₁ * f) = g₁ * (f * g₁) * f := by group
      _ = g₁ * (g₁ * f) * f := by rw [← hcomm1]
      _ = (g₁ * g₁) * (f * f) := by group
      _ = 1 := by rw [hg₁sq, hff, one_mul]
  obtain ⟨c', hc', hconj⟩ := exists_conj_fieldAutHom e y (by rw [← hψ, hψord]; exact hy4)
  rw [← hψ] at hconj
  have hPinn : N.P ≤ innAut K := inf_le_right
  have hP'le : N.P.map (MulAut.conj c'⁻¹).toMonoidHom ≤
      centralizer ({fieldAutHom e ψ} : Set (MulAut K)) ⊓ innDiagSub e := by
    rintro _ ⟨p, hp, rfl⟩
    have hcp : (MulAut.conj c'⁻¹) p = c'⁻¹ * p * c' := by simp
    simp only [MulEquiv.coe_toMonoidHom, hcp]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · rw [← hconj]
      have hpy : p * y = y * p := Subgroup.mem_centralizer_iff.mp hyC p hp
      calc c'⁻¹ * p * c' * (c'⁻¹ * y * c') = c'⁻¹ * (p * y) * c' := by group
        _ = c'⁻¹ * (y * p) * c' := by rw [hpy]
        _ = c'⁻¹ * y * c' * (c'⁻¹ * p * c') := by group
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc')
        (innAut_le_innDiagSub e (hPinn hp))) hc'
  have hcardP' : Nat.card (N.P.map (MulAut.conj c'⁻¹).toMonoidHom) = Nat.card N.P :=
    Subgroup.card_map_of_injective (MulAut.conj c'⁻¹).injective
  apply not_card_P_dvd_of_orderOf_four hF N ψ hψord
  rw [← hcardP']
  exact Subgroup.card_dvd_of_le hP'le

theorem two_elt_mem
    (hF : L2Field F) (N : L2Notation e) (x : MulAut K)
    (hxC : x ∈ centralizer (N.P : Set (MulAut K))) {k : ℕ} (hxk : orderOf x = 2 ^ k) :
    ∃ g ∈ (center ↥N.P).map N.P.subtype,
      ∃ φ ∈ fieldAutSub e ⊓ centralizer (N.P : Set (MulAut K)), x = g * φ := by
  have hdvd := orderOf_fieldProj_dvd_two hF N x hxC hxk
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · have hx1 : fieldProj e x = 1 := orderOf_eq_one_iff.mp h1
    refine ⟨x, ?_, 1, one_mem _, by simp⟩
    rw [← centralizer_P_inf_innDiagSub hF N]
    exact ⟨hxC, (mem_innDiagSub_iff e x).mpr hx1⟩
  · obtain ⟨φ, hφ⟩ : ∃ φ : MulAut K, φ = fieldAutHom e (fieldProj e x) := ⟨_, rfl⟩
    have hφo : orderOf φ = 2 := by
      rw [hφ, orderOf_injective _ (fieldAutHom_injective e), h2]
    have hφF : φ ∈ fieldAutSub e := hφ ▸ ⟨_, rfl⟩
    have hφT : φ ∈ (N.T : Subgroup (MulAut K)) :=
      fieldAut_two_elt_mem_T N hφF 1 (by simpa using hφo)
    have hφC : φ ∈ centralizer (N.P : Set (MulAut K)) :=
      Subgroup.mem_centralizer_iff.mpr (fun p hp => N.R_cent φ ⟨hφT, hφF⟩ hφo p hp)
    refine ⟨x * φ⁻¹, ?_, φ, ⟨hφF, hφC⟩, by group⟩
    rw [← centralizer_P_inf_innDiagSub hF N]
    refine ⟨Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ hφC), (mem_innDiagSub_iff e _).mpr ?_⟩
    rw [map_mul, map_inv, hφ, fieldProj_fieldAutHom, mul_inv_cancel]

theorem odd_elt_mem
    (hF : L2Field F) (N : L2Notation e) (x : MulAut K)
    (hxC : x ∈ centralizer (N.P : Set (MulAut K))) (hodd : Odd (orderOf x)) :
    x ∈ fieldAutSub e ⊓ centralizer (N.P : Set (MulAut K)) := by
  have hPT : N.P ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut K, φ = fieldAutHom e (fieldProj e x) := ⟨_, rfl⟩
  have hφF : φ ∈ fieldAutSub e := hφ ▸ ⟨_, rfl⟩
  have hφo : Odd (orderOf φ) := by
    rw [hφ, orderOf_injective _ (fieldAutHom_injective e)]
    exact hodd.of_dvd_nat (orderOf_map_dvd (fieldProj e) x)
  have hφcomm : ∀ p ∈ (N.T : Subgroup (MulAut K)), p * φ = φ * p :=
    fun p hp => N.F_odd_cent φ hφF hφo p hp
  have hφC : φ ∈ centralizer (N.P : Set (MulAut K)) :=
    Subgroup.mem_centralizer_iff.mpr (fun p hp => hφcomm p (hPT hp))
  obtain ⟨g, hg⟩ : ∃ g : MulAut K, g = x * φ⁻¹ := ⟨_, rfl⟩
  have hgC : g ∈ centralizer (N.P : Set (MulAut K)) :=
    hg ▸ Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ hφC)
  have hgD : g ∈ innDiagSub e := by
    rw [mem_innDiagSub_iff, hg, map_mul, map_inv, hφ, fieldProj_fieldAutHom, mul_inv_cancel]
  have hgZ : g ∈ (center ↥N.P).map N.P.subtype := by
    rw [← centralizer_P_inf_innDiagSub hF N]
    exact ⟨hgC, hgD⟩
  obtain ⟨c, -, hcg⟩ := hgZ
  have hgP : g ∈ N.P := hcg ▸ c.2
  have hgcomm : g * φ = φ * g := hφcomm g (hPT hgP)
  have hxφ : x = g * φ := by rw [hg]; group
  have hxφcomm : Commute x φ := by
    rw [hxφ]
    exact (show Commute g φ from hgcomm).mul_left (Commute.refl φ)
  have hgodd : Odd (orderOf g) := by
    have hc : Commute x φ⁻¹ := hxφcomm.inv_right
    have h1 := hc.orderOf_mul_dvd_lcm
    rw [← hg, orderOf_inv] at h1
    exact (hodd.mul hφo).of_dvd_nat (h1.trans (Nat.lcm_dvd_mul _ _))
  have hg1 : g = 1 := by
    obtain ⟨v, hv⟩ : ∃ v, Nat.card N.P = 2 ^ v := ⟨_, card_P_eq e N⟩
    have hdvd : orderOf g ∣ 2 ^ v := hv ▸ Subgroup.orderOf_dvd_natCard N.P hgP
    have hcop : Nat.Coprime (orderOf g) (2 ^ v) :=
      (Nat.coprime_two_right.mpr hgodd).pow_right v
    exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd)
  rw [hg1, one_mul] at hxφ
  rw [hxφ]
  exact ⟨hφF, hφC⟩

omit [Finite K] in
theorem oPrimeResidual_normal : (oPrimeResidual 2 (MulAut K)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    apply Subgroup.subset_closure
    exact ⟨k, by rw [conj_pow, hk]; group⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem oPrimeResidual_sup_E (hF : L2Field F) (N : L2Notation e) :
    oPrimeResidual 2 (MulAut K) ⊔ (fieldAutSub e ⊓ centralizer (N.P : Set (MulAut K))) = ⊤ := by
  have hPT : N.P ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  have hPinn : N.P ≤ innAut K := inf_le_right
  have hQnorm := oPrimeResidual_normal (K := K)
  set Q := oPrimeResidual 2 (MulAut K) with hQ
  have hmemQ : ∀ x : MulAut K, (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ Q :=
    fun x hx => Subgroup.subset_closure hx
  have hTQ : (N.T : Subgroup (MulAut K)) ≤ Q := by
    intro x hx
    obtain ⟨k, hk⟩ := N.T.isPGroup' (⟨x, hx⟩ : ↥(N.T : Subgroup (MulAut K)))
    exact hmemQ x ⟨k, congrArg Subtype.val hk⟩
  have hsimple : IsSimpleGroup ↥(innAut K) := by
    have : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by have := hF.2; omega)
    exact (innAutEquiv e).isSimpleGroup
  have hPne : N.P ≠ ⊥ := by
    obtain ⟨U, hUle, hU4, -⟩ := N.four_cent
    intro hbot
    have hU : U ≤ ⊥ := hbot ▸ hUle
    have h1 : Nat.card U = 1 := by
      rw [Subgroup.card_eq_one]
      exact le_bot_iff.mp hU
    have := hU4.2
    omega
  have hinnQ : innAut K ≤ Q := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Q.subgroupOf (innAut K)) with hbot | htop
    · exfalso
      apply hPne
      rw [eq_bot_iff]
      intro p hp
      have : (⟨p, hPinn hp⟩ : ↥(innAut K)) ∈ Q.subgroupOf (innAut K) := hTQ (hPT hp)
      rw [hbot] at this
      have := Subgroup.mem_bot.mp this
      exact Subtype.ext_iff.mp this |> fun h => by simpa using h
    · intro y hy
      have : (⟨y, hy⟩ : ↥(innAut K)) ∈ Q.subgroupOf (innAut K) := by rw [htop]; trivial
      exact this
  have hdiagQ : innDiagSub e ≤ Q := by
    rw [← (ivk_1_2d F hF K e N).1]
    exact sup_le hinnQ (Subgroup.zpowers_le.mpr (hTQ N.t_mem))
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, hg, hxg⟩ := fieldAutHom_fieldProj_mul e x
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut K, φ = fieldAutHom e (fieldProj e x) := ⟨_, rfl⟩
  have hφF : φ ∈ fieldAutSub e := hφ ▸ ⟨_, rfl⟩
  rw [← hφ] at hxg
  obtain ⟨a, b, ha, hb, hab, ⟨k, hk⟩, hbodd⟩ :=
    exists_two_part φ (isOfFinOrder_of_finite φ)
  have haF : a ∈ fieldAutSub e := Subgroup.zpowers_le.mpr hφF ha
  have hbF : b ∈ fieldAutSub e := Subgroup.zpowers_le.mpr hφF hb
  have haQ : a ∈ Q := hmemQ a ⟨k, by rw [← hk]; exact pow_orderOf_eq_one a⟩
  have hbE : b ∈ fieldAutSub e ⊓ centralizer (N.P : Set (MulAut K)) :=
    ⟨hbF, Subgroup.mem_centralizer_iff.mpr (fun p hp =>
      N.F_odd_cent b hbF hbodd p (hPT hp))⟩
  rw [hxg, hab, ← mul_assoc]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem _ (hdiagQ hg) haQ) hbE

theorem ivk_1_4j : IVK_1_4j := by
  intro F _ _ hF K _ _ e N
  set E : Subgroup (MulAut K) := fieldAutSub e ⊓ centralizer (N.P : Set (MulAut K)) with hE
  have hEF : E ≤ fieldAutSub e := inf_le_left
  have hEcyc : IsCyclic ↥E := by
    have h1 : IsCyclic ↥(fieldAutSub e) := isCyclic_fieldAutSub e
    have h2 : IsCyclic ↥(E.subgroupOf (fieldAutSub e)) := Subgroup.isCyclic _
    exact (Subgroup.subgroupOfEquivOfLe hEF).isCyclic.mp h2
  refine ⟨E, hEcyc, hEF, ?_, ?_, ?_, oPrimeResidual_sup_E hF N⟩
  · have hpos : Nat.card E ≠ 0 := Nat.card_pos.ne'
    obtain ⟨j, m, hm, hjm⟩ := Nat.exists_eq_two_pow_mul_odd hpos
    have hj : j ≤ 1 := by
      by_contra hj2
      push Not at hj2
      have h4 : 4 ∣ Nat.card E := by
        rw [hjm]
        refine Dvd.dvd.mul_right ?_ m
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this]
        exact pow_dvd_pow 2 hj2
      obtain ⟨δ, hδ⟩ := exists_orderOf_four_of_cyclic h4
      have hδC : (δ : MulAut K) ∈ centralizer (N.P : Set (MulAut K)) := δ.2.2
      have hδ4 : orderOf (δ : MulAut K) = 2 ^ 2 := by
        rw [Subgroup.orderOf_coe, hδ]; norm_num
      have hdvd := orderOf_fieldProj_dvd_two hF N (δ : MulAut K) hδC hδ4
      obtain ⟨ψ, hψ⟩ : (δ : MulAut K) ∈ fieldAutSub e := δ.2.1
      have hord : orderOf (fieldProj e (δ : MulAut K)) = 4 := by
        rw [← hψ, fieldProj_fieldAutHom,
          ← orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) ψ, hψ, hδ4]
        norm_num
      rw [hord] at hdvd
      exact absurd hdvd (by norm_num)
    refine ⟨m, hm, ?_⟩
    interval_cases j
    · left; simpa using hjm
    · right; rw [hjm]; ring
  · apply le_antisymm
    · intro x hx
      obtain ⟨a, b, ha, hb, hab, ⟨k, hk⟩, hbodd⟩ :=
        exists_two_part x (isOfFinOrder_of_finite x)
      have haC : a ∈ centralizer (N.P : Set (MulAut K)) :=
        Subgroup.zpowers_le.mpr hx ha
      have hbC : b ∈ centralizer (N.P : Set (MulAut K)) :=
        Subgroup.zpowers_le.mpr hx hb
      obtain ⟨g, hg, φ, hφ, rfl⟩ := two_elt_mem hF N a haC hk
      have hbE := odd_elt_mem hF N b hbC hbodd
      rw [hab]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right hφ)) (Subgroup.mem_sup_right hbE)
    · apply sup_le
      · rintro _ ⟨c, hc, rfl⟩
        refine Subgroup.mem_centralizer_iff.mpr (fun p hp => ?_)
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨p, hp⟩)
      · exact inf_le_right
  · rw [eq_bot_iff]
    rintro x ⟨⟨c, -, rfl⟩, hxE⟩
    have h1 : N.P.subtype c ∈ innDiagSub e :=
      innAut_le_innDiagSub e ((inf_le_right : N.P ≤ innAut K) c.2)
    have : N.P.subtype c ∈ innDiagSub e ⊓ fieldAutSub e := ⟨h1, hxE.1⟩
    rw [innDiagSub_inf_fieldAutSub e] at this
    exact this

end PFacts

end CFSG.GH74.GLS.IVK
