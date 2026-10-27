module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisBase
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsShape
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHilbert90

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem nm_one_false (σ : F ≃+* F) : nm F 1 false σ = SemidirectProduct.inr σ :=
  SemidirectProduct.ext (by simp) rfl

omit [Finite F] in
theorem right_pow (x : PGammaL2 F) (n : ℕ) : (x ^ n).right = x.right ^ n :=
  map_pow SemidirectProduct.rightHom x n

omit [Finite F] in
theorem twist_not (ε : Bool) (y : Fˣ) : twist F (!ε) y = (twist F ε y)⁻¹ := by
  cases ε <;> simp

omit [Finite F] in
theorem nm_false_zpow' (x : Fˣ) (j : ℤ) : nm F (x ^ j) false 1 = nm F x false 1 ^ j := by
  rw [← inl_tor, ← inl_tor, map_zpow, map_zpow]

variable (F) in
abbrev rStd : Subgroup (PGammaL2 F) := (stdT F).map (incl F)

theorem nm_mem_rStd (hsq : IsSquare (-1 : F)) {c : Fˣ} (hc : c ∈ zpowers (stdGen F ^ 2))
    (ε : Bool) : nm F c ε 1 ∈ rStd F :=
  (mem_map_stdT_iff hsq _).mpr ⟨c, hc, ε, rfl⟩

theorem rStd_le_pslRange : rStd F ≤ pGammaL2PSLRange F := by
  rintro _ ⟨t, -, rfl⟩
  exact ⟨t, rfl⟩

theorem HarrisHyp.c₀_ne_inv (hH : HarrisHyp F) : stdGen F ^ 2 ≠ (stdGen F ^ 2)⁻¹ := by
  intro h
  have h1 : (stdGen F ^ 2) ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 2 [h]
    exact mul_inv_cancel _
  have := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_stdGen_sq hH.odd] at this
  have h4 := hH.four_le
  have := Nat.le_of_dvd (by norm_num) this
  have : 2 ^ 2 ≤ 2 ^ (twoVal F - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem HarrisHyp.neg_one_mem (hH : HarrisHyp F) : (-1 : Fˣ) ∈ zpowers (stdGen F ^ 2) := by
  apply (pow_half_eq_one_iff hH.odd).mp
  apply Even.neg_one_pow
  have h4 := hH.four_le
  exact (Nat.even_pow' (by omega)).mpr even_two

theorem HarrisHyp.zStd_ne_one (hH : HarrisHyp F) : nm F (-1) false 1 ≠ 1 := by
  intro h
  rw [← nm_one, nm_eq_nm_iff] at h
  exact hH.neg_one_ne_one h.1

theorem HarrisHyp.zStd_mem_rStd (hH : HarrisHyp F) : nm F (-1) false 1 ∈ rStd F :=
  nm_mem_rStd hH.sq hH.neg_one_mem false

theorem HarrisHyp.le_sylS0 (hH : HarrisHyp F) {Q : Subgroup (PGammaL2 F)} (hQ : IsPGroup 2 Q)
    (hRQ : rStd F ≤ Q) : Q ≤ sylS0 F := by
  intro x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₀ := stdSylow F hH.odd hH.sq hH.q4
  have hS₀ : (S₀ : Subgroup (PSL2 F)) = stdT F := coe_stdSylow hH.odd hH.sq hH.q4
  have hnorm := conj_mem_of_mem S₀ Q hQ (by rw [hS₀]; exact hRQ) hx
  rw [hS₀] at hnorm
  obtain ⟨b, ε, hxb⟩ := exists_nm_of_normalizes_stdT hH.odd hH.sq
    (by have := hH.four_le; omega) x hnorm
  have hσ : x.right ∈ galTwo F := by
    obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have h1 : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [← right_pow, h1]
    rfl
  have h1 := hnorm _ (nm_mem_rStd hH.sq (one_mem _) true)
  rw [hxb, nm_conj_refl, map_one, twist_one, mul_one] at h1
  obtain ⟨y, hy, ε', hyeq⟩ := (mem_map_stdT_iff hH.sq _).mp h1
  have hbb : b * b = y := (nm_injective hyeq).1
  have hb : b ∈ zpowers (stdGen F) := by
    apply mem_zpowers_of_orderOf_dvd
    rw [orderOf_stdGen]
    apply orderOf_dvd_of_pow_eq_one
    have := (pow_half_eq_one_iff hH.odd).mpr (hbb ▸ hy)
    rw [← pow_two, ← pow_mul, ← pow_succ', Nat.sub_add_cancel (one_le_twoVal hH.odd)] at this
    exact this
  rw [hxb]
  exact nm_mem_sylS0 hb ε hσ

section Overgroup

variable (F) in
abbrev stdTS (K : Subgroup (PGammaL2 F)) : Subgroup (PGammaL2 F) := sylS0 F ⊓ K

variable {K : Subgroup (PGammaL2 F)}

theorem HarrisHyp.rStd_le_stdTS (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    rStd F ≤ stdTS F K :=
  le_inf (map_stdT_le_sylS0 hH.sq) (rStd_le_pslRange.trans hK)

theorem HarrisHyp.isSylowIn_stdTS (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    IsSylowIn (stdTS F K) K :=
  ⟨inf_le_right, isPGroup_sylS0.to_le inf_le_left, fun _ hQK hQ hTQ =>
    le_antisymm (le_inf (hH.le_sylS0 hQ ((hH.rStd_le_stdTS hK).trans hTQ)) hQK) hTQ⟩

theorem HarrisHyp.stdTS_inf (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    stdTS F K ⊓ pGammaL2PSLRange F = rStd F := by
  have h := inf_pslRange_eq (stdSylow F hH.odd hH.sq hH.q4) (stdTS F K)
    (isPGroup_sylS0.to_le inf_le_left) (by rw [coe_stdSylow]; exact hH.rStd_le_stdTS hK)
  rwa [coe_stdSylow] at h

theorem HarrisHyp.nm_mem_iff (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) {c : Fˣ}
    (hc : c ∈ zpowers (stdGen F ^ 2)) (ε : Bool) (σ : F ≃+* F) :
    nm F c ε σ ∈ K ↔ SemidirectProduct.inr σ ∈ K := by
  have h1 : nm F c ε 1 ∈ K := hK (rStd_le_pslRange (nm_mem_rStd hH.sq hc ε))
  have h2 : nm F c ε σ = nm F c ε 1 * SemidirectProduct.inr σ := by
    rw [← nm_one_false, nm_mul]
    simp [fu_one]
  rw [h2]
  constructor
  · intro h
    have := K.mul_mem (K.inv_mem h1) h
    rwa [inv_mul_cancel_left] at this
  · intro h
    exact K.mul_mem h1 h

variable (F) in
abbrev gam0 (K : Subgroup (PGammaL2 F)) : Subgroup (F ≃+* F) :=
  galTwo F ⊓ K.comap SemidirectProduct.inr

theorem exists_zpowers_eq_gam0 (K : Subgroup (PGammaL2 F)) :
    ∃ φ : F ≃+* F, zpowers φ = gam0 F K := by
  have := isCyclic_ringAut F
  exact (Subgroup.isCyclic_iff_exists_zpowers_eq_top (gam0 F K)).mp inferInstance

variable (F) in
@[expose] def phiGam (K : Subgroup (PGammaL2 F)) : F ≃+* F :=
  (exists_zpowers_eq_gam0 (F := F) K).choose

theorem zpowers_phiGam (K : Subgroup (PGammaL2 F)) : zpowers (phiGam F K) = gam0 F K :=
  (exists_zpowers_eq_gam0 K).choose_spec

theorem phiGam_mem (K : Subgroup (PGammaL2 F)) : phiGam F K ∈ gam0 F K := by
  rw [← zpowers_phiGam]
  exact mem_zpowers _

theorem HarrisHyp.psiF_mem_gam0 (hH : HarrisHyp F)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) : psiF F ∈ gam0 F K :=
  ⟨hH.psiF_mem_galTwo, hψK⟩

theorem HarrisHyp.phiGam_ne_one (hH : HarrisHyp F) (hψK : SemidirectProduct.inr (psiF F) ∈ K) :
    phiGam F K ≠ 1 := by
  intro h
  have := hH.psiF_mem_gam0 hψK
  rw [← zpowers_phiGam, h, zpowers_one_eq_bot, mem_bot] at this
  exact hH.psiF_ne_one this

theorem orderOf_eq_two_pow_of_mem_galTwo {σ : F ≃+* F} (hσ : σ ∈ galTwo F) :
    ∃ i : ℕ, orderOf σ = 2 ^ i := by
  obtain ⟨k, hk⟩ := hσ
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  exact ⟨i, hi⟩

theorem HarrisHyp.phiGam_pow_half (hH : HarrisHyp F)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) :
    phiGam F K ^ (orderOf (phiGam F K) / 2) = psiF F := by
  obtain ⟨i, hi⟩ := orderOf_eq_two_pow_of_mem_galTwo (phiGam_mem K).1
  have hi1 : 1 ≤ i := by
    by_contra h
    apply hH.phiGam_ne_one hψK
    rw [← orderOf_eq_one_iff, hi, show i = 0 by omega, pow_zero]
  have h2 : 2 ∣ 2 ^ i := dvd_pow_self 2 (by omega)
  have hdvd : 2 ^ i / 2 ∣ 2 ^ i := Nat.div_dvd_of_dvd h2
  have hne : 2 ^ i / 2 ≠ 0 := by
    have : 2 ≤ 2 ^ i := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi1
    omega
  apply hH.eq_psiF_of_orderOf
  rw [orderOf_pow_of_dvd (by rw [hi]; exact hne) (by rw [hi]; exact hdvd), hi,
    Nat.div_div_self h2 (by positivity)]

theorem HarrisHyp.mul_self_of_epsR (hH : HarrisHyp F) (hε : epsR F = true) {σ : F ≃+* F}
    (hσ : σ ∈ galTwo F) : σ * σ = 1 := by
  obtain ⟨p, f, hp, hp2, hF, -⟩ := hH.char
  by_contra hne
  obtain ⟨i, hσi⟩ := orderOf_eq_two_pow_of_mem_galTwo hσ
  have hi2 : 2 ≤ i := by
    by_contra h
    apply hne
    rw [← pow_two]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hσi]
    exact (Nat.pow_dvd_pow 2 (by omega : i ≤ 1)).trans (by norm_num)
  set τ := σ ^ 2 ^ (i - 2)
  have hτ : orderOf τ = 2 ^ 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hσi]; exact Nat.pow_dvd_pow 2 (by omega)),
      hσi, Nat.pow_div (by omega) (by norm_num)]
    congr 1
    omega
  obtain ⟨t, u, ht, -, -, hτx⟩ := exists_odd_pow_of_orderOf_two_pow hp hp2 hF τ (by norm_num) hτ
  have hττ : τ * τ = psiF F := by
    apply hH.eq_psiF_of_orderOf
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hτ]; norm_num), hτ]
    norm_num
  set s := t ^ u
  have hs : Odd s := ht.pow
  have hfuτ : ∀ c : Fˣ, fu F τ c = c ^ s := fun c => by
    ext
    simp [hτx, s]
  have hinv : fu F (psiF F) (stdGen F ^ 2) = (stdGen F ^ 2)⁻¹ := by
    have := hH.twist_epsR_sq
    rw [hε, twist_true] at this
    exact inv_eq_iff_eq_inv.mp this
  rw [← hττ, fu_mul, hfuτ, hfuτ, ← pow_mul] at hinv
  have h1 : (stdGen F ^ 2) ^ (s * s + 1) = 1 := by rw [pow_succ, hinv, inv_mul_cancel]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_stdGen_sq hH.odd] at h2
  have h8 : 2 ^ 3 ∣ s * s + 1 :=
    (Nat.pow_dvd_pow 2 (by have := hH.four_le; omega : 3 ≤ twoVal F - 1)).trans h2
  obtain ⟨m, hm⟩ := hs
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self m
  have e : s * s + 1 = 4 * (m * (m + 1)) + 2 := by rw [hm]; ring
  rw [e, hj] at h8
  norm_num at h8
  omega

theorem HarrisHyp.phiGam_eq_psiF (hH : HarrisHyp F) (hψK : SemidirectProduct.inr (psiF F) ∈ K)
    (hε : epsR F = true) : phiGam F K = psiF F :=
  hH.eq_psiF (hH.phiGam_ne_one hψK) (hH.mul_self_of_epsR hε (phiGam_mem K).1)

variable (F) in
abbrev vStd (K : Subgroup (PGammaL2 F)) : PGammaL2 F := nm F 1 (epsR F) (phiGam F K)

variable (F) in
abbrev v0Std : PGammaL2 F := nm F 1 (epsR F) (psiF F)

theorem HarrisHyp.vStd_mem (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    vStd F K ∈ stdTS F K :=
  ⟨nm_mem_sylS0 (one_mem _) _ (phiGam_mem K).1,
    (hH.nm_mem_iff hK (one_mem _) _ _).mpr (phiGam_mem K).2⟩

theorem HarrisHyp.v0Std_mem (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) : v0Std F ∈ stdTS F K :=
  ⟨nm_mem_sylS0 (one_mem _) _ hH.psiF_mem_galTwo, (hH.nm_mem_iff hK (one_mem _) _ _).mpr hψK⟩

theorem vStd_pow (K : Subgroup (PGammaL2 F)) (j : ℕ) :
    ∃ ε' : Bool, vStd F K ^ j = nm F 1 ε' (phiGam F K ^ j) := by
  induction j with
  | zero => exact ⟨false, by rw [pow_zero, pow_zero, nm_one]⟩
  | succ j ih =>
    obtain ⟨ε', h⟩ := ih
    refine ⟨xor ε' (epsR F), ?_⟩
    rw [pow_succ, h, nm_mul, map_one, twist_one, mul_one, ← pow_succ]

theorem HarrisHyp.v0Std_mul_self (hH : HarrisHyp F) : v0Std F * v0Std F = 1 := by
  rw [nm_mul, map_one, twist_one, mul_one, Bool.xor_self, hH.psiF_mul_self, nm_one]

theorem HarrisHyp.v0Std_ne_one (hH : HarrisHyp F) : v0Std F ≠ 1 := by
  intro h
  have := congrArg SemidirectProduct.right h
  exact hH.psiF_ne_one this

theorem HarrisHyp.orderOf_v0Std (hH : HarrisHyp F) : orderOf (v0Std F) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hH.v0Std_mul_self) hH.v0Std_ne_one

theorem HarrisHyp.orderOf_vStd (hH : HarrisHyp F) (hψK : SemidirectProduct.inr (psiF F) ∈ K) :
    orderOf (vStd F K) = orderOf (phiGam F K) := by
  cases hε : epsR F
  · simp only [vStd, hε, nm_one_false]
    exact orderOf_injective _ SemidirectProduct.inr_injective _
  · have hφ := hH.phiGam_eq_psiF hψK hε
    have : vStd F K = v0Std F := by simp only [vStd, v0Std, hφ]
    rw [this, hH.orderOf_v0Std, hφ, hH.orderOf_psiF]

theorem HarrisHyp.vStd_pow_half (hH : HarrisHyp F) (hψK : SemidirectProduct.inr (psiF F) ∈ K) :
    vStd F K ^ (orderOf (vStd F K) / 2) = v0Std F := by
  rw [hH.orderOf_vStd hψK]
  cases hε : epsR F
  · simp only [vStd, v0Std, hε, nm_one_false]
    rw [← map_pow, hH.phiGam_pow_half hψK]
  · have hφ := hH.phiGam_eq_psiF hψK hε
    simp only [vStd, v0Std, hφ, hH.orderOf_psiF]
    rw [Nat.div_self two_pos, pow_one]

theorem isFieldInvModel_of_involution (hodd : IsOddPrimePower (Nat.card F)) {x : PGammaL2 F}
    (hx : orderOf x = 2) (hr : x.right ≠ 1) : IsFieldInvModel x := by
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd x hx hr
  refine ⟨SemidirectProduct.inl C, x.right, ?_, ?_⟩
  · apply orderOf_eq_prime _ hr
    have h2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hx])
    rw [← right_pow, h2]
    rfl
  · rw [← hC]
    group

theorem isFieldAutModel_of_involution (hodd : IsOddPrimePower (Nat.card F)) {x : PGammaL2 F}
    (hx : orderOf x = 2) (hr : x.right ≠ 1) : IsFieldAutModel x := by
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd x hx hr
  exact ⟨SemidirectProduct.inl C, x.right, hr, by rw [← hC]; group⟩

theorem HarrisHyp.isFieldInvModel_v0Std (hH : HarrisHyp F) : IsFieldInvModel (v0Std F) :=
  isFieldInvModel_of_involution hH.odd hH.orderOf_v0Std (by simp [hH.psiF_ne_one])

theorem HarrisHyp.commute_v0Std_iff (hH : HarrisHyp F) {a : Fˣ} (ha : a ∈ zpowers (stdGen F))
    (ε : Bool) (σ : F ≃+* F) :
    nm F a ε σ * v0Std F = v0Std F * nm F a ε σ ↔ a ∈ zpowers (stdGen F ^ 2) := by
  constructor
  · intro h
    by_contra ha2
    have h2 := (hH.v₀_mul_nm ha ε σ).2 ha2
    rw [← h] at h2
    exact hH.zStd_ne_one (right_eq_mul.mp h2)
  · exact fun h => ((hH.v₀_mul_nm ha ε σ).1 h).symm

theorem HarrisHyp.mem_sup_of (hH : HarrisHyp F) {c : Fˣ} (hc : c ∈ zpowers (stdGen F ^ 2))
    (ε : Bool) {σ : F ≃+* F} (hσ : σ ∈ gam0 F K) :
    nm F c ε σ ∈ rStd F ⊔ zpowers (vStd F K) := by
  rw [← zpowers_phiGam] at hσ
  obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers (x := phiGam F K) (y := σ)).mpr hσ
  simp only at hj
  subst hj
  obtain ⟨ε', hv⟩ := vStd_pow K j
  have : nm F c ε (phiGam F K ^ j) = nm F c (xor ε ε') 1 * vStd F K ^ j := by
    rw [hv, nm_mul, map_one, twist_one, mul_one, one_mul, Bool.xor_assoc, Bool.xor_self,
      Bool.xor_false]
  rw [this]
  exact mul_mem (mem_sup_left (nm_mem_rStd hH.sq hc _))
    (mem_sup_right (pow_mem (mem_zpowers _) j))

theorem HarrisHyp.stdTS_inf_centralizer_v0Std (hH : HarrisHyp F)
    (hK : pGammaL2PSLRange F ≤ K) :
    stdTS F K ⊓ centralizer {v0Std F} = rStd F ⊔ zpowers (vStd F K) := by
  apply le_antisymm
  · rintro x ⟨⟨⟨a, ha, ε, σ, hσ, rfl⟩, hxK⟩, hxC⟩
    replace hxC := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have ha2 := (hH.commute_v0Std_iff ha ε σ).mp hxC
    exact hH.mem_sup_of ha2 ε ⟨hσ, (hH.nm_mem_iff hK ha2 ε σ).mp hxK⟩
  · apply sup_le
    · refine le_inf (hH.rStd_le_stdTS hK) ?_
      intro x hx
      obtain ⟨c, hc, ε, rfl⟩ := (mem_map_stdT_iff hH.sq x).mp hx
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact (hH.commute_v0Std_iff (zpowers_sq_le hc) ε 1).mpr hc
    · rw [zpowers_le]
      refine ⟨hH.vStd_mem hK, ?_⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact (hH.commute_v0Std_iff (one_mem _) _ _).mpr (one_mem _)

theorem HarrisHyp.eq_of_centralizes_rStd (hH : HarrisHyp F) {x : PGammaL2 F}
    (hx : x ∈ sylS0 F) (hxC : ∀ g ∈ rStd F, g * x = x * g) :
    ∃ s : Fˣ, (s = 1 ∨ s = -1) ∧ (x = nm F s false 1 ∨ x = nm F s (epsR F) (psiF F)) := by
  obtain ⟨p, f, hp, hp2, hF, -⟩ := hH.char
  obtain ⟨a, ha, ε, σ, hσ, rfl⟩ := hx
  have h1 := hxC _ (nm_mem_rStd hH.sq (one_mem _) true)
  rw [nm_mul, nm_mul, nm_eq_nm_iff] at h1
  have ha1 : a⁻¹ = a := by simpa [fu_one] using h1.1
  have hs : a = 1 ∨ a = -1 :=
    units_eq_one_or_neg_one (by rw [pow_two]; nth_rw 1 [← ha1]; exact inv_mul_cancel a)
  have h2 := hxC _ (nm_mem_rStd hH.sq (mem_zpowers (stdGen F ^ 2)) false)
  have h2' : twist F ε (fu F σ (stdGen F ^ 2)) = stdGen F ^ 2 :=
    (nm_commute_tor_iff a _ ε σ).mp h2.symm
  refine ⟨a, hs, ?_⟩
  by_cases hσ1 : σ = 1
  · left
    subst hσ1
    cases ε
    · rfl
    · exfalso
      rw [fu_one, twist_true] at h2'
      exact hH.c₀_ne_inv h2'.symm
  · right
    obtain ⟨i, hi⟩ := orderOf_eq_two_pow_of_mem_galTwo hσ
    have hi1 : 1 ≤ i := by
      by_contra h
      apply hσ1
      rw [← orderOf_eq_one_iff, hi, show i = 0 by omega, pow_zero]
    have hfix : Units.map σ.toRingHom (stdGen F ^ 2) = stdGen F ^ 2 ∨
        Units.map σ.toRingHom (stdGen F ^ 2) = (stdGen F ^ 2)⁻¹ := by
      cases ε
      · exact Or.inl h2'
      · rw [twist_true] at h2'
        exact Or.inr (inv_eq_iff_eq_inv.mp h2')
    have hdvd := two_pow_add_dvd_of_fix_or_inv hp hp2 hF σ hi1 hi _ (orderOf_stdGen_sq hH.odd)
      hfix
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by
      have := Finite.one_lt_card (α := F); omega)).mp hdvd
    have h4 := hH.four_le
    have hi' : i = 1 := by
      change twoVal F - 1 + i ≤ twoVal F at hle
      omega
    have hσψ : σ = psiF F := hH.eq_psiF_of_orderOf (by rw [hi, hi', pow_one])
    subst hσψ
    have hεeq : ε = epsR F := by
      by_contra hne
      have : ε = !epsR F := by cases ε <;> cases h : epsR F <;> simp_all
      rw [this, twist_not, hH.twist_epsR_sq] at h2'
      exact hH.c₀_ne_inv h2'.symm
    rw [hεeq]

end Overgroup

end CFSG.ComponentClassification.AutL2Facts
