module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W3
public import CFSG.ClassicalInvolution.Q3.TL4Conn264T
public import CFSG.ClassicalInvolution.Q3.TL4Conn264B
public import CFSG.ClassicalInvolution.Asc77.AscE187P1a
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem false_of_three_secImg_of (hP : Q3CL.PartIHypG Ω) (hthree : NoThreeMeetSylow Ω)
    {M₁ M₂ M₃ : Subgroup G} (h₁ : XMem Ω x M₁) (h₂ : XMem Ω x M₂) (h₃ : XMem Ω x M₃)
    (h12 : secImg Ω x M₁ ≠ secImg Ω x M₂) (h13 : secImg Ω x M₁ ≠ secImg Ω x M₃)
    (h23 : secImg Ω x M₂ ≠ secImg Ω x M₃) {Pb : Subgroup (SecQuot Ω x)} (hPb : IsPGroup 2 ↥Pb)
    (hc₁ : 2 < Nat.card ↥(secImg Ω x M₁ ⊓ Pb)) (hc₂ : 2 < Nat.card ↥(secImg Ω x M₂ ⊓ Pb))
    (hc₃ : 2 < Nat.card ↥(secImg Ω x M₃ ⊓ Pb)) : False := by
  obtain ⟨P, hP2, rfl⟩ := exists_isPGroup_map_eq hPb
  obtain ⟨ν₁, hν₁, hk₁⟩ := exists_conj_lt_card_inf M₁ hP2 hc₁
  obtain ⟨ν₂, hν₂, hk₂⟩ := exists_conj_lt_card_inf M₂ hP2 hc₂
  obtain ⟨ν₃, hν₃, hk₃⟩ := exists_conj_lt_card_inf M₃ hP2 hc₃
  obtain ⟨S₂, hS₂⟩ := (hP2.map (layerY Ω x).subtype).exists_le_sylow
  have hcl := hP.hyp.conjInvariant
  have hne : ∀ {A B : Subgroup G} {ν μ : ↥(layerY Ω x)},
      ν ∈ classicalInvolutionOddCore ↥(layerY Ω x) →
      μ ∈ classicalInvolutionOddCore ↥(layerY Ω x) →
      secImg Ω x A ≠ secImg Ω x B → conjSub (ν : G) A ≠ conjSub (μ : G) B := by
    intro A B ν μ hν hμ hAB he
    apply hAB
    rw [← secImg_conj_of_mem hν A, he, secImg_conj_of_mem hμ B]
  have hcard : ∀ {A : Subgroup G}, 2 < Nat.card ↥(A ⊓ P.map (layerY Ω x).subtype) →
      2 < Nat.card ↥(A ⊓ (S₂ : Subgroup G)) := fun hA =>
    lt_of_lt_of_le hA (Subgroup.card_le_of_le (inf_le_inf_left _ hS₂))
  exact hthree S₂ _ _ _ (hcl _ _ h₁.1) (hcl _ _ h₂.1) (hcl _ _ h₃.1) (hne hν₁ hν₂ h12)
    (hne hν₁ hν₃ h13) (hne hν₂ hν₃ h23) (hcard hk₁) (hcard hk₂) (hcard hk₃)

end Lift

theorem exists_wSet_normal {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaGen Ω) (S₂ : Sylow 2 G) :
    ∃ W : Subgroup G, W ∈ WSet Ω ∧ W ≤ (S₂ : Subgroup G) ∧
      ∀ s ∈ (S₂ : Subgroup G), conjSub s W = W :=
  Q3CP.exists_W_of_hypOmegaGen hΩ S₂

structure SPropSec {G : Type} [Group G] (Ω : Set (Subgroup G)) (x : G) (K J : Subgroup G)
    (σ : MulAut (SecQuot Ω x)) : Prop where
  sq : σ * σ = 1
  perm : ∀ M ∈ secFam Ω x, M.map σ.toMonoidHom ∈ secFam Ω x
  fixK : ∃ Q : Subgroup (SecQuot Ω x), IsSylow2In Q (secImg Ω x K) ∧ ∀ y ∈ Q, σ y = y
  normJ : ∀ k ∈ secImg Ω x J, σ k ∈ secImg Ω x J
  onJ : ∃ Q : Subgroup (SecQuot Ω x), IsSylow2In Q (secImg Ω x J) ∧ (∀ y ∈ Q, σ y ∈ Q) ∧
    ∀ y ∈ Q, σ y = y → y * y = 1

section Act

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

private theorem secAct_mk_of_commute (hcl : ConjInvariant Ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({x} : Set G)) (w : ↥(layerY Ω x)) (hyw : y * (w : G) = w * y) :
    secAct hcl hy (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) w) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) w :=
  s26Act_mk (layerY Ω x) ⟨y, mem_normalizer_layerY hcl hy⟩ w w (by
    show (w : G) = y * w * y⁻¹
    rw [hyw, mul_inv_cancel_right])

private theorem secAct_mk_conj (hcl : ConjInvariant Ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({x} : Set G)) (w : ↥(layerY Ω x))
    (hw : y * (w : G) * y⁻¹ ∈ layerY Ω x) :
    secAct hcl hy (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) w) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨y * (w : G) * y⁻¹, hw⟩ :=
  s26Act_mk (layerY Ω x) ⟨y, mem_normalizer_layerY hcl hy⟩ w _ rfl

private theorem eq_one_of_mem_oddCore [Finite G] {T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (w : ↥(layerY Ω x)) (hwT : (w : G) ∈ T)
    (hwO : w ∈ classicalInvolutionOddCore ↥(layerY Ω x)) : (w : G) = 1 := by
  have hodd : Odd (orderOf w) :=
    (odd_natCard_oddCore_layerY (Ω := Ω) (x := x)).of_dvd_nat
      (by rw [← Subgroup.orderOf_mk w hwO]; exact orderOf_dvd_natCard _)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨w, hwT⟩
  have h2 : orderOf w = 2 ^ k := by
    rw [← Subgroup.orderOf_coe w, ← hk]
    exact Subgroup.orderOf_coe (⟨(w : G), hwT⟩ : ↥T)
  rw [h2] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at h2
  rw [h2]; rfl

end Act

section SBar

private theorem q8_eq_sq_of_involution : ∀ x : QuaternionGroup 2, x * x = 1 → x ≠ 1 →
    x = QuaternionGroup.a 1 ^ 2 := by decide

private theorem mem_of_index_le_two_of_quat {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hidx : N.index ≤ 2) {Q : Subgroup X} (hQ : Nonempty (↥Q ≃* QuaternionGroup 2)) {z : X}
    (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1) : z ∈ N := by
  obtain ⟨e⟩ := hQ
  have hz' : e ⟨z, hzQ⟩ = QuaternionGroup.a 1 ^ 2 := by
    refine q8_eq_sq_of_involution _ ?_ ?_
    · rw [← map_mul]
      have : (⟨z, hzQ⟩ : ↥Q) * ⟨z, hzQ⟩ = 1 := Subtype.ext hz2
      rw [this, map_one]
    · intro h
      apply hz1
      have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
      exact this
  have hzq : z = ((e.symm (QuaternionGroup.a 1) : ↥Q) : X) ^ 2 := by
    have h1 : (⟨z, hzQ⟩ : ↥Q) = e.symm (QuaternionGroup.a 1) ^ 2 := by
      apply e.injective
      rw [hz', map_pow, MulEquiv.apply_symm_apply]
    have := congrArg Subtype.val h1
    rw [Subgroup.coe_pow] at this
    exact this
  have hne0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : N.index = 1 ∨ N.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top z
  · rw [hzq]; exact Subgroup.sq_mem_of_index_two h2 _

private theorem conj_invol_of_psl2 {H : Type*} [Group H] {K : Type} [Field K] [Finite K]
    (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K))
    (e : H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
    ∀ a b : H, a ≠ 1 → a * a = 1 → b ≠ 1 → b * b = 1 → ∃ g : H, g * a * g⁻¹ = b := by
  intro a b ha ha2 hb hb2
  obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power K hK
    (e a) (e b)
    ⟨fun h => ha (e.injective (h.trans (map_one e).symm)), by
      rw [pow_two, ← map_mul, ha2, map_one]⟩
    ⟨fun h => hb (e.injective (h.trans (map_one e).symm)), by
      rw [pow_two, ← map_mul, hb2, map_one]⟩
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hg

private theorem exists_two_comm_invol_of_psl2 {H : Type*} [Group H] {K : Type} [Field K]
    [Finite K] (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K))
    (e : H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
    ∃ v w : H, v ≠ 1 ∧ v * v = 1 ∧ w ≠ 1 ∧ w * w = 1 ∧ v ≠ w ∧ v * w = w * v := by
  let S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := default
  obtain ⟨m, hm, ⟨φ⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hK S
  let ι : DihedralGroup (2 ^ m) →* H :=
    e.symm.toMonoidHom.comp ((S : Subgroup _).subtype.comp φ.symm.toMonoidHom)
  have hι : Function.Injective ι :=
    e.symm.injective.comp (Subtype.val_injective.comp φ.symm.injective)
  have hao : orderOf (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) = 2 :=
    CFSG.GorensteinWalter.TwoClassFusion.orderOf_r_half hm
  have ha1 : (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hao
    omega
  have ha2 : DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) *
      DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 1 := by
    have h1 := pow_orderOf_eq_one (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    rwa [hao, pow_two] at h1
  have hc : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
    have h1 := ha2
    rw [DihedralGroup.r_mul_r, ← DihedralGroup.r_zero] at h1
    exact DihedralGroup.r.inj h1
  have hb1 : (DihedralGroup.sr 0 : DihedralGroup (2 ^ m)) ≠ 1 := by
    rw [DihedralGroup.one_def]
    exact fun h => by cases h
  have hab : DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ DihedralGroup.sr 0 :=
    fun h => by cases h
  have hcomm : DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) * DihedralGroup.sr 0 =
      DihedralGroup.sr 0 * DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, zero_sub, zero_add,
      neg_eq_of_add_eq_zero_right hc]
  refine ⟨ι (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))), ι (DihedralGroup.sr 0),
    fun h => ha1 (hι (h.trans (map_one ι).symm)), by rw [← map_mul, ha2, map_one],
    fun h => hb1 (hι (h.trans (map_one ι).symm)), by
      rw [← map_mul, DihedralGroup.sr_mul_self, map_one],
    fun h => hab (hι h), by rw [← map_mul, ← map_mul, hcomm]⟩

private theorem exists_invol_comm_of_conj_of_four {N : Type*} [Group N]
    (hconj : ∀ a b : N, a ≠ 1 → a * a = 1 → b ≠ 1 → b * b = 1 → ∃ g : N, g * a * g⁻¹ = b)
    {v w : N} (hv : v ≠ 1) (hv2 : v * v = 1) (hw : w ≠ 1) (hw2 : w * w = 1) (hvw : v ≠ w)
    (hcomm : v * w = w * v) {b : N} (hb : b ≠ 1) (hb2 : b * b = 1) :
    ∃ d : N, d ≠ 1 ∧ d * d = 1 ∧ d ≠ b ∧ d * b = b * d := by
  obtain ⟨g, hg⟩ := hconj v b hv hv2 hb hb2
  refine ⟨g * w * g⁻¹, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hw
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  · calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = 1 := by rw [hw2]; simp
  · intro h
    apply hvw
    have h1 : g * w * g⁻¹ = g * v * g⁻¹ := h.trans hg.symm
    have := congrArg (fun z => g⁻¹ * z * g) h1
    simpa [mul_assoc] using this.symm
  · rw [← hg]
    calc g * w * g⁻¹ * (g * v * g⁻¹) = g * (w * v) * g⁻¹ := by group
      _ = g * (v * w) * g⁻¹ := by rw [hcomm]
      _ = g * v * g⁻¹ * (g * w * g⁻¹) := by group

private theorem exists_conj_comm_of_psl2 {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup ↥(genFittingFStar X)) {p f : ℕ} (hp2 : p ≠ 2)
    (hl : LieModel (FStarQuot X) .PSL 2 p f) {z : X} (hz : z ∈ genFittingFStar X)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ g : X, g * z * g⁻¹ ≠ z ∧ (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
  haveI := hsimple
  obtain ⟨hp, h4, F, _, _, hFcard, ⟨e⟩⟩ := MF163.psl2_of_lieModel hl
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h4
    · exact h
  have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hFcard⟩
  have hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian F
        (by omega) (by omega)
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm x)
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm y)
    refine ⟨a, b, fun hab => hxy ?_⟩
    have := congrArg (fun g => e (QuotientGroup.mk g : FStarQuot X)) hab
    simp only [QuotientGroup.mk_mul, map_mul] at this
    rwa [ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have hZ : Subgroup.center ↥(genFittingFStar X) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(genFittingFStar X))
      with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  let ψ : ↥(genFittingFStar X) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  have hconj := conj_invol_of_psl2 hK ψ
  obtain ⟨v, w, hv, hv2, hw, hw2, hvw, hvwc⟩ := exists_two_comm_invol_of_psl2 hK ψ
  have hz1' : (⟨z, hz⟩ : ↥(genFittingFStar X)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz2' : (⟨z, hz⟩ : ↥(genFittingFStar X)) * ⟨z, hz⟩ = 1 := Subtype.ext hz2
  obtain ⟨d, hd1, hd2, hdb, hdc⟩ :=
    exists_invol_comm_of_conj_of_four hconj hv hv2 hw hw2 hvw hvwc hz1' hz2'
  obtain ⟨k, hk⟩ := hconj ⟨z, hz⟩ d hz1' hz2' hd1 hd2
  have hk' : (k : X) * z * (k : X)⁻¹ = (d : X) := congrArg Subtype.val hk
  refine ⟨(k : X), ?_, ?_⟩
  · rw [hk']
    exact fun h => hdb (Subtype.ext h)
  · rw [hk']
    exact congrArg Subtype.val hdc

private theorem sq_eq_one_of_commute_of_isSemidihedral {G : Type} [Group G] [Finite G]
    {R : Subgroup G} (hR : Nonempty (↥R ≃* QuaternionGroup 2)) {d : G} (hd2 : d * d = 1)
    (hdR : d ∈ Subgroup.normalizer (R : Set G))
    (hsd : IsSemidihedral (R ⊔ Subgroup.zpowers d)) {y : G} (hy : y ∈ R)
    (hyd : y * d = d * y) : y * y = 1 := by
  obtain ⟨φ⟩ := hR
  have hexp : ∀ x ∈ R, x ^ 4 = 1 := fun x hx => by
    have h1 : φ (⟨x, hx⟩ ^ 4) = φ 1 := by
      rw [map_pow, map_one]
      exact (by decide : ∀ q : QuaternionGroup 2, q ^ 4 = 1) _
    simpa using congrArg Subtype.val (φ.injective h1)
  obtain ⟨a, b, ha8, hcard, hb2, hbA, hbab, hcl⟩ := hsd
  have haP : a ∈ R ⊔ Subgroup.zpowers d := hcl ▸ Subgroup.subset_closure (by simp)
  have ha2R : a * a ∈ R :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.mul_self_mem_of_mem_sup_zpowers hd2 hdR haP
  have hord : orderOf a = 8 := by
    have h8 : a ^ 8 = 1 := by
      have h := hexp _ ha2R
      rwa [← sq, ← pow_mul] at h
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h8)
    omega
  have h : CFSG.ClassicalInvolution.Disconnected.AschTight.SDData
      (R ⊔ Subgroup.zpowers d) a b 1 := by
    refine ⟨by omega, ⟨0, by norm_num⟩, by omega, hb2, hbA, ?_, ?_⟩
    · rw [hbab, hord, ← zpow_natCast]
      norm_num
    · rw [← CFSG.ClassicalInvolution.Disconnected.AschTight.closure_pair_eq_sup_zpowers, hcl]
  have hz : ∀ i : ℤ, a ^ i = 1 ↔ (8 : ℤ) ∣ i := fun i => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hord, Nat.cast_ofNat]
  have heq : ∀ i j : ℤ, a ^ i = a ^ j ↔ (8 : ℤ) ∣ i - j := fun i j => by
    rw [← hz, zpow_sub, mul_inv_eq_one]
  have hconj : ∀ i : ℤ, b * a ^ i = a ^ (3 * i) * b := fun i => by
    rw [← mul_inv_eq_iff_eq_mul, h.conj_zpow]
    congr 1
    push_cast
    ring
  have hmul0 : ∀ i j : ℤ, a ^ i * (a ^ j * b) = a ^ (i + j) * b := fun i j => by
    rw [← mul_assoc, ← zpow_add]
  have hmul1 : ∀ i j : ℤ, a ^ j * b * a ^ i = a ^ (j + 3 * i) * b := fun i j => by
    rw [mul_assoc, hconj, ← mul_assoc, ← zpow_add]
  have hmul : ∀ i j : ℤ, a ^ i * b * (a ^ j * b) = a ^ (i + 3 * j) := fun i j => by
    calc a ^ i * b * (a ^ j * b) = a ^ i * (b * a ^ j) * b := by simp only [mul_assoc]
      _ = a ^ (i + 3 * j) * (b * b) := by rw [hconj, zpow_add]; simp only [mul_assoc]
      _ = a ^ (i + 3 * j) := by rw [hb2, mul_one]
  have hpow2 : ∀ k : ℤ, a ^ (2 * k) ∈ R := fun k => by
    rw [zpow_mul, zpow_two]
    exact R.zpow_mem ha2R k
  have hdnR : d ∉ R := by
    intro hdR'
    have hle : R ⊔ Subgroup.zpowers d ≤ R := sup_le le_rfl (Subgroup.zpowers_le.mpr hdR')
    have h4 := orderOf_dvd_of_pow_eq_one (hexp a (hle haP))
    rw [hord] at h4
    omega
  by_contra hyy
  rcases h.mem_or (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)) with ⟨j, hj⟩ | ⟨j, hj⟩
  ·
    apply hdnR
    rw [← hj] at hd2 ⊢
    have h1 : (8 : ℤ) ∣ j + j := by rw [← hz, zpow_add]; exact hd2
    obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    exact hpow2 k
  ·
    rw [← hj] at hd2 hyd
    have h1 : (8 : ℤ) ∣ j + 3 * j := by rw [← hz, ← hmul]; exact hd2
    rcases h.mem_or (Subgroup.mem_sup_left hy) with ⟨i, hi⟩ | ⟨i, hi⟩
    ·
      rw [← hi] at hyy hyd
      have h2 : ¬ (8 : ℤ) ∣ i + i := by rw [← hz, zpow_add]; exact hyy
      rw [hmul0, hmul1] at hyd
      have h3 := (heq _ _).mp (mul_right_cancel hyd)
      omega
    ·
      rw [← hi] at hyy hyd
      have h2 : ¬ (8 : ℤ) ∣ i + 3 * i := by rw [← hz, ← hmul]; exact hyy
      rw [hmul, hmul] at hyd
      have h3 := (heq _ _).mp hyd
      omega

private theorem exists_conj_sd {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam 3 Φ) (hedge : Disconnected.DEdgeless Φ)
    (hstar : ∀ L ∈ Φ, omegaStarNbr Φ L = ∅) {M : Subgroup X} (hM : M ∈ Φ) {z : X}
    (hz : IsUniqueInvolution M z) {T : Subgroup X} (hT : IsSylow2In T M) {g₁ : X}
    (hne : g₁ * z * g₁⁻¹ ≠ z) (hcomm : (g₁ * z * g₁⁻¹) * z = z * (g₁ * z * g₁⁻¹)) :
    ∃ g : X, g * z * g⁻¹ ∈ Subgroup.normalizer (T : Set X) ∧
      ∀ y ∈ T, y * (g * z * g⁻¹) = (g * z * g⁻¹) * y → y * y = 1 := by
  classical
  have hΩ := hΦ.hyp
  have hcl := hΩ.conjInvariant
  set δ := g₁ * z * g₁⁻¹ with hδ
  have hM₂Φ : conjSub g₁ M ∈ Φ := hcl g₁ M hM
  have hδM₂ : IsUniqueInvolution (conjSub g₁ M) δ := hz.conj g₁
  have hM₂ne : conjSub g₁ M ≠ M := by
    intro e
    rw [e] at hδM₂
    exact hne (hz.eq hδM₂).symm
  have htw : conjSub g₁ M ∉ twinSet Φ M := by
    rintro ⟨-, w, hw, hw'⟩
    exact hne ((hδM₂.eq hw').trans (hw.eq hz))
  have hδC : δ ∈ Subgroup.centralizer ({z} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hδ2 : IsPGroup 2 ↥(Subgroup.zpowers δ) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hδM₂.sq) hδM₂.ne_one]
      norm_num)
  obtain ⟨V, hV, hδV⟩ := IsSylow2In.exists_ge hδ2
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hδM₂.mem, hδC⟩))
  have hδV' : δ ∈ V := hδV (Subgroup.mem_zpowers δ)
  rcases Sec6Gen.l6_2Gen X Φ hΩ M hM z hz _ hM₂Φ htw δ hδM₂ V hV hδV' with
    ⟨-, hne'⟩ | ⟨hVe, -, R', hR', hR'M, hVR', hsd⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVc⟩
  · exact absurd (mem_normalizer_iff_conjSub_eq.mp (hΦ.tight M hM z hz hδC)) hne'
  · have hR'syl : IsSylow2In R' M := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hM hR' hR'M
    obtain ⟨m, -, hmT⟩ := exists_conjSub_eq_of_isSylow2In hT hR'syl
    have hδN : δ ∈ Subgroup.normalizer (R' : Set X) := hVR' hδV'
    have hR'q : Nonempty (↥R' ≃* QuaternionGroup 2) := hΦ.quat M hM R' hR'syl
    have hsdδ : IsSemidihedral (R' ⊔ Subgroup.zpowers δ) := by rw [← hVe]; exact hsd
    have e : m⁻¹ * g₁ * z * (m⁻¹ * g₁)⁻¹ = m⁻¹ * δ * m := by rw [hδ]; group
    refine ⟨m⁻¹ * g₁, ?_, fun y hy hyc => ?_⟩
    · rw [e, mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul, hmT,
        mem_normalizer_iff_conjSub_eq.mp hδN, ← hmT, conjSub_inv_conjSub]
    · rw [e] at hyc
      have hy' : m * y * m⁻¹ ∈ R' := by rw [← hmT]; exact conj_mem_conjSub hy m
      have hc : (m * y * m⁻¹) * δ = δ * (m * y * m⁻¹) := by
        calc (m * y * m⁻¹) * δ = m * (y * (m⁻¹ * δ * m)) * m⁻¹ := by group
          _ = m * ((m⁻¹ * δ * m) * y) * m⁻¹ := by rw [hyc]
          _ = δ * (m * y * m⁻¹) := by group
      have h1 := sq_eq_one_of_commute_of_isSemidihedral hR'q hδM₂.sq hδN hsdδ hy' hc
      calc y * y = m⁻¹ * ((m * y * m⁻¹) * (m * y * m⁻¹)) * m := by group
        _ = 1 := by rw [h1]; group
  · exfalso
    have h : conjSub g₁ M ∈ omegaStarNbr Φ M :=
      ⟨hM₂Φ, hM₂ne, V, hVU, hV.1.trans inf_le_left, hVN⟩
    rw [hstar M hM] at h
    exact h
  · exact absurd (Or.inl ⟨hM₂Φ, hM₂ne, V, hVR, hV.1.trans inf_le_left,
      le_normalizer_of_commutator_le_oddCoreOf hVc⟩) (hedge M hM _ hM₂Φ)

end SBar

section SLift

private theorem mem_normalizer_of_mul_self {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g * g = 1) (h : ∀ y ∈ H, g * y * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨h y, fun hy => ?_⟩
  have h1 := h _ hy
  have e : g * (g * y * g⁻¹) * g⁻¹ = y := by
    calc g * (g * y * g⁻¹) * g⁻¹ = (g * g) * y * (g * g)⁻¹ := by group
      _ = y := by rw [hg]; group
  rwa [e] at h1

private theorem exists_conj_of_odd {G : Type*} [Group G] {w s : G} (hw : w * w = 1)
    (hs : s * s = 1) (ho : Odd (orderOf (w⁻¹ * s))) : ∃ g : G, g * w * g⁻¹ = s := by
  obtain ⟨k, hk⟩ := ho
  obtain ⟨o, ho⟩ : ∃ o, o = w⁻¹ * s := ⟨_, rfl⟩
  rw [← ho] at hk
  have hwi : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw).symm
  have hsi : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hs).symm
  have hom : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one o
  have hinv : w * o * w⁻¹ = o⁻¹ := by
    rw [ho]
    calc w * (w⁻¹ * s) * w⁻¹ = s * w⁻¹ := by group
      _ = s⁻¹ * w⁻¹⁻¹ := by rw [hsi, inv_inv, hwi]
      _ = (w⁻¹ * s)⁻¹ := by group
  obtain ⟨o₁, ho₁⟩ : ∃ o₁, o₁ = o ^ (k + 1) := ⟨_, rfl⟩
  have hinv₁ : w * o₁ * w⁻¹ = o₁⁻¹ := by rw [ho₁, ← conj_pow, hinv, inv_pow]
  have hsq : o₁ * o₁ = o := by
    rw [ho₁, ← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hom, one_mul]
  have h1 : w * o₁ = o₁⁻¹ * w := by
    calc w * o₁ = (w * o₁ * w⁻¹) * w := by group
      _ = o₁⁻¹ * w := by rw [hinv₁]
  refine ⟨o₁⁻¹, ?_⟩
  calc o₁⁻¹ * w * o₁⁻¹⁻¹ = o₁⁻¹ * (w * o₁) := by group
    _ = (o₁ * o₁)⁻¹ * w := by rw [h1]; group
    _ = s := by rw [hsq, ho, mul_inv_rev, inv_inv, mul_assoc, hw, mul_one, hsi]

private theorem exists_lift_of_mod {Y : Type} [Group Y] [Finite Y] {Λ R₀ T₀ : Subgroup Y}
    (h2 : IsPGroup 2 ↥(R₀ ⊔ T₀)) (hTΛ : T₀ ≤ Λ)
    (hRΛ : ∀ r ∈ R₀, ∀ y ∈ Λ, r * y * r⁻¹ ∈ Λ)
    (hRO : ∀ r ∈ R₀, ∀ y ∈ Λ, r * y * r⁻¹ * y⁻¹ ∈ oddCoreOf Λ)
    {w : Y} (hwΛ : w ∈ Λ) (hww : w * w = 1)
    (hN : ∀ y ∈ T₀, ∃ y' ∈ T₀, w * y * w⁻¹ * y'⁻¹ ∈ oddCoreOf Λ) :
    ∃ s ∈ Λ, s * s = 1 ∧ (∀ r ∈ R₀, r * s = s * r) ∧ (∀ y ∈ T₀, s * y * s⁻¹ ∈ T₀) ∧
      (∀ y ∈ T₀, y * s = s * y → w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf Λ) ∧
      w⁻¹ * s ∈ oddCoreOf Λ := by
  classical
  set N := classicalInvolutionOddCore ↥Λ with hNdef
  set mk : ↥Λ →* ↥Λ ⧸ N := QuotientGroup.mk' N with hmkdef
  have hNodd : Odd (Nat.card ↥N) := CFSG.ComponentClassification.OddCore.odd_card ↥Λ
  have hO : ∀ g : ↥Λ, (g : Y) ∈ oddCoreOf Λ ↔ g ∈ N := fun g =>
    Subgroup.mem_map_iff_mem Λ.subtype_injective
  have hker : ∀ g : ↥Λ, mk g = 1 ↔ (g : Y) ∈ oddCoreOf Λ := fun g =>
    (QuotientGroup.eq_one_iff g).trans (hO g).symm
  have hmk : ∀ a b : ↥Λ, mk a = mk b ↔ (a : Y) * (b : Y)⁻¹ ∈ oddCoreOf Λ := fun a b => by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
    exact hker (a * b⁻¹)
  have hmk' : ∀ a b : ↥Λ, mk a = mk b ↔ (a : Y)⁻¹ * (b : Y) ∈ oddCoreOf Λ := fun a b => by
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul]
    exact hker (a⁻¹ * b)
  set w' : ↥Λ := ⟨w, hwΛ⟩ with hw'def
  have hmkw : mk w' * mk w' = 1 := by
    rw [← map_mul, show w' * w' = 1 from Subtype.ext hww, map_one]
  obtain ⟨Db, hDb2, hwD, hTD⟩ : ∃ Db : Subgroup (↥Λ ⧸ N), IsPGroup 2 ↥Db ∧ mk w' ∈ Db ∧
      ∀ y (hy : y ∈ T₀), mk ⟨y, hTΛ hy⟩ ∈ Db := by
    have hT2 : IsPGroup 2 ↥((T₀.subgroupOf Λ).map mk) :=
      ((h2.to_le le_sup_right).comap_subtype (K := Λ)).map mk
    have hw2 : IsPGroup 2 ↥(Subgroup.zpowers (mk w')) := by
      by_cases h1 : mk w' = 1
      · rw [h1, Subgroup.zpowers_one_eq_bot]; exact IsPGroup.of_bot
      · exact isPGroup_zpowers_of_mul_self_eq_one hmkw h1
    have hwn : mk w' ∈ Subgroup.normalizer (((T₀.subgroupOf Λ).map mk : Subgroup _) : Set _) := by
      refine mem_normalizer_of_mul_self hmkw ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨y', hy', hyy'⟩ := hN y (Subgroup.mem_subgroupOf.mp hy)
      refine ⟨⟨y', hTΛ hy'⟩, Subgroup.mem_subgroupOf.mpr hy', ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      exact ((hmk _ _).mpr hyy').symm
    refine ⟨Subgroup.zpowers (mk w') ⊔ (T₀.subgroupOf Λ).map mk,
      hw2.to_sup_of_normal_right' hT2 (Subgroup.zpowers_le.mpr hwn),
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _), fun y hy => Subgroup.mem_sup_right ?_⟩
    exact Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hy)
  obtain ⟨H, hH⟩ : ∃ H : Subgroup Y, ∀ y, y ∈ H ↔ ∃ hy : y ∈ Λ, mk ⟨y, hy⟩ ∈ Db := by
    refine ⟨(Db.comap mk).map Λ.subtype, fun y => ⟨?_, ?_⟩⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g.2, hg⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hHΛ : H ≤ Λ := fun y hy => ((hH y).mp hy).1
  have hTH : T₀ ≤ H := fun y hy => (hH y).mpr ⟨hTΛ hy, hTD y hy⟩
  have hwH : w ∈ H := (hH w).mpr ⟨hwΛ, hwD⟩
  have hRH : ∀ r ∈ R₀, ∀ y ∈ H, r * y * r⁻¹ ∈ H := by
    intro r hr y hy
    obtain ⟨hyΛ, hyD⟩ := (hH y).mp hy
    have h1 := hRΛ r hr y hyΛ
    refine (hH _).mpr ⟨h1, ?_⟩
    have e : mk ⟨r * y * r⁻¹, h1⟩ = mk ⟨y, hyΛ⟩ := (hmk _ _).mpr (hRO r hr y hyΛ)
    rw [e]
    exact hyD
  have hRN : R₀ ≤ Subgroup.normalizer (H : Set Y) := fun r hr =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨hRH r hr y, fun h => by
      have := hRH r⁻¹ (R₀.inv_mem hr) _ h
      rwa [show r⁻¹ * (r * y * r⁻¹) * r⁻¹⁻¹ = y by group] at this⟩
  obtain ⟨Sst, hSst, hRTS⟩ := IsSylow2In.exists_ge h2
    (sup_le le_sup_right (hTH.trans le_sup_left) : R₀ ⊔ T₀ ≤ H ⊔ R₀)
  have hV : IsSylow2In (Sst ⊓ H) H :=
    S1916.isSylow2In_inf_of_le_normalizer hSst le_sup_left (sup_le Subgroup.le_normalizer hRN)
  have hSO : ∀ g ∈ Sst, g ∈ oddCoreOf Λ → g = 1 := fun g h1 h3 =>
    (Subgroup.eq_bot_iff_forall _).mp (S1916.inf_oddCoreOf_eq_bot hSst.2.1 Λ) g
      (Subgroup.mem_inf.mpr ⟨h1, h3⟩)
  have hRS : R₀ ≤ Sst := le_sup_left.trans hRTS
  have hTS : T₀ ≤ Sst := le_sup_right.trans hRTS
  have hVb := isSylow2In_map_mk hNodd (hV.subgroupOf hHΛ)
  have hle : (H.subgroupOf Λ).map mk ≤ Db := by
    rintro _ ⟨g, hg, rfl⟩
    exact ((hH g).mp (Subgroup.mem_subgroupOf.mp hg)).2
  have heq := hVb.2.2 _ le_rfl (hDb2.to_le hle) hVb.1
  have hwV : mk w' ∈ ((Sst ⊓ H).subgroupOf Λ).map mk := by
    rw [← heq]
    exact Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hwH)
  obtain ⟨s', hs'V, hs'w⟩ := hwV
  have hsV : (s' : Y) ∈ Sst ⊓ H := Subgroup.mem_subgroupOf.mp hs'V
  have hsS : (s' : Y) ∈ Sst := (Subgroup.mem_inf.mp hsV).1
  refine ⟨s', s'.2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : mk (s' * s') = 1 := by rw [map_mul, hs'w, hmkw]
    exact hSO _ (Sst.mul_mem hsS hsS) ((hker _).mp h1)
  ·
    intro r hr
    have h1 := hSO _ (Sst.mul_mem (Sst.mul_mem (Sst.mul_mem (hRS hr) hsS) (Sst.inv_mem (hRS hr)))
      (Sst.inv_mem hsS)) (hRO r hr _ s'.2)
    calc r * (s' : Y) = r * s' * r⁻¹ * (s' : Y)⁻¹ * s' * r := by group
      _ = s' * r := by rw [h1, one_mul]
  ·
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := hN y hy
    have e : mk (s' * ⟨y, hTΛ hy⟩ * s'⁻¹) = mk ⟨y', hTΛ hy'⟩ := by
      rw [map_mul, map_mul, map_inv, hs'w, ← map_inv, ← map_mul, ← map_mul]
      exact (hmk _ _).mpr hyy'
    have h1 := hSO _ (Sst.mul_mem (Sst.mul_mem (Sst.mul_mem hsS (hTS hy)) (Sst.inv_mem hsS))
      (Sst.inv_mem (hTS hy'))) ((hmk _ _).mp e)
    have h3 : (s' : Y) * y * (s' : Y)⁻¹ = y' := mul_inv_eq_one.mp h1
    rw [h3]
    exact hy'
  ·
    intro y hy hys
    have e : mk (w' * ⟨y, hTΛ hy⟩ * w'⁻¹) = mk ⟨y, hTΛ hy⟩ := by
      rw [map_mul, map_mul, map_inv, ← hs'w, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (s' : Y) * y * (s' : Y)⁻¹ = y
      rw [← hys, mul_inv_cancel_right]
    exact (hmk _ _).mp e
  · exact (hmk' w' s').mp hs'w.symm

end SLift

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2Set.exists_conj_le (hs : Z2Set n R S t J u R₀ T₀ P) {Q : Subgroup Y}
    (hQ : IsPGroup 2 ↥Q) (hQa : Q ≤ Subgroup.centralizer ({t * u} : Set Y)) :
    ∃ c ∈ Subgroup.centralizer ({t * u} : Set Y), conjSub c Q ≤ (P : Subgroup Y) := by
  have hPa : (P : Subgroup Y) ≤ Subgroup.centralizer ({t * u} : Set Y) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hs.comm_tu hy)
  obtain ⟨h, hh, hle⟩ := exists_conj_sylow_ge hPa hQ hQa
  refine ⟨h⁻¹, inv_mem hh, ?_⟩
  have := conjSub_mono (n := h⁻¹) hle
  rwa [conjSub_inv_conjSub] at this

private theorem Z2Set.card_sylow (hs : Z2Set n R S t J u R₀ T₀ P) {M Q : Subgroup Y}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) (hQ : IsSylow2In Q M) : Nat.card ↥Q = 8 := by
  obtain ⟨e⟩ := (TightLargeHypR.typeRFam hs.large).quat M hM Q hQ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]; norm_num

private theorem Z2Set.card_uSet (hs : Z2Set n R S t J u R₀ T₀ P) {U : Subgroup Y}
    (hU : U ∈ USet (CoreAssembly.conjClass (tightCore R))) : Nat.card ↥U = 4 := by
  obtain ⟨R', -, J', hJ', hR'J', -, -, hcard, -⟩ :=
    Sec6Gen.exists_data_of_mem_USet hs.large.datum.hypOmegaGen hU
  rw [hs.card_sylow hJ' hR'J'] at hcard
  omega

theorem Z2Set.eq_of_two_lt_card (hs : Z2Set n R S t J u R₀ T₀ P) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y} (hy : IsUniqueInvolution L y)
    (h4 : 2 < Nat.card ↥(L ⊓ (P : Subgroup Y))) : y = t ∨ y = u := by
  classical
  have hΩ := hs.large.datum.hypOmegaGen
  have ht := hs.large.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ P
  have hηG : η ∈ etaG (CoreAssembly.conjClass (tightCore R)) := ⟨P, hη, hinv⟩
  have hηS : ∀ V ∈ η, V ≤ (P : Subgroup Y) := fun V hV => (hη.1 hV).2
  have hWab := (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hη hinv).1
  have hWP : (⨆ U ∈ η, U) ≤ (P : Subgroup Y) := iSup₂_le fun V hV => hηS V hV
  have hinvW : ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ m : Y, IsUniqueInvolution M m →
      2 < Nat.card ↥(M ⊓ (P : Subgroup Y)) → m ∈ ⨆ U ∈ η, U := by
    intro M hM m hm hc
    have hMW := Sec6Gen.l6_11Gen Y _ hΩ P η hηG hηS M hM hc
    have hU := (hη.1 hMW).1
    exact (T3.mem_of_isPGroup hm inf_le_left (Sec6Gen.isPGroup_of_mem_USet hΩ hU)
      (by rw [hs.card_uSet hU]; norm_num)).2
  have hcardR : ∀ {M Q : Subgroup Y}, M ∈ CoreAssembly.conjClass (tightCore R) → IsSylow2In Q M →
      Q ≤ (P : Subgroup Y) → 2 < Nat.card ↥(M ⊓ (P : Subgroup Y)) := by
    intro M Q hM hQ hQP
    have := Subgroup.card_le_of_le (le_inf hQ.1 hQP)
    rw [hs.card_sylow hM hQ] at this
    omega
  have htW := hinvW _ hK t ht (hcardR hK hs.hR₀ hs.hR₀P)
  have huW := hinvW _ hs.hJ.1 u hs.hu (hcardR hs.hJ.1 hs.hT₀ hs.hT₀P)
  have hLW := Sec6Gen.l6_11Gen Y _ hΩ P η hηG hηS L hL h4
  have hU := (hη.1 hLW).1
  have hU4 := hs.card_uSet hU
  obtain ⟨-, -, -, -, -, -, hcyc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(L ⊓ ⨆ U ∈ η, U))
  have hgo : orderOf (g : Y) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hU4]
  have hgL : (g : Y) ∈ L := g.2.1
  have hgW : (g : Y) ∈ ⨆ U ∈ η, U := g.2.2
  have hgA : (g : Y) ∈ edgeCent (P : Subgroup Y) t u :=
    ⟨⟨hWP hgW, Subgroup.mem_centralizer_singleton_iff.mpr (hWab _ hgW _ htW)⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (hWab _ hgW _ huW)⟩
  have hg4 : (g : Y) ^ 4 = 1 := by rw [← hgo]; exact pow_orderOf_eq_one _
  have hsq : (g : Y) ^ 2 ∈ Subgroup.closure ({t, u} : Set Y) := hs.sq_mem_E hgA hg4
  have hg2 : (g : Y) ^ 2 = y := by
    have h1 : (g : Y) ^ 2 * (g : Y) ^ 2 = 1 := by rw [← pow_add]; exact hg4
    rcases hy.unique _ (L.pow_mem hgL 2) h1 with h | h
    · exfalso
      have := orderOf_dvd_of_pow_eq_one h
      rw [hgo] at this
      norm_num at this
    · exact h
  rw [hg2] at hsq
  have htu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hs.hJ hs.hu
  rcases Thompson.eq_of_mem_closure_pair ht.sq hs.hu.sq htu hsq with h | h | h | h
  · exact absurd h hy.ne_one
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨c, rfl⟩ := hL
    have hc : y = c * t * c⁻¹ := hy.eq (ht.conj c)
    apply hs.tu_not_conj c⁻¹
    rw [← h, hc]
    group

theorem Z2Set.noThreeMeetSylow (hs : Z2Set n R S t J u R₀ T₀ P) :
    NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)) := by
  intro S₂ L₁ L₂ L₃ h₁ h₂ h₃ h12 h13 h23 hc₁ hc₂ hc₃
  have hΩ := hs.large.datum.hypOmegaGen
  have hcl := hΩ.conjInvariant
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₂ P
  have key : ∀ {M : Subgroup Y}, M ∈ CoreAssembly.conjClass (tightCore R) →
      2 < Nat.card ↥(M ⊓ (S₂ : Subgroup Y)) →
        ∃ m : Y, IsUniqueInvolution (conjSub g M) m ∧ (m = t ∨ m = u) := by
    intro M hM hc
    obtain ⟨m, hm⟩ := Sec6Gen.exists_uniqueInvolution hΩ (hcl g M hM)
    refine ⟨m, hm, hs.eq_of_two_lt_card (hcl g M hM) hm ?_⟩
    rw [← hg, ← conjSub_inf, natCard_conjSub]
    exact hc
  have heq : ∀ {M M' : Subgroup Y}, M ∈ CoreAssembly.conjClass (tightCore R) →
      M' ∈ CoreAssembly.conjClass (tightCore R) → ∀ {m : Y},
      IsUniqueInvolution (conjSub g M) m → IsUniqueInvolution (conjSub g M') m → M = M' := by
    intro M M' hM hM' m hm hm'
    have h := (TightLargeHypR.typeRFam hs.large).noTwins _ (hcl g M hM) _
      ⟨hcl g M' hM', m, hm, hm'⟩
    exact (conjSub_injective g h).symm
  obtain ⟨m₁, hm₁, e₁⟩ := key h₁ hc₁
  obtain ⟨m₂, hm₂, e₂⟩ := key h₂ hc₂
  obtain ⟨m₃, hm₃, e₃⟩ := key h₃ hc₃
  rcases e₁ with rfl | rfl <;> rcases e₂ with e₂ | e₂ <;> rcases e₃ with e₃ | e₃ <;> subst e₂ e₃
  all_goals first
    | exact h12 (heq h₁ h₂ hm₁ hm₂)
    | exact h13 (heq h₁ h₃ hm₁ hm₃)
    | exact h23 (heq h₂ h₃ hm₂ hm₃)

theorem Z2Set.exists_std8 (hs : Z2Set n R S t J u R₀ T₀ P) :
    ∃ W : Subgroup Y, TightStd8R 3 n R S t J P R₀ T₀ W u := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  obtain ⟨W, hW, hWP, hWn⟩ := exists_wSet_normal hs.large.datum.hypOmegaGen P
  exact ⟨W, ⟨hs.large, hs.hJ, hs.hu, ⟨mem_RSet_of_isSylow2In hK hs.hR₀, hs.hR₀.1, hs.hR₀P⟩,
    ⟨mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀, hs.hT₀.1, hs.hT₀P⟩, ⟨hW, hWP, hWn⟩⟩⟩

private theorem normalizer_secImg_core_eq_top (hL : TightLargeHypR 3 n Y R S t) :
    Subgroup.normalizer (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) :
      Set (SecQuot (CoreAssembly.conjClass (tightCore R)) t)) = ⊤ := by
  have h := TightLargeHypR.typeRFam hL
  have hΦ := h.secFam (x := t)
  have hK := secImg_mem (xMem_core hL)
  have hu := isUniqueInvolution_secImg h (xMem_core hL) hL.datum.isUniqueInvolution_core
  refine eq_top_iff.mpr (le_trans (fun g _ => ?_) (hΦ.tight _ hK _ hu))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (layerY_le_centralizer g.2))

private theorem commutes_secImg_core_of_isSylow2In (hL : TightLargeHypR 3 n Y R S t)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {V : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) t)}
    (hV : IsSylow2In V (secImg (CoreAssembly.conjClass (tightCore R)) t J)) :
    Commutes (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R)) V := by
  have h := TightLargeHypR.typeRFam hL
  have hΦ := h.secFam (x := t)
  have hK := secImg_mem (xMem_core hL)
  have hJΦ := secImg_mem (xMem_of_mem_omegaNbr_core hL hJ)
  have hK2 := isPGroup_secImg_core hL
  have hu := isUniqueInvolution_secImg h (xMem_core hL) hL.datum.isUniqueInvolution_core
  have hVR := mem_RSet_of_isSylow2In hJΦ hV
  have hVN : V ≤ Subgroup.normalizer
      (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) : Set _) := by
    rw [normalizer_secImg_core_eq_top hL]
    exact le_top
  obtain ⟨P, hPS⟩ := (hV.2.1.to_sup_of_normal_right' hK2 hVN).exists_le_sylow
  have hne : secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) ≠ V := by
    intro e
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hJΦ
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΦ.hyp hVR
    have hzV : z ∈ V := T3.mem_of_isPGroup hz hV.1 hV.2.1 (by omega)
    rw [← e] at hzV
    have hzu := (hu.unique z hzV hz.sq).resolve_left hz.ne_one
    rw [hzu] at hz
    exact (secImg_mem_omegaNbr_secImg_core hL hJ).2.1 (hΦ.noTwins _ hK _ ⟨hJΦ, _, hu, hz⟩)
  exact Q3CP.l67Gen _ (secFam (CoreAssembly.conjClass (tightCore R)) t) hΦ.hyp P _
    (TC.mem_RSet_of_isPGroup hK hK2) V hVR (le_sup_right.trans hPS) (le_sup_left.trans hPS) hne

private theorem secImg_le_centralizer_secImg_core (hL : TightLargeHypR 3 n Y R S t)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    secImg (CoreAssembly.conjClass (tightCore R)) t J ≤ Subgroup.centralizer
      (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) : Set _) := by
  have hJX := xMem_of_mem_omegaNbr_core hL hJ
  have hle : coreAt t J ≤ ((Subgroup.centralizer
      (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) : Set _)).comap
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)))).map
            (layerY (CoreAssembly.conjClass (tightCore R)) t).subtype := by
    rw [← closure_twoElts_coreAt, Subgroup.closure_le]
    rintro g ⟨hgc, hg2⟩
    have hgY := coreAt_le_layerY hJX hgc
    refine ⟨⟨g, hgY⟩, ?_, rfl⟩
    have hmem : QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨g, hgY⟩ ∈
          secImg (CoreAssembly.conjClass (tightCore R)) t J :=
      ⟨⟨g, hgY⟩, Subgroup.mem_subgroupOf.mpr hgc, rfl⟩
    have h2 := ((isPGroup_zpowers_coe_iff (v := ⟨g, hgY⟩)).mp hg2).map
      (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)))
    rw [MonoidHom.map_zpowers] at h2
    obtain ⟨V, hV, hgV⟩ := IsSylow2In.exists_ge h2 (Subgroup.zpowers_le.mpr hmem)
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro k hk
    exact commutes_secImg_core_of_isSylow2In hL hJ hV k hk _ (hgV (Subgroup.mem_zpowers _))
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨w', hw', e⟩ := hle (Subgroup.mem_subgroupOf.mp hw)
  obtain rfl : w' = w := Subtype.ext e
  exact hw'

private theorem linkGrp_le_centralizer' (hL : TightLargeHypR 3 n Y R S t) :
    linkGrp R t ≤ Subgroup.centralizer
      (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) : Set _) := by
  refine iSup₂_le fun Lb hLb => ?_
  obtain ⟨J, hJ, rfl⟩ := hLb
  exact secImg_le_centralizer_secImg_core hL hJ

theorem commutator_mem_oddCoreOf_linkLayer' (hL : TightLargeHypR 3 n Y R S t) {x : Y}
    (hx : x ∈ coreAt t (tightCore R)) {y : Y} (hy : y ∈ linkLayer R t) :
    x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t) := by
  have hxC := coreAt_le_centralizer t (tightCore R) hx
  have hxy : x * y * x⁻¹ ∈ linkLayer R t := conj_mem_linkLayer hL hxC hy
  have hc : x * y * x⁻¹ * y⁻¹ ∈ linkLayer R t := (linkLayer R t).mul_mem hxy
    ((linkLayer R t).inv_mem hy)
  suffices hk : (⟨_, hc⟩ : ↥(linkLayer R t)) ∈ (linkLayerHom' hL).ker by
    rw [ker_linkLayerHom hL] at hk
    exact ⟨⟨_, hc⟩, hk, rfl⟩
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  show linkLayerHom hL ⟨_, hc⟩ = 1
  have hxL := coreAt_le_layerY (xMem_core hL) hx
  have hyL := linkLayer_le_layerY hL hy
  have hxK : QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨x, hxL⟩ ∈
        secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R) :=
    ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hyX : QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨y, hyL⟩ ∈ linkGrp R t := by
    have := linkLayerHom_mem hL ⟨y, hy⟩
    rwa [linkLayerHom_apply] at this
  have hcomm := Subgroup.mem_centralizer_iff.mp (linkGrp_le_centralizer' hL hyX) _ hxK
  rw [linkLayerHom_apply]
  have e : (⟨x * y * x⁻¹ * y⁻¹, linkLayer_le_layerY hL hc⟩ :
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) =
      ⟨x, hxL⟩ * ⟨y, hyL⟩ * ⟨x, hxL⟩⁻¹ * ⟨y, hyL⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

private theorem Z2Set.exists_s_of_mod (hs : Z2Set n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ linkLayer R t)
    (hN : ∀ y ∈ T₀, ∃ y' ∈ T₀,
      (x * u * x⁻¹) * y * (x * u * x⁻¹)⁻¹ * y'⁻¹ ∈ oddCoreOf (linkLayer R t))
    (hC : ∀ y ∈ T₀, (x * u * x⁻¹) * y * (x * u * x⁻¹)⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t) →
      y * y = 1) :
    ∃ s : Y, s * s = 1 ∧ s * t = t * s ∧ s * u = u * s ∧
      R₀ ≤ Subgroup.centralizer ({s} : Set Y) ∧ s ∈ Subgroup.normalizer (T₀ : Set Y) ∧
      (∀ x ∈ T₀, x * s = s * x → x * x = 1) ∧ ∃ h : Y, h * u * h⁻¹ = s := by
  have ht := hs.large.datum.isUniqueInvolution_core
  have hNt := S1916.normalizer_le_centralizer_of_isUniqueInvolution ht
  have hT₀t : T₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun y hy => hNt (hs.hT₀N hy)
  have hR₀t : R₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun r hr =>
    hNt (Subgroup.le_normalizer (hs.hR₀.1 hr))
  have hR₀K : R₀ ≤ coreAt t (tightCore R) := le_coreAt t hs.hR₀.2.1 hs.hR₀.1 hR₀t
  have hT₀Λ : T₀ ≤ linkLayer R t :=
    (le_coreAt t hs.hT₀.2.1 hs.hT₀.1 hT₀t).trans (coreAt_le_linkLayerAt hs.hJ)
  have hcardT : Nat.card ↥T₀ = 8 := by
    obtain ⟨e⟩ := (TightLargeHypR.typeRFam hs.large).quat J hs.hJ.1 T₀ hs.hT₀
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]; norm_num
  have huT : u ∈ T₀ := T3.mem_of_isPGroup hs.hu hs.hT₀.1 hs.hT₀.2.1 (by rw [hcardT]; norm_num)
  have hwΛ : x * u * x⁻¹ ∈ linkLayer R t :=
    (linkLayer R t).mul_mem ((linkLayer R t).mul_mem hx (hT₀Λ huT)) ((linkLayer R t).inv_mem hx)
  have hww : x * u * x⁻¹ * (x * u * x⁻¹) = 1 := by
    calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
      _ = 1 := by rw [hs.hu.sq]; group
  have h2 : IsPGroup 2 ↥(R₀ ⊔ T₀) := P.isPGroup'.to_le (sup_le hs.hR₀P hs.hT₀P)
  obtain ⟨s, hsΛ, hss, hsR, hsT, hsC, hso⟩ := exists_lift_of_mod h2 hT₀Λ
    (fun r hr y hy => conj_mem_linkLayer hs.large (hR₀t hr) hy)
    (fun r hr y hy => commutator_mem_oddCoreOf_linkLayer' hs.large (hR₀K hr) hy) hwΛ hww hN
  have hsu : s * u * s⁻¹ = u := by
    have h1 : s * u * s⁻¹ ∈ T₀ := hsT u huT
    have h3 : s * u * s⁻¹ * (s * u * s⁻¹) = 1 := by
      calc s * u * s⁻¹ * (s * u * s⁻¹) = s * (u * u) * s⁻¹ := by group
        _ = 1 := by rw [hs.hu.sq]; group
    rcases hs.hu.unique _ (hs.hT₀.1 h1) h3 with h | h
    · exfalso
      apply hs.hu.ne_one
      calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
    · exact h
  obtain ⟨g, hg⟩ := exists_conj_of_odd hww hss
    ((oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hso))
  refine ⟨s, hss, ?_, ?_, fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hsR r hr),
    mem_normalizer_of_mul_self hss hsT, fun y hy hys => hC y hy (hsC y hy hys), g * x, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hsΛ)
  · calc s * u = s * u * s⁻¹ * s := by group
      _ = u * s := by rw [hsu]
  · rw [← hg]
    group

theorem Z2Set.exists_s (hs : Z2Set n R S t J u R₀ T₀ P) :
    ∃ s : Y, s * s = 1 ∧ s * t = t * s ∧ s * u = u * s ∧
      R₀ ≤ Subgroup.centralizer ({s} : Set Y) ∧ s ∈ Subgroup.normalizer (T₀ : Set Y) ∧
      (∀ x ∈ T₀, x * s = s * x → x * x = 1) ∧ ∃ h : Y, h * u * h⁻¹ = s := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hL := hs.large
  have ht := hL.datum.isUniqueInvolution_core
  have hJX : XMem Ω t J := xMem_of_mem_omegaNbr_core hL hs.hJ
  have huT : u ∈ T₀ := T3.mem_of_isPGroup hs.hu hs.hT₀.1 hs.hT₀.2.1
    (by rw [hs.card_sylow hs.hJ.1 hs.hT₀]; norm_num)
  have hTt : T₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hs.hT₀N hx)
  have hTc : IsSylow2In T₀ (coreAt t J) := (isSylow2In_coreAt_iff hJX).mpr ⟨hs.hT₀, hTt⟩
  have hTΛ : T₀ ≤ linkLayer R t := hTc.1.trans (coreAt_le_linkLayerAt hs.hJ)
  have huΛ : u ∈ linkLayer R t := hTΛ huT
  have hΦ : TypeRFam 3 (linkFam R t) := (lieLinkSection_of hL hs.z2.1).1
  have hM : (secImg Ω t J).subgroupOf (linkGrp R t) ∈ linkFam R t :=
    ⟨_, ⟨J, hs.hJ, rfl⟩, le_linkGrp hs.hJ, rfl⟩
  have hu' := isUniqueInvolution_secImg (TightLargeHypR.typeRFam hL) hJX hs.hu
  have hz : IsUniqueInvolution ((secImg Ω t J).subgroupOf (linkGrp R t))
      (linkLayerHom' hL ⟨u, huΛ⟩) :=
    ⟨Subgroup.mem_subgroupOf.mpr hu'.mem, fun h => hu'.ne_one (congrArg Subtype.val h),
      Subtype.ext hu'.sq, fun y hy hy2 =>
        (hu'.unique _ (Subgroup.mem_subgroupOf.mp hy) (congrArg Subtype.val hy2)).imp
          (fun h => Subtype.ext h) (fun h => Subtype.ext h)⟩
  have hT : IsSylow2In ((((T₀.subgroupOf (layerY Ω t)).map (QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(layerY Ω t)))).subgroupOf (linkGrp R t)))
      ((secImg Ω t J).subgroupOf (linkGrp R t)) :=
    (isSylow2In_map_mk odd_natCard_oddCore_layerY
      (hTc.subgroupOf (coreAt_le_layerY hJX))).subgroupOf (le_linkGrp hs.hJ)
  set T : Subgroup ↥(linkGrp R t) := (((T₀.subgroupOf (layerY Ω t)).map (QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(layerY Ω t)))).subgroupOf (linkGrp R t)) with hTdef
  set z : ↥(linkGrp R t) := linkLayerHom' hL ⟨u, huΛ⟩ with hzdef
  have hT8 : Nat.card ↥T = 8 := by
    obtain ⟨e⟩ := hΦ.quat _ hM T hT
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]; norm_num
  have hzT : z ∈ T := T3.mem_of_isPGroup hz hT.1 hT.2.1 (by rw [hT8]; norm_num)
  have hzF : z ∈ genFittingFStar ↥(linkGrp R t) :=
    mem_of_index_le_two_of_quat hs.index (hΦ.quat _ hM T hT) hzT hz.sq hz.ne_one
  obtain ⟨p, f, -, hp2, -, -, hl⟩ := hs.model
  obtain ⟨g₁, hne, hcomm⟩ := exists_conj_comm_of_psl2 hs.simple hp2 hl hzF hz.sq hz.ne_one
  obtain ⟨g, hgN, hgC⟩ := exists_conj_sd hΦ hs.z2.2.2.1 hs.z2.2.2.2 hM hz hT hne hcomm
  obtain ⟨x, hx⟩ := linkLayerHom'_surjective hL g
  have hπT : ∀ y (hy : y ∈ T₀), linkLayerHom' hL ⟨y, hTΛ hy⟩ ∈ T := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    exact ⟨⟨y, linkLayer_le_layerY hL (hTΛ hy)⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hTπ : ∀ τ ∈ T, ∃ y, ∃ hy : y ∈ T₀, linkLayerHom' hL ⟨y, hTΛ hy⟩ = τ := by
    intro τ hτ
    obtain ⟨y₀, hy₀, e⟩ := Subgroup.mem_subgroupOf.mp hτ
    exact ⟨y₀, Subgroup.mem_subgroupOf.mp hy₀, Subtype.ext e⟩
  have hker : ∀ w : ↥(linkLayer R t), linkLayerHom' hL w = 1 →
      (w : Y) ∈ oddCoreOf (linkLayer R t) := by
    intro w hw
    have h1 : w ∈ (linkLayerHom' hL).ker := hw
    rw [ker_linkLayerHom hL] at h1
    exact ⟨w, h1, rfl⟩
  have hker' : ∀ w : ↥(linkLayer R t), (w : Y) ∈ oddCoreOf (linkLayer R t) →
      linkLayerHom' hL w = 1 := by
    intro w hw
    obtain ⟨w', hw', e⟩ := hw
    obtain rfl : w' = w := Subtype.ext e
    have h1 : w' ∈ (linkLayerHom' hL).ker := by rw [ker_linkLayerHom hL]; exact hw'
    exact h1
  have hxw : linkLayerHom' hL (x * ⟨u, huΛ⟩ * x⁻¹) = g * z * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hx]
  refine hs.exists_s_of_mod x.2 (fun y hy => ?_) (fun y hy hyO => ?_)
  · have h1 : g * z * g⁻¹ * linkLayerHom' hL ⟨y, hTΛ hy⟩ * (g * z * g⁻¹)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hgN _).mp (hπT y hy)
    obtain ⟨y', hy', e⟩ := hTπ _ h1
    refine ⟨y', hy', hker ((x * ⟨u, huΛ⟩ * x⁻¹) * ⟨y, hTΛ hy⟩ * (x * ⟨u, huΛ⟩ * x⁻¹)⁻¹ *
      ⟨y', hTΛ hy'⟩⁻¹) ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxw, e]
    group
  · have h1 := hker' ((x * ⟨u, huΛ⟩ * x⁻¹) * ⟨y, hTΛ hy⟩ * (x * ⟨u, huΛ⟩ * x⁻¹)⁻¹ *
      ⟨y, hTΛ hy⟩⁻¹) hyO
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxw] at h1
    have hc : linkLayerHom' hL ⟨y, hTΛ hy⟩ * (g * z * g⁻¹) =
        (g * z * g⁻¹) * linkLayerHom' hL ⟨y, hTΛ hy⟩ := by
      have h2 := mul_eq_one_iff_eq_inv.mp h1
      rw [inv_inv] at h2
      calc linkLayerHom' hL ⟨y, hTΛ hy⟩ * (g * z * g⁻¹)
          = g * z * g⁻¹ * linkLayerHom' hL ⟨y, hTΛ hy⟩ * (g * z * g⁻¹)⁻¹ * (g * z * g⁻¹) := by
            rw [h2]
        _ = (g * z * g⁻¹) * linkLayerHom' hL ⟨y, hTΛ hy⟩ := by group
    have h2 := hgC _ (hπT y hy) hc
    have h3 : y * y ∈ oddCoreOf (linkLayer R t) :=
      hker (⟨y, hTΛ hy⟩ * ⟨y, hTΛ hy⟩) (by rw [map_mul]; exact h2)
    have h4 : y * y ∈ T₀ ⊓ oddCoreOf (linkLayer R t) := ⟨T₀.mul_mem hy hy, h3⟩
    rw [S1916.inf_oddCoreOf_eq_bot hs.hT₀.2.1] at h4
    exact h4

theorem Z2Set.sPropSec_of_s (hs : Z2Set n R S t J u R₀ T₀ P) {s : Y}
    (hsa : s ∈ Subgroup.centralizer ({t * u} : Set Y)) (hs2 : s * s = 1)
    (hsR : R₀ ≤ Subgroup.centralizer ({s} : Set Y)) (hsT : s ∈ Subgroup.normalizer (T₀ : Set Y))
    (hsZ : ∀ x ∈ T₀, x * s = s * x → x * x = 1) :
    SPropSec (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) J
      (secAct hs.large.datum.hypOmegaGen.conjInvariant hsa) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := hs.large.datum.hypOmegaGen
  have hcl : ConjInvariant Ω := hΩ.conjInvariant
  have hyY1 := mem_normalizer_layerY hcl hsa
  obtain ⟨W, hs8⟩ := hs.exists_std8
  have hXK : XMem Ω (t * u) (tightCore R) := hs8.xMem_K
  have hXJ : XMem Ω (t * u) J := hs8.xMem_J
  have huT : u ∈ T₀ := T3.mem_of_isPGroup hs.hu hs.hT₀.1 hs.hT₀.2.1
    (by rw [hs.card_sylow hs.hJ.1 hs.hT₀]; norm_num)
  have hsu : s * u * s⁻¹ = u := by
    have h1 : s * u * s⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp hsT u).mp huT
    have h2 : s * u * s⁻¹ * (s * u * s⁻¹) = 1 := by
      calc s * u * s⁻¹ * (s * u * s⁻¹) = s * (u * u) * s⁻¹ := by group
        _ = 1 := by rw [hs.hu.sq]; group
    rcases hs.hu.unique _ (hs.hT₀.1 h1) h2 with h | h
    · exfalso
      apply hs.hu.ne_one
      calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hsJ : conjSub s J = J := by
    have hsC : s ∈ Subgroup.centralizer ({u} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc s * u = s * u * s⁻¹ * s := by group
        _ = u * s := by rw [hsu]
    exact mem_normalizer_iff_conjSub_eq.mp
      ((TightLargeHypR.typeRFam hs.large).tight J hs.hJ.1 u hs.hu hsC)
  have hRa : R₀ ≤ Subgroup.centralizer ({t * u} : Set Y) :=
    Q3CL.T8R.Loc.le_centralizer_mul hs8.toStd8Core
  have hTa : T₀ ≤ Subgroup.centralizer ({t * u} : Set Y) := by
    intro x hx
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution
        hs.large.datum.isUniqueInvolution_core (hs.hT₀N hx))
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution hs.hu
        (Subgroup.le_normalizer (hs.hT₀.1 hx)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (t * u) = (x * t) * u := by group
      _ = t * (x * u) := by rw [hxt]; group
      _ = t * u * x := by rw [hxu]; group
  have hRc : IsSylow2In R₀ (coreAt (t * u) (tightCore R)) :=
    (isSylow2In_coreAt_iff hXK).mpr ⟨hs.hR₀, hRa⟩
  have hTc : IsSylow2In T₀ (coreAt (t * u) J) :=
    (isSylow2In_coreAt_iff hXJ).mpr ⟨hs.hT₀, hTa⟩
  have hTY : T₀ ≤ layerY Ω (t * u) := hTc.1.trans (coreAt_le_layerY hXJ)
  have hRbar := isSylow2In_map_mk odd_natCard_oddCore_layerY
    (hRc.subgroupOf (coreAt_le_layerY hXK))
  have hTbar := isSylow2In_map_mk odd_natCard_oddCore_layerY
    (hTc.subgroupOf (coreAt_le_layerY hXJ))
  refine ⟨?_, fun M hM => ?_, ⟨_, hRbar, fun w hw => ?_⟩, fun k hk => ?_,
    ⟨_, hTbar, fun w hw => ?_, fun w hw hfix => ?_⟩⟩
  · show s26Act (layerY Ω (t * u)) ⟨s, hyY1⟩ * s26Act (layerY Ω (t * u)) ⟨s, hyY1⟩ = 1
    rw [← map_mul]
    have e : (⟨s, hyY1⟩ * ⟨s, hyY1⟩ : ↥(Subgroup.normalizer
        ((layerY Ω (t * u) : Subgroup Y) : Set Y))) = 1 := Subtype.ext hs2
    rw [e, map_one]
  · obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM
    rw [← secImg_conjSub_eq_map hcl hsa L]
    exact secImg_mem (XMem.conj' hcl hL hsa)
  · obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hw
    exact secAct_mk_of_commute hcl hsa r
      (Subgroup.mem_centralizer_singleton_iff.mp (hsR (Subgroup.mem_subgroupOf.mp hr))).symm
  · have e := secImg_conjSub_eq_map hcl hsa J
    rw [hsJ] at e
    rw [e]
    exact Subgroup.mem_map_of_mem _ hk
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    have hxT : (x : Y) ∈ T₀ := Subgroup.mem_subgroupOf.mp hx
    have hsx : s * (x : Y) * s⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp hsT _).mp hxT
    rw [secAct_mk_conj hcl hsa x (hTY hsx)]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hsx)
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    have hxT : (x : Y) ∈ T₀ := Subgroup.mem_subgroupOf.mp hx
    have hsx : s * (x : Y) * s⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp hsT _).mp hxT
    rw [secAct_mk_conj hcl hsa x (hTY hsx)] at hfix
    have hq := (QuotientGroup.eq (s := classicalInvolutionOddCore ↥(layerY Ω (t * u)))).mp hfix
    have h1 := eq_one_of_mem_oddCore hs.hT₀.2.1 _ (T₀.mul_mem (T₀.inv_mem hsx) hxT) hq
    have h2 : s * (x : Y) * s⁻¹ = x := by
      have h3 : (s * (x : Y) * s⁻¹)⁻¹ * x = 1 := h1
      calc s * (x : Y) * s⁻¹ = s * (x : Y) * s⁻¹ * ((s * (x : Y) * s⁻¹)⁻¹ * x) := by
            rw [h3, mul_one]
        _ = x := by group
    have hxs : (x : Y) * s = s * x := by
      calc (x : Y) * s = (s * x * s⁻¹) * s := by rw [h2]
        _ = s * x := by group
    have hxx := hsZ _ hxT hxs
    rw [← map_mul]
    have e : x * x = 1 := Subtype.ext hxx
    rw [e, map_one]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
