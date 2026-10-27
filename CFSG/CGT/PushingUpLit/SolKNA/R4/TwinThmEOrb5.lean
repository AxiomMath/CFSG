module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOrb3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf23Orb4Data

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

namespace ThmE

section Orb4NonCommute

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem goodFourD_of_noncommute_of' (hΩ : HypOmegaGen Ω)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hcmm : ∀ (M₁ M₂ R₁ R₂ : Subgroup G), M₁ ∈ Ω → M₂ ∈ Ω → M₁ ≠ M₂ → R₁ ∈ RSet Ω → R₁ ≤ M₁ →
      R₁ ≤ (S : Subgroup G) → R₂ ∈ RSet Ω → R₂ ≤ M₂ → R₂ ≤ (S : Subgroup G) →
      ∀ x ∈ M₁ ⊓ (S : Subgroup G), ∀ y ∈ M₂ ⊓ (S : Subgroup G), x * y = y * x)
    (hfour : ∀ {M R₀ : Subgroup G}, M ∈ Ω → R₀ ∈ RSet Ω → R₀ ≤ M → R₀ ≤ (S : Subgroup G) →
      ∃ u ∈ M ⊓ W, orderOf u = 4)
    (hKS : K ⊓ (S : Subgroup G) = R) (hquat : IsQuatSub R)
    (hnt : ∀ {x : G}, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≠ ⊤)
    (hZ0 : ∀ {K₃ K₄ R₃ R₄ : Subgroup G}, K₃ ∈ twinSet Ω K → K₄ ∈ twinSet Ω K → K₄ ≠ K₃ →
      R₃ ∈ RSet Ω → R₃ ≤ K₃ → R₃ ≤ (S : Subgroup G) → R₄ ∈ RSet Ω → R₄ ≤ K₄ →
      R₄ ≤ (S : Subgroup G) → K₄ ∈ twinSet Ω K₃ → ∀ x : G, x ≠ 1 → x * x = 1 →
      IsPGroup 2 (Subgroup.zpowers x) →
      R₃ ⊔ R₄ ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) →
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≠ ⊤ →
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ H)
    (hK : K ∈ Ω) (hRR : R ∈ RSet Ω) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G))
    (hWS : W ≤ (S : Subgroup G)) (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    {K' R' : Subgroup G} (hK'tw : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hR' : R' ∈ RSet Ω)
    (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) (hKS' : K' ⊓ (S : Subgroup G) = R') {z g t : G} (hz : IsUniqueInvolution K z)
    (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t)
    (htt : ∃ (B : Subgroup G) (b : G) (g' : G), B ≤ (S : Subgroup G) ∧
      B ≤ Subgroup.centralizer ({t} : Set G) ∧ IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧
      b = z * (t * z * t⁻¹) ∧ b ∈ W ∧ Subgroup.centralizer ({b} : Set G) ≤ H ∧
      t = g' * z * g'⁻¹ ∧ g' ∉ H ∧ (∀ β ∈ B, g'⁻¹ * β * g' ∈ (S : Subgroup G)) ∧
      ∃ β₃ ∈ B, ∃ β₄ ∈ B, conjSub (g'⁻¹ * β₃ * g') K ≠ conjSub (g'⁻¹ * β₄ * g') K ∧
        conjSub (g'⁻¹ * β₃ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₃ * g') K ≠ K' ∧
        conjSub (g'⁻¹ * β₄ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₄ * g') K ≠ K') :
    TwinThmEW.GoodFourWD (S : Subgroup G) H W t := by
  classical
  classical
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hz' : IsUniqueInvolution K' z := by
    obtain ⟨-, z', hz'K, hz'K'⟩ := hK'tw
    have := hz.eq hz'K
    rwa [← this] at hz'K'
  obtain ⟨B, b, g', hBS, hBt, hBb, hB8, hbdef, hbW, hbH, ht', hg'H, hBg', β₃, hβ₃, β₄, hβ₄,
    hne34, hK₃K, hK₃K', hK₄K, hK₄K'⟩ := htt
  have ht2 : t * t = 1 := by
    rw [ht]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hz2 := hz.sq
  have hRS' : R ≤ (S : Subgroup G) := hRS

  have hconjdata : ∀ s : G, s ∈ (S : Subgroup G) → ∀ M R₀ : Subgroup G, M ∈ Ω → R₀ ∈ RSet Ω →
      R₀ ≤ M → R₀ ≤ (S : Subgroup G) → conjSub s M ∈ Ω ∧ conjSub s R₀ ∈ RSet Ω ∧
        conjSub s R₀ ≤ conjSub s M ∧ conjSub s R₀ ≤ (S : Subgroup G) :=
    fun s hs M R₀ hM hR₀ hR₀M hR₀S => ⟨hΩ.conjInvariant s M hM, RSet.conj hΩ.conjInvariant hR₀ s,
      conjSub_mono hR₀M, conjSub_le_of_mem hs hR₀S⟩

  obtain ⟨zt, hzt⟩ : ∃ zt, zt = t * z * t⁻¹ := ⟨_, rfl⟩
  have hzt1 : IsUniqueInvolution (conjSub t K) zt := hzt ▸ hz.conj t
  have hz't1 : IsUniqueInvolution (conjSub t K') zt := hzt ▸ hz'.conj t
  have hzzt : z ≠ zt := by
    intro h'
    apply hnc
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [← hzt, ← h']
  obtain ⟨hKtΩ, hRtmem, hRtK, hRtS⟩ := hconjdata t htS K R hK hRR hRK hRS
  obtain ⟨hK'tΩ, hR'tmem, hR'tK, hR'tS⟩ := hconjdata t htS K' R' hK'Ω hR' hR'K' hR'S

  have hsz : ∀ β ∈ B, (g'⁻¹ * β * g') * z * (g'⁻¹ * β * g')⁻¹ = z := by
    intro β hβ
    have hβt : β * t = t * β := Subgroup.mem_centralizer_singleton_iff.mp (hBt hβ)
    calc (g'⁻¹ * β * g') * z * (g'⁻¹ * β * g')⁻¹
        = g'⁻¹ * (β * (g' * z * g'⁻¹) * β⁻¹) * g' := by group
      _ = g'⁻¹ * (β * t * β⁻¹) * g' := by rw [← ht']
      _ = g'⁻¹ * (t * β * β⁻¹) * g' := by rw [hβt]
      _ = g'⁻¹ * t * g' := by group
      _ = z := by rw [ht']; group
  have hs₃S := hBg' β₃ hβ₃
  have hs₄S := hBg' β₄ hβ₄
  have hs₃z := hsz β₃ hβ₃
  have hs₄z := hsz β₄ hβ₄
  generalize g'⁻¹ * β₃ * g' = s₃ at hne34 hK₃K hK₃K' hs₃S hs₃z
  generalize g'⁻¹ * β₄ * g' = s₄ at hne34 hK₄K hK₄K' hs₄S hs₄z
  obtain ⟨hK₃Ω, hR₃mem, hR₃K, hR₃S⟩ := hconjdata s₃ hs₃S K R hK hRR hRK hRS
  obtain ⟨hK₄Ω, hR₄mem, hR₄K, hR₄S⟩ := hconjdata s₄ hs₄S K R hK hRR hRK hRS
  have hK₃z : IsUniqueInvolution (conjSub s₃ K) z := by
    have := hz.conj s₃
    rwa [hs₃z] at this
  have hK₄z : IsUniqueInvolution (conjSub s₄ K) z := by
    have := hz.conj s₄
    rwa [hs₄z] at this

  obtain ⟨u, huKW, hu4⟩ := hfour hK hRR hRK hRS
  obtain ⟨u', hu'KW, hu'4⟩ := hfour hK'Ω hR' hR'K' hR'S
  obtain ⟨ut, hut⟩ : ∃ ut, ut = t * u * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨u't, hu't⟩ : ∃ u't, u't = t * u' * t⁻¹ := ⟨_, rfl⟩
  have huS : u ∈ (S : Subgroup G) := hWS huKW.2
  have hu'S : u' ∈ (S : Subgroup G) := hWS hu'KW.2
  have hutS : ut ∈ (S : Subgroup G) := by
    rw [hut]; exact S.mul_mem (S.mul_mem htS huS) (S.inv_mem htS)
  have hu'tS : u't ∈ (S : Subgroup G) := by
    rw [hu't]; exact S.mul_mem (S.mul_mem htS hu'S) (S.inv_mem htS)
  have hutK : ut ∈ conjSub t K := hut ▸ conj_mem_conjSub huKW.1
  have hu'tK : u't ∈ conjSub t K' := hu't ▸ conj_mem_conjSub hu'KW.1
  have hu2 : u * u = z := sq_eq_of_orderOf_four hz huKW.1 hu4
  have hu'2 : u' * u' = z := sq_eq_of_orderOf_four hz' hu'KW.1 hu'4
  have hut2 : ut * ut = zt := by
    rw [hut, hzt, ← hu2]; group
  have hu't2 : u't * u't = zt := by
    rw [hu't, hzt, ← hu'2]; group
  have ht1 : t * u * t⁻¹ = ut := hut.symm
  have ht3 : t * u' * t⁻¹ = u't := hu't.symm
  have ht2' : t * ut * t⁻¹ = u := by
    rw [hut]
    have : t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
    rw [this, ht2]; group
  have ht4 : t * u't * t⁻¹ = u' := by
    rw [hu't]
    have : t * (t * u' * t⁻¹) * t⁻¹ = (t * t) * u' * (t * t)⁻¹ := by group
    rw [this, ht2]; group

  have hKK' : K ≠ K' := Ne.symm hne
  have hKKt : K ≠ conjSub t K := ne_of_involution_ne hz hzt1 hzzt
  have hKK't : K ≠ conjSub t K' := ne_of_involution_ne hz hz't1 hzzt
  have hK'Kt : K' ≠ conjSub t K := ne_of_involution_ne hz' hzt1 hzzt
  have hK'K't : K' ≠ conjSub t K' := ne_of_involution_ne hz' hz't1 hzzt
  have hKtK't : conjSub t K ≠ conjSub t K' := fun h' => hne ((conjSub_inj t).mp h').symm

  have huut : u * ut = ut * u :=
    hcmm K (conjSub t K) R (conjSub t R) hK hKtΩ hKKt hRR hRK hRS hRtmem hRtK hRtS u
      ⟨huKW.1, huS⟩ ut ⟨hutK, hutS⟩
  have huu' : u * u' = u' * u :=
    hcmm K K' R R' hK hK'Ω hKK' hRR hRK hRS hR' hR'K' hR'S u ⟨huKW.1, huS⟩ u'
      ⟨hu'KW.1, hu'S⟩
  have huu't : u * u't = u't * u :=
    hcmm K (conjSub t K') R (conjSub t R') hK hK'tΩ hKK't hRR hRK hRS hR'tmem hR'tK
      hR'tS u ⟨huKW.1, huS⟩ u't ⟨hu'tK, hu'tS⟩
  have hutu' : ut * u' = u' * ut :=
    hcmm (conjSub t K) K' (conjSub t R) R' hKtΩ hK'Ω (Ne.symm hK'Kt) hRtmem hRtK hRtS hR' hR'K'
      hR'S ut ⟨hutK, hutS⟩ u' ⟨hu'KW.1, hu'S⟩
  have hutu't : ut * u't = u't * ut :=
    hcmm (conjSub t K) (conjSub t K') (conjSub t R) (conjSub t R') hKtΩ hK'tΩ hKtK't hRtmem hRtK
      hRtS hR'tmem hR'tK hR'tS ut ⟨hutK, hutS⟩ u't ⟨hu'tK, hu'tS⟩
  have hu'u't : u' * u't = u't * u' :=
    hcmm K' (conjSub t K') R' (conjSub t R') hK'Ω hK'tΩ hK'K't hR' hR'K' hR'S hR'tmem hR'tK
      hR'tS u' ⟨hu'KW.1, hu'S⟩ u't ⟨hu'tK, hu'tS⟩

  have hu_inf : u ∈ K ⊓ (S : Subgroup G) := ⟨huKW.1, huS⟩
  have huR : u ∈ R := by
    rw [← hKS]
    exact hu_inf
  obtain ⟨y, hyR, hy1⟩ : ∃ y ∈ R, y * u ≠ u * y := by
    by_contra hcon
    push Not at hcon
    have := hquat.sq_eq_one_of_central huR
      (fun y hy => (hcon y hy).symm)
    exact hz.ne_one (hu2 ▸ this)
  have hyin : y ∈ K ⊓ (S : Subgroup G) := ⟨hRK hyR, hRS hyR⟩
  have hy2 : y * ut = ut * y :=
    hcmm K (conjSub t K) R (conjSub t R) hK hKtΩ hKKt hRR hRK hRS hRtmem hRtK hRtS y
      hyin ut ⟨hutK, hutS⟩
  have hy3 : y * u' = u' * y :=
    hcmm K K' R R' hK hK'Ω hKK' hRR hRK hRS hR' hR'K' hR'S y hyin u'
      ⟨hu'KW.1, hu'S⟩
  have hy4 : y * u't = u't * y :=
    hcmm K (conjSub t K') R (conjSub t R') hK hK'tΩ hKK't hRR hRK hRS hR'tmem hR'tK
      hR'tS y hyin u't ⟨hu'tK, hu'tS⟩
  have hb : b = z * zt := by rw [hbdef, hzt]
  have hb2 : b * b = 1 := hBb.sq
  obtain ⟨he2, he1, he3, hebc, het⟩ := core4 hu2 hut2 hu'2 hu't2 huut huu' huu't hutu' hutu't
    hu'u't hb hb2 ht1 ht2' ht3 ht4 hy1 hy2 hy3 hy4
  obtain ⟨e, he⟩ : ∃ e, e = (u * ut) * (u' * u't)⁻¹ := ⟨_, rfl⟩
  rw [← he] at he2 he1 he3 hebc het
  have hutW : ut ∈ W := by
    rw [hut]
    have := conj_mem_conjSub (n := t) huKW.2
    rwa [hWn t htS] at this
  have hu'tW : u't ∈ W := by
    rw [hu't]
    have := conj_mem_conjSub (n := t) hu'KW.2
    rwa [hWn t htS] at this
  have heW : e ∈ W := by
    rw [he]
    exact W.mul_mem (W.mul_mem huKW.2 hutW) (W.inv_mem (W.mul_mem hu'KW.2 hu'tW))

  have hcent : ∀ M R₀ : Subgroup G, M ∈ Ω → R₀ ∈ RSet Ω → R₀ ≤ M → R₀ ≤ (S : Subgroup G) →
      M ≠ K → M ≠ conjSub t K → M ≠ K' → M ≠ conjSub t K' →
      ∀ y' ∈ R₀, y' * e = e * y' ∧ y' * b = b * y' := by
    intro M R₀ hM hR₀ hR₀M hR₀S hMK hMKt hMK' hMK't y' hy'
    have hy'in : y' ∈ M ⊓ (S : Subgroup G) := ⟨hR₀M hy', hR₀S hy'⟩
    have cu : Commute y' u :=
      hcmm M K R₀ R hM hK hMK hR₀ hR₀M hR₀S hRR hRK hRS y' hy'in u hu_inf
    have cut : Commute y' ut :=
      hcmm M (conjSub t K) R₀ (conjSub t R) hM hKtΩ hMKt hR₀ hR₀M hR₀S hRtmem hRtK hRtS y' hy'in
        ut ⟨hutK, hutS⟩
    have cu' : Commute y' u' :=
      hcmm M K' R₀ R' hM hK'Ω hMK' hR₀ hR₀M hR₀S hR' hR'K' hR'S y' hy'in u' ⟨hu'KW.1, hu'S⟩
    have cu't : Commute y' u't :=
      hcmm M (conjSub t K') R₀ (conjSub t R') hM hK'tΩ hMK't hR₀ hR₀M hR₀S hR'tmem hR'tK hR'tS
        y' hy'in u't ⟨hu'tK, hu'tS⟩
    refine ⟨?_, ?_⟩
    · rw [he]
      exact (((cu.mul_right cut).mul_right ((cu'.mul_right cu't).inv_right))).eq
    · rw [hb, ← hu2, ← hut2]
      exact ((cu.mul_right cu).mul_right (cut.mul_right cut)).eq

  have hK₃tw : conjSub s₃ K ∈ twinSet Ω K := ⟨hK₃Ω, z, hz, hK₃z⟩
  have hK₄tw : conjSub s₄ K ∈ twinSet Ω K := ⟨hK₄Ω, z, hz, hK₄z⟩
  have hK₄tw' : conjSub s₄ K ∈ twinSet Ω (conjSub s₃ K) := ⟨hK₄Ω, z, hK₃z, hK₄z⟩
  have hZ : ∀ x : G, x ≠ 1 → x * x = 1 → (∀ y' ∈ conjSub s₃ R, y' * x = x * y') →
      (∀ y' ∈ conjSub s₄ R, y' * x = x * y') → Subgroup.centralizer ({x} : Set G) ≤ H := by
    intro x hx1 hx2 hc3 hc4
    have hA2 : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_two_of_sq hx1 hx2]; norm_num)
    have hsup : conjSub s₃ R ⊔ conjSub s₄ R ≤
        Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq_singleton]
      refine sup_le (fun y' hy' => ?_) (fun y' hy' => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hc3 y' hy'
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hc4 y' hy'
    have hXne : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≠ ⊤ := by
      rw [centralizer_zpowers_eq_singleton]
      exact hnt hx1
    have := hZ0 hK₃tw hK₄tw (Ne.symm hne34) hR₃mem hR₃K hR₃S hR₄mem hR₄K hR₄S hK₄tw' x hx1 hx2 hA2
      hsup hXne
    rwa [centralizer_zpowers_eq_singleton] at this
  have hne3 : ∀ M : Subgroup G, M = conjSub s₃ K → M ≠ conjSub t K ∧ M ≠ conjSub t K' := by
    rintro M rfl
    exact ⟨ne_of_involution_ne hK₃z hzt1 hzzt, ne_of_involution_ne hK₃z hz't1 hzzt⟩
  have hne4 : ∀ M : Subgroup G, M = conjSub s₄ K → M ≠ conjSub t K ∧ M ≠ conjSub t K' := by
    rintro M rfl
    exact ⟨ne_of_involution_ne hK₄z hzt1 hzzt, ne_of_involution_ne hK₄z hz't1 hzzt⟩
  have hc3 := hcent (conjSub s₃ K) (conjSub s₃ R) hK₃Ω hR₃mem hR₃K hR₃S hK₃K
    (hne3 _ rfl).1 hK₃K' (hne3 _ rfl).2
  have hc4 := hcent (conjSub s₄ K) (conjSub s₄ R) hK₄Ω hR₄mem hR₄K hR₄S hK₄K
    (hne4 _ rfl).1 hK₄K' (hne4 _ rfl).2
  have hbt : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp (hBt hBb.mem)
  have hte : e * t = t * e := (mul_inv_eq_iff_eq_mul.mp het).symm
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbe1 : b * e ≠ 1 := by
    intro h'
    apply he3
    have := eq_inv_of_mul_eq_one_right h'
    rw [this, hbi]
  have hbe2 : (b * e) * (b * e) = 1 := by
    calc (b * e) * (b * e) = b * (e * b) * e := by group
      _ = b * (b * e) * e := by rw [hebc]
      _ = (b * b) * (e * e) := by group
      _ = 1 := by rw [hb2, he2, one_mul]
  have hbet : (b * e) * t = t * (b * e) := by
    calc (b * e) * t = b * (e * t) := by group
      _ = b * (t * e) := by rw [hte]
      _ = (b * t) * e := by group
      _ = (t * b) * e := by rw [hbt]
      _ = t * (b * e) := by group
  have hu'R : u' ∈ R' := by
    rw [← hKS']
    exact ⟨hu'KW.1, hu'S⟩
  have hshape : TwinThmEW.D4Shape (S : Subgroup G) t b e := by
    have hne₁₂ : R ≠ R' := orb4_rset_ne_of_ne hΩ hK hK'Ω hKK' hRR hRK hR'K'
    have hne₁₃ : R ≠ conjSub t R := orb4_rset_ne_of_ne hΩ hK hKtΩ hKKt hRR hRK (conjSub_mono hRK)
    have hne₁₄ : R ≠ conjSub t R' := orb4_rset_ne_of_ne hΩ hK hK'tΩ hKK't hRR hRK (conjSub_mono hR'K')
    have hne₂₃ : R' ≠ conjSub t R := orb4_rset_ne_of_ne hΩ hK'Ω hKtΩ hK'Kt hR' hR'K' (conjSub_mono hRK)
    have hne₂₄ : R' ≠ conjSub t R' :=
      orb4_rset_ne_of_ne hΩ hK'Ω hK'tΩ hK'K't hR' hR'K' (conjSub_mono hR'K')
    have hshape0 := shape_noncommute' hΩ S hWn hWab hK hK'Ω hKK' hRR hR' hRK hR'K' hRS hR'S htS ht2
      hne₁₂ hne₁₃ hne₁₄ hne₂₃ hne₂₄ hz hz' huR huKW.2 hu4 hu'R hu'KW.2 hu'4 hu2 hu'2
      (fun h' => hzzt (by rw [hzt]; exact h'.symm))
    rw [hb, he, hzt, hut, hu't]
    exact hshape0
  refine ⟨b, e, ⟨hBb.ne_one, hb2, hbt, hbH⟩,
    ⟨he1, he2, hte, hZ e he1 he2 (fun y' hy' => (hc3 y' hy').1) (fun y' hy' => (hc4 y' hy').1)⟩,
    ⟨hbe1, hbe2, hbet, hZ (b * e) hbe1 hbe2 ?_ ?_⟩, hebc.symm, hbW, heW, hshape⟩
  · intro y' hy'
    obtain ⟨h1, h2⟩ := hc3 y' hy'
    calc y' * (b * e) = (y' * b) * e := by group
      _ = (b * y') * e := by rw [h2]
      _ = b * (y' * e) := by group
      _ = b * (e * y') := by rw [h1]
      _ = (b * e) * y' := by group
  · intro y' hy'
    obtain ⟨h1, h2⟩ := hc4 y' hy'
    calc y' * (b * e) = (y' * b) * e := by group
      _ = (b * y') * e := by rw [h2]
      _ = b * (y' * e) := by group
      _ = b * (e * y') := by rw [h1]
      _ = (b * e) * y' := by group

end Orb4NonCommute

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
