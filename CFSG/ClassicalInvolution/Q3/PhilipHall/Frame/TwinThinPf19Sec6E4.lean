module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6Lift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSplitModel
public import CFSG.ClassicalInvolution.Q3.TL3T50

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

set_option linter.unusedSectionVars false

namespace TwinThin

section GenericE4

variable {Y : Type} [Group Y] [Finite Y]

theorem commutes_of_le_gen {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {J J' P : Subgroup Y} (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) (hne : J ≠ J') (hP : IsPGroup 2 P)
    (hJP : J ≤ P) (hJ'P : J' ≤ P) : ∀ x ∈ J, ∀ y ∈ J', x * y = y * x := by
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  exact Q3CP.l67Gen Y Ω hΩ T J (mem_RSet_of_isPGroup hJ (h2 J hJ)) J'
    (mem_RSet_of_isPGroup hJ' (h2 J' hJ')) (hJP.trans hPT) (hJ'P.trans hPT) hne

theorem inf_normal_eq_bot {R N : Subgroup Y} {t : Y} (hR2 : IsPGroup 2 R)
    (ht : IsUniqueInvolution R t) (htN : t ∉ N) : ∀ x ∈ R, x ∈ N → x = 1 := by
  intro x hxR hxN
  by_contra hx1
  have hA : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    hR2.to_le (Subgroup.zpowers_le.mpr hxR)
  have h2 : 2 ≤ Nat.card ↥(Subgroup.zpowers x) := by
    rw [Nat.card_zpowers]
    have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    have h0 : 0 < orderOf x := orderOf_pos x
    omega
  have htA := AscQuot.mem_of_uniqueInvolution ht (Subgroup.zpowers_le.mpr hxR) hA h2
  exact htN ((Subgroup.zpowers_le.mpr hxN) htA)

theorem normal_cent_of_inf_bot {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {R : Subgroup Y} (hR : R ∈ Ω) {N : Subgroup Y} [N.Normal]
    (hN2 : IsPGroup 2 N) (hRN : ∀ x ∈ R, x ∈ N → x = 1) : ∀ n ∈ N, ∀ r ∈ R, n * r = r * n := by
  intro n hn r hr
  have hR2 := h2 R hR
  have hRle : R ≤ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr ‹N.Normal›]
    exact le_top
  have hP : IsPGroup 2 ↥(N ⊔ R) := hN2.to_sup_of_normal_left' hR2 hRle
  have hcommN : ∀ x : Y, n * x * n⁻¹ * x⁻¹ ∈ N := by
    intro x
    have h1 : x * n⁻¹ * x⁻¹ ∈ N := ‹N.Normal›.conj_mem n⁻¹ (N.inv_mem hn) x
    have : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
    rw [this]
    exact N.mul_mem hn h1
  by_cases hM : conjSub n R = R
  · have hmem : n * r * n⁻¹ ∈ R := by
      have : n * r * n⁻¹ ∈ conjSub n R := conj_mem_conjSub hr
      rwa [hM] at this
    have h3 : n * r * n⁻¹ * r⁻¹ ∈ R := R.mul_mem hmem (R.inv_mem hr)
    have h4 := hRN _ h3 (hcommN r)
    calc n * r = (n * r * n⁻¹ * r⁻¹) * (r * n) := by group
      _ = r * n := by rw [h4, one_mul]
  · exfalso
    have hMΩ : conjSub n R ∈ Ω := hΩ.conjInvariant n R hR
    have hMle : conjSub n R ≤ N ⊔ R := by
      rintro _ ⟨x, hx, rfl⟩
      have e : (MulAut.conj n).toMonoidHom x = (n * x * n⁻¹ * x⁻¹) * x := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
        group
      rw [e]
      exact Subgroup.mul_mem_sup (hcommN x) hx
    have hc := commutes_of_le_gen hΩ h2 hMΩ hR hM hP hMle le_sup_right
    obtain ⟨a, ha, b, hb, hab⟩ := noncomm_of_mem hΩ hR
    apply hab
    have h1 := hc (n * a * n⁻¹) (conj_mem_conjSub ha) b hb
    have hcb : n * a * n⁻¹ * a⁻¹ ∈ N := hcommN a
    have e1 : a * b * a⁻¹ * b⁻¹ = (n * a * n⁻¹ * a⁻¹)⁻¹ * (b * (n * a * n⁻¹ * a⁻¹) * b⁻¹) := by
      have : n * a * n⁻¹ * b = b * (n * a * n⁻¹) := h1
      calc a * b * a⁻¹ * b⁻¹
          = (n * a * n⁻¹ * a⁻¹)⁻¹ * ((n * a * n⁻¹) * b) * a⁻¹ * b⁻¹ := by group
        _ = (n * a * n⁻¹ * a⁻¹)⁻¹ * (b * (n * a * n⁻¹)) * a⁻¹ * b⁻¹ := by rw [this]
        _ = _ := by group
    have h2' : a * b * a⁻¹ * b⁻¹ ∈ N := by
      rw [e1]
      exact N.mul_mem (N.inv_mem hcb) (‹N.Normal›.conj_mem _ hcb b)
    have h3 : a * b * a⁻¹ * b⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
    have h4 := hRN _ h3 h2'
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h4, one_mul]

theorem member_eq_of_le_sup {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {R M N : Subgroup Y} [N.Normal] (hR : R ∈ Ω) (hM : M ∈ Ω)
    (hq : Nonempty (↥R ≃* QuaternionGroup 2)) {t : Y} (ht : IsUniqueInvolution R t)
    (hN2 : IsPGroup 2 N) (hNc : ∀ n ∈ N, ∀ y : Y, n * y = y * n) (hMle : M ≤ R ⊔ N) :
    M = R := by
  by_contra hne
  have hR2 := h2 R hR
  have hP : IsPGroup 2 ↥(R ⊔ N) := hR2.to_sup_of_normal_right hN2
  have hc := commutes_of_le_gen hΩ h2 hM hR hne hP hMle le_sup_left
  have hdec : ∀ x ∈ M, ∃ r : Y, (r = 1 ∨ r = t) ∧ ∃ n ∈ N, x = r * n := by
    intro x hx
    obtain ⟨r, hr, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hMle hx)
    refine ⟨r, ?_, n, hn, rfl⟩
    refine central_eq_of_q8 hq ht hr fun k hk => ?_
    have h1 := hc (r * n) hx k hk
    have hnk : n * k = k * n := hNc n hn k
    have h3 : r * k * n = k * r * n :=
      calc r * k * n = r * (k * n) := mul_assoc _ _ _
        _ = r * (n * k) := by rw [hnk]
        _ = r * n * k := (mul_assoc _ _ _).symm
        _ = k * (r * n) := h1
        _ = k * r * n := (mul_assoc _ _ _).symm
    exact mul_right_cancel h3
  obtain ⟨a, ha, b, hb, hab⟩ := noncomm_of_mem hΩ hM
  obtain ⟨r₁, hr₁, n₁, hn₁, rfl⟩ := hdec a ha
  obtain ⟨r₂, hr₂, n₂, hn₂, rfl⟩ := hdec b hb
  apply hab
  have hrr : r₁ * r₂ = r₂ * r₁ := by
    rcases hr₁ with rfl | rfl <;> rcases hr₂ with rfl | rfl <;> simp
  calc r₁ * n₁ * (r₂ * n₂) = r₁ * (n₁ * r₂) * n₂ := by group
    _ = r₁ * (r₂ * n₁) * n₂ := by rw [hNc n₁ hn₁ r₂]
    _ = (r₁ * r₂) * (n₁ * n₂) := by group
    _ = (r₂ * r₁) * (n₂ * n₁) := by rw [hrr, hNc n₁ hn₁ n₂ ]
    _ = r₂ * (r₁ * n₂) * n₁ := by group
    _ = r₂ * (n₂ * r₁) * n₁ := by rw [hNc n₂ hn₂ r₁]
    _ = r₂ * n₂ * (r₁ * n₁) := by group

theorem conj_inf_normal_eq_bot {R N : Subgroup Y} [N.Normal] (hRN : ∀ x ∈ R, x ∈ N → x = 1) :
    ∀ K ∈ CoreAssembly.conjClass R, ∀ x ∈ K, x ∈ N → x = 1 := by
  rintro _ ⟨y, rfl⟩ x hx hxN
  have hx' : y⁻¹ * x * y ∈ R := mem_conjSub_iff.mp hx
  have hxN' : y⁻¹ * x * y ∈ N := by
    have := ‹N.Normal›.conj_mem x hxN y⁻¹
    simpa using this
  have h1 := hRN _ hx' hxN'
  calc x = y * (y⁻¹ * x * y) * y⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem exists_split_of_twinE4 {Q : Type} [Group Q] (hE4 : E4SplitModel) {R R' : Subgroup Y} {t : Y}
    (hq : Nonempty (↥R ≃* QuaternionGroup 2)) (hq' : Nonempty (↥R' ≃* QuaternionGroup 2))
    (hR2 : IsPGroup 2 R) (ht : IsUniqueInvolution R t) (hR'conj : R' ∈ CoreAssembly.conjClass R)
    (ht' : IsUniqueInvolution R' t) (hne : R' ≠ R) (hΩ : HypOmegaGen (CoreAssembly.conjClass R))
    (hgen : (⨆ y : Y, conjSub y R) = ⊤) (f : Y →* Q) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker)
    (hLie : CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1)
    (htN : t ∉ f.ker) :
    ∃ w : Y, w ^ 3 = 1 ∧ conjSub w R = R ∧ (∀ y ∈ R', w * y = y * w) ∧
      ∃ r ∈ R, w * r ≠ r * w := by
  classical
  haveI : f.ker.Normal := MonoidHom.normal_ker f
  have h2 : ∀ J ∈ CoreAssembly.conjClass R, IsPGroup 2 J := by
    rintro _ ⟨y, rfl⟩
    exact isPGroup_conjSub y hR2
  have hRmem : R ∈ CoreAssembly.conjClass R := CoreAssembly.mem_conjClass_self R
  have hRN : ∀ x ∈ R, x ∈ f.ker → x = 1 := inf_normal_eq_bot hR2 ht htN
  have hconjN := conj_inf_normal_eq_bot (N := f.ker) hRN
  have hR'N : ∀ x ∈ R', x ∈ f.ker → x = 1 := hconjN R' hR'conj
  have hcentR : ∀ n ∈ f.ker, ∀ r ∈ R, n * r = r * n :=
    normal_cent_of_inf_bot hΩ h2 hRmem hk hRN
  have hNc : ∀ n ∈ f.ker, ∀ y : Y, n * y = y * n := by
    intro n hn y
    have hle : (⨆ y : Y, conjSub y R) ≤ Subgroup.centralizer ({n} : Set Y) := by
      refine iSup_le fun y' x hx => ?_
      have hx' : y'⁻¹ * x * y' ∈ R := mem_conjSub_iff.mp hx
      have hn' : y'⁻¹ * n * y' ∈ f.ker := by
        have := ‹f.ker.Normal›.conj_mem n hn y'⁻¹
        simpa using this
      have h1 := hcentR _ hn' _ hx'
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * n = y' * ((y'⁻¹ * x * y') * (y'⁻¹ * n * y')) * y'⁻¹ := by group
        _ = y' * ((y'⁻¹ * n * y') * (y'⁻¹ * x * y')) * y'⁻¹ := by rw [h1]
        _ = n * x := by group
    have hy : y ∈ Subgroup.centralizer ({n} : Set Y) := hle (hgen ▸ Subgroup.mem_top y)
    exact (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  have hNcenter : f.ker ≤ Subgroup.center Y := fun n hn =>
    Subgroup.mem_center_iff.mpr fun y => (hNc n hn y).symm
  have hNK : ∀ K ∈ CoreAssembly.conjClass R, Odd (Nat.card ↥(f.ker ⊓ K)) := by
    intro K hK
    have : f.ker ⊓ K = ⊥ := eq_bot_iff.mpr fun x hx =>
      (Subgroup.mem_bot).mpr (hconjN K hK x hx.2 hx.1)
    rw [this, Subgroup.card_bot]
    exact odd_one
  have hqbar := QuaternionBridge.CentQ.quotient_hypOmegaGen hΩ f.ker hNcenter hNK
  set φ : Y →* Y ⧸ f.ker := QuotientGroup.mk' f.ker with hφ
  have hkerφ : φ.ker = f.ker := QuotientGroup.ker_mk' f.ker
  have hRb : R ⊓ f.ker = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hRN x hx.1 hx.2)
  have hR'b : R' ⊓ f.ker = ⊥ :=
    eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hR'N x hx.1 hx.2)
  have hKq : Nonempty (↥(R.map φ) ≃* QuaternionGroup 2) :=
    ⟨(AscQuot.quotRestrictEquiv hRb).symm.trans hq.some⟩
  have hs : IsUniqueInvolution (R.map φ) (φ t) := AscQuot.isUniqueInvolution_map_mk hRb ht
  have hs' : IsUniqueInvolution (R'.map φ) (φ t) := AscQuot.isUniqueInvolution_map_mk hR'b ht'
  have hmemΩbar : R.map φ ∈ Set.image (fun K : Subgroup Y => K.map (QuotientGroup.mk' f.ker))
      (CoreAssembly.conjClass R) := ⟨R, hRmem, rfl⟩
  have htwc : ∀ c ∈ Subgroup.centralizer ({φ t} : Set (Y ⧸ f.ker)),
      conjSub c (R.map φ) = R.map φ ∨ ∀ x ∈ R.map φ, ∀ y ∈ conjSub c (R.map φ), x * y = y * x := by
    intro c hc
    by_cases hcK : conjSub c (R.map φ) = R.map φ
    · exact Or.inl hcK
    · right
      have hJ := hqbar.conjInvariant c (R.map φ) hmemΩbar
      have hct : c * φ t * c⁻¹ = φ t := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hc
        rw [this]
        group
      have hsJ : φ t ∈ conjSub c (R.map φ) := by
        have := conj_mem_conjSub (n := c) hs.mem
        rwa [hct] at this
      have hdvd : 2 ∣ Nat.card ↥(R.map φ ⊓ conjSub c (R.map φ)) := by
        have := Subgroup.orderOf_dvd_natCard (R.map φ ⊓ conjSub c (R.map φ))
          (x := φ t) ⟨hs.mem, hsJ⟩
        rwa [orderOf_eq_prime (by rw [pow_two]; exact hs.sq) hs.ne_one] at this
      obtain ⟨h4, h4'⟩ := hqbar.omega4 _ hmemΩbar _ hJ (Ne.symm hcK)
      have h1 := one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
      have hc := h4' (le_antisymm h4 h1)
      have hKb2 : IsPGroup 2 ↥(R.map φ) := hR2.map φ
      rw [OddQuot.oddCoreOf_eq_bot_of_isPGroup hKb2, bot_inf_eq, le_bot_iff] at hc
      intro x hx y hy
      have hmem : ⁅x, y⁆ ∈ ⁅R.map φ, conjSub c (R.map φ)⁆ :=
        Subgroup.commutator_mem_commutator hx hy
      rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
  have hK'conj : R'.map φ ∈ CoreAssembly.conjClass (R.map φ) := by
    obtain ⟨y, rfl⟩ := hR'conj
    exact ⟨φ y, (AscQuot.map_conjSub φ y R).symm⟩
  have hle_of_eq : ∀ {B M : Subgroup Y}, M.map φ ≤ B.map φ → M ≤ B ⊔ f.ker := by
    intro B M hM x hx
    have : x ∈ Subgroup.comap φ (B.map φ) := hM (Subgroup.mem_map_of_mem φ hx)
    rwa [Subgroup.comap_map_eq, hkerφ] at this
  have hne' : R'.map φ ≠ R.map φ := by
    intro h
    apply hne
    exact member_eq_of_le_sup hΩ h2 hRmem hR'conj hq ht hk hNc (hle_of_eq h.le)
  have e : (Y ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hLie' : CFSG.Blueprint.LieModel (Y ⧸ f.ker) .PSp 3 2 1 ∨
      CFSG.Blueprint.LieModel (Y ⧸ f.ker) .POmegaPlus 4 2 1 := by
    rcases hLie with h | h
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h)
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h)
  obtain ⟨c, hc3, hcK, hcK', kbar, hkbar, hkbarne⟩ :=
    hE4 (Y ⧸ f.ker) hLie' (R.map φ) (φ t) hKq hs htwc (R'.map φ) hK'conj hs' hne'
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective f.ker c
  obtain ⟨w, hwφ, hw3⟩ := TC.Thin.exists_lift_pow_three φ (by rwa [hkerφ]) x₀
    (by rw [hφ, hx₀]; exact hc3)
  have hwc : φ w = c := hwφ.trans hx₀
  have hwmem : conjSub w R ∈ CoreAssembly.conjClass R := hΩ.conjInvariant w R hRmem
  have hA : conjSub w R = R := by
    refine member_eq_of_le_sup hΩ h2 hRmem hwmem hq ht hk hNc ?_
    apply hle_of_eq
    rw [AscQuot.map_conjSub, hwc, hcK]
  have hcR' : conjSub c (R'.map φ) = R'.map φ := by
    refine conjSub_eq_of_le_fin ?_
    rintro _ ⟨m, hm, rfl⟩
    have := hcK' m hm
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    rw [this]
    simpa using hm
  have hA' : conjSub w R' = R' := by
    refine member_eq_of_le_sup hΩ h2 hR'conj (hΩ.conjInvariant w R' hR'conj) hq' ht' hk hNc ?_
    apply hle_of_eq
    rw [AscQuot.map_conjSub, hwc, hcR']
  refine ⟨w, hw3, hA, fun y hy => ?_, ?_⟩
  · have hmem : w * y * w⁻¹ ∈ R' := by
      have : w * y * w⁻¹ ∈ conjSub w R' := conj_mem_conjSub hy
      rwa [hA'] at this
    have h1 : y⁻¹ * (w * y * w⁻¹) ∈ f.ker := by
      rw [← hkerφ, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hwc]
      have := hcK' (φ y) (Subgroup.mem_map_of_mem φ hy)
      calc (φ y)⁻¹ * (c * φ y * c⁻¹) = (φ y)⁻¹ * (φ y * c * c⁻¹) := by rw [this]
        _ = 1 := by group
    have h2 := hR'N _ (R'.mul_mem (R'.inv_mem hy) hmem) h1
    calc w * y = (w * y * w⁻¹) * w := by group
      _ = (y * (y⁻¹ * (w * y * w⁻¹))) * w := by group
      _ = y * w := by rw [h2, mul_one]
  · obtain ⟨r, hr, hrk⟩ := Subgroup.mem_map.mp hkbar
    refine ⟨r, hr, fun h => hkbarne ?_⟩
    have hcomm : φ w * φ r = φ r * φ w := by rw [← map_mul, ← map_mul, h]
    rw [← hwc, ← hrk]
    calc φ w * φ r * (φ w)⁻¹ = (φ r * φ w) * (φ w)⁻¹ := by rw [hcomm]
      _ = φ r := by group

end GenericE4

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
