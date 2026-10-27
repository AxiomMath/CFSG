module

public import CFSG.LocalAnalysis.ComponentClassification.GS82L34FieldSqrt
public import CFSG.LocalAnalysis.ComponentClassification.GS82L34Rbar
public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenter
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionSemidirectTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CL34
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open scoped MatrixGroups

namespace FixedSqrt

theorem eq_of_q_eq {E : Type*} [Group E] [Group.IsPerfect E] {q : E →* Equiv.Perm (Fin 42)}
    (hqker : q.ker = center E) (γ : E ≃* E) (hγ : ∀ e, q (γ e) = q e) (e : E) : γ e = e := by
  have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement γ.toMonoidHom fun x => by
    rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, MulEquiv.coe_toMonoidHom, hγ x,
      inv_mul_cancel]
  exact DFunLike.congr_fun hid e

variable {X : Type} [Group X] [Finite X]

theorem betaHat_eq_one_or_eq {K L : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hLK : L ≤ K) {F : Type*} [Field F] [Finite F] (h7 : Nat.card F = 7)
    (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) {q : Jhat K →* Equiv.Perm (Fin 42)}
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat K))
    {x : X} (hxN : x ∈ normalizer (K : Set X)) (hLx : L ≤ centralizer ({x} : Set X))
    (hxq : ∀ e, q (betaHat K hxN e) = r₂ * q e * r₂⁻¹) {y : X}
    (hyN : y ∈ normalizer (K : Set X)) (hLy : L ≤ centralizer ({y} : Set X)) :
    (∀ e, betaHat K hyN e = e) ∨ ∀ e, betaHat K hyN e = betaHat K hxN e := by
  have : Group.IsPerfect (Jhat K) := ⟨commutator_jhat hK⟩
  have hle : (imageHom hLK q).range ≤ C₂ := range_imageHom_le hLK hxN hLx hqS hxq
  have hodd : Odd (Nat.card F) := by rw [h7]; decide
  have hdvd := card_sl2_dvd hLK (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd) e
    q hqker
  rw [card_sl2, h7] at hdvd
  have hle2 : Nat.card (imageHom hLK q).range ∣ 168 := by
    rw [← card_C₂]
    exact Subgroup.card_dvd_of_le hle
  have h168 : 168 ∣ Nat.card (imageHom hLK q).range :=
    (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 (by simpa using hdvd)
  have hrange : (imageHom hLK q).range = C₂ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_C₂, Nat.dvd_antisymm hle2 h168])
  obtain ⟨r, hrR, hr⟩ := exists_realization q hqS hqsurj (betaHat K hyN) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hcomm : ∀ s ∈ C₂, r * s = s * r := by
    intro s hs
    rw [← hrange] at hs
    obtain ⟨s', rfl⟩ := hs
    rw [imageHom_apply]
    have hfix : betaHat K hyN (jq K ⟨s', hLK s'.2⟩) = jq K ⟨s', hLK s'.2⟩ := by
      rw [betaHat_mk]
      congr 1
      exact Subtype.ext (conj_eq_of_mem_centralizer (hLy s'.2))
    have h1 := hr (jq K ⟨s', hLK s'.2⟩)
    rw [hfix] at h1
    calc r * q (jq K ⟨s', hLK s'.2⟩) = r * q (jq K ⟨s', hLK s'.2⟩) * r⁻¹ * r := by group
      _ = q (jq K ⟨s', hLK s'.2⟩) * r := by rw [← h1]
  rcases centralizer_C₂_inf_R r hrR hcomm with rfl | rfl
  · left
    exact eq_of_q_eq hqker _ fun e => by rw [hr e]; group
  · right
    intro e
    have h := eq_of_q_eq hqker ((betaHat K hyN).trans (betaHat K hxN).symm) (fun e => by
      have h1 := hxq ((betaHat K hxN).symm (betaHat K hyN e))
      rw [MulEquiv.apply_symm_apply, hr e] at h1
      have h2 := (mul_left_cancel (mul_right_cancel h1)).symm
      exact h2) e
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_eq] at h
    exact h

theorem pPrimeCore_eq_bot {H : Type} [Group H] [Finite H] (hH : IsQuasisimple H)
    (hZ : IsPGroup 2 ↥(center H)) (hL : Blueprint.LieModel (H ⧸ center H) .PSL 3 2 2) :
    pPrimeCore 2 H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 H)) := pPrimeCore_coprime_card
  rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hH pPrimeCore_normal with
    h | h
  · rw [h, Subgroup.card_top, card_eq_card_quotient_mul_card_subgroup (center H),
      CatLeafProof.X10CL.card_of_lieModel_L34 hL] at hcop
    exact absurd (Nat.Coprime.coprime_dvd_right (dvd_mul_right 20160 _) hcop) (by norm_num)
  · rcases (hZ.to_le h).card_eq_or_dvd with h1 | h2
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)

theorem not_forall_conj_inl {H : Type} [Group H] {σ : MulAut H} (hσ1 : σ ≠ 1) :
    ¬ ∀ k ∈ (SemidirectProduct.inl (φ := MonoidHom.id (MulAut H))).range,
      (SemidirectProduct.inr σ)⁻¹ * k * SemidirectProduct.inr σ = k := by
  intro h
  refine hσ1 (MulEquiv.ext fun y => ?_)
  have h1 := h _ ⟨y, rfl⟩
  rw [← map_inv, ← SemidirectProduct.inl_aut_inv] at h1
  have h2 : σ⁻¹ y = y := SemidirectProduct.inl_injective h1
  calc σ y = σ (σ⁻¹ y) := by rw [h2]
    _ = y := MulAut.apply_inv_self H σ y

end FixedSqrt

open FixedSqrt

theorem exists_fixed_central_sqrt
    {H : Type} [Group H]
    [Finite H] (hH : IsQuasisimple H) (hL : GH74.GLS.IsL34Quotient H)
    (hZ : Nat.card ↥(center H) = 16) (A : Subgroup (MulAut H)) (hA : IsPGroup 2 A)
    (T : Subgroup H) (hTA : ∀ α ∈ A, ∀ y ∈ T, α y = y) {F : Type*} [Field F] [Finite F]
    (h7 : Nat.card F = 7) (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* SL(2, F)) {w : H} (hw : w ^ 2 = 1)
    (hwT : w ∈ T) (hwZ : w ∈ center H) :
    ∃ ω ∈ center H, (∀ α ∈ A, α ω = ω) ∧ ω ^ 2 = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHp : Group.IsPerfect H := hH.1
  have hZ2 : IsPGroup 2 ↥(center H) := IsPGroup.of_card (n := 4) (by rw [hZ]; norm_num)
  have hOH : pPrimeCore 2 H = ⊥ := pPrimeCore_eq_bot hH hZ2 hL
  have : Finite (H ⋊[MonoidHom.id (MulAut H)] MulAut H) :=
    AschbacherComponentInvolution.semidirect_finite _
  set ι : H →* H ⋊[MonoidHom.id (MulAut H)] MulAut H :=
    SemidirectProduct.inl (φ := MonoidHom.id (MulAut H)) with hιdef
  set K : Subgroup (H ⋊[MonoidHom.id (MulAut H)] MulAut H) := ι.range with hKdef
  have hKn : K.Normal := AschbacherComponentInvolution.semidirect_base_normal _
  have hinj : Function.Injective ι := SemidirectProduct.inl_injective
  have hNK : ∀ x, x ∈ normalizer (K : Set (H ⋊[MonoidHom.id (MulAut H)] MulAut H)) := fun x => by
    rw [normalizer_eq_top_iff.mpr hKn]
    exact mem_top _
  have hOK : pPrimeCore 2 ↥K = ⊥ := by
    rw [← pPrimeCore_map_iso 2 (MonoidHom.ofInjective hinj), hOH, Subgroup.map_bot]
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)
  have hL34 : IsL34Type (↥K ⧸ Open.fusionZStar ↥K) :=
    ((show Blueprint.LieModel (H ⧸ center H) .PSL 3 2 2 from hL).of_mulEquiv
      (QuotientGroup.congr _ _ (MonoidHom.ofInjective hinj) (Subgroup.map_center_eq _))).of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center_of_pPrimeCore_eq_bot hOK).symm)
  set π : H →* Jhat K := (jq K).comp ι.rangeRestrict with hπdef
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hh
    have h1 := (QuotientGroup.eq_one_iff (N := pPrimeCore 2 ↥K) _).1 hh
    rw [hOK, mem_bot] at h1
    rw [mem_bot]
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.coe_rangeRestrict] at h2
    exact hinj (h2.trans (map_one ι).symm)
  have hπsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp ι.rangeRestrict_surjective
  set Θ : H ≃* Jhat K := MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩ with hΘdef
  have hΘ : ∀ h, Θ h = π h := fun _ => rfl
  have hbh : ∀ (α : MulAut H) (h : H),
      betaHat K (hNK (SemidirectProduct.inr α⁻¹)) (Θ h) = Θ (α h) := by
    intro α h
    rw [hΘ, hΘ]
    show jq K (conjJ K (hNK _) (ι.rangeRestrict h)) = jq K (ι.rangeRestrict (α h))
    congr 1
    apply Subtype.ext
    rw [coe_conjJ, MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict]
    show (SemidirectProduct.inr α⁻¹)⁻¹ * ι h * SemidirectProduct.inr α⁻¹ = ι (α h)
    rw [← map_inv, inv_inv, hιdef]
    exact (SemidirectProduct.inl_aut α h).symm
  have hcen : ∀ h, Θ h ∈ center (Jhat K) ↔ h ∈ center H := fun h => by
    simp only [mem_center_iff]
    constructor
    · intro hc g
      apply Θ.injective
      rw [map_mul, map_mul, hc]
    · intro hc g
      obtain ⟨g', rfl⟩ := Θ.surjective g
      rw [← map_mul, ← map_mul, hc]
  by_cases hA1 : ∀ α ∈ A, α = 1
  ·
    obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls⟩ := exists_setting hKperf hL34
    have hQS : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
    have hz : Θ w ∈ q.ker := by rw [hqker]; exact (hcen w).2 hwZ
    obtain ⟨c, d, hcd⟩ := (WIso.mem_ker_iff_zz hQS).1 hz
    have hmem : ∀ c d : ZMod 4, zz l c d ∈ center (Jhat K) := fun c d => by
      rw [← hqker]
      exact zz_mem_ker hQS c d
    set f : ZMod 4 × ZMod 4 → center (Jhat K) := fun p => ⟨zz l p.1 p.2, hmem p.1 p.2⟩ with hf
    have hfsurj : Function.Surjective f := by
      rintro ⟨z, hz⟩
      rw [← hqker] at hz
      obtain ⟨a, b, rfl⟩ := (WIso.mem_ker_iff_zz hQS).1 hz
      exact ⟨(a, b), rfl⟩
    have hcard : Nat.card (center (Jhat K)) = 16 := by
      rw [← hZ]
      exact (Nat.card_congr (Subgroup.centerCongr Θ).toEquiv).symm
    have hfinj : Function.Injective f :=
      (hfsurj.bijective_of_nat_card_le (by simp [hcard])).1
    have hinj0 : ∀ c d : ZMod 4, zz l c d = 1 → c = 0 ∧ d = 0 := by
      intro c d h
      have h1 : f (c, d) = f (0, 0) := Subtype.ext (by simp only [hf]; rw [h, zz_zero])
      have h2 := hfinj h1
      exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
    have h2 : zz l (2 * c) (2 * d) = 1 := by
      have h' := zz_pow (l := l) c d 2
      rw [← hcd, ← map_pow, hw, map_one, Nat.cast_ofNat] at h'
      exact h'.symm
    obtain ⟨hc0, hd0⟩ := hinj0 _ _ h2
    have key : ∀ x : ZMod 4, 2 * x = 0 → ∃ y : ZMod 4, 2 * y = x := by decide
    obtain ⟨c', hc'⟩ := key c hc0
    obtain ⟨d', hd'⟩ := key d hd0
    refine ⟨Θ.symm (zz l c' d'), (hcen _).1 (by rw [MulEquiv.apply_symm_apply]; exact hmem _ _),
      fun α hα => by rw [hA1 α hα]; rfl, ?_⟩
    apply Θ.injective
    rw [map_pow, MulEquiv.apply_symm_apply, hcd, zz_pow, Nat.cast_ofNat, hc', hd']
  ·
    push Not at hA1
    obtain ⟨σ₀, hσ₀A, hσ₀1⟩ := hA1
    obtain ⟨σ, hσ⟩ : ∃ σ : A, orderOf σ = 2 := by
      apply exists_prime_orderOf_dvd_card' 2
      rcases hA.card_eq_or_dvd with h1 | h2
      · exfalso
        have := Subgroup.card_eq_one.mp h1
        rw [this] at hσ₀A
        exact hσ₀1 (mem_bot.mp hσ₀A)
      · exact h2
    set s : MulAut H := (σ : MulAut H) with hsdef
    have hsA : s ∈ A := σ.2
    have hs2 : s * s = 1 := by
      have h := pow_orderOf_eq_one σ
      rw [hσ, pow_two] at h
      exact congrArg Subtype.val h
    have hs1 : s ≠ 1 := by
      intro h
      have : σ = 1 := Subtype.ext h
      rw [this, orderOf_one] at hσ
      exact absurd hσ (by norm_num)
    set x : H ⋊[MonoidHom.id (MulAut H)] MulAut H := SemidirectProduct.inr s⁻¹ with hxdef
    have hx2 : x * x = 1 := by
      rw [hxdef, ← map_mul, ← mul_inv_rev, hs2, inv_one, map_one]
    have hxK : ¬ ∀ k ∈ K, x⁻¹ * k * x = k := not_forall_conj_inl (inv_ne_one.mpr hs1)
    set L : Subgroup (H ⋊[MonoidHom.id (MulAut H)] MulAut H) := T.map ι with hLdef
    have hLK : L ≤ K := map_le_range _ _
    have hLc : ∀ α ∈ A, L ≤ centralizer ({SemidirectProduct.inr α⁻¹} :
        Set (H ⋊[MonoidHom.id (MulAut H)] MulAut H)) := by
      rintro α hα _ ⟨t, ht, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (AschbacherComponentInvolution.semidirect_fixed_commute _ α⁻¹ t
          (hTA α⁻¹ (A.inv_mem hα) t ht)).eq.symm
    have hLx : L ≤ centralizer ({x} : Set (H ⋊[MonoidHom.id (MulAut H)] MulAut H)) :=
      hLc s hsA
    let eL : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F) :=
      (QuotientGroup.congr _ _ (T.equivMapOfInjective _ hinj) (pPrimeCore_map_iso 2 _)).symm.trans eT
    have hfield := isL34Field_of_sl2Seven hKperf hOK hL34 (hNK x) hx2 hxK hLK hLx h7 eL
    obtain ⟨q, l, hQS, hxq, -, -⟩ :=
      exists_field_frame hKperf hL34 (hNK x) hx2 hLK hLx h7 eL hfield
    have hz : Θ w ∈ center (Jhat K) := (hcen w).2 hwZ
    have hfix : betaHat K (hNK x) (Θ w) = Θ w := by
      rw [hxdef, hbh, hTA s hsA w hwT]
    have hz2 : Θ w ^ 2 = 1 := by rw [← map_pow, hw, map_one]
    obtain ⟨ω', hω'Z, hω'fix, hω'2⟩ :=
      exists_fixed_sqrt_center' hKperf hOK hL34 (hNK x) hx2 hxK hLK hLx h7 eL (Θ w) hz hfix hz2
    refine ⟨Θ.symm ω', (hcen _).1 (by rw [MulEquiv.apply_symm_apply]; exact hω'Z), ?_, ?_⟩
    · intro α hα
      apply Θ.injective
      rw [← hbh, MulEquiv.apply_symm_apply]
      rcases betaHat_eq_one_or_eq hKperf hLK h7 eL hQS.qS hQS.qsurj hQS.ker (hNK x) hLx hxq
          (hNK (SemidirectProduct.inr α⁻¹)) (hLc α hα) with h | h
      · exact h ω'
      · rw [h ω']
        exact hω'fix
    · apply Θ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hω'2]

end CFSG.ComponentClassification.TBLit.L34P
