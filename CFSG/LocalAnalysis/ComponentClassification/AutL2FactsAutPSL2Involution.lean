module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGInvolution
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOddClosure
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSplitCent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterCent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsDihedralOdd
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteCore

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup

theorem mulAut_conj_conj {Y : Type*} [Group Y] (α : MulAut Y) (s : Y) :
    α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := by
  ext g
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem innAut_normal (Y : Type*) [Group Y] : (MulAut.conj : Y →* MulAut Y).range.Normal :=
  ⟨fun _ ⟨s, hs⟩ g => ⟨g s, by rw [← hs, mulAut_conj_conj]⟩⟩

theorem inn_inf_centralizer_equiv {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥)
    (α : MulAut Y) :
    Nonempty (↥((MulAut.conj : Y →* MulAut Y).range ⊓
        Subgroup.centralizer ({α} : Set (MulAut Y))) ≃*
      ↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y))) := by
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    intro a b h
    have hc : b⁻¹ * a ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h g
      simp only [MulAut.conj_apply] at this
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [this]
        _ = b⁻¹ * a * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  have hmap : (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y)).map MulAut.conj =
      (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer ({α} : Set (MulAut Y)) := by
    ext φ
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : α s = s := hs
      refine ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h := mulAut_conj_conj α s
      rw [hs'] at h
      calc MulAut.conj s * α = α * MulAut.conj s * α⁻¹ * α := by rw [h]
        _ = α * MulAut.conj s := by group
    · rintro ⟨⟨s, rfl⟩, hc⟩
      refine ⟨s, ?_, rfl⟩
      have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
      have h := mulAut_conj_conj α s
      have h2 : α * MulAut.conj s * α⁻¹ = MulAut.conj s := by rw [← hc']; group
      rw [h] at h2
      exact hinj h2
  exact ⟨((MulEquiv.subgroupCongr hmap).symm.trans
    ((MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y)).equivMapOfInjective _ hinj).symm)⟩

theorem odd_mul_of_centralizer_inner {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (hH : HarrisHyp F) (e : Y ≃* PSL2 F) {ι : MulAut Y} (hι : ι ∈ HarrisLit.innAut Y)
    (hιo : orderOf ι = 2) {x y : MulAut Y} (hx : x ∈ Subgroup.centralizer ({ι} : Set (MulAut Y)))
    (hy : y ∈ Subgroup.centralizer ({ι} : Set (MulAut Y))) (hxo : Odd (orderOf x))
    (hyo : Odd (orderOf y)) : Odd (orderOf (x * y)) := by
  set Φ := autEquiv e
  have hιL : Φ ι ∈ pGammaL2PSLRange F := by
    rw [← map_autEquiv_innAut e]
    exact Subgroup.mem_map_of_mem _ hι
  have hx' : Φ x * Φ ι = Φ ι * Φ x := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hx]
  have hy' : Φ y * Φ ι = Φ ι * Φ y := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hy]
  have := hH.odd_mul_of_commute_inv hιL (by rw [MulEquiv.orderOf_eq]; exact hιo) hx' hy'
    (by rw [MulEquiv.orderOf_eq]; exact hxo) (by rw [MulEquiv.orderOf_eq]; exact hyo)
  rwa [← map_mul, MulEquiv.orderOf_eq] at this

theorem cfAutPSL2Involution : HarrisLit.AutPSL2InvolutionInput := by
  intro Y _ _ p f hp hp2 hfe h16 hY K hIK T hTK hSyl v hv
  obtain ⟨-, hf1, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hH : HarrisHyp F := harrisHyp_of hp hp2 hF hfe h16
  have hodd := hH.odd
  set Φ := autEquiv e with hΦ
  have hInn : (HarrisLit.innAut Y).map Φ.toMonoidHom = pGammaL2PSLRange F :=
    map_autEquiv_innAut e
  have : (HarrisLit.innAut Y).Normal := innAut_normal Y
  set R := T ⊓ HarrisLit.innAut Y with hR
  set Rv := R ⊔ zpowers v with hRv
  refine ⟨fun ι hι hιo => ?_, ?_, fun α hαT hαR hα2 => ?_⟩
  ·
    apply isPGroup_quotient_pPrimeCore_of_odd_mul
    intro x hx y hy hxo hyo
    exact odd_mul_of_centralizer_inner hH e (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hι).1).2
      hιo (Subgroup.mem_inf.mp hx).2 (Subgroup.mem_inf.mp hy).2 hxo hyo
  ·
    obtain ⟨m, hm3, ⟨ρ⟩⟩ := hv.dihedral
    have hn4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hneven : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
    have hZcard : Nat.card (Subgroup.center ↥R) = 2 := by
      rw [Nat.card_congr (Subgroup.centerCongr ρ).toEquiv]
      exact CFSG.Walter.card_center_dihedralGroup hn4 hneven
    obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.mp hZcard
    obtain ⟨ι₀', hι₀'1, hι₀'uniq⟩ : ∃ z : Subgroup.center ↥R, z ≠ 1 ∧
        ∀ w : Subgroup.center ↥R, w ≠ 1 → w = z := by
      have hmem : ∀ w : Subgroup.center ↥R, w = a ∨ w = b := fun w => by
        have : w ∈ ({a, b} : Set _) := by rw [huniv]; trivial
        simpa using this
      rcases hmem 1 with h1 | h1
      · refine ⟨b, fun h => hab (h1.symm.trans h.symm), fun w hw => ?_⟩
        rcases hmem w with h | h
        · exact absurd (h.trans h1.symm) hw
        · exact h
      · refine ⟨a, fun h => hab (h.trans h1), fun w hw => ?_⟩
        rcases hmem w with h | h
        · exact h
        · exact absurd (h.trans h1.symm) hw
    set ι₀ : MulAut Y := ((ι₀' : ↥R) : MulAut Y) with hι₀
    have hι₀R : ι₀ ∈ R := (ι₀' : ↥R).2
    have hι₀c : ∀ r ∈ R, r * ι₀ = ι₀ * r := by
      intro r hr
      have := Subgroup.mem_center_iff.mp ι₀'.2 ⟨r, hr⟩
      exact congrArg Subtype.val this
    have hι₀1 : ι₀ ≠ 1 := by
      intro h
      apply hι₀'1
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have hι₀o : orderOf ι₀ = 2 := by
      have hdvd : orderOf ι₀' ∣ 2 := hZcard ▸ orderOf_dvd_natCard ι₀'
      have h1 : orderOf ι₀' ≠ 1 := fun h => hι₀'1 (orderOf_eq_one_iff.mp h)
      have h2 : orderOf ι₀' = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd h h1
        · exact h
      rw [hι₀, Subgroup.orderOf_coe, Subgroup.orderOf_coe, h2]
    have hRvT : Rv ≤ T := sup_le inf_le_left ((zpowers_le).mpr hv.mem)
    have hnorm : ∀ g ∈ K ⊓ normalizer ((Rv : Subgroup (MulAut Y)) : Set (MulAut Y)),
        g ∈ Subgroup.centralizer ({ι₀} : Set (MulAut Y)) := by
      intro g hg
      have hgN := (Subgroup.mem_inf.mp hg).2
      have hA : ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
        intro r hr
        have h1 : g * r * g⁻¹ ∈ Rv :=
          (Subgroup.mem_normalizer_iff.mp hgN r).mp (le_sup_left (b := zpowers v) hr)
        exact Subgroup.mem_inf.mpr ⟨hRvT h1, ‹(HarrisLit.innAut Y).Normal›.conj_mem r
          (Subgroup.mem_inf.mp hr).2 g⟩
      have hB : ∀ r ∈ R, g⁻¹ * r * g ∈ R := by
        intro r hr
        have h1 : g⁻¹ * r * g ∈ Rv := by
          apply (Subgroup.mem_normalizer_iff.mp hgN _).mpr
          rw [show g * (g⁻¹ * r * g) * g⁻¹ = r by group]
          exact le_sup_left (b := zpowers v) hr
        have h2 : g⁻¹ * r * g ∈ HarrisLit.innAut Y := by
          have := ‹(HarrisLit.innAut Y).Normal›.conj_mem r (Subgroup.mem_inf.mp hr).2 g⁻¹
          rwa [inv_inv] at this
        exact Subgroup.mem_inf.mpr ⟨hRvT h1, h2⟩
      set ι := g * ι₀ * g⁻¹
      have hιR : ι ∈ R := hA ι₀ hι₀R
      have hιc : ⟨ι, hιR⟩ ∈ Subgroup.center ↥R := by
        rw [Subgroup.mem_center_iff]
        rintro ⟨r, hr⟩
        apply Subtype.ext
        show r * ι = ι * r
        have h := hι₀c _ (hB r hr)
        calc r * ι = g * ((g⁻¹ * r * g) * ι₀) * g⁻¹ := by simp only [ι]; group
          _ = g * (ι₀ * (g⁻¹ * r * g)) * g⁻¹ := by rw [h]
          _ = ι * r := by simp only [ι]; group
      have hι1 : (⟨⟨ι, hιR⟩, hιc⟩ : Subgroup.center ↥R) ≠ 1 := by
        intro h
        apply hι₀1
        have : ι = 1 := congrArg (fun w : Subgroup.center ↥R => ((w : ↥R) : MulAut Y)) h
        calc ι₀ = g⁻¹ * ι * g := by simp only [ι]; group
          _ = 1 := by rw [this]; group
      have hιeq := hι₀'uniq _ hι1
      have hιι₀ : ι = ι₀ := congrArg (fun w : Subgroup.center ↥R => ((w : ↥R) : MulAut Y)) hιeq
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * ι₀ = ι * g := by simp only [ι]; group
        _ = ι₀ * g := by rw [hιι₀]
    apply isPGroup_quotient_pPrimeCore_of_odd_mul
    intro x hx y hy hxo hyo
    exact odd_mul_of_centralizer_inner hH e (Subgroup.mem_inf.mp hι₀R).2 hι₀o (hnorm x hx)
      (hnorm y hy) hxo hyo
  ·
    have hα1 : α ≠ 1 := fun h => hαR (h ▸ one_mem _)
    have hαo : orderOf α = 2 := orderOf_eq_prime hα2 hα1
    have hY4 : ∃ y : Y, y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
      obtain ⟨y, hy4, hy2⟩ := exists_psl2_pow_four (F := F) (by have := hH.four_le; omega)
      refine ⟨e.symm y, by rw [← map_pow, hy4, map_one], fun h => hy2 ?_⟩
      rw [← map_pow] at h
      exact e.symm.injective (h.trans (map_one _).symm)
    have hr : (Φ α).right = 1 := by
      by_contra hr
      have hfi : IsFieldInvModel (Φ α) :=
        isFieldInvModel_of_involution hodd (by rw [MulEquiv.orderOf_eq]; exact hαo) hr
      have hfa := (isFieldAutPSL2_iff hodd e hY4 α).mpr hfi
      obtain ⟨ρ', hρ', hαρ⟩ := hv.fieldInv α hαT hfa
      apply hαR
      rw [hαρ]
      exact mul_mem (le_sup_left (b := zpowers v) hρ')
        (le_sup_right (a := R) (pow_mem (mem_zpowers v) _))
    have hsq : ¬ SqLeft (Φ α) := by
      intro hsq
      have hmem : Φ α ∈ pGammaL2PSLRange F := (mem_pslRange_iff _).mpr ⟨hr, hsq⟩
      rw [← hInn] at hmem
      obtain ⟨β, hβ, hβα⟩ := hmem
      have : β = α := Φ.injective hβα
      subst this
      exact hαR (le_sup_left (b := zpowers v) (Subgroup.mem_inf.mpr ⟨hαT, hβ⟩))
    set t := (Φ α).left with ht
    have hΦt : Φ α = SemidirectProduct.inl t := SemidirectProduct.ext rfl hr
    have htt : t * t = 1 := by
      have h := congrArg Φ (show α * α = 1 by rw [← pow_two]; exact hα2)
      rw [map_mul, map_one, hΦt, ← map_mul] at h
      exact SemidirectProduct.inl_injective (h.trans (map_one _).symm)
    have ht1 : t ≠ 1 := by
      intro h
      apply hα1
      apply Φ.injective
      rw [hΦt, h, map_one, map_one]
    have hq4 : Nat.card F % 4 = 1 := hH.q4
    have hq3 : 3 < Nat.card F := by
      have := hH.four_le
      have h2 := Finite.one_lt_card (α := F)
      have h16' : 16 ∣ Nat.card F - 1 := by rw [hF]; exact h16
      omega
    have hfix : (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y)).map e.toMonoidHom =
        MonoidHom.eqLocus (pglAction F t).toMonoidHom (MonoidHom.id (PSL2 F)) := by
      ext z
      rw [Subgroup.mem_map_equiv]
      show α (e.symm z) = e.symm z ↔ pglAction F t z = z
      rw [← semilinearAction_inl, ← hΦt]
      have h := semilinearAction_autEquiv_apply e α (e.symm z)
      rw [MulEquiv.apply_symm_apply] at h
      rw [h]
      constructor
      · intro h'
        rw [h', MulEquiv.apply_symm_apply]
      · intro h'
        apply e.injective
        rw [h', MulEquiv.apply_symm_apply]
    obtain ⟨d⟩ := psl2_fix_outer_involution hodd hq4 hq3 htt ht1 hsq
    have hD : Nonempty (↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y)) ≃*
        DihedralGroup ((p ^ f + 1) / 2)) := by
      rw [← hF]
      exact ⟨((e.subgroupMap _).trans (MulEquiv.subgroupCongr hfix)).trans d⟩
    refine ⟨hD, ?_⟩
    have hZ : Subgroup.center Y = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz' : e z ∈ Subgroup.center (PSL2 F) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
      rw [psl2_center_eq_bot, Subgroup.mem_bot] at hz'
      exact Subgroup.mem_bot.mpr (e.injective (hz'.trans (map_one _).symm))
    obtain ⟨dα⟩ := hD
    obtain ⟨iα⟩ := inn_inf_centralizer_equiv hZ α
    have hnodd : Odd ((p ^ f + 1) / 2) := by
      rw [← hF]
      exact ⟨(Nat.card F - 1) / 4, by omega⟩
    have hcomm : ∀ x y : MulAut Y, x * y * x⁻¹ * y⁻¹ ∈ HarrisLit.innAut Y := by
      intro x y
      obtain ⟨s, hs⟩ := footeOutAbelian Y p f hp hp2 hf1 hY x y
      exact ⟨s, hs.symm⟩
    apply isPGroup_quotient_pPrimeCore_of_odd_mul
    intro x hx y hy hxo hyo
    exact odd_mul_of_dihedral (HarrisLit.innAut Y) hcomm α hnodd ⟨iα.trans dα⟩
      (Subgroup.mem_inf.mp hx).2 (Subgroup.mem_inf.mp hy).2 hxo hyo

end CFSG.ComponentClassification.AutL2Facts
