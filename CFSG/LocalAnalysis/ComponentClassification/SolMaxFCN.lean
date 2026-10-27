module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixGen
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem isPComponent_map_conj_inv (S : Sig36 X t J 9 e E D) {g s : X} (hgs : g⁻¹ * t * g = s) :
    J.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({s} : Set X) ∧
      IsPComponent 2 ((J.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf
        (centralizer ({s} : Set X))) := by
  have hC : (centralizer ({t} : Set X)).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer ({s} : Set X) := by
    ext y
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hgs]
      calc g⁻¹ * z * g * (g⁻¹ * t * g) = g⁻¹ * (z * t) * g := by group
        _ = g⁻¹ * (t * z) * g := by rw [hz]
        _ = g⁻¹ * t * g * (g⁻¹ * z * g) := by group
    · intro hy
      refine ⟨g * y * g⁻¹, ?_, by group⟩
      rw [← hgs] at hy
      calc g * y * g⁻¹ * t = g * (y * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by rw [hy]
        _ = t * (g * y * g⁻¹) := by group
  have h1 := isPComponent_map_conj S.pair.1.2.1 S.pair.1.2.2.1 g⁻¹
  rw [hC] at h1
  exact ⟨hC ▸ map_mono S.pair.1.2.1, h1⟩

theorem false_of_cover_of_six (S : Sig36 X t J 9 e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {s g : X}
    (hsH : s ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hs1 : ρ ⟨s, hHN hsH⟩ ≠ 1) (hgs : g⁻¹ * t * g = s) {v₁ v₂ : X}
    (hv₁H : v₁ ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hv₂H : v₂ ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hv₁t : v₁ * t = t * v₁) (hv₂t : v₂ * t = t * v₂) (hv₁2 : v₁ * v₁ = 1) (hv₂2 : v₂ * v₂ = 1)
    (h12 : v₁ * v₂ = v₂ * v₁)
    (hC₁ : ∀ y ∈ centralizer ({v₁} : Set X),
      g⁻¹ * y * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hC₂ : ∀ y ∈ centralizer ({v₂} : Set X),
      g⁻¹ * y * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hC₁₂ : ∀ y ∈ centralizer ({v₁ * v₂} : Set X),
      g⁻¹ * y * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X))
    (h6 : (ρ ⟨v₁, hHN hv₁H⟩).support.card = 6) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hCtJ : centralizer ({t} : Set X) ≤ normalizer (J : Set X) :=
    S.centralizer_le_normalizer hT13 hML hSch
  have hJt : J ≤ centralizer ({t} : Set X) := S.pair.1.2.1
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have htJN : t ∈ normalizer (J : Set X) := hCtJ (mem_centralizer_singleton_iff.mpr rfl)
  have htK : t ∈ UnbalancedLayer.coreActionKernel J :=
    mem_coreActionKernel_of_forall_commute fun l hl => mem_centralizer_singleton_iff.mp (hJt hl)
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) e
  have hρJt : ρJ ⟨t, htJN⟩ = 1 := hρJ.eq_one_of_mem_coreActionKernel (by norm_num) htK
  have hv₁J : v₁ ∈ normalizer (J : Set X) := hCtJ (mem_centralizer_singleton_iff.mpr hv₁t)
  have hv₂J : v₂ ∈ normalizer (J : Set X) := hCtJ (mem_centralizer_singleton_iff.mpr hv₂t)
  have hv12H : v₁ * v₂ ∈ H := mul_mem hv₁H hv₂H
  have hv12t : v₁ * v₂ * t = t * (v₁ * v₂) := by
    rw [mul_assoc, hv₂t, ← mul_assoc, hv₁t, mul_assoc]
  have hv12J : v₁ * v₂ ∈ normalizer (J : Set X) := mul_mem hv₁J hv₂J
  have hv122 : v₁ * v₂ * (v₁ * v₂) = 1 := by
    calc v₁ * v₂ * (v₁ * v₂) = v₁ * (v₂ * v₁) * v₂ := by group
      _ = v₁ * (v₁ * v₂) * v₂ := by rw [h12]
      _ = (v₁ * v₁) * (v₂ * v₂) := by group
      _ = 1 := by rw [hv₁2, hv₂2, one_mul]
  have h6J : (ρJ ⟨v₁, hv₁J⟩).support.card = 6 := by
    rw [← card_support_rho_eq_rhoJ (by norm_num) hJM hsup hρ hρJ hv₁J (hHN hv₁H)]
    exact h6
  set Y : Subgroup X := (J ⊓ centralizer ({v₁} : Set X)) ⊔ (J ⊓ centralizer ({v₂} : Set X)) ⊔
    (J ⊓ centralizer ({v₁ * v₂} : Set X)) with hYdef
  have hYJ : Y ≤ J := sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  set ρY : Subgroup (Perm (Fin 9)) := (Y.subgroupOf (normalizer (J : Set X))).map ρJ
    with hρYdef
  have hlift : ∀ w : X, ∀ hw : w ∈ normalizer (J : Set X), w * w = 1 → w * t = t * w →
      J ⊓ centralizer ({w} : Set X) ≤ Y →
      centralizer ({ρJ ⟨w, hw⟩} : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) ≤ ρY := by
    intro w hw hw2 hwt hwY b hb
    obtain ⟨hbc, hbA⟩ := mem_inf.mp hb
    set B : Subgroup X := zpowers t ⊔ zpowers w with hBdef
    have hB2 : IsPGroup 2 B := (isPGroup_zpowers_of_mul_self ht2).to_sup_of_normal_left'
      (isPGroup_zpowers_of_mul_self hw2)
      (zpowers_le.mpr (mem_normalizer_zpowers_of_commute hwt.symm))
    have hBN : B ≤ normalizer (J : Set X) := sup_le (zpowers_le.mpr htJN) (zpowers_le.mpr hw)
    have hbB : ∀ (y : X) (hy : y ∈ B),
        (b : Perm (Fin 9)) * ρJ ⟨y, hBN hy⟩ = ρJ ⟨y, hBN hy⟩ * b := by
      set Z : Subgroup X := ((centralizer ({b} : Set (Perm (Fin 9)))).comap ρJ).map
        (normalizer (J : Set X)).subtype with hZdef
      have htZ : t ∈ Z := by
        refine ⟨⟨t, htJN⟩, ?_, rfl⟩
        show ρJ ⟨t, htJN⟩ ∈ centralizer ({b} : Set (Perm (Fin 9)))
        rw [hρJt]
        exact one_mem _
      have hwZ : w ∈ Z := ⟨⟨w, hw⟩, mem_comap.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hbc).symm), rfl⟩
      intro y hy
      obtain ⟨y', hy', hyy⟩ := sup_le (zpowers_le.mpr htZ) (zpowers_le.mpr hwZ) hy
      have h1 : (⟨y, hBN hy⟩ : ↥(normalizer (J : Set X))) = y' := Subtype.ext hyy.symm
      rw [h1]
      exact (mem_centralizer_singleton_iff.mp (mem_comap.mp hy')).symm
    obtain ⟨x, hxC, hxθ⟩ := hρJ.exists_lift_of_isPGroup hBN hB2 (b := ⟨b, hbA⟩) hbB
    have hxw : (x : X) ∈ centralizer ({w} : Set X) := mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hxC w (mem_sup_right (mem_zpowers w))).symm)
    have hxY : (x : X) ∈ Y := hwY (mem_inf.mpr ⟨x.2, hxw⟩)
    refine ⟨⟨x, le_normalizer x.2⟩, hxY, ?_⟩
    rw [hρJ.apply_of_mem (by norm_num) x, hxθ]
  have hρ12 : ρJ ⟨v₁ * v₂, hv12J⟩ = ρJ ⟨v₁, hv₁J⟩ * ρJ ⟨v₂, hv₂J⟩ := by
    rw [← map_mul]
    rfl
  have hu2 : ρJ ⟨v₁, hv₁J⟩ * ρJ ⟨v₁, hv₁J⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨v₁, hv₁J⟩ : ↥(normalizer (J : Set X))) * ⟨v₁, hv₁J⟩ = 1 := Subtype.ext hv₁2
    rw [h1, map_one]
  have hv2' : ρJ ⟨v₂, hv₂J⟩ * ρJ ⟨v₂, hv₂J⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨v₂, hv₂J⟩ : ↥(normalizer (J : Set X))) * ⟨v₂, hv₂J⟩ = 1 := Subtype.ext hv₂2
    rw [h1, map_one]
  have huv : ρJ ⟨v₁, hv₁J⟩ * ρJ ⟨v₂, hv₂J⟩ = ρJ ⟨v₂, hv₂J⟩ * ρJ ⟨v₁, hv₁J⟩ := by
    rw [← map_mul, ← map_mul]
    have h1 : (⟨v₁, hv₁J⟩ : ↥(normalizer (J : Set X))) * ⟨v₂, hv₂J⟩ = ⟨v₂, hv₂J⟩ * ⟨v₁, hv₁J⟩ :=
      Subtype.ext h12
    rw [h1]
  have hgen := alternatingGroup_le_sup_centralizer_of_six hu2 hv2' huv h6J
  have hAY : alternatingGroup (Fin 9) ≤ ρY := by
    refine hgen.trans (sup_le (sup_le ?_ ?_) ?_)
    · exact hlift v₁ hv₁J hv₁2 hv₁t (le_sup_left.trans le_sup_left)
    · exact hlift v₂ hv₂J hv₂2 hv₂t (le_sup_right.trans le_sup_left)
    · rw [← hρ12]
      exact hlift (v₁ * v₂) hv12J hv122 hv12t le_sup_right
  have hYsup : Y ⊔ (pPrimeCore 2 ↥J).map J.subtype = J := by
    refine le_antisymm (sup_le hYJ (map_subtype_le _)) ?_
    intro j hj
    have hjA : ρJ ⟨j, le_normalizer hj⟩ ∈ alternatingGroup (Fin 9) := by
      rw [hρJ.apply_of_mem (by norm_num) ⟨j, hj⟩]
      exact (e _).2
    obtain ⟨y', hy', hyj⟩ := hAY hjA
    have hyY : (y' : X) ∈ Y := hy'
    set k : X := (y' : X)⁻¹ * j with hkdef
    have hkN : k ∈ normalizer (J : Set X) := mul_mem (inv_mem y'.2) (le_normalizer hj)
    have hρk : ρJ ⟨k, hkN⟩ = 1 := by
      have h1 : (⟨k, hkN⟩ : ↥(normalizer (J : Set X))) = y'⁻¹ * ⟨j, le_normalizer hj⟩ :=
        Subtype.ext rfl
      rw [h1, map_mul, map_inv, hyj, inv_mul_cancel]
    have hkJ : k ∈ J := mul_mem (inv_mem (hYJ hyY)) hj
    have hkO : k ∈ (pPrimeCore 2 ↥J).map J.subtype :=
      mem_core_of_mem_coreActionKernel hρJ (by norm_num) hkJ (hρJ.mem_coreActionKernel hkN hρk)
    have h2 : j = (y' : X) * k := by rw [hkdef]; group
    rw [h2]
    exact mul_mem (mem_sup_left hyY) (mem_sup_right hkO)
  set φ : X →* X := (MulAut.conj g⁻¹).toMonoidHom with hφdef
  have hφ : ∀ x, φ x = g⁻¹ * x * g := fun x => by simp [hφdef]
  set N := J.map φ with hNdef
  set Y' := Y.map φ with hY'def
  have hY'N : Y' ≤ N := map_mono hYJ
  have hYH : Y ≤ H.comap φ := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      rw [mem_comap, hφ]
      exact hC₁ y (mem_inf.mp hy).2
    · intro y hy
      rw [mem_comap, hφ]
      exact hC₂ y (mem_inf.mp hy).2
    · intro y hy
      rw [mem_comap, hφ]
      exact hC₁₂ y (mem_inf.mp hy).2
  have hY'H : Y' ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact hYH hy
  have hNs : N ≤ centralizer ({s} : Set X) := by
    rintro _ ⟨l, hl, rfl⟩
    have h1 := mem_centralizer_singleton_iff.mp (hJt hl)
    rw [mem_centralizer_singleton_iff, hφ, ← hgs]
    calc g⁻¹ * l * g * (g⁻¹ * t * g) = g⁻¹ * (l * t) * g := by group
      _ = g⁻¹ * (t * l) * g := by rw [h1]
      _ = g⁻¹ * t * g * (g⁻¹ * l * g) := by group
  let θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin 9) :=
    (Sol78.coreQuotCongr (J.equivMapOfInjective φ (MulAut.conj g⁻¹).injective)).symm.trans e
  have hsupN : Y' ⊔ (pPrimeCore 2 ↥N).map N.subtype = N := by
    rw [hNdef, hφdef, ← GSLit.map_map_pPrimeCore (MulAut.conj g⁻¹) J, hY'def, hφdef,
      ← Subgroup.map_sup, hYsup]
  have hs2 : IsPGroup 2 (zpowers s) := isPGroup_zpowers_of_mul_self (by
    rw [← hgs]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group)
  exact S.false_of_cover_of_centralizer_of_isPComponent h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ
    hρ hs2 hsH hs1 hNs (S.isPComponent_map_conj_inv hgs).2 θN hY'N hY'H hsupN

end Sig36

end CFSG.ComponentClassification.SolMax
