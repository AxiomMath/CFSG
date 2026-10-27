module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeSL2Sections
public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts
public import CFSG.GroupTheory.QuasiDihedralFusion.Classes
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.QCover

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion CFSG.ABGQGroups
open CFSG.BenderSuzuki.MatrixGroups
open scoped Pointwise

section Wreath

open CFSG.Wreathed (Wreath)

private theorem qdloc_wreath_half_involution (k : ℕ) :
    orderOf (Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0) = 2 ∧
      Wreathed.element (2 ^ (k + 1)) 0 0 1 *
          Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 *
          (Wreathed.element (2 ^ (k + 1)) 0 0 1)⁻¹ ≠
        Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 := by
  refine ⟨(Wreathed.element_base_involution_iff k _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
  rw [Wreathed.conjugate_base_by_swap]
  intro h
  rw [Wreathed.element_eq_iff] at h
  exact Wreathed.half_residue_ne_zero k h.1.symm

private theorem qdloc_wreath_not_embed {n k : ℕ} (hn : 4 ≤ n) (hk : 1 ≤ k)
    (ι : Wreath (2 ^ (k + 1)) →* SemidihedralGroup n) (hι : Function.Injective ι) : False := by
  have := presentation_finite n (by omega)
  obtain ⟨hx2, hxw⟩ := qdloc_wreath_half_involution k
  set x := Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 with hx
  set y := Wreathed.element (2 ^ (k + 1)) 1 0 0 with hy
  set w := Wreathed.element (2 ^ (k + 1)) 0 0 1 with hw
  have hxy : x * y = y * x := by
    rw [hx, hy, Wreathed.element_base_mul, Wreathed.element_base_mul, Wreathed.element_eq_iff]
    exact ⟨add_comm _ _, rfl, rfl⟩
  have hy2 : y ^ 2 ≠ 1 := by
    rw [hy, Wreathed.element_base_pow]
    intro h2
    rw [Wreathed.element_base_eq_one_iff] at h2
    have h2' : ((2 : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by simpa [nsmul_eq_mul] using h2.1
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have hle := Nat.le_of_dvd (by norm_num) h2'
    have h4 : 2 ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hX2 : orderOf (ι x) = 2 := by rw [orderOf_injective ι hι, hx2]
  have hXz : ι x ∉ Subgroup.zpowers (z n) := by
    intro h
    rcases (KleinFourOddKernel.mem_zpowers_involution _ _ (orderOf_z n (by omega))).mp h with
      h1 | h1
    · rw [h1, orderOf_one] at hX2
      omega
    · apply hxw
      apply hι
      rw [map_mul, map_mul, map_inv, h1,
        Subgroup.mem_center_iff.mp (z_mem_center n hn) (ι w), mul_inv_cancel_right]
  obtain ⟨h1, -, -⟩ := Local.semidihedral_four_subgroup_centralizers n hn
    (MulEquiv.refl (SemidihedralGroup n))
  have hz : (MulEquiv.refl (SemidihedralGroup n)) (r n) ^ (2 ^ (n - 1) / 2) = z n := by
    rw [MulEquiv.refl_apply, two_pow_div_two hn]
    rfl
  rw [hz] at h1
  obtain ⟨hC, hK⟩ := h1 (ι x) hX2 hXz
  have hYC : ι y ∈ Subgroup.centralizer ({ι x} : Set (SemidihedralGroup n)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxy]
  rw [hC] at hYC
  have hYsq := congrArg Subtype.val (IsKleinFour.mul_self (⟨ι y, hYC⟩ :
    Subgroup.closure ({z n, ι x} : Set (SemidihedralGroup n))))
  apply hy2
  apply hι
  rw [map_pow, map_one, pow_two]
  exact hYsq

end Wreath

section QDSubgroups

variable {G : Type} [Group G] [Finite G]

private theorem qdloc_exists_sd_model {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (H : Subgroup G)
    (hH : HasQDOrWreathedSylow H) (P : Sylow 2 H) :
    ∃ m : ℕ, 4 ≤ m ∧ Nonempty (SemidihedralGroup m ≃* P) := by
  rcases exists_sylow_model hH P with ⟨m, hm, hf⟩ | ⟨k, hk, ⟨e⟩⟩
  · exact ⟨m, hm, hf⟩
  · exfalso
    let P' : Subgroup G := (P : Subgroup H).map H.subtype
    have hP' : IsPGroup 2 P' := P.isPGroup'.map H.subtype
    obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
    let f' : SemidihedralGroup n ≃* (S' : Subgroup G) := fS.trans (Sylow.equiv S S')
    let ι : Wreathed.Wreath (2 ^ k) →* SemidihedralGroup n :=
      f'.symm.toMonoidHom.comp ((Subgroup.inclusion hS').comp
        (((P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom.comp
          e.symm.toMonoidHom))
    have hι : Function.Injective ι := by
      intro a b hab
      have h1 := congrArg Subtype.val (f'.symm.injective hab)
      apply e.symm.injective
      exact Subtype.ext (Subtype.ext h1)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact qdloc_wreath_not_embed hn (by omega) ι hι

private theorem qdloc_sd_noncommuting_involutions {m : ℕ} (hm : 4 ≤ m) :
    orderOf (s m) = 2 ∧ orderOf (r m ^ 2 ^ (m - 3) * s m) = 2 ∧
      s m * (r m ^ 2 ^ (m - 3) * s m) ≠ r m ^ 2 ^ (m - 3) * s m * s m := by
  have hs2 := orderOf_s m (by omega)
  have hsq : s m * s m = 1 := by
    have := pow_orderOf_eq_one (s m)
    rwa [hs2, pow_two] at this
  have hsinv : (s m)⁻¹ = s m := inv_eq_of_mul_eq_one_right hsq
  have hconj := sd_s_conj_quarter hm
  rw [hsinv] at hconj
  set v := r m ^ 2 ^ (m - 3) with hv
  have hne : v ≠ v⁻¹ := sd_quarter_ne_inv hm
  refine ⟨hs2, orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [pow_two]
    calc v * s m * (v * s m) = v * (s m * v * s m) := by group
      _ = 1 := by rw [hconj, mul_inv_cancel]
  · intro h1
    have hvs : v = s m := by
      rw [← mul_inv_eq_one, hsinv]
      exact h1
    exact hne (by rw [hvs, hsinv])
  · intro h
    apply hne
    calc v = v * s m * s m := by rw [mul_assoc, hsq, mul_one]
      _ = s m * (v * s m) := h.symm
      _ = v⁻¹ := by rw [← mul_assoc, hconj]

private theorem qdloc_oddCoreIn_ne_bot (H : Subgroup G)
    (hloc : ∃ ℓ : ℕ, ℓ.Prime ∧ IsPLocal ℓ H) (hQD : IsQDGroup H)
    (hSD : ∀ P : Sylow 2 H, ∃ m : ℕ, 4 ≤ m ∧ Nonempty (SemidihedralGroup m ≃* P)) :
    oddCoreIn H ≠ ⊥ := by
  obtain ⟨ℓ, hℓ, R, hR1, hRℓ, rfl⟩ := hloc
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hRN : R ≤ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    exfalso
    have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
    have hZnt := hRℓ.center_nontrivial
    have hZ2 : IsPGroup 2 (Subgroup.center R) := hRℓ.to_subgroup _
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hk
    obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hz₀c : ((z₀ : R) : G) ∈ centerOf R := by
      rw [← map_center_subtype]
      exact ⟨z₀, z₀.2, rfl⟩
    have hz₀2 : orderOf ((z₀ : R) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀]
    have hcen : ∀ y : Subgroup.normalizer (R : Set G), orderOf y = 2 → (y : G) ∈ centerOf R := by
      intro y hy
      obtain ⟨c, hc⟩ := isConj_iff.mp (hQD.involutions_isConj ⟨_, hRN hz₀c.1⟩ y
        (by rw [Subgroup.orderOf_mk]; exact hz₀2) hy)
      have hcg : (c : G) ∈ Subgroup.normalizer (R : Set G) := c.2
      have hval : (y : G) = (c : G) * ((z₀ : R) : G) * (c : G)⁻¹ := by
        rw [← hc]
        rfl
      rw [hval]
      refine ⟨(Subgroup.mem_normalizer_iff.mp hcg _).mp hz₀c.1, ?_⟩
      show _ ∈ Subgroup.centralizer (R : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : (c : G)⁻¹ * x * c ∈ R := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hcg) x).mp hx
        simpa only [inv_inv] using this
      have h1 := Subgroup.mem_centralizer_iff.mp hz₀c.2 _ hx'
      change x * ((c : G) * ((z₀ : R) : G) * (c : G)⁻¹) =
        (c : G) * ((z₀ : R) : G) * (c : G)⁻¹ * x
      calc x * ((c : G) * ((z₀ : R) : G) * (c : G)⁻¹)
          = c * (((c : G)⁻¹ * x * c) * ((z₀ : R) : G)) * (c : G)⁻¹ := by group
        _ = c * (((z₀ : R) : G) * ((c : G)⁻¹ * x * c)) * (c : G)⁻¹ := by rw [h1]
        _ = (c : G) * ((z₀ : R) : G) * (c : G)⁻¹ * x := by group
    obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.normalizer (R : Set G))) := inferInstance
    obtain ⟨m, hm, ⟨f⟩⟩ := hSD P
    obtain ⟨h1, h2, hne⟩ := qdloc_sd_noncommuting_involutions hm
    let ι : SemidihedralGroup m →* G :=
      (Subgroup.normalizer (R : Set G)).subtype.comp ((P : Subgroup _).subtype.comp f.toMonoidHom)
    have hι : Function.Injective ι := Subtype.val_injective.comp
      (Subtype.val_injective.comp f.injective)
    have hy₁ := hcen (f (s m)).1 (by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact h1)
    have hy₂ := hcen (f (r m ^ 2 ^ (m - 3) * s m)).1 (by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact h2)
    have hcomm := Subgroup.mem_centralizer_iff.mp hy₂.2 _ hy₁.1
    apply hne
    apply hι
    have hmul : ∀ a b : SemidihedralGroup m, ι (a * b) = ι a * ι b := fun a b => map_mul ι a b
    rw [hmul (s m) (r m ^ 2 ^ (m - 3) * s m), hmul (r m ^ 2 ^ (m - 3) * s m) (s m)]
    exact hcomm
  ·
    intro hbot
    apply hR1
    obtain ⟨k, hk⟩ := hRℓ.exists_card_eq
    have hodd : Odd (Nat.card R) := by
      rw [hk]
      exact (hℓ.odd_of_ne_two hℓ2).pow
    have hle := le_oddCoreIn hRN le_rfl hodd
    rw [hbot] at hle
    exact le_bot_iff.mp hle

omit [Finite G] in
private theorem qdloc_exists_centered (H : Subgroup G) (hQD : IsQDGroup H)
    (hSD : ∀ P : Sylow 2 H, ∃ m : ℕ, 4 ≤ m ∧ Nonempty (SemidihedralGroup m ≃* P))
    (y : G) (hyH : y ∈ H) (hy : orderOf y = 2) :
    ∃ (m : ℕ) (P : Subgroup G) (f : SemidihedralGroup m ≃* P), 4 ≤ m ∧ P ≤ H ∧
      (f (z m) : G) = y := by
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨m, hm, ⟨f₀⟩⟩ := hSD P₀
  have hz0 : orderOf ((f₀ (z m) : H)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_z m (by omega)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hQD.involutions_isConj _ ⟨y, hyH⟩ hz0
    (by rw [Subgroup.orderOf_mk]; exact hy))
  let P₁ : Subgroup G := (P₀ : Subgroup H).map H.subtype
  let P : Subgroup G := P₁.map (MulAut.conj (c : G)).toMonoidHom
  let f : SemidihedralGroup m ≃* P :=
    f₀.trans (((P₀ : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (P₁.equivMapOfInjective _ (MulAut.conj (c : G)).injective))
  refine ⟨m, P, f, hm, ?_, ?_⟩
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact H.mul_mem (H.mul_mem c.2 x.2) (H.inv_mem c.2)
  · have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    change (c : G) * ((f₀ (z m) : H) : G) * (c : G)⁻¹ = y
    exact this

end QDSubgroups

section Layer

variable {G : Type} [Group G]

private abbrev qdlocQ (t : G) : Subgroup (H t) :=
  (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)

private abbrev qdlocA (t : G) (K : Subgroup G) : Subgroup (H t) :=
  (K.subgroupOf (C t) ⊓ localLayerPreimage t).map (nu t)

private theorem qdlocA_le (t : G) (K : Subgroup G) : qdlocA t K ≤ qdlocQ t := by
  rintro _ ⟨c, ⟨-, hc⟩, rfl⟩
  exact hc

private theorem mem_qdlocA {t : G} {K : Subgroup G} {c : C t} (hcK : (c : G) ∈ K)
    (hcQ : nu t c ∈ qdlocQ t) : nu t c ∈ qdlocA t K :=
  ⟨c, ⟨hcK, hcQ⟩, rfl⟩

private theorem qdloc_layer_data [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht2 : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ∃ (eta : qdlocQ t ≃* Matrix.SpecialLinearGroup (Fin 2) F) (htQ : nu t (tInC t) ∈ qdlocQ t),
        eta ⟨nu t (tInC t), htQ⟩ = -1 ∧ Group.IsSolvable (H t ⧸ qdlocQ t) ∧
        ∃ a : ℕ, Odd a ∧ (qdlocQ t).index = 2 * a := by
  obtain ⟨-, hJindex, hz, -, -, -, -⟩ := actual_quotient_inputs n hn S fS hG t ht2
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  obtain ⟨-, hsolv, -, -, -, eta, heta⟩ := SameParameterRegularity.actual_matrix_layer_properties
    t n p f hp hpodd hf hq.le F A rho data hcentral hz
  obtain ⟨-, -, -, hAcard⟩ := data.compatible_layer
  have htQ : nu t (tInC t) ∈ qdlocQ t :=
    QuaternionDoubleCoverUniqueness.central_involution_mem_preimage (nu t (tInC t)) (barKappa t)
      (barKappa_kernel t) (CFSG.generalizedFitting (Gamma t))
  refine ⟨F, hfield, hfinite, data.field_card, eta, htQ, heta htQ, hsolv, Nat.card A,
    data.field_group_odd, ?_⟩
  have hLJ : CFSG.generalizedFitting (Gamma t) ≤ J t := simple_le_index_two _ _ hJindex hnonab
  have hQJ : qdlocQ t ≤ (J t).comap (barKappa t) := Subgroup.comap_mono hLJ
  have hJ' : ((J t).comap (barKappa t)).index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ (barKappa_surjective t), hJindex]
  rw [← Subgroup.relIndex_mul_index hQJ, hJ', mul_comm]
  congr 1

end Layer

section Cover

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

private theorem qdloc_not_cover
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : ProperSubgroupRegularity.SmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht2 : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hQD : IsQDGroup H) (hO : oddCoreIn H ≠ ⊥) (s' : G) (hs' : orderOf s' = 2)
    (hs'C : s' ∈ C t) (hts' : t ≠ s') (htH : t ∈ H) (hs'H : s' ∈ H)
    (hcov : qdlocA t H = qdlocQ t) : False := by
  have hVH : Subgroup.closure ({t, s'} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact htH
    · exact hs'H
  have hR : CFSG.pPrimeCore 2 H ≠ ⊥ := by
    intro hbot
    apply hO
    rw [oddCoreIn, QuaternionFocalFactorization.oddCore_eq_twoPrimeCore, hbot, Subgroup.map_bot]
  obtain ⟨-, K, hK⟩ :=
    LocalCoverFactorization.original_layer_cover_nontrivial_odd_core_forces_index_two
      G hGnonab hrec n hn S fS t s' ht2 hs' hs'C hts' hnonab hcentral hnc p f hp hpodd hf hq.le
      hmodel H hVH hR hcov
  exact hQD.noIndexTwo K hK

omit [Finite G] [IsSimpleGroup G] in
private theorem qdloc_exists_second_involution {m : ℕ} (hm : 4 ≤ m) (H P : Subgroup G)
    (f : SemidihedralGroup m ≃* P) (hPH : P ≤ H) (t : G) (hft : (f (z m) : G) = t) :
    ∃ s' : G, orderOf s' = 2 ∧ s' ∈ C t ∧ t ≠ s' ∧ s' ∈ H := by
  have hs2 := orderOf_s m (by omega)
  refine ⟨f (s m), ?_, ?_, ?_, hPH (f (s m)).2⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hs2]
  · rw [Subgroup.mem_centralizer_singleton_iff, ← hft]
    have hc := Subgroup.mem_center_iff.mp (z_mem_center m hm) (s m)
    have := congrArg (fun x => ((f x : P) : G)) hc
    simpa only [map_mul, Subgroup.coe_mul] using this
  · intro h
    rw [← hft] at h
    have hsz : s m = z m := f.injective (Subtype.ext h.symm)
    have hconj := sd_s_conj_quarter hm
    rw [hsz, (Subgroup.mem_center_iff.mp (z_mem_center m hm) _).symm, mul_inv_cancel_right]
      at hconj
    exact sd_quarter_ne_inv hm hconj

end Cover

section Section

variable {G : Type} [Group G] [Finite G]

private theorem qdloc_section_char_power
    {t : G} {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hpodd : Odd p) (hF : Nat.card F = p ^ f)
    (eta : qdlocQ t ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hsolv : Group.IsSolvable (H t ⧸ qdlocQ t))
    {B : Type*} [Group B] [Finite B] (ι : B →* C t) (hι : Function.Injective ι) {r : ℕ}
    (hr : HasNormalSL2 (B ⧸ CFSG.oddCore B) r) (hr7 : 7 ≤ r) (hrodd : Odd r) :
    (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧ r = p ^ m) ∧ (r = p ^ f → qdlocQ t ≤ ι.range.map (nu t)) := by
  obtain ⟨L, E, hE, hEfin, hLn, hEcard, ⟨eL⟩⟩ := hr
  let β : B →* H t := (nu t).comp ι
  have hβ : Odd (Nat.card β.ker) := by
    have hNodd : Odd (Nat.card (N t)) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
    have hle : β.ker.map ι ≤ N t := by
      rintro _ ⟨b, hb, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hb
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective hι] at h1
    exact hNodd.of_dvd_nat h1
  have hE4 : 4 ≤ Nat.card E := by omega
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) E) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card E hE4
  have hLperf : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  obtain ⟨Y, hYperf, hYQ, hYX, hYsurj, -⟩ :=
    SL2Sections.exists_perfect_section β hβ (qdlocQ t) hsolv (CFSG.oddCore B)
      (odd_card_oddCore B) L hLperf
  have := hYperf
  let φ₀ : Y →* qdlocQ t := (β.comp Y.subtype).codRestrict (qdlocQ t) fun y => hYQ y y.2
  let φ : Y →* Matrix.SpecialLinearGroup (Fin 2) F := eta.toMonoidHom.comp φ₀
  have hφ : Odd (Nat.card φ.ker) := by
    have hle : φ.ker.map Y.subtype ≤ β.ker := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : eta (φ₀ y) = 1 := hy
      rw [map_eq_one_iff _ eta.injective] at h1
      exact congrArg Subtype.val h1
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective Y.subtype_injective] at h1
    exact hβ.of_dvd_nat h1
  let ψ : Y →* Matrix.SpecialLinearGroup (Fin 2) E := eL.toMonoidHom.comp
    (((QuotientGroup.mk' (CFSG.oddCore B)).comp Y.subtype).codRestrict L fun y => hYX y y.2)
  have hψ : Function.Surjective ψ := by
    intro w
    obtain ⟨y, hy, hyx⟩ := hYsurj _ (eL.symm w).2
    refine ⟨⟨y, hy⟩, ?_⟩
    change eL ⟨QuotientGroup.mk' (CFSG.oddCore B) y, _⟩ = w
    rw [← eL.apply_symm_apply w]
    congr 1
    exact Subtype.ext hyx
  obtain ⟨⟨m, hm, hmf, hmr⟩, hsurj⟩ := SL2Sections.sl2_section_char_power hpodd hF
    (hEcard ▸ hr7) (hEcard ▸ hrodd) φ hφ ψ hψ
  refine ⟨⟨m, hm, hmf, hEcard ▸ hmr⟩, fun hrq => ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := hsurj (hEcard.trans hrq) (eta ⟨x, hx⟩)
  have h1 : φ₀ y = ⟨x, hx⟩ := eta.injective hy
  exact ⟨ι y, ⟨y, rfl⟩, congrArg Subtype.val h1⟩

end Section

theorem frontier_localQD_charPower
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G) :
    ∀ H : Subgroup G, (∃ r : ℕ, r.Prime ∧ IsPLocal r H) → IsQDGroup H →
      ∀ r : ℕ, HasQDCharPower H r → r = 3 ∨ r = 5 ∨
        (r ∣ (frontierSetting S fS t p f).q ∧ r ≠ (frontierSetting S fS t p f).q) := by
  intro K hloc hQD r hr
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hzt, ht2, -, -, -, -⟩ := Principal.supplied_t_s_facts hn fS ht
  have hG := Principal.index_ne_two_of_isSimpleGroup hGnonab
  have hSD : ∀ P : Sylow 2 K, ∃ m : ℕ, 4 ≤ m ∧ Nonempty (SemidihedralGroup m ≃* P) :=
    qdloc_exists_sd_model hn S fS K hQD.sylow
  have hO := qdloc_oddCoreIn_ne_bot K hloc hQD hSD
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨m₀, hm₀, ⟨f₀⟩⟩ := hSD P₀
  set y : G := ((f₀ (z m₀) : K) : G) with hy
  have hyK : y ∈ K := (f₀ (z m₀) : K).2
  have hy2 : orderOf y = 2 := by
    rw [hy, Subgroup.orderOf_coe, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_z m₀ (by omega)
  obtain ⟨m, P, fP, hm, hPK, hfy⟩ := qdloc_exists_centered K hQD hSD y hyK hy2
  obtain ⟨y₂, hy₂2, hy₂C, hyy₂, hy₂K⟩ := qdloc_exists_second_involution hm K P fP hPK y hfy
  have hyt : IsConj y t := by
    have h := InvolutionFusion.ambient_involution_isConj_z n hn S fS hG y hy2
    rwa [hzt] at h
  obtain ⟨g, hg⟩ := isConj_iff.mp hyt
  have hy2' : orderOf (⟨y, hyK⟩ : K) = 2 := by rw [Subgroup.orderOf_mk, hy2]
  obtain ⟨-, hrodd, hrSL⟩ := hr.2 ⟨y, hyK⟩ hy2'
  obtain ⟨-, E, hE, hEfin, -, hEcard, -⟩ := hrSL
  have hr2 : 2 ≤ r := hEcard ▸ Finite.one_lt_card
  by_cases hr3 : r = 3
  · exact Or.inl hr3
  by_cases hr5 : r = 5
  · exact Or.inr (Or.inl hr5)
  right
  right
  have hr7 : 7 ≤ r := by
    obtain ⟨k, hk⟩ := hrodd
    omega
  let B := Subgroup.centralizer ({(⟨y, hyK⟩ : K)} : Set K)
  have hιC : ∀ b : B, (MulAut.conj g).toMonoidHom (K.subtype (B.subtype b)) ∈ C t := by
    intro b
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have hb := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp b.2)
    change ((b : K) : G) * y = y * ((b : K) : G) at hb
    change g * ((b : K) : G) * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * ((b : K) : G) * g⁻¹)
    calc g * ((b : K) : G) * g⁻¹ * (g * y * g⁻¹) = g * (((b : K) : G) * y) * g⁻¹ := by group
      _ = g * (y * ((b : K) : G)) * g⁻¹ := by rw [hb]
      _ = g * y * g⁻¹ * (g * ((b : K) : G) * g⁻¹) := by group
  let ι : B →* C t :=
    ((MulAut.conj g).toMonoidHom.comp (K.subtype.comp B.subtype)).codRestrict (C t) hιC
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext ((MulAut.conj g).injective h1))
  obtain ⟨F, hF, hFin, hFcard, eta, -, -, hsolv, -⟩ :=
    qdloc_layer_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hq hmodel
  obtain ⟨⟨k, hk, hkf, hrk⟩, hcov⟩ := qdloc_section_char_power hpodd hFcard eta hsolv ι hι
    (hr.2 ⟨y, hyK⟩ hy2').2.2 hr7 hrodd
  refine ⟨?_, fun hrq => ?_⟩
  · change r ∣ p ^ f
    rw [hrk]
    exact pow_dvd_pow p (Nat.le_of_dvd (by omega) hkf)
  ·
    let K' : Subgroup G := K.map (MulAut.conj g).toMonoidHom
    have hQ := hcov hrq
    have hcov' : qdlocA t K' = qdlocQ t := by
      refine le_antisymm (qdlocA_le t K') fun x hx => ?_
      obtain ⟨c, ⟨b, rfl⟩, rfl⟩ := hQ hx
      exact mem_qdlocA ⟨(b : K), (b : K).2, rfl⟩ hx
    let e : K ≃* K' := K.equivMapOfInjective _ (MulAut.conj g).injective
    have hQD' : IsQDGroup K' := hQD.of_mulEquiv e
    have hO' : oddCoreIn K' ≠ ⊥ := by
      intro hbot
      apply hO
      have hmap : (CFSG.oddCore K).map e.toMonoidHom = CFSG.oddCore K' := by
        rw [QuaternionFocalFactorization.oddCore_eq_twoPrimeCore,
          QuaternionFocalFactorization.oddCore_eq_twoPrimeCore]
        exact CFSG.pPrimeCore_map_iso 2 e
      have h1 : CFSG.oddCore K' = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ K'.subtype_injective).mp hbot
      rw [h1, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hmap
      rw [oddCoreIn, hmap, Subgroup.map_bot]
    have hrec' := PerfectLayerNormalization.original_smaller_simple_recognition_transport
      (Equiv.refl G) hrec
    refine qdloc_not_cover hGnonab hrec' n hn S fS t ht2 hnonab hcentral hnc p f hp hpodd hf hq
      hmodel K' hQD' hO' (g * y₂ * g⁻¹) ?_ ?_ ?_ ⟨y, hyK, hg⟩ ⟨y₂, hy₂K, rfl⟩ hcov'
    · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy₂2]
    · rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hy₂C
      calc g * y₂ * g⁻¹ * (g * y * g⁻¹) = g * (y₂ * y) * g⁻¹ := by group
        _ = g * (y * y₂) * g⁻¹ := by rw [hc]
        _ = g * y * g⁻¹ * (g * y₂ * g⁻¹) := by group
    · rw [← hg]
      intro h
      exact hyy₂ ((MulAut.conj g).injective h)

section NotQD

variable {G : Type} [Group G] [Finite G]

private theorem qdloc_le_of_isPerfect {M : Type*} [Group M] (Q : Subgroup M) [Q.Normal]
    (hsolv : Group.IsSolvable (M ⧸ Q)) (X : Subgroup M) (hX : Group.IsPerfect X) : X ≤ Q := by
  have := hsolv
  have := hX
  have hXperf : Group.IsPerfect (X.map (QuotientGroup.mk' Q)) := Group.IsPerfect.map _
  have hbot : X.map (QuotientGroup.mk' Q) = ⊥ := by
    by_contra hne
    have : Nontrivial (X.map (QuotientGroup.mk' Q)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (X.map (QuotientGroup.mk' Q)) inferInstance
  intro x hx
  have h1 : QuotientGroup.mk' Q x ∈ X.map (QuotientGroup.mk' Q) := Subgroup.mem_map_of_mem _ hx
  rw [hbot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).mp h1

private theorem qdloc_eight_dvd (t : G) (K P : Subgroup G) (hPK : P ≤ K) (hPC : P ≤ C t)
    {m : ℕ} (hm : 4 ≤ m) (hP : Nat.card P = 2 ^ m) {a : ℕ} (ha : Odd a)
    (hidx : (qdlocQ t).index = 2 * a) : 8 ∣ Nat.card (qdlocA t K) := by
  set Bt := K.subgroupOf (C t) with hBt
  set Y := localLayerPreimage t with hY
  have : Y.Normal := localLayerPreimage_normal t
  have h16 : 16 ∣ Nat.card Bt := by
    have hle : P.subgroupOf (C t) ≤ Bt := Subgroup.comap_mono hPK
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, hP] at h1
    exact (pow_dvd_pow 2 hm).trans h1
  have hcard : Nat.card (Bt ⊓ Y : Subgroup (C t)) * Y.relIndex Bt = Nat.card Bt := by
    have h1 := Subgroup.card_mul_index ((Bt ⊓ Y).subgroupOf Bt)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      Subgroup.inf_subgroupOf_left] at h1
    exact h1
  have hYidx : Y.index = 2 * a := by
    rw [hY, localLayerPreimage, Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective _)]
    exact hidx
  have hdvd : Y.relIndex Bt ∣ 2 * a := hYidx ▸ Subgroup.relIndex_dvd_index_of_normal Y Bt
  have h8 : 8 ∣ Nat.card (Bt ⊓ Y : Subgroup (C t)) := by
    have h1 : 16 ∣ Nat.card (Bt ⊓ Y : Subgroup (C t)) * (2 * a) :=
      h16.trans (hcard ▸ Nat.mul_dvd_mul_left _ hdvd)
    have h2 : 8 ∣ Nat.card (Bt ⊓ Y : Subgroup (C t)) * a := by
      obtain ⟨k, hk⟩ := h1
      exact ⟨k, by linarith⟩
    have hc : Nat.Coprime 8 a := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ha)
    exact hc.dvd_of_dvd_mul_right h2
  let ν := (nu t).comp (Bt ⊓ Y).subtype
  have hν : ν.range = qdlocA t K := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Odd (Nat.card ν.ker) := by
    have hNodd : Odd (Nat.card (N t)) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
    have hle : ν.ker.map (Bt ⊓ Y).subtype ≤ N t := by
      rintro _ ⟨b, hb, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hb
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h1
    exact hNodd.of_dvd_nat h1
  have hprod := SL2Sections.card_ker_mul_card_range ν
  rw [hν] at hprod
  rw [← hprod] at h8
  have hc : Nat.Coprime 8 (Nat.card ν.ker) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hker)
  exact hc.dvd_of_dvd_mul_left h8

open ActualFourGroupCentralizer in
private theorem qdloc_torus (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t : G) (ht2 : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hsolv : Group.IsSolvable (H t ⧸ qdlocQ t))
    (K : Subgroup G) (sC : C t) (hsC2 : orderOf sC = 2) (hsCt : sC ≠ tInC t)
    (hcov : ∀ c : C t, (c : G) * (sC : G) = sC * c → nu t c ∈ qdlocQ t → nu t c ∈ qdlocA t K) :
    ∃ x₀ ∈ qdlocA t K, orderOf x₀ = MatrixTorus.torusSize (p ^ f) / 2 ∧
      x₀ * nu t sC = nu t sC * x₀ ∧
      Nat.card (Subgroup.centralizer ({nu t sC} : Set (H t))) ≤
        4 * (f * (MatrixTorus.torusSize (p ^ f) / 2)) := by
  obtain ⟨-, F₂, hF₂, hF₂fin, A₂, a₂, hF₂card, -, hA₂f, -, -, -, -, -, -, -, htorus, hcent⟩ :=
    actual_simple_layer_four_group_centralizer_odd_core n hn S fS hG t ht2
      hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, -, hPsiU, hdata, -, hDmap, -, -⟩ := hcent sC hsC2 hsCt
  have := htorus.odd_cyclic
  obtain ⟨w₀, hw₀⟩ := IsCyclic.exists_generator
    (α := MatrixTorus.W F₂ (MatrixCover.fixedUnit F₂ A₂ a₂))
  have hw₀ord : orderOf w₀ = MatrixTorus.torusSize (p ^ f) / 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hw₀, htorus.odd_card, hF₂card]
  let ιW : MatrixTorus.W F₂ (MatrixCover.fixedUnit F₂ A₂ a₂) →* H t :=
    Psi.toMonoidHom.comp ((MatrixTorus.originalSlInH F₂ (MatrixCover.fixedUnit F₂ A₂ a₂) A₂
      (fixed_coefficient_action F₂ A₂ a₂)).comp
      ((MatrixTorus.Torus F₂ (MatrixCover.fixedUnit F₂ A₂ a₂)).subtype.comp
        (MatrixTorus.W F₂ (MatrixCover.fixedUnit F₂ A₂ a₂)).subtype))
  have hιW : Function.Injective ιW := by
    intro x y hxy
    have h1 := Psi.injective hxy
    have h2 := SemidirectProduct.inl_injective h1
    have h3 := MatrixCoverData.inclusion_injective F₂ _ h2
    exact Subtype.ext (Subtype.ext h3)
  set x₀ := ιW w₀ with hx₀def
  have hx₀ord : orderOf x₀ = MatrixTorus.torusSize (p ^ f) / 2 :=
    (orderOf_injective ιW hιW w₀).trans hw₀ord
  have hx₀B : x₀ ∈ B F₂ A₂ (MatrixCover.fixedUnit F₂ A₂ a₂)
      (fixed_coefficient_action F₂ A₂ a₂) Psi := by
    rw [hdata.odd_factor_range]
    exact ⟨SemidirectProduct.inl w₀, rfl⟩
  have hx₀Q : x₀ ∈ qdlocQ t := by
    have hF₂4 : 4 ≤ Nat.card F₂ := by omega
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F₂) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F₂ hF₂4
    let φ := Psi.toMonoidHom.comp (MatrixTorus.originalSlInH F₂ (MatrixCover.fixedUnit F₂ A₂ a₂)
      A₂ (fixed_coefficient_action F₂ A₂ a₂))
    have hperf : Group.IsPerfect φ.range :=
      Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    exact qdloc_le_of_isPerfect (qdlocQ t) hsolv φ.range hperf ⟨_, rfl⟩
  have hx₀c : x₀ * nu t sC = nu t sC * x₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (B_le_centralizer F₂ A₂ sC _ _ Psi hPsiU hx₀B)
  obtain ⟨gR, hgR, -, hgRv⟩ := hdata.restricted_nu
  obtain ⟨rr, hrr⟩ := hgR ⟨x₀, hx₀B⟩
  have hx₀ : nu t ((rr : D sC) : C t) = x₀ := by
    rw [← hgRv rr, hrr]
  have hcomm : (((rr : D sC) : C t) : G) * sC = sC * ((rr : D sC) : C t) := by
    have hmem : (((rr : D sC) : C t) : G) ∈ C t ⊓ Subgroup.centralizer {(sC : G)} := by
      rw [← hDmap]
      exact ⟨_, (rr : D sC).2, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  have hx₀A : x₀ ∈ qdlocA t K := by
    rw [← hx₀]
    exact hcov _ hcomm (hx₀ ▸ hx₀Q)
  refine ⟨x₀, hx₀A, hx₀ord, hx₀c, ?_⟩
  obtain ⟨e, -⟩ := hdata.quotient_direct
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hdata.odd_factor_card]
  have hV : Nat.card (QuotientV sC) ≤ 4 := by
    rw [← hdata.lifted.four_card]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have hA : Nat.card A₂ ≤ f := Nat.le_of_dvd (by omega) hA₂f
  calc Nat.card (QuotientV sC) * (Nat.card A₂ * (MatrixTorus.torusSize (p ^ f) / 2))
      ≤ 4 * (Nat.card A₂ * (MatrixTorus.torusSize (p ^ f) / 2)) := Nat.mul_le_mul_right _ hV
    _ ≤ 4 * (f * (MatrixTorus.torusSize (p ^ f) / 2)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA)

private theorem qdloc_torusSize_cases {q : ℕ} (hq : Odd q) :
    (q % 4 = 1 ∧ 2 * (MatrixTorus.torusSize q / 2) = q + 1) ∨
      (q % 4 = 3 ∧ 2 * (MatrixTorus.torusSize q / 2) = q - 1) := by
  have h := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq)
  unfold MatrixTorus.torusSize
  rcases h with h | h
  · left
    rw [ite_eq_left_iff.mpr (fun h' => absurd h h')]
    omega
  · right
    rw [ite_eq_right_iff.mpr (fun h' => by omega)]
    omega

private theorem qdloc_sq_of_mem_zpowers {Y : Type*} [Group Y] {z v : Y} (hz : z * z = 1)
    (hv : v ∈ Subgroup.zpowers z) : v * v = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz, one_zpow]

private theorem qdloc_cover_of_torus
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (K : Subgroup G) (htK : t ∈ K) (hsK : (fS (s n) : G) ∈ K)
    (hcov : ∀ c : C t, (c : G) * (fS (s n) : G) = fS (s n) * c → nu t c ∈ qdlocQ t →
      nu t c ∈ qdlocA t K)
    (h8 : 8 ∣ Nat.card (qdlocA t K)) : qdlocA t K = qdlocQ t := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hG := Principal.index_ne_two_of_isSimpleGroup hGnonab
  set sC : C t := ⟨fS (s n), hsC⟩ with hsCdef
  have hsC2 : orderOf sC = 2 := by rw [Subgroup.orderOf_mk]; exact hs2
  have hsCt : sC ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  have hsC1 : sC * sC = 1 := Subtype.ext (by
    change (fS (s n) : G) * fS (s n) = 1
    have := pow_orderOf_eq_one (fS (s n) : G)
    rwa [hs2, pow_two] at this)
  obtain ⟨F, hF, hFin, hFcard, eta, htQ, heta, hsolv, a, ha, hidx⟩ :=
    qdloc_layer_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hFodd : Odd (Nat.card F) := by rw [hFcard]; exact hpodd.pow
  have h2F : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hFodd
  set tb : H t := nu t (tInC t) with htb
  have htbc : tb ∈ Subgroup.center (H t) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
      (Subgroup.mem_map_of_mem _ (tInC_central t))
  have htb2 : tb * tb = 1 := by
    rw [htb, ← map_mul]
    have : tInC t * tInC t = 1 := Subtype.ext (by
      change t * t = 1
      rw [← pow_two, ← ht2, pow_orderOf_eq_one])
    rw [this, map_one]
  obtain ⟨x₀, hx₀A, hx₀ord, hx₀c, hcent⟩ := qdloc_torus n hn S fS hG t ht2 hnonab hcentral hnc
    p f hp hpodd hf hq hmodel hsolv K sC hsC2 hsCt hcov
  set w := MatrixTorus.torusSize (p ^ f) / 2 with hwdef
  have hw := qdloc_torusSize_cases (q := p ^ f) hpodd.pow
  rw [← hwdef] at hw
  have hwodd : w % 2 = 1 := by rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  let Θ : qdlocQ t →* PSL2MatrixGroup F :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
      eta.toMonoidHom
  have hΘker : ∀ v : qdlocQ t, Θ v = 1 → (v : H t) ∈ Subgroup.zpowers tb := by
    intro v hv
    have hc : eta v ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      (QuotientGroup.eq_one_iff _).mp hv
    rcases (SL2Sections.mem_center_sl2_iff hFodd _).mp hc with h1 | h1
    · rw [(map_eq_one_iff _ eta.injective).mp h1]
      exact Subgroup.one_mem _
    · rw [← heta] at h1
      rw [eta.injective h1]
      exact Subgroup.mem_zpowers _
  have htbA : tb ∈ qdlocA t K := mem_qdlocA (c := tInC t) htK htQ
  let θ₀ : qdlocA t K →* PSL2MatrixGroup F := Θ.comp (Subgroup.inclusion (qdlocA_le t K))
  have hθ₀ker : ∀ u : qdlocA t K, θ₀ u = 1 → (u : H t) ∈ Subgroup.zpowers tb :=
    fun u hu => hΘker (Subgroup.inclusion (qdlocA_le t K) u) hu
  have hkercard : Nat.card θ₀.ker = 2 := by
    have hmap : θ₀.ker.map (qdlocA t K).subtype = Subgroup.zpowers tb := by
      apply le_antisymm
      · rintro _ ⟨u, hu, rfl⟩
        exact hθ₀ker u hu
      · rw [Subgroup.zpowers_le]
        refine ⟨⟨tb, htbA⟩, ?_, rfl⟩
        change (QuotientGroup.mk' _) (eta ⟨tb, htQ⟩) = 1
        rw [heta]
        exact (QuotientGroup.eq_one_iff _).mpr ((SL2Sections.mem_center_sl2_iff hFodd _).mpr
          (Or.inr rfl))
    rw [← Subgroup.card_map_of_injective (qdlocA t K).subtype_injective, hmap, Nat.card_zpowers]
    have hord : orderOf (⟨tb, htQ⟩ : qdlocQ t) = 2 := by
      rw [← MulEquiv.orderOf_eq eta, heta]
      exact OddFieldSL2.minusIdentity_orderOf F h2F
    rw [Subgroup.orderOf_mk] at hord
    exact hord
  have hAcard := SL2Sections.card_ker_mul_card_range θ₀
  rw [hkercard] at hAcard
  have h4 : 4 ∣ Nat.card θ₀.range := by
    rw [← hAcard] at h8
    obtain ⟨k, hk⟩ := h8
    exact ⟨k, by omega⟩
  set x : θ₀.range := θ₀.rangeRestrict ⟨x₀, hx₀A⟩ with hxdef
  have hxord : orderOf x = w := by
    rw [hxdef, ← Subgroup.orderOf_coe, MonoidHom.coe_rangeRestrict]
    apply Nat.dvd_antisymm
    · rw [← hx₀ord, ← Subgroup.orderOf_mk x₀ hx₀A]
      exact orderOf_map_dvd _ _
    · have h1 : θ₀ (⟨x₀, hx₀A⟩ ^ orderOf (θ₀ ⟨x₀, hx₀A⟩)) = 1 := by
        rw [map_pow, pow_orderOf_eq_one]
      have h2 := qdloc_sq_of_mem_zpowers htb2 (hθ₀ker _ h1)
      have h3 : x₀ ^ (2 * orderOf (θ₀ ⟨x₀, hx₀A⟩)) = 1 := by
        rw [pow_mul', pow_two]
        simpa only [Subgroup.coe_pow] using h2
      have h4 := orderOf_dvd_of_pow_eq_one h3
      rw [hx₀ord] at h4
      have hc2 : Nat.Coprime w 2 := by
        rw [Nat.coprime_two_right]
        exact Nat.odd_iff.mpr hwodd
      exact hc2.dvd_of_dvd_mul_left h4
  have hsQ : nu t sC ∉ qdlocQ t := by
    intro hmem
    have hNodd : Odd (Nat.card (N t)) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
    have hnot : ∀ y : C t, y ∈ N t → y * y = 1 → y = 1 := by
      intro y hy hy2
      by_contra hy1
      have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
      have := Subgroup.orderOf_dvd_natCard (N t) hy
      rw [hord] at this
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr this)
    have hsne : nu t sC ≠ 1 := by
      intro h1
      have h2 := hnot sC ((QuotientGroup.eq_one_iff _).mp h1) hsC1
      rw [h2, orderOf_one] at hsC2
      omega
    have hord : orderOf (⟨nu t sC, hmem⟩ : qdlocQ t) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_two, ← map_mul, hsC1, map_one]) hsne
    rw [← MulEquiv.orderOf_eq eta, OddFieldSL2.orderOf_eq_two_iff F h2F] at hord
    have heq : (⟨nu t sC, hmem⟩ : qdlocQ t) = ⟨tb, htQ⟩ := eta.injective (hord.trans heta.symm)
    have h1 : nu t (sC * (tInC t)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr (congrArg Subtype.val heq)
    have hcomm : sC * tInC t = tInC t * sC :=
      Subgroup.mem_center_iff.mp (tInC_central t) sC
    have ht1 : tInC t * tInC t = 1 := Subtype.ext (by
      change t * t = 1
      rw [← pow_two, ← ht2, pow_orderOf_eq_one])
    have hy2 : sC * (tInC t)⁻¹ * (sC * (tInC t)⁻¹) = 1 := by
      have htinv : (tInC t)⁻¹ = tInC t := inv_eq_of_mul_eq_one_right ht1
      rw [htinv]
      calc sC * tInC t * (sC * tInC t) = sC * (tInC t * sC) * tInC t := by group
        _ = sC * (sC * tInC t) * tInC t := by rw [hcomm]
        _ = 1 := by rw [← mul_assoc, hsC1, one_mul, ht1]
    have := hnot _ ((QuotientGroup.eq_one_iff _).mp h1) hy2
    exact hsCt (mul_inv_eq_one.mp this)
  have hsA : nu t sC ∉ qdlocA t K := fun h => hsQ (qdlocA_le t K h)
  rcases SL2Sections.psl2_subgroup_eq_top_or_small hpodd hFcard hq hw θ₀.range h4 x hxord with
    htop | ⟨hw3, hA4 | hS4⟩ | ⟨hw5, hA5⟩
  ·
    have hcov' : qdlocA t K = qdlocQ t := by
      refine le_antisymm (qdlocA_le t K) fun v hv => ?_
      have hmem : Θ ⟨v, hv⟩ ∈ θ₀.range := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨u, hu⟩ := hmem
      have h1 : Θ ((Subgroup.inclusion (qdlocA_le t K) u)⁻¹ * ⟨v, hv⟩) = 1 := by
        rw [map_mul, map_inv]
        exact inv_mul_eq_one.mpr hu
      have h2 := hΘker _ h1
      have h3 : ((u : H t))⁻¹ * v ∈ qdlocA t K :=
        (Subgroup.zpowers_le.mpr htbA) h2
      have h4 := (qdlocA t K).mul_mem u.2 h3
      rwa [mul_inv_cancel_left] at h4
    exact hcov'
  all_goals
    exfalso
    have hgU : ∀ u ∈ qdlocA t K, nu t sC * u * (nu t sC)⁻¹ ∈ qdlocA t K := by
      rintro _ ⟨c, ⟨hcK, hcY⟩, rfl⟩
      refine ⟨sC * c * sC⁻¹, ⟨?_, ?_⟩, by rw [map_mul, map_mul, map_inv]⟩
      · exact K.mul_mem (K.mul_mem hsK hcK) (K.inv_mem hsK)
      · exact (localLayerPreimage_normal t).conj_mem c hcY sC
    have hg2 : nu t sC * nu t sC = 1 := by
      rw [← map_mul, hsC1, map_one]
    have hθ : Function.Surjective θ₀.rangeRestrict := θ₀.rangeRestrict_surjective
    have hrr : ∀ u : qdlocA t K, (θ₀.rangeRestrict u : PSL2MatrixGroup F) = θ₀ u := fun _ => rfl
    have hker : ∀ u : qdlocA t K, θ₀.rangeRestrict u = 1 →
        θ₀.rangeRestrict ⟨nu t sC * u * (nu t sC)⁻¹, hgU u u.2⟩ = 1 := by
      intro u hu
      have hu' : (u : H t) ∈ Subgroup.zpowers tb :=
        hθ₀ker u (congrArg Subtype.val hu)
      have hcu : nu t sC * u * (nu t sC)⁻¹ = u := by
        have hcomm : (u : H t) * nu t sC = nu t sC * u :=
          (Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr htbc) hu') (nu t sC)).symm
        rw [← hcomm, mul_inv_cancel_right]
      have : (⟨nu t sC * u * (nu t sC)⁻¹, hgU u u.2⟩ : qdlocA t K) = u := Subtype.ext hcu
      rw [this, hu]
    obtain ⟨σ, hσ2, hσ⟩ := SL2Sections.exists_mulAut_of_conj (qdlocA t K) θ₀.rangeRestrict hθ
      (nu t sC) hgU hg2 hker
    have hσc : σ x = x := by
      rw [hxdef, hσ]
      congr 1
      apply Subtype.ext
      change nu t sC * x₀ * (nu t sC)⁻¹ = x₀
      rw [← hx₀c, mul_inv_cancel_right]
    have hfix : ∀ u : qdlocA t K, σ (θ₀.rangeRestrict u) = θ₀.rangeRestrict u →
        nu t sC * u * (nu t sC)⁻¹ * (u : H t)⁻¹ ∈ Subgroup.zpowers tb := by
      intro u hu
      rw [hσ] at hu
      have h1 : θ₀ (⟨nu t sC * u * (nu t sC)⁻¹, hgU u u.2⟩ * u⁻¹) = 1 := by
        rw [map_mul, map_inv]
        exact mul_inv_eq_one.mpr (congrArg Subtype.val hu)
      exact hθ₀ker _ h1
  ·
    obtain ⟨e⟩ := hA4
    have hσ1 := SL2Sections.mulAut_eq_one_of_alternatingFour e σ hσ2 x (hxord.trans hw3) hσc
    have hle := SL2Sections.card_le_card_centralizer_of_conj_mem_zpowers (qdlocA t K) (nu t sC)
      tb htbc htb2 hsA fun u hu => hfix ⟨u, hu⟩ (by rw [hσ1, MulAut.one_apply])
    have hX : Nat.card θ₀.range = 12 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have hf1 : f = 1 := by
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        obtain ⟨k, hk⟩ := hpodd
        omega
      by_contra hf1
      have h9 : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos (by omega)
      have : 9 ≤ p ^ 2 := by nlinarith
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    rw [hX] at hAcard
    rw [hw3, hf1] at hcent
    omega
  ·
    obtain ⟨e⟩ := hS4
    have hfixA := SL2Sections.mulAut_fix_alternating_of_symmetricFour e σ hσ2 x
      (hxord.trans hw3) hσc
    let φ : qdlocA t K →* Equiv.Perm (Fin 4) := e.toMonoidHom.comp θ₀.rangeRestrict
    have hφ : Function.Surjective φ := e.surjective.comp hθ
    let U : Subgroup (H t) := ((alternatingGroup (Fin 4)).comap φ).map (qdlocA t K).subtype
    have hUcard : Nat.card U * 2 = Nat.card (qdlocA t K) := by
      rw [Subgroup.card_map_of_injective (qdlocA t K).subtype_injective]
      have h1 := Subgroup.card_mul_index ((alternatingGroup (Fin 4)).comap φ)
      rw [Subgroup.index_comap_of_surjective _ hφ, alternatingGroup.index_eq_two] at h1
      exact h1
    have hsU : nu t sC ∉ U := by
      rintro ⟨u, -, hu⟩
      exact hsA (hu ▸ u.2)
    have hle := SL2Sections.card_le_card_centralizer_of_conj_mem_zpowers U (nu t sC)
      tb htbc htb2 hsU fun v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact hfix u (hfixA _ hu)
    have hX : Nat.card θ₀.range = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    have hf1 : f = 1 := by
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        obtain ⟨k, hk⟩ := hpodd
        omega
      by_contra hf1
      have h9 : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos (by omega)
      have : 9 ≤ p ^ 2 := by nlinarith
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    rw [hX] at hAcard
    rw [hw3, hf1] at hcent
    omega
  ·
    obtain ⟨e⟩ := hA5
    have hσ1 := SL2Sections.mulAut_eq_one_of_alternatingFive e σ hσ2 x (hxord.trans hw5) hσc
    have hle := SL2Sections.card_le_card_centralizer_of_conj_mem_zpowers (qdlocA t K) (nu t sC)
      tb htbc htb2 hsA fun u hu => hfix ⟨u, hu⟩ (by rw [hσ1, MulAut.one_apply])
    have hX : Nat.card θ₀.range = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have hf2 : f ≤ 2 := by
      by_contra hf3
      have h27 : p ^ 3 ≤ p ^ f := Nat.pow_le_pow_right hp.pos (by omega)
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        obtain ⟨k, hk⟩ := hpodd
        omega
      have : 27 ≤ p ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    rw [hX] at hAcard
    rw [hw5] at hcent
    have : 4 * (f * 5) ≤ 40 := by omega
    omega

theorem frontier_not_qd_of_cover
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G) :
    ∀ H : Subgroup G, (frontierSetting S fS t p f).T ≤ H → oddCoreIn H ≠ ⊥ →
      (((frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L : Subgroup G) :
          Set G) ⊆
        (H : Set G) * (((frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).ON :
          Subgroup G) : Set G) →
      ¬ IsQDGroup H := by
  intro K hTK hO hcovL hQD
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hG := Principal.index_ne_two_of_isSimpleGroup hGnonab
  have hrec' := PerfectLayerNormalization.original_smaller_simple_recognition_transport
    (Equiv.refl G) hrec
  have htK : t ∈ K := hTK (Subgroup.subset_closure (Set.mem_insert _ _))
  have hsK : (fS (s n) : G) ∈ K := hTK (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  obtain ⟨F, hF, hFin, hFcard, eta, htQ, heta, hsolv, a, ha, hidx⟩ :=
    qdloc_layer_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hcov : ∀ c : C t, (c : G) * (fS (s n) : G) = fS (s n) * c → nu t c ∈ qdlocQ t →
      nu t c ∈ qdlocA t K := by
    intro c hcs hcQ
    have hcCL : (c : G) ∈ ((frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L) := by
      refine ⟨?_, ?_⟩
      · change (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure ({t, (fS (s n) : G)} : Set G) : Subgroup G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hle : Subgroup.closure ({t, (fS (s n) : G)} : Set G) ≤
            Subgroup.centralizer ({(c : G)} : Set G) := by
          rw [Subgroup.closure_le]
          rintro y (rfl | rfl)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
          · exact Subgroup.mem_centralizer_singleton_iff.mpr hcs.symm
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
      · exact Subgroup.mem_sup_left ⟨c, hcQ, rfl⟩
    obtain ⟨h, hh, m, hm, hhm⟩ := Set.mem_mul.mp (hcovL hcCL)
    have hmON := hm.2
    rw [frontierSetting_ON] at hmON
    obtain ⟨m', hm', rfl⟩ := hmON
    have hhC : h ∈ C t := by
      rw [eq_mul_inv_of_mul_eq hhm]
      exact (C t).mul_mem c.2 ((C t).inv_mem m'.2)
    have hkey : nu t ⟨h, hhC⟩ = nu t c := by
      have hc' : c = ⟨h, hhC⟩ * m' := Subtype.ext hhm.symm
      have hm1 : nu t m' = 1 := (QuotientGroup.eq_one_iff m').mpr hm'
      rw [hc', map_mul, hm1, mul_one]
    rw [← hkey]
    exact mem_qdlocA hh (hkey ▸ hcQ)
  have hSD := qdloc_exists_sd_model hn S fS K hQD.sylow
  obtain ⟨m, P, fP, hm, hPK, hfP⟩ := qdloc_exists_centered K hQD hSD t htK ht2
  have hPC : P ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hfP]
    obtain ⟨y, hy⟩ := fP.surjective ⟨x, hx⟩
    have hc := Subgroup.mem_center_iff.mp (z_mem_center m hm) y
    have := congrArg (fun w => ((fP w : P) : G)) hc
    simp only [map_mul, Subgroup.coe_mul, hy] at this
    exact this
  have hPcard : Nat.card P = 2 ^ m := by
    rw [← Nat.card_congr fP.toEquiv, CFSG.Semidihedral.card m (by omega)]
  have h8 := qdloc_eight_dvd t K P hPK hPC hm hPcard ha hidx
  exact qdloc_not_cover hGnonab hrec' n hn S fS t ht2 hnonab hcentral hnc p f hp hpodd hf hq
    hmodel K hQD hO (fS (s n)) hs2 hsC hst.symm htK hsK
    (qdloc_cover_of_torus hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
      K htK hsK hcov h8)

end NotQD

section QCover

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem qdloc_mem_centralizer_closure {a b c : G} (ha : c * a = a * c)
    (hb : c * b = b * c) :
    c ∈ Subgroup.centralizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ha.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hb.symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

private theorem qdloc_mem_layer_of_noIndexTwo (t : G) [(localLayerPreimage t).Normal]
    (hab : IsMulCommutative (C t ⧸ localLayerPreimage t)) {a : ℕ} (ha : Odd a)
    (hidx : (localLayerPreimage t).index = 2 * a) (K₀ : Subgroup (C t))
    (hK₀ : ∀ M : Subgroup K₀, M.index ≠ 2) (y : C t) (hy : y ∈ K₀) {k : ℕ}
    (hy2 : y ^ 2 ^ k = 1) : y ∈ localLayerPreimage t := by
  let π := QuotientGroup.mk' (localLayerPreimage t)
  have hcomm : ∀ x z : C t ⧸ localLayerPreimage t, x * z = z * x := fun x z =>
    hab.is_comm.comm x z
  let χ : K₀ →* C t ⧸ localLayerPreimage t :=
    { toFun := fun x => π x ^ a
      map_one' := by simp
      map_mul' := fun x z => by
        simp only [Subgroup.coe_mul, map_mul]
        exact (Commute.mul_pow (hcomm _ _) a) }
  have hcard : Nat.card (C t ⧸ localLayerPreimage t) = 2 * a := hidx
  have hrange : Nat.card χ.range ≤ 2 := by
    have h2 : IsPGroup 2 χ.range := by
      rintro ⟨_, ⟨x, rfl⟩⟩
      refine ⟨1, Subtype.ext ?_⟩
      change (π x ^ a) ^ 2 ^ 1 = 1
      rw [← pow_mul, pow_one, mul_comm, ← hcard, pow_card_eq_one']
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := h2.exists_card_eq
    have hdvd : 2 ^ j ∣ 2 * a := hj ▸ hcard ▸ Subgroup.card_subgroup_dvd_card _
    rw [hj]
    by_contra hlt
    have hj2 : 2 ≤ j := by
      by_contra hj1
      interval_cases j <;> simp_all
    have h4 : 4 ∣ 2 * a := (pow_dvd_pow 2 hj2).trans hdvd
    obtain ⟨m, hm⟩ := ha
    omega
  have hker : χ.ker = ⊤ := by
    have hidx' := Subgroup.index_ker χ
    have h0 : χ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : χ.ker.index ≠ 2 := hK₀ _
    have h1 : χ.ker.index = 1 := by omega
    exact Subgroup.index_eq_one.mp h1
  have hya : π y ^ a = 1 := by
    have : (⟨y, hy⟩ : K₀) ∈ χ.ker := by rw [hker]; exact Subgroup.mem_top _
    exact this
  have hy2' : π y ^ 2 ^ k = 1 := by rw [← map_pow, hy2, map_one]
  have hord : orderOf (π y) = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hya
    have h2 := orderOf_dvd_of_pow_eq_one hy2'
    have hc : Nat.Coprime a (2 ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr ha)
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h2
  rw [orderOf_eq_one_iff] at hord
  exact (QuotientGroup.eq_one_iff y).mp hord

theorem frontier_qCoverFact [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).QCoverFact := by
  intro K hKN hCK hQ
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hG := Principal.index_ne_two_of_isSimpleGroup hGnonab
  have hts : t * fS (s n) = fS (s n) * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have htK : t ∈ K := hCK (qdloc_mem_centralizer_closure rfl hts)
  have hsK : (fS (s n) : G) ∈ K := hCK (qdloc_mem_centralizer_closure hts.symm rfl)
  obtain ⟨F, hF, hFin, hFcard, eta, htQ, heta, hsolv, a, ha, hidx⟩ :=
    qdloc_layer_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hidx' : (localLayerPreimage t).index = 2 * a := by
    rw [localLayerPreimage, Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective _)]
    exact hidx
  obtain ⟨hab, -⟩ :=
    LocalLayerAbelianQuotients.original_local_layer_preimage_has_abelian_quotient_univ_zero
      n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hq.le hmodel
  have hcov : ∀ c : C t, (c : G) * (fS (s n) : G) = fS (s n) * c → nu t c ∈ qdlocQ t →
      nu t c ∈ qdlocA t K := by
    intro c hcs hcQ
    exact mem_qdlocA (hCK (qdloc_mem_centralizer_closure
      (Subgroup.mem_centralizer_singleton_iff.mp c.2) hcs)) hcQ
  obtain ⟨R, K₀, hK₀⟩ := hQ
  obtain ⟨k, hk, ⟨eY⟩⟩ := hK₀.quaternion.exists_quaternion_equiv
  let Y : Subgroup G := (K₀ ⊓ (R : Subgroup K)).map K.subtype
  have hYK : Y ≤ K := Subgroup.map_subtype_le _
  have hYC : Y ≤ C t := hYK.trans hKN
  have hYcard : Nat.card Y = 4 * 2 ^ k := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, Nat.card_congr eY.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hY8 : 8 ∣ Nat.card Y := by
    rw [hYcard]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨2 ^ j, by ring⟩
  let K₀C : Subgroup (C t) := (K₀.map K.subtype).subgroupOf (C t)
  have hK₀C : ∀ M : Subgroup K₀C, M.index ≠ 2 := by
    have hle : K₀.map K.subtype ≤ C t := (Subgroup.map_subtype_le _).trans hKN
    let e : K₀ ≃* K₀C := (K₀.equivMapOfInjective K.subtype K.subtype_injective).trans
      (Subgroup.subgroupOfEquivOfLe hle).symm
    exact noIndexTwo_of_mulEquiv e hK₀.noIndexTwo
  have hYL : Y.subgroupOf (C t) ≤ K.subgroupOf (C t) ⊓ localLayerPreimage t := by
    intro y hy
    refine ⟨hYK hy, ?_⟩
    obtain ⟨x, hx, hxy⟩ := hy
    have hxK₀ : (y : C t) ∈ K₀C := ⟨x, hx.1, hxy⟩
    obtain ⟨j, hj⟩ := (R.isPGroup' : IsPGroup 2 (R : Subgroup K)) ⟨x, hx.2⟩
    have hy2 : (y : C t) ^ 2 ^ j = 1 := by
      have hxy' : (x : G) = (y : G) := hxy
      have h1 : (x : G) ^ 2 ^ j = 1 := by
        have := congrArg (fun z : (R : Subgroup K) => ((z : K) : G)) hj
        simpa using this
      apply Subtype.ext
      simpa [← hxy'] using h1
    have : (localLayerPreimage t).Normal := localLayerPreimage_normal t
    exact qdloc_mem_layer_of_noIndexTwo t hab ha hidx' K₀C hK₀C y hxK₀ hy2
  have h8 : 8 ∣ Nat.card (qdlocA t K) := by
    let ν := (nu t).comp (Y.subgroupOf (C t)).subtype
    have hle : ν.range ≤ qdlocA t K := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y, hYL y.2, rfl⟩
    have hker : Odd (Nat.card ν.ker) := by
      have hNodd : Odd (Nat.card (N t)) :=
        Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
      have hle' : ν.ker.map (Y.subgroupOf (C t)).subtype ≤ N t := by
        rintro _ ⟨b, hb, rfl⟩
        exact (QuotientGroup.eq_one_iff _).mp hb
      have h1 := Subgroup.card_dvd_of_le hle'
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h1
      exact hNodd.of_dvd_nat h1
    have hprod := SL2Sections.card_ker_mul_card_range ν
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv] at hprod
    rw [← hprod] at hY8
    have hc : Nat.Coprime 8 (Nat.card ν.ker) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hker)
    exact (hc.dvd_of_dvd_mul_left hY8).trans (Subgroup.card_dvd_of_le hle)
  have hcov' := qdloc_cover_of_torus hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel K htK hsK hcov h8
  rintro _ ⟨c, hc, rfl⟩
  have hcA : nu t c ∈ qdlocA t K := hcov' ▸ hc
  obtain ⟨c', ⟨hc'K, -⟩, hc'⟩ := hcA
  refine Set.mem_mul.mpr ⟨c', hc'K, (c'⁻¹ * c : C t), ?_, by simp⟩
  rw [frontierSetting_ON]
  refine ⟨c'⁻¹ * c, ?_, rfl⟩
  have h1 : nu t (c'⁻¹ * c) = 1 := by rw [map_mul, map_inv, hc', inv_mul_cancel]
  exact (QuotientGroup.eq_one_iff _).mp h1

end QCover

end CFSG.Semidihedral.AllPrime
