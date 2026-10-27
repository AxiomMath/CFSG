module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteF
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneration
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
  CFSG.ComponentClassification.FooteLit

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_centralizer_le_gen (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {M : Subgroup G} (hMres : M ≤ oddResidualIn M)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (ε : M ⧸ pPrimeCore 2 M ≃* S)
    (hD : AschbacherKnownGroup.HasDihedralSylowTwo S)
    (hnab : ∀ P : Sylow 2 S, ∃ x ∈ (P : Subgroup S), ∃ y ∈ (P : Subgroup S), x * y ≠ y * x)
    {T : Subgroup G} (hTN : T ≤ normalizer (M : Set G)) (hTp : IsPGroup 2 T)
    (hTiso : ∃ P : Sylow 2 S, Nonempty ((P : Subgroup S) ≃* T))
    {V : Subgroup G} (hV : IsKleinFour V) (hVT : V ≤ T) {H' : Subgroup G}
    (hC : ∀ t ∈ T, orderOf t = 2 → M ⊓ centralizer ({t} : Set G) ≤ H') : M ≤ H' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : oddCoreIn M ≤ H' := by
    refine le_of_isKleinFour_inf_centralizer_le hV
      (fun x hx => mem_normalizer_oddCoreIn (hTN (hVT hx))) (odd_card_oddCoreIn M)
      fun w hw hw1 => (inf_le_inf_right _ (map_subtype_le _)).trans (hC w (hVT hw) ?_)
    exact orderOf_eq_prime (sq_eq_one_of_isKleinFour hV hw) hw1
  by_cases hA : ∃ t ∈ T, orderOf t = 2 ∧ t ∈ coreActionKernel M
  ·
    obtain ⟨t, htT, ht, htC⟩ := hA
    have ht2 : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have h1 := le_oddResidualIn_inf_centralizer_sup ht2 (zpowers_le.mpr htC) hMres
    rw [FooteLit.centralizer_zpowers_eq] at h1
    exact h1.trans (sup_le ((oddResidualIn_le _).trans (hC t htT ht)) hO)
  push Not at hA
  have hTC : ∀ x ∈ T, x ∈ coreActionKernel M → x = 1 := by
    intro x hxT hxC
    by_contra hx1
    obtain ⟨k, hk⟩ := (hTp.to_le (zpowers_le.mpr hxT)).exists_card_eq
    have hx2 : IsPGroup 2 (zpowers x) := hTp.to_le (zpowers_le.mpr hxT)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := zpowers x) 2 (by
      have h1 : 1 < Nat.card (zpowers x) := by
        rw [Nat.card_zpowers]
        exact lt_of_le_of_ne (orderOf_pos x) (fun h => hx1 (orderOf_eq_one_iff.mp h.symm))
      obtain ⟨n, hn⟩ := hx2.exists_card_eq
      rw [hn] at h1 ⊢
      exact dvd_pow_self 2 (by rintro rfl; simp at h1))
    have hyx : (y : G) ∈ zpowers x := y.2
    exact hA y ((zpowers_le.mpr hxT) hyx) (by rw [Subgroup.orderOf_coe]; exact hy)
      ((zpowers_le.mpr hxC) hyx)
  set N := normalizer (M : Set G) with hN
  set Φ : ↥N →* MulAut S := (MulAut.congr ε).toMonoidHom.comp (GSThmB.oddBarConj M) with hΦ
  have hker : ∀ x : N, Φ x = 1 → (x : G) ∈ coreActionKernel M := by
    intro x hx
    apply GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one
    have h1 : (MulAut.congr ε) (GSThmB.oddBarConj M x) = 1 := hx
    rwa [map_eq_one_iff _ (MulAut.congr ε).injective] at h1
  set T' := (T.subgroupOf N).map Φ with hT'
  have hinj : Function.Injective (Φ.comp (T.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    exact hTC _ x.2 (hker _ hx)
  have hrange : (Φ.comp (T.subgroupOf N).subtype).range = T' := by
    rw [MonoidHom.range_comp, range_subtype]
  let eT : ↥T ≃* ↥T' := (subgroupOfEquivOfLe hTN).symm.trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
  have hSnc : ∃ a b : S, a * b ≠ b * a := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 S))
    obtain ⟨x, -, y, -, hxy⟩ := hnab P
    exact ⟨x, y, hxy⟩
  have hT'p : IsPGroup 2 T' := (hTp.comap_subtype (K := N)).map Φ
  have hT'iso : ∃ P : Sylow 2 S, Nonempty ((P : Subgroup S) ≃* T') := by
    obtain ⟨P, ⟨eP⟩⟩ := hTiso
    exact ⟨P, ⟨eP.trans eT⟩⟩
  set V' := (V.subgroupOf N).map Φ with hV'
  have hV'T' : V' ≤ T' := map_mono fun x hx => hVT hx
  have hVN : V ≤ N := hVT.trans hTN
  have hinjV : Function.Injective (Φ.comp (V.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    exact hTC _ (hVT x.2) (hker _ hx)
  have hV' : IsKleinFour V' := by
    refine isKleinFour_of_card_eq_four ?_ ?_
    · have hrangeV : (Φ.comp (V.subgroupOf N).subtype).range = V' := by
        rw [MonoidHom.range_comp, range_subtype]
      rw [← hrangeV, ← Nat.card_congr (MonoidHom.ofInjective hinjV).toEquiv,
        ← hV.card_four]
      exact Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv
    · rintro _ ⟨x, hx, rfl⟩
      have hx2 : x ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact sq_eq_one_of_isKleinFour hV hx)
      rw [← map_pow, hx2, map_one]
  have hgen := footeL2_fix_generation hK hcalc hSnc hD hnab hT'p hT'iso hV' hV'T'
  set K := ⨆ (t : G) (_ : t ∈ T) (_ : orderOf t = 2), M ⊓ centralizer ({t} : Set G) with hKdef
  have hKH : K ≤ H' := iSup₂_le fun t ht => iSup_le fun ht2 => hC t ht ht2
  set π := QuotientGroup.mk' (pPrimeCore 2 M) with hπ
  have hKbar : (K.subgroupOf M).map π = ⊤ := by
    apply map_injective (f := ε.toMonoidHom) ε.injective
    rw [Subgroup.map_top_of_surjective _ ε.surjective, eq_top_iff, ← hgen]
    refine iSup₂_le fun τ hτ => iSup_le fun hτ2 => ?_
    obtain ⟨⟨t, htN⟩, htT, rfl⟩ := hτ
    have htT' : t ∈ T := htT
    have ht2 : orderOf t = 2 := by
      have h1 := orderOf_injective _ hinj (⟨⟨t, htN⟩, htT⟩ : T.subgroupOf N)
      have h2 : (Φ.comp (T.subgroupOf N).subtype) ⟨⟨t, htN⟩, htT⟩ = Φ ⟨t, htN⟩ := rfl
      rw [h2] at h1
      rw [h1, Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hτ2
      exact hτ2
    have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
    intro s hs
    have hs' : Φ ⟨t, htN⟩ s = s := hs
    obtain ⟨⟨y, hyM⟩, hy⟩ := QuotientGroup.mk_surjective (ε.symm s)
    have hfix : GSThmB.oddBarConj M ⟨t, htN⟩ ((⟨y, hyM⟩ : M) : M ⧸ pPrimeCore 2 M) =
        ((⟨y, hyM⟩ : M) : M ⧸ pPrimeCore 2 M) := by
      rw [hy]
      apply ε.injective
      have h1 : Φ ⟨t, htN⟩ s = ε (GSThmB.oddBarConj M ⟨t, htN⟩ (ε.symm s)) := by
        rw [hΦ, MonoidHom.comp_apply]
        simp [MulAut.congr_apply]
      rw [← h1, hs', MulEquiv.apply_symm_apply]
    obtain ⟨y', hy'y, hty'⟩ := GSThmB.exists_fixed_lift (t := ⟨t, htN⟩) htt hfix
    refine ⟨π y', ⟨y', ?_, rfl⟩, ?_⟩
    · show (y' : G) ∈ K
      refine le_iSup₂_of_le (f := fun t (_ : t ∈ T) => ⨆ (_ : orderOf t = 2),
        M ⊓ centralizer ({t} : Set G)) t htT' (le_iSup (fun _ : orderOf t = 2 =>
          M ⊓ centralizer ({t} : Set G)) ht2) (mem_inf.mpr ⟨y'.2, ?_⟩)
      exact mem_centralizer_singleton_iff.mpr hty'.symm
    · show ε (π y') = s
      rw [hπ, QuotientGroup.mk'_apply, hy'y, hy, MulEquiv.apply_symm_apply]
  have hMK : M ≤ K ⊔ oddCoreIn M := by
    intro m hm
    have h1 : π ⟨m, hm⟩ ∈ (K.subgroupOf M).map π := hKbar ▸ mem_top _
    obtain ⟨⟨k, hkM⟩, hkK, hkm⟩ := mem_map.mp h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkm
    have h3 : m = k * (k⁻¹ * m) := by group
    rw [h3]
    refine mul_mem (mem_sup_left hkK) (mem_sup_right ⟨_, hkm, ?_⟩)
    simp
  exact hMK.trans (sup_le hKH hO)

end CFSG.ComponentClassification.Sol78.F514
