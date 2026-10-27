module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGenerationM

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

theorem centralizer_range_conj_eq_bot {S : Type*} [Group S] (hS : center S = ⊥) :
    centralizer ((MulAut.conj : S →* MulAut S).range : Set (MulAut S)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [mem_bot]
  ext s
  have h1 : MulAut.conj s * φ = φ * MulAut.conj s := mem_centralizer_iff.mp hφ _ ⟨s, rfl⟩
  have h2 : MulAut.conj (φ s) = MulAut.conj s := by
    have h3 : MulAut.conj (φ s) = φ * MulAut.conj s * φ⁻¹ := by
      ext y
      simp [MulAut.conj_apply, MulAut.mul_apply]
    rw [h3, ← h1]
    group
  exact congrArg (fun x => x) (injective_mulAut_conj hS h2)

theorem footeL2_fix_generation_e8 (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (hD : AschbacherKnownGroup.HasDihedralSylowTwo S)
    (hrank : CFSG.pRank 2 S ≤ 2) {E : Subgroup (MulAut S)} (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hE8 : Nat.card E = 8) :
    ⨆ (τ : MulAut S) (_ : τ ∈ E) (_ : orderOf τ = 2),
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) = ⊤ := by
  obtain ⟨-, hZ⟩ := open_isQuasisimple_of_isSimpleGroup hnc
  set c : S →* MulAut S := MulAut.conj with hc
  have hcinj : Function.Injective c := injective_mulAut_conj hZ
  set Inn := c.range with hInn
  obtain ⟨e₁, he₁E, he₁I⟩ : ∃ e₁ ∈ E, e₁ ∉ Inn := by
    by_contra hall
    push Not at hall
    set E' := E.comap c with hE'
    have hmap : E'.map c = E := by
      rw [hE', map_comap_eq, ← hInn]
      exact inf_eq_right.mpr fun x hx => hall x hx
    have hcard : Nat.card E' = 2 ^ 3 := by
      rw [← card_map_of_injective hcinj, hmap, hE8]
      norm_num
    have hel : Open.IsElemAbelian 2 E' := by
      have hsq : ∀ x ∈ E', x ^ 2 = 1 := by
        intro x hx
        apply hcinj
        rw [map_pow, map_one]
        exact hE2 _ hx
      exact ⟨isMulCommutative_of_sq_eq_one hsq, hsq⟩
    have h3 := SectionRank.le_pRank one_lt_two (le_top : E' ≤ ⊤) hel hcard
    rw [← SectionRank.pRank_eq_open_pRank_top] at h3
    omega
  obtain ⟨e₂, he₂E, he₂⟩ : ∃ e₂ ∈ E, e₂ ∉ zpowers e₁ := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card E ≤ Nat.card (zpowers e₁) := Subgroup.card_le_of_le fun x hx => hall x hx
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf e₁ ≤ 2 := orderOf_le_of_pow_eq_one two_pos (hE2 e₁ he₁E)
    omega
  have he₁1 : e₁ ≠ 1 := fun h1 => he₁I (h1 ▸ one_mem _)
  have he₂1 : e₂ ≠ 1 := fun h1 => he₂ (h1 ▸ one_mem _)
  have he₂₁ : e₂ ≠ e₁ := fun h1 => he₂ (h1 ▸ mem_zpowers e₁)
  have hU := isKleinFour_sup_zpowers (hE2 e₁ he₁E) (hE2 e₂ he₂E) he₁1 he₂1 he₂₁
    (commute_of_sq_eq_one hE2 he₁E he₂E)
  set U := zpowers e₁ ⊔ zpowers e₂ with hUdef
  have hUE : U ≤ E := sup_le (zpowers_le.mpr he₁E) (zpowers_le.mpr he₂E)
  let eInn : S ≃* Inn := MonoidHom.ofInjective hcinj
  have : IsSimpleGroup Inn := eInn.symm.isSimpleGroup
  have hInnc : ∃ a b : Inn, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eInn a, eInn b, fun h1 => hab (eInn.injective (by rw [map_mul, map_mul, h1]))⟩
  obtain ⟨hqI, hZI⟩ := open_isQuasisimple_of_isSimpleGroup hInnc
  let eQ : Inn ⧸ center Inn ≃* S :=
    ((QuotientGroup.quotientMulEquivOfEq hZI).trans QuotientGroup.quotientBot).trans eInn.symm
  have hDI : AschbacherKnownGroup.HasDihedralSylowTwo (Inn ⧸ center Inn) :=
    hasDihedralSylowTwo_of_equiv eQ.symm hD
  have hfact : (Nat.card (center Inn)).factorization 2 ≤ 1 := by
    rw [hZI, card_bot]
    simp
  have hU4 : AschbacherKnownGroup.IsFourGroup U :=
    ⟨⟨@IsKleinFour.isMulCommutative U _ hU, fun x hx => sq_eq_one_of_isKleinFour hU hx⟩,
      hU.card_four⟩
  have hgen := hK.dihedral_cover_generation (MulAut S) Inn U hqI hDI hfact
    (le_normalizer_range_conj U) hU4
  have hle : Inn ≤ AschbacherKnownGroup.centralizerJoin U Inn := by
    by_contra hle
    have h1 := (hgen hle).2
    rw [centralizer_range_conj_eq_bot hZ, sup_bot_eq] at h1
    exact he₁I (h1 (mem_sup_left (mem_zpowers e₁)))
  have hjoin : AschbacherKnownGroup.centralizerJoin U Inn =
      (⨆ (u : MulAut S) (_ : u ∈ U) (_ : u ≠ 1),
        MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id S)).map c := by
    unfold AschbacherKnownGroup.centralizerJoin
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun u => iSup_congr fun _ => iSup_congr fun _ =>
      range_inf_centralizer_eq hZ u
  refine eq_top_iff.mpr fun s _ => ?_
  have h1 := hle ⟨s, rfl⟩
  rw [hjoin, mem_map_iff_mem hcinj] at h1
  have hle2 : (⨆ (u : MulAut S) (_ : u ∈ U) (_ : u ≠ 1),
      MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id S)) ≤
      ⨆ (τ : MulAut S) (_ : τ ∈ E) (_ : orderOf τ = 2),
        MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) := by
    refine iSup₂_le fun u hu => iSup_le fun hu1 => ?_
    have hu2 : orderOf u = 2 := orderOf_eq_prime (sq_eq_one_of_isKleinFour hU hu) hu1
    exact le_iSup₂_of_le (f := fun τ (_ : τ ∈ E) => ⨆ (_ : orderOf τ = 2),
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S)) u (hUE hu)
      (le_iSup (fun _ : orderOf u = 2 => MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id S)) hu2)
  exact hle2 h1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_of_forall_centralizer_le_e8 (h : FooteSec4 G L)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) {M : Subgroup G} (hM : IsFooteM L M)
    {F : Subgroup G} (hFN : F ≤ normalizer (M : Set G)) (hF2 : ∀ x ∈ F, x ^ 2 = 1)
    (hF8 : Nat.card F = 8) {H' : Subgroup G}
    (hC : ∀ t ∈ F, orderOf t = 2 → centralizer ({t} : Set G) ≤ H') : M ≤ H' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV, hVF⟩ := exists_isKleinFour_le hF2 (by omega)
  have hO : oddCoreIn M ≤ H' := by
    refine le_of_isKleinFour_inf_centralizer_le hV
      (fun x hx => mem_normalizer_oddCoreIn (hFN (hVF hx))) (odd_card_oddCoreIn M)
      fun w hw hw1 => inf_le_right.trans (hC w (hVF hw) ?_)
    exact orderOf_eq_prime (sq_eq_one_of_isKleinFour hV hw) hw1
  have hMres := hM.le_oddResidualIn h
  by_cases hA : ∃ t ∈ F, orderOf t = 2 ∧ t ∈ coreActionKernel M
  ·
    obtain ⟨t, htF, ht, htC⟩ := hA
    have ht2 : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have h1 := le_oddResidualIn_inf_centralizer_sup ht2 (zpowers_le.mpr htC) hMres
    rw [centralizer_zpowers_eq] at h1
    exact h1.trans (sup_le ((oddResidualIn_le _).trans (inf_le_right.trans (hC t htF ht))) hO)
  push Not at hA
  have hFC : ∀ x ∈ F, x ∈ coreActionKernel M → x = 1 := by
    intro x hxF hxC
    by_contra hx1
    exact hA x hxF (orderOf_eq_prime (hF2 x hxF) hx1) hxC
  obtain ⟨hs, ⟨ε⟩⟩ := hM.quotient h
  set S := L ⧸ Open.fusionZStar L with hS
  set N := normalizer (M : Set G) with hN
  set Φ : ↥N →* MulAut S := (MulAut.congr ε).toMonoidHom.comp (GSThmB.oddBarConj M) with hΦ
  have hker : ∀ x : N, Φ x = 1 → (x : G) ∈ coreActionKernel M := by
    intro x hx
    apply GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one
    have h1 : (MulAut.congr ε) (GSThmB.oddBarConj M x) = 1 := hx
    rwa [map_eq_one_iff _ (MulAut.congr ε).injective] at h1
  set F' := (F.subgroupOf N).map Φ with hF'
  have hinj : Function.Injective (Φ.comp (F.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    exact hFC _ x.2 (hker _ hx)
  have hrange : (Φ.comp (F.subgroupOf N).subtype).range = F' := by
    rw [MonoidHom.range_comp, range_subtype]
  have hF'8 : Nat.card F' = 8 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hF8]
    exact Nat.card_congr (subgroupOfEquivOfLe hFN).toEquiv
  have hF'2 : ∀ e ∈ F', e ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hF2 _ hx)
    rw [← map_pow, hx2, map_one]
  have : IsSimpleGroup S := ε.symm.isSimpleGroup
  have hSnc : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hM.exists_mul_ne h
    exact ⟨ε a, ε b, fun h1 => hab (ε.injective (by rw [map_mul, map_mul, h1]))⟩
  have hGW := hasDihedralSylowTwo_of_footeFamilyType h.footeFamilyType
  have hgen := footeL2_fix_generation_e8 hK hSnc (hasDihedralSylowTwo_of_gorensteinWalter hGW)
    (pRank_le_two_of_hasDihedralSylowTwo hGW) hF'2 hF'8
  set K := ⨆ (t : G) (_ : t ∈ F) (_ : orderOf t = 2), M ⊓ centralizer ({t} : Set G) with hKdef
  have hKH : K ≤ H' := iSup₂_le fun t ht => iSup_le fun ht2 => inf_le_right.trans (hC t ht ht2)
  set π := QuotientGroup.mk' (pPrimeCore 2 M) with hπ
  have hKbar : (K.subgroupOf M).map π = ⊤ := by
    apply map_injective (f := ε.toMonoidHom) ε.injective
    rw [Subgroup.map_top_of_surjective _ ε.surjective, eq_top_iff, ← hgen]
    refine iSup₂_le fun τ hτ => iSup_le fun hτ2 => ?_
    obtain ⟨⟨t, htN⟩, htF, rfl⟩ := hτ
    have htF' : t ∈ F := htF
    have ht2 : orderOf t = 2 := by
      have h1 := orderOf_injective _ hinj (⟨⟨t, htN⟩, htF⟩ : F.subgroupOf N)
      have h2 : (Φ.comp (F.subgroupOf N).subtype) ⟨⟨t, htN⟩, htF⟩ = Φ ⟨t, htN⟩ := rfl
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
      refine le_iSup₂_of_le (f := fun t (_ : t ∈ F) => ⨆ (_ : orderOf t = 2),
        M ⊓ centralizer ({t} : Set G)) t htF' (le_iSup (fun _ : orderOf t = 2 =>
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

end CFSG.ComponentClassification.FooteLit
