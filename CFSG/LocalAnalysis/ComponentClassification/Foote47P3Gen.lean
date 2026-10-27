module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47Inputs
public import CFSG.LocalAnalysis.ComponentClassification.Foote47Lift
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteM

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_isKleinFour_not_mem {F : Subgroup G} (hF2 : ∀ x ∈ F, x ^ 2 = 1)
    (hF8 : Nat.card F = 8) {v : G} (hvF : v ∈ F) (hv1 : v ≠ 1) :
    ∃ U : Subgroup G, IsKleinFour U ∧ U ≤ F ∧ v ∉ U := by
  have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    commute_of_sq_eq_one hF2 ha hb
  have hv2 := hF2 v hvF
  obtain ⟨a, haF, ha⟩ : ∃ a ∈ F, a ∉ zpowers v := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (fun x hx => hall x hx : F ≤ zpowers v)
    rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1, hF8] at h1
    omega
  have ha1 : a ≠ 1 := fun h => ha (h ▸ one_mem _)
  have hav : a ≠ v := fun h => ha (h ▸ mem_zpowers v)
  have hW' := isKleinFour_sup_zpowers hv2 (hF2 a haF) hv1 ha1 hav (hcomm v hvF a haF)
  obtain ⟨b, hbF, hb⟩ : ∃ b ∈ F, b ∉ zpowers v ⊔ zpowers a := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (fun x hx => hall x hx : F ≤ zpowers v ⊔ zpowers a)
    rw [hW'.card_four, hF8] at h1
    omega
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  have hba : b ≠ a := fun h => hb (by rw [h]; exact mem_sup_right (mem_zpowers a))
  have hU := isKleinFour_sup_zpowers (hF2 a haF) (hF2 b hbF) ha1 hb1 hba (hcomm a haF b hbF)
  refine ⟨_, hU, sup_le (zpowers_le.mpr haF) (zpowers_le.mpr hbF), fun hvU => ?_⟩
  rcases mem_of_isKleinFour hU (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers b))
    hvU ha1 hb1 hba.symm with h | h | h | h
  · exact hv1 h
  · exact hav h.symm
  · exact hb (by rw [← h]; exact mem_sup_left (mem_zpowers v))
  · apply hb
    have h1 : b = a⁻¹ * v := by rw [h]; group
    rw [h1]
    exact mul_mem (inv_mem (mem_sup_right (mem_zpowers a))) (mem_sup_left (mem_zpowers v))

theorem le_of_forall_isKleinFour_inf_centralizer_le {F₀ X H' : Subgroup G}
    (hF₀2 : ∀ x ∈ F₀, x ^ 2 = 1) (hF₀8 : Nat.card F₀ = 8)
    (hF₀X : F₀ ≤ normalizer (X : Set G)) (hX : Odd (Nat.card X))
    (h : ∀ W : Subgroup G, IsKleinFour W → W ≤ F₀ → X ⊓ centralizer (W : Set G) ≤ H') :
    X ≤ H' := by
  have hcomm : ∀ a ∈ F₀, ∀ b ∈ F₀, a * b = b * a := fun a ha b hb =>
    commute_of_sq_eq_one hF₀2 ha hb
  obtain ⟨V, hV, hVF⟩ := exists_isKleinFour_le hF₀2 (by omega)
  refine le_of_isKleinFour_inf_centralizer_le hV (hVF.trans hF₀X) hX fun v hv hv1 => ?_
  have hvF := hVF hv
  obtain ⟨U, hU, hUF, hvU⟩ := exists_isKleinFour_not_mem hF₀2 hF₀8 hvF hv1
  have hUX : U ≤ normalizer ((X ⊓ centralizer ({v} : Set G) : Subgroup G) : Set G) :=
    fun u hu => mem_normalizer_inf' (hF₀X (hUF hu))
      (mem_normalizer_centralizer_singleton (hcomm u (hUF hu) v hvF))
  have hXv : Odd (Nat.card ↥(X ⊓ centralizer ({v} : Set G))) :=
    Odd.of_dvd_nat hX (Subgroup.card_dvd_of_le inf_le_left)
  refine le_of_isKleinFour_inf_centralizer_le hU hUX hXv fun u hu hu1 => ?_
  have huF := hUF hu
  have huv : v ≠ u := fun h => hvU (h ▸ hu)
  have hW := isKleinFour_sup_zpowers (hF₀2 u huF) (hF₀2 v hvF) hu1 hv1 huv (hcomm u huF v hvF)
  refine le_trans (fun x hx => ?_) (h _ hW (sup_le (zpowers_le.mpr huF) (zpowers_le.mpr hvF)))
  obtain ⟨⟨hxX, hxv⟩, hxu⟩ := hx
  refine mem_inf.mpr ⟨hxX, mem_centralizer_iff.mpr fun w hw => ?_⟩
  have hWx : zpowers u ⊔ zpowers v ≤ centralizer ({x} : Set G) := sup_le
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxu).symm))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxv).symm))
  exact mem_centralizer_singleton_iff.mp (hWx hw)

theorem le_of_forall_fourgroup_le (h : FooteSec4 G L) (hFG : Foote47FourgroupGeneration)
    {M : Subgroup G} (hM : IsFooteM L M) {T : Subgroup G} (hTN : T ≤ normalizer (M : Set G))
    (hTp : IsPGroup 2 T) (hTC : ∀ x ∈ T, x ∈ coreActionKernel M → x = 1)
    {F₀ : Subgroup G} (hF₀T : F₀ ≤ T) (hF₀2 : ∀ x ∈ F₀, x ^ 2 = 1) (hF₀8 : Nat.card F₀ = 8)
    (hnab : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) {H' : Subgroup G}
    (hC : ∀ W F : Subgroup G, IsKleinFour W → W ≤ F → F ≤ T → (∀ x ∈ F, x ^ 2 = 1) →
      Nat.card F = 8 → M ⊓ centralizer (W : Set G) ≤ H') : M ≤ H' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : oddCoreIn M ≤ H' := le_of_forall_isKleinFour_inf_centralizer_le hF₀2 hF₀8
    (fun x hx => mem_normalizer_oddCoreIn (hTN (hF₀T hx))) (odd_card_oddCoreIn M)
    fun W hW hWF => (inf_le_inf_right _ (map_subtype_le _)).trans
      (hC W F₀ hW hWF hF₀T hF₀2 hF₀8)
  obtain ⟨hs, ⟨ε⟩⟩ := hM.quotient h
  set S := L ⧸ Open.fusionZStar L with hS
  set N := normalizer (M : Set G) with hN
  set Φ : ↥N →* MulAut S := (MulAut.congr ε).toMonoidHom.comp (GSThmB.oddBarConj M) with hΦ
  have hker : ∀ x : N, Φ x = 1 → (x : G) ∈ coreActionKernel M := by
    intro x hx
    apply GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one
    have h1 : (MulAut.congr ε) (GSThmB.oddBarConj M x) = 1 := hx
    rwa [map_eq_one_iff _ (MulAut.congr ε).injective] at h1
  set ψ := Φ.comp (T.subgroupOf N).subtype with hψ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    exact hTC _ x.2 (hker _ hx)
  set T' := (T.subgroupOf N).map Φ with hT'
  have hrange : ψ.range = T' := by rw [MonoidHom.range_comp, range_subtype]
  let pb : Subgroup (MulAut S) → Subgroup G := fun W' =>
    ((W'.comap ψ).map (T.subgroupOf N).subtype).map N.subtype
  have hpb_mem : ∀ W' x, x ∈ pb W' →
      ∃ (hxN : x ∈ N) (hxT : x ∈ T), ψ ⟨⟨x, hxN⟩, hxT⟩ ∈ W' := by
    rintro W' _ ⟨_, ⟨⟨⟨x, hxN⟩, hxT⟩, hxW, rfl⟩, rfl⟩
    exact ⟨hxN, hxT, hxW⟩
  have hpbT : ∀ W', pb W' ≤ T := fun W' x hx => by
    obtain ⟨-, hxT, -⟩ := hpb_mem W' x hx
    exact hxT
  have hcard_pb : ∀ W', W' ≤ T' → Nat.card (pb W') = Nat.card W' := by
    intro W' hW'
    rw [Subgroup.card_map_of_injective N.subtype_injective,
      Subgroup.card_map_of_injective (T.subgroupOf N).subtype_injective]
    have h1 : (W'.comap ψ).map ψ = W' := by
      rw [map_comap_eq, hrange, inf_eq_right.mpr hW']
    rw [← Subgroup.card_map_of_injective hinj, h1]
  have hsq_pb : ∀ W', (∀ w ∈ W', w * w = 1) → ∀ x ∈ pb W', x ^ 2 = 1 := by
    intro W' hW' x hx
    obtain ⟨hxN, hxT, hxW⟩ := hpb_mem W' x hx
    have h1 : ψ (⟨⟨x, hxN⟩, hxT⟩ * ⟨⟨x, hxN⟩, hxT⟩) = ψ 1 := by
      rw [map_mul, map_one]
      exact hW' _ hxW
    have h2 := congrArg (fun y : T.subgroupOf N => ((y : N) : G)) (hinj h1)
    rw [sq]
    exact h2
  have hT'p : IsPGroup 2 T' := (hTp.comap_subtype (K := N)).map Φ
  set F' := (F₀.subgroupOf N).map Φ with hF'
  have hF'T' : F' ≤ T' := map_mono fun x hx => hF₀T hx
  have hF₀N : F₀ ≤ N := hF₀T.trans hTN
  have hF'8 : Nat.card F' = 8 := by
    have hinjF : Function.Injective (Φ.comp (F₀.subgroupOf N).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      apply Subtype.ext
      apply Subtype.ext
      exact hTC _ (hF₀T x.2) (hker _ hx)
    have hrangeF : (Φ.comp (F₀.subgroupOf N).subtype).range = F' := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hrangeF, ← Nat.card_congr (MonoidHom.ofInjective hinjF).toEquiv, ← hF₀8]
    exact Nat.card_congr (subgroupOfEquivOfLe hF₀N).toEquiv
  have hF'2 : ∀ e ∈ F', e * e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x * x = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, OneMemClass.coe_one, ← sq]
      exact hF₀2 _ hx)
    rw [← map_mul, hx2, map_one]
  have hT'nab : ∃ x ∈ T', ∃ y ∈ T', x * y ≠ y * x := by
    obtain ⟨x, hxT, y, hyT, hxy⟩ := hnab
    refine ⟨ψ ⟨⟨x, hTN hxT⟩, hxT⟩, hrange ▸ ⟨_, rfl⟩, ψ ⟨⟨y, hTN hyT⟩, hyT⟩,
      hrange ▸ ⟨_, rfl⟩, fun h1 => hxy ?_⟩
    rw [← map_mul, ← map_mul] at h1
    exact congrArg (fun y : T.subgroupOf N => ((y : N) : G)) (hinj h1)
  have hgen := hFG S h.footeFamilyType T' hT'p ⟨F', hF'T', hF'2, hF'8⟩ hT'nab
  set K := ⨆ (W : Subgroup G) (_ : IsKleinFour W)
    (_ : ∃ F : Subgroup G, W ≤ F ∧ F ≤ T ∧ (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8),
      M ⊓ centralizer (W : Set G) with hKdef
  have hKH : K ≤ H' := iSup_le fun W => iSup_le fun hW => iSup_le fun hF => by
    obtain ⟨F, hWF, hFT, hF2, hF8⟩ := hF
    exact hC W F hW hWF hFT hF2 hF8
  set π := QuotientGroup.mk' (pPrimeCore 2 M) with hπ
  have hKbar : (K.subgroupOf M).map π = ⊤ := by
    apply map_injective (f := ε.toMonoidHom) ε.injective
    rw [Subgroup.map_top_of_surjective _ ε.surjective, eq_top_iff, ← hgen]
    refine iSup_le fun W' => iSup_le fun hW' => iSup_le fun hF => ?_
    obtain ⟨F'', hW'F'', hF''T', hF''2, hF''8⟩ := hF
    have hWT' : W' ≤ T' := hW'F''.trans hF''T'
    have hW'2 : ∀ w ∈ W', w * w = 1 := fun w hw => by
      rw [← sq]
      exact sq_eq_one_of_isKleinFour hW' hw
    have hW : IsKleinFour (pb W') :=
      isKleinFour_of_card_eq_four (by rw [hcard_pb W' hWT', hW'.card_four]) (hsq_pb W' hW'2)
    have hWF : pb W' ≤ pb F'' := map_mono (map_mono (comap_mono hW'F''))
    have hF8 : Nat.card (pb F'') = 8 := by rw [hcard_pb F'' hF''T', hF''8]
    intro s hs
    obtain ⟨⟨m, hmM⟩, hm⟩ := QuotientGroup.mk_surjective (ε.symm s)
    have hfix : ∀ x ∈ pb W', m⁻¹ * (x * m * x⁻¹) ∈ oddCoreIn M := by
      intro x hx
      obtain ⟨hxN, hxT, hxW⟩ := hpb_mem W' x hx
      have h1 : Φ ⟨x, hxN⟩ s = s := by
        have h2 := mem_iInf.mp (mem_iInf.mp hs (ψ ⟨⟨x, hxN⟩, hxT⟩)) hxW
        exact h2
      have h3 : GSThmB.oddBarConj M ⟨x, hxN⟩ (ε.symm s) = ε.symm s := by
        apply ε.injective
        have h4 : Φ ⟨x, hxN⟩ s = ε (GSThmB.oddBarConj M ⟨x, hxN⟩ (ε.symm s)) := by
          rw [hΦ, MonoidHom.comp_apply]
          simp [MulAut.congr_apply]
        rw [← h4, h1, MulEquiv.apply_symm_apply]
      rw [← hm, GSThmB.oddBarConj_apply_mk, QuotientGroup.eq] at h3
      have h5 := inv_mem ((mem_pPrimeCore_iff_mem_oddCoreIn _).mp h3)
      convert h5 using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    obtain ⟨o, ho, hmo⟩ := exists_mem_centralizer_of_isPGroup (hTp.to_le (hpbT W'))
      (fun x hx => mem_normalizer_oddCoreIn (hTN (hpbT W' hx))) (odd_card_oddCoreIn M) hfix
    have hoM : o ∈ M := map_subtype_le _ ho
    refine ⟨π ⟨m * o, mul_mem hmM hoM⟩, ⟨⟨m * o, mul_mem hmM hoM⟩, ?_, rfl⟩, ?_⟩
    · show m * o ∈ K
      have hle : M ⊓ centralizer ((pb W' : Subgroup G) : Set G) ≤ K := by
        refine le_iSup_of_le (pb W') ?_
        refine le_iSup_of_le hW ?_
        exact le_iSup_of_le (⟨pb F'', hWF, hpbT F'', hsq_pb F'' hF''2, hF8⟩ :
          ∃ F : Subgroup G, pb W' ≤ F ∧ F ≤ T ∧ (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8) le_rfl
      exact hle (mem_inf.mpr ⟨mul_mem hmM hoM, hmo⟩)
    · show ε (π ⟨m * o, mul_mem hmM hoM⟩) = s
      have h6 : π ⟨m * o, mul_mem hmM hoM⟩ = π ⟨m, hmM⟩ := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        refine (mem_pPrimeCore_iff_mem_oddCoreIn _).mpr ?_
        simpa using inv_mem ho
      rw [h6, hπ, QuotientGroup.mk'_apply, hm, MulEquiv.apply_symm_apply]
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

end CFSG.ComponentClassification.Foote47
