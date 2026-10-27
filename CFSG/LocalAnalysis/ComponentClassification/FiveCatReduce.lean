module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpReduce

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_fixedComponent_bijOn {A : Type} [Group A] [Finite A] (c : MulAut A)
    (hc : ∀ x, c (c x) = x) :
    ∃ (σ : MulAut ((A ⧸ pPrimeCore 2 A) ⧸ center (A ⧸ pPrimeCore 2 A)))
      (ρ : ↥(fixedSubgroup c) →* ↥(fixedSubgroup σ)),
      (∀ y, σ (σ y) = y) ∧
      (∀ a : ↥(fixedSubgroup c),
        ((ρ a : ↥(fixedSubgroup σ)) : (A ⧸ pPrimeCore 2 A) ⧸ center (A ⧸ pPrimeCore 2 A)) =
          QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A))
            (QuotientGroup.mk' (pPrimeCore 2 A) (a : A))) ∧
      (∀ T : Subgroup A, T ≤ fixedSubgroup c →
        ((T.map (QuotientGroup.mk' (pPrimeCore 2 A))).map
            (QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A)))) ≤ fixedSubgroup σ ∧
          (T.subgroupOf (fixedSubgroup c)).map ρ =
            (((T.map (QuotientGroup.mk' (pPrimeCore 2 A))).map
              (QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A)))).subgroupOf (fixedSubgroup σ))) ∧
      Set.BijOn (Subgroup.map ρ) {L | IsPComponent 2 L} {P | IsPComponent 2 P} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 A with hO
  set π := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOmap : O.map c.toMonoidHom = O :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance c
  have hcO : ∀ n ∈ O, c n ∈ O := fun n hn => hOmap ▸ mem_map_of_mem c.toMonoidHom hn
  set cbar : MulAut (A ⧸ O) := QuotientGroup.congr O O c hOmap with hcbardef
  have hcbar : ∀ x, cbar (π x) = π (c x) := fun x => rfl
  have hcbar2 : ∀ y, cbar (cbar y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [hcbar, hcbar, hc]
  set C := fixedSubgroup c with hCdef
  set Cbar := fixedSubgroup cbar with hCbardef
  have hfix : C.map π = Cbar := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change cbar (π x) = π x
      rw [hcbar]
      exact congrArg π hx
    · intro y hy
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective O y
      have hy' : π (c w) = π w := (hcbar w).symm.trans hy
      have hw : w⁻¹ * c w ∈ O := by
        have := (QuotientGroup.eq (s := O)).mp hy'.symm
        exact this
      obtain ⟨n, hn, hfixed⟩ := GrSLit.exists_fixed_mul_of_inv_mul_mem c hc hcO hOodd hw
      refine ⟨w * n, hfixed, ?_⟩
      have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul, h1, mul_one]
  let r₁ : C →* Cbar := (π.comp C.subtype).codRestrict Cbar fun x => by
    rw [← hfix]
    exact mem_map_of_mem π x.2
  have hr₁s : Function.Surjective r₁ := by
    rintro ⟨y, hy⟩
    rw [← hfix] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hr₁k : Odd (Nat.card r₁.ker) := by
    let g : r₁.ker →* O := (C.subtype.comp r₁.ker.subtype).codRestrict O fun k => by
      have h1 : r₁ (k : C) = 1 := k.2
      have h2 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : O => (x : A)) h
      exact Subtype.ext (Subtype.ext h')
    exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)
  set Z := center (A ⧸ O) with hZ
  have hZmap : Z.map cbar.toMonoidHom = Z :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance cbar
  set σ : MulAut ((A ⧸ O) ⧸ Z) :=
    CatalogueBFixedCentralQuotient.onQuotient Z cbar hZmap with hσdef
  have hσ : ∀ y, σ (QuotientGroup.mk' Z y) = QuotientGroup.mk' Z (cbar y) := fun y => rfl
  have hσ2 : ∀ q, σ (σ q) = q := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z q
    rw [hσ, hσ, hcbar2]
  have hZc : Z ≤ Subgroup.center (A ⧸ O) := le_rfl
  set N := CatalogueBFixedCentralQuotient.fixedImage Z cbar hZmap with hN
  let f : ↥(fixedSubgroup cbar) →* ↥N :=
    CatalogueBFixedCentralQuotient.fixedImageProjection Z cbar hZmap
  have hfs : Function.Surjective f :=
    CatalogueBFixedCentralQuotient.fixedImageProjection_surjective Z cbar hZmap
  have hfk : f.ker ≤ Subgroup.center ↥(fixedSubgroup cbar) :=
    CatalogueBFixedCentralQuotient.fixedImageProjection_kernel_central Z cbar hZmap hZc
  have hNn : N.Normal := CatalogueBFixedCentralQuotient.fixedImage_normal Z cbar hZmap hZc
  have habel := CatalogueBFixedCentralQuotient.fixed_quotient_abelian Z cbar hZmap hZc
  have hb₃ : Set.BijOn (Subgroup.map N.subtype) {L : Subgroup N | IsPComponent 2 L}
      {M : Subgroup ↥(fixedSubgroup σ) | IsPComponent 2 M} := by
    haveI := hNn
    haveI := habel
    refine ⟨?_, ?_, ?_⟩
    · intro L hL
      have hLN : (L.map N.subtype).subgroupOf N = L :=
        comap_map_eq_self_of_injective N.subtype_injective L
      refine (CatalogueBFixedCentralQuotient.p_components_solvable_quotient_invariance 2
        Nat.prime_two N (L.map N.subtype)).mpr ⟨map_subtype_le L, ?_⟩
      rw [hLN]
      exact hL
    · exact (Subgroup.map_injective N.subtype_injective).injOn
    · intro P hP
      obtain ⟨hPN, hPc⟩ :=
        (CatalogueBFixedCentralQuotient.p_components_solvable_quotient_invariance 2
          Nat.prime_two N P).mp hP
      exact ⟨P.subgroupOf N, hPc, map_subgroupOf_eq_of_le hPN⟩
  have hb₂ : Set.BijOn (Subgroup.map f) {L | IsPComponent 2 L} {M | IsPComponent 2 M} :=
    CatalogueBCentralQuotient.pComponent_bijOn 2 f hfs hfk
  have hb₁ : Set.BijOn (fun L : Subgroup C => L.map r₁) {L | IsPComponent 2 L}
      {M | IsPComponent 2 M} :=
    (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection (p := 2) r₁ hr₁s
      (fun h => (Nat.not_even_iff_odd.mpr hr₁k) (even_iff_two_dvd.mpr h))).1
  set ρ : ↥(fixedSubgroup c) →* ↥(fixedSubgroup σ) := N.subtype.comp (f.comp r₁) with hρdef
  have hρ : ∀ a : ↥(fixedSubgroup c),
      ((ρ a : ↥(fixedSubgroup σ)) : (A ⧸ O) ⧸ Z) = QuotientGroup.mk' Z (π (a : A)) := fun a => rfl
  have himg : ∀ T : Subgroup A, T ≤ fixedSubgroup c →
      ((T.map π).map (QuotientGroup.mk' Z)) ≤ fixedSubgroup σ ∧
        (T.subgroupOf (fixedSubgroup c)).map ρ =
          (((T.map π).map (QuotientGroup.mk' Z)).subgroupOf (fixedSubgroup σ)) := by
    intro T hT
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      have h1 := (ρ ⟨t, hT ht⟩).2
      rw [hρ ⟨t, hT ht⟩] at h1
      exact h1
    · ext ⟨y, hyF⟩
      constructor
      · rintro ⟨a, ha, hay⟩
        have h1 := congrArg Subtype.val hay
        rw [hρ] at h1
        exact ⟨π (a : A), ⟨a, ha, rfl⟩, h1⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, hty⟩
        refine ⟨⟨t, hT ht⟩, ht, Subtype.ext ?_⟩
        rw [hρ]
        exact hty
  refine ⟨σ, ρ, hσ2, hρ, himg, ?_⟩
  have hall := hb₃.comp (hb₂.comp hb₁)
  have hfun : (Subgroup.map ρ : Subgroup C → Subgroup ↥(fixedSubgroup σ)) =
      (Subgroup.map N.subtype) ∘ ((Subgroup.map f) ∘ (fun L : Subgroup C => L.map r₁)) := by
    funext L
    simp only [hρdef, Function.comp_apply, Subgroup.map_map]
  rw [hfun]
  exact hall


@[expose] def imageInSimple {H : Type} [Group H] [Finite H] (M T : Subgroup H) :
    Subgroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) :=
  ((T.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).map
    (QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M)))

private theorem fixedSubgroup_conj_eq {H : Type} [Group H] (M : Subgroup H) {x : H}
    (hxN : x ∈ normalizer (M : Set H)) :
    fixedSubgroup (M.normalizerMonoidHom ⟨x, hxN⟩) =
      (M ⊓ centralizer ({x} : Set H)).subgroupOf M := by
  ext a
  rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
    mem_centralizer_singleton_iff]
  constructor
  · intro ha
    have h1 := congrArg Subtype.val ha
    change x * (a : H) * x⁻¹ = (a : H) at h1
    refine ⟨a.2, ?_⟩
    calc (a : H) * x = x * a * x⁻¹ * x := by rw [h1]
      _ = x * a := by group
  · rintro ⟨-, ha⟩
    apply Subtype.ext
    change x * (a : H) * x⁻¹ = (a : H)
    calc x * (a : H) * x⁻¹ = a * x * x⁻¹ := by rw [ha]
      _ = a := by group

theorem exists_fixedComponent_correspondence {H : Type} [Group H] [Finite H] {M : Subgroup H}
    (hM : IsPComponent 2 M) {x : H} (hx : orderOf x = 2) (hxN : x ∈ normalizer (M : Set H)) :
    ∃ σ : MulAut ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)),
      (∀ y, σ (σ y) = y) ∧
      (∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
        IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
        imageInSimple M T ≤ fixedSubgroup σ ∧
          IsPComponent 2 ((imageInSimple M T).subgroupOf (fixedSubgroup σ))) ∧
      (∀ P : Subgroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)),
        P ≤ fixedSubgroup σ → IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) →
        ∃ T : Subgroup H, T ≤ M ∧ T ≤ centralizer ({x} : Set H) ∧
          IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) ∧ imageInSimple M T = P) ∧
      (∀ T₁ T₂ : Subgroup H, T₁ ≤ M → T₁ ≤ centralizer ({x} : Set H) →
        IsPComponent 2 (T₁.subgroupOf (centralizer ({x} : Set H))) → T₂ ≤ M →
        T₂ ≤ centralizer ({x} : Set H) →
        IsPComponent 2 (T₂.subgroupOf (centralizer ({x} : Set H))) →
        imageInSimple M T₁ = imageInSimple M T₂ → T₁ = T₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hMsub : M.IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).1
  set c : MulAut M := M.normalizerMonoidHom ⟨x, hxN⟩ with hcdef
  have hcapp : ∀ a : M, ((c a : M) : H) = x * a * x⁻¹ := fun a => rfl
  have hc : ∀ a, c (c a) = a := by
    intro a
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc x * (x * (a : H) * x⁻¹) * x⁻¹ = (x * x) * a * (x * x)⁻¹ := by group
      _ = a := by rw [haa]; group
  have hfixC : fixedSubgroup c = (M ⊓ centralizer ({x} : Set H)).subgroupOf M :=
    fixedSubgroup_conj_eq M hxN
  obtain ⟨σ, ρ, hσ2, hρ, himg, hbij⟩ := exists_fixedComponent_bijOn c hc
  have hle : ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      T.subgroupOf M ≤ fixedSubgroup c := by
    intro T hTM hTC a ha
    rw [hfixC]
    exact le_inf hTM hTC ha
  have fwdL : ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
      IsPComponent 2 ((T.subgroupOf M).subgroupOf (fixedSubgroup c)) := by
    intro T hTM hTC hTpc
    have hTMC : T ≤ M ⊓ centralizer ({x} : Set H) := le_inf hTM hTC
    have hTp' : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({x} : Set H))) :=
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTMC inf_le_right hTpc
    rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTp'
  have fwdP : ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
      imageInSimple M T ≤ fixedSubgroup σ ∧
        ((T.subgroupOf M).subgroupOf (fixedSubgroup c)).map ρ =
          (imageInSimple M T).subgroupOf (fixedSubgroup σ) :=
    fun T hTM hTC _ => himg (T.subgroupOf M) (hle T hTM hTC)
  refine ⟨σ, hσ2, ?_, ?_, ?_⟩
  · intro T hTM hTC hTpc
    obtain ⟨h1, h2⟩ := fwdP T hTM hTC hTpc
    refine ⟨h1, ?_⟩
    rw [← h2]
    exact hbij.mapsTo (fwdL T hTM hTC hTpc)
  · intro P hPF hPc
    have hPc' : P.subgroupOf (fixedSubgroup σ) ∈ {P | IsPComponent 2 P} := hPc
    obtain ⟨L, hL, hLmap⟩ := hbij.surjOn hPc'
    set T : Subgroup H := (L.map (fixedSubgroup c).subtype).map M.subtype with hTdef
    have hTM : T ≤ M := map_subtype_le _
    have hTM' : T.subgroupOf M = L.map (fixedSubgroup c).subtype :=
      comap_map_eq_self_of_injective M.subtype_injective _
    have hLT : L = (T.subgroupOf M).subgroupOf (fixedSubgroup c) := by
      rw [hTM']
      exact (comap_map_eq_self_of_injective (fixedSubgroup c).subtype_injective L).symm
    have hTC : T ≤ centralizer ({x} : Set H) := by
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have hb2 : c (b : M) = (b : M) := b.2
      have h1 := congrArg Subtype.val hb2
      rw [hcapp] at h1
      rw [mem_centralizer_singleton_iff]
      show ((b : M) : H) * x = x * ((b : M) : H)
      calc ((b : M) : H) * x = x * ((b : M) : H) * x⁻¹ * x := by rw [h1]
        _ = x * ((b : M) : H) := by group
    have hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) := by
      have hTMC : T ≤ M ⊓ centralizer ({x} : Set H) := le_inf hTM hTC
      have h1 : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({x} : Set H))) := by
        have h2 : IsPComponent 2 ((T.subgroupOf M).subgroupOf (fixedSubgroup c)) := hLT ▸ hL
        rw [hfixC] at h2
        exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
          Nat.prime_two).mp h2
      refine (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hTMC inf_le_right
        ?_).mpr h1
      rw [inf_subgroupOf_right]
      exact hMsub.subgroupOf
    obtain ⟨h1, h2⟩ := fwdP T hTM hTC hTpc
    refine ⟨T, hTM, hTC, hTpc, ?_⟩
    have h3 : (imageInSimple M T).subgroupOf (fixedSubgroup σ) =
        P.subgroupOf (fixedSubgroup σ) := by
      rw [← h2, ← hLT]
      exact hLmap
    exact (inf_of_le_left h1).symm.trans ((subgroupOf_inj.mp h3).trans (inf_of_le_left hPF))
  · intro T₁ T₂ hT₁M hT₁C hT₁pc hT₂M hT₂C hT₂pc hΦ
    have hL : (T₁.subgroupOf M).subgroupOf (fixedSubgroup c) =
        (T₂.subgroupOf M).subgroupOf (fixedSubgroup c) := by
      refine hbij.injOn (fwdL T₁ hT₁M hT₁C hT₁pc) (fwdL T₂ hT₂M hT₂C hT₂pc) ?_
      rw [(fwdP T₁ hT₁M hT₁C hT₁pc).2, (fwdP T₂ hT₂M hT₂C hT₂pc).2, hΦ]
    have h1 : T₁.subgroupOf M = T₂.subgroupOf M := by
      have := subgroupOf_inj.mp hL
      rwa [inf_of_le_left (hle T₁ hT₁M hT₁C), inf_of_le_left (hle T₂ hT₂M hT₂C)] at this
    have h2 := subgroupOf_inj.mp h1
    rwa [inf_of_le_left hT₁M, inf_of_le_left hT₂M] at h2


theorem comparison_ambient {H : Type} [Group H] [Finite H] {M : Subgroup H}
    (hM : IsPComponent 2 M) {x : H} (hx : orderOf x = 2) (hxN : x ∈ normalizer (M : Set H))
    {T : Subgroup H} (hTM : T ≤ M) (hTC : T ≤ centralizer ({x} : Set H))
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H)))) :
    (pPrimeCore 2 T).index ≤ (pPrimeCore 2 M).index ∧
      ((pPrimeCore 2 T).index = (pPrimeCore 2 M).index →
        (∀ U : Subgroup H, U ≤ M → U ≤ centralizer ({x} : Set H) →
          IsPComponent 2 (U.subgroupOf (centralizer ({x} : Set H))) → U = T) ∧
        T ⊔ (pPrimeCore 2 M).map M.subtype = M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMx : conjugate M x = M := mem_normalizer_iff_map_conj_eq.mp (inv_mem hxN)
  set C := (M ⊔ conjugate M x) ⊓ centralizer ({x} : Set H) with hCdef
  have hCeq : C = M ⊓ centralizer ({x} : Set H) := by rw [hCdef, hMx, sup_idem]
  have hmem : ∀ U : Subgroup H, U ≤ M → U ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (U.subgroupOf (centralizer ({x} : Set H))) →
      U ≤ C ∧ IsPComponent 2 (U.subgroupOf C) := by
    intro U hUM hUC hUpc
    have hUC' : U ≤ C := by rw [hCeq]; exact le_inf hUM hUC
    exact ⟨hUC', CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hUC' inf_le_right hUpc⟩
  obtain ⟨hTC', hTpc'⟩ := hmem T hTM hTC hTpc
  obtain ⟨hle, -, heq⟩ := UnbalancedGS.involution_orbit_fixed_component_quotient_comparison hx M
    hM _ rfl C rfl T hTC' hTpc'
  refine ⟨hle, fun hidx => ⟨fun U hUM hUC hUpc => ?_, (heq hidx).2 hMx.symm⟩⟩
  obtain ⟨hlay, -⟩ := heq hidx
  obtain ⟨hUC', hUpc'⟩ := hmem U hUM hUC hUpc
  have h1 : U.subgroupOf C ≤ pLayer C 2 := le_sSup hUpc'
  have h2 : U ≤ T := by
    rw [← hlay, ← map_subgroupOf_eq_of_le hUC']
    exact map_mono h1
  have h3 : U.subgroupOf C ≤ T.subgroupOf C := fun a ha => h2 ha
  have h4 := CatalogueBPrimeJoin.eq_of_le 2 _ _ hUpc' hTpc' h3
  have h5 := subgroupOf_inj.mp h4
  rwa [inf_of_le_left hUC', inf_of_le_left hTC'] at h5

theorem fusionZStar_eq_pPrimeCore_of_alt_five {L : Type*} [Group L]
    (φ : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5)) :
    Open.fusionZStar L = pPrimeCore 2 L := by
  rw [Sol78.fusionZStar_eq_iff, eq_bot_iff]
  intro q hq
  have h1 : φ q ∈ center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hq y]
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), mem_bot] at h1
  exact φ.injective (by rw [h1, map_one])

theorem layer_facts {H : Type} [Group H] [Finite H] {M : Subgroup H} (hM : IsPComponent 2 M)
    {x : H} (hx : orderOf x = 2) (hxN : x ∈ normalizer (M : Set H))
    {σ : MulAut ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M))}
    (hσ2 : ∀ y, σ (σ y) = y) {T : Subgroup H} (hTM : T ≤ M)
    (hTC : T ≤ centralizer ({x} : Set H))
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))))
    (hPF : imageInSimple M T ≤ fixedSubgroup σ)
    (hPc : IsPComponent 2 ((imageInSimple M T).subgroupOf (fixedSubgroup σ)))
    (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 5))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index) :
    ProperFixedComponent σ (imageInSimple M T) ∧
      Open.fusionZStar ↥(imageInSimple M T) = pPrimeCore 2 ↥(imageInSimple M T) ∧
      Nonempty (↥(imageInSimple M T) ⧸ Open.fusionZStar ↥(imageInSimple M T) ≃*
        alternatingGroup (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMx : conjugate M x = M := mem_normalizer_iff_map_conj_eq.mp (inv_mem hxN)
  have hTMC : T ≤ M ⊓ centralizer ({x} : Set H) := le_inf hTM hTC
  have hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({x} : Set H))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTMC inf_le_right hTpc
  obtain ⟨σ₀, hPF₀, ⟨eP₀⟩⟩ :=
    exists_properFixedComponent_of_stable_image hx hM hMx hTMC hTp hlt
  have hPne : imageInSimple M T ≠ ⊤ := hPF₀.2.2.2
  have hPFC : ProperFixedComponent σ (imageInSimple M T) := ⟨hσ2, hPF, hPc, hPne⟩
  set P := imageInSimple M T with hPdef
  have hZT : Open.fusionZStar T = pPrimeCore 2 T := fusionZStar_eq_pPrimeCore_of_alt_five eT
  let eTZ : ↥T ⧸ Open.fusionZStar ↥T ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hZT).trans eT
  let eP : ↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5) := eP₀.symm.trans eTZ
  have hTperf : Group.IsPerfect ↥T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hTpc
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTC).toMonoidHom)
      (subgroupOfEquivOfLe hTC).surjective
  have hTq : IsQuasisimple (↥T ⧸ pPrimeCore 2 ↥T) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hTC)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hTpc)
  set T' := T.subgroupOf M with hT'def
  let eTT : ↥T' ≃* ↥T := subgroupOfEquivOfLe hTM
  haveI : Group.IsPerfect ↥T' :=
    Group.IsPerfect.ofSurjective (f := eTT.symm.toMonoidHom) eTT.symm.surjective
  have hT'q : IsQuasisimple (↥T' ⧸ pPrimeCore 2 ↥T') :=
    LocalCores.isQuasisimple_of_mulEquiv (Sol78.coreQuotCongr eTT).symm hTq
  have hZT' : Open.fusionZStar ↥T' = pPrimeCore 2 ↥T' :=
    fusionZStar_eq_pPrimeCore_of_alt_five ((Sol78.coreQuotCongr eTT).trans eT)
  have hZ' : ∀ t : ↥T', t ∈ Open.fusionZStar ↥T' →
      ∃ o : ↥T', o ∈ pPrimeCore 2 ↥T' ∧ ((o⁻¹ * t : ↥T') : ↥M) ∈ Open.fusionZStar ↥M :=
    fun t ht => ⟨t, hZT' ▸ ht, by rw [inv_mul_cancel]; exact (Open.fusionZStar ↥M).one_mem⟩
  have hPO : pPrimeCore 2 ↥P ≠ ⊤ := by
    intro htop
    have hZtop : Open.fusionZStar ↥P = ⊤ :=
      eq_top_iff.mpr (htop ▸ Sol78.pPrimeCore_le_fusionZStar _)
    have : Subsingleton (alternatingGroup (Fin 5)) := by
      have hs : Subsingleton (↥P ⧸ Open.fusionZStar ↥P) :=
        QuotientGroup.subsingleton_iff.mpr hZtop
      exact eP.symm.toEquiv.subsingleton
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    exact false_of_nontrivial_of_subsingleton (alternatingGroup (Fin 5))
  exact ⟨hPFC, fusionZStar_eq_pPrimeCore_of_image hT'q hZ' hPO, ⟨eP⟩⟩

theorem fiveTwoLayerInput_of_leaf (hleaf : FiveTwoLayerLeaf) : FiveTwoLayerInput := by
  intro H _ _ hK M hM x hx hxN T₁ T₂ hne hT₁M hT₂M hT₁C hT₂C hT₁pc hT₂pc ⟨e₁⟩ ⟨e₂⟩ huniq
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt : ∀ U V : Subgroup H, U ≤ M → U ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (U.subgroupOf (centralizer ({x} : Set H))) → V ≤ M →
      V ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (V.subgroupOf (centralizer ({x} : Set H))) → U ≠ V →
      (pPrimeCore 2 U).index < (pPrimeCore 2 M).index := by
    intro U V hUM hUC hUpc hVM hVC hVpc hUV
    obtain ⟨hle, heq⟩ := comparison_ambient hM hx hxN hUM hUC hUpc
    exact lt_of_le_of_ne hle fun hidx => hUV ((heq hidx).1 V hVM hVC hVpc).symm
  have hlt₁ := hlt T₁ T₂ hT₁M hT₁C hT₁pc hT₂M hT₂C hT₂pc hne
  have hlt₂ := hlt T₂ T₁ hT₂M hT₂C hT₂pc hT₁M hT₁C hT₁pc hne.symm
  obtain ⟨σ, hσ2, hfwd, hbwd, hinj⟩ := exists_fixedComponent_correspondence hM hx hxN
  obtain ⟨hP₁F, hP₁c⟩ := hfwd T₁ hT₁M hT₁C hT₁pc
  obtain ⟨hP₂F, hP₂c⟩ := hfwd T₂ hT₂M hT₂C hT₂pc
  obtain ⟨hPF₁, hPex₁, ⟨eP₁⟩⟩ := layer_facts hM hx hxN hσ2 hT₁M hT₁C hT₁pc hP₁F hP₁c e₁ hlt₁
  obtain ⟨hPF₂, hPex₂, ⟨eP₂⟩⟩ := layer_facts hM hx hxN hσ2 hT₂M hT₂C hT₂pc hP₂F hP₂c e₂ hlt₂
  have hne' : imageInSimple M T₁ ≠ imageInSimple M T₂ := fun h =>
    hne (hinj T₁ T₂ hT₁M hT₁C hT₁pc hT₂M hT₂C hT₂pc h)
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  have : IsSimpleGroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := hMq.2.1
  have hna := hMq.2.2
  have hcat : Blueprint.Catalog ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hK M
      ((QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M))).comp
        (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have huniq' : ∀ P' : Subgroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)),
      ProperFixedComponent σ P' → P' = imageInSimple M T₁ ∨ P' = imageInSimple M T₂ := by
    rintro P' ⟨-, hP'F, hP'c, -⟩
    obtain ⟨T'', hT''M, hT''C, hT''pc, hΦ⟩ := hbwd P' hP'F hP'c
    rcases huniq T'' hT''M hT''C hT''pc with h | h
    · exact Or.inl (by rw [← hΦ, h])
    · exact Or.inr (by rw [← hΦ, h])
  have hout := hleaf _ inferInstance hna hcat σ _ _ hPF₁ hPF₂ hne' hPex₁ hPex₂ ⟨eP₁⟩ ⟨eP₂⟩ huniq'
  obtain ⟨eMS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥M
  rcases hout with h | h
  · exact Or.inl (Blueprint.LieModel.of_mulEquiv eMS h)
  · exact Or.inr (Blueprint.LieModel.of_mulEquiv eMS h)

end CFSG.ComponentClassification.SolMax.FiveCat
