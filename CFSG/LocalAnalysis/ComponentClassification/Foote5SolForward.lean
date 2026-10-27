module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolReanchor

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjClosure_le_coreActionKernel {X Y U : Subgroup G} (hX : X ≤ coreActionKernel U)
    (hY : Y ≤ normalizer (U : Set G)) : conjClosure X Y ≤ coreActionKernel U :=
  Sol78.conjClosure_le hX (hY.trans (normalizer_le_normalizer_coreActionKernel U))

theorem exists_moved {X V : Subgroup G} (hVX : V ≤ twoLayerIn X) (hV : ⁅V, V⁆ = V)
    (hne : V ≠ ⊥) : ∃ U : Subgroup G, IsTwoComponentIn U X ∧ ¬ V ≤ coreActionKernel U := by
  by_contra hall
  push Not at hall
  apply hne
  have h1 := le_iSup_of_moved (X := X) (J := V) (fun _ => False) (fun _ _ _ _ h => h) hVX hV
    (fun U hU hmv => hmv (hall U hU))
  rw [eq_bot_iff]
  refine h1.trans (iSup₂_le fun U hU => absurd hU.2 id)

omit [Finite G] in
theorem ne_bot_of_isQuasisimple {V : Subgroup G} (hVq : IsQuasisimple (↥V ⧸ pPrimeCore 2 ↥V)) :
    V ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, a, b, hab⟩ := hVq
  apply hab
  have : Subsingleton (↥(⊥ : Subgroup G) ⧸ pPrimeCore 2 ↥(⊥ : Subgroup G)) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
    rw [Subsingleton.elim x y]
  have : Subsingleton ((↥(⊥ : Subgroup G) ⧸ pPrimeCore 2 ↥(⊥ : Subgroup G)) ⧸
      center (↥(⊥ : Subgroup G) ⧸ pPrimeCore 2 ↥(⊥ : Subgroup G))) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
    rw [Subsingleton.elim x y]
  exact Subsingleton.elim _ _

theorem card_moved_of_anchor {J K A V : Subgroup G} {t : G} (hML : GSMirrorMaximal J)
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hKZ : Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J))
    (ht : orderOf t = 2) (htK : t ∈ coreActionKernel K)
    (hcls : ∀ U : Subgroup G, IsTwoComponentIn U (centralizer ({t} : Set G)) →
      ¬ twoLayerIn (K ⊓ centralizer ({t} : Set G)) ≤ coreActionKernel U → GSMirrorReach J U)
    (hA2 : IsPGroup 2 A) (htA : t ∈ A) (hAt : A ≤ centralizer ({t} : Set G))
    (hAQ : A ≤ coreActionKernel K)
    (hstarA : twoLayerIn (K ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G)))
    (hV : IsTwoComponentIn V (centralizer (A : Set G)))
    (hmv : ¬ twoLayerIn (K ⊓ centralizer (A : Set G)) ≤ coreActionKernel V) :
    Nat.card (↥V ⧸ Open.fusionZStar ↥V) = Nat.card (↥K ⧸ Open.fusionZStar ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ct := centralizer ({t} : Set G) with hCt
  have ht2 : IsPGroup 2 (zpowers t) := isPGroup_zpowers_of_orderOf ht
  have htQ : zpowers t ≤ coreActionKernel K := zpowers_le.mpr htK
  obtain ⟨hKAc, hKAr, -, ⟨eKA⟩⟩ := cover_facts hKq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hA2 hAQ)
  have hKAperf : ⁅twoLayerIn (K ⊓ centralizer (A : Set G)),
      twoLayerIn (K ⊓ centralizer (A : Set G))⁆ = twoLayerIn (K ⊓ centralizer (A : Set G)) := by
    rw [hKAr]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hKAc.1 hKAc.2
  have hKAq : IsQuasisimple (↥(twoLayerIn (K ⊓ centralizer (A : Set G))) ⧸
      pPrimeCore 2 ↥(twoLayerIn (K ⊓ centralizer (A : Set G)))) := by
    rw [hKAr]
    exact LocalCores.isQuasisimple_of_mulEquiv eKA.symm hKq
  have hKAcard : Nat.card (↥(twoLayerIn (K ⊓ centralizer (A : Set G))) ⧸
      Open.fusionZStar ↥(twoLayerIn (K ⊓ centralizer (A : Set G)))) =
      Nat.card (↥K ⧸ Open.fusionZStar ↥K) := by
    rw [hKAr]
    exact Nat.card_congr (Sol78.fusionZStarQuotOfCore eKA).toEquiv
  have hlow := (moved_facts hstarA hKAperf hKAq hV hmv).1
  have hCAt : centralizer (A : Set G) ≤ Ct := by
    rw [hCt, ← centralizer_zpowers']
    exact centralizer_le (zpowers_le.mpr htA)
  have hVL : V ≤ twoLayerIn Ct := by
    have h1 := GrSLit.pLayer_inf_centralizer_le (Y := Ct) (A := A) hAt hA2
    rw [inf_eq_right.mpr hCAt] at h1
    exact (le_twoLayerIn_of_isTwoComponentIn hV).trans h1
  have hVperf : ⁅V, V⁆ = V := UnbalancedCorr.commutator_eq_of_isPComponent hV.1 hV.2
  have hVq : IsQuasisimple (↥V ⧸ pPrimeCore 2 ↥V) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 V _ hV.1).1 hV.2).2.2
  obtain ⟨U, hU, hmvU⟩ := exists_moved hVL hVperf (ne_bot_of_isQuasisimple hVq)
  have hKAKt : twoLayerIn (K ⊓ centralizer (A : Set G)) ≤ twoLayerIn (K ⊓ Ct) := by
    have h1 := twoLayerIn_inf_centralizer_anti hKq ht2 hA2 htQ hAQ (zpowers_le.mpr htA)
    rw [centralizer_zpowers'] at h1
    exact h1
  have hKtU : ¬ twoLayerIn (K ⊓ Ct) ≤ coreActionKernel U := by
    intro hc
    apply hmvU
    have hLA : twoLayerIn (centralizer (A : Set G)) ≤ normalizer (U : Set G) := by
      have h1 := GrSLit.pLayer_inf_centralizer_le (Y := Ct) (A := A) hAt hA2
      rw [inf_eq_right.mpr hCAt] at h1
      exact h1.trans (twoLayerIn_le_normalizer hU)
    exact (le_conjClosure_of_not_le_coreActionKernel hV hstarA hmv).trans
      (conjClosure_le_coreActionKernel (hKAKt.trans hc) hLA)
  have hUcard := card_eq_of_reach hML (hcls U hU hKtU)
  have hup := (moved_facts hVL hVperf hVq hU hmvU).1
  rw [hKAcard] at hlow
  rw [hUcard, ← hKZ] at hup
  exact le_antisymm hup hlow

@[expose] def MirrorAnchor (J K : Subgroup G) (w : G) : Prop :=
  orderOf w = 2 ∧ w ∈ coreActionKernel K ∧
    twoLayerIn (K ⊓ centralizer ({w} : Set G)) ≤ twoLayerIn (centralizer ({w} : Set G)) ∧
    ∀ V : Subgroup G, IsTwoComponentIn V (centralizer ({w} : Set G)) →
      ¬ twoLayerIn (K ⊓ centralizer ({w} : Set G)) ≤ coreActionKernel V → GSMirrorReach J V

@[expose] def MirrorGood (J K : Subgroup G) : Prop :=
  IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
    Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* ↥J ⧸ Open.fusionZStar ↥J) ∧ ∃ w : G, MirrorAnchor J K w

omit [Finite G] in
theorem map_centralizer_singleton (φ : G ≃* G) (u : G) :
    (centralizer ({u} : Set G)).map φ.toMonoidHom = centralizer ({φ u} : Set G) := by
  rw [← centralizer_zpowers', Sol76.map_centralizer, MonoidHom.map_zpowers, centralizer_zpowers']
  rfl

theorem MirrorAnchor.conj {J K : Subgroup G} {w y : G} (h : MirrorAnchor J K w)
    (hy : y ∈ normalizer (K : Set G)) : MirrorAnchor J K ((MulAut.conj y) w) := by
  obtain ⟨hw, hwK, hstar, hcls⟩ := h
  set φ := MulAut.conj y with hφ
  have hKφ : K.map φ.toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp hy
  have hCφ := map_centralizer_singleton φ w
  have hLφ : (twoLayerIn (K ⊓ centralizer ({w} : Set G))).map φ.toMonoidHom =
      twoLayerIn (K ⊓ centralizer ({φ w} : Set G)) := by
    rw [Sol76.map_twoLayerIn, map_inf_eq _ _ _ φ.injective, hKφ, hCφ]
  refine ⟨?_, ?_, ?_, fun M hM hmv => ?_⟩
  · rw [hφ, MulAut.conj_apply, ← inv_inv y]
    rw [inv_inv]
    have := GSLit.orderOf_conj_inv w y⁻¹
    rwa [inv_inv, hw] at this
  · have h1 : φ w ∈ (coreActionKernel K).map φ.toMonoidHom := mem_map_of_mem _ hwK
    rwa [Sol76.map_coreActionKernel φ K, hKφ] at h1
  · have h1 := map_mono (f := φ.toMonoidHom) hstar
    rwa [hLφ, Sol76.map_twoLayerIn, hCφ] at h1
  ·
    set M₀ := M.map φ.symm.toMonoidHom with hM₀
    have hMM₀ : M₀.map φ.toMonoidHom = M := by
      rw [hM₀, Subgroup.map_map]
      convert Subgroup.map_id M using 2
      ext x; simp
    have hC' : (centralizer ({φ w} : Set G)).map φ.symm.toMonoidHom =
        centralizer ({w} : Set G) := by
      rw [map_centralizer_singleton]; simp
    have hM₀c : IsTwoComponentIn M₀ (centralizer ({w} : Set G)) := by
      have := Sol76.isTwoComponentIn_map φ.symm hM
      rwa [hC'] at this
    have hmv₀ : ¬ twoLayerIn (K ⊓ centralizer ({w} : Set G)) ≤ coreActionKernel M₀ := by
      intro hc
      apply hmv
      have h1 := map_mono (f := φ.toMonoidHom) hc
      rwa [hLφ, Sol76.map_coreActionKernel φ M₀, hMM₀] at h1
    have h2 := (hcls M₀ hM₀c hmv₀).conj y⁻¹
    have h3 : conjugate M₀ y⁻¹ = M := by
      unfold conjugate
      rw [inv_inv]
      exact hMM₀
    rwa [h3] at h2

theorem star_of_anchor {J K T : Subgroup G} {t : G} (hML : GSMirrorMaximal J)
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hKZ : Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J))
    (h : MirrorAnchor J K t) (hT2 : IsPGroup 2 T) (hTt : T ≤ centralizer ({t} : Set G))
    (hTQ : T ≤ coreActionKernel K) :
    ∀ A : Subgroup G, zpowers t ≤ A → A ≤ T →
      twoLayerIn (K ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G)) →
      twoLayerIn (K ⊓ centralizer (T : Set G)) ≤ twoLayerIn (centralizer (T : Set G)) := by
  obtain ⟨ht, htK, -, hcls⟩ := h
  suffices key : ∀ n : ℕ, ∀ A : Subgroup G, Nat.card T - Nat.card A = n → zpowers t ≤ A →
      A ≤ T → twoLayerIn (K ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G)) →
      twoLayerIn (K ⊓ centralizer (T : Set G)) ≤ twoLayerIn (centralizer (T : Set G)) from
    fun A => key _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn htA hAT hA
    by_cases hAT' : A = T
    · rw [← hAT']; exact hA
    obtain ⟨s, hsT, hsN, hsA, hs2⟩ := exists_sq_mem_of_ne hT2 hAT hAT'
    set A' := A ⊔ zpowers s with hA'
    have hA'T : A' ≤ T := sup_le hAT (zpowers_le.mpr hsT)
    have hAA' : A < A' := lt_of_le_of_ne le_sup_left fun h =>
      hsA (h ▸ mem_sup_right (mem_zpowers s))
    have hcard : Nat.card A < Nat.card A' := Subgroup.card_lt_of_lt hAA'
    have hcardT : Nat.card A' ≤ Nat.card T := card_le_of_le hA'T
    have htyp := fun V hV hmv => card_moved_of_anchor hML hKq hKZ ht htK hcls (hT2.to_le hAT)
      (htA (mem_zpowers t)) (hAT.trans hTt) (hAT.trans hTQ) hA (V := V) hV hmv
    have hA'star := star_sup_zpowers hKq (hT2.to_le hAT) (hAT.trans hTQ)
      (hT2.to_le (zpowers_le.mpr hsT)) (hTQ hsT) hsN hs2 hA htyp
    exact ih _ (by omega) A' rfl (htA.trans le_sup_left) hA'T hA'star

theorem anchor_at {J K : Subgroup G} (hML : GSMirrorMaximal J) (hK : MirrorGood J K) {v : G}
    (hv : orderOf v = 2) (hvK : v ∈ coreActionKernel K) : MirrorAnchor J K v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKq, ⟨eK⟩, w, hanc⟩ := hK
  have hKZ : Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) :=
    Nat.card_congr eK.toEquiv
  set N := coreActionKernel K with hN
  have hw2 : IsPGroup 2 (zpowers w) := isPGroup_zpowers_of_orderOf hanc.1
  have hv2 : IsPGroup 2 (zpowers v) := isPGroup_zpowers_of_orderOf hv
  obtain ⟨P₁, hwP₁⟩ := (hw2.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨P₂, hvP₂⟩ := (hv2.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥N P₁ P₂
  set P := (P₂ : Subgroup ↥N).map N.subtype with hP
  have hP2 : IsPGroup 2 P := P₂.isPGroup'.map N.subtype
  have hPN : P ≤ N := map_subtype_le _
  have hvP : v ∈ P := ⟨⟨v, hvK⟩, hvP₂ (mem_subgroupOf.mpr (mem_zpowers v)), rfl⟩
  have hw'P : (MulAut.conj (y : G)) w ∈ P := by
    have h1 : (⟨w, hanc.2.1⟩ : ↥N) ∈ (P₁ : Subgroup ↥N) :=
      hwP₁ (mem_subgroupOf.mpr (mem_zpowers w))
    have h2 := Subgroup.smul_mem_pointwise_smul (⟨w, hanc.2.1⟩ : ↥N) (MulAut.conj y)
      (P₁ : Subgroup ↥N) h1
    rw [← Sylow.coe_subgroup_smul, hy] at h2
    refine ⟨_, h2, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply]
  have hyN : (y : G) ∈ normalizer (K : Set G) := (mem_coreActionKernel.mp y.2).1
  have hanc' := hanc.conj hyN
  set w' := (MulAut.conj (y : G)) w with hw'
  have hPne : P ≠ ⊥ := by
    intro h
    have : v ∈ (⊥ : Subgroup G) := h ▸ hvP
    rw [mem_bot] at this
    rw [this, orderOf_one] at hv
    exact absurd hv (by norm_num)
  obtain ⟨c, hcP, hc, hcP'⟩ := GSLit.exists_involution_mem_center hP2 le_rfl le_normalizer hPne
  have hw'c : w' * c = c * w' := hcP' w' hw'P
  obtain ⟨hstarc, hclsc⟩ := reanchor hML hKq hKZ hanc'.1 hc hw'c hanc'.2.1 (hPN hcP) hanc'.2.2.1
    hanc'.2.2.2
  have hcv : c * v = v * c := (hcP' v hvP).symm
  obtain ⟨hstarv, hclsv⟩ := reanchor hML hKq hKZ hc hv hcv (hPN hcP) hvK hstarc hclsc
  exact ⟨hv, hvK, hstarv, hclsv⟩

theorem forward {J K T : Subgroup G} (hML : GSMirrorMaximal J) (hK : MirrorGood J K)
    (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) (hTQ : T ≤ coreActionKernel K) :
    twoLayerIn (K ⊓ centralizer (T : Set G)) ≤ twoLayerIn (centralizer (T : Set G)) ∧
    ∀ K₁ : Subgroup G, IsTwoComponentIn K₁ (centralizer (T : Set G)) →
      ¬ twoLayerIn (K ⊓ centralizer (T : Set G)) ≤ coreActionKernel K₁ → MirrorGood J K₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' := hK
  obtain ⟨hKq, ⟨eK⟩, -, -⟩ := hK
  have hKZ : Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) :=
    Nat.card_congr eK.toEquiv
  obtain ⟨t, htT, ht, htT'⟩ := GSLit.exists_involution_mem_center hT2 le_rfl le_normalizer hT
  have hanct : MirrorAnchor J K t := anchor_at hML hK' ht (hTQ htT)
  obtain ⟨-, -, hstart, hclst⟩ := hanct
  have hTt : T ≤ centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (htT' x hx)
  have hstartz : twoLayerIn (K ⊓ centralizer ((zpowers t : Subgroup G) : Set G)) ≤
      twoLayerIn (centralizer ((zpowers t : Subgroup G) : Set G)) := by
    rw [centralizer_zpowers']; exact hstart
  have hstarT := star_of_anchor hML hKq hKZ ⟨ht, hTQ htT, hstart, hclst⟩ hT2 hTt hTQ (zpowers t)
    (le_refl _) (zpowers_le.mpr htT) hstartz
  refine ⟨hstarT, fun K₁ hK₁ hmv => ?_⟩
  have hcard := card_moved_of_anchor hML hKq hKZ ht (hTQ htT) hclst hT2 htT hTt hTQ hstarT hK₁ hmv
  obtain ⟨hKTc, hKTr, -, ⟨eKT⟩⟩ := cover_facts hKq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hT2 hTQ)
  have hKTperf : ⁅twoLayerIn (K ⊓ centralizer (T : Set G)),
      twoLayerIn (K ⊓ centralizer (T : Set G))⁆ = twoLayerIn (K ⊓ centralizer (T : Set G)) := by
    rw [hKTr]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hKTc.1 hKTc.2
  have hKTq : IsQuasisimple (↥(twoLayerIn (K ⊓ centralizer (T : Set G))) ⧸
      pPrimeCore 2 ↥(twoLayerIn (K ⊓ centralizer (T : Set G)))) := by
    rw [hKTr]
    exact LocalCores.isQuasisimple_of_mulEquiv eKT.symm hKq
  have eKT' : ↥(twoLayerIn (K ⊓ centralizer (T : Set G))) ⧸
      Open.fusionZStar ↥(twoLayerIn (K ⊓ centralizer (T : Set G))) ≃* ↥K ⧸ Open.fusionZStar ↥K := by
    rw [hKTr]
    exact Sol78.fusionZStarQuotOfCore eKT
  have hcard' : Nat.card (↥(twoLayerIn (K ⊓ centralizer (T : Set G))) ⧸
      Open.fusionZStar ↥(twoLayerIn (K ⊓ centralizer (T : Set G)))) =
      Nat.card (↥K₁ ⧸ Open.fusionZStar ↥K₁) := by
    rw [hcard]; exact Nat.card_congr eKT'.toEquiv
  obtain ⟨⟨e₁⟩, -⟩ := (moved_facts hstarT hKTperf hKTq hK₁ hmv).2 hcard'
  have hK₁q : IsQuasisimple (↥K₁ ⧸ pPrimeCore 2 ↥K₁) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K₁ _ hK₁.1).1 hK₁.2).2.2
  refine ⟨hK₁q, ⟨(e₁.symm.trans eKT').trans eK⟩, t, ht, ?_, ?_, fun U hU hmvU => ?_⟩
  · exact Sol78.mem_coreActionKernel_of_commute fun k hk =>
      ((mem_centralizer_iff.mp (hK₁.1 hk)) t htT).symm
  ·
    have hCT : centralizer (T : Set G) ≤ centralizer ({t} : Set G) := by
      rw [← centralizer_zpowers']; exact centralizer_le (zpowers_le.mpr htT)
    have h1 := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({t} : Set G)) (A := T) hTt hT2
    rw [inf_eq_right.mpr hCT] at h1
    exact ((map_subtype_le _).trans inf_le_left).trans
      ((le_twoLayerIn_of_isTwoComponentIn hK₁).trans h1)
  ·
    apply hclst U hU
    intro hc
    apply hmvU
    have hCT : centralizer (T : Set G) ≤ centralizer ({t} : Set G) := by
      rw [← centralizer_zpowers']; exact centralizer_le (zpowers_le.mpr htT)
    have hLT : twoLayerIn (centralizer (T : Set G)) ≤ normalizer (U : Set G) := by
      have h1 := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({t} : Set G)) (A := T) hTt
        hT2
      rw [inf_eq_right.mpr hCT] at h1
      exact h1.trans (twoLayerIn_le_normalizer hU)
    have hKTKt : twoLayerIn (K ⊓ centralizer (T : Set G)) ≤
        twoLayerIn (K ⊓ centralizer ({t} : Set G)) := by
      have h1 := twoLayerIn_inf_centralizer_anti hKq (isPGroup_zpowers_of_orderOf ht) hT2
        (zpowers_le.mpr (hTQ htT)) hTQ (zpowers_le.mpr htT)
      rw [centralizer_zpowers'] at h1
      exact h1
    have hK₁U : K₁ ≤ coreActionKernel U :=
      (le_conjClosure_of_not_le_coreActionKernel hK₁ hstarT hmv).trans
        (conjClosure_le_coreActionKernel (hKTKt.trans hc) hLT)
    exact ((map_subtype_le _).trans inf_le_left).trans hK₁U

end CFSG.ComponentClassification.Foote5.SolMax
