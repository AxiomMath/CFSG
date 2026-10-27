module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourRep

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem range_comm_sq {L : Subgroup G} {B : Subgroup G} (hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (θ : ↥B →* ↥L) :
    (∀ a ∈ θ.range, ∀ b ∈ θ.range, a * b = b * a) ∧ ∀ a ∈ θ.range, a ^ 2 = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ x.2 _ y.2)
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hB2 _ x.2)
    rw [this, map_one]

theorem rep4 [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W) (hρ : Function.Injective ρ)
    {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 7))
    (HA : Alt7Hyp (alternatingGroup (Fin 7))) {U : Submodule (ZMod 2) W}
    (hUc : U = commOn ρ L ⊤) (hUUL : commOn ρ L U = U) (hU0 : U ≠ ⊥) (hU16 : Nat.card U = 16)
    (hfix0 : fixOn ρ L U = ⊥)
    (hSA : ∀ γ ∈ Subgroup.normalizer (L : Set G), ∃ l ∈ L, ∀ u ∈ U, ρ γ u = ρ l u)
    {T₁ : Subgroup G}
    (hT₁ : CFSG.QuasithinUnique.IsSylowTwoOf T₁ (Subgroup.normalizer (L : Set G)))
    {Fam : Set (Subgroup G)}
    (hFam : ∀ A ∈ Fam, A ≤ T₁ ∧ CFSG.IsElementaryAbelian 2 ↥A ∧ IsBestOffenderOn ρ A ⊤)
    (hA₀ : ∃ A ∈ Fam, ⁅L, A⁆ = L) :
    ∃ ℓ : Submodule (ZMod 2) W, ℓ ≤ U ∧ (∀ A ∈ Fam, ∀ a ∈ A, ∀ v ∈ ℓ, ρ a v = v) ∧
      ∃ E : Subgroup G, E ≤ L ∧ Nat.card E = 9 ∧ ∀ e ∈ E, ∀ t ∈ T₁, (∀ v ∈ ℓ, ρ t v = v) →
        e * t * e⁻¹ ∈ T₁ ∧ ∀ v ∈ ℓ, ρ (e * t * e⁻¹) v = v := by
  classical
  have := isSimpleGroup_alt7
  obtain ⟨hq, -, -, -⟩ := isQuasisimple_of_mulEquiv center_alt7 exists_ne_comm_alt7 eL
  have HL : Alt7Hyp ↥L := Alt7Hyp.of_mulEquiv eL HA
  have hfa := fun {l₁ l₂ : G} (h1 : l₁ ∈ L) (h2 : l₂ ∈ L) (h : ∀ u ∈ U, ρ l₁ u = ρ l₂ u) =>
    faithful_on ρ eL hUc hUUL hU0 h1 h2 h
  have hT₁Γ : T₁ ≤ Subgroup.normalizer (L : Set G) := hT₁.1
  obtain ⟨A₀, hA₀F, hLA₀⟩ := hA₀
  obtain ⟨hA₀T, hA₀2, hA₀b⟩ := hFam A₀ hA₀F
  obtain ⟨B₀, hB₀A, hLB₀, hB₀c, hB₀2, hbud₀⟩ :=
    exists_offender_budget ρ hρ eL hA₀2 (hA₀T.trans hT₁Γ) hLA₀ hA₀b
  have hbud₀' : 2 ^ secCod ρ B₀ ⊥ U * Nat.card ↥(B₀ ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card B₀ := by rw [hUc]; exact hbud₀
  obtain ⟨θ₀, hθ₀, hR₀1, hR₀4, hℓ₀4, hnorm₀, h72₀, E₀, hE₀, hE₀9⟩ :=
    offender_in_L ρ eL hUc hUUL hU0 HA hU16 hSA (hB₀A.trans (hA₀T.trans hT₁Γ)) hLB₀ hB₀c hB₀2
      hbud₀'
  obtain ⟨θT, hθT⟩ := exists_theta ρ eL hUc hUUL hU0 hSA T₁ hT₁Γ
  set R₀ : Subgroup ↥L := θ₀.range with hR₀
  set ℓ₀ : Submodule (ZMod 2) ↥U := fixSub (repL ρ hUc) R₀ with hℓ₀
  set D : Subgroup ↥L := θT.range with hD
  have hDp : IsPGroup 2 D := hT₁.2.1.of_surjective θT.rangeRestrict θT.rangeRestrict_surjective
  have hθeq : ∀ {S : Subgroup G} (hS : S ≤ T₁) (θ : ↥S →* ↥L)
      (hθ : ∀ (s : S), ∀ u ∈ U, ρ (θ s : G) u = ρ (s : G) u) (s : S),
      θ s = θT ⟨s, hS s.2⟩ := fun {S} hS θ hθ s =>
    Subtype.ext (hfa (θ s).2 (θT ⟨s, hS s.2⟩).2 (fun u hu => by rw [hθ s u hu, hθT _ u hu]))
  have hR₀D : R₀ ≤ D := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, (hB₀A.trans hA₀T) b.2⟩, (hθeq (hB₀A.trans hA₀T) θ₀ hθ₀ b).symm⟩
  have hAR : ∀ A ∈ Fam, ∀ θA : ↥A →* ↥L, (∀ (a : A), ∀ u ∈ U, ρ (θA a : G) u = ρ (a : G) u) →
      θA.range ≤ R₀ := by
    intro A hAF θA hθA
    obtain ⟨hAT, hA2, hAb⟩ := hFam A hAF
    have hAΓ : A ≤ Subgroup.normalizer (L : Set G) := hAT.trans hT₁Γ
    by_cases hLA : ⁅L, A⁆ = L
    · obtain ⟨B, hBA, hLB, hBc, hB2, hbud⟩ := exists_offender_budget ρ hρ eL hA2 hAΓ hLA hAb
      have hbud' : 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
          Nat.card B := by rw [hUc]; exact hbud
      obtain ⟨θB, hθB, hRB1, hRB4, hℓB4, hnormB, h72B, EB, hEB, hEB9⟩ :=
        offender_in_L ρ eL hUc hUUL hU0 HA hU16 hSA (hBA.trans hAΓ) hLB hBc hB2 hbud'
      have hRBD : θB.range ≤ D := by
        rintro _ ⟨b, rfl⟩
        exact ⟨⟨b, (hBA.trans hAT) b.2⟩, (hθeq (hBA.trans hAT) θB hθB b).symm⟩
      obtain ⟨hc₀, hs₀⟩ := range_comm_sq hB₀c hB₀2 θ₀
      obtain ⟨hcB, hsB⟩ := range_comm_sq hBc hB2 θB
      have hRBeq : θB.range = R₀ :=
        HL.klein_unique hDp hRBD hR₀D hRB4 hR₀4 hsB hs₀ h72B.ge h72₀.ge
      have hBA' : θB.range ≤ θA.range := by
        rintro _ ⟨b, rfl⟩
        refine ⟨⟨b, hBA b.2⟩, Subtype.ext (hfa (θA ⟨b, hBA b.2⟩).2 (θB b).2 ?_)⟩
        intro u hu
        rw [hθA ⟨b, hBA b.2⟩ u hu, hθB b u hu]
      obtain ⟨hcA, hsA⟩ := range_comm_sq (fun a ha c hc => by
          exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) ⟨c, hc⟩))
        (fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) a ha) θA
      have hcard : Nat.card θA.range ≤ 4 := HL.card_le θA.range hcA hsA
      have : θB.range = θA.range :=
        Subgroup.eq_of_le_of_card_ge hBA' (by rw [hRB4]; exact hcard)
      rw [← this, hRBeq]
    · have hbot : ⁅L, A⁆ = ⊥ := by
        by_contra hne
        exact hLA (commutator_eq_of_ne_bot hq hAΓ hne)
      have hcent : A ≤ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.commutator_comm] at hbot
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
      rintro _ ⟨x, rfl⟩
      have h1 : θA x = 1 :=
        (theta_eq_one_iff ρ eL hUc hUUL hU0 A hAΓ θA hθA x).2 (hcent x.2)
      rw [h1]
      exact R₀.one_mem
  have hfam : ∀ A ∈ Fam, ∀ a ∈ A, ∀ v : ↥U, v ∈ ℓ₀ → ρ a (v : W) = (v : W) := by
    intro A hAF a ha v hv
    obtain ⟨hAT, -, -⟩ := hFam A hAF
    obtain ⟨θA, hθA⟩ := exists_theta ρ eL hUc hUUL hU0 hSA A (hAT.trans hT₁Γ)
    have hmem : θA ⟨a, ha⟩ ∈ R₀ := hAR A hAF θA hθA ⟨⟨a, ha⟩, rfl⟩
    have h1 := hv _ hmem
    have h2 := congrArg Subtype.val h1
    rw [repL_apply_coe] at h2
    rw [← hθA ⟨a, ha⟩ v v.2]
    exact h2
  refine ⟨ℓ₀.map U.subtype, Submodule.map_subtype_le U ℓ₀, ?_, E₀.map L.subtype, ?_, ?_, ?_⟩
  · rintro A hAF a ha _ ⟨v₀, hv₀, rfl⟩
    exact hfam A hAF a ha v₀ hv₀
  · rintro _ ⟨e', _, rfl⟩
    exact e'.2
  · rw [Subgroup.card_map_of_injective L.subtype_injective]; exact hE₀9
  · rintro _ ⟨e', he', rfl⟩ t ht hfixt
    change (e' : G) * t * (e' : G)⁻¹ ∈ T₁ ∧ ∀ v ∈ ℓ₀.map U.subtype, ρ ((e' : G) * t * (e' : G)⁻¹) v = v
    have heΓ : (e' : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer e'.2
    have hlfix : ∀ v : ↥U, v ∈ ℓ₀ → repL ρ hUc (θT ⟨t, ht⟩) v = v := by
      intro v hv
      apply Subtype.ext
      rw [repL_apply_coe, hθT ⟨t, ht⟩ v v.2]
      exact hfixt v ⟨v, hv, rfl⟩
    have hlR : θT ⟨t, ht⟩ ∈ R₀ :=
      fixing_le_of_two_group ρ eL hUc hUUL hU0 HL hU16 hfix0 hDp hR₀D hR₀4 hℓ₀4
        ⟨⟨t, ht⟩, rfl⟩ hlfix
    have hlT : ((θT ⟨t, ht⟩ : ↥L) : G) ∈ T₁ :=
      mem_of_theta_sylow ρ eL hUc hUUL hU0 hSA hT₁ ht (θT ⟨t, ht⟩).2
        (fun u hu => hθT ⟨t, ht⟩ u hu)
    have hl2R : e' * θT ⟨t, ht⟩ * e'⁻¹ ∈ R₀ :=
      (Subgroup.mem_normalizer_iff.1 (hE₀ he') _).1 hlR
    obtain ⟨⟨t₂, ht₂⟩, ht₂eq⟩ := hR₀D hl2R
    have hl2T : ((e' * θT ⟨t, ht⟩ * e'⁻¹ : ↥L) : G) ∈ T₁ := by
      refine mem_of_theta_sylow ρ eL hUc hUUL hU0 hSA hT₁ ht₂ (e' * θT ⟨t, ht⟩ * e'⁻¹).2
        (fun u hu => ?_)
      rw [← ht₂eq, hθT ⟨t₂, ht₂⟩ u hu]
    obtain ⟨l, hl⟩ : ∃ l : G, l = ((θT ⟨t, ht⟩ : ↥L) : G) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : G, c = l⁻¹ * t := ⟨_, rfl⟩
    have hlT' : l ∈ T₁ := hl ▸ hlT
    have hlL : l ∈ L := hl ▸ (θT ⟨t, ht⟩).2
    have hcT : c ∈ T₁ := hc ▸ T₁.mul_mem (T₁.inv_mem hlT') ht
    have hcfix : ∀ u ∈ U, ρ c u = u := by
      intro u hu
      rw [hc, map_mul, Module.End.mul_apply, hl, ← hθT ⟨t, ht⟩ u hu]
      exact rho_inv_apply_rho ρ _ u
    have hccent := centralizes_of_trivial ρ eL hUc hUUL hU0 (hT₁Γ hcT) hcfix
    have hec : (e' : G) * c = c * (e' : G) :=
      Subgroup.mem_centralizer_iff.1 hccent (e' : G) e'.2
    have hcc : (e' : G) * c * (e' : G)⁻¹ = c := by rw [hec]; group
    have htl : t = l * c := by rw [hc]; group
    have hteq : (e' : G) * t * (e' : G)⁻¹ =
        ((e' : G) * l * (e' : G)⁻¹) * c := by
      calc (e' : G) * t * (e' : G)⁻¹ = (e' : G) * (l * c) * (e' : G)⁻¹ := by rw [← htl]
        _ = ((e' : G) * l * (e' : G)⁻¹) * ((e' : G) * c * (e' : G)⁻¹) := by group
        _ = _ := by rw [hcc]
    have hl2T' : (e' : G) * l * (e' : G)⁻¹ ∈ T₁ := by
      have : ((e' * θT ⟨t, ht⟩ * e'⁻¹ : ↥L) : G) = (e' : G) * l * (e' : G)⁻¹ := by
        rw [hl]; rfl
      rw [← this]; exact hl2T
    refine ⟨?_, ?_⟩
    · rw [hteq]; exact T₁.mul_mem hl2T' hcT
    · rintro _ ⟨v₀, hv₀, rfl⟩
      change ρ ((e' : G) * t * (e' : G)⁻¹) (v₀ : W) = (v₀ : W)
      have hinvN : e'⁻¹ ∈ Subgroup.normalizer (R₀ : Set ↥L) := Subgroup.inv_mem _ (hE₀ he')
      have hv₁ : repL ρ hUc e'⁻¹ v₀ ∈ ℓ₀ := (hnorm₀ _).1 hinvN v₀ |>.mp hv₀
      have hv₁' := hfixt (repL ρ hUc e'⁻¹ v₀ : W) ⟨_, hv₁, rfl⟩
      have hcoe : ((repL ρ hUc e'⁻¹ v₀ : ↥U) : W) = ρ ((e' : G)⁻¹) (v₀ : W) := by
        rw [repL_apply_coe]; rfl
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← hcoe, hv₁', hcoe,
        rho_apply_rho_inv]
