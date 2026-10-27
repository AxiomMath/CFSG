module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSec4
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteF
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitNormalFour

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem footeME_conjugate
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M) (E : Subgroup G) (g : G) :
    footeME L (conjugate E g) = conjugate (footeME L E) g := by
  have hmono : ∀ {X Y : Subgroup G}, X ≤ Y → conjugate X g ≤ conjugate Y g :=
    fun hXY => map_mono hXY
  apply le_antisymm
  · refine iSup₂_le fun e' he' => iSup_le fun he'1 => ?_
    rw [mem_conjugate_iff] at he'
    have he1 : g * e' * g⁻¹ ≠ 1 := fun h => he'1 (by
      calc e' = g⁻¹ * (g * e' * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    have h1 : footeF L e' = conjugate (footeF L (g * e' * g⁻¹)) g := by
      rw [← footeF_conj huniq, show g⁻¹ * (g * e' * g⁻¹) * g = e' by group]
    rw [h1]
    exact hmono (le_iSup₂_of_le (f := fun e (_ : e ∈ E) => ⨆ (_ : e ≠ 1), footeF L e) _ he'
      (le_iSup (fun _ : g * e' * g⁻¹ ≠ 1 => footeF L (g * e' * g⁻¹)) he1))
  · have e1 : conjugate (footeME L E) g =
        ⨆ e ∈ E, ⨆ (_ : e ≠ 1), conjugate (footeF L e) g := by
      unfold footeME conjugate
      simp only [Subgroup.map_iSup]
    rw [e1]
    refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    rw [← footeF_conj huniq]
    have he' : g⁻¹ * e * g ∈ conjugate E g := conj_mem_conjugate he g
    have he'1 : g⁻¹ * e * g ≠ 1 := fun h => he1 (by
      calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group)
    exact le_iSup₂_of_le (f := fun e (_ : e ∈ conjugate E g) => ⨆ (_ : e ≠ 1), footeF L e) _ he'
      (le_iSup (fun _ : g⁻¹ * e * g ≠ 1 => footeF L (g⁻¹ * e * g)) he'1)

omit [Finite G] in
theorem footeF_le_footeME {E : Subgroup G} {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    footeF L e ≤ footeME L E :=
  le_iSup₂_of_le (f := fun e (_ : e ∈ E) => ⨆ (_ : e ≠ 1), footeF L e) e he
    (le_iSup (fun _ : e ≠ 1 => footeF L e) he1)

theorem footeF_spec (h : FooteSec4 G L) {z : G} {A : Subgroup G}
    (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L) {b : G} (hb : orderOf b = 2)
    (hbA : b ∈ coreActionKernel A) :
    IsTwoComponentAt b (footeF L b) ∧ FootePointedMaximal b (footeF L b) ∧
      footeF L b ∈ footeFamilyOf L ∧ oddResidualIn (A ⊓ centralizer ({b} : Set G)) ≤ footeF L b ∧
      footeFixed A b = footeF L b := by
  obtain ⟨B, hB, hBmax, hBF, hBA⟩ :=
    exists_mem_footeFamilyOf_of_mem_coreActionKernel h.hLB h.huniq hAmax hAF hb hbA
  have hfix := (footeFixed_eq_footeF h.hLB h.hGA h.hGC h.hSA h.footeFamilyType h.huniq h.hrank2
    hAmax hAF hb hbA).1
  rw [eq_footeF h.huniq hB hBF] at hfix ⊢
  exact ⟨hB, hBmax, hBF, hBA, hfix⟩

theorem mem_coreActionKernel_footeF (h : FooteSec4 G L) {z : G} {A : Subgroup G}
    (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L) {b : G} (hb : orderOf b = 2)
    (hbA : b ∈ coreActionKernel A) {x : G} (hxb : b * x = x * b)
    (hxA : x ∈ coreActionKernel A) : x ∈ coreActionKernel (footeF L b) := by
  obtain ⟨hB, -, -, -, hfix⟩ := footeF_spec h hAmax hAF hb hbA
  rw [← hfix] at hB ⊢
  exact mem_coreActionKernel_footeFixed hxb hxA hB

theorem exists_involution_central {S : Subgroup G} (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) :
    ∃ e ∈ S, orderOf e = 2 ∧ ∀ x ∈ S, x * e = e * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hS1
  have hlt := hS.bot_lt_center
  have hZ : IsPGroup 2 (center S) := hS.to_subgroup _
  have hZ1 : Nontrivial (center S) := (nontrivial_iff_ne_bot _).mpr hlt.ne'
  obtain ⟨n, hn0, hn⟩ := hZ.nontrivial_iff_card.mp hZ1
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 (by omega))
  refine ⟨((c : S) : G), (c : S).2, ?_, fun x hx => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  · have h1 := mem_center_iff.mp c.2 ⟨x, hx⟩
    exact congrArg Subtype.val h1

theorem exists_normal_four_le {Q E : Subgroup G} (hQ : IsPGroup 2 Q) (hEQ : E ≤ Q)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8) :
    ∃ U : Subgroup G, IsKleinFour U ∧ U ≤ Q ∧ Q ≤ normalizer (U : Set G) ∧
      ∃ u₁ ∈ U, u₁ ≠ 1 ∧ ∀ x ∈ Q, x * u₁ = u₁ * x := by
  have hE2' : ∀ x ∈ E.subgroupOf Q, x ^ 2 = 1 := fun x hx => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hE2 x hx)
  have hE8' : Nat.card (E.subgroupOf Q) = 8 := by
    rw [← hE8]
    exact Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv
  obtain ⟨U', hU'n, hU'4, hU'2⟩ := exists_normal_four hQ hE2' hE8'
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hU'1 : U' ≠ ⊥ := fun h => by rw [h, card_bot] at hU'4; omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hU'1)
  refine ⟨U'.map Q.subtype, ?_, map_subtype_le _, fun x hx => ?_, (u : G), ?_, ?_, ?_⟩
  · refine isKleinFour_of_card_eq_four ?_ ?_
    · rw [Subgroup.card_map_of_injective Q.subtype_injective, hU'4]
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.coe_subtype, ← SubgroupClass.coe_pow, hU'2 y hy, OneMemClass.coe_one]
  · refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, hU'n.conj_mem _ hy' _, rfl⟩
    · obtain ⟨y', hy', hy'e⟩ := hy
      have hyQ : y ∈ Q := by
        have h1 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        rw [h1, ← hy'e]
        exact mul_mem (mul_mem (inv_mem hx) y'.2) hx
      refine ⟨⟨y, hyQ⟩, ?_, rfl⟩
      have hy'e' : (y' : G) = x * y * x⁻¹ := hy'e
      have h2 : (⟨y, hyQ⟩ : Q) = ⟨x, hx⟩⁻¹ * y' * ⟨x, hx⟩ := Subtype.ext (by
        show y = x⁻¹ * (y' : G) * x
        rw [hy'e']
        group)
      rw [h2]
      have h3 := hU'n.conj_mem _ hy' (⟨x, hx⟩⁻¹)
      rwa [inv_inv] at h3
  · exact ⟨u, (mem_inf.mp hu).1, rfl⟩
  · intro h1
    apply hu1
    exact Subtype.ext (Subtype.ext h1)
  · intro x hx
    have h1 := mem_center_iff.mp (mem_inf.mp hu).2 ⟨x, hx⟩
    exact congrArg Subtype.val h1

theorem eq_sup_zpowers_of_isKleinFour {U : Subgroup G} (hU : IsKleinFour U) {u₁ u₂ : G}
    (hu₁ : u₁ ∈ U) (hu₂ : u₂ ∈ U) (hu₂1 : u₂ ≠ 1) (hu₂₁ : u₂ ≠ u₁) (hu₁1 : u₁ ≠ 1) :
    zpowers u₁ ⊔ zpowers u₂ = U := by
  have hle : zpowers u₁ ⊔ zpowers u₂ ≤ U := sup_le (zpowers_le.mpr hu₁) (zpowers_le.mpr hu₂)
  have hX := isKleinFour_sup_zpowers (sq_eq_one_of_isKleinFour hU hu₁)
    (sq_eq_one_of_isKleinFour hU hu₂) hu₁1 hu₂1 hu₂₁
    (commute_of_sq_eq_one (fun x hx => sq_eq_one_of_isKleinFour hU hx) hu₁ hu₂)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hX.card_four, hU.card_four])

theorem eq_of_eight_subgroups_of_isPGroup {α : Type*} (𝓜 : Subgroup G → α) {R Q E : Subgroup G}
    (h𝓜 : ∀ F W : Subgroup G, F ≤ R → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F = 8 →
      IsKleinFour W → W ≤ F → 𝓜 F = 𝓜 W)
    (hQp : IsPGroup 2 Q) (hQR : Q ≤ R) (hEQ : E ≤ Q) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hE8 : Nat.card E = 8) :
    ∀ F : Subgroup G, F ≤ Q → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F = 8 → 𝓜 F = 𝓜 E := by
  obtain ⟨U, hU, hUQ, hQU, u₁, hu₁U, hu₁1, hu₁Z⟩ := exists_normal_four_le hQp hEQ hE2 hE8
  obtain ⟨u₂, hu₂U, hu₂1, hu₂₁⟩ := exists_ne_of_isKleinFour hU u₁
  have hUgen := eq_sup_zpowers_of_isKleinFour hU hu₁U hu₂U hu₂1 hu₂₁ hu₁1
  have key : ∀ F : Subgroup G, F ≤ Q → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F = 8 →
      𝓜 F = 𝓜 U := by
    intro F hFQ hF2 hF8
    have hmove : ∀ f ∈ F, f * u₂ * f⁻¹ = u₂ ∨ f * u₂ * f⁻¹ = u₁ * u₂ := by
      intro f hf
      have hfU : f * u₂ * f⁻¹ ∈ U := (mem_normalizer_iff.mp (hQU (hFQ hf)) u₂).mp hu₂U
      have hne1 : f * u₂ * f⁻¹ ≠ 1 := fun h1 => hu₂1 (by
        calc u₂ = f⁻¹ * (f * u₂ * f⁻¹) * f := by group
          _ = 1 := by rw [h1]; group)
      have hne₁ : f * u₂ * f⁻¹ ≠ u₁ := fun h1 => hu₂₁ (by
        have h2 : f * u₁ * f⁻¹ = u₁ := by rw [hu₁Z f (hFQ hf)]; group
        calc u₂ = f⁻¹ * (f * u₂ * f⁻¹) * f := by group
          _ = f⁻¹ * (f * u₁ * f⁻¹) * f := by rw [h1, h2]
          _ = u₁ := by group)
      rcases mem_of_isKleinFour hU hu₁U hu₂U hfU hu₁1 hu₂1 hu₂₁.symm with h1 | h1 | h1 | h1
      · exact absurd h1 hne1
      · exact absurd h1 hne₁
      · exact Or.inl h1
      · exact Or.inr h1
    have hcard := card_le_two_mul_card_inf_centralizer_of_or hmove
    rw [hF8] at hcard
    set F₀ := F ⊓ centralizer ({u₂} : Set G) with hF₀
    obtain ⟨W, hW, hWF₀⟩ := exists_isKleinFour_le (B := F₀)
      (fun x hx => hF2 x (mem_inf.mp hx).1) (by omega)
    have hWF : W ≤ F := hWF₀.trans inf_le_left
    have hWU : ∀ w ∈ W, ∀ u ∈ U, w * u = u * w := by
      intro w hw u hu
      have hU' : U ≤ centralizer ({w} : Set G) := by
        rw [← hUgen]
        refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
        · exact mem_centralizer_singleton_iff.mpr (hu₁Z w (hFQ (hWF hw))).symm
        · exact mem_centralizer_singleton_iff.mpr
            ((mem_centralizer_singleton_iff.mp (mem_inf.mp (hWF₀ hw)).2).symm)
      exact (mem_centralizer_singleton_iff.mp (hU' hu)).symm
    calc 𝓜 F = 𝓜 W := h𝓜 F W (hFQ.trans hQR) hF2 hF8 hW hWF
      _ = 𝓜 U := eq_of_isKleinFour_of_commute (𝓜) h𝓜 hW hU
          ((hWF.trans hFQ).trans hQR) (hUQ.trans hQR) hWU
  intro F hFQ hF2 hF8
  exact (key F hFQ hF2 hF8).trans (key E hEQ hE2 hE8).symm

theorem foote_lemma_4_5_core (h : FooteSec4 G L) {e : G} (he : orderOf e = 2)
    (hKmax : FootePointedMaximal e (footeF L e)) (hKF : footeF L e ∈ footeFamilyOf L)
    {E Q : Subgroup G} (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8) (heE : e ∈ E)
    (hQ : IsSylowOf 2 Q (coreActionKernel (footeF L e))) (hEQ : E ≤ Q) :
    footeF L e ≤ footeME L E ∧ footeF L e ⊔ oddCoreIn (footeME L E) = footeME L E ∧
      (∀ F : Subgroup G, F ≤ Q → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F = 8 →
        footeME L F = footeME L E) ∧
      normalizer (Q : Set G) ≤ normalizer (footeME L E : Set G) ∧
      Q ≤ coreActionKernel (footeME L E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := footeF L e with hK
  set M := footeME L E with hM
  have he1 : e ≠ 1 := fun h1 => by rw [h1, orderOf_one] at he; omega
  have hQK : Q ≤ coreActionKernel K := hQ.le
  have hQp : IsPGroup 2 Q := hQ.isPGroup
  have hspec : ∀ F : Subgroup G, F ≤ coreActionKernel K → (∀ x ∈ F, x ^ 2 = 1) →
      Nat.card F = 8 → _ := fun F hFK hF2 hF8 =>
    footeME_spec h hKmax hKF (isMulCommutative_of_sq_eq_one hF2) hF2 hF8 hFK
  have hE := hspec E (hEQ.trans hQK) hE2 hE8
  have hKM : K ≤ M := footeF_le_footeME heE he1
  have hsup : K ⊔ oddCoreIn M = M := le_antisymm (sup_le hKM (map_subtype_le _))
    (hE.2.1.2.2.trans (sup_le_sup_right ((oddResidualIn_le _).trans inf_le_left) _))
  have h𝓜 : ∀ F W : Subgroup G, F ≤ coreActionKernel K → (∀ x ∈ F, x ^ 2 = 1) →
      Nat.card F = 8 → IsKleinFour W → W ≤ F → footeME L F = footeME L W :=
    fun F W hFK hF2 hF8 hW hWF => (hspec F hFK hF2 hF8).2.2 W hW hWF
  have hall : ∀ F : Subgroup G, F ≤ Q → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F = 8 →
      footeME L F = M :=
    eq_of_eight_subgroups_of_isPGroup (footeME L) h𝓜 hQp hQK hEQ hE2 hE8
  have hNQ : normalizer (Q : Set G) ≤ normalizer (M : Set G) := by
    intro g hg
    apply mem_normalizer_of_conjugate_eq
    rw [← footeME_conjugate h.huniq]
    refine hall _ ?_ ?_ ?_
    · rw [← conjugate_eq_of_mem_normalizer hg]
      exact map_mono hEQ
    · intro x hx
      rw [mem_conjugate_iff] at hx
      have h1 := hE2 _ hx
      calc x ^ 2 = g⁻¹ * (g * x * g⁻¹) ^ 2 * g := by rw [sq, sq]; group
        _ = 1 := by rw [h1]; group
    · unfold conjugate
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE8]
  refine ⟨hKM, hsup, hall, hNQ, fun x hx => ?_⟩
  exact mem_coreActionKernel_of_sup hKM hsup (hNQ (le_normalizer hx)) (hQK hx)

theorem foote_lemma_4_5_sylow (h : FooteSec4 G L) {z : G} {A E : Subgroup G}
    (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8) (hEA : E ≤ coreActionKernel A) :
    ∃ (e : G) (S : Subgroup G), orderOf e = 2 ∧ e ∈ S ∧
      FootePointedMaximal e (footeF L e) ∧ footeF L e ∈ footeFamilyOf L ∧
      IsSylowOf 2 S (coreActionKernel (footeME L E)) ∧
      IsSylowOf 2 S (coreActionKernel (footeF L e)) ∧ E ≤ S ∧
      footeF L e ≤ footeME L E ∧ footeF L e ⊔ oddCoreIn (footeME L E) = footeME L E ∧
      (∀ F : Subgroup G, F ≤ S → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F = 8 →
        footeME L F = footeME L E) ∧
      normalizer (S : Set G) ≤ normalizer (footeME L E : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := footeME L E with hM
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE8]; norm_num)
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hall
    push Not at hall
    have hE1 : E = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (hall x hx)
    rw [hE1, card_bot] at hE8
    omega
  have he : orderOf e = 2 := orderOf_eq_prime (hE2 e heE) he1
  obtain ⟨-, hKmax, hKF, -, -⟩ := footeF_spec h hAmax hAF he (hEA heE)
  set K := footeF L e with hK
  have hEK : E ≤ coreActionKernel K := fun x hx =>
    mem_coreActionKernel_footeF h hAmax hAF he (hEA heE) (commute_of_sq_eq_one hE2 heE hx)
      (hEA hx)
  obtain ⟨Q, hQ, hEQ⟩ := exists_isSylowOf_ge_of_le hEK hEp
  obtain ⟨hKM, -, hallQ, -, hQM⟩ := foote_lemma_4_5_core h he hKmax hKF hE2 hE8 heE hQ hEQ
  obtain ⟨S, hS, hQS⟩ := exists_isSylowOf_ge_of_le hQM hQ.isPGroup
  have hSp : IsPGroup 2 S := hS.isPGroup
  have hSNK : S ⊓ normalizer (K : Set G) = Q := by
    refine hQ.eq_of_le (le_inf hQS (hQ.le.trans fun x hx => hx.1)) ?_ (hSp.to_le inf_le_left)
    intro x hx
    exact mem_coreActionKernel_of_le hKM (mem_inf.mp hx).2 (hS.le (mem_inf.mp hx).1)
  have hS1 : S ≠ ⊥ := fun h1 => by
    have h2 : E ≤ ⊥ := h1 ▸ (hEQ.trans hQS)
    rw [le_bot_iff] at h2
    rw [h2, card_bot] at hE8
    omega
  obtain ⟨e', he'S, he', he'Z⟩ := exists_involution_central hSp hS1
  have hKN : centralizer ({e} : Set G) ≤ normalizer (K : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.huniq hKmax.1 hKF
  have he'Q : e' ∈ Q := by
    rw [← hSNK]
    exact mem_inf.mpr ⟨he'S,
      hKN (mem_centralizer_singleton_iff.mpr (he'Z e (hQS (hEQ heE))).symm)⟩
  have he'2 : e' ^ 2 = 1 := by rw [← he']; exact pow_orderOf_eq_one e'
  have he'1 : e' ≠ 1 := fun h1 => by rw [h1, orderOf_one] at he'; omega
  obtain ⟨F', hF'2, hF'8, he'F', hF'le⟩ := exists_card_eight_mem hE2 hE8 he'2
    (fun f hf => he'Z f (hQS (hEQ hf)))
  have hF'Q : F' ≤ Q := hF'le.trans (sup_le hEQ (zpowers_le.mpr he'Q))
  have hMF' : footeME L F' = M := hallQ F' hF'Q hF'2 hF'8
  obtain ⟨-, hK'max, hK'F, -, -⟩ := footeF_spec h hKmax hKF he' (hQ.le he'Q)
  set K' := footeF L e' with hK'
  have hK'M : K' ≤ M := hMF' ▸ footeF_le_footeME he'F' he'1
  have hK'N : centralizer ({e'} : Set G) ≤ normalizer (K' : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.huniq hK'max.1 hK'F
  have hSK' : S ≤ coreActionKernel K' := fun x hx =>
    mem_coreActionKernel_of_le hK'M (hK'N (mem_centralizer_singleton_iff.mpr (he'Z x hx)))
      (hS.le hx)
  obtain ⟨Q', hQ', hSQ'⟩ := exists_isSylowOf_ge_of_le hSK' hSp
  obtain ⟨hK'M', hsup', hallQ', hNQ', hQ'M⟩ :=
    foote_lemma_4_5_core h he' hK'max hK'F hF'2 hF'8 he'F' hQ' (hF'Q.trans (hQS.trans hSQ'))
  rw [hMF'] at hK'M' hsup' hallQ' hNQ' hQ'M
  have hQ'S : Q' = S := hS.eq_of_le hSQ' hQ'M hQ'.isPGroup
  rw [hQ'S] at hQ' hallQ' hNQ'
  exact ⟨e', S, he', he'S, hK'max, hK'F, hS, hQ', hEQ.trans hQS, hK'M', hsup', hallQ', hNQ'⟩

end CFSG.ComponentClassification.FooteLit
