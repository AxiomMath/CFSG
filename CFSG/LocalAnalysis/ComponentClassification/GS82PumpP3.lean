module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP3Sub
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpPSL2NotChev2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpSq
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP3Defs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem mem_normalizer_centralizer {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) : g ∈ normalizer (centralizer (A : Set G) : Set G) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro h
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hh a ha
    have ha' : g⁻¹ * a * g ∈ A := (hg (g⁻¹ * a * g)).mpr (by convert ha using 1; group)
    have := hh _ ha'
    calc a * (g * h * g⁻¹) = g * ((g⁻¹ * a * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = g * h * g⁻¹ * a := by group
  · intro hh a ha
    have ha' : g * a * g⁻¹ ∈ A := (hg a).mp ha
    have := hh _ ha'
    have h1 : g * a * g⁻¹ * (g * h * g⁻¹) = g * (a * h) * g⁻¹ := by group
    have h2 : g * h * g⁻¹ * (g * a * g⁻¹) = g * (h * a) * g⁻¹ := by group
    rw [h1, h2] at this
    have := congrArg (fun x => g⁻¹ * x * g) this
    simpa [mul_assoc] using this

theorem eleven_le_of_odd {q : ℕ} (hq : Odd q) (h3 : 3 ≤ q) (h : q ∉ ({3, 5, 7, 9} : Finset ℕ)) :
    11 ≤ q := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  obtain ⟨k, rfl⟩ := hq
  omega

theorem kgData_of_mulEquiv {A Z : Type} [Group A] [Group Z] [Finite A] [Finite Z] {r q : ℕ}
    (e : A ≃* Z) (hA : HarrisLit.IsSimpleChevalleyOver r (A ⧸ Open.fusionZStar A))
    (hA2 : ¬ GH74.GLS.InChev2 (A ⧸ Open.fusionZStar A))
    (hk : q * (q ^ 2 - 1) ∣ Nat.card (A ⧸ pPrimeCore 2 A)) :
    HarrisLit.IsSimpleChevalleyOver r (Z ⧸ Open.fusionZStar Z) ∧
      ¬ GH74.GLS.InChev2 (Z ⧸ Open.fusionZStar Z) ∧
      q * (q ^ 2 - 1) ∣ Nat.card (Z ⧸ pPrimeCore 2 Z) := by
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' e
  obtain ⟨h1, h2⟩ := chev_of_mulEquiv hA hA2 eZ
  exact ⟨h1, h2, UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr e ▸ hk⟩

theorem kgClaim (hleaf : ChevOddPumpLeaf) (hloc : FixedTwoComponentLocation)
    (n : ℕ) :
    ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ B : Subgroup H, IsPGroup 2 B → B ≤ normalizer (M : Set H) → Nat.card B ≤ n →
    ∀ T : Subgroup H, T ≤ M ⊓ centralizer (B : Set H) →
      IsPComponent 2 (T.subgroupOf (M ⊓ centralizer (B : Set H))) →
    ∀ r q : ℕ, r.Prime → r ≠ 2 → 11 ≤ q →
      HarrisLit.IsSimpleChevalleyOver r (↥T ⧸ Open.fusionZStar ↥T) →
      ¬ GH74.GLS.InChev2 (↥T ⧸ Open.fusionZStar ↥T) →
      q * (q ^ 2 - 1) ∣ Nat.card (↥T ⧸ pPrimeCore 2 ↥T) →
      HarrisLit.IsSimpleChevalleyOver r (↥M ⧸ Open.fusionZStar ↥M) ∧
        ¬ GH74.GLS.InChev2 (↥M ⧸ Open.fusionZStar ↥M) := by
  induction n with
  | zero =>
    intro H _ _ _ M _ B _ _ hcard
    exact absurd hcard (by have := Nat.card_pos (α := B); omega)
  | succ n ih =>
  intro H _ _ hK M hM B hB hBN hcard T hT hTp r q hr hr2 h11 hTY hTY2 hk
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect M := CatalogueBHeldSmallCore.pComponent_perfect 2 M hM
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  by_cases hB1 : B = ⊥
  ·
    subst hB1
    have hMC : M ⊓ centralizer ((⊥ : Subgroup H) : Set H) = M := by
      rw [centralizer_eq_top_iff_subset.mpr (by
        rw [coe_bot, Set.singleton_subset_iff]; exact one_mem _), inf_top_eq]
    rw [hMC] at hT hTp
    have : Group.IsPerfect (↥M ⧸ pPrimeCore 2 ↥M) := hMq.1
    have hcat : Blueprint.Catalog ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := by
      have : IsSimpleGroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := hMq.2.1
      exact SectionRank.catalog_of_isKGroupCat_of_surjective hK M
        ((QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M))).comp
          (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
        ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
    have hfix1 : fixedSubgroup (1 : MulAut ↥M) = ⊤ := by
      ext x
      simp [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff]
    set T' := T.subgroupOf M with hT'
    have hT'F : T' ≤ fixedSubgroup (1 : MulAut ↥M) := by rw [hfix1]; exact le_top
    have hT'p : IsPComponent 2 (T'.subgroupOf (fixedSubgroup (1 : MulAut ↥M))) := by
      rw [hfix1, CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T' ⊤ le_top]
      rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple] at hTp
      exact ⟨hTp.1.subgroupOf, hTp.2⟩
    obtain ⟨h1, h2, h3⟩ := kgData_of_mulEquiv (subgroupOfEquivOfLe hT).symm hTY hTY2 hk
    exact chevOddPump_aut hleaf hMq hcat 1 (fun _ => rfl) hT'F hT'p hr hr2 h11 h1 h2 h3
  obtain ⟨k, hk2⟩ := (IsPGroup.iff_card.mp hB)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hB1 (Subgroup.eq_bot_of_card_eq B (by simpa using hk2))
  obtain ⟨B₁', hB₁'⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 2 (n := k - 1)
    (by rw [hk2]; exact pow_dvd_pow 2 (Nat.sub_le k 1))
  have hidx : B₁'.index = 2 := by
    have h := B₁'.card_mul_index
    rw [hB₁', hk2] at h
    have : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [this] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hB₁'n : B₁'.Normal := Subgroup.normal_of_index_eq_two hidx
  set B₁ := B₁'.map B.subtype with hB₁def
  have hB₁B : B₁ ≤ B := map_subtype_le _
  have hB₁card : Nat.card B₁ ≤ n := by
    have h1 : Nat.card B₁ = Nat.card B₁' :=
      (Nat.card_congr (B₁'.equivMapOfInjective _ B.subtype_injective).toEquiv).symm
    rw [h1, hB₁']
    have h2 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨b', hb'⟩ : ∃ b' : B, b' ∉ B₁' := by
    by_contra hall
    push Not at hall
    have : B₁' = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [this, index_top] at hidx
    exact absurd hidx (by norm_num)
  set b : H := (b' : H) with hbdef
  have hbB : b ∈ B := b'.2
  have hb2 : b ^ 2 ∈ B₁ :=
    ⟨b' ^ 2, Subgroup.sq_mem_of_index_two hidx b', by simp [hbdef]⟩
  have hbN₁ : b ∈ normalizer (B₁ : Set H) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨b' * c * b'⁻¹, hB₁'n.conj_mem c hc b', by simp [hbdef]⟩
    · rintro ⟨c, hc, hce⟩
      refine ⟨b'⁻¹ * c * b', ?_, ?_⟩
      · have := hB₁'n.conj_mem c hc b'⁻¹
        rwa [inv_inv] at this
      · simp only [coe_subtype, coe_mul, coe_inv] at hce ⊢
        rw [hce, ← hbdef]
        group
  have hCB : centralizer (B : Set H) = centralizer (B₁ : Set H) ⊓ centralizer ({b} : Set H) := by
    apply le_antisymm
    · exact le_inf (centralizer_le hB₁B) (centralizer_le (Set.singleton_subset_iff.mpr hbB))
    · rintro c ⟨hc1, hc2⟩
      rw [mem_centralizer_iff]
      intro x hx
      by_cases hxB : (⟨x, hx⟩ : B) ∈ B₁'
      · exact mem_centralizer_iff.mp hc1 x ⟨_, hxB, rfl⟩
      ·
        have hy : b'⁻¹ * ⟨x, hx⟩ ∈ B₁' := by
          by_contra hy
          have := (Subgroup.mul_mem_iff_of_index_two hidx (a := b'⁻¹) (b := ⟨x, hx⟩)).mpr
          exact hy (this ⟨fun h => (hb' (by simpa using inv_mem h)).elim,
            fun h => (hxB h).elim⟩)
        set y : H := ((b'⁻¹ * ⟨x, hx⟩ : B) : H) with hydef
        have hyc : y * c = c * y := mem_centralizer_iff.mp hc1 _ ⟨_, hy, rfl⟩
        have hbc : b * c = c * b := by
          have := mem_centralizer_singleton_iff.mp hc2
          first | exact this | exact this.symm
        have hx' : x = b * y := by simp [hydef, hbdef]
        rw [hx']
        calc b * y * c = b * (y * c) := by group
          _ = b * (c * y) := by rw [hyc]
          _ = (b * c) * y := by group
          _ = (c * b) * y := by rw [hbc]
          _ = c * (b * y) := by group
  set X := M ⊓ centralizer (B₁ : Set H) with hXdef
  have hbX : b ∈ normalizer (X : Set H) :=
    GSThmB.Pump516.mem_normalizer_inf (hBN hbB) (mem_normalizer_centralizer hbN₁)
  let β : MulAut ↥X := X.normalizerMonoidHom ⟨b, hbX⟩
  have hβapp : ∀ x : ↥X, ((β x : ↥X) : H) = b * x * b⁻¹ := fun x => rfl
  have hb2c : ∀ x : ↥X, b ^ 2 * x = x * b ^ 2 := fun x =>
    mem_centralizer_iff.mp (mem_inf.mp x.2).2 _ hb2
  have hββ : ∀ x, β (β x) = x := by
    intro x
    apply Subtype.ext
    rw [hβapp, hβapp]
    calc b * (b * (x : H) * b⁻¹) * b⁻¹ = (b * b) * x * (b * b)⁻¹ := by group
      _ = x := by rw [← sq, hb2c x]; group
  have hfix : fixedSubgroup β = (M ⊓ centralizer (B : Set H)).subgroupOf X := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, hCB, ← inf_assoc,
      mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      have h1 := congrArg Subtype.val h
      rw [hβapp] at h1
      calc (x : H) * b = b * x * b⁻¹ * b := by rw [h1]
        _ = b * x := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hβapp, ← h]
      group
  have hMBX : M ⊓ centralizer (B : Set H) ≤ X := inf_le_inf_left _ (centralizer_le hB₁B)
  have hTX : T ≤ X := hT.trans hMBX
  set T₁ := T.subgroupOf X with hT₁def
  have hT₁F : T₁ ≤ fixedSubgroup β := by
    rw [hfix]
    intro x hx
    exact hT hx
  have hT₁p : IsPComponent 2 (T₁.subgroupOf (fixedSubgroup β)) := by
    rw [hfix, OddStandard.Solomon75.isPComponent_subgroupOf_subgroupOf_iff hT hTX,
      inf_eq_left.mpr hMBX]
    exact hTp
  obtain ⟨h1, h2, h3⟩ := kgData_of_mulEquiv (subgroupOfEquivOfLe hTX).symm hTY hTY2 hk
  obtain ⟨X₁, hX₁, hcase⟩ := hloc ↥X β hββ T₁ hT₁F hT₁p
  have hX₁data : HarrisLit.IsSimpleChevalleyOver r (↥X₁ ⧸ Open.fusionZStar ↥X₁) ∧
      ¬ GH74.GLS.InChev2 (↥X₁ ⧸ Open.fusionZStar ↥X₁) ∧
      q * (q ^ 2 - 1) ∣ Nat.card (↥X₁ ⧸ pPrimeCore 2 ↥X₁) := by
    rcases hcase with ⟨hinv, hT₁X₁⟩ | ⟨-, ⟨eZ⟩, hdvd⟩
    · obtain ⟨g1, g2⟩ := chevOddPump_sub hleaf (hK.subgroup X) β hββ hX₁ hinv hT₁F hT₁p hT₁X₁
        hr hr2 h11 h1 h2 h3
      refine ⟨g1, g2, h3.trans ?_⟩
      rw [← UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr
        (subgroupOfEquivOfLe hT₁X₁)]
      exact card_quot_pPrimeCore_dvd _
    · obtain ⟨g1, g2⟩ := chev_of_mulEquiv h1 h2 eZ
      exact ⟨g1, g2, h3.trans hdvd⟩
  set K₁ := X₁.map X.subtype with hK₁def
  have hK₁X : K₁ ≤ X := map_subtype_le _
  have hK₁p : IsPComponent 2 (K₁.subgroupOf X) := by
    have hK₁X₁ : K₁.subgroupOf X = X₁ :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective X₁
    rw [hK₁X₁]
    exact hX₁
  obtain ⟨k1, k2, k3⟩ := hX₁data
  obtain ⟨g1, g2, g3⟩ :=
    kgData_of_mulEquiv (X₁.equivMapOfInjective X.subtype X.subtype_injective) k1 k2 k3
  exact ih H hK M hM B₁ (hB.to_le hB₁B) (hB₁B.trans hBN) hB₁card K₁ hK₁X hK₁p r q hr hr2 h11
    g1 g2 g3

theorem card_specialLinearGroup_two {F : Type} [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    show Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) by
      rw [Nat.mul_sub_one, sq], ← mul_assoc, Nat.mul_div_cancel _ (by omega), mul_comm]

theorem kgSLTwoInput_of_inputs (hleaf : ChevOddPumpLeaf) (hloc : FixedTwoComponentLocation)
    (hO : LieOrderFormulasInput) :
    KGSLTwoInput := by
  intro H _ _ hK M hM B hB hBN T hT hTp r e hr hr2 he hq hSL
  have hodd : Odd (r ^ e) := (hr.odd_of_ne_two hr2).pow
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have h3 : 3 ≤ r ^ e := hr3.trans (Nat.le_self_pow (by omega) r)
  have h11 := eleven_le_of_odd hodd h3 hq
  obtain ⟨-, -, hL, -⟩ := HarrisLit.Lemma47.sl2_facts hr hr2 he (by omega) hSL
  obtain ⟨eTZ⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥T
  have hTL := Blueprint.LieModel.of_mulEquiv eTZ hL
  have hTY2 := not_inChev2_of_lieModel_psl_two_of_orders hO hr hr2 he hq hTL
  have hk : r ^ e * ((r ^ e) ^ 2 - 1) ∣ Nat.card (↥T ⧸ pPrimeCore 2 ↥T) := by
    obtain ⟨F, _, _, hF, ⟨eSL⟩⟩ := hSL
    rw [Nat.card_congr eSL.toEquiv, card_specialLinearGroup_two, hF]
  exact kgClaim hleaf hloc (Nat.card B) H hK M hM B hB hBN le_rfl T hT hTp r (r ^ e) hr hr2 h11
    ⟨.PSL, 2, e, hTL⟩ hTY2 hk

end CFSG.ComponentClassification.GS82PumpInputs
