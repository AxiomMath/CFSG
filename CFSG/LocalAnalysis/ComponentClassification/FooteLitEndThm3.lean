module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInnerRank
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem card_le_sq_card_inf_centralizer_of_sq {T : Subgroup X}
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hsq : ∀ y ∈ T, y * y = 1) {v : X}
    (hvT : ∀ y ∈ T, v * y * v⁻¹ ∈ T) (hv2 : ∀ y ∈ T, v * (v * y * v⁻¹) * v⁻¹ = y) :
    Nat.card T ≤ Nat.card (T ⊓ centralizer {v} : Subgroup X) ^ 2 := by
  let φ : T →* T :=
    { toFun := fun y => ⟨y * (v * y * v⁻¹), mul_mem y.2 (hvT y y.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y₁ y₂ => Subtype.ext (by
        change (y₁ : X) * y₂ * (v * (y₁ * y₂) * v⁻¹) =
          (y₁ * (v * y₁ * v⁻¹)) * (y₂ * (v * y₂ * v⁻¹))
        have e : v * ((y₁ : X) * y₂) * v⁻¹ = (v * y₁ * v⁻¹) * (v * y₂ * v⁻¹) := by group
        rw [e]
        have h := hcomm _ y₂.2 _ (hvT y₁ y₁.2)
        calc (y₁ : X) * y₂ * ((v * y₁ * v⁻¹) * (v * y₂ * v⁻¹))
            = y₁ * (y₂ * (v * y₁ * v⁻¹)) * (v * y₂ * v⁻¹) := by group
          _ = y₁ * ((v * y₁ * v⁻¹) * y₂) * (v * y₂ * v⁻¹) := by rw [h]
          _ = _ := by group) }
  set C := T ⊓ centralizer {v} with hC
  have hmemC : ∀ y : X, y ∈ C ↔ y ∈ T ∧ v * y * v⁻¹ = y := fun y => by
    rw [hC, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, by rw [← h, mul_inv_cancel_right]⟩
    · rintro ⟨hy, h⟩
      refine ⟨hy, ?_⟩
      calc y * v = (v * y * v⁻¹) * v := by rw [h]
        _ = v * y := by group
  have hker : φ.ker = C.subgroupOf T := by
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf, hmemC]
    constructor
    · intro h
      have h' : (y : X) * (v * y * v⁻¹) = 1 := congrArg Subtype.val h
      refine ⟨y.2, ?_⟩
      have := eq_inv_of_mul_eq_one_right h'
      rw [this, inv_eq_of_mul_eq_one_right (hsq y y.2)]
    · rintro ⟨-, h⟩
      exact Subtype.ext (by
        change (y : X) * (v * y * v⁻¹) = 1
        rw [h, hsq y y.2])
  have hrange : φ.range ≤ C.subgroupOf T := by
    rintro _ ⟨y, rfl⟩
    rw [mem_subgroupOf, hmemC]
    refine ⟨(φ y).2, ?_⟩
    change v * ((y : X) * (v * y * v⁻¹)) * v⁻¹ = y * (v * y * v⁻¹)
    have e : v * ((y : X) * (v * y * v⁻¹)) * v⁻¹ =
        (v * y * v⁻¹) * (v * (v * y * v⁻¹) * v⁻¹) := by group
    rw [e, hv2 y y.2]
    exact hcomm _ (hvT y y.2) _ y.2
  have hCT : C ≤ T := inf_le_left
  have hcardC : Nat.card (C.subgroupOf T) = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe hCT).toEquiv
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hker, hcardC] at h1
  have h2 : Nat.card φ.range ≤ Nat.card C := by
    rw [← hcardC]
    exact Subgroup.card_le_of_le hrange
  rw [← h1, sq]
  exact Nat.mul_le_mul_left _ h2

theorem exists_two_involutions_of_card_eight {F : Subgroup X} (hF2 : ∀ x ∈ F, x ^ 2 = 1)
    (hF8 : Nat.card F = 8) :
    ∃ u ∈ F, ∃ v ∈ F, orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v := by
  obtain ⟨W, hW, hWF⟩ := exists_isKleinFour_le hF2 (by omega)
  obtain ⟨u, hu, hu1, -⟩ := exists_ne_of_isKleinFour hW 1
  obtain ⟨v, hv, hv1, hvu⟩ := exists_ne_of_isKleinFour hW u
  exact ⟨u, hWF hu, v, hWF hv, orderOf_eq_prime (sq_eq_one_of_isKleinFour hW hu) hu1,
    orderOf_eq_prime (sq_eq_one_of_isKleinFour hW hv) hv1, fun h => hvu h.symm⟩

theorem exists_isKleinFour_of_card_le {Q F : Subgroup X} (hFQ : F ≤ Q)
    (hF2 : ∀ x ∈ F, x ^ 2 = 1) {τ : X}
    (hcard : 4 ≤ Nat.card ↥(F ⊓ centralizer ({τ} : Set X))) :
    ∃ V : Subgroup X, IsKleinFour V ∧ V ≤ Q ⊓ centralizer ({τ} : Set X) := by
  obtain ⟨V, hV, hVF⟩ := exists_isKleinFour_le (B := F ⊓ centralizer ({τ} : Set X))
    (fun x hx => hF2 x (mem_inf.mp hx).1) hcard
  exact ⟨V, hV, hVF.trans (inf_le_inf_right _ hFQ)⟩

theorem exists_isKleinFour_of_thm3Conclusion {Q T S F : Subgroup X}
    (h3 : Thm3Conclusion Q T S) (hTQ : T ≤ normalizer (Q : Set X)) (hTQb : T ⊓ Q = ⊥)
    (hS : IsSylowOf 2 S (Q ⊔ T)) (hTS : T ≤ S) {τ : X} (hτT : τ ∈ T)
    (hτ : orderOf τ = 2) (huniq : ∀ x ∈ T, orderOf x = 2 → x = τ) (hFQ : F ≤ Q)
    (hF2 : ∀ x ∈ F, x ^ 2 = 1) (hF8 : Nat.card F = 8) :
    ∃ V : Subgroup X, IsKleinFour V ∧ V ≤ Q ⊓ centralizer ({τ} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hτ2)
  have hτ1 : τ ≠ 1 := fun h => by rw [h, orderOf_one] at hτ; omega
  have hτQ : τ ∉ Q := fun h => hτ1 (by
    have : τ ∈ T ⊓ Q := mem_inf.mpr ⟨hτT, h⟩
    rwa [hTQb, mem_bot] at this)
  have hQn : Q ⊔ T ≤ normalizer (Q : Set X) := sup_le le_normalizer hTQ
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 3) (by rw [hF8]; norm_num)
  have hSQ : IsSylowOf 2 (S ⊓ Q) Q := hS.inf_of_le_normalizer le_sup_left hQn
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hSQ hFQ hFp
  set F' := conjugate F k with hF'def
  have hF'SQ : F' ≤ S ⊓ Q := conjugate_le_of_forall hk
  have hF'2 : ∀ x ∈ F', x ^ 2 = 1 := sq_eq_one_of_mem_conjugate hF2 k
  have hF'8 : Nat.card F' = 8 := by rw [card_conjugate_eq_card, hF8]
  rcases h3 with ⟨-, hshape, -⟩ | hnorm | ⟨n, hn, hO2, hOL, hcommOL, hel, hcard, ⟨e⟩⟩ |
    ⟨x, hxQ, hW, hTTx, hcommx, hWS, hWn, -, -⟩ | ⟨hWn, hW3, -, -, -, hΩ, hidx⟩
  ·
    exfalso
    obtain ⟨u, hu, v, hv, hu2, hv2, huv⟩ := exists_two_involutions_of_card_eight hF'2 hF'8
    rcases hshape with hcyc | hquat | hdih
    · have h1 := AschbacherToolkit.atMostOneInvolution_of_isCyclic (P := ↥(S ⊓ Q))
        ⟨u, hF'SQ hu⟩ ⟨v, hF'SQ hv⟩ (by rw [Subgroup.orderOf_mk]; exact hu2)
        (by rw [Subgroup.orderOf_mk]; exact hv2)
      exact huv (congrArg Subtype.val h1)
    · exact huv (AschbacherTheorem5.SectionSix.quaternion_unique_involution hquat (hF'SQ hu)
        (hF'SQ hv) hu2 hv2)
    · have h1 := AschbacherTheorem5.SectionSix.dihedral_pRank_two hdih
      have hel : Open.IsElemAbelian 2 F' := ⟨isMulCommutative_of_sq_eq_one hF'2, hF'2⟩
      have h2 := SectionRank.le_pRank one_lt_two hF'SQ hel (k := 3) (by rw [hF'8]; norm_num)
      omega
  ·
    refine exists_isKleinFour_of_card_le hFQ hF2 ?_
    have hFC : F ⊓ centralizer ({τ} : Set X) = F := by
      refine inf_eq_left.mpr fun q hq => mem_centralizer_singleton_iff.mpr ?_
      have hqQ := hFQ hq
      have h1 : q * τ * q⁻¹ * τ⁻¹ ∈ T :=
        mul_mem ((mem_normalizer_iff.mp (hnorm (mem_sup_left hqQ)) τ).mp hτT) (inv_mem hτT)
      have h2 : q * τ * q⁻¹ * τ⁻¹ ∈ Q := by
        have h3 : τ * q⁻¹ * τ⁻¹ ∈ Q := (mem_normalizer_iff.mp (hTQ hτT) q⁻¹).mp (inv_mem hqQ)
        rw [show q * τ * q⁻¹ * τ⁻¹ = q * (τ * q⁻¹ * τ⁻¹) by group]
        exact mul_mem hqQ h3
      have h4 : q * τ * q⁻¹ * τ⁻¹ ∈ T ⊓ Q := mem_inf.mpr ⟨h1, h2⟩
      rw [hTQb, mem_bot] at h4
      calc q * τ = q * τ * q⁻¹ * τ⁻¹ * (τ * q) := by group
        _ = τ * q := by rw [h4, one_mul]
    rw [hFC, hF8]
    norm_num
  ·
    set O₂ := Open.pCoreOf 2 (Q ⊔ T) with hO₂def
    set L' := oTwoPrime Q with hL'def
    have hcommOL' : ∀ a ∈ O₂, ∀ l ∈ L', a * l = l * a := by
      intro a ha l hl
      have h1 : ⁅a, l⁆ ∈ ⁅O₂, L'⁆ := commutator_mem_commutator ha hl
      rw [hcommOL, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hτO : τ ∈ O₂ ⊔ L' := by
      rw [← hO2]
      exact subset_closure ⟨mem_sup_right hτT, 1, by rw [pow_one]; exact hτ2⟩
    have hO₂L : O₂ ≤ normalizer (L' : Set X) := fun a ha => mem_normalizer_iff.mpr fun l => by
      constructor
      · intro hl
        rw [hcommOL' a ha l hl, mul_assoc, mul_inv_cancel, mul_one]
        exact hl
      · intro hl
        have h1 := hcommOL' a ha _ hl
        have h2 : l = a * l * a⁻¹ := by
          calc l = a⁻¹ * ((a * l * a⁻¹) * a) := by group
            _ = a⁻¹ * (a * (a * l * a⁻¹)) := by rw [← h1]
            _ = a * l * a⁻¹ := by group
        rw [h2]
        exact hl
    obtain ⟨a, ha, l, hl, hal⟩ : ∃ a ∈ O₂, ∃ l ∈ L', a * l = τ := by
      have h1 : τ ∈ ((O₂ : Set X) * L') := by
        rw [← coe_mul_of_left_le_normalizer_right O₂ L' hO₂L]
        exact hτO
      obtain ⟨a, ha, l, hl, hal⟩ := Set.mem_mul.mp h1
      exact ⟨a, ha, l, hl, hal⟩
    have ha2 : a ^ 2 = 1 := hel.2 a ha
    have hl2 : l ^ 2 = 1 := by
      have h1 : (a * l) ^ 2 = a ^ 2 * l ^ 2 := by
        rw [sq, sq, sq, mul_assoc, ← mul_assoc l a l, ← hcommOL' a ha l hl]
        group
      rw [hal, hτ2, ha2, one_mul] at h1
      exact h1.symm
    have hlp : IsPGroup 2 (zpowers l) := by
      have hdvd : orderOf l ∣ 2 := orderOf_dvd_of_pow_eq_one hl2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
    obtain ⟨P, hP⟩ := (hlp.comap_subtype (K := L')).exists_le_sylow
    set P' := P.mapSurjective (f := e.toMonoidHom) e.surjective with hP'def
    obtain ⟨hPel, hPcard⟩ := Walter.psl2_even_sylow_two hn P'
    have hP'coe : (P' : Subgroup _) = (P : Subgroup L').map e.toMonoidHom := rfl
    have hPsq : ∀ y ∈ (P : Subgroup L'), y ^ 2 = 1 := by
      intro y hy
      have h1 : e y ∈ (P' : Subgroup _) := by rw [hP'coe]; exact ⟨y, hy, rfl⟩
      have := hPel
      have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := (P' : Subgroup _)) (e y) h1
      apply e.injective
      rw [map_pow, h2, map_one]
    have hPcomm : ∀ y ∈ (P : Subgroup L'), ∀ z ∈ (P : Subgroup L'), y * z = z * y := by
      intro y hy z hz
      have h1 : e y ∈ (P' : Subgroup _) := by rw [hP'coe]; exact ⟨y, hy, rfl⟩
      have h2 : e z ∈ (P' : Subgroup _) := by rw [hP'coe]; exact ⟨z, hz, rfl⟩
      have h3 := (@IsMulCommutative.is_comm _ _ hPel.toIsMulCommutative).comm ⟨e y, h1⟩ ⟨e z, h2⟩
      apply e.injective
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h3
    have hPcard' : Nat.card (P : Subgroup L') = 2 ^ n := by
      rw [← hPcard, hP'coe, card_map_of_injective e.injective]
    set U := (P : Subgroup L').map L'.subtype with hUdef
    have hUL : U ≤ L' := map_subtype_le _
    have hLQ : L' ≤ Q := (closure_le Q).mpr fun y hy => hy.1
    have hlP : (⟨l, hl⟩ : L') ∈ (P : Subgroup L') :=
      hP (show (⟨l, hl⟩ : L') ∈ (zpowers l).subgroupOf L' from mem_subgroupOf.mpr (mem_zpowers l))
    have hlU : l ∈ U := ⟨⟨l, hl⟩, hlP, rfl⟩
    have hU2 : ∀ y ∈ U, y ^ 2 = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hPsq y hy, map_one]
    have hUcomm : ∀ y ∈ U, ∀ z ∈ U, y * z = z * y := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hPcomm y hy z hz]
    have hU4 : 4 ≤ Nat.card U := by
      rw [hUdef, card_map_of_injective L'.subtype_injective, hPcard']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨V, hV, hVU⟩ := exists_isKleinFour_le hU2 hU4
    refine ⟨V, hV, le_inf ((hVU.trans hUL).trans hLQ) fun v hv => ?_⟩
    rw [mem_centralizer_singleton_iff, ← hal]
    have h1 := hcommOL' a ha v (hUL (hVU hv))
    have h2 := hUcomm v (hVU hv) l hlU
    calc v * (a * l) = (v * a) * l := by group
      _ = (a * v) * l := by rw [h1]
      _ = a * (v * l) := by group
      _ = a * (l * v) := by rw [h2]
      _ = a * l * v := by group
  ·
    set W := relativeWeakClosure Q T S with hWdef
    set Tx := rightConjugate T x with hTxdef
    set τx := x⁻¹ * τ * x with hτxdef
    have hτW : τ ∈ W := subgroup_le_relative_weak_closure Q T S hTS hτT
    have hcommTTx : ∀ t ∈ T, ∀ s ∈ Tx, t * s = s * t := by
      intro t ht s hs
      have h1 : ⁅t, s⁆ ∈ ⁅T, Tx⁆ := commutator_mem_commutator ht hs
      rw [hcommx, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hTTxN : T ≤ normalizer (Tx : Set X) := fun t ht => mem_normalizer_iff.mpr fun s => by
      constructor
      · intro hs
        rw [hcommTTx t ht s hs, mul_assoc, mul_inv_cancel, mul_one]
        exact hs
      · intro hs
        have h1 := hcommTTx t ht _ hs
        have h2 : s = t * s * t⁻¹ := by
          calc s = t⁻¹ * ((t * s * t⁻¹) * t) := by group
            _ = t⁻¹ * (t * (t * s * t⁻¹)) := by rw [← h1]
            _ = t * s * t⁻¹ := by group
        rw [h2]
        exact hs
    have hor : ∀ f ∈ F, f * τ * f⁻¹ = τ ∨ f * τ * f⁻¹ = τx := by
      intro f hf
      have hfQ := hFQ hf
      have hfW : f * τ * f⁻¹ ∈ W :=
        (mem_normalizer_iff.mp (hWn (mem_sup_left hfQ)) τ).mp hτW
      have h1 : f * τ * f⁻¹ ∈ ((T : Set X) * Tx) := by
        rw [← coe_mul_of_left_le_normalizer_right T Tx hTTxN, ← hW]
        exact hfW
      obtain ⟨t, ht, s, hs, hts⟩ := Set.mem_mul.mp h1
      have hconj2 : (f * τ * f⁻¹) * (f * τ * f⁻¹) = 1 := by
        calc (f * τ * f⁻¹) * (f * τ * f⁻¹) = f * (τ * τ) * f⁻¹ := by group
          _ = 1 := by rw [← sq, hτ2]; group
      have hts2 : t ^ 2 * s ^ 2 = 1 := by
        calc t ^ 2 * s ^ 2 = t * (t * s) * s := by rw [sq, sq]; group
          _ = t * (s * t) * s := by rw [hcommTTx t ht s hs]
          _ = (t * s) * (t * s) := by group
          _ = 1 := by rw [hts]; exact hconj2
      have ht2 : t ^ 2 = 1 := by
        have h2 : t ^ 2 = (s ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hts2
        have h3 : t ^ 2 ∈ T ⊓ Tx := mem_inf.mpr ⟨pow_mem ht 2, h2 ▸ inv_mem (pow_mem hs 2)⟩
        rwa [hTTx, mem_bot] at h3
      have hs2 : s ^ 2 = 1 := by rw [ht2, one_mul] at hts2; exact hts2
      have htc : t = 1 ∨ t = τ := by
        by_cases ht1 : t = 1
        · exact Or.inl ht1
        · exact Or.inr (huniq t ht (orderOf_eq_prime ht2 ht1))
      have hsc : s = 1 ∨ s = τx := by
        have hxs : x * s * x⁻¹ ∈ T := (mem_rightConjugate_iff T x s).mp hs
        have hxs2 : (x * s * x⁻¹) ^ 2 = 1 := by
          calc (x * s * x⁻¹) ^ 2 = x * (s * s) * x⁻¹ := by rw [sq]; group
            _ = 1 := by rw [← sq, hs2]; group
        by_cases hxs1 : x * s * x⁻¹ = 1
        · left
          calc s = x⁻¹ * (x * s * x⁻¹) * x := by group
            _ = 1 := by rw [hxs1]; group
        · right
          have h4 := huniq _ hxs (orderOf_eq_prime hxs2 hxs1)
          calc s = x⁻¹ * (x * s * x⁻¹) * x := by group
            _ = τx := by rw [h4]
      have hττx : τ * τx ∈ Q := by
        have h5 : τ * x⁻¹ * τ⁻¹ ∈ Q := (mem_normalizer_iff.mp (hTQ hτT) x⁻¹).mp (inv_mem hxQ)
        have h6 : τ * τx = (τ * x⁻¹ * τ⁻¹) * x := by rw [hτxdef, hτinv]; group
        rw [h6]
        exact mul_mem h5 hxQ
      rcases htc with ht' | ht' <;> rcases hsc with hs' | hs' <;> rw [ht', hs'] at hts
      · exfalso
        rw [mul_one] at hts
        apply hτ1
        calc τ = f⁻¹ * (f * τ * f⁻¹) * f := by group
          _ = 1 := by rw [← hts]; group
      · exact Or.inr (by rw [← hts, one_mul])
      · exact Or.inl (by rw [← hts, mul_one])
      · exfalso
        apply hτQ
        have h7 : f * τ * f⁻¹ ∈ Q := hts ▸ hττx
        have h8 : τ = f⁻¹ * (f * τ * f⁻¹) * f := by group
        rw [h8]
        exact mul_mem (mul_mem (inv_mem hfQ) h7) hfQ
    refine exists_isKleinFour_of_card_le hFQ hF2 ?_
    have h9 := card_le_two_mul_card_inf_centralizer_of_or hor
    rw [hF8] at h9
    omega
  ·
    set W := relativeWeakClosure Q T S with hWdef
    have hT2' : Nat.card T = 2 := by
      have h1 : T ≤ zpowers τ := by
        rw [← hΩ]
        refine (closure_le _).mpr fun y hy => ?_
        obtain ⟨hyT, hy2⟩ := hy
        by_cases hy1 : y = 1
        · rw [hy1]
          exact one_mem _
        · rw [huniq y hyT (orderOf_eq_prime hy2 hy1)]
          exact mem_zpowers τ
      have h2 := Subgroup.card_le_of_le h1
      rw [Nat.card_zpowers, hτ] at h2
      have h3 : 2 ≤ Nat.card T := by
        have h4 := Subgroup.card_le_of_le (zpowers_le.mpr hτT)
        rwa [Nat.card_zpowers, hτ] at h4
      omega
    have hW8 : Nat.card W = 8 := by rw [hW3, hT2']; norm_num
    have hWS' : W ≤ S := relative_weak_closure_le Q T S
    have hS16 : Nat.card S = 16 := by
      have h1 := Subgroup.relIndex_mul_card W S
      rw [hidx, inf_eq_left.mpr hWS', hW8] at h1
      omega
    have hSN : S ≤ normalizer ((S ⊓ Q : Subgroup X) : Set X) := fun s hs =>
      mem_normalizer_iff.mpr fun y => by
        rw [mem_inf, mem_inf]
        constructor
        · rintro ⟨hyS, hyQ⟩
          exact ⟨mul_mem (mul_mem hs hyS) (inv_mem hs),
            (mem_normalizer_iff.mp (hQn (hS.le hs)) y).mp hyQ⟩
        · rintro ⟨hyS, hyQ⟩
          refine ⟨?_, (mem_normalizer_iff.mp (hQn (hS.le hs)) y).mpr hyQ⟩
          have h1 : y = s⁻¹ * (s * y * s⁻¹) * s := by group
          rw [h1]
          exact mul_mem (mul_mem (inv_mem hs) hyS) hs
    have : ((S ⊓ Q).subgroupOf S).Normal :=
      (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hSN
    have hfac : ∀ s ∈ S, ∃ t ∈ T, ∃ q ∈ S ⊓ Q, s = t * q := by
      intro s hs
      have h1 : s ∈ ((T : Set X) * Q) := by
        rw [← coe_mul_of_left_le_normalizer_right T Q hTQ, sup_comm]
        exact hS.le hs
      obtain ⟨t, ht, q, hq, rfl⟩ := Set.mem_mul.mp h1
      refine ⟨t, ht, q, mem_inf.mpr ⟨?_, hq⟩, rfl⟩
      have h2 : q = t⁻¹ * (t * q) := by group
      rw [h2]
      exact mul_mem (inv_mem (hTS ht)) hs
    have hidxT := relIndex_eq_relIndex_inf_of_mul hTS inf_le_left hfac
    have hbot : T ⊓ (S ⊓ Q) = ⊥ := by
      rw [eq_bot_iff, ← hTQb]
      exact inf_le_inf_left _ inf_le_right
    rw [hbot, relIndex_bot_left] at hidxT
    have hSQ8 : Nat.card (S ⊓ Q : Subgroup X) = 8 := by
      have h1 : Nat.card T * T.relIndex S = Nat.card S := by
        have := Subgroup.card_mul_index (T.subgroupOf S)
        rwa [Nat.card_congr (subgroupOfEquivOfLe hTS).toEquiv] at this
      rw [hidxT, hT2', hS16] at h1
      omega
    have hF'eq : F' = S ⊓ Q := Subgroup.eq_of_le_of_card_ge hF'SQ (by rw [hSQ8, hF'8])
    have hτF' : ∀ y ∈ F', τ * y * τ⁻¹ ∈ F' := by
      intro y hy
      rw [hF'eq] at hy ⊢
      exact (mem_normalizer_iff.mp (hSN (hTS hτT)) y).mp hy
    have hc := card_le_sq_card_inf_centralizer_of_sq (T := F')
      (fun a ha b hb => commute_of_sq_eq_one hF'2 ha hb)
      (fun y hy => by rw [← sq]; exact hF'2 y hy) hτF'
      (fun y _ => by rw [hτinv]; calc τ * (τ * y * τ) * τ = (τ * τ) * y * (τ * τ) := by group
        _ = y := by rw [← sq, hτ2]; group)
    rw [hF'8] at hc
    have hdvd : Nat.card ↥(F' ⊓ centralizer {τ}) ∣ 8 :=
      hF'8 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h4 : 4 ≤ Nat.card ↥(F' ⊓ centralizer {τ}) := by
      have h5 : Nat.card ↥(F' ⊓ centralizer {τ}) ∈ Nat.divisors 8 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have h6 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
      rw [h6] at h5
      simp only [Finset.mem_insert, Finset.mem_singleton] at h5
      rcases h5 with h | h | h | h <;> rw [h] at hc ⊢ <;> omega
    exact exists_isKleinFour_of_card_le (hF'SQ.trans inf_le_right) hF'2 h4

end CFSG.ComponentClassification.FooteLit
