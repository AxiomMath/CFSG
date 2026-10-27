module

public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_eq_mul {a b c d : G} (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d) : ⁅a * c, b * d⁆ = ⁅a, b⁆ * ⁅c, d⁆ := by
  simp only [commutatorElement_def]
  have h1 : Commute a⁻¹ (c * d * c⁻¹) := ((hac.mul_right had).mul_right hac.inv_right).inv_left
  have h2 : Commute b⁻¹ (c * d * c⁻¹ * d⁻¹) :=
    (((hbc.mul_right hbd).mul_right hbc.inv_right).mul_right hbd.inv_right).inv_left
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
    _ = a * (b * c) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [← hbc.eq]
    _ = a * b * (c * d * c⁻¹ * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * (c * d * c⁻¹)) * d⁻¹ * b⁻¹ := by rw [← h1.eq]
    _ = a * b * a⁻¹ * (c * d * c⁻¹ * d⁻¹ * b⁻¹) := by group
    _ = a * b * a⁻¹ * (b⁻¹ * (c * d * c⁻¹ * d⁻¹)) := by rw [← h2.eq]
    _ = a * b * a⁻¹ * b⁻¹ * (c * d * c⁻¹ * d⁻¹) := by group

theorem mem_centralizer_singleton_of_conj {t g : G} (h : t⁻¹ * g * t = g) :
    g ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.1 hw]
  calc t * g = t * (t⁻¹ * g * t) := by rw [h]
    _ = g * t := by group

section TwoFactors

variable {X Y : Subgroup G} {t : G}

theorem commute_of_commutator_eq_bot' (hXY : ⁅X, Y⁆ = ⊥) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) :
    Commute x y := by
  have := Subgroup.commutator_mem_commutator hx hy
  rw [hXY, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem coe_sup_of_commutator_eq_bot (hXY : ⁅X, Y⁆ = ⊥) :
    ((X ⊔ Y : Subgroup G) : Set G) = (X : Set G) * (Y : Set G) :=
  coe_mul_of_left_le_normalizer_right X Y
    ((commutator_eq_bot_iff_le_centralizer.1 hXY).trans (centralizer_le_normalizer _))

theorem exists_fixed_decomposition (hXY : ⁅X, Y⁆ = ⊥) (hX : t ∈ normalizer (X : Set G))
    (hY : t ∈ normalizer (Y : Set G)) {u : G}
    (hu : u ∈ (X ⊔ Y) ⊓ centralizer ({t} : Set G)) :
    ∃ x ∈ X, ∃ y ∈ Y, ∃ c ∈ X ⊓ Y,
      x * y = u ∧ t⁻¹ * x * t = x * c ∧ t⁻¹ * y * t = y * c⁻¹ := by
  obtain ⟨hu1, hu2⟩ := mem_inf.1 hu
  rw [← SetLike.mem_coe, coe_sup_of_commutator_eq_bot hXY] at hu1
  obtain ⟨x, hx, y, hy, rfl⟩ := hu1
  have hxt : t⁻¹ * x * t ∈ X := by
    simpa using (mem_normalizer_iff.1 (inv_mem hX) x).1 hx
  have hyt : t⁻¹ * y * t ∈ Y := by
    simpa using (mem_normalizer_iff.1 (inv_mem hY) y).1 hy
  have hfix : t⁻¹ * x * t * (t⁻¹ * y * t) = x * y := by
    have h := mem_centralizer_iff.1 hu2 t rfl
    calc t⁻¹ * x * t * (t⁻¹ * y * t) = t⁻¹ * (t * (x * y)) := by rw [h]; group
      _ = x * y := by rw [inv_mul_cancel_left]
  have hc : x⁻¹ * (t⁻¹ * x * t) = y * (t⁻¹ * y * t)⁻¹ := by
    rw [eq_mul_inv_of_mul_eq hfix]
    group
  have hcX : x⁻¹ * (t⁻¹ * x * t) ∈ X := mul_mem (inv_mem hx) hxt
  have hcY : x⁻¹ * (t⁻¹ * x * t) ∈ Y := by
    rw [hc]
    exact mul_mem hy (inv_mem hyt)
  refine ⟨x, hx, y, hy, _, mem_inf.2 ⟨hcX, hcY⟩, rfl, (mul_inv_cancel_left x _).symm, ?_⟩
  have hcy : Commute (x⁻¹ * (t⁻¹ * x * t))⁻¹ y :=
    (commute_of_commutator_eq_bot' hXY hcX hy).inv_left
  rw [← hcy.eq, hc]
  group

theorem commutator_fixed_sup_le (hXY : ⁅X, Y⁆ = ⊥) (hX : t ∈ normalizer (X : Set G))
    (hY : t ∈ normalizer (Y : Set G)) :
    ⁅(X ⊔ Y) ⊓ centralizer ({t} : Set G), (X ⊔ Y) ⊓ centralizer ({t} : Set G)⁆ ≤
      (X ⊓ centralizer ({t} : Set G)) ⊔ (Y ⊓ centralizer ({t} : Set G)) := by
  have hcomm : ∀ {x y : G}, x ∈ X → y ∈ Y → Commute x y := fun hx hy =>
    commute_of_commutator_eq_bot' hXY hx hy
  rw [commutator_le]
  intro u hu v hv
  obtain ⟨x, hx, y, hy, c, hc, rfl, hxt, hyt⟩ := exists_fixed_decomposition hXY hX hY hu
  obtain ⟨x', hx', y', hy', c', hc', rfl, hxt', hyt'⟩ := exists_fixed_decomposition hXY hX hY hv
  obtain ⟨hcX, hcY⟩ := mem_inf.1 hc
  obtain ⟨hcX', hcY'⟩ := mem_inf.1 hc'
  rw [commutatorElement_mul_mul_eq_mul (hcomm hx hy) (hcomm hx hy') (hcomm hx' hy)
    (hcomm hx' hy')]
  have hconj : ∀ a b : G, t⁻¹ * ⁅a, b⁆ * t = ⁅t⁻¹ * a * t, t⁻¹ * b * t⁆ := fun a b => by
    simp only [commutatorElement_def]
    group
  refine mul_mem (mem_sup_left (mem_inf.2 ⟨?_, ?_⟩)) (mem_sup_right (mem_inf.2 ⟨?_, ?_⟩))
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hx') (inv_mem hx)) (inv_mem hx')
  · refine mem_centralizer_singleton_of_conj ?_
    rw [hconj, hxt, hxt']
    exact commutatorElement_mul_mul_of_commute (hcomm hx' hcY).symm (hcomm hcX' hcY).symm
      (hcomm hx hcY').symm
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
  · refine mem_centralizer_singleton_of_conj ?_
    rw [hconj, hyt, hyt']
    exact commutatorElement_mul_mul_of_commute (hcomm hcX hy').inv_left
      (hcomm hcX hcY').inv_left.inv_right (hcomm hcX' hy).inv_left

theorem le_or_le_of_isComponentOf_centralizer [Finite G] {J : Subgroup G} (hXY : ⁅X, Y⁆ = ⊥)
    (hX : t ∈ normalizer (X : Set G)) (hY : t ∈ normalizer (Y : Set G))
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G))) (hJXY : J ≤ X ⊔ Y) :
    J ≤ X ∨ J ≤ Y := by
  set C := centralizer ({t} : Set G) with hCdef
  set D := (X ⊓ C) ⊔ (Y ⊓ C) with hDdef
  have hJC : J ≤ C := hJ.1
  have hJD : J ≤ D := by
    rw [← commutator_self_of_isQuasisimple hJ.2.2]
    exact (commutator_mono (le_inf hJXY hJC) (le_inf hJXY hJC)).trans
      (commutator_fixed_sup_le hXY hX hY)
  have hDC : D ≤ C := sup_le inf_le_right inf_le_right
  have hJn : CFSG.IsComponent (J.subgroupOf D) :=
    (isComponentOf_iff_isComponent_subgroupOf hJD).1 (isComponentOf_of_le hJ hJD hDC)
  have hXYC : ⁅X ⊓ C, Y ⊓ C⁆ = ⊥ :=
    eq_bot_iff.2 (hXY ▸ commutator_mono inf_le_left inf_le_left)
  have hnormX : D ≤ normalizer ((X ⊓ C : Subgroup G) : Set G) :=
    sup_le le_normalizer ((commutator_eq_bot_iff_le_centralizer.1
      (by rw [commutator_comm]; exact hXYC)).trans (centralizer_le_normalizer _))
  have hnormY : D ≤ normalizer ((Y ⊓ C : Subgroup G) : Set G) :=
    sup_le ((commutator_eq_bot_iff_le_centralizer.1 hXYC).trans (centralizer_le_normalizer _))
      le_normalizer
  have hread : ∀ N : Subgroup G, N ≤ D → ⁅J.subgroupOf D, N.subgroupOf D⁆ = ⊥ → ⁅J, N⁆ = ⊥ :=
    fun N hND h => by
      have := congrArg (Subgroup.map D.subtype) h
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJD,
        Subgroup.map_subgroupOf_eq_of_le hND, Subgroup.map_bot] at this
  have hle : ∀ N : Subgroup G, J.subgroupOf D ≤ N.subgroupOf D → J ≤ N := fun N h j hj =>
    (Subgroup.mem_subgroupOf.1 (h (Subgroup.mem_subgroupOf.2 hj :
      (⟨j, hJD hj⟩ : D) ∈ J.subgroupOf D)))
  rcases component_normal_subgroup hJn (normal_subgroupOf_of_le_normalizer hnormX) with h1 | h1
  · exact Or.inl ((hle _ h1).trans inf_le_left)
  rcases component_normal_subgroup hJn (normal_subgroupOf_of_le_normalizer hnormY) with h2 | h2
  · exact Or.inr ((hle _ h2).trans inf_le_left)
  exfalso
  have hcX := commutator_eq_bot_iff_le_centralizer.1 (hread _ le_sup_left h1)
  have hcY := commutator_eq_bot_iff_le_centralizer.1 (hread _ le_sup_right h2)
  refine not_le_centralizer_self_of_isQuasisimple hJ.2.2 ?_
  rw [le_centralizer_iff] at hcX hcY ⊢
  exact (hJD.trans (sup_le hcX hcY))

end TwoFactors

section Orbit

variable {H : Type*} [Group H] [Finite H] {t : H}

omit [Finite H] in
theorem conjSub_conjSub_of_inv_eq (ht : t⁻¹ = t) (K : Subgroup H) :
    conjSub t⁻¹ (conjSub t⁻¹ K) = K := by
  have := conjSub_inv_conjSub t K
  rw [ht] at this ⊢
  exact this

omit [Finite H] in
theorem mem_normalizer_of_conjSub_inv_le (ht : t⁻¹ = t) {K : Subgroup H}
    (h : conjSub t⁻¹ K ≤ K) : t ∈ normalizer (K : Set H) :=
  mem_normalizer_of_conjSub_le (by rwa [ht] at h) h

omit [Finite H] in
theorem conjSub_sSup_le {S : Set (Subgroup H)} (hS : ∀ K ∈ S, conjSub t⁻¹ K ∈ S) :
    conjSub t⁻¹ (sSup S) ≤ sSup S := by
  rw [conjSub, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (hS K hK)

theorem exists_mem_le_sup_conjSub (ht : orderOf t = 2) {J : Subgroup H}
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set H))) :
    ∀ (n : ℕ) (S : Finset (Subgroup H)), S.card ≤ n → (∀ K ∈ S, CFSG.IsComponent K) →
      (∀ K ∈ S, conjSub t⁻¹ K ∈ S) → J ≤ sSup (S : Set (Subgroup H)) →
        ∃ L ∈ S, J ≤ L ⊔ conjSub t⁻¹ L := by
  classical
  have ht' : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have hJne : ∀ S : Finset (Subgroup H), J ≤ sSup (S : Set (Subgroup H)) → S.Nonempty := by
    intro S hS
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, sSup_empty, le_bot_iff] at hS
    exact not_le_centralizer_self_of_isQuasisimple hJ.2.2 (by rw [hS]; exact bot_le)
  intro n
  induction n with
  | zero =>
    intro S hS _ _ hJS
    obtain ⟨K, hK⟩ := hJne S hJS
    exact absurd (Finset.card_pos.2 ⟨K, hK⟩) (by omega)
  | succ n ih =>
    intro S hS hcomp hinv hJS
    obtain ⟨L, hL⟩ := hJne S hJS
    set O : Finset (Subgroup H) := {L, conjSub t⁻¹ L} with hOdef
    have hOS : O ⊆ S := by
      intro K hK
      rw [Finset.mem_insert, Finset.mem_singleton] at hK
      rcases hK with rfl | rfl
      · exact hL
      · exact hinv L hL
    set S' := S \ O with hS'def
    have hS'inv : ∀ K ∈ S', conjSub t⁻¹ K ∈ S' := by
      intro K hK
      rw [Finset.mem_sdiff] at hK ⊢
      refine ⟨hinv K hK.1, fun hKO => hK.2 ?_⟩
      rw [Finset.mem_insert, Finset.mem_singleton] at hKO ⊢
      rcases hKO with h | h
      · right
        rw [← h, conjSub_conjSub_of_inv_eq ht']
      · left
        have := congrArg (conjSub t⁻¹) h
        rwa [conjSub_conjSub_of_inv_eq ht', conjSub_conjSub_of_inv_eq ht'] at this
    have hS'card : S'.card ≤ n := by
      have : S'.card < S.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset hOS ⟨L, Finset.mem_insert_self _ _⟩)
      omega
    have hsplit : sSup (S : Set (Subgroup H)) =
        (L ⊔ conjSub t⁻¹ L) ⊔ sSup (S' : Set (Subgroup H)) := by
      conv_lhs => rw [← Finset.union_sdiff_of_subset hOS]
      rw [Finset.coe_union, sSup_union, hOdef, Finset.coe_pair, sSup_pair]
    have hLcomp := hcomp L hL
    have hLtcomp := hcomp _ (hinv L hL)
    have hcommute : ⁅L ⊔ conjSub t⁻¹ L, sSup (S' : Set (Subgroup H))⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
      refine sSup_le fun K hK => ?_
      have hK' := Finset.mem_sdiff.1 hK
      have hKL : K ≠ L := fun h => hK'.2 (by rw [h]; exact Finset.mem_insert_self _ _)
      have hKLt : K ≠ conjSub t⁻¹ L := fun h => hK'.2 (by
        rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hc1 := (CFSG.LocalCores.distinct_components_commute (hcomp K hK'.1) hLcomp).resolve_left
        hKL
      have hc2 := (CFSG.LocalCores.distinct_components_commute (hcomp K hK'.1)
        hLtcomp).resolve_left hKLt
      rw [← le_centralizer_iff]
      exact sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hc1))
        (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hc2))
    have hnormO : t ∈ normalizer ((L ⊔ conjSub t⁻¹ L : Subgroup H) : Set H) := by
      refine mem_normalizer_of_conjSub_inv_le ht' ?_
      rw [conjSub, Subgroup.map_sup]
      refine sup_le le_sup_right ?_
      change conjSub t⁻¹ (conjSub t⁻¹ L) ≤ _
      rw [conjSub_conjSub_of_inv_eq ht']
      exact le_sup_left
    have hnormS' : t ∈ normalizer ((sSup (S' : Set (Subgroup H)) : Subgroup H) : Set H) :=
      mem_normalizer_of_conjSub_inv_le ht' (conjSub_sSup_le fun K hK => hS'inv K hK)
    rw [hsplit] at hJS
    rcases le_or_le_of_isComponentOf_centralizer hcommute hnormO hnormS' hJ hJS with h | h
    · exact ⟨L, hL, h⟩
    · obtain ⟨L', hL', hJL'⟩ := ih S' hS'card (fun K hK => hcomp K (Finset.mem_sdiff.1 hK).1)
        hS'inv h
      exact ⟨L', (Finset.mem_sdiff.1 hL').1, hJL'⟩

theorem involution_layer_component_orbit_location (ht : orderOf t = 2) {J : Subgroup H}
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set H)))
    (hJE : J ≤ CFSG.layer H) :
    ∃ L : Subgroup H, CFSG.IsComponent L ∧
      ((conjSub t⁻¹ L = L ∧ CFSG.Assembly.IsComponentOf J (L ⊓ centralizer ({t} : Set H))) ∨
        (conjSub t⁻¹ L ≠ L ∧
          (J : Set H) = {g | ∃ x ∈ L, x * (t⁻¹ * x * t) = g} ∧
          (∃ δ : L →* J, (∀ x : L, (δ x : H) = x * (t⁻¹ * x * t)) ∧ Function.Surjective δ ∧
            δ.ker ≤ center L) ∧
          Nonempty (J ⧸ center J ≃* L ⧸ center L) ∧
          (∃ Z : Subgroup H,
            Z ≤ (center (L ⊔ conjSub t⁻¹ L : Subgroup H)).map (L ⊔ conjSub t⁻¹ L).subtype ∧
            (((L ⊔ conjSub t⁻¹ L) ⊓ centralizer ({t} : Set H) : Subgroup H) : Set H) =
              (J : Set H) * (Z : Set H)) ∧
          ⁅(L ⊔ conjSub t⁻¹ L) ⊓ centralizer ({t} : Set H),
            (L ⊔ conjSub t⁻¹ L) ⊓ centralizer ({t} : Set H)⁆ = J)) := by
  classical
  have ht' : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have : Finite (Subgroup H) := Finite.of_injective (fun K : Subgroup H => (K : Set H))
    SetLike.coe_injective
  set S₀ : Finset (Subgroup H) := (Set.toFinite {K : Subgroup H | CFSG.IsComponent K}).toFinset
    with hS₀
  have hmem : ∀ K, K ∈ S₀ ↔ CFSG.IsComponent K := fun K => by
    rw [hS₀, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hsSup : sSup (S₀ : Set (Subgroup H)) = CFSG.layer H := by
    rw [hS₀, Set.Finite.coe_toFinset]
    rfl
  obtain ⟨L, hL, hJL⟩ := exists_mem_le_sup_conjSub ht hJ S₀.card S₀ le_rfl
    (fun K hK => (hmem K).1 hK) (fun K hK => (hmem _).2 (isComponent_conjSub ((hmem K).1 hK) _))
    (hsSup ▸ hJE)
  have hLc := (hmem L).1 hL
  refine ⟨L, hLc, ?_⟩
  by_cases hLt : conjSub t⁻¹ L = L
  · refine Or.inl ⟨hLt, ?_⟩
    rw [hLt, sup_idem] at hJL
    exact isComponentOf_of_le hJ (le_inf hJL hJ.1) inf_le_right
  · refine Or.inr ⟨hLt, ?_⟩
    have hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥ := commutator_conjSub_eq_bot hLc hLt
    obtain ⟨hset, hΔC, hsurj, hker, -, -, hCset, hIZ, hder, hcomp, -, hiso⟩ :=
      swapped_quasisimple_fixed_central_product ht (assembly_isQuasisimple_of_isComponent hLc)
        hAB
    have hJC' : CFSG.Assembly.IsComponentOf J ((L ⊔ conjSub t⁻¹ L) ⊓ centralizer ({t} : Set H)) :=
      isComponentOf_of_le hJ (le_inf hJL hJ.1) inf_le_right
    have hJΔ : J = (swapDiag hAB).range := (hcomp J).1 hJC'
    subst hJΔ
    refine ⟨hset, ⟨(swapDiag hAB).rangeRestrict, fun x => rfl, hsurj, ?_⟩, ?_,
      ⟨_, hIZ, hCset⟩, hder⟩
    · exact hker
    · obtain ⟨e⟩ := hiso
      exact ⟨e⟩

end Orbit

end CFSG.LocalAnalysis.ComponentInitial
