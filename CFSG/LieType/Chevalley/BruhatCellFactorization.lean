module

public import CFSG.LieType.Chevalley.BruhatDecomposition
public import CFSG.LieType.Chevalley.OppositeBorel
public import CFSG.LieType.Chevalley.PositiveRootCollection
public import CFSG.LieType.Chevalley.WeylInversion

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag}

@[expose] def nonInversionSet
    (w : WeylGroup τ) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ 0 < height α ∧ 0 < height (w • α)}

theorem smul_nsmul_add_nsmul
    (w : WeylGroup τ) (a b : ℕ) (α β : Fin τ.rank → ℤ) :
    w • (a • α + b • β) = a • (w • α) + b • (w • β) := by
  rw [smul_add, smul_comm w a α, smul_comm w b β]

theorem inversionSet_pos
    {w : WeylGroup τ} {α : Fin τ.rank → ℤ} (h : α ∈ inversionSet w) :
    IsRoot τ α ∧ 0 < height α :=
  ⟨h.1, h.2.1⟩

theorem nonInversionSet_pos
    {w : WeylGroup τ} {α : Fin τ.rank → ℤ} (h : α ∈ nonInversionSet w) :
    IsRoot τ α ∧ 0 < height α :=
  ⟨h.1, h.2.1⟩

theorem inversionSet_closed
    (w : WeylGroup τ) :
    ∀ α ∈ inversionSet w, ∀ β ∈ inversionSet w, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ inversionSet w := by
  rintro α ⟨-, hα, -, hwα⟩ β ⟨-, hβ, -, hwβ⟩ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, IsRoot.smul hr w, ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith
  · rw [smul_nsmul_add_nsmul, height_nsmul_add_nsmul]
    nlinarith

theorem nonInversionSet_closed
    (w : WeylGroup τ) :
    ∀ α ∈ nonInversionSet w, ∀ β ∈ nonInversionSet w, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ nonInversionSet w := by
  rintro α ⟨-, hα, hwα⟩ β ⟨-, hβ, hwβ⟩ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith
  · rw [smul_nsmul_add_nsmul, height_nsmul_add_nsmul]
    nlinarith

theorem exists_rootEnum {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite) :
    ∃ α : Fin S.ncard → Fin τ.rank → ℤ, Function.Injective α ∧ Set.range α = S := by
  classical
  set s := hS.toFinset
  have hcard : S.ncard = s.card := Set.ncard_eq_toFinset_card S hS
  let α : Fin s.card → Fin τ.rank → ℤ := fun k => (s.equivFin.symm k : Fin τ.rank → ℤ)
  have hα : Function.Injective α := fun k l h => s.equivFin.symm.injective (Subtype.ext h)
  have hrange : Set.range α = S := by
    ext γ
    refine ⟨fun ⟨k, hk⟩ => hk ▸ hS.mem_toFinset.1 (s.equivFin.symm k).2, fun hγ =>
      ⟨s.equivFin ⟨γ, hS.mem_toFinset.2 hγ⟩, ?_⟩⟩
    simp [α]
  rw [hcard]
  exact ⟨α, hα, hrange⟩

theorem finite_of_forall_isRoot_pos {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α) : S.Finite :=
  (finite_setOf_isRoot τ).subset fun α hα => (hS α hα).1

variable {K : Type} [Field K]

theorem rootSpan_le_posUnipotent
    {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α) : rootSpan τ K S ≤ posUnipotent τ K :=
  iSup₂_le fun α hα => le_iSup₂_of_le α (hS α hα) le_rfl

theorem rootSpan_le_negUnipotent
    {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ height α < 0) : rootSpan τ K S ≤ negUnipotent τ K :=
  iSup₂_le fun α hα => le_iSup₂_of_le α (hS α hα) le_rfl

theorem pinnedX_mem_rootSpan
    {S : Set (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ} (hα : α ∈ S)
    (c : K) : pinnedX τ K α c ∈ rootSpan τ K S :=
  (le_iSup₂_of_le α hα le_rfl : rootSubgroup τ K α ≤ rootSpan τ K S)
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem list_prod_pinnedX_mem_rootSpan
    {S : Set (Fin τ.rank → ℤ)} {m : ℕ}
    (α : Fin m → Fin τ.rank → ℤ) (hα : ∀ k, α k ∈ S) (c : Fin m → K) :
    (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod ∈ rootSpan τ K S := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  exact pinnedX_mem_rootSpan (hα k) (c k)

theorem posUnipotent_eq_mul_rootSpan
    (w : WeylGroup τ) :
    (posUnipotent τ K : Set (ModGL τ K)) =
      (rootSpan τ K (nonInversionSet w) : Set (ModGL τ K)) *
        (rootSpan τ K (inversionSet w) : Set (ModGL τ K)) := by
  refine Set.Subset.antisymm (fun u hu => ?_) ?_
  · obtain ⟨αJ, hJinj, hJrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos
      fun α h => nonInversionSet_pos (w := w) h)
    obtain ⟨αI, hIinj, hIrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos
      fun α h => inversionSet_pos (w := w) h)
    have hJ : ∀ k, αJ k ∈ nonInversionSet w := fun k => hJrange ▸ Set.mem_range_self k
    have hI : ∀ k, αI k ∈ inversionSet w := fun k => hIrange ▸ Set.mem_range_self k
    set α := Fin.append αJ αI
    have hdisj : ∀ k l, αJ k ≠ αI l := fun k l h => by
      have h1 := (hJ k).2.2
      have h2 := (hI l).2.2.2
      rw [h] at h1
      omega
    have hinj : Function.Injective α := by
      intro k l h
      induction k using Fin.addCases with
      | left k =>
        induction l using Fin.addCases with
        | left l => simp only [α, Fin.append_left] at h; rw [hJinj h]
        | right l =>
          simp only [α, Fin.append_left, Fin.append_right] at h
          exact absurd h (hdisj k l)
      | right k =>
        induction l using Fin.addCases with
        | left l =>
          simp only [α, Fin.append_left, Fin.append_right] at h
          exact absurd h.symm (hdisj l k)
        | right l => simp only [α, Fin.append_right] at h; rw [hIinj h]
    have hrange : Set.range α = {β | IsRoot τ β ∧ 0 < height β} := by
      ext β
      constructor
      · rintro ⟨k, rfl⟩
        induction k using Fin.addCases with
        | left k => simpa [α] using nonInversionSet_pos (hJ k)
        | right k => simpa [α] using inversionSet_pos (hI k)
      · rintro ⟨hβ, hβp⟩
        rcases IsRoot.height_pos_or_neg (IsRoot.smul hβ w) with hp | hn
        · obtain ⟨k, hk⟩ : β ∈ Set.range αJ := by
            rw [hJrange]
            exact ⟨hβ, hβp, hp⟩
          exact ⟨Fin.castAdd _ k, by simp [α, hk]⟩
        · obtain ⟨k, hk⟩ : β ∈ Set.range αI := by
            rw [hIrange]
            exact ⟨hβ, hβp, IsRoot.smul hβ w, hn⟩
          exact ⟨Fin.natAdd _ k, by simp [α, hk]⟩
    obtain ⟨c, -, rfl⟩ := ((positive_root_collection τ K).2 α hinj hrange).2.2 hu
    refine ⟨_, list_prod_pinnedX_mem_rootSpan αJ hJ (fun k => c (Fin.castAdd _ k)), _,
      list_prod_pinnedX_mem_rootSpan αI hI (fun k => c (Fin.natAdd _ k)), ?_⟩
    simp only
    rw [← List.prod_append, ← List.ofFn_fin_append]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    induction k using Fin.addCases with
    | left k => simp [α]
    | right k => simp [α]
  · rintro _ ⟨u, hu, v, hv, rfl⟩
    exact mul_mem (rootSpan_le_posUnipotent (fun α h => nonInversionSet_pos (w := w) h) hu)
      (rootSpan_le_posUnipotent (fun α h => inversionSet_pos (w := w) h) hv)

theorem canonicalRep_conj_mem_rootSpan
    {w : WeylGroup τ} {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) {u : ModGL τ K} (hu : u ∈ rootSpan τ K S) :
    canonicalRep (coxeterSystem τ) K w * u * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      rootSpan τ K ((fun α => w • α) '' S) := by
  rw [← (canonical_weyl_root_transport τ K).1 w S hS]
  exact ⟨u, hu, rfl⟩

theorem canonicalRep_conj_mem_posUnipotent
    {w : WeylGroup τ} {u : ModGL τ K}
    (hu : u ∈ rootSpan τ K (nonInversionSet w)) :
    canonicalRep (coxeterSystem τ) K w * u * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      posUnipotent τ K := by
  have h := canonicalRep_conj_mem_rootSpan (w := w)
    (fun α (h : α ∈ nonInversionSet w) => h.1) hu
  refine rootSpan_le_posUnipotent (fun β hβ => ?_) h
  obtain ⟨α, ⟨hα, -, hwα⟩, rfl⟩ := hβ
  exact ⟨IsRoot.smul hα w, hwα⟩

theorem canonicalRep_conj_mem_negUnipotent
    {w : WeylGroup τ} {u : ModGL τ K}
    (hu : u ∈ rootSpan τ K (inversionSet w)) :
    canonicalRep (coxeterSystem τ) K w * u * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      negUnipotent τ K := by
  have h := canonicalRep_conj_mem_rootSpan (w := w)
    (fun α (h : α ∈ inversionSet w) => h.1) hu
  refine rootSpan_le_negUnipotent (fun β hβ => ?_) h
  obtain ⟨α, ⟨-, -, hwα⟩, rfl⟩ := hβ
  exact hwα

theorem borelGroup_inf_negUnipotent
    : borelGroup τ K ⊓ negUnipotent τ K = ⊥ := by
  refine eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (Units.ext ?_)
  obtain ⟨hgB, hgU⟩ := Subgroup.mem_inf.1 hg
  exact eq_one_of_isUpperTriangular_of_isLowerUnitriangular
    ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.1 g hgB)
    (((positive_root_triangularity.{0, 0} τ).1 K).2.1 g hgU)

theorem bijOn_bruhatCell
    (w : WeylGroup τ) :
    Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * canonicalRep (coxeterSystem τ) K w * p.2)
      ((borelGroup τ K : Set (ModGL τ K)) ×ˢ (rootSpan τ K (inversionSet w) : Set (ModGL τ K)))
      (bruhatCell τ K w) := by
  set n := canonicalRep (coxeterSystem τ) K w
  have hIB : rootSpan τ K (inversionSet w) ≤ borelGroup τ K :=
    (rootSpan_le_posUnipotent fun α h => inversionSet_pos (w := w) h).trans le_sup_right
  refine ⟨fun p hp => mem_bruhatCell.2 ⟨p.1, hp.1, p.2, hIB hp.2, rfl⟩, ?_, fun x hx => ?_⟩
  · rintro ⟨b, u⟩ ⟨hb, hu⟩ ⟨b', u'⟩ ⟨hb', hu'⟩ h
    simp only at h hb hu hb' hu'
    have hmem : b'⁻¹ * b = n * (u' * u⁻¹) * n⁻¹ :=
      calc b'⁻¹ * b = b'⁻¹ * (b * n * u) * u⁻¹ * n⁻¹ := by group
        _ = b'⁻¹ * (b' * n * u') * u⁻¹ * n⁻¹ := by rw [h]
        _ = n * (u' * u⁻¹) * n⁻¹ := by group
    have hneg : b'⁻¹ * b ∈ negUnipotent τ K := by
      rw [hmem]
      exact canonicalRep_conj_mem_negUnipotent (mul_mem hu' (inv_mem hu))
    have h1 : b'⁻¹ * b ∈ borelGroup τ K ⊓ negUnipotent τ K :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hb') hb, hneg⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, inv_mul_eq_one] at h1
    subst h1
    rw [mul_left_cancel h]
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
    obtain ⟨-, -, -, -, hHU, -⟩ := triangular_borel_structure.{0, 0} τ K
    have hb'' : b' ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
      rw [← hHU]
      exact hb'
    obtain ⟨h, hh, v, hv, rfl⟩ := hb''
    rw [posUnipotent_eq_mul_rootSpan w] at hv
    obtain ⟨uJ, huJ, uI, huI, rfl⟩ := hv
    have hnh : n * h * n⁻¹ ∈ torusGroup τ K :=
      (Subgroup.mem_normalizer_iff.1 ((canonical_weyl_root_transport τ K).2.2 w) h).1 hh
    refine ⟨(b * (n * h * n⁻¹) * (n * uJ * n⁻¹), uI), ⟨mul_mem (mul_mem hb
      (torusGroup_le_borelGroup hnh))
      (Subgroup.mem_sup_right (canonicalRep_conj_mem_posUnipotent huJ)), huI⟩, ?_⟩
    show b * (n * h * n⁻¹) * (n * uJ * n⁻¹) * n * uI = b * n * (h * (uJ * uI))
    group

theorem bijOn_prod_pinnedX_inversionSet
    (w : WeylGroup τ) {m : ℕ} (α : Fin m → Fin τ.rank → ℤ)
    (hα : Function.Injective α) (hrange : Set.range α = inversionSet w) :
    Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
      Set.univ (rootSpan τ K (inversionSet w)) :=
  bijOn_prod_pinnedX K (fun _ h => inversionSet_pos (w := w) h) (inversionSet_closed w) α hα
    hrange

theorem card_rootSpan
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S) :
    Nat.card (rootSpan τ K S) = Nat.card K ^ S.ncard := by
  obtain ⟨α, hα, hrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos hS)
  calc Nat.card (rootSpan τ K S) = Nat.card (Set.univ : Set (Fin S.ncard → K)) :=
        Nat.card_congr (bijOn_prod_pinnedX K hS hclosed α hα hrange).equiv.symm
    _ = Nat.card K ^ S.ncard := by rw [Nat.card_univ, Nat.card_fun, Nat.card_fin]

theorem card_rootSpan_inversionSet
    (w : WeylGroup τ) :
    Nat.card (rootSpan τ K (inversionSet w)) = Nat.card K ^ (coxeterSystem τ).length w := by
  rw [card_rootSpan (fun _ h => inversionSet_pos (w := w) h) (inversionSet_closed w),
    ← (weyl_inversion_length τ).1 w]

theorem card_posUnipotent :
    Nat.card (posUnipotent τ K) =
      Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard :=
  card_rootSpan (fun _ h => h) fun α hα β hβ a b ha hb hr => ⟨hr, by
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    rw [height_nsmul_add_nsmul]
    nlinarith [hα.2, hβ.2]⟩

theorem card_borelGroup :
    Nat.card (borelGroup τ K) = Nat.card (torusGroup τ K) * Nat.card (posUnipotent τ K) := by
  obtain ⟨-, -, -, -, hHU, -, huniq, -⟩ := triangular_borel_structure.{0, 0} τ K
  have hbij : Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * p.2)
      ((torusGroup τ K : Set (ModGL τ K)) ×ˢ (posUnipotent τ K : Set (ModGL τ K)))
      (borelGroup τ K : Set (ModGL τ K)) := by
    refine ⟨fun p hp => ?_, fun p hp q hq h => ?_, fun x hx => ?_⟩
    · rw [hHU]
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
    · obtain ⟨h1, h2⟩ := huniq p.1 hp.1 q.1 hq.1 p.2 hp.2 q.2 hq.2 h
      exact Prod.ext h1 h2
    · rw [hHU] at hx
      obtain ⟨h, hh, u, hu, rfl⟩ := hx
      exact ⟨(h, u), ⟨hh, hu⟩, rfl⟩
  calc Nat.card (borelGroup τ K) = Nat.card ((torusGroup τ K : Set (ModGL τ K)) ×ˢ
        (posUnipotent τ K : Set (ModGL τ K))) := Nat.card_congr hbij.equiv.symm
    _ = Nat.card (torusGroup τ K) * Nat.card (posUnipotent τ K) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      rfl

theorem card_bruhatCell
    (w : WeylGroup τ) :
    Nat.card (bruhatCell τ K w) = Nat.card (torusGroup τ K) *
      Nat.card K ^ ({α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard +
        (coxeterSystem τ).length w) := by
  calc Nat.card (bruhatCell τ K w) = Nat.card ((borelGroup τ K : Set (ModGL τ K)) ×ˢ
        (rootSpan τ K (inversionSet w) : Set (ModGL τ K))) :=
        Nat.card_congr (bijOn_bruhatCell (K := K) w).equiv.symm
    _ = Nat.card (borelGroup τ K) * Nat.card (rootSpan τ K (inversionSet w)) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      rfl
    _ = _ := by
      rw [card_borelGroup, card_posUnipotent, card_rootSpan_inversionSet, pow_add, mul_assoc]

theorem card_adjointGroup
    [Finite K] :
    Nat.card (adjointGroup τ K) = Nat.card (torusGroup τ K) *
      Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard *
        ∑ᶠ w : WeylGroup τ, Nat.card K ^ (coxeterSystem τ).length w := by
  classical
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  have : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  have e : (adjointGroup τ K : Set (ModGL τ K)) ≃ Σ w : WeylGroup τ, bruhatCell τ K w := by
    rw [adjointGroup_eq_iUnion_bruhatCell]
    exact Set.unionEqSigmaOfDisjoint fun w w' h => disjoint_bruhatCell h
  calc Nat.card (adjointGroup τ K) = Nat.card (Σ w : WeylGroup τ, bruhatCell τ K w) :=
        Nat.card_congr e
    _ = ∑ w : WeylGroup τ, Nat.card (bruhatCell τ K w) := Nat.card_sigma
    _ = _ := by
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [card_bruhatCell, pow_add, mul_assoc]

variable (τ K) in
theorem bruhat_cell_factorization :
    (∀ w : WeylGroup τ,
      Set.BijOn (fun p : ModGL τ K × ModGL τ K =>
          p.1 * canonicalRep (coxeterSystem τ) K w * p.2)
        ((borelGroup τ K : Set (ModGL τ K)) ×ˢ (rootSpan τ K (inversionSet w) : Set (ModGL τ K)))
        (bruhatCell τ K w)) ∧
    (∀ (w : WeylGroup τ) {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α →
      Set.range α = inversionSet w →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K (inversionSet w))) ∧
    ∀ [Finite K],
      (∀ w : WeylGroup τ,
        Nat.card (rootSpan τ K (inversionSet w)) = Nat.card K ^ (coxeterSystem τ).length w) ∧
      (∀ w : WeylGroup τ, Nat.card (bruhatCell τ K w) = Nat.card (torusGroup τ K) *
        Nat.card K ^ ({α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard +
          (coxeterSystem τ).length w)) ∧
      Nat.card (adjointGroup τ K) = Nat.card (torusGroup τ K) *
        Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard *
          ∑ᶠ w : WeylGroup τ, Nat.card K ^ (coxeterSystem τ).length w :=
  ⟨bijOn_bruhatCell, fun w _ α hα hrange => bijOn_prod_pinnedX_inversionSet w α hα hrange,
    ⟨card_rootSpan_inversionSet, card_bruhatCell, card_adjointGroup⟩⟩

end CFSG.LieType.Chevalley
