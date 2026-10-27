module

public import CFSG.LieType.Chevalley.SimpleWeylComplement
public import CFSG.LieType.Chevalley.RankOneBruhat
public import CFSG.LieType.Chevalley.WeylExchange

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable (τ : Tag) (K : Type) [Field K]

@[expose] def bruhatCell
    (w : WeylGroup τ) : Set (ModGL τ K) :=
  (borelGroup τ K : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K w} *
    (borelGroup τ K : Set (ModGL τ K))

variable {τ K}

theorem mem_bruhatCell
    {w : WeylGroup τ} {x : ModGL τ K} :
    x ∈ bruhatCell τ K w ↔ ∃ b ∈ borelGroup τ K, ∃ b' ∈ borelGroup τ K,
      b * canonicalRep (coxeterSystem τ) K w * b' = x := by
  simp only [bruhatCell, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩

private theorem torus_le_borel
    : torusGroup τ K ≤ borelGroup τ K :=
  le_sup_left

private theorem posUnipotent_le_borel
    : posUnipotent τ K ≤ borelGroup τ K :=
  le_sup_right

theorem xUnit_mem_borelGroup
    (i : Fin τ.rank) (c : K) : xUnit τ K i c ∈ borelGroup τ K := by
  rw [← pinnedX_single]
  exact posUnipotent_le_borel (Subgroup.mem_iSup_of_mem (Pi.single i 1)
    (Subgroup.mem_iSup_of_mem ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩
      (Subgroup.subset_closure ⟨c, rfl⟩)))

theorem weylElt_mul_eq_of_mem_borelGroup
    (i : Fin τ.rank) {b : ModGL τ K}
    (hb : b ∈ borelGroup τ K) :
    ∃ b' ∈ borelGroup τ K, ∃ c : K,
      weylElt τ K i 1 * b = b' * (weylElt τ K i 1 * xUnit τ K i c) := by
  obtain ⟨-, -, -, -, hHU, -⟩ := triangular_borel_structure.{0, 0} τ K
  obtain ⟨hle, -, -, hUN, -⟩ := simple_positive_root_complement τ K i
  have hb' : b ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hHU]
    exact hb
  obtain ⟨h, hh, v, hv, rfl⟩ := hb'
  rw [SetLike.mem_coe, ← SetLike.mem_coe, hUN] at hv
  obtain ⟨u, hu, x, hx, rfl⟩ := hv
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  set n := weylElt τ K i 1
  have hnh : n * h * n⁻¹ ∈ torusGroup τ K :=
    (Subgroup.mem_normalizer_iff.1 (weylElt_mem_normalizer_torus τ K i 1) h).1 hh
  have hnu : n * u * n⁻¹ ∈ posComplement τ K i := by
    rw [← (simple_Weyl_positive_complement τ K i 1).1]
    exact ⟨u, hu, rfl⟩
  refine ⟨n * h * n⁻¹ * (n * u * n⁻¹), mul_mem (torus_le_borel hnh)
    (posUnipotent_le_borel (hle hnu)), c, ?_⟩
  rw [pinnedX_single]
  group

theorem exists_mul_canonicalRep_eq
    {w : WeylGroup τ} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : 0 < height (w⁻¹ • α)) {g : ModGL τ K} (hg : g ∈ rootSubgroup τ K α) :
    ∃ b ∈ borelGroup τ K,
      g * canonicalRep (coxeterSystem τ) K w = canonicalRep (coxeterSystem τ) K w * b := by
  have ht := (canonical_weyl_root_transport τ K).2.1 w (w⁻¹ • α) (IsRoot.smul hα w⁻¹)
  rw [smul_inv_smul] at ht
  rw [← ht] at hg
  obtain ⟨b, hb, rfl⟩ := hg
  refine ⟨b, posUnipotent_le_borel (Subgroup.mem_iSup_of_mem (w⁻¹ • α)
    (Subgroup.mem_iSup_of_mem ⟨IsRoot.smul hα w⁻¹, hpos⟩ hb)), ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_mul_cancel_right]

theorem height_inv_smul_single_pos
    {w : WeylGroup τ} {i : Fin τ.rank}
    (h : (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1) :
    0 < height (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  rcases IsRoot.height_pos_or_neg (IsRoot.smul (isRoot_single τ i) w⁻¹) with hp | hn
  · exact hp
  · have := ((weyl_exchange_condition τ).1 w i).1 ⟨IsRoot.smul (isRoot_single τ i) w⁻¹, hn⟩
    omega

theorem height_inv_smul_neg_single_pos
    {w : WeylGroup τ} {i : Fin τ.rank}
    (h : (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w - 1) :
    0 < height (w⁻¹ • (-Pi.single i 1 : Fin τ.rank → ℤ)) := by
  rw [smul_neg, height_neg, neg_pos]
  rcases IsRoot.height_pos_or_neg (IsRoot.smul (isRoot_single τ i) w⁻¹) with hp | hn
  · have := ((weyl_exchange_condition τ).1 w i).2 ⟨IsRoot.smul (isRoot_single τ i) w⁻¹, hp⟩
    omega
  · exact hn

theorem exists_of_mem_bruhatCell_simple_mul
    {i : Fin τ.rank} {w : WeylGroup τ} {x : ModGL τ K}
    (hx : x ∈ bruhatCell τ K (simple τ i) * bruhatCell τ K w) :
    ∃ b ∈ borelGroup τ K, ∃ b' ∈ borelGroup τ K, ∃ c : K,
      x = b * (weylElt τ K i 1 * xUnit τ K i c) * canonicalRep (coxeterSystem τ) K w * b' := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.1 hy
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := mem_bruhatCell.1 hz
  obtain ⟨b', hb', c, hc⟩ := weylElt_mul_eq_of_mem_borelGroup i (mul_mem hb₂ hb₃)
  refine ⟨b₁ * b', mul_mem hb₁ hb', b₄, hb₄, c, ?_⟩
  rw [canonicalRep_simple]
  calc b₁ * weylElt τ K i 1 * b₂ * (b₃ * canonicalRep (coxeterSystem τ) K w * b₄) =
        b₁ * (weylElt τ K i 1 * (b₂ * b₃)) * canonicalRep (coxeterSystem τ) K w * b₄ := by
        group
    _ = _ := by rw [hc]; group

theorem mem_bruhatCell_simple_mul
    {i : Fin τ.rank} {w : WeylGroup τ} {b b₁ b₂ b' : ModGL τ K}
    (hb : b ∈ borelGroup τ K) (hb₁ : b₁ ∈ borelGroup τ K) (hb₂ : b₂ ∈ borelGroup τ K)
    (hb' : b' ∈ borelGroup τ K) :
    b * weylElt τ K i 1 * b₁ * (b₂ * canonicalRep (coxeterSystem τ) K w * b') ∈
      bruhatCell τ K (simple τ i) * bruhatCell τ K w :=
  Set.mem_mul.2 ⟨_, mem_bruhatCell.2 ⟨b, hb, b₁, hb₁, by rw [canonicalRep_simple]⟩, _,
    mem_bruhatCell.2 ⟨b₂, hb₂, b', hb', rfl⟩, rfl⟩

theorem bruhatCell_simple_mul_of_length_eq_add_one
    {i : Fin τ.rank} {w : WeylGroup τ}
    (h : (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1) :
    bruhatCell τ K (simple τ i) * bruhatCell τ K w = bruhatCell τ K (simple τ i * w) := by
  have hn : weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K (simple τ i * w) :=
    weylElt_mul_canonicalRep_of_length_eq h
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨b, hb, b', hb', c, rfl⟩ := exists_of_mem_bruhatCell_simple_mul hx
    obtain ⟨b'', hb'', hc⟩ := exists_mul_canonicalRep_eq (w := w) (isRoot_single τ i)
      (height_inv_smul_single_pos h) (Subgroup.subset_closure ⟨c, pinnedX_single τ K i c⟩)
    refine mem_bruhatCell.2 ⟨b, hb, b'' * b', mul_mem hb'' hb', ?_⟩
    calc b * canonicalRep (coxeterSystem τ) K (simple τ i * w) * (b'' * b') =
          b * (weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w) * (b'' * b') := by
          rw [hn]
      _ = b * weylElt τ K i 1 * (canonicalRep (coxeterSystem τ) K w * b'') * b' := by group
      _ = b * weylElt τ K i 1 * (xUnit τ K i c * canonicalRep (coxeterSystem τ) K w) * b' := by
          rw [hc]
      _ = _ := by group
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
    have e : b * weylElt τ K i 1 * 1 * (1 * canonicalRep (coxeterSystem τ) K w * b') =
        b * canonicalRep (coxeterSystem τ) K (simple τ i * w) * b' := by
      rw [← hn]
      group
    rw [← e]
    exact mem_bruhatCell_simple_mul hb (one_mem _) (one_mem _) hb'

theorem bruhatCell_simple_mul_of_length_eq_sub_one
    {i : Fin τ.rank} {w : WeylGroup τ}
    (h : (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w - 1) :
    bruhatCell τ K (simple τ i) * bruhatCell τ K w =
      bruhatCell τ K (simple τ i * w) ∪ bruhatCell τ K w := by
  have hlen : (coxeterSystem τ).length (simple τ i * w) + 1 = (coxeterSystem τ).length w := by
    rcases length_simple_mul_cases w i with h' | h'
    · omega
    · exact h'
  have hn : weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w =
      torusElt τ K i (-1) * canonicalRep (coxeterSystem τ) K (simple τ i * w) :=
    weylElt_mul_canonicalRep_of_length_add_one_eq hlen
  have hd : torusElt τ K i (-1) ∈ borelGroup τ K :=
    torus_le_borel (torusElt_mem_torusGroup i (-1))
  have hy : ∀ d : K, ∃ b'' ∈ borelGroup τ K, yUnit τ K i d * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K w * b'' := fun d =>
    exists_mul_canonicalRep_eq (isRoot_neg_single τ i) (height_inv_smul_neg_single_pos h)
      (Subgroup.subset_closure ⟨d, pinnedX_neg_single τ K i d⟩)
  have hrank := (simple_rank_one_bruhat_identity τ K).2 K i
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.union_subset (fun x hx => ?_) fun x hx => ?_)
  · obtain ⟨b, hb, b', hb', c, rfl⟩ := exists_of_mem_bruhatCell_simple_mul hx
    by_cases hc : c = 0
    ·
      left
      refine mem_bruhatCell.2 ⟨b * torusElt τ K i (-1), mul_mem hb hd, b', hb', ?_⟩
      calc b * torusElt τ K i (-1) * canonicalRep (coxeterSystem τ) K (simple τ i * w) * b' =
            b * (torusElt τ K i (-1) * canonicalRep (coxeterSystem τ) K (simple τ i * w)) * b' := by
            group
        _ = b * (weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w) * b' := by rw [hn]
        _ = _ := by rw [hc, xUnit_zero, mul_one]; group
    ·
      right
      obtain ⟨b₀, hb₀, h₀⟩ := hrank c hc
      obtain ⟨b'', hb'', h''⟩ := hy c⁻¹
      refine mem_bruhatCell.2 ⟨b * b₀, mul_mem hb hb₀, b'' * b', mul_mem hb'' hb', ?_⟩
      calc b * b₀ * canonicalRep (coxeterSystem τ) K w * (b'' * b') =
            b * b₀ * (canonicalRep (coxeterSystem τ) K w * b'') * b' := by group
        _ = b * b₀ * (yUnit τ K i c⁻¹ * canonicalRep (coxeterSystem τ) K w) * b' := by
            rw [h'']
        _ = b * (b₀ * yUnit τ K i c⁻¹) * canonicalRep (coxeterSystem τ) K w * b' := by group
        _ = _ := by rw [h₀]
  ·
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
    have e : b * (torusElt τ K i (-1))⁻¹ * weylElt τ K i 1 * 1 *
        (1 * canonicalRep (coxeterSystem τ) K w * b') =
          b * canonicalRep (coxeterSystem τ) K (simple τ i * w) * b' := by
      calc _ = b * (torusElt τ K i (-1))⁻¹ *
            (weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w) * b' := by group
        _ = _ := by rw [hn]; group
    rw [← e]
    exact mem_bruhatCell_simple_mul (mul_mem hb (inv_mem hd)) (one_mem _) (one_mem _) hb'
  ·
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
    obtain ⟨b₀, hb₀, h₀⟩ := hrank 1 one_ne_zero
    obtain ⟨b'', hb'', h''⟩ := hy 1⁻¹
    have key : weylElt τ K i 1 * xUnit τ K i 1 * canonicalRep (coxeterSystem τ) K w =
        b₀ * (canonicalRep (coxeterSystem τ) K w * b'') := by
      rw [h₀, mul_assoc, h'']
    have e : b * b₀⁻¹ * weylElt τ K i 1 * xUnit τ K i 1 *
        (1 * canonicalRep (coxeterSystem τ) K w * (b''⁻¹ * b')) =
          b * canonicalRep (coxeterSystem τ) K w * b' := by
      calc _ = b * b₀⁻¹ * (weylElt τ K i 1 * xUnit τ K i 1 * canonicalRep (coxeterSystem τ) K w) *
            b''⁻¹ * b' := by group
        _ = _ := by rw [key]; group
    rw [← e]
    exact mem_bruhatCell_simple_mul (mul_mem hb (inv_mem hb₀)) (xUnit_mem_borelGroup i 1)
      (one_mem _) (mul_mem (inv_mem hb'') hb')

theorem bruhatCell_subset_adjointGroup
    (w : WeylGroup τ) :
    bruhatCell τ K w ⊆ adjointGroup τ K := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hC⟩ := triangular_borel_structure.{0, 0} τ K
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
  exact mul_mem (mul_mem ((hC K).1 hb) (canonicalRep_mem_adjointGroup _ K w)) ((hC K).1 hb')

variable (τ K) in
theorem simple_bruhat_multiplication :
    (∀ (i : Fin τ.rank) (w : WeylGroup τ),
      (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1 →
        bruhatCell τ K (simple τ i) * bruhatCell τ K w = bruhatCell τ K (simple τ i * w)) ∧
    (∀ (i : Fin τ.rank) (w : WeylGroup τ),
      (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w - 1 →
        bruhatCell τ K (simple τ i) * bruhatCell τ K w =
          bruhatCell τ K (simple τ i * w) ∪ bruhatCell τ K w) ∧
    ∀ w : WeylGroup τ, bruhatCell τ K w ⊆ adjointGroup τ K :=
  ⟨fun _ _ h => bruhatCell_simple_mul_of_length_eq_add_one h,
    fun _ _ h => bruhatCell_simple_mul_of_length_eq_sub_one h, bruhatCell_subset_adjointGroup⟩

end CFSG.LieType.Chevalley
