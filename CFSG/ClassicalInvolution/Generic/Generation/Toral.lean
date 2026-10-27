module

public import CFSG.ClassicalInvolution.Generic.Generation.Defs

public section

namespace CFSG.ClassicalInvolution.Generic

variable {F : Type*} [Field F] {G : Type*} [Group G]

theorem mul_comm_of_sq_eq_one {E : Subgroup G} (hE : ∀ x ∈ E, x * x = 1) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := by
  have h1 : (x * y) * (x * y) = 1 := hE _ (E.mul_mem hx hy)
  have h2 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hE x hx),
    inv_eq_of_mul_eq_one_right (hE y hy)] at h2
  exact h2.symm

theorem exists_two_ne_one_of_three_le_card (Q : Subgroup G) [Finite Q] (h : 3 ≤ Nat.card Q) :
    ∃ v ∈ Q, ∃ w ∈ Q, v ≠ 1 ∧ w ≠ 1 ∧ v ≠ w := by
  by_contra hne
  push Not at hne
  by_cases hQ : Q = ⊥
  · rw [hQ, Subgroup.card_bot] at h
    omega
  obtain ⟨⟨v, hvQ⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ
  have hv1' : v ≠ 1 := fun h' => hv1 (Subtype.ext h')
  have hsub : (Q : Set G) ⊆ {1, v} := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hne x hx v hvQ hx1 hv1')
  have h2 : (Q : Set G).ncard ≤ ({1, v} : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({1, v} : Set G).ncard ≤ 2 := by
    refine (Set.ncard_insert_le 1 {v}).trans ?_
    rw [Set.ncard_singleton]
  have h4 : Nat.card Q = (Q : Set G).ncard := Nat.card_coe_set_eq (Q : Set G)
  omega

@[expose] def AxisIndexLeTwo (E K : Subgroup G) : Prop :=
  ∃ a ∈ E, ∀ x ∈ E, x ∈ axisSub E K ∨ x * a ∈ axisSub E K

theorem InSigma.axisIndexLeTwo {E K : Subgroup G} (hK : InSigma F E K) : AxisIndexLeTwo E K := by
  obtain ⟨a, ha, -, h⟩ := hK.exists_split
  exact ⟨a, ha, h⟩

theorem exists_mem_axis_of_axisIndexLeTwo {E K V : Subgroup G} (hE : ∀ x ∈ E, x * x = 1)
    (hV : V ≤ E) (hK : AxisIndexLeTwo E K) {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) (hvw : v ≠ w) : ∃ u ∈ V, u ≠ 1 ∧ u ∈ axisSub E K := by
  obtain ⟨a, ha, h⟩ := hK
  by_cases hva : v ∈ axisSub E K
  · exact ⟨v, hv, hv1, hva⟩
  by_cases hwa : w ∈ axisSub E K
  · exact ⟨w, hw, hw1, hwa⟩
  have hv' : v * a ∈ axisSub E K := (h v (hV hv)).resolve_left hva
  have hw' : w * a ∈ axisSub E K := (h w (hV hw)).resolve_left hwa
  refine ⟨v * w, V.mul_mem hv hw, ?_, ?_⟩
  · intro h1
    apply hvw
    exact (eq_inv_of_mul_eq_one_left h1).trans (inv_eq_of_mul_eq_one_right (hE w (hV hw)))
  · have e : (v * a) * (w * a) = v * w := by
      calc (v * a) * (w * a) = v * (a * w) * a := by group
        _ = v * (w * a) * a := by rw [mul_comm_of_sq_eq_one hE ha (hV hw)]
        _ = v * w * (a * a) := by group
        _ = v * w := by rw [hE a ha, mul_one]
    rw [← e]
    exact (axisSub E K).mul_mem hv' hw'

namespace ToralFrame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem le_centSpan_of_mem_axis (Fr : ToralFrame F Ω E S) {K V : Subgroup G} (hK : K ∈ S) {u : G}
    (hu : u ∈ V) (hu1 : u ≠ 1) (hax : u ∈ axisSub E K) : K ≤ centSpan Ω V :=
  le_centSpan_of_commute (Fr.subset hK) hu hu1 (mem_axisSub_iff.mp hax).2

theorem member_le_centSpan (Fr : ToralFrame F Ω E S) {K V : Subgroup G} (hK : K ∈ S) (hV : V ≤ E)
    {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v ≠ w) :
    K ≤ centSpan Ω V := by
  obtain ⟨u, hu, hu1, hax⟩ := exists_mem_axis_of_axisIndexLeTwo Fr.elem hV
    (Fr.inSigma hK).axisIndexLeTwo hv hw hv1 hw1 hvw
  exact Fr.le_centSpan_of_mem_axis hK hu hu1 hax

theorem le_centLayer_of_isUniqueInvolution (Fr : ToralFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S)
    {z : G} (hz : IsUniqueInvolution K z) : K ≤ centLayer Ω z := by
  have := Fr.finite
  exact le_centLayer (mem_centMembers_iff_commute.mpr ⟨Fr.subset hK,
    (mem_axisSub_iff.mp ((Fr.inSigma hK).unique_involution_mem_axis Fr.odd hz)).2⟩)

theorem member_le_centSpan_E (Fr : ToralFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S) :
    K ≤ centSpan Ω E := by
  obtain ⟨z, hz⟩ := Fr.exists_isUniqueInvolution hK
  exact (Fr.le_centLayer_of_isUniqueInvolution hK hz).trans
    (le_centSpan (Fr.mem_of_isUniqueInvolution hK hz) hz.ne_one)

theorem centSpan_ne_bot (Fr : ToralFrame F Ω E S) : centSpan Ω E ≠ ⊥ := by
  obtain ⟨K, hK, -⟩ := Fr.exists_ne
  obtain ⟨z, hz⟩ := Fr.exists_isUniqueInvolution hK
  intro h
  have := Fr.member_le_centSpan_E hK hz.mem
  rw [h, Subgroup.mem_bot] at this
  exact hz.ne_one this

end ToralFrame

variable (Ω : Set (Subgroup G)) (E : Subgroup G)

@[expose] def ToralIndependence : Prop :=
  ∀ V : Subgroup G, V ≤ E → ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → v ≠ w →
    ∀ x ∈ E, x ≠ 1 → centLayer Ω x ≤ centSpan Ω V

@[expose] def KGGeneration : Prop :=
  ∀ x ∈ E, x ≠ 1 →
    centLayer Ω x ≤ ⨆ K ∈ {K | K ∈ centMembers Ω x ∧ AxisIndexLeTwo E K}, K

@[expose] def FrameGeneration (S : Set (Subgroup G)) : Prop :=
  ∀ x ∈ E, x ≠ 1 →
    centLayer Ω x ≤ ⨆ K ∈ {K | K ∈ S ∧ K ≤ Subgroup.centralizer ({x} : Set G)}, K

variable {Ω E} {S : Set (Subgroup G)}

theorem FrameGeneration.kgGeneration (Fr : ToralFrame F Ω E S) (h : FrameGeneration Ω E S) :
    KGGeneration Ω E := fun x hx hx1 =>
  (h x hx hx1).trans <| iSup₂_le fun K hK =>
    le_iSup₂_of_le K ⟨⟨Fr.subset hK.1, hK.2⟩, (Fr.inSigma hK.1).axisIndexLeTwo⟩ le_rfl

theorem KGGeneration.toralIndependence (hE : ∀ x ∈ E, x * x = 1) (hKG : KGGeneration Ω E) :
    ToralIndependence Ω E := fun V hV v hv w hw hv1 hw1 hvw x hx hx1 =>
  (hKG x hx hx1).trans <| iSup₂_le fun K hK => by
    obtain ⟨u, hu, hu1, hax⟩ :=
      exists_mem_axis_of_axisIndexLeTwo hE hV hK.2 hv hw hv1 hw1 hvw
    exact le_centSpan_of_commute hK.1.1 hu hu1 (mem_axisSub_iff.mp hax).2

theorem ToralIndependence.centSpan_eq (h : ToralIndependence Ω E) {V : Subgroup G} (hV : V ≤ E)
    {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v ≠ w) :
    centSpan Ω V = centSpan Ω E :=
  le_antisymm (centSpan_mono hV) <|
    centSpan_le fun _ hx hx1 => h V hV v hv w hw hv1 hw1 hvw _ hx hx1

theorem ToralIndependence.normalizer_le (h : ToralIndependence Ω E) (hΩ : ConjInvariant Ω)
    {V : Subgroup G} (hV : V ≤ E) {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) (hvw : v ≠ w) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (centSpan Ω E : Set G) := by
  have := normalizer_le_normalizer_centSpan hΩ V
  rwa [h.centSpan_eq hV hv hw hv1 hw1 hvw] at this

theorem centSpan_eq_iSup_frame (Fr : ToralFrame F Ω E S) (h : FrameGeneration Ω E S) :
    centSpan Ω E = ⨆ K ∈ S, K :=
  le_antisymm
    (centSpan_le fun x hx hx1 => (h x hx hx1).trans <|
      iSup₂_le fun K hK => le_iSup₂_of_le K hK.1 le_rfl)
    (iSup₂_le fun _ hK => Fr.member_le_centSpan_E hK)

end CFSG.ClassicalInvolution.Generic
