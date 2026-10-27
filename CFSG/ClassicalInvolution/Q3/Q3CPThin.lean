module

public import CFSG.ClassicalInvolution.Q3.Q3CPLocC
public import CFSG.ClassicalInvolution.AschTight.Hall196Idx
public import CFSG.ClassicalInvolution.Q3.Q3CPNotThin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Asc77

section Generic

variable {G : Type} [Group G] [Finite G]

theorem modOddIn_eq_top_of_le_sup {X K₂ : Subgroup G} (hK₂X : K₂ ≤ X)
    (hthin : X ≤ K₂ ⊔ Balance.oddCoreIn X) : modOddIn X K₂ = ⊤ := by
  set ρ := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hρ
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have hx : (x : G) ∈ K₂ ⊔ Balance.oddCoreIn X := hthin x.2
  have hK₂P : K₂ ≤ ((modOddIn X K₂).comap ρ).map X.subtype :=
    fun k hk => ⟨⟨k, hK₂X hk⟩, ⟨⟨k, hK₂X hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩
  have hOP : Balance.oddCoreIn X ≤ ((modOddIn X K₂).comap ρ).map X.subtype := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    show ρ n ∈ modOddIn X K₂
    have hρn : ρ n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [hρn]
    exact Subgroup.one_mem _
  obtain ⟨x', hx', hxx'⟩ := sup_le hK₂P hOP hx
  have hx'x : x' = x := Subtype.ext hxx'
  rw [← hx'x]
  exact hx'

theorem isSylow2In_of_le_sup {X K₂ T : Subgroup G} (hK₂X : K₂ ≤ X)
    (hthin : X ≤ K₂ ⊔ Balance.oddCoreIn X) (hT : IsSylow2In T K₂) : IsSylow2In T X := by
  obtain ⟨V, hV⟩ := Uniform.exists_isSylow2In X
  have htop := modOddIn_eq_top_of_le_sup hK₂X hthin
  set ρ := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hρ
  have hV2 : IsPGroup 2 (V.subgroupOf X) := hV.2.1.comap_subtype
  have hT2 : IsPGroup 2 (T.subgroupOf X) := hT.2.1.comap_subtype
  have hinjV := Uniform.injective_mk_oddCore_of_isPGroup X hV2
  have hinjT := Uniform.injective_mk_oddCore_of_isPGroup X hT2
  have hsyl : IsSylow2In ((T.subgroupOf X).map ρ) ((K₂.subgroupOf X).map ρ) :=
    Disconnected.AschTight.Hall196.isSylow2In_map_hom ρ (hT.subgroupOf hK₂X)
  have hsyl' : IsSylow2In ((T.subgroupOf X).map ρ) (modOddIn X K₂) := hsyl
  rw [htop] at hsyl'
  have hcardV : Nat.card ((V.subgroupOf X).map ρ) = Nat.card V := by
    have h1 : (V.subgroupOf X).map ρ = (ρ.comp (V.subgroupOf X).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinjV).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV.1).toEquiv
  have hcardT : Nat.card ((T.subgroupOf X).map ρ) = Nat.card T := by
    have h1 : (T.subgroupOf X).map ρ = (ρ.comp (T.subgroupOf X).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinjT).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hT.1.trans hK₂X)).toEquiv
  have hle : Nat.card ((V.subgroupOf X).map ρ) ≤ Nat.card ((T.subgroupOf X).map ρ) :=
    hsyl'.natCard_le (hV2.map ρ) le_top
  rw [hcardV, hcardT] at hle
  exact hV.of_natCard_le hT.2.1 (hT.1.trans hK₂X) hle

theorem conjSub_nbrSpan3 {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G)
    (K : Subgroup G) : nbrSpan3 Ω (conjSub g K) = conjSub g (nbrSpan3 Ω K) := by
  apply le_antisymm
  · refine iSup₂_le fun J hJ => ?_
    have hJ' : conjSub g⁻¹ J ∈ nbrs3 Ω K := by
      refine ⟨hΩ g⁻¹ J hJ.1, fun h => hJ.2.1 ?_, ?_⟩
      · calc J = conjSub g (conjSub g⁻¹ J) := by rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
          _ = conjSub g K := by rw [h]
      · have := hJ.2.2.conjSub g⁻¹
        rwa [conjSub_inv_conjSub] at this
    have := conjSub_mono (n := g) (le_nbrSpan3 hJ')
    rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
  · rw [nbrSpan3, conjSub_iSup]
    refine iSup_le fun J => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hJ => ?_
    refine le_nbrSpan3 ⟨hΩ g J hJ.1, fun h => hJ.2.1 ?_, hJ.2.2.conjSub g⟩
    calc J = conjSub g⁻¹ (conjSub g J) := (conjSub_inv_conjSub g J).symm
      _ = conjSub g⁻¹ (conjSub g K) := by rw [h]
      _ = K := conjSub_inv_conjSub g K

theorem exists_conjSub_eq_of_mem_conjClass3 {K K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ conjClass3 K)
    (h₂ : K₂ ∈ conjClass3 K) : ∃ g : G, conjSub g K₁ = K₂ := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  exact ⟨b * a⁻¹, by rw [← conjSub_mul]; congr 1; group⟩

end Generic

section Thin

variable {G : Type} [Group G] [Finite G]

structure ThinData (Ω : Set (Subgroup G)) (K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop where
  edge : IsEdge3 Ω K₁ K₂ z₁ z₂
  thin : nbrSpan3 Ω K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 Ω K₁)
  congr : ∀ x ∈ nbrSpan3 Ω K₁, ∀ y ∈ nbrSpan3 Ω K₁, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 →
    x * y⁻¹ ∈ Balance.oddCoreIn (nbrSpan3 Ω K₁)

namespace ThinData

variable {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

theorem mem_nbrs (h : ThinData Ω K₁ K₂ z₁ z₂) : K₂ ∈ nbrs3 Ω K₁ :=
  ⟨h.edge.mem₂, fun hh => h.edge.ne (involution_unique3 h.edge.cls₁ (hh ▸ h.edge.cls₂)),
    h.edge.comm⟩

theorem le_nbrSpan (h : ThinData Ω K₁ K₂ z₁ z₂) : K₂ ≤ nbrSpan3 Ω K₁ := le_nbrSpan3 h.mem_nbrs

theorem z₂_mem (h : ThinData Ω K₁ K₂ z₁ z₂) : z₂ ∈ nbrSpan3 Ω K₁ :=
  h.le_nbrSpan h.edge.cls₂.mem

theorem isSylow2In (h : ThinData Ω K₁ K₂ z₁ z₂) {T : Subgroup G} (hT : IsSylow2In T K₂) :
    IsSylow2In T (nbrSpan3 Ω K₁) :=
  isSylow2In_of_le_sup h.le_nbrSpan h.thin hT

theorem eq_of_comm (h : ThinData Ω K₁ K₂ z₁ z₂) {x : G} (hx : x ∈ nbrSpan3 Ω K₁)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hc : x * z₂ = z₂ * x) : x = z₂ := by
  have hz2sq : z₂ * z₂ = 1 := h.edge.cls₂.isCentralInvolution.sq
  have h1 := h.congr x hx z₂ h.z₂_mem hx2 hz2sq hx1 h.edge.cls₂.ne_one
  have hz2inv : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz2sq
  rw [hz2inv] at h1
  have hsq : (x * z₂) * (x * z₂) = 1 := by
    calc (x * z₂) * (x * z₂) = x * (z₂ * x) * z₂ := by group
      _ = x * (x * z₂) * z₂ := by rw [← hc]
      _ = (x * x) * (z₂ * z₂) := by group
      _ = 1 := by rw [hx2, hz2sq, one_mul]
  have h2 : x * z₂ = 1 := eq_one_of_mem_of_odd_of_sq (Balance.odd_card_oddCoreIn _) h1 hsq
  calc x = x * z₂ * z₂⁻¹ := by group
    _ = z₂⁻¹ := by rw [h2, one_mul]
    _ = z₂ := hz2inv

end ThinData

end Thin

section Branch

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem mem_nbrSpan3_of_involution (hC : LocCommuteAt K z)
    {K₁ : Subgroup G} {z₁ : G} (hK₁ : K₁ ∈ conjClass3 K) (hz₁ : IsClassicalMember3 K₁ z₁)
    {M₀ : Subgroup G} {y : G} (hM₀ : M₀ ∈ conjClass3 K) (hy : IsClassicalMember3 M₀ y)
    (hne : y ≠ z₁) (hc : z₁ * y = y * z₁)
    (hP : ∃ P : Subgroup G, IsSylow2In P M₀ ∧ P ≤ Subgroup.centralizer ({z₁} : Set G)) :
    y ∈ nbrSpan3 (conjClass3 K) K₁ := by
  have hcomm : Commutes K₁ M₀ := hC K₁ M₀ z₁ y hK₁ hM₀ hz₁ hy hne.symm hc hP
  have hM₀ne : M₀ ≠ K₁ := fun h => hne (involution_unique3 hz₁ (h ▸ hy)).symm
  exact le_nbrSpan3 ⟨hM₀, hM₀ne, hcomm⟩ hy.mem


theorem thinData_of_thin (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂)
    (hthin : nbrSpan3 (conjClass3 K) K₁ ≤
      K₂ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁)) :
    ThinData (conjClass3 K) K₁ K₂ z₁ z₂ := by
  refine ⟨he, hthin, ?_⟩
  obtain ⟨ι, -, D, h⟩ := nbhd_shape3_free hz hBelow hB hC he
  rcases h with ⟨-, hT, -⟩ | ⟨hzX, -⟩ | ⟨hzX, -⟩
  · obtain ⟨i₀, hone, hk₀⟩ := hT
    obtain ⟨x, y, ζ, -, -, -, -, huniq⟩ := exists_quatPair_of_sl23 D hk₀
    have hrange : (D.hom i₀).range = ⊤ := range_eq_top_of_forall_eq D hone
    set X := nbrSpan3 (conjClass3 K) K₁ with hX
    intro a ha b hb ha2 hb2 ha1 hb1
    set ρ := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hρ
    have hsq : ∀ (x : G) (hx : x ∈ X), x * x = 1 → ρ ⟨x, hx⟩ * ρ ⟨x, hx⟩ = 1 := by
      intro x hx hx2
      rw [← map_mul]
      have : (⟨x, hx⟩ : ↥X) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
      rw [this, map_one]
    have hu : ∀ u : ↥X ⧸ classicalInvolutionOddCore ↥X, u * u = 1 → u = 1 ∨ u = ζ := fun u hu =>
      huniq u (by rw [hrange]; exact Subgroup.mem_top _) hu
    have ha' := (hu _ (hsq a ha ha2)).resolve_left (Q3Y.mk_ne_one_of_involution X ha ha2 ha1)
    have hb' := (hu _ (hsq b hb hb2)).resolve_left (Q3Y.mk_ne_one_of_involution X hb hb2 hb1)
    have hab : ρ ⟨a, ha⟩ = ρ ⟨b, hb⟩ := ha'.trans hb'.symm
    have hdiv : (⟨a, ha⟩ : ↥X) / ⟨b, hb⟩ ∈ classicalInvolutionOddCore ↥X :=
      QuotientGroup.eq_iff_div_mem.mp hab
    exact ⟨_, hdiv, by simp [div_eq_mul_inv]⟩
  · exact absurd hthin (not_thin_of_mem he hzX)
  · exact absurd hthin (not_thin_of_mem he hzX)

theorem thinData_symm (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (h : ThinData (conjClass3 K) K₁ K₂ z₁ z₂) :
    ThinData (conjClass3 K) K₂ K₁ z₂ z₁ := by
  have he := h.edge
  have hΩ : ConjInvariant (conjClass3 K) := (inClass3_conjugates hz).conjInvariant
  have hz1X : z₁ ∉ nbrSpan3 (conjClass3 K) K₁ := fun hzX => not_thin_of_mem he hzX h.thin
  have hz2X : z₂ ∉ nbrSpan3 (conjClass3 K) K₂ := by
    obtain ⟨g, hg⟩ := exists_conjSub_eq_of_mem_conjClass3 he.mem₁ he.mem₂
    have hz2 : z₂ = g * z₁ * g⁻¹ := by
      have := he.cls₁.conj g
      rw [hg] at this
      exact involution_unique3 he.cls₂ this
    intro hmem
    rw [← hg, conjSub_nbrSpan3 hΩ, mem_conjSub_iff] at hmem
    apply hz1X
    have : g⁻¹ * z₂ * g = z₁ := by rw [hz2]; group
    rwa [this] at hmem
  have hthin' : nbrSpan3 (conjClass3 K) K₂ ≤
      K₁ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₂) :=
    (nbhd_mem_or_thin_free hz hBelow hB hC he.symm).resolve_left hz2X
  exact thinData_of_thin hz hBelow hB hC he.symm hthin'

end Branch

end CFSG.ClassicalInvolution.Q3.Q3CP
