module

public import CFSG.LieType.Chevalley.E6SignedGraphBruhatData
public import CFSG.LieType.Chevalley.E6SignedGraphPerfect

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise commutatorElement

variable (K : Type) [Field K]

@[expose] def torusPart
    : Subgroup (ModGL TwistTag.E6.tag K) :=
  rootGenerated K ⊓ torusGroup TwistTag.E6.tag K

@[expose] def borelPart
    : Subgroup (ModGL TwistTag.E6.tag K) :=
  torusPart K ⊔ posFixed K

@[expose] def simpleLift
    (v : Fin 4 → WeylGroup TwistTag.E6.tag)
    (a : Fin 4 → Fin TwistTag.E6.foldedTag.rank) (i : Fin 4) : ModGL TwistTag.E6.tag K :=
  orbitSL2 K (v i) (a i) (nSL 1)

@[expose] def liftGroup
    (v : Fin 4 → WeylGroup TwistTag.E6.tag)
    (a : Fin 4 → Fin TwistTag.E6.foldedTag.rank) : Subgroup (ModGL TwistTag.E6.tag K) :=
  torusPart K ⊔ Subgroup.closure (Set.range (simpleLift K v a))

@[expose] def signedCell
    (x : ModGL TwistTag.E6.tag K) : Set (ModGL TwistTag.E6.tag K) :=
  (borelPart K : Set (ModGL TwistTag.E6.tag K)) * {x} *
    (borelPart K : Set (ModGL TwistTag.E6.tag K))

variable {K}

theorem liftGroup_le_monomialSubgroup
    (v : Fin 4 → WeylGroup TwistTag.E6.tag)
    (a : Fin 4 → Fin TwistTag.E6.foldedTag.rank) :
    liftGroup K v a ≤ monomialSubgroup TwistTag.E6.tag K :=
  sup_le (fun _ hx => torusGroup_le_monomialSubgroup (Subgroup.mem_inf.1 hx).2)
    ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun i =>
      orbitSL2_nSL_mem_monomialSubgroup (v i) (a i) 1))

variable (K) in
@[expose] def liftWeylHom
    (v : Fin 4 → WeylGroup TwistTag.E6.tag)
    (a : Fin 4 → Fin TwistTag.E6.foldedTag.rank) : liftGroup K v a →* WeylGroup TwistTag.E6.tag :=
  (weylQuotientHom TwistTag.E6.tag K).comp (Subgroup.inclusion (liftGroup_le_monomialSubgroup v a))

theorem rootGenerated_le_fixedGroup
    : rootGenerated K ≤ fixedGroup K :=
  sup_le inf_le_right inf_le_right

theorem torusPart_le_torusFixed
    : torusPart K ≤ torusFixed K := fun _ hx =>
  Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, rootGenerated_le_fixedGroup
    (Subgroup.mem_inf.1 hx).1⟩

theorem inversionFixed_le_posFixed
    (w : WeylGroup TwistTag.E6.tag) :
    inversionFixed K w ≤ posFixed K :=
  inf_le_inf_right _ (rootSpan_le_posUnipotent fun _ h => inversionSet_pos (w := w) h)

theorem borelPart_le_rootGenerated
    : borelPart K ≤ rootGenerated K :=
  sup_le inf_le_left le_sup_left

theorem borelPart_le_borelGroup
    : borelPart K ≤ borelGroup TwistTag.E6.tag K :=
  sup_le (fun _ hx => torusGroup_le_borelGroup (Subgroup.mem_inf.1 hx).2)
    (fun _ hx => Subgroup.mem_sup_right (Subgroup.mem_inf.1 hx).1)

theorem torusPart_le_normalizer_posFixed
    :
    torusPart K ≤ Subgroup.normalizer (posFixed K : Set (ModGL TwistTag.E6.tag K)) :=
  fun _ hx => torusFixed_le_normalizer_posFixed (torusPart_le_torusFixed hx)

theorem coe_borelPart
    : (borelPart K : Set (ModGL TwistTag.E6.tag K)) =
    (torusPart K : Set (ModGL TwistTag.E6.tag K)) * (posFixed K : Set (ModGL TwistTag.E6.tag K)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _ torusPart_le_normalizer_posFixed

theorem posFixed_subgroupOf_borelPart_normal :
    ((posFixed K).subgroupOf (borelPart K)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
    (sup_le torusPart_le_normalizer_posFixed Subgroup.le_normalizer)

theorem torusPart_inf_posFixed
    : torusPart K ⊓ posFixed K = ⊥ :=
  eq_bot_iff.2 fun _ hx => by
    have h := Subgroup.mem_inf.2 ⟨torusPart_le_torusFixed (Subgroup.mem_inf.1 hx).1,
      (Subgroup.mem_inf.1 hx).2⟩
    rwa [torusFixed_inf_posFixed] at h

theorem exists_mem_bruhatCell
    (hK : ringChar K ≠ 2) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ fixedGroup K) : ∃ w ∈ weylGroup, g ∈ bruhatCell TwistTag.E6.tag K w := by
  have hgC : g ∈ (adjointGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) :=
    (mem_fixedGroup.1 hg).1
  rw [adjointGroup_eq_iUnion_bruhatCell] at hgC
  obtain ⟨w, hgw⟩ := Set.mem_iUnion.1 hgC
  exact ⟨w, mem_weylGroup_of_mem_fixedGroup hK hg hgw, hgw⟩

theorem coe_fixedGroup
    (hK : ringChar K ≠ 2) :
    (fixedGroup K : Set (ModGL TwistTag.E6.tag K)) =
      (torusFixed K : Set (ModGL TwistTag.E6.tag K)) *
        (rootGenerated K : Set (ModGL TwistTag.E6.tag K)) := by
  refine Set.Subset.antisymm (fun g hg => ?_) ?_
  · obtain ⟨w, hw, hgw⟩ := exists_mem_bruhatCell hK hg
    obtain ⟨z, hzS, hzN, hzΓ, hzw⟩ := exists_lift_of_mem_weylGroup (K := K) hw
    obtain ⟨⟨u, h, v⟩, ⟨hu, hh, hv⟩, rfl⟩ :=
      (fixed_cell_bijOn (weylGroup_le_parityGroup hw).1 hzΓ hzN hzw).2.2 ⟨hg, hgw⟩
    have huS : h⁻¹ * u * h ∈ rootGenerated K := by
      have h' := (Subgroup.mem_normalizer_iff.1
        (torusFixed_le_normalizer_rootGenerated (inv_mem hh)) u).1
        (le_sup_left (a := posFixed K) (b := negFixed K) hu)
      rwa [inv_inv] at h'
    refine ⟨h, hh, h⁻¹ * u * h * z * v, mul_mem (mul_mem huS hzS)
      (le_sup_left (a := posFixed K) (b := negFixed K) (inversionFixed_le_posFixed w hv)), ?_⟩
    show h * (h⁻¹ * u * h * z * v) = u * h * z * v
    group
  · rintro _ ⟨h, hh, s, hs, rfl⟩
    exact mul_mem (Subgroup.mem_inf.1 hh).2 (rootGenerated_le_fixedGroup hs)

theorem fixedGroup_le_normalizer
    (hK : ringChar K ≠ 2) :
    fixedGroup K ≤ Subgroup.normalizer (rootGenerated K : Set (ModGL TwistTag.E6.tag K)) := by
  intro g hg
  have hg' : g ∈ (fixedGroup K : Set (ModGL TwistTag.E6.tag K)) := hg
  rw [coe_fixedGroup hK] at hg'
  obtain ⟨h, hh, s, hs, rfl⟩ := hg'
  exact mul_mem (torusFixed_le_normalizer_rootGenerated hh) (Subgroup.le_normalizer hs)

theorem commutator_fixedGroup
    (hK : ringChar K ≠ 2) :
    ⁅fixedGroup K, fixedGroup K⁆ = rootGenerated K := by
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_) ?_
  · have h₁ : g₁ ∈ (fixedGroup K : Set (ModGL TwistTag.E6.tag K)) := hg₁
    have h₂ : g₂ ∈ (fixedGroup K : Set (ModGL TwistTag.E6.tag K)) := hg₂
    rw [coe_fixedGroup hK] at h₁ h₂
    obtain ⟨a, ha, b, hb, rfl⟩ := h₁
    obtain ⟨c, hc, d, hd, rfl⟩ := h₂
    have hNa := torusFixed_le_normalizer_rootGenerated ha
    have hNc := torusFixed_le_normalizer_rootGenerated hc
    have e : ⁅a * b, c * d⁆ = (a * b * a⁻¹) * ((a * c) * (d * b⁻¹) * (a * c)⁻¹) *
        (a * c * a⁻¹ * c⁻¹) * (c * d⁻¹ * c⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e, show a * c * a⁻¹ * c⁻¹ = 1 by rw [torusFixed_mul_comm ha hc]; group, mul_one]
    refine mul_mem (mul_mem ((Subgroup.mem_normalizer_iff.1 hNa b).1 hb)
      ((Subgroup.mem_normalizer_iff.1 (mul_mem hNa hNc) _).1 (mul_mem hd (inv_mem hb))))
      ((Subgroup.mem_normalizer_iff.1 hNc _).1 (inv_mem hd))
  · calc rootGenerated K = ⁅rootGenerated K, rootGenerated K⁆ :=
          (commutator_rootGenerated hK).symm
      _ ≤ ⁅fixedGroup K, fixedGroup K⁆ :=
          Subgroup.commutator_mono rootGenerated_le_fixedGroup rootGenerated_le_fixedGroup

theorem mem_signedCell
    {x y : ModGL TwistTag.E6.tag K} :
    y ∈ signedCell K x ↔ ∃ b ∈ borelPart K, ∃ b' ∈ borelPart K, b * x * b' = y := by
  simp only [signedCell, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩

theorem eq_torus_mul_canonicalRep
    {d : ModGL TwistTag.E6.tag K}
    (hdN : d ∈ monomialSubgroup TwistTag.E6.tag K) {w : WeylGroup TwistTag.E6.tag}
    (hdw : MapsRootLines d w) :
    ∃ k ∈ torusGroup TwistTag.E6.tag K,
      d = k * canonicalRep (coxeterSystem TwistTag.E6.tag) K w := by
  obtain ⟨w', k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hdN
  have hw' : w' = w := (mapsRootLines_mul_canonicalRep hk w').unique hdw
  subst hw'
  exact ⟨k, hk, rfl⟩

theorem signedCell_subset_bruhatCell
    {d : ModGL TwistTag.E6.tag K}
    (hdN : d ∈ monomialSubgroup TwistTag.E6.tag K) {w : WeylGroup TwistTag.E6.tag}
    (hdw : MapsRootLines d w) : signedCell K d ⊆ bruhatCell TwistTag.E6.tag K w := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_signedCell.1 hx
  obtain ⟨k, hk, rfl⟩ := eq_torus_mul_canonicalRep hdN hdw
  exact mem_bruhatCell.2 ⟨b * k, mul_mem (borelPart_le_borelGroup hb)
    (torusGroup_le_borelGroup hk), b', borelPart_le_borelGroup hb', by group⟩

theorem signedCell_subset_rootGenerated
    {d : ModGL TwistTag.E6.tag K}
    (hdS : d ∈ rootGenerated K) :
    signedCell K d ⊆ (rootGenerated K : Set (ModGL TwistTag.E6.tag K)) := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_signedCell.1 hx
  exact mul_mem (mul_mem (borelPart_le_rootGenerated hb) hdS) (borelPart_le_rootGenerated hb')

theorem mem_torusPart_of_factor
    {u h d v : ModGL TwistTag.E6.tag K} (hu : u ∈ posFixed K)
    (hh : h ∈ torusFixed K) (hdS : d ∈ rootGenerated K) {w : WeylGroup TwistTag.E6.tag}
    (hv : v ∈ inversionFixed K w) (hx : u * h * d * v ∈ rootGenerated K) : h ∈ torusPart K := by
  have e : h = u⁻¹ * (u * h * d * v) * v⁻¹ * d⁻¹ := by group
  have hhS : h ∈ rootGenerated K := by
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem (le_sup_left (a := posFixed K) (b := negFixed K) hu))
      hx) (inv_mem (le_sup_left (a := posFixed K) (b := negFixed K)
        (inversionFixed_le_posFixed w hv)))) (inv_mem hdS)
  exact Subgroup.mem_inf.2 ⟨hhS, (Subgroup.mem_inf.1 hh).1⟩

theorem signed_cell_bijOn
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup)
    {d : ModGL TwistTag.E6.tag K} (hdS : d ∈ rootGenerated K)
    (hdN : d ∈ monomialSubgroup TwistTag.E6.tag K) (hdw : MapsRootLines d w) :
    Set.BijOn (fun p : ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K ×
        ModGL TwistTag.E6.tag K => p.1 * p.2.1 * d * p.2.2)
      ((posFixed K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
        (torusPart K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
          (inversionFixed K w : Set (ModGL TwistTag.E6.tag K)))
      (signedCell K d) := by
  have hΓ := fixed_cell_bijOn (weylGroup_le_parityGroup hw).1 (rootGenerated_le_fixedGroup hdS)
    hdN hdw
  refine ⟨fun p hp => ?_, fun p hp q hq hpq => hΓ.2.1 ⟨hp.1, torusPart_le_torusFixed hp.2.1,
    hp.2.2⟩ ⟨hq.1, torusPart_le_torusFixed hq.2.1, hq.2.2⟩ hpq, fun x hx => ?_⟩
  · obtain ⟨hu, hh, hv⟩ := hp
    exact mem_signedCell.2 ⟨p.1 * p.2.1, mul_mem (le_sup_right (a := torusPart K) hu)
      (le_sup_left (b := posFixed K) hh), p.2.2,
      le_sup_right (a := torusPart K) (inversionFixed_le_posFixed w hv), rfl⟩
  · have hxS := signedCell_subset_rootGenerated hdS hx
    obtain ⟨⟨u, h, v⟩, ⟨hu, hh, hv⟩, rfl⟩ :=
      hΓ.2.2 ⟨rootGenerated_le_fixedGroup hxS, signedCell_subset_bruhatCell hdN hdw hx⟩
    exact ⟨(u, h, v), ⟨hu, mem_torusPart_of_factor hu hh hdS hv hxS, hv⟩, rfl⟩

theorem coe_rootGenerated_eq_iUnion
    (hK : ringChar K ≠ 2)
    {dot : WeylGroup TwistTag.E6.tag → ModGL TwistTag.E6.tag K}
    (hdot : ∀ w ∈ weylGroup, dot w ∈ rootGenerated K ∧
      dot w ∈ monomialSubgroup TwistTag.E6.tag K ∧ MapsRootLines (dot w) w) :
    (rootGenerated K : Set (ModGL TwistTag.E6.tag K)) = ⋃ w ∈ weylGroup, signedCell K (dot w) := by
  refine Set.Subset.antisymm (fun x hx => ?_)
    (Set.iUnion₂_subset fun w hw => signedCell_subset_rootGenerated (hdot w hw).1)
  have hxΓ := rootGenerated_le_fixedGroup hx
  obtain ⟨w, hw, hxw⟩ := exists_mem_bruhatCell hK hxΓ
  obtain ⟨hdS, hdN, hdw⟩ := hdot w hw
  obtain ⟨⟨u, h, v⟩, ⟨hu, hh, hv⟩, rfl⟩ := (fixed_cell_bijOn (weylGroup_le_parityGroup hw).1
    (rootGenerated_le_fixedGroup hdS) hdN hdw).2.2 ⟨hxΓ, hxw⟩
  exact Set.mem_iUnion₂.2 ⟨w, hw, (signed_cell_bijOn hw hdS hdN hdw).1
    ⟨hu, mem_torusPart_of_factor hu hh hdS hv hx, hv⟩⟩

section Lifts

variable
    {v : Fin 4 → WeylGroup TwistTag.E6.tag} {a : Fin 4 → Fin TwistTag.E6.foldedTag.rank}
  (hva : ∀ i, v i ∈ relWeylTwist TwistTag.E6 ∧ orbitImage (v i) (a i) = simpleOrbit i)
include hva

theorem simpleLift_mem
    (i : Fin 4) :
    simpleLift K v a i ∈ rootGenerated K ∧ simpleLift K v a i ∈ fixedGroup K ∧
      MapsRootLines (simpleLift K v a i) (gen i) := by
  obtain ⟨hw, he⟩ := hva i
  have hO : orbitImage (v i) (a i) ∈ orbits := he ▸ (simpleOrbit_spec i).1
  refine ⟨range_orbitSL2_le_rootGenerated hw hO ⟨_, rfl⟩,
    orbitSL2_mem_fixedGroup hw (orbitSign_eq_one_of_mem_orbits hO) _, ?_⟩
  have h := mapsRootLines_orbitSL2_nSL (K := K) (v i) (a i) 1
  rw [he] at h
  exact h

theorem liftGroup_le_rootGenerated
    : liftGroup K v a ≤ rootGenerated K :=
  sup_le inf_le_left ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun i =>
    (simpleLift_mem hva i).1))

omit hva in
theorem liftGroup_eq_closure :
    liftGroup K v a = Subgroup.closure ((torusPart K : Set (ModGL TwistTag.E6.tag K)) ∪
      Set.range (simpleLift K v a)) := by
  rw [liftGroup, Subgroup.closure_union, Subgroup.closure_eq]

theorem exists_mapsRootLines_of_mem_liftGroup
    {n : ModGL TwistTag.E6.tag K}
    (hn : n ∈ liftGroup K v a) : ∃ w ∈ weylGroup, MapsRootLines n w := by
  rw [liftGroup_eq_closure] at hn
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨i, rfl⟩
    · exact ⟨1, one_mem _, mapsRootLines_of_mem_torusGroup (Subgroup.mem_inf.1 hx).2⟩
    · exact ⟨gen i, Subgroup.subset_closure ⟨i, rfl⟩, (simpleLift_mem hva i).2.2⟩
  | one => exact ⟨1, one_mem _, mapsRootLines_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, hw, hxw⟩ := hx
    obtain ⟨w', hw', hyw⟩ := hy
    exact ⟨w * w', mul_mem hw hw', hxw.mul hyw⟩
  | inv x _ hx =>
    obtain ⟨w, hw, hxw⟩ := hx
    exact ⟨w⁻¹, inv_mem hw, hxw.inv⟩

theorem exists_mem_liftGroup_of_mem_weylGroup
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ weylGroup) : ∃ n ∈ liftGroup K v a, MapsRootLines n w := by
  have hw' : w ∈ Subgroup.closure (Set.range gen) := hw
  clear hw
  induction hw' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨simpleLift K v a i, le_sup_right (a := torusPart K)
      (Subgroup.subset_closure ⟨i, rfl⟩), (simpleLift_mem hva i).2.2⟩
  | one => exact ⟨1, one_mem _, mapsRootLines_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨n', hn', hny⟩ := hy
    exact ⟨n * n', mul_mem hn hn', hnx.mul hny⟩
  | inv x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    exact ⟨n⁻¹, inv_mem hn, hnx.inv⟩

theorem mem_torusPart_of_mapsRootLines_one
    {n : ModGL TwistTag.E6.tag K}
    (hn : n ∈ liftGroup K v a) (h1 : MapsRootLines n 1) : n ∈ torusPart K := by
  obtain ⟨k, hk, rfl⟩ := eq_torus_mul_canonicalRep (liftGroup_le_monomialSubgroup v a hn) h1
  rw [canonicalRep_one, mul_one] at hn ⊢
  exact Subgroup.mem_inf.2 ⟨liftGroup_le_rootGenerated hva hn, hk⟩

omit hva in
theorem liftWeylHom_eq_iff
    {n : liftGroup K v a} {w : WeylGroup TwistTag.E6.tag} :
    liftWeylHom K v a n = w ↔ MapsRootLines (n : ModGL TwistTag.E6.tag K) w := by
  have h := mapsRootLines_weylQuotientHom (τ := TwistTag.E6.tag) (R := K)
    (Subgroup.inclusion (liftGroup_le_monomialSubgroup v a) n)
  constructor
  · rintro rfl
    exact h
  · intro hw
    exact weylQuotientHom_eq hw

theorem range_liftWeylHom
    : (liftWeylHom K v a).range = weylGroup := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨w', hw', hnw⟩ := exists_mapsRootLines_of_mem_liftGroup hva n.2
    rw [liftWeylHom_eq_iff.2 hnw]
    exact hw'
  · intro hw
    obtain ⟨n, hn, hnw⟩ := exists_mem_liftGroup_of_mem_weylGroup (K := K) hva hw
    exact ⟨⟨n, hn⟩, liftWeylHom_eq_iff.2 hnw⟩

theorem ker_liftWeylHom :
    (liftWeylHom K v a).ker = (torusPart K).subgroupOf (liftGroup K v a) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, liftWeylHom_eq_iff]
  exact ⟨mem_torusPart_of_mapsRootLines_one hva n.2,
    fun h => mapsRootLines_of_mem_torusGroup (Subgroup.mem_inf.1 h).2⟩

theorem borelPart_inf_liftGroup
    : borelPart K ⊓ liftGroup K v a = torusPart K := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left le_sup_left)
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.1 hx
  have hxH : x ∈ torusGroup TwistTag.E6.tag K := by
    rw [← (borel_weyl_intersection TwistTag.E6.tag K).1]
    exact Subgroup.mem_inf.2 ⟨borelPart_le_borelGroup hxB, liftGroup_le_monomialSubgroup v a hxN⟩
  exact Subgroup.mem_inf.2 ⟨liftGroup_le_rootGenerated hva hxN, hxH⟩

end Lifts

end CFSG.LieType.Chevalley.E6SignedGraph

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  E6SignedGraph
open scoped Pointwise

theorem E6_signed_graph_centralizer_Bruhat_structure
    (K : Type) [Field K]
    (hK : ringChar K ≠ 2) :
    (fixedGroup K : Set (ModGL TwistTag.E6.tag K)) =
        (torusFixed K : Set (ModGL TwistTag.E6.tag K)) *
          (rootGenerated K : Set (ModGL TwistTag.E6.tag K)) ∧
    rootGenerated K ≤ fixedGroup K ∧ ((rootGenerated K).subgroupOf (fixedGroup K)).Normal ∧
    ⁅fixedGroup K, fixedGroup K⁆ = rootGenerated K ∧
    posFixed K ≤ borelPart K ∧ ((posFixed K).subgroupOf (borelPart K)).Normal ∧
    Group.IsNilpotent (posFixed K) ∧ torusPart K ≤ borelPart K ∧
    (∀ g ∈ torusPart K, ∀ g' ∈ torusPart K, g * g' = g' * g) ∧
    torusPart K ⊓ posFixed K = ⊥ ∧
    (borelPart K : Set (ModGL TwistTag.E6.tag K)) =
      (torusPart K : Set (ModGL TwistTag.E6.tag K)) *
        (posFixed K : Set (ModGL TwistTag.E6.tag K)) ∧
    (∀ w, ((fixedGroup K : Set (ModGL TwistTag.E6.tag K)) ∩
      bruhatCell TwistTag.E6.tag K w).Nonempty → w ∈ weylGroup) ∧
    ∀ (v : Fin 4 → WeylGroup TwistTag.E6.tag) (a : Fin 4 → Fin TwistTag.E6.foldedTag.rank),
      (∀ i, v i ∈ relWeylTwist TwistTag.E6 ∧ orbitImage (v i) (a i) = simpleOrbit i) →
      liftGroup K v a ≤ monomialSubgroup TwistTag.E6.tag K ∧ torusPart K ≤ liftGroup K v a ∧
      (liftWeylHom K v a).range = weylGroup ∧
      (liftWeylHom K v a).ker = (torusPart K).subgroupOf (liftGroup K v a) ∧
      borelPart K ⊓ liftGroup K v a = torusPart K ∧
      ∀ dot : WeylGroup TwistTag.E6.tag → ModGL TwistTag.E6.tag K,
        (∀ w ∈ weylGroup, ∃ hd : dot w ∈ liftGroup K v a, liftWeylHom K v a ⟨dot w, hd⟩ = w) →
        (rootGenerated K : Set (ModGL TwistTag.E6.tag K)) =
          ⋃ w ∈ weylGroup, signedCell K (dot w) ∧
        (∀ w ∈ weylGroup, ∀ w' ∈ weylGroup, w ≠ w' →
          Disjoint (signedCell K (dot w)) (signedCell K (dot w'))) ∧
        ∀ w ∈ weylGroup,
          Set.BijOn (fun p : ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K ×
              ModGL TwistTag.E6.tag K => p.1 * p.2.1 * dot w * p.2.2)
            ((posFixed K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
              (torusFixed K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
                (inversionFixed K w : Set (ModGL TwistTag.E6.tag K)))
            ((fixedGroup K : Set (ModGL TwistTag.E6.tag K)) ∩ bruhatCell TwistTag.E6.tag K w) ∧
          Set.BijOn (fun p : ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K ×
              ModGL TwistTag.E6.tag K => p.1 * p.2.1 * dot w * p.2.2)
            ((posFixed K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
              (torusPart K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
                (inversionFixed K w : Set (ModGL TwistTag.E6.tag K)))
            (signedCell K (dot w)) := by
  refine ⟨coe_fixedGroup hK, rootGenerated_le_fixedGroup,
    (Subgroup.normal_subgroupOf_iff_le_normalizer rootGenerated_le_fixedGroup).2
      (fixedGroup_le_normalizer hK), commutator_fixedGroup hK, le_sup_right,
    posFixed_subgroupOf_borelPart_normal, isNilpotent_posFixed, le_sup_left,
    fun g hg g' hg' => torusFixed_mul_comm (torusPart_le_torusFixed hg)
      (torusPart_le_torusFixed hg'), torusPart_inf_posFixed, coe_borelPart,
    fun w ⟨g, hgΓ, hgw⟩ => mem_weylGroup_of_mem_fixedGroup hK hgΓ hgw,
    fun v a hva => ⟨liftGroup_le_monomialSubgroup v a, le_sup_left, range_liftWeylHom hva,
      ker_liftWeylHom hva, borelPart_inf_liftGroup hva, fun dot hdot => ?_⟩⟩
  have hlift : ∀ w ∈ weylGroup, dot w ∈ rootGenerated K ∧
      dot w ∈ monomialSubgroup TwistTag.E6.tag K ∧ MapsRootLines (dot w) w := fun w hw => by
    obtain ⟨hd, hdw⟩ := hdot w hw
    exact ⟨liftGroup_le_rootGenerated hva hd, liftGroup_le_monomialSubgroup v a hd,
      liftWeylHom_eq_iff.1 hdw⟩
  refine ⟨coe_rootGenerated_eq_iUnion hK hlift, fun w hw w' hw' hne => ?_, fun w hw => ?_⟩
  · obtain ⟨-, hdN, hdw⟩ := hlift w hw
    obtain ⟨-, hdN', hdw'⟩ := hlift w' hw'
    exact (disjoint_bruhatCell hne).mono (signedCell_subset_bruhatCell hdN hdw)
      (signedCell_subset_bruhatCell hdN' hdw')
  · obtain ⟨hdS, hdN, hdw⟩ := hlift w hw
    exact ⟨fixed_cell_bijOn (weylGroup_le_parityGroup hw).1 (rootGenerated_le_fixedGroup hdS)
      hdN hdw, signed_cell_bijOn hw hdS hdN hdw⟩

end CFSG.LieType.Chevalley
