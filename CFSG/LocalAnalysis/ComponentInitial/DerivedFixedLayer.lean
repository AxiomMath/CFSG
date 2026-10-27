module

public import CFSG.LocalAnalysis.ComponentInitial.FactorwiseFixedLayer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem isComponentOf_map_iff {f : G →* G'} (hf : Function.Injective f) {Q K : Subgroup G} :
    CFSG.Assembly.IsComponentOf (Q.map f) (K.map f) ↔ CFSG.Assembly.IsComponentOf Q K := by
  have hq : CFSG.Assembly.IsQuasisimple (Q.map f) ↔ CFSG.Assembly.IsQuasisimple Q := by
    rw [AssemblyBPredicates.isQuasisimple_iff_native, AssemblyBPredicates.isQuasisimple_iff_native]
    exact (isQuasisimple_congr (Q.equivMapOfInjective f hf)).symm
  refine ⟨fun h => ⟨(map_le_map_iff_of_injective hf).1 h.1, ?_, hq.1 h.2.2⟩,
    fun h => ⟨map_mono h.1, assembly_isSubnormal_map f h.2.1, hq.2 h.2.2⟩⟩
  have := assembly_isSubnormal_comap f h.2.1
  rwa [Subgroup.comap_map_eq_self_of_injective hf,
    Subgroup.comap_map_eq_self_of_injective hf] at this

end Transport

variable {T : Type*} [Group T]

theorem map_commutator_aut (b : MulAut T) : (commutator T).map b.toMonoidHom = commutator T :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance b

@[expose] def derivedAut (b : MulAut T) : MulAut (commutator T) :=
  restrictAut b (commutator T) (map_commutator_aut b)

theorem map_subgroupOf_derivedAut (b : MulAut T) {Z : Subgroup T}
    (hbZ : Z.map b.toMonoidHom = Z) :
    (Z.subgroupOf (commutator T)).map (derivedAut b).toMonoidHom =
      Z.subgroupOf (commutator T) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change b y ∈ Z
    rw [← hbZ]
    exact ⟨y, hy, rfl⟩
  · intro hx
    have hx' : (x : T) ∈ Z.map b.toMonoidHom := by rw [hbZ]; exact hx
    obtain ⟨z, hz, hzx⟩ := hx'
    have hzH : z ∈ commutator T := by
      have h1 : b.symm x ∈ (commutator T).map b.symm.toMonoidHom := ⟨x, x.2, rfl⟩
      rw [map_commutator_aut b.symm] at h1
      have h2 : b.symm x = z := by rw [← hzx]; simp
      rwa [h2] at h1
    exact ⟨⟨z, hzH⟩, hz, Subtype.ext hzx⟩

@[expose] def derivedQuotientAut (b : MulAut T) (Z : Subgroup T) [Z.Normal]
    (hbZ : Z.map b.toMonoidHom = Z) : MulAut (commutator T ⧸ Z.subgroupOf (commutator T)) :=
  QuotientGroup.congr _ _ (derivedAut b) (map_subgroupOf_derivedAut b hbZ)

theorem derivedQuotientAut_mk (b : MulAut T) (Z : Subgroup T) [Z.Normal]
    (hbZ : Z.map b.toMonoidHom = Z) (x : commutator T) :
    derivedQuotientAut b Z hbZ (x : commutator T ⧸ Z.subgroupOf (commutator T)) =
      ((derivedAut b x : commutator T) : commutator T ⧸ Z.subgroupOf (commutator T)) :=
  rfl

theorem map_fixed_derivedAut (b : MulAut T) :
    (fixedSubgroup (derivedAut b)).map (commutator T).subtype =
      fixedSubgroup b ⊓ commutator T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨congrArg Subtype.val hy, y.2⟩
  · rintro ⟨hx, hxH⟩
    exact ⟨⟨x, hxH⟩, Subtype.ext hx, rfl⟩

section Solvable

variable {G G' : Type*} [Group G] [Group G']

theorem isSolvable_iff_of_isMulCommutative_quotient {N : Subgroup G} [N.Normal]
    (hab : IsMulCommutative (G ⧸ N)) : Group.IsSolvable G ↔ Group.IsSolvable N := by
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective N.subtype_injective
  · intro h
    have : Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_comm fun a b => hab.is_comm.comm a b
    exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_iff_of_surjective_of_ker_le_center (f : G →* G') (hf : Function.Surjective f)
    (hker : f.ker ≤ center G) : Group.IsSolvable G ↔ Group.IsSolvable G' := by
  constructor
  · intro h
    exact Group.isSolvable_of_surjective hf
  · intro h
    have : Group.IsSolvable f.ker := Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hker b.2) a)
    exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])

theorem isSolvable_congr (e : G ≃* G') : Group.IsSolvable G ↔ Group.IsSolvable G' :=
  ⟨fun _ => Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective,
    fun _ => Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

end Solvable

theorem derived_central_quotient_involution_fixed_layer_and_solvability [Finite T]
    {Z : Subgroup T} [Z.Normal] (hZ : Z ≤ center T) (b : MulAut T) (hb : ∀ x, b (b x) = x)
    (hbZ : Z.map b.toMonoidHom = Z) :
    let H := commutator T
    let π := QuotientGroup.mk' (Z.subgroupOf H)
    let α := derivedQuotientAut b Z hbZ
    let B := fixedSubgroup b
    let B₀ := fixedSubgroup b ⊓ H
    let C := fixedSubgroup α
    let I := (fixedSubgroup (derivedAut b)).map π
    let K := π.ker ⊓ fixedSubgroup (derivedAut b)
    (∃ _ : (B₀.subgroupOf B).Normal, IsMulCommutative (B ⧸ B₀.subgroupOf B)) ∧
      {Q : Subgroup T | CFSG.Assembly.IsComponentOf Q B} =
        {Q | CFSG.Assembly.IsComponentOf Q B₀} ∧
      (layer B).map B.subtype = (layer B₀).map B₀.subtype ∧
      (∃ _ : (I.subgroupOf C).Normal, IsElementaryAbelian 2 (C ⧸ I.subgroupOf C)) ∧
      (π.comp (fixedSubgroup (derivedAut b)).subtype).ker =
        K.subgroupOf (fixedSubgroup (derivedAut b)) ∧ K ≤ center H ∧
      Set.BijOn (fun Q : Subgroup T => (Q.subgroupOf H).map π)
        {Q | CFSG.Assembly.IsComponentOf Q B} {R | CFSG.Assembly.IsComponentOf R C} ∧
      (∀ R : Subgroup (H ⧸ Z.subgroupOf H), CFSG.Assembly.IsComponentOf R C →
        CFSG.Assembly.IsComponentOf ((⁅R.comap π, R.comap π⁆).map H.subtype) B ∧
        (((⁅R.comap π, R.comap π⁆).map H.subtype).subgroupOf H).map π = R) ∧
      (layer B = ⊥ ↔ layer C = ⊥) ∧
      (Group.IsSolvable B ↔ Group.IsSolvable C) := by
  intro H π α B B₀ C I K
  set bH := derivedAut b with hbH
  have hBB : ⁅B, B⁆ ≤ B₀ := by
    refine le_inf (Subgroup.commutator_le.2 fun x hx y hy => ?_) ?_
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    · calc ⁅B, B⁆ ≤ ⁅⊤, ⊤⁆ := commutator_mono le_top le_top
        _ = commutator T := (_root_.commutator_def T).symm
  have hB₀n : (B₀.subgroupOf B).Normal := by
    rw [normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 hh
    exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hk hh1) (inv_mem hk),
      (inferInstance : (commutator T).Normal).conj_mem _ hh2 k⟩
  have hBab : IsMulCommutative (B ⧸ B₀.subgroupOf B) := by
    refine ⟨⟨fun u v => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : ((x * y)⁻¹ * (y * x) : B) = ⁅y⁻¹, x⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [h1]
    exact hBB (Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2))
  have hcompsB : {Q : Subgroup T | CFSG.Assembly.IsComponentOf Q B} =
      {Q | CFSG.Assembly.IsComponentOf Q B₀} := by
    ext Q
    constructor
    · intro hQ
      have hQB₀ : Q ≤ B₀ := by
        calc Q = ⁅Q, Q⁆ := (commutator_self_of_isQuasisimple hQ.2.2).symm
          _ ≤ ⁅B, B⁆ := commutator_mono hQ.1 hQ.1
          _ ≤ B₀ := hBB
      exact isComponentOf_of_le hQ hQB₀ inf_le_left
    · intro hQ
      exact ⟨hQ.1.trans inf_le_left, assembly_isSubnormal_trans hQ.2.1
        (CFSG.Assembly.IsSubnormal.step inf_le_left hB₀n (CFSG.Assembly.IsSubnormal.refl _)),
        hQ.2.2⟩
  have hlayerB : (layer B).map B.subtype = (layer B₀).map B₀.subtype := by
    rw [layer_map_subtype, layer_map_subtype, hcompsB]
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hK : π.ker ≤ center H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZ hx) y)
  have ha : ∀ x, bH (bH x) = x := fun x => Subtype.ext (hb x)
  have hα : ∀ s, α (α s) = s := by
    intro s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    change α (α (x : H ⧸ Z.subgroupOf H)) = x
    rw [derivedQuotientAut_mk, derivedQuotientAut_mk, ha]
  have hcomm : ∀ x, π (bH x) = α (π x) := fun x => rfl
  obtain ⟨hquot, hkerB, hbij, hlift, -, -, -, hiffH⟩ :=
    full_central_kernel_involution_fixed_component_correspondence hπ hK ha hα hcomm
  have hB₀H : (fixedSubgroup bH).map H.subtype = B₀ := map_fixed_derivedAut b
  have hsub : Set.BijOn (fun Q : Subgroup T => Q.subgroupOf H)
      {Q | CFSG.Assembly.IsComponentOf Q B₀}
      {Q | CFSG.Assembly.IsComponentOf Q (fixedSubgroup bH)} := by
    have hQH : ∀ {Q : Subgroup T}, CFSG.Assembly.IsComponentOf Q B₀ →
        (Q.subgroupOf H).map H.subtype = Q := fun hQ => by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hQ.1.trans inf_le_right)]
    refine ⟨fun Q hQ => ?_, fun Q₁ hQ₁ Q₂ hQ₂ h => ?_, fun Q hQ => ?_⟩
    · show CFSG.Assembly.IsComponentOf (Q.subgroupOf H) (fixedSubgroup bH)
      rw [← isComponentOf_map_iff H.subtype_injective, hB₀H, hQH hQ]
      exact hQ
    · rw [← hQH hQ₁, ← hQH hQ₂]
      exact congrArg (Subgroup.map H.subtype) h
    · refine ⟨Q.map H.subtype, ?_, Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q⟩
      show CFSG.Assembly.IsComponentOf (Q.map H.subtype) B₀
      rw [← hB₀H, isComponentOf_map_iff H.subtype_injective]
      exact hQ
  have hbijB : Set.BijOn (fun Q : Subgroup T => (Q.subgroupOf H).map π)
      {Q | CFSG.Assembly.IsComponentOf Q B} {R | CFSG.Assembly.IsComponentOf R C} := by
    rw [hcompsB]
    exact hbij.comp hsub
  have hinv : ∀ R : Subgroup (H ⧸ Z.subgroupOf H), CFSG.Assembly.IsComponentOf R C →
      CFSG.Assembly.IsComponentOf ((⁅R.comap π, R.comap π⁆).map H.subtype) B ∧
      (((⁅R.comap π, R.comap π⁆).map H.subtype).subgroupOf H).map π = R := by
    intro R hR
    obtain ⟨-, hQ, hQmap, -⟩ := hlift R hR
    refine ⟨?_, ?_⟩
    · have h1 : CFSG.Assembly.IsComponentOf ((⁅R.comap π, R.comap π⁆).map H.subtype) B₀ := by
        rw [← hB₀H, isComponentOf_map_iff H.subtype_injective]
        exact hQ
      have h2 : ((⁅R.comap π, R.comap π⁆).map H.subtype) ∈
          {Q : Subgroup T | CFSG.Assembly.IsComponentOf Q B₀} := h1
      rw [← hcompsB] at h2
      exact h2
    · have hQQ : ((⁅R.comap π, R.comap π⁆).map H.subtype).subgroupOf H =
          ⁅R.comap π, R.comap π⁆ :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      rw [hQQ]
      exact hQmap
  have hiff : layer B = ⊥ ↔ layer C = ⊥ := by
    rw [layer_eq_bot_iff, layer_eq_bot_iff, ← hbijB.image_eq, Set.image_eq_empty]
  obtain ⟨hIn, hIab, -⟩ := hquot
  have hKc : K ≤ center H := inf_le_left.trans hK
  have hsolv : Group.IsSolvable B ↔ Group.IsSolvable C := by
    have h1 := isSolvable_iff_of_isMulCommutative_quotient hBab
    have h2 := isSolvable_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : B₀ ≤ B))
    have h3 := isSolvable_congr ((MulEquiv.subgroupCongr hB₀H).symm.trans
      ((fixedSubgroup bH).equivMapOfInjective H.subtype H.subtype_injective).symm)
    let f : fixedSubgroup bH →* I := (π.comp (fixedSubgroup bH).subtype).codRestrict I
      fun x => ⟨x, x.2, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfker : f.ker ≤ center (fixedSubgroup bH) := fun x hx => by
      have hxK : (x : H) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        have h1 : ((f x : I) : H ⧸ Z.subgroupOf H) = 1 := by rw [MonoidHom.mem_ker.1 hx]; rfl
        exact h1
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.1 (hK hxK) y)
    have h4 := isSolvable_iff_of_surjective_of_ker_le_center f hf hfker
    have hIC : I ≤ C := map_fixed_le hcomm
    have h5 := isSolvable_congr (Subgroup.subgroupOfEquivOfLe hIC)
    have h6 := isSolvable_iff_of_isMulCommutative_quotient (N := I.subgroupOf C)
      hIab.toIsMulCommutative
    rw [h1, h2, h3, h4, ← h5, ← h6]
  exact ⟨⟨hB₀n, hBab⟩, hcompsB, hlayerB, ⟨hIn, hIab⟩, hkerB, hKc, hbijB, hinv, hiff, hsolv⟩

end CFSG.LocalAnalysis.ComponentInitial
