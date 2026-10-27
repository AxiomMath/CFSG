module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.Wreathed.NoncentralScalarSylowCoverage

open scoped commutatorElement

universe u v w

theorem noncentral_normal_contains_quasisimple
    {H : Type u} [Group H] (M U : Subgroup H) [M.Normal] [U.Normal]
    (hM : CFSG.IsQuasisimple M)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H)
    (hnoncentral : ¬ U ≤ Subgroup.center H) : M ≤ U := by
  let : Group.IsPerfect M := hM.1
  have hquasi : CFSG.Open.IsQuasisimple M :=
    ⟨Group.IsPerfect.commutator_eq_top, hM.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      hquasi (U.subgroupOf M) with hcenter | htop
  · have hintersection : M ⊓ U ≤ Subgroup.centralizer (M : Set H) := by
      intro a ha
      apply Subgroup.mem_centralizer_iff.mpr
      intro b hb
      have hcentral : (⟨a, ha.1⟩ : M) ∈ Subgroup.center M := hcenter ha.2
      exact congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hcentral) (⟨b, hb⟩ : M))
    have hdouble : ⁅⁅M, U⁆, M⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        ((Subgroup.commutator_le_inf M U).trans hintersection)
    have hcommute : ⁅M, U⁆ = ⊥ :=
      CFSG.ComponentClassification.Quasisimple.perfect_double_commutator M U hdouble
    have hUcenter : U ≤ Subgroup.center H := by
      rw [← hcentralizer]
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      rwa [Subgroup.commutator_comm]
    exact (hnoncentral hUcenter).elim
  · exact Subgroup.subgroupOf_eq_top.mp htop

theorem commutator_preimage_center_le_kernel
    {B : Type u} {A : Type v} [Group B] [Group A] (α : B →* A) :
    ⁅(Subgroup.center A).comap α, (Subgroup.center A).comap α⁆ ≤ α.ker := by
  apply (Subgroup.map_eq_bot_iff _).mp
  rw [Subgroup.map_commutator]
  apply le_antisymm _ bot_le
  have hmap : ((Subgroup.center A).comap α).map α ≤ Subgroup.center A :=
    Subgroup.map_comap_le α (Subgroup.center A)
  have hbound := Subgroup.commutator_mono hmap hmap
  rw [Subgroup.commutator_center_left] at hbound
  exact hbound

theorem quasisimple_le_kernel_image_of_noncentral_central_action
    {B : Type u} {H : Type v} {A : Type w} [Group B] [Group H] [Group A]
    (π : B →* H) (hπ : Function.Surjective π) (α : B →* A)
    (M : Subgroup H) [M.Normal] (hM : CFSG.IsQuasisimple M)
    (hcentralizer : Subgroup.centralizer (M : Set H) = Subgroup.center H)
    (b : B) (hb : π b ∉ Subgroup.center H)
    (haction : α b ∈ Subgroup.center A) : M ≤ α.ker.map π := by
  let D : Subgroup B := (Subgroup.center A).comap α
  let U : Subgroup H := D.map π
  let : D.Normal := inferInstance
  let : U.Normal := Subgroup.Normal.map inferInstance π hπ
  have hU : ¬ U ≤ Subgroup.center H := by
    intro hle
    exact hb (hle (Subgroup.mem_map_of_mem π haction))
  have hMU : M ≤ U := noncentral_normal_contains_quasisimple M U hM hcentralizer hU
  let : Group.IsPerfect M := hM.1
  calc
    M = ⁅M, M⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅U, U⁆ := Subgroup.commutator_mono hMU hMU
    _ = (⁅D, D⁆).map π := (Subgroup.map_commutator D D π).symm
    _ ≤ α.ker.map π := Subgroup.map_mono (commutator_preimage_center_le_kernel α)

theorem inverting_automorphism_isMulCommutative
    {A : Type u} [Group A] (α : MulAut A) (hinverts : ∀ a : A, α a = a⁻¹) :
    IsMulCommutative A := by
  apply isMulCommutative_iff.mpr
  intro a b
  have h := α.map_mul a⁻¹ b⁻¹
  simpa only [hinverts, mul_inv_rev, inv_inv] using h.symm

theorem inverting_automorphism_mem_center
    {A : Type u} [Group A] (α : MulAut A) (hinverts : ∀ a : A, α a = a⁻¹) :
    α ∈ Subgroup.center (MulAut A) := by
  apply Subgroup.mem_center_iff.mpr
  intro β
  apply MulEquiv.ext
  intro a
  change β (α a) = α (β a)
  rw [hinverts, hinverts, map_inv]

theorem quotient_normalizer_surjective
    {N : Type u} [Group N] [Finite N] (R : Subgroup N) [R.Normal]
    {ℓ : ℕ} (hprime : ℓ.Prime) (P : Sylow ℓ R) :
    Function.Surjective ((QuotientGroup.mk' R).domRestrict
      (Subgroup.normalizer (((P : Subgroup R).map R.subtype) : Set N))) := by
  let : Fact ℓ.Prime := ⟨hprime⟩
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.domRestrict_range]
  have hfrattini := congrArg (Subgroup.map (QuotientGroup.mk' R))
    (Sylow.normalizer_sup_eq_top P)
  have hkernel : R.map (QuotientGroup.mk' R) = ⊥ := by
    apply (R.map_eq_bot_iff).mpr
    rw [QuotientGroup.ker_mk']
  rw [Subgroup.map_sup, hkernel, sup_bot_eq,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R)] at hfrattini
  exact hfrattini

theorem scalar_normalizer_action_mem_center
    {N : Type u} [Group N] (P : Subgroup N) (v : N)
    (hv : v ∈ Subgroup.normalizer (P : Set N))
    (hscalar : (∀ a ∈ P, v * a * v⁻¹ = a) ∨
      (∀ a ∈ P, v * a * v⁻¹ = a⁻¹)) :
    P.normalizerMonoidHom ⟨v, hv⟩ ∈ Subgroup.center (MulAut P) := by
  rcases hscalar with hidentity | hinverts
  · have haction : P.normalizerMonoidHom ⟨v, hv⟩ = 1 := by
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      exact hidentity a a.property
    rw [haction]
    exact (Subgroup.center (MulAut P)).one_mem
  · apply inverting_automorphism_mem_center
    intro a
    apply Subtype.ext
    exact hinverts a a.property

theorem noncentral_scalar_Sylow_action_gives_quasisimple_centralizer_coverage
    {N : Type u} [Group N] [Finite N] (R : Subgroup N) [R.Normal]
    (M : Subgroup (N ⧸ R)) [M.Normal] (hM : CFSG.IsQuasisimple M)
    (hcentralizer : Subgroup.centralizer (M : Set (N ⧸ R)) = Subgroup.center (N ⧸ R))
    {ℓ : ℕ} (hprime : ℓ.Prime) (_hdivides : ℓ ∣ Nat.card R) (P : Sylow ℓ R)
    (v : N)
    (hv : v ∈ Subgroup.normalizer (((P : Subgroup R).map R.subtype) : Set N))
    (hnoncentral : QuotientGroup.mk' R v ∉ Subgroup.center (N ⧸ R))
    (hscalar : (∀ a ∈ (P : Subgroup R).map R.subtype, v * a * v⁻¹ = a) ∨
      (∀ a ∈ (P : Subgroup R).map R.subtype, v * a * v⁻¹ = a⁻¹)) :
    (Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set N) ⊓
      M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M := by
  let Q : Subgroup N := (P : Subgroup R).map R.subtype
  let B : Subgroup N := Subgroup.normalizer (Q : Set N)
  let π : B →* (N ⧸ R) := (QuotientGroup.mk' R).domRestrict B
  have hπ : Function.Surjective π := quotient_normalizer_surjective R hprime P
  have haction : Q.normalizerMonoidHom ⟨v, hv⟩ ∈ Subgroup.center (MulAut Q) :=
    scalar_normalizer_action_mem_center Q v hv hscalar
  have hcoverage : M ≤ Q.normalizerMonoidHom.ker.map π :=
    quasisimple_le_kernel_image_of_noncentral_central_action π hπ Q.normalizerMonoidHom
      M hM hcentralizer ⟨v, hv⟩ hnoncentral haction
  have hkernelImage : Q.normalizerMonoidHom.ker.map π =
      (Subgroup.centralizer (Q : Set N)).map (QuotientGroup.mk' R) := by
    rw [Q.normalizerMonoidHom_ker]
    change ((Subgroup.centralizer (Q : Set N)).subgroupOf B).map
      ((QuotientGroup.mk' R).comp B.subtype) = _
    rw [← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer (Q : Set N))]
  rw [hkernelImage] at hcoverage
  apply le_antisymm
  · intro m hm
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hm
    exact ha.2
  · intro m hm
    obtain ⟨a, ha, hma⟩ := Subgroup.mem_map.mp (hcoverage hm)
    exact Subgroup.mem_map.mpr ⟨a, ⟨ha, by
      change QuotientGroup.mk' R a ∈ M
      rw [hma]
      exact hm⟩, hma⟩

end CFSG.Wreathed.NoncentralScalarSylowCoverage
