module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Conj
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitProperComplete

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

namespace Q81

variable {Q : Type} [Group Q]

theorem eq_one_of_forall_inv_mul_mem_center (hQ : Group.IsPerfect Q) {φ : MulAut Q}
    (hφ : ∀ q : Q, q⁻¹ * φ q ∈ center Q) : φ = 1 := by
  let δ : Q →* ↥(center Q) :=
    { toFun := fun q => ⟨q⁻¹ * φ q, hφ q⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun q r => Subtype.ext (by
        have h1 := mem_center_iff.mp (hφ q) r⁻¹
        change (q * r)⁻¹ * φ (q * r) = q⁻¹ * φ q * (r⁻¹ * φ r)
        rw [map_mul, _root_.mul_inv_rev]
        calc r⁻¹ * q⁻¹ * (φ q * φ r) = r⁻¹ * (q⁻¹ * φ q) * φ r := by group
          _ = q⁻¹ * φ q * r⁻¹ * φ r := by rw [h1]
          _ = q⁻¹ * φ q * (r⁻¹ * φ r) := by group) }
  have hker : δ.ker = ⊤ := by
    rw [eq_top_iff, ← hQ.commutator_eq_top]
    exact Abelianization.commutator_subset_ker δ
  ext q
  have hq : q ∈ δ.ker := hker ▸ mem_top q
  have h1 : q⁻¹ * φ q = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hq)
  rw [MulAut.one_apply]
  calc φ q = q * (q⁻¹ * φ q) := by group
    _ = q := by rw [h1, mul_one]

abbrev barAut (φ : MulAut Q) : MulAut (Q ⧸ center Q) :=
  QuotientGroup.congr (center Q) (center Q) φ (map_center_equiv φ)

theorem barAut_mk (φ : MulAut Q) (q : Q) :
    barAut φ (q : Q ⧸ center Q) = ((φ q : Q) : Q ⧸ center Q) :=
  QuotientGroup.congr_mk _ _ _ _ q

theorem map_fixedPoints_le (φ : MulAut Q) :
    (fixedPoints φ).map (QuotientGroup.mk' (center Q)) ≤ fixedPoints (barAut φ) := by
  rintro _ ⟨c, hc, rfl⟩
  rw [mem_fixedPoints, QuotientGroup.mk'_apply, barAut_mk, mem_fixedPoints.mp hc]

theorem map_fixedPoints_normal (φ : MulAut Q) :
    (((fixedPoints φ).map (QuotientGroup.mk' (center Q))).subgroupOf
      (fixedPoints (barAut φ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨c, hc, hcn⟩ := hn
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (g : Q ⧸ center Q)
  have hgF : barAut φ (g : Q ⧸ center Q) = g := g.2
  rw [← hx, barAut_mk, QuotientGroup.eq] at hgF
  have hcφ : φ c = c := mem_fixedPoints.mp hc
  have hxc : x * c * x⁻¹ ∈ fixedPoints φ := by
    rw [mem_fixedPoints, map_mul, map_mul, map_inv, hcφ]
    have hz := mem_center_iff.mp hgF c
    calc φ x * c * (φ x)⁻¹ = φ x * c * ((φ x)⁻¹ * x) * x⁻¹ := by group
      _ = φ x * (c * ((φ x)⁻¹ * x)) * x⁻¹ := by group
      _ = φ x * (((φ x)⁻¹ * x) * c) * x⁻¹ := by rw [hz]
      _ = x * c * x⁻¹ := by group
  refine ⟨x * c * x⁻¹, hxc, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    hx]
  rw [QuotientGroup.mk'_apply] at hcn
  rw [hcn]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

variable [Finite Q]

theorem isTwoQuasisimple_of_surjective {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (hX : IsTwoQuasisimple X) (f : X →* Y) (hf : Function.Surjective f)
    (hY : pPrimeCore 2 Y ≠ ⊤) :
    IsTwoQuasisimple Y ∧ Nonempty (X ⧸ Open.fusionZStar X ≃* Y ⧸ Open.fusionZStar Y) := by
  have : Group.IsPerfect X := hX.1
  have hYp : Group.IsPerfect Y := Group.IsPerfect.ofSurjective hf
  obtain ⟨e⟩ := GrSLit.nonempty_fusionZStar_equiv_of_surjective' f hf hX.2 hY
  refine ⟨⟨hYp, ?_⟩, ⟨e⟩⟩
  obtain ⟨eX⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar X
  obtain ⟨eY⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar Y
  let e' : (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X) ≃*
      (Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y) := (eX.trans e).trans eY.symm
  obtain ⟨-, hsX, a, b, hab⟩ := hX.2
  have : IsSimpleGroup ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) := hsX
  refine ⟨Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _), e'.symm.isSimpleGroup,
    e' a, e' b, fun h => hab ?_⟩
  apply e'.injective
  rw [map_mul, map_mul, h]

theorem subsingleton_of_pPrimeCore_eq_top {Y : Type} [Group Y] [Finite Y]
    (hY : Group.IsPerfect Y) (h : pPrimeCore 2 Y = ⊤) : Subsingleton Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card Y) := by
    have h1 := (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := Y)))
    rwa [h, card_top] at h1
  have hsolv : Group.IsSolvable Y := Milestones.odd_order_solvable hodd
  by_contra hnt
  rw [not_subsingleton_iff_nontrivial] at hnt
  have : Group.IsPerfect Y := hY
  exact Group.IsPerfect.not_isSolvable (G := Y) hsolv

theorem isBlowup_of_fixed (hQ : IsQuasisimple Q) {φ : MulAut Q} (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    {J : Subgroup Q} (hJA : J ≤ fixedPoints φ) (hJs : (J.subgroupOf (fixedPoints φ)).IsSubnormal)
    (hJq : IsTwoQuasisimple ↥J) {Y : Type} [Group Y] (eY : ↥J ⧸ Open.fusionZStar ↥J ≃* Y) :
    IsBlowup (Q ⧸ center Q) Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center Q) with hπ
  set A := fixedPoints φ with hA
  set F := fixedPoints (barAut φ) with hF
  set Ab := A.map π with hAb
  set Yb := J.map π with hYb
  have hYA : Yb ≤ Ab := map_mono hJA
  have hAF : Ab ≤ F := map_fixedPoints_le φ
  have hα2 : barAut φ ^ 2 = 1 := by
    ext s
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    rw [sq, MulAut.mul_apply, barAut_mk, barAut_mk, ← MulAut.mul_apply, hφ2, MulAut.one_apply,
      MulAut.one_apply]
  have hα1 : barAut φ ≠ 1 := by
    intro h
    apply hφ1
    refine eq_one_of_forall_inv_mul_mem_center hQ.1 fun q => ?_
    have h1 := congrArg (fun α : MulAut (Q ⧸ center Q) => α (q : Q ⧸ center Q)) h
    simp only [barAut_mk, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1
    have h3 := inv_mem h2
    rwa [_root_.mul_inv_rev, inv_inv] at h3
  have hα : orderOf (barAut φ) = 2 := orderOf_eq_prime hα2 hα1
  have hYbs : (Yb.subgroupOf F).IsSubnormal := by
    rw [CatalogueBPrimeJoin.subgroupOf_isSubnormal_iff hYA hAF
      (map_fixedPoints_normal φ).isSubnormal]
    have h1 := hJs.map (MonoidHom.subgroupMap_surjective π A)
    have h2 : (J.subgroupOf A).map (π.subgroupMap A) = Yb.subgroupOf Ab := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨⟨a, ha⟩, haJ, h⟩
        rw [mem_subgroupOf]
        have h3 : π a = y := congrArg Subtype.val h
        change y ∈ Yb
        rw [← h3]
        exact mem_map_of_mem π haJ
      · intro h
        rw [mem_subgroupOf] at h
        obtain ⟨j, hj, rfl⟩ := h
        exact ⟨⟨j, hJA hj⟩, hj, rfl⟩
    rwa [h2] at h1
  have hJnt := Cor441.nontrivial_of_isTwoQuasisimple hJq
  have : Group.IsPerfect ↥J := hJq.1
  have hYO : pPrimeCore 2 ↥Yb ≠ ⊤ := by
    intro htop
    have hYp : Group.IsPerfect ↥Yb :=
      Group.IsPerfect.ofSurjective (MonoidHom.subgroupMap_surjective π J) (G := ↥J)
    have hsub := subsingleton_of_pPrimeCore_eq_top hYp htop
    have hJZ : ∀ j ∈ J, j ∈ center Q := by
      intro j hj
      have h1 : (⟨π j, mem_map_of_mem π hj⟩ : ↥Yb) = 1 := Subsingleton.elim _ _
      have h2 : π j = 1 := congrArg Subtype.val h1
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hc : ∀ x y : ↥J, x * y = y * x := fun x y => Subtype.ext
      (mem_center_iff.mp (hJZ x x.2) y).symm
    have := ProperComplete.subsingleton_of_isPerfect_of_comm hJq.1 hc
    exact not_nontrivial ↥J hJnt
  obtain ⟨hYq, ⟨eJY⟩⟩ := isTwoQuasisimple_of_surjective hJq (π.subgroupMap J)
    (MonoidHom.subgroupMap_surjective π J) hYO
  let eL : ↥(Yb.subgroupOf F) ≃* ↥Yb := subgroupOfEquivOfLe (hYA.trans hAF)
  obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv eL
  have hLp : IsPComponent 2 (Yb.subgroupOf F) := by
    rw [← isTwoComponent_iff_isPComponent]
    exact ⟨hYbs, isTwoQuasisimple_of_mulEquiv eL.symm hYq⟩
  exact ⟨inferInstance, hQ.2.1, barAut φ, hα, Yb.subgroupOf F, hLp,
    ⟨(eZ.trans eJY.symm).trans eY⟩⟩

end Q81

end CFSG.ComponentClassification.HarrisLit
