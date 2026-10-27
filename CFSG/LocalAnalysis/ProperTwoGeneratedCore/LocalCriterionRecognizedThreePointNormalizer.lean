module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

variable {G : Type*} [Group G] [Finite G]

theorem quotient_normalizer_image_of_sylow_intersection
    {p : ℕ} (hp : p.Prime) (R P : Subgroup G) [R.Normal]
    (hP : IsPGroup p P)
    (hintersection : ∃ T : Sylow p R,
      (T : Subgroup R).map R.subtype = P ⊓ R) :
    (Subgroup.normalizer (P : Set G)).map (QuotientGroup.mk' R) =
      Subgroup.normalizer
        (P.map (QuotientGroup.mk' R) : Set (G ⧸ R)) := by
  let : Fact p.Prime := ⟨hp⟩
  let q := QuotientGroup.mk' R
  apply le_antisymm (Subgroup.le_normalizer_map q)
  intro y hy
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective R y
  let J := R ⊔ P
  have hconj : P.map (MulAut.conj g).toMonoidHom ≤ J := by
    rintro x ⟨a, ha, rfl⟩
    have hqx : q (g * a * g⁻¹) ∈ P.map q := by
      rw [map_mul, map_mul, map_inv, hg]
      exact Subgroup.le_normalizer_iff.mp le_rfl y hy (q a)
        (Subgroup.mem_map_of_mem q ha)
    have hx : g * a * g⁻¹ ∈ (P.map q).comap q := hqx
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] at hx
    exact hx
  obtain ⟨A, hA⟩ :=
    sylow_in_normal_sup_of_sylow_intersection hp R P hP hintersection
  have hcard :
      Nat.card ((P.map (MulAut.conj g).toMonoidHom).subgroupOf J) =
        Nat.card (A : Subgroup J) := by
    rw [hA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconj).toEquiv,
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (le_sup_right : P ≤ J)).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hfull :
      Nat.card ((P.map (MulAut.conj g).toMonoidHom).subgroupOf J) =
        p ^ (Nat.card J).factorization p :=
    hcard.trans A.card_eq_multiplicity
  let B : Sylow p J := Sylow.ofCard _ hfull
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq J B A
  have heq := congrArg (fun Q : Sylow p J => (Q : Subgroup J)) hc
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Sylow.coe_ofCard, hA] at heq
  change ((P.map (MulAut.conj g).toMonoidHom).subgroupOf J).map
    (MulAut.conj c).toMonoidHom = P.subgroupOf J at heq
  have hmapped := congrArg (Subgroup.map J.subtype) heq
  rw [Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le (le_sup_right : P ≤ J)] at hmapped
  have hmapConj :
      ((P.map (MulAut.conj g).toMonoidHom).subgroupOf J).map
          (J.subtype.comp (MulAut.conj c).toMonoidHom) =
        P.map (MulAut.conj (c.val * g)).toMonoidHom := by
    have hcomm : J.subtype.comp (MulAut.conj c).toMonoidHom =
        (MulAut.conj c.val).toMonoidHom.comp J.subtype := by
      ext x
      rfl
    rw [hcomm, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hconj, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hmapConj] at hmapped
  have hcg : c.val * g ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapped
  obtain ⟨r, hr, a, ha, hra⟩ := Subgroup.mem_sup_of_normal_left.mp c.property
  let n := a⁻¹ * (c.val * g)
  have hn : n ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).mul_mem
      (Subgroup.le_normalizer (P.inv_mem ha)) hcg
  refine ⟨n, hn, ?_⟩
  have hqr : q r = 1 := (QuotientGroup.eq_one_iff _).mpr hr
  change q (a⁻¹ * (c.val * g)) = y
  rw [← hra, map_mul, map_inv, map_mul, map_mul, hqr, one_mul,
    ← mul_assoc, inv_mul_cancel, one_mul, hg]

end CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
