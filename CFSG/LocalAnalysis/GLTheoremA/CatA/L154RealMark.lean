module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReal
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplitConj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenProj LargeEvenProjMk
  LargeEvenMatConjImage LargeEvenScalars LargeEvenSLGroup LargeEvenSUGroup LargeEvenGUSet)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (slSubfieldIncl largeEvenSL_isPerfect
  largeEvenSL_center_eq)
open scoped MatrixGroups

section Cover

theorem l154_exists_centerQuot_equiv {U M P : Type*} [Group U] [Group M] [Group P]
    (hU : commutator U = ⊤) (g : U →* M) (hker : g.ker ≤ Subgroup.center U) (q : U →* P)
    (hq : Function.Surjective q) (hqk : q.ker = Subgroup.center U) :
    ∃ θ : ↥g.range ⧸ Subgroup.center ↥g.range ≃* P,
      ∀ u, θ (QuotientGroup.mk (g.rangeRestrict u)) = q u := by
  let q₁ : U →* ↥g.range ⧸ Subgroup.center ↥g.range :=
    (QuotientGroup.mk' _).comp g.rangeRestrict
  have hq₁ : Function.Surjective q₁ :=
    (QuotientGroup.mk'_surjective _).comp g.rangeRestrict_surjective
  have hk₁ : q₁.ker = Subgroup.center U := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (g.rangeRestrict u) : ↥g.range ⧸ Subgroup.center ↥g.range) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine ⟨CFSG.StandardType.InnerDiagA.mem_center_of_rangeRestrict_mem_center hU g hker,
      fun hu => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨s, rfl⟩ := g.rangeRestrict_surjective l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  let θ : ↥g.range ⧸ Subgroup.center ↥g.range ≃* P :=
    (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk₁.trans hqk.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))
  refine ⟨θ, fun u => ?_⟩
  show θ (q₁ u) = q u
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm (q₁ u) =
      (u : U ⧸ q₁.ker) := (MulEquiv.symm_apply_eq _).mpr rfl
  simp only [θ, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end Cover

section Lift

variable {M : Type} [Group M] {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ} {K : Subfield L}
  {H : Subgroup (GL (Fin ν) ↥K)}

theorem l154_exists_lift (hν : 1 ≤ ν) (ι : ↥H →* SL(ν, L))
    (hι : ∀ h : ↥H, ((ι h : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      ((h : GL (Fin ν) ↥K) : Matrix (Fin ν) (Fin ν) ↥K).map K.subtype)
    (W : SL(ν, L) →* M) {A : GL (Fin ν) ↥K}
    (hA : A ∈ Subgroup.normalizer (H : Set (GL (Fin ν) ↥K))) :
    ∃ (w : M) (α β : ↥H → ↥H),
      (∀ h, ((α h : ↥H) : GL (Fin ν) ↥K) = A * h * A⁻¹) ∧
      (∀ h, ((β h : ↥H) : GL (Fin ν) ↥K) = A⁻¹ * h * A) ∧
      (∀ h, w * W (ι h) * w⁻¹ = W (ι (α h))) ∧ (∀ h, w⁻¹ * W (ι h) * w = W (ι (β h))) := by
  have hA' : A⁻¹ ∈ Subgroup.normalizer (H : Set (GL (Fin ν) ↥K)) := Subgroup.inv_mem _ hA
  let α : ↥H → ↥H := fun h => ⟨A * h * A⁻¹, (Subgroup.mem_normalizer_iff.1 hA h).1 h.2⟩
  let β : ↥H → ↥H := fun h => ⟨A⁻¹ * h * A, by
    simpa using (Subgroup.mem_normalizer_iff.1 hA' h).1 h.2⟩
  obtain ⟨B, hB⟩ := CFSG.RankThree.Classical2.exists_specialLinear_conj_eq (n := ν) hν
    (Matrix.GeneralLinearGroup.map K.subtype A)
  have hα : ∀ h, ι (α h) = B * ι h * B⁻¹ := by
    intro h
    apply Subtype.ext
    have h1 := hB ((ι h : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1, hι, hι]
    change ((A * h * A⁻¹ : GL (Fin ν) ↥K) : Matrix (Fin ν) (Fin ν) ↥K).map K.subtype = _
    simp only [Units.val_mul, Matrix.map_mul]
    rfl
  have hαβ : ∀ h, α (β h) = h := fun h => Subtype.ext (by simp only [α, β]; group)
  refine ⟨W B, α, β, fun h => rfl, fun h => rfl, fun h => ?_, fun h => ?_⟩
  · rw [hα h, map_mul, map_mul, map_inv]
  · have h1 := hα (β h)
    rw [hαβ] at h1
    rw [h1, map_mul, map_mul, map_inv]
    group

end Lift

section Assembly

variable {M : Type} [Group M] {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ} {K : Subfield L}
  {H : Subgroup (GL (Fin ν) ↥K)}

theorem l154_exists_realized_of_cover (hν : 1 ≤ ν) {S' : Set (GL (Fin ν) ↥K)}
    (hS' : ∀ A ∈ S', A ∈ Subgroup.normalizer (H : Set (GL (Fin ν) ↥K)))
    (ι : ↥H →* SL(ν, L))
    (hι : ∀ h : ↥H, ((ι h : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      ((h : GL (Fin ν) ↥K) : Matrix (Fin ν) (Fin ν) ↥K).map K.subtype)
    (W : SL(ν, L) →* M) {R : Subgroup M} (hR : (W.comp ι).range = R)
    (hperf : Group.IsPerfect ↥H)
    (hZ : (LargeEvenScalars (Fin ν) ↥K).subgroupOf H = Subgroup.center ↥H)
    (hker : (W.comp ι).ker ≤ Subgroup.center ↥H) (hqs : CFSG.IsQuasisimple ↥R) :
    commutator ↥R = ⊤ ∧ IsSimpleGroup (LargeEvenProj H) ∧
      (∃ a b : LargeEvenProj H, a * b ≠ b * a) ∧
      ∃ θ : ↥R ⧸ Subgroup.center ↥R ≃* LargeEvenProj H,
        ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S', ∃ w ∈ Subgroup.normalizer (R : Set M),
          LargeEvenInduces θ (fun r r' : ↥R => w * (r : M) * w⁻¹ = (r' : M)) φ := by
  subst hR
  obtain ⟨hperfR, hsimple, hnonab⟩ := hqs
  obtain ⟨θ, hθ⟩ := l154_exists_centerQuot_equiv Group.IsPerfect.commutator_eq_top (W.comp ι)
    hker (LargeEvenProjMk H) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hZ)
  refine ⟨Group.IsPerfect.commutator_eq_top, (MulEquiv.isSimpleGroup_congr θ).1 hsimple, ?_, θ, ?_⟩
  · obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨θ a, θ b, fun h => hab (θ.injective (by rw [map_mul, map_mul]; exact h))⟩
  · intro φ hφ
    obtain ⟨A, hAS, hφA⟩ := hφ
    obtain ⟨w, α, β, hα, hβ, hwα, hwβ⟩ := l154_exists_lift hν ι hι W (hS' A hAS)
    refine ⟨w, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨α u, (hwα u).symm⟩
      · rintro ⟨u, hu⟩
        refine ⟨β u, ?_⟩
        have h1 : x = w⁻¹ * (w * x * w⁻¹) * w := by group
        rw [h1, ← hu]
        exact (hwβ u).symm.trans (by simp)
    · intro r r' hr
      obtain ⟨u, rfl⟩ := (W.comp ι).rangeRestrict_surjective r
      have hr' : r' = (W.comp ι).rangeRestrict (α u) :=
        Subtype.ext (by rw [← hr]; exact hwα u)
      rw [hr', hθ, hθ]
      exact hφA u (α u) (hα u)

end Assembly

section Markings

variable {M : Type} [Group M] {L : Type} [Field L] [IsAlgClosed L]

theorem l154_realizedMarking_of_split {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) {K : Subfield L}
    [Finite ↥K] (hK : Nat.card ↥K = 2 ^ f) (W : SL(m + 1, L) →* M) {R : Subgroup M}
    (hR : (W.comp (slSubfieldIncl K (m + 1))).range = R)
    (hker : (W.comp (slSubfieldIncl K (m + 1))).ker ≤
      Subgroup.center ↥(LargeEvenSLGroup (Fin (m + 1)) ↥K))
    (hqs : CFSG.IsQuasisimple ↥R) : L154RealizedMarking R := by
  have hnorm : ∀ A ∈ (Set.univ : Set (GL (Fin (m + 1)) ↥K)),
      A ∈ Subgroup.normalizer ((LargeEvenSLGroup (Fin (m + 1)) ↥K : Subgroup _) :
        Set (GL (Fin (m + 1)) ↥K)) := fun A _ => by
    rw [Subgroup.mem_normalizer_iff]
    exact fun h => ⟨fun hh => Subgroup.Normal.conj_mem inferInstance h hh A, fun hh => by
      simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance _ hh A⁻¹⟩
  obtain ⟨hcomm, hsimple, hnonab, θ, hθ⟩ := l154_exists_realized_of_cover (by omega) hnorm
    (slSubfieldIncl K (m + 1)) (fun h => rfl) W hR (largeEvenSL_isPerfect (by omega))
    (largeEvenSL_center_eq (by omega)) hker hqs
  have hlab : CFSG.Assembly.LargeEvenInLambda2 ⟨.A, m, f⟩ := by
    simp only [CFSG.Assembly.LargeEvenInLambda2]
    exact ⟨hf, by omega, fun h => by omega⟩
  refine ⟨hcomm, ⟨.A, m, f⟩, hlab, ?_⟩
  exact ⟨↥K, inferInstance, inferInstance, hK, hsimple, hnonab, θ, hθ⟩

theorem l154_realizedMarking_of_unitary {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f)
    (h32 : (m + 1, 2 ^ f) ≠ (3, 2)) {K : Subfield L} [Finite ↥K]
    (hK : Nat.card ↥K = (2 ^ f) ^ 2) (W : SL(m + 1, L) →* M) {R : Subgroup M}
    (hR : (W.comp (CFSG.RankThree.Classical2.statedSUToSL K (m + 1) (2 ^ f))).range = R)
    (hker : (W.comp (CFSG.RankThree.Classical2.statedSUToSL K (m + 1) (2 ^ f))).ker ≤
      Subgroup.center ↥(CFSG.Open.StatedSU (m + 1) (2 ^ f) ↥K))
    (hqs : CFSG.IsQuasisimple ↥R) : L154RealizedMarking R := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f ↥K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hnorm : ∀ A ∈ LargeEvenGUSet (Fin (m + 1)) ↥K (2 ^ f),
      A ∈ Subgroup.normalizer ((CFSG.Open.StatedSU (m + 1) (2 ^ f) ↥K : Subgroup _) :
        Set (GL (Fin (m + 1)) ↥K)) := fun A hA =>
    CFSG.StandardType.TableBUE.gu_subset_normalizer hU hA
  obtain ⟨hq, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) hK (by omega : 3 ≤ m + 1) h32
  obtain ⟨hcomm, hsimple, hnonab, θ, hθ⟩ := l154_exists_realized_of_cover (by omega) hnorm
    (CFSG.RankThree.Classical2.statedSUToSL K (m + 1) (2 ^ f))
    (fun h => CFSG.RankThree.Classical2.coe_statedSUToSL K (m + 1) (2 ^ f) h) W hR
    hq.1 hZ.symm hker hqs
  have h2f : m = 2 → 2 ≤ f := fun hm2 => by
    by_contra hlt
    have hf1 : f = 1 := by omega
    exact h32 (by rw [hm2, hf1]; rfl)
  have hlab : CFSG.Assembly.LargeEvenInLambda2 ⟨.twA, m, f⟩ := by
    simp only [CFSG.Assembly.LargeEvenInLambda2]
    exact ⟨hf, hm, h2f⟩
  refine ⟨hcomm, ⟨.twA, m, f⟩, hlab, ?_⟩
  exact ⟨↥K, inferInstance, inferInstance, hK, hsimple, hnonab, θ, hθ⟩

end Markings

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
