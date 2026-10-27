module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairCentralizerModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSevenAffine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSevenLocal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSevenSinger

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.CosetNormalizer
open CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped IsMulCommutative Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

theorem involution_coset_normalizer_solvable_or_projective_seven
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (R : Sylow 2 ↥(localInvolutionPointHull z u ⊓ H))
    (T₁ : Sylow 2 ↥(H ⊓ Subgroup.centralizer ({u} : Set G))) :
    let M := Subgroup.centralizer ({u} : Set G)
    let D := involutionPointClass z
    let L := localInvolutionPointHull z u
    let K := M ⊓ Subgroup.centralizer (L : Set G)
    let A := (T₁ : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
    let T := (A : Set G) ∩ ((L : Set G) * (K : Set G))
    let Δ := involutionPointClass u ∩ T
    let N := Subgroup.normalizer Δ
    let NΔ := (cosetNormalizerPerm Δ).range
    ∃ (U : Subgroup G) (_ : IsElementaryAbelian 2 U),
      (U : Set G) = {1} ∪ (D ∩ (M : Set G) ∩ (H : Set G)) ∧
      (∃ e : ℕ, 2 ≤ e ∧ Nat.card U = 2 ^ e) ∧
      Δ = (fun v : G => u * v) '' (U : Set G) ∧
      (∃ ε : Subgroup.zpowers u × U ≃* ↥(Subgroup.zpowers u ⊔ U),
        ∀ (a : Subgroup.zpowers u) (b : U), (ε (a, b) : G) = a * b) ∧
      {g : G | g ∈ N ∧ ∀ x ∈ Δ, g⁻¹ * x * g = x} =
        (Subgroup.centralizer ((Subgroup.zpowers u ⊔ U : Subgroup G) : Set G) : Set G) ∧
      N ≤ H ∧ N ⊓ M = M ⊓ Subgroup.normalizer (U : Set G) ∧
      ∃ j : Additive U ≃ Δ, (∀ v : U, (j (Additive.ofMul v) : G) = u * v) ∧
        (NΔ : Set (Equiv.Perm Δ)) ⊆
          Set.range (fun g : Additive U ≃ᵃ[ZMod 2] Additive U => j.permCongr g.toEquiv) ∧
        MulAction.IsMultiplyPretransitive NΔ Δ 2 ∧
        L ⊓ Subgroup.normalizer (U : Set G) ≤ N ∧
        (let C := ((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf N).map (cosetNormalizerPerm Δ)
          let NΔu := NΔ ⊓ MulAction.stabilizer (Equiv.Perm Δ) (j 0)
          C ≤ NΔu ∧ (C.subgroupOf NΔu).Normal ∧ IsCyclic C ∧ Nat.card C = Nat.card U - 1 ∧
            ∀ x y : Δ, (x : G) ≠ u → (y : G) ≠ u → ∃! σ : C, (σ : Equiv.Perm Δ) x = y) ∧
        ((Group.IsSolvable NΔ ∧
            ∀ g ∈ translationGroup (Additive U), j.permCongr g.toEquiv ∈ NΔ) ∨
          (Nat.card U = 8 ∧ (∃ b : Δ ≃ Omega (ZMod 7),
            (fun σ : Equiv.Perm Δ => b.permCongr σ) '' (NΔ : Set (Equiv.Perm Δ)) =
              (coordinateG (ZMod 7) : Set (Equiv.Perm (Omega (ZMod 7))))) ∧
            (coordinatePSLAction (ZMod 7)).range = coordinateG (ZMod 7))) := by
  intro M D L K A T Δ
  classical
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huB
  have hLM : L ≤ M := localInvolutionPointHull_le_centralizer z u
  have huLcomm : ∀ l ∈ L, Commute u l := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLM hl)).symm
  obtain ⟨-, -, -, hRcenter, hRodd, U, hUset, hUelem, -, hRU, hzU, hmodels, -, ⟨S, hS⟩, huL,
    hOmT, -, hcommute, he, -, -, -, -, hUclass, -, -, hinterA, hDelta, -, -, -, -, -⟩ :=
    rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm hsmallerR1 beta
      hbeta hpairRank huB hu huz hescape R T₁
  have hΔ : Δ = (fun v : G => u * v) '' (U : Set G) := hDelta
  clear_value Δ
  subst hΔ
  intro N NΔ
  obtain ⟨-, hLnormal, -, -, -, -, hfixL, -⟩ :=
    minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hsmallerR1 huH hu huz
      hescape
  have hΓodd : Odd (Nat.card (elementFixedSet H u)) := by
    rcases hmodels with ⟨hΓ, f, hf, hq, -⟩ | ⟨hΓ, m, -, hq, -⟩ | ⟨hΓ, f, hf, hq, -⟩
    · rw [hΓ, hq]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    · rw [hΓ, hq]
      exact (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by omega⟩).add_one
    · rw [hΓ, hq]
      exact (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by omega⟩).add_one
  have hodd : Odd (Nat.card (numeratorRightOrbit H L (rightCosetMk H 1))) := by
    rw [← hfixL]
    exact hΓodd
  obtain ⟨R', hR'⟩ := exists_sylow_of_odd_orbit hodd R
  have hsingerModel : (∃ f : ℕ, 2 ≤ f ∧ Nat.card U = 2 ^ f ∧
        Nonempty (L ⧸ CFSG.oddCore L ≃* PSL2BinaryMatrixGroup f)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card U = 2 ^ (2 * m + 1) ∧
        Nonempty (L ⧸ CFSG.oddCore L ≃* SuzukiMatrixGroup m)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ Nat.card U = 2 ^ f ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k)
        (J : HermitianForm 3 k), J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
          Nat.card k = Nat.card U ^ 2 ∧ Nat.card {x : k // J.conj x = x} = Nat.card U ∧
          Nonempty (L ⧸ CFSG.oddCore L ≃* ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rcases hmodels with ⟨-, f, hf, hq, -, E, -⟩ | ⟨-, m, hm, hq, -, E, -⟩ |
      ⟨-, f, hf, hq, k, hk, hkfin, J, hJ, hkcard, hfixed, -, -, E, -⟩
    · exact Or.inl ⟨f, hf, hq, ⟨E⟩⟩
    · exact Or.inr (Or.inl ⟨m, hm, hq, ⟨E⟩⟩)
    · exact Or.inr (Or.inr ⟨f, hf, hq, k, hk, hkfin, J, hJ, hkcard, hfixed, ⟨E⟩⟩)
  obtain ⟨e, he2, hcardU⟩ : ∃ e : ℕ, 2 ≤ e ∧ Nat.card U = 2 ^ e := by
    rcases hsingerModel with ⟨f, hf, hq, -⟩ | ⟨m, hm, hq, -⟩ | ⟨f, hf, hq, -⟩
    · exact ⟨f, hf, hq⟩
    · exact ⟨2 * m + 1, by omega, hq⟩
    · exact ⟨f, hf, hq⟩
  obtain ⟨-, -, hcyc, hcardS, hreg, -⟩ :=
    even_rank_one_central_odd_cover_involution_normalizer_singer_action (CFSG.oddCore L)
      hRcenter hRodd R' (Nat.card U) hsingerModel
  have hU'map : (Subgroup.closure {x : L | x ∈ (R' : Subgroup L) ∧ orderOf x = 2}).map
      L.subtype = U := by
    rw [map_closure_involutions, hR', ← map_omega_one_eq_closure]
    exact hRU
  have hUL : U ≤ L := hU'map ▸ Subgroup.map_subtype_le _
  have hU' : Subgroup.closure {x : L | x ∈ (R' : Subgroup L) ∧ orderOf x = 2} =
      U.subgroupOf L := by
    rw [← hU'map]
    exact (Subgroup.comap_map_eq_self_of_injective L.subtype_injective _).symm
  rw [hU'] at hcyc hcardS hreg
  obtain ⟨hCcyc, hCcard, hCreg⟩ := coset_conjugation_image_of_singer hUL huLcomm hcyc hcardS hreg
  have hUbot : U ≠ ⊥ := fun hbot => hzU.2 (Subgroup.mem_bot.mp (hbot ▸ hzU.1))
  have huC : u ∈ Subgroup.centralizer (U : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun x hx => (hcommute u (Subgroup.mem_zpowers u) x hx).symm.eq
  have huU : u ∉ U := fun huU => huL (hUL huU)
  have hΩ : Subgroup.closure {x : G | x ∈ (S : Subgroup M).map M.subtype ∧ orderOf x = 2} =
      Subgroup.closure ({u} : Set G) ⊔ U := by
    rw [hS, ← Subgroup.zpowers_eq_closure, ← hOmT]
    exact (map_omega_one_eq_closure (T₁ : Subgroup ↥(H ⊓ M))).symm
  have hclass : conjugatesOf u ∩ (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) =
      (fun v : G => u * v) '' (U : Set G) := by
    rw [hS, ← hinterA]
    congr 1
    ext w
    exact mem_involutionPointClass_iff.symm
  obtain ⟨S₀, hzS₀, hzcenter⟩ := h.central_sylow
  have htrans : ∀ v ∈ U, ∀ w ∈ U, v ≠ 1 → w ≠ 1 →
      ∃ g ∈ M ⊓ Subgroup.normalizer (U : Set G), g * v * g⁻¹ = w := by
    intro v hv w hw hv1 hw1
    obtain ⟨⟨_, m, hm, rfl⟩, hσ, -⟩ := hCreg ⟨u * v, v, hv, rfl⟩ ⟨u * w, w, hw, rfl⟩
      (by simpa using hv1) (by simpa using hw1)
    obtain ⟨hmL, hmU⟩ := Subgroup.mem_subgroupOf.mp hm
    refine ⟨m, ⟨hLM hmL, hmU⟩, ?_⟩
    have hσ' := congrArg Subtype.val hσ
    rw [cosetNormalizerPerm_apply] at hσ'
    have hmu : (m : G) * u = u * m := (huLcomm _ hmL).eq.symm
    calc (m : G) * v * (m : G)⁻¹ = u⁻¹ * ((m : G) * (u * v) * (m : G)⁻¹) := by
          rw [← mul_assoc (m : G) u, hmu]
          group
      _ = w := by
          change (m : G) * (u * v) * (m : G)⁻¹ = u * w at hσ'
          rw [hσ']
          group
  have : IsElementaryAbelian 2 U := hUelem
  obtain ⟨-, h2⟩ := involution_coset_normalizer_fusion_transitivity U hUbot huC huU hu S hΩ hclass
    ⟨S₀, z, hzS₀, hzcenter, fun v hv hv1 => mem_involutionPointClass_iff.mp (hUclass ⟨hv, hv1⟩)⟩
    htrans
  obtain ⟨-, hNU, hker, ⟨φ, -, -, hφ⟩, hNu⟩ :=
    involution_coset_normalizer_affine_action U hUbot huC huU hu
  have hUH : U ≤ H := by
    intro x hx
    have hx' : x ∈ (U : Set G) := hx
    rw [hUset] at hx'
    rcases hx' with rfl | ⟨-, hxH⟩
    · exact H.one_mem
    · exact hxH
  have hfixz := ((involution_point_unique_containment_action h.local_datum.distinguished_mem
    h.local_datum.distinguished_order).2 h.local_datum.unique_containment).2.2.1
  have hNH : N ≤ H := hNU.trans (normalizer_le_of_unique_fixed_coset hUH hzU.1 hfixz)
  let X := (L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf N
  have hXu : ∀ x ∈ X, (x : G) ∈ M := fun x hx => hLM (Subgroup.mem_subgroupOf.mp hx).1
  have hXn : ∀ m : N, (m : G) ∈ M → ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
    intro m hm x hx
    obtain ⟨hxL, hxU⟩ := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mp
        (hLnormal.conj_mem ⟨x, hLM hxL⟩ (Subgroup.mem_subgroupOf.mpr hxL) ⟨m, hm⟩)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hNU m.2) hxU) (Subgroup.inv_mem _ (hNU m.2))
  have hfixu : ∀ m : N, cosetNormalizerPerm _ m (cosetCoordinates U u 0) =
      cosetCoordinates U u 0 ↔ (m : G) ∈ M := by
    intro m
    rw [Subgroup.mem_centralizer_singleton_iff, ← Subtype.coe_inj, cosetNormalizerPerm_apply,
      cosetCoordinates_zero]
    constructor
    · intro hm
      calc (m : G) * u = (m : G) * u * (m : G)⁻¹ * m := by group
        _ = u * m := by rw [hm]
    · intro hm
      rw [hm, mul_inv_cancel_right]
  refine ⟨U, hUelem, hUset, ⟨e, he2, hcardU⟩, rfl, ?_, ?_, hNH, hNu, cosetCoordinates U u,
    fun v => rfl, ?_, ?_, inf_normalizer_le_normalizer_coset huLcomm, ?_, ?_⟩
  · obtain ⟨ε, hε⟩ := he
    have hι : Function.Injective ((H ⊓ M).subtype.comp (T₁ : Subgroup ↥(H ⊓ M)).subtype) :=
      (H ⊓ M).subtype_injective.comp (T₁ : Subgroup ↥(H ⊓ M)).subtype_injective
    exact ⟨(ε.trans ((CFSG.omega₁ (G := T₁) (p := 2)).equivMapOfInjective _ hι)).trans
      (MulEquiv.subgroupCongr hOmT), hε⟩
  · ext g
    rw [← Subgroup.zpowers_eq_closure] at hker
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, ← hker g]
    exact and_congr_right fun _ => forall₂_congr fun x _ => inv_mul_mul_eq_iff g x
  · rintro _ ⟨n, rfl⟩
    exact ⟨φ n, DFunLike.congr_fun (cosetAffinePerm_comp_eq φ hφ) n⟩
  · refine MulAction.is_two_pretransitive_iff.mpr fun {a b c d} hab hcd => ?_
    obtain ⟨n, hn, hna, hnb⟩ := h2 a a.2 b b.2 c c.2 d d.2 (fun h => hab (Subtype.ext h))
      (fun h => hcd (Subtype.ext h))
    exact ⟨⟨cosetNormalizerPerm _ ⟨n, hn⟩, ⟨n, hn⟩, rfl⟩, Subtype.ext hna, Subtype.ext hnb⟩
  · intro C NΔu
    have hCle : C ≤ NΔu := by
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨⟨m, rfl⟩, (hfixu m).mpr (hXu m hm)⟩
    refine ⟨hCle, (Subgroup.normal_subgroupOf_iff hCle).mpr ?_, hCcyc, hCcard, hCreg⟩
    rintro _ _ ⟨m, hm, rfl⟩ ⟨⟨m', rfl⟩, hk⟩
    exact ⟨m' * m * m'⁻¹, hXn m' ((hfixu m').mp hk) m hm, by simp only [map_mul, map_inv]⟩
  · have htrans1 : ∀ x ∈ (fun v : G => u * v) '' (U : Set G),
        ∀ y ∈ (fun v : G => u * v) '' (U : Set G), ∃ n ∈ N, n * x * n⁻¹ = y := by
      intro x hx y hy
      by_cases hxy : x = y
      · exact ⟨1, Subgroup.one_mem _, by rw [hxy]; group⟩
      · obtain ⟨n, hn, hnx, -⟩ := h2 x hx y hy y hy x hx hxy (Ne.symm hxy)
        exact ⟨n, hn, hnx⟩
    exact coset_normalizer_perm_solvable_or_projective_seven (by omega) hcardU φ hφ htrans1 X
      hXu hXn hCcyc hCreg

end CFSG.ProperTwoGeneratedCore.RankOnePair
