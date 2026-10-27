module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofSUData
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCore
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSU
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSL
import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverSU

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup Matrix CFSG.Open
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr conjTr_mul SUid mem_SUid)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Unitary

variable {n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

theorem l212in_conjTr_map (σ : K ≃+* K) (M : Matrix (Fin n) (Fin n) K) :
    conjTr (unitaryInvolution K r f) (M.map σ) = (conjTr (unitaryInvolution K r f) M).map σ := by
  ext i j
  simp only [conjTr, transpose_apply, map_apply]
  rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]

theorem l212in_glAut_mem_Uid (σ : K ≃+* K) {B : GL (Fin n) K}
    (hB : B ∈ Uid (unitaryInvolution K r f) n) : glAut σ B ∈ Uid (unitaryInvolution K r f) n := by
  rw [mem_Uid_iff] at hB ⊢
  rw [coe_glAut, l212in_conjTr_map, ← Matrix.map_mul, hB, Matrix.map_one σ (map_zero σ)
    (map_one σ)]

theorem l212in_det_glAut (σ : K ≃+* K) (M : GL (Fin n) K) :
    GeneralLinearGroup.det (glAut σ M) = Units.map (σ : K →+* K) (GeneralLinearGroup.det M) := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply,
    coe_glAut]
  exact (RingHom.map_det (σ : K →+* K) (M : Matrix (Fin n) (Fin n) K)).symm

theorem l212in_glAut_scalar (σ : K ≃+* K) (c : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →+* K) c) := by
  refine Units.ext ?_
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
    scalar_apply, diagonal_map (map_zero σ)]
  rfl

theorem outDiag_of_unitary {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) (hZne : center L ≠ ⊥) (hZp : IsPGroup p (center L))
    (hn : 5 ≤ n) (hK : Nat.card K = (r ^ f) ^ 2)
    (e : L ⧸ center L ≃* StatedProj (StatedSU n (r ^ f) K)) (α δ : MulAut L) (a b : ℕ)
    (hδp : δ ^ p = 1) (hδ : δ ∉ (MulAut.conj : L →* MulAut L).range)
    (hαδ : α * δ * α⁻¹ = δ ^ b) (hαc : ∀ c ∈ center L, c ^ p = 1 → α c = c ^ a) :
    (a : ZMod p) = b ∨ (b : ZMod p) = 1 := by
  obtain ⟨φ, hφ, hφπ⟩ := exists_cover_unitary hp hp5 hGA hL hZp hn hK e
  have hperf : Group.IsPerfect (StatedSU n (r ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  obtain ⟨ψ, hψ⟩ := l212in_aut_su_hom hn hK
  have hn1 : 1 ≤ n := by omega
  refine outDiag_core (n := n) hp hL hZne hZp hperf (QuotientGroup.mk' _) e φ hφπ hφ
    (l212in_suPhi hK) l212in_detU ?_ ?_ ?_ ?_ α δ a b hδp hδ hαδ hαc
  ·
    intro x y
    set γ := x * y * x⁻¹ * y⁻¹ with hγ
    have h1 : ψ γ = 1 := by
      rw [hγ, map_mul, map_mul, map_mul, map_inv, map_inv, l212in_ringAut_comm (ψ x) (ψ y),
        mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨B, hB, hrep⟩ := (hψ γ).1
    refine ⟨⟨B, (mem_Uid_iff _ _ _).2 hB⟩, ?_⟩
    ext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨hg, hγg⟩ := hrep g
    rw [hγg, l212in_suPhi_mk]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show B * (g : GL (Fin n) K) * B⁻¹ = B * glAut (ψ γ) (g : GL (Fin n) K) * B⁻¹
    rw [h1, map_one, MulAut.one_apply]
  ·
    intro B hB
    have hconj : ∀ g : StatedSU n (r ^ f) K,
        ∃ hg : (B : GL (Fin n) K) * (g : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ ∈
          StatedSU n (r ^ f) K,
        (QuotientGroup.mk ⟨_, hg⟩ : StatedProj (StatedSU n (r ^ f) K)) = QuotientGroup.mk g := by
      intro g
      refine ⟨l212in_conj_mem_statedSU hK B.2 g.2, ?_⟩
      have h1 : l212in_suPhi hK B (QuotientGroup.mk g) =
          (1 : MulAut (StatedProj (StatedSU n (r ^ f) K))) (QuotientGroup.mk g) := by rw [hB]
      rw [l212in_suPhi_mk, MulAut.one_apply] at h1
      exact h1
    obtain ⟨z, hz⟩ := l212in_conj_scalar_su hn hK B ((mem_Uid_iff _ _ _).1 B.2) hconj
    have hzu : z ^ (r ^ f + 1) = 1 := by
      refine l212in_scalar_unitary hn1 ?_
      rw [← hz]
      exact B.2
    refine ⟨⟨z, (mem_rootsOfUnity _ _).2 hzu⟩, ?_⟩
    apply Subtype.ext
    show GeneralLinearGroup.det (B : GL (Fin n) K) = z ^ n
    rw [hz, l212in_det_scalar]
  ·
    rintro B ⟨c, hc⟩
    have hc' : GeneralLinearGroup.det (B : GL (Fin n) K) = (c : Kˣ) ^ n := congrArg Subtype.val hc
    have hcu : (c : Kˣ) ^ (r ^ f + 1) = 1 := (mem_rootsOfUnity _ _).1 c.2
    have hsc : GeneralLinearGroup.scalar (Fin n) (c : Kˣ) ∈ Uid (unitaryInvolution K r f) n :=
      (l212in_scalar_mem_Uid_iff hn1 _).2 hcu
    have hB'U : (B : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹ ∈
        Uid (unitaryInvolution K r f) n := mul_mem B.2 (inv_mem hsc)
    have hB'S : (B : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹ ∈
        StatedSU n (r ^ f) K := by
      rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n]
      refine mem_SUid.2 ⟨?_, (mem_Uid_iff _ _ _).1 hB'U⟩
      have hdet : GeneralLinearGroup.det ((B : GL (Fin n) K) *
          (GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹) = 1 := by
        rw [map_mul, map_inv, l212in_det_scalar, hc', mul_inv_cancel]
      rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
    refine ⟨QuotientGroup.mk ⟨_, hB'S⟩, ?_⟩
    ext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, l212in_suPhi_mk]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    have hs : (GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹ * (g : GL (Fin n) K) *
        GeneralLinearGroup.scalar (Fin n) (c : Kˣ) = g := by
      rw [mul_assoc, l212in_scalar_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [l212in_suConj_coe, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv]
    calc _ = (B : GL (Fin n) K) * ((GeneralLinearGroup.scalar (Fin n) (c : Kˣ))⁻¹ * g *
          GeneralLinearGroup.scalar (Fin n) (c : Kˣ)) * (B : GL (Fin n) K)⁻¹ := by group
      _ = _ := by rw [hs]
  ·
    intro γ
    obtain ⟨σ, B, hB, hg⟩ := l212in_aut_su hn hK γ
    choose hmem hγ using hg
    obtain ⟨ρ, hρ⟩ := l212in_exists_zpow_units σ
    have hBU : B ∈ Uid (unitaryInvolution K r f) n := (mem_Uid_iff _ _ _).2 hB
    let Ã : StatedSU n (r ^ f) K →* StatedSU n (r ^ f) K :=
      { toFun := fun g => ⟨B * glAut σ (g : GL (Fin n) K) * B⁻¹, hmem g⟩
        map_one' := Subtype.ext (by
          show B * glAut σ (1 : GL (Fin n) K) * B⁻¹ = 1
          rw [map_one, mul_one, mul_inv_cancel])
        map_mul' := fun g h => Subtype.ext (by
          show B * glAut σ ((g : GL (Fin n) K) * (h : GL (Fin n) K)) * B⁻¹ =
            (B * glAut σ (g : GL (Fin n) K) * B⁻¹) * (B * glAut σ (h : GL (Fin n) K) * B⁻¹)
          rw [map_mul]
          group) }
    let t : Uid (unitaryInvolution K r f) n → Uid (unitaryInvolution K r f) n := fun B' =>
      ⟨B * glAut σ (B' : GL (Fin n) K) * B⁻¹,
        mul_mem (mul_mem hBU (l212in_glAut_mem_Uid σ B'.2)) (inv_mem hBU)⟩
    refine ⟨ρ, Ã, t, ?_, ?_, ?_, ?_⟩
    · intro s
      exact (hγ s).symm
    · intro s hs
      rw [QuotientGroup.ker_mk'] at hs
      obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hs
      apply Subtype.ext
      show B * glAut σ (s : GL (Fin n) K) * B⁻¹ = ((s ^ ρ : StatedSU n (r ^ f) K) : GL (Fin n) K)
      rw [Subgroup.coe_zpow, ← hc, l212in_glAut_scalar, l212in_conj_scalar, hρ,
        ← map_zpow (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) c ρ]
    · intro B'
      have key : γ * l212in_suPhi hK B' = l212in_suPhi hK (t B') * γ := by
        ext z
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
        rw [MulAut.mul_apply, MulAut.mul_apply, l212in_suPhi_mk, hγ, hγ g, l212in_suPhi_mk]
        refine congrArg QuotientGroup.mk (Subtype.ext ?_)
        show B * glAut σ ((B' : GL (Fin n) K) * (g : GL (Fin n) K) * (B' : GL (Fin n) K)⁻¹) * B⁻¹ =
          (B * glAut σ (B' : GL (Fin n) K) * B⁻¹) * (B * glAut σ (g : GL (Fin n) K) * B⁻¹) *
            (B * glAut σ (B' : GL (Fin n) K) * B⁻¹)⁻¹
        simp only [map_mul, map_inv]
        group
      exact mul_inv_eq_iff_eq_mul.2 key
    · intro B'
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      change GeneralLinearGroup.det (B * glAut σ (B' : GL (Fin n) K) * B⁻¹) =
        (GeneralLinearGroup.det (B' : GL (Fin n) K)) ^ ρ
      rw [map_mul, map_mul, map_inv, l212in_det_glAut, hρ, mul_right_comm, mul_inv_cancel,
        one_mul]

end Unitary

end CFSG.LocalAnalysis.RankFourTheoremC
