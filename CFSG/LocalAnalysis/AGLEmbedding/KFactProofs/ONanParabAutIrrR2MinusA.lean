module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2MinusAOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2MinusATns
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2Pow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTorus

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section Tau

variable {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) (hn4 : 4 ≤ n) (b c : K)
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def mnTau : MulAut (matrixDerived (Qm n hn4 b c)) :=
  conjAct (Qm n hn4 b c) (frobPair n (by omega) b c (ne_zero_of_irreducible_tail b c hirr))

@[expose] noncomputable def mnTauE :
    MulAut (orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c))) :=
  MulAut.congr (mnPhi n hn4 b c hirr) (mnTau n hn4 b c hirr)

theorem mnTauE_rel (g : orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c)))
    (y : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) :
    (mnTauE n hn4 b c hirr g).val
        (mnFrob n (by omega) b c (ne_zero_of_irreducible_tail b c hirr) y) =
      mnFrob n (by omega) b c (ne_zero_of_irreducible_tail b c hirr) (g.val y) := by
  have h := mnPhi_conjAct n hn4 b c hirr ((mnPhi n hn4 b c hirr).symm g) y
  rw [MulEquiv.apply_symm_apply] at h
  rw [mnTauE, MulAut.congr_apply]
  exact h

theorem mnTauE_mem_tailFlagStab (g : orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c)))
    (hg : g.val ∈ tailFlagStab (n - 1) (minusTailForm K b c)) :
    (mnTauE n hn4 b c hirr g).val ∈ tailFlagStab (n - 1) (minusTailForm K b c) := by
  refine mem_tailFlagStab.2
    ⟨orthElementaryGroup_le _ (mnTauE n hn4 b c hirr g).2, fun i hi hir => ?_⟩
  exact mnMapTailFlag_of_rel n (by omega) b c (ne_zero_of_irreducible_tail b c hirr)
    (mnTauE_rel n hn4 b c hirr g) ((mem_tailFlagStab.1 hg).2 i hi hir)

theorem mnTauE_mem_tailBorel (g : orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c)))
    (hg : g.val ∈ tailBorel (n - 1) (minusTailForm K b c)) :
    (mnTauE n hn4 b c hirr g).val ∈ tailBorel (n - 1) (minusTailForm K b c) := by
  refine mem_tailBorel.2 ⟨(mnTauE n hn4 b c hirr g).2, fun i hi hir => ?_⟩
  exact mnMapTailFlag_of_rel n (by omega) b c (ne_zero_of_irreducible_tail b c hirr)
    (mnTauE_rel n hn4 b c hirr g) ((mem_tailBorel.1 hg).2 i hi hir)

theorem mnTauE_mem_tailUnipotent (g : orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c)))
    (hg : g.val ∈ tailUnipotent (n - 1) (minusTailForm K b c)) :
    (mnTauE n hn4 b c hirr g).val ∈ tailUnipotent (n - 1) (minusTailForm K b c) := by
  have hani := anisotropic_minusTailForm hirr
  have hb := ne_zero_of_irreducible_tail b c hirr
  obtain ⟨hf, h1⟩ := (mem_tailUnipotent_iff_ker hani).1 hg
  refine (mem_tailUnipotent_iff_ker hani).2 ⟨mnTauE_mem_tailFlagStab n hn4 b c hirr g hf, ?_⟩
  have hrel := mnTauE_rel n hn4 b c hirr g
  refine Prod.ext (funext fun i => ?_) (LinearMap.ext fun a' => ?_)
  · have e1 := mnStabDiag_fst_of_rel n (by omega) b c hb hrel i
    have e2 : (stabDiag g.val).1 i = 1 := congrFun (congrArg Prod.fst h1) i
    change (stabDiag (mnTauE n hn4 b c hirr g).val).1 i = 1
    rw [e1, e2, one_pow]
  · obtain ⟨a, rfl⟩ := tailA_surjective n (by omega) b c hb a'
    have e1 := mnStabDiag_snd_of_rel n (by omega) b c hb hrel a
    have e2 : (stabDiag g.val).2 = 1 := congrArg Prod.snd h1
    change (stabDiag (mnTauE n hn4 b c hirr g).val).2 (tailA b c a) = tailA b c a
    rw [e1, e2]
    rfl

end Tau

section Main

theorem mn_mem_iff_of_aut_mem {Y : Type*} [Group Y] [Finite Y] {S : Subgroup Y} {φ : MulAut Y}
    (hφ : ∀ w ∈ S, φ w ∈ S) (w : Y) : w ∈ S ↔ φ w ∈ S := by
  refine ⟨hφ w, fun hw => ?_⟩
  have hle : S.map φ.toMonoidHom ≤ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hφ z hz
  have heq : S.map φ.toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective φ.injective])
  rw [← heq] at hw
  obtain ⟨z, hz, hzw⟩ := hw
  have : z = w := φ.injective hzw
  rwa [← this]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem finite_tailEquiv (r : ℕ) :
    Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
  Finite.of_injective (fun g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
    ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) => (g : _ → _)) DFunLike.coe_injective

theorem autScalarTorus_minusE (n : ℕ) (hn4 : 4 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f) :
    AutScalarTorus (orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c))) := by
  have hn : 1 ≤ n := by omega
  have hb := ne_zero_of_irreducible_tail b c hirr
  have hr : 3 ≤ n - 1 := by omega
  have hani := anisotropic_minusTailForm hirr
  have hreg := nondegenerate_minusTailForm hirr
  have hm : Module.finrank K (Fin 2 → K) = 1 ∨ Module.finrank K (Fin 2 → K) = 2 :=
    Or.inr finrank_fin_two_fun
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin := finite_tailEquiv (K := K) (n - 1)
  obtain ⟨⟨S, hS⟩, hN, -⟩ :=
    orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hr hani hreg hm
  have hSτ : ∀ w, w ∈ (S : Subgroup (orthElementaryGroup (quadTail (n - 1)
      (minusTailForm K b c)))) ↔ mnTauE n hn4 b c hirr w ∈ (S : Subgroup (orthElementaryGroup
        (quadTail (n - 1) (minusTailForm K b c)))) := by
    rw [hS]
    refine mn_mem_iff_of_aut_mem (fun w hw => ?_)
    exact mnTauE_mem_tailUnipotent n hn4 b c hirr w hw
  obtain ⟨k₁, hk₁⟩ := tail_power_map n hn b c hb hirr hr fun g hg =>
    ⟨(mnTauE n hn4 b c hirr ⟨g, tailBorel_le hg⟩).val,
      mnTauE_mem_tailBorel n hn4 b c hirr ⟨g, tailBorel_le hg⟩ hg,
      mnTauE_rel n hn4 b c hirr ⟨g, tailBorel_le hg⟩⟩
  have hpow : ∀ b' ∈ Subgroup.normalizer ((S : Subgroup (orthElementaryGroup (quadTail (n - 1)
      (minusTailForm K b c)))) : Set _), mnTauE n hn4 b c hirr b' * (b' ^ k₁)⁻¹ ∈
        (S : Subgroup (orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c)))) := by
    intro b' hb'
    rw [hS] at hb' ⊢
    rw [hN] at hb'
    have hb'B : b'.val ∈ tailBorel (n - 1) (minusTailForm K b c) := hb'
    have hg'B := mnTauE_mem_tailBorel n hn4 b c hirr b' hb'B
    have hrel := mnTauE_rel n hn4 b c hirr b'
    have hkk := hk₁ b'.val hb'B (mnTauE n hn4 b c hirr b').val hg'B hrel
    have hgF : b'.val ∈ tailFlagStab (n - 1) (minusTailForm K b c) :=
      tailBorel_le_tailFlagStab hb'B
    have hg'F : (mnTauE n hn4 b c hirr b').val ∈ tailFlagStab (n - 1) (minusTailForm K b c) :=
      tailBorel_le_tailFlagStab hg'B
    rw [Subgroup.mem_subgroupOf]
    have hz : (mnTauE n hn4 b c hirr b' * (b' ^ k₁)⁻¹).val ∈
        tailFlagStab (n - 1) (minusTailForm K b c) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact mul_mem hg'F (inv_mem (pow_mem hgF k₁))
    refine (mem_tailUnipotent_iff_ker hani).2 ⟨hz, ?_⟩
    set B1 : tailFlagStab (n - 1) (minusTailForm K b c) := ⟨_, hg'F⟩ with hB1
    set B0 : tailFlagStab (n - 1) (minusTailForm K b c) := ⟨_, hgF⟩ with hB0
    have hzB : (⟨_, hz⟩ : tailFlagStab (n - 1) (minusTailForm K b c)) = B1 * (B0 ^ k₁)⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]; rfl)
    have hs : stabDiagHom (n - 1) (minusTailForm K b c) hani B1 =
        stabDiagHom (n - 1) (minusTailForm K b c) hani (B0 ^ k₁) := by
      rw [map_pow]
      exact hkk
    rw [hzB, map_mul, hs, ← map_mul, mul_inv_cancel, map_one]
  refine AutScalarTorus.of_decomp S ?_ ?_
  · intro b' hb' c' hc'
    rw [hS] at hb' hc' ⊢
    rw [hN] at hb' hc'
    rw [Subgroup.mem_subgroupOf]
    exact tail_commutator hirr hr hb' hc'
  · intro α _
    obtain ⟨k, hk⟩ := mn_aut_decomp n hn4 b c hirr hf (MulAut.congr (mnPhi n hn4 b c hirr).symm α)
    obtain ⟨y, hy⟩ := hk
    have hy' : MulAut.conj y = (mnTau n hn4 b c hirr ^ k)⁻¹ *
        MulAut.congr (mnPhi n hn4 b c hirr).symm α := hy
    have hαΓ : MulAut.congr (mnPhi n hn4 b c hirr).symm α = mnTau n hn4 b c hirr ^ k *
        MulAut.conj y := by
      rw [hy']
      group
    have hα : α = mnTauE n hn4 b c hirr ^ k * MulAut.conj (mnPhi n hn4 b c hirr y) := by
      have h1 : α = MulAut.congr (mnPhi n hn4 b c hirr)
          (MulAut.congr (mnPhi n hn4 b c hirr).symm α) :=
        DFunLike.ext _ _ fun x => by simp [MulAut.congr_apply]
      rw [h1, hαΓ, map_mul, map_pow, congr_conj]
      rfl
    obtain ⟨hS', hpow'⟩ := aut_pow_power_map hSτ hpow k
    refine ⟨(mnTauE n hn4 b c hirr ^ k) (mnPhi n hn4 b c hirr y), mnTauE n hn4 b c hirr ^ k,
      k₁ ^ k, ?_, hS', hpow'⟩
    rw [hα]
    have := aut_mul_conj_mul_inv (mnTauE n hn4 b c hirr ^ k) (mnPhi n hn4 b c hirr y)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this

end Main

section Model

open CFSG.Assembly.LowTwoRank

theorem autScalarTorus_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) : AutScalarTorus Y := by
  have hn4 : 4 ≤ n := h.1.2.2
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hQ := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  let eΓ : Y ≃* matrixDerived (Qm n hn4 b c) :=
    (coordinateMinusWitnessEquiv K (by omega) b c e).trans (derivedProjEquiv _ hQ).symm
  let eE : Y ≃* orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c)) :=
    eΓ.trans (mnPhi n hn4 b c hirr)
  have : Finite (orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c))) :=
    Finite.of_equiv Y eE.toEquiv
  exact AutScalarTorus.of_mulEquiv eE.symm (autScalarTorus_minusE n hn4 b c hirr hK)

end Model

end CFSG.AGLEmbedding.ParabAutIrr
