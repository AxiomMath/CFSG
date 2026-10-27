module

public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.LieType.SteinbergBR.AltFiveGL3

open Equiv Equiv.Perm Subgroup CFSG.QuasithinUnique.Setup.Family
  CFSG.LieType.SteinbergBR.AutGL32

theorem congr_conj {E H : Type*} [Group E] [Group H] (e : E ≃* H) (z : E) :
    MulAut.congr e (MulAut.conj z) = MulAut.conj (e z) :=
  MulEquiv.ext fun x => by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]

@[expose] def v1 : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def v2 : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def c4 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3

theorem v1_mem : v1 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, v1, map_mul, sign_swap (by decide), sign_swap (by decide)]
  decide

theorem v2_mem : v2 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, v2, map_mul, sign_swap (by decide), sign_swap (by decide)]
  decide

theorem orderOf_v1 : orderOf v1 = 2 := orderOf_eq_prime (by decide) (by decide)

theorem orderOf_v2 : orderOf v2 = 2 := orderOf_eq_prime (by decide) (by decide)

theorem orderOf_c4 : orderOf c4 = 2 ^ 2 := orderOf_eq_prime_pow (by decide) (by decide)

theorem v1_mul_v2 : v1 * v2 = v2 * v1 := by decide

theorem v1_ne_v2 : v1 ≠ v2 := by decide

@[expose] noncomputable def autEquivPerm {E : Type*} [Group E] (e : E ≃* alternatingGroup (Fin 5)) :
    MulAut E ≃* Perm (Fin 5) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective (CFSG.Quasithin.SteinbergCB.conjPerm 5)
    ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num),
      CFSG.Quasithin.SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩).symm

theorem autEquivPerm_symm_eq_conj {E : Type*} [Group E] (e : E ≃* alternatingGroup (Fin 5))
    {σ : Perm (Fin 5)} (hσ : σ ∈ alternatingGroup (Fin 5)) :
    (autEquivPerm e).symm σ = MulAut.conj (e.symm ⟨σ, hσ⟩) := by
  apply (MulAut.congr e).injective
  rw [congr_conj, MulEquiv.apply_symm_apply, autEquivPerm, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  refine MulEquiv.ext fun g => Subtype.ext ?_
  change ((CFSG.Quasithin.SteinbergCB.conjPerm 5 σ g : alternatingGroup (Fin 5)) :
    Perm (Fin 5)) = _
  rw [CFSG.Quasithin.SteinbergCB.conjPerm_apply, MulAut.conj_apply]
  rfl

theorem nonempty_equiv_GL32 {E : Type} [Group E] (h : CFSG.Blueprint.LieModel E .PSL 3 2 1) :
    Nonempty (E ≃* GL32) := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := hc
    exact ⟨e.trans ((statedProjSL_equiv_of_card_two 3 K (by rw [hcard]; norm_num)).trans
      (slEquivGL 3))⟩
  all_goals exact absurd h0 (by norm_num)

theorem factorization_336 : (336 : ℕ).factorization 2 = 4 := by
  have h := ordProj_prime_pow_mul Nat.prime_two 4 (m := 21) (by norm_num)
  rw [show 2 ^ 4 * 21 = 336 by norm_num] at h
  exact Nat.pow_right_injective le_rfl h

end CFSG.LieType.SteinbergBR.AltFiveGL3

namespace CFSG.LieType

open Equiv Equiv.Perm Subgroup CFSG.QuasithinUnique.Setup.Family
  CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.AutGL32 CFSG.LieType.SteinbergBR.AltFiveGL3

theorem nq_Alt5_and_binary_GL3_full_automorphism_two_rank (E : Type) [Group E] [Finite E]
    (hE : Nonempty (E ≃* alternatingGroup (Fin 5)) ∨ CFSG.Blueprint.LieModel E .PSL 3 2 1) :
    (∀ D : Subgroup (MulAut E), (MulAut.conj : E →* MulAut E).range ≤ D →
      CFSG.pRank 2 D = 2) ∧
    (CFSG.Blueprint.LieModel E .PSL 3 2 1 →
      ∃ S : Sylow 2 (MulAut E), Nat.card S = 16 ∧ Nonempty (S ≃* DihedralGroup 8)) := by
  refine ⟨fun D hD => ?_, fun hL => ?_⟩
  · rcases hE with he | hL
    ·
      obtain ⟨e⟩ := he
      set Θ := autEquivPerm e
      have : Finite (MulAut E) := Finite.of_equiv _ Θ.symm.toEquiv
      have hcard : Nat.card (MulAut E) = 120 := by
        rw [Nat.card_congr Θ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      have hbound : ∀ A : Subgroup (MulAut E), IsElementaryAbelian 2 A → Nat.card A ≤ 2 ^ 2 :=
        fun A hA => card_le_sq_of_orderOf (g := Θ.symm c4) (k := 2)
          (by rw [MulEquiv.orderOf_eq, orderOf_c4]) (by rw [hcard]; norm_num) A
      refine pRank_two_eq_two_of D (x := Θ.symm v1) (y := Θ.symm v2) (hD ?_) (hD ?_)
        (by rw [MulEquiv.orderOf_eq, orderOf_v1]) (by rw [MulEquiv.orderOf_eq, orderOf_v2])
        (by rw [← map_mul, ← map_mul, v1_mul_v2]) (fun h => v1_ne_v2 (Θ.symm.injective h))
        hbound
      · exact ⟨e.symm ⟨v1, v1_mem⟩, (autEquivPerm_symm_eq_conj e v1_mem).symm⟩
      · exact ⟨e.symm ⟨v2, v2_mem⟩, (autEquivPerm_symm_eq_conj e v2_mem).symm⟩
    ·
      obtain ⟨e⟩ := nonempty_equiv_GL32 hL
      set Φ := MulAut.congr e
      have : Finite (MulAut E) := Finite.of_equiv _ Φ.symm.toEquiv
      have hcard : Nat.card (MulAut E) = 336 := by
        rw [Nat.card_congr Φ.toEquiv, card_mulAut_GL32]
      have hbound : ∀ A : Subgroup (MulAut E), IsElementaryAbelian 2 A → Nat.card A ≤ 2 ^ 2 :=
        fun A hA => card_le_sq_of_orderOf (g := Φ.symm alphaAut) (k := 3)
          (by rw [MulEquiv.orderOf_eq, orderOf_alphaAut]) (by rw [hcard]; norm_num) A
      have hΦ : ∀ z : GL32, Φ (MulAut.conj (e.symm z)) = MulAut.conj z := fun z => by
        rw [congr_conj, MulEquiv.apply_symm_apply]
      refine pRank_two_eq_two_of D (x := MulAut.conj (e.symm aGL))
        (y := MulAut.conj (e.symm bGL)) (hD ⟨_, rfl⟩) (hD ⟨_, rfl⟩) ?_ ?_ ?_ ?_ hbound
      · rw [← MulEquiv.orderOf_eq Φ, hΦ, orderOf_injective _ conj_injective,
          orderOf_eq_two_of_mul_self aGL_sq aGL_ne_one]
      · rw [← MulEquiv.orderOf_eq Φ, hΦ, orderOf_injective _ conj_injective,
          orderOf_eq_two_of_mul_self bGL_sq bGL_ne_one]
      · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, aGL_mul_bGL]
      · intro h
        have := congrArg Φ h
        rw [hΦ, hΦ] at this
        exact aGL_ne_bGL (conj_injective this)
  ·
    obtain ⟨e⟩ := nonempty_equiv_GL32 hL
    set Φ := MulAut.congr e
    have : Finite (MulAut E) := Finite.of_equiv _ Φ.symm.toEquiv
    have hcard : Nat.card (MulAut E) = 336 := by
      rw [Nat.card_congr Φ.toEquiv, card_mulAut_GL32]
    obtain ⟨eD⟩ := nonempty_closure_mulEquiv_dihedral
    set S₀ := closure ({alphaAut, betaAut} : Set (MulAut GL32))
    have hS : Nat.card (S₀.map Φ.symm.toMonoidHom) = 2 ^ (Nat.card (MulAut E)).factorization 2 := by
      rw [Subgroup.card_map_of_injective Φ.symm.injective, card_closure_alpha_beta, hcard,
        factorization_336]
      rfl
    refine ⟨Sylow.ofCard _ hS, ?_, ⟨(Φ.symm.subgroupMap S₀).symm.trans eD⟩⟩
    change Nat.card (S₀.map Φ.symm.toMonoidHom) = 16
    rw [Subgroup.card_map_of_injective Φ.symm.injective, card_closure_alpha_beta]

end CFSG.LieType
