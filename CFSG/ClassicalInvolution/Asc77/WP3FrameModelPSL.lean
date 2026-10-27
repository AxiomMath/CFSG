module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameModel
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalLinear

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Signs

variable {K : Type} [Field K] {n : ℕ}

theorem commutator_blockSL_not_central (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) {e : SL(n, K)}
    (he : e ∈ signGroup K n) (hne : ent e ⟨0, by omega⟩ ≠ ent e ⟨1, by omega⟩) :
    e * blockSL K n 2 0 (by omega) transvec2 * e⁻¹ *
      (blockSL K n 2 0 (by omega) transvec2)⁻¹ ∉ Subgroup.center SL(n, K) := by
  intro hc
  rw [conj_blockSL_eq hn he, ← map_inv, ← map_mul] at hc
  obtain ⟨A, hA⟩ : ∃ A : SL(2, K), A = slConjugation 2 K (signGL2 (ent_mul_self he ⟨0, by omega⟩)
      (ent_mul_self he ⟨1, by omega⟩)) transvec2 * transvec2⁻¹ := ⟨_, rfl⟩
  rw [← hA] at hc
  have hAc : A ∈ Subgroup.center SL(2, K) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h1 := Subgroup.mem_center_iff.mp hc (blockSL K n 2 0 (by omega) s)
    apply blockSL_injective (K := K) (by omega : 0 + 2 ≤ n)
    rw [map_mul, map_mul]
    exact h1
  obtain ⟨r, -, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hAc
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hrA
  have ha := ent_cases he ⟨0, by omega⟩
  have hb := ent_cases he ⟨1, by omega⟩
  have hab : ent e ⟨0, by omega⟩ * ent e ⟨1, by omega⟩ = -1 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp_all
  simp only [hA, Matrix.SpecialLinearGroup.coe_mul, slConjugation_matrix, coe_signGL2,
    coe_signGL2_inv, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, coe_transvec2,
    Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1)] at h01
  simp [Matrix.mul_apply, Fin.sum_univ_two, hab] at h01
  rw [ent_mul_self he ⟨0, by omega⟩] at h01
  exact h2 (by linear_combination h01)

end Signs

section Chain

variable {F : Type} [Field F] {m : ℕ}

@[expose] noncomputable def monoSL (hn : 0 < m + 1) (σ : Equiv.Perm (Fin (m + 1))) : SL(m + 1, F) :=
  ⟨monoMat F σ, det_monoMat hn σ⟩

theorem coe_monoSL (hn : 0 < m + 1) (σ : Equiv.Perm (Fin (m + 1))) :
    ((monoSL (F := F) hn σ : SL(m + 1, F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      monoMat F σ := rfl

theorem monoSL_conj_zElt (hn : 0 < m + 1) (σ : Equiv.Perm (Fin (m + 1))) (T T' : Pair (m + 1))
    (hT : T'.1 = T.1.map σ.toEmbedding) :
    monoSL (F := F) hn σ * zElt F T * (monoSL (F := F) hn σ)⁻¹ = zElt F T' := by
  have hg : IsMonomialFor ((monoSL (F := F) hn σ : SL(m + 1, F)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) σ := isMonomialFor_monoMat σ
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_zElt, coe_zElt,
    hg.mul_zMat_mul_inv (coe_mul_coe_inv (monoSL (F := F) hn σ)), hT]

theorem chainPair_slModel (h2 : (2 : F) ≠ 0) (hm : 2 ≤ m) :
    ∃ (R₁ R₂ : Subgroup SL(m + 1, F)) (τ₁ τ₂ ν₁ ν₂ : SL(m + 1, F)),
      R₁ ∈ longRootSet (K := F) (by omega : 2 ≤ m + 1) ∧
      R₂ ∈ longRootSet (K := F) (by omega : 2 ≤ m + 1) ∧
      ChainPairData (longRootSet (K := F) (by omega : 2 ≤ m + 1)) R₁ R₂ τ₁ τ₂ ν₁ ν₂ := by
  have hn : 2 ≤ m + 1 := by omega
  have hn0 : 0 < m + 1 := by omega
  set a₀ : Fin (m + 1) := ⟨0, by omega⟩ with ha₀
  set a₁ : Fin (m + 1) := ⟨1, by omega⟩ with ha₁
  set a₂ : Fin (m + 1) := ⟨2, by omega⟩ with ha₂
  have h01 : a₀ ≠ a₁ := fun h => by simpa [ha₀, ha₁] using congrArg Fin.val h
  have h12 : a₁ ≠ a₂ := fun h => by simpa [ha₁, ha₂] using congrArg Fin.val h
  have h02 : a₀ ≠ a₂ := fun h => by simpa [ha₀, ha₂] using congrArg Fin.val h
  let T₂ : Pair (m + 1) := ⟨{a₀, a₁}, Finset.card_pair h01⟩
  let T₁ : Pair (m + 1) := ⟨{a₁, a₂}, Finset.card_pair h12⟩
  let T₃ : Pair (m + 1) := ⟨{a₀, a₂}, Finset.card_pair h02⟩
  have hR₁ : Lc F T₁ ∈ longRootSet (K := F) hn := Lc_mem_longRootSet h2 hn T₁
  have hR₂ : Lc F T₂ ∈ longRootSet (K := F) hn := Lc_mem_longRootSet h2 hn T₂
  have hU₁ := isUniqueInvolution_Lc h2 hn T₁
  have hU₂ := isUniqueInvolution_Lc h2 hn T₂
  have hcomm : zElt F T₁ * zElt F T₂ = zElt F T₂ * zElt F T₁ :=
    signGroup_comm (zElt_mem_signGroup T₁) (zElt_mem_signGroup T₂)
  have hprod : zElt F T₁ * zElt F T₂ = zElt F T₃ := by
    rw [hcomm]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact zMat_pair_mul h01 h12 h02
  have hsq₁ := zElt_mul_self (K := F) T₁
  have hsq₂ := zElt_mul_self (K := F) T₂
  refine ⟨Lc F T₁, Lc F T₂, zElt F T₁, zElt F T₂, monoSL hn0 (Equiv.swap a₀ a₂),
    monoSL hn0 (Equiv.swap a₀ a₁), hR₁, hR₂, ?_⟩
  have hLc₂ : Lc F T₂ = (blockSL F (m + 1) 2 0 (by omega)).range := by
    unfold Lc
    rw [range_blockSL_eq_longRootGroup h2 (by omega : 0 + 2 ≤ m + 1),
      negBlock_eq_zMat (by omega : 0 + 2 ≤ m + 1)]
  have hr : blockSL F (m + 1) 2 0 (by omega) transvec2 ∈ Lc F T₂ := by
    rw [hLc₂]
    exact ⟨_, rfl⟩
  have hent₁ : ent (zElt F T₁) a₀ ≠ ent (zElt F T₁) a₁ := by
    rw [zElt_ent, zElt_ent]
    simp only [T₁, Finset.mem_insert, Finset.mem_singleton, h01, h02, or_self, ite_false,
      true_or, ite_true]
    intro h
    exact h2 (by linear_combination h)
  have hent₁₂ : ent (zElt F T₁ * zElt F T₂) a₀ ≠ ent (zElt F T₁ * zElt F T₂) a₁ := by
    rw [ent_mul (zElt_mem_signGroup T₁) (zElt_mem_signGroup T₂),
      ent_mul (zElt_mem_signGroup T₁) (zElt_mem_signGroup T₂), zElt_ent, zElt_ent, zElt_ent,
      zElt_ent]
    simp only [T₁, T₂, Finset.mem_insert, Finset.mem_singleton, h01, h02, h12, true_or, or_true,
      or_self, ite_false, ite_true, mul_neg, neg_neg, mul_one]
    intro h
    exact h2 (by linear_combination -h)
  have hT1 : T₂.1 = T₁.1.map (Equiv.swap a₀ a₂).toEmbedding := by
    show ({a₀, a₁} : Finset (Fin (m + 1))) =
      Finset.map (Equiv.swap a₀ a₂).toEmbedding {a₁, a₂}
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_of_ne_of_ne h01.symm h12,
      Equiv.swap_apply_right]
    exact Finset.pair_comm _ _
  have hT1' : T₁.1 = T₂.1.map (Equiv.swap a₀ a₂).toEmbedding := by
    show ({a₁, a₂} : Finset (Fin (m + 1))) =
      Finset.map (Equiv.swap a₀ a₂).toEmbedding {a₀, a₁}
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_of_ne_of_ne h01.symm h12,
      Equiv.swap_apply_left]
    exact Finset.pair_comm _ _
  have hT2 : T₃.1 = T₁.1.map (Equiv.swap a₀ a₁).toEmbedding := by
    show ({a₀, a₂} : Finset (Fin (m + 1))) =
      Finset.map (Equiv.swap a₀ a₁).toEmbedding {a₁, a₂}
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm,
      Equiv.swap_apply_right]
  have hT2' : T₂.1 = T₂.1.map (Equiv.swap a₀ a₁).toEmbedding := by
    show ({a₀, a₁} : Finset (Fin (m + 1))) =
      Finset.map (Equiv.swap a₀ a₁).toEmbedding {a₀, a₁}
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact Finset.pair_comm _ _
  exact
    { mem₁ := hU₁.mem
      mem₂ := hU₂.mem
      center₁ := fun c hc hcc =>
        hU₁.unique c hc (mul_self_eq_one_of_mem_center_longRootSet hR₁ hc hcc)
      center₂ := fun c hc hcc =>
        hU₂.unique c hc (mul_self_eq_one_of_mem_center_longRootSet hR₂ hc hcc)
      sq₁ := hsq₁
      sq₂ := hsq₂
      comm := hcomm
      prod_not_central := by
        intro hcen
        refine commutator_blockSL_not_central h2 hn
          (mul_mem (zElt_mem_signGroup T₁) (zElt_mem_signGroup T₂)) hent₁₂ ?_
        have := Subgroup.mem_center_iff.mp hcen (blockSL F (m + 1) 2 0 (by omega) transvec2)
        have h1 : (zElt F T₁ * zElt F T₂) * blockSL F (m + 1) 2 0 (by omega) transvec2 *
            (zElt F T₁ * zElt F T₂)⁻¹ * (blockSL F (m + 1) 2 0 (by omega) transvec2)⁻¹ = 1 := by
          rw [← this]
          group
        rw [h1]
        exact one_mem _
      not_central := ⟨_, hr, commutator_blockSL_not_central h2 hn (zElt_mem_signGroup T₁) hent₁⟩
      swap₁ := monoSL_conj_zElt hn0 _ T₁ T₂ hT1
      swap₁' := monoSL_conj_zElt hn0 _ T₂ T₁ hT1'
      swap₂ := (monoSL_conj_zElt hn0 _ T₁ T₃ hT2).trans hprod.symm
      swap₂' := monoSL_conj_zElt hn0 _ T₂ T₂ hT2'
      gen := iSup_longRootSet_centralizing h2 hn hsq₁ hsq₂ hcomm }

end Chain

section Model

variable {K : Type*} [Group K]

theorem ChainPairData.mono {𝓕 𝓕' : Set (Subgroup K)} (h : 𝓕 ⊆ 𝓕') {R₁ R₂ : Subgroup K}
    {τ₁ τ₂ ν₁ ν₂ : K} (hd : ChainPairData 𝓕 R₁ R₂ τ₁ τ₂ ν₁ ν₂) :
    ChainPairData 𝓕' R₁ R₂ τ₁ τ₂ ν₁ ν₂ :=
  { hd with gen := hd.gen.trans (iSup₂_le fun R hR => le_iSup₂_of_le R (h hR) le_rfl) }

end Model

section PSL

variable {p : ℕ} [Fact p.Prime]

theorem chainPair_psl (hp2 : p ≠ 2) {m e : ℕ} (hm : 2 ≤ m) :
    ChainPair (Generic.fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m (GaloisField p e))) := by
  have h2 : (2 : GaloisField p e) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p e) p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)
  obtain ⟨R₁, R₂, τ₁, τ₂, ν₁, ν₂, hR₁, hR₂, hd⟩ := chainPair_slModel h2 hm
  have hsub := longRootSet_subset_fundamentalSubgroups_psl (F := GaloisField p e)
    (by omega : 2 ≤ m + 1)
  exact ⟨R₁, hsub hR₁, R₂, hsub hR₂, τ₁, τ₂, ν₁, ν₂, hd.mono hsub⟩

end PSL

end CFSG.ClassicalInvolution.Asc77
