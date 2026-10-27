module

public import CFSG.GF2Type.Smith1979W3.Cert690.Statements
public import CFSG.GF2Type.Smith1979W3.T1216
public import CFSG.GF2Type.Smith1979W3.MbarModel
public import CFSG.LargeExtraspecial.AS35LMain
public import CFSG.LargeExtraspecial.S3cShult

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.GroupTheory.WeirSylow

private theorem finrank_V₀ : Module.finrank (ZMod 2) V₀ = 6 := by
  rw [Module.finrank_fin_fun]

private theorem card_V₀ : Nat.card V₀ = 64 := natCard_eq_sixtyFour (V := V₀) finrank_V₀

private theorem ncard_zero_qPlus : {v : V₀ | qPlus v = 0}.ncard = 36 := by
  have hc : {v : V₀ | qPlus v = 0} = {v : V₀ | qPlus v = 1}ᶜ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    rcases zmod2_eq_zero_or_eq_one (qPlus v) with h | h <;> simp [h]
  have h1 := Set.ncard_add_ncard_compl {v : V₀ | qPlus v = 1}
  rw [ncard_qPlus, ← hc, card_V₀] at h1
  omega

private theorem ncard_zero_qMinus : {v : V₀ | qMinus v = 0}.ncard = 28 := by
  have hc : {v : V₀ | qMinus v = 0} = {v : V₀ | qMinus v = 1}ᶜ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    rcases zmod2_eq_zero_or_eq_one (qMinus v) with h | h <;> simp [h]
  have h1 := Set.ncard_add_ncard_compl {v : V₀ | qMinus v = 1}
  rw [ncard_qMinus, ← hc, card_V₀] at h1
  omega

private theorem card_orthogonalGroup_of_ncard_zero {Q : QuadraticForm (ZMod 2) V₀}
    (hQ : Q.polarBilin.Nondegenerate) (h : {v : V₀ | Q v = 0}.ncard = 36) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 40320 := by
  have h1 := S12DW.card_orthogonalGroup_mul_ncard_eq (V := V₀) (Q := Q) hQ (m := 3)
    (by rw [finrank_V₀])
  rw [h] at h1
  have h2 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
  rw [h2] at h1
  omega

private theorem card_orthogonalGroup_of_ncard_zero' {Q : QuadraticForm (ZMod 2) V₀}
    (hQ : Q.polarBilin.Nondegenerate) (h : {v : V₀ | Q v = 0}.ncard = 28) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 51840 := by
  have h1 := S12DW.card_orthogonalGroup_mul_ncard_eq (V := V₀) (Q := Q) hQ (m := 3)
    (by rw [finrank_V₀])
  rw [h] at h1
  have h2 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
  rw [h2] at h1
  omega

private theorem card_O₀_false : Nat.card (O₀ false) = 40320 := by
  refine card_orthogonalGroup_of_ncard_zero (Q := qModel false) (qModel_nondegenerate false) ?_
  rw [qModel_false]
  exact ncard_zero_qPlus

private theorem card_O₀_true : Nat.card (O₀ true) = 51840 := by
  refine card_orthogonalGroup_of_ncard_zero' (Q := qModel true) (qModel_nondegenerate true) ?_
  rw [qModel_true]
  exact ncard_zero_qMinus

private theorem card_Ω₀_false : Nat.card (Ω₀ false) = 20160 := by
  have h := S12DW.card_orthogonalGroup_eq (Q := qModel false) (qModel_nondegenerate false)
  rw [card_O₀_false] at h
  change Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (qModel false)
    (qModel_nondegenerate false)) = 20160
  omega

private theorem card_Ω₀_true : Nat.card (Ω₀ true) = 25920 := by
  have h := S12DW.card_orthogonalGroup_eq (Q := qModel true) (qModel_nondegenerate true)
  rw [card_O₀_true] at h
  change Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (qModel true)
    (qModel_nondegenerate true)) = 25920
  omega

private theorem not_isPlusType_qMinus : ¬ IsPlusType qMinus := by
  intro hp
  have h1 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup qMinus) : ℤ) = 40320 := by
    have h := natCard_orthogonalGroup_of_type (K := ZMod 2) (V := V₀) (Q := qMinus)
      qMinus_nondegenerate (m := 2) (by rw [finrank_V₀]) (ε := 1) (Or.inl ⟨rfl, hp⟩)
    rw [Nat.card_zmod] at h
    norm_num [Finset.prod_Icc_succ_top] at h ⊢
    exact h
  have h2 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup qMinus) = 51840 := card_O₀_true
  omega

private theorem isPlusType_of_qtPlusType {G : Type*} [Group G] [Finite G] (S : Setting G)
    (L : S.Qt ≃ₗ[ZMod 2] V₀) {Q : QuadraticForm (ZMod 2) V₀}
    (hL : ∀ v, Q (L v) = S.q v) (hdim : Module.finrank (ZMod 2) S.Qt = 6)
    (hp : QtPlusType S) : IsPlusType Q := by
  obtain ⟨W, hW, hWs⟩ := hp
  refine ⟨W.map (L : S.Qt →ₗ[ZMod 2] V₀), ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hW, hdim, finrank_V₀]
  · rintro _ ⟨w, hw, rfl⟩
    simpa using (hL w).trans (hWs w hw)

theorem qtPlusType_of_qPlus {G : Type*} [Group G] [Finite G] (S : Setting G)
    (L : S.Qt ≃ₗ[ZMod 2] V₀) (hL : ∀ v, qPlus (L v) = S.q v)
    (hdim : Module.finrank (ZMod 2) S.Qt = 6) : QtPlusType S := by
  obtain ⟨W, hW, hWs⟩ := isPlus_of_qPlus L hL
  exact ⟨W, by rw [hW, hdim], hWs⟩

theorem not_qtPlusType_of_qMinus {G : Type*} [Group G] [Finite G] (S : Setting G)
    (L : S.Qt ≃ₗ[ZMod 2] V₀) (hL : ∀ v, qMinus (L v) = S.q v)
    (hdim : Module.finrank (ZMod 2) S.Qt = 6) : ¬ QtPlusType S :=
  fun hp => not_isPlusType_qMinus (isPlusType_of_qtPlusType S L hL hdim hp)

theorem exists_isometry_qPlus {G : Type*} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 3) (hp : QtPlusType S) :
    ∃ L : S.Qt ≃ₗ[ZMod 2] V₀, ∀ v, qPlus (L v) = S.q v := by
  have hdim : Module.finrank (ZMod 2) S.Qt = 6 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  obtain ⟨L, hL | hL⟩ := exists_linearEquiv_model (V := S.Qt) (Q := S.q) hdim S.q_nondegenerate
  · exact ⟨L, hL⟩
  · exact absurd hp (not_qtPlusType_of_qMinus S L hL hdim)

private theorem clSub_inf_Qa_sq {G : Type*} [Group G] [Finite G] (S : Setting G) {g : G}
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), S.q v = 0 := by
  intro v hv
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.q_cl_eq_zero_iff hxQ]
  exact S.QG_inf_Qa_sq hne hx

private theorem finrank_clSub_inf_Qa_le_three {G : Type*} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 3) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) ≤ 3 := by
  have h := finrank_le_of_totallySingular (q := S.q) S.q_nondegenerate (n := S.width)
    S.finrank_Qt_eq_two_mul_width (clSub_inf_Qa_sq S hne)
  rw [hw] at h
  exact h

private theorem finrank_clSub_inf_Qa_le_two {G : Type*} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 3) (hnot : ¬ QtPlusType S) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) ≤ 2 := by
  have h3 := finrank_clSub_inf_Qa_le_three S hw haQ hne
  by_contra h
  have hle : 3 ≤ Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) := by omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2)
    (M := S.clSub (S.QG ⊓ S.Qa g)) (n := 3) hle
  let W' : Submodule (ZMod 2) S.Qt :=
    (Submodule.span (ZMod 2) (Set.range v)).map (S.clSub (S.QG ⊓ S.Qa g)).subtype
  have hdim : Module.finrank (ZMod 2) W' = 3 := by
    dsimp only [W']
    rw [Submodule.finrank_map_subtype_eq, finrank_span_eq_card hv, Fintype.card_fin]
  have hW'le : W' ≤ S.clSub (S.QG ⊓ S.Qa g) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hsing : ∀ x ∈ W', S.q x = 0 := fun x hx => clSub_inf_Qa_sq S hne x (hW'le hx)
  exact hnot ⟨W', by rw [hdim, S.finrank_Qt_eq_two_mul_width, hw], hsing⟩

private theorem card_QG_inf_Qa {G : Type*} [Group G] [Finite G] (S : Setting G) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card ↥(S.QG ⊓ S.Qa g) = 2 * Nat.card ↥(S.clSub (S.QG ⊓ S.Qa g)) := by
  have hX : S.QG ⊓ S.Qa g ≤ S.QG := inf_le_left
  have hz : S.z ∈ S.QG ⊓ S.Qa g := ⟨S.z_mem_QG, S.z_mem_Qa haQ hne⟩
  calc Nat.card ↥(S.QG ⊓ S.Qa g) = Nat.card ↥(S.clPre (S.clSub (S.QG ⊓ S.Qa g))) := by
        rw [S.clPre_clSub hX hz]
    _ = 2 * Nat.card ↥(S.clSub (S.QG ⊓ S.Qa g)) := S.card_clPre _

private theorem card_QG_inf_Qa_le_sixteen {G : Type*} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 3) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : Nat.card ↥(S.QG ⊓ S.Qa g) ≤ 16 := by
  have hdim := finrank_clSub_inf_Qa_le_three S hw haQ hne
  have hcard := card_QG_inf_Qa S haQ hne
  have hW : Nat.card ↥(S.clSub (S.QG ⊓ S.Qa g)) =
      2 ^ Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) := S.card_submodule _
  rw [hcard, hW]
  calc 2 * 2 ^ Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g))
      ≤ 2 * 2 ^ 3 := Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 16 := by norm_num

private theorem card_QG_inf_Qa_le_eight {G : Type*} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 3) (hnot : ¬ QtPlusType S) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : Nat.card ↥(S.QG ⊓ S.Qa g) ≤ 8 := by
  have hdim := finrank_clSub_inf_Qa_le_two S hw hnot haQ hne
  have hcard := card_QG_inf_Qa S haQ hne
  have hW : Nat.card ↥(S.clSub (S.QG ⊓ S.Qa g)) =
      2 ^ Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) := S.card_submodule _
  rw [hcard, hW]
  calc 2 * 2 ^ Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g))
      ≤ 2 * 2 ^ 2 := Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 8 := by norm_num

private theorem four_le_card_Lbar {G : Type*} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 3) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : 4 ≤ Nat.card ↥(S.Lbar g) := by
  have hX := card_QG_inf_Qa_le_sixteen S hw haQ hne
  have hprod := S.card_Lbar_mul g
  have hL0 := S.card_L0 haQ hne
  by_contra h
  have hle : Nat.card ↥(S.Lbar g) ≤ 3 := by omega
  have h1 : Nat.card ↥(S.Lbar g) * Nat.card ↥(S.QG ⊓ S.Qa g) ≤ 3 * 16 :=
    Nat.mul_le_mul hle hX
  rw [hprod, hL0, hw] at h1
  norm_num at h1

private theorem eight_le_card_Lbar {G : Type*} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 3) (hnot : ¬ QtPlusType S) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : 8 ≤ Nat.card ↥(S.Lbar g) := by
  have hX := card_QG_inf_Qa_le_eight S hw hnot haQ hne
  have hprod := S.card_Lbar_mul g
  have hL0 := S.card_L0 haQ hne
  by_contra h
  have hle : Nat.card ↥(S.Lbar g) ≤ 7 := by omega
  have h1 : Nat.card ↥(S.Lbar g) * Nat.card ↥(S.QG ⊓ S.Qa g) ≤ 7 * 8 :=
    Nat.mul_le_mul hle hX
  rw [hprod, hL0, hw] at h1
  norm_num at h1

theorem mbarModel_normal_two_eq_bot {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (L : S.Qt ≃ₗ[ZMod 2] V₀) (N : Subgroup (V₀ ≃ₗ[ZMod 2] V₀))
    (hNH : N ≤ mbarModel S L)
    (hN : ∀ h ∈ mbarModel S L, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  let φ : S.O →* (V₀ ≃ₗ[ZMod 2] V₀) := (conjL L).toMonoidHom.comp S.O.subtype
  have hφinj : Function.Injective φ :=
    (conjL L).injective.comp S.O.subtype_injective
  have hmodel : mbarModel S L = S.Mbar.map φ := by
    rw [mbarModel, Subgroup.map_map]
  let N' : Subgroup S.O := N.comap φ
  have hN'le : N' ≤ S.Mbar := by
    intro x hx
    have h1 : φ x ∈ S.Mbar.map φ := by
      rw [← hmodel]
      exact hNH hx
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp h1
    rw [← hφinj hmx]
    exact hm
  have hN'norm : S.Mbar ≤ Subgroup.normalizer (N' : Set S.O) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      change φ (m * x * m⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hN (φ m) (by rw [hmodel]; exact Subgroup.mem_map_of_mem φ hm) (φ x) hx
    · intro hx
      change φ x ∈ N
      have h1 : (φ m)⁻¹ * φ (m * x * m⁻¹) * ((φ m)⁻¹)⁻¹ ∈ N :=
        hN ((φ m)⁻¹) (by rw [hmodel]; exact Subgroup.inv_mem _ (Subgroup.mem_map_of_mem φ hm))
          (φ (m * x * m⁻¹)) hx
      have h2 : (φ m)⁻¹ * φ (m * x * m⁻¹) * ((φ m)⁻¹)⁻¹ = φ x := by
        rw [map_mul, map_mul, map_inv]
        group
      rwa [h2] at h1
  have hN'2 : IsPGroup 2 N' := by
    intro x
    obtain ⟨k, hk⟩ := h2 ⟨φ x, x.2⟩
    have hk' : (φ x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, Subtype.ext (hφinj ?_)⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, hk', map_one]
  have hbot := S.eq_bot_of_normalized_L hN'le hN'norm hN'2
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp (by rw [← hmodel]; exact hNH hn)
  have hxN : x ∈ N' := by
    change φ x ∈ N
    rw [hx]
    exact hn
  rw [hbot, Subgroup.mem_bot] at hxN
  rw [← hx, hxN, map_one]

theorem mbarModel_irreducible {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (L : S.Qt ≃ₗ[ZMod 2] V₀) (hirr : ¬ S.IsReducible)
    (W : Submodule (ZMod 2) V₀) (hW : ∀ h ∈ mbarModel S L, ∀ w ∈ W, h w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  let W' : Submodule (ZMod 2) S.Qt := W.comap (L : S.Qt →ₗ[ZMod 2] V₀)
  have hInv : ∀ m : S.M, ∀ v ∈ W', (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W' := by
    intro m v hv
    change L (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ∈ W
    have h1 : conjL L ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (L v) =
        L (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      rw [conjL_apply, LinearEquiv.symm_apply_apply]
    rw [← h1]
    exact hW _ (conjL_ρ_mem_mbarModel S L m) _ hv
  have hW' : W' = ⊥ ∨ W' = ⊤ := by
    by_contra h
    exact hirr ⟨W', fun hbot => h (Or.inl hbot), fun htop => h (Or.inr htop), hInv⟩
  have hmap : W'.map (L : S.Qt →ₗ[ZMod 2] V₀) = W := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨L.symm x, ?_, by simp⟩
      change L (L.symm x) ∈ W
      simpa using hx
  rcases hW' with h | h
  · left
    rw [← hmap, h, Submodule.map_bot]
  · right
    rw [← hmap, h, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr L.surjective


theorem censusCond_conj {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G)
    (L : S.Qt ≃ₗ[ZMod 2] V₀) (minus : Bool) (hw : S.width = 3)
    (hL : ∀ v, qModel minus (L v) = S.q v) (hminus : minus = true ↔ ¬ QtPlusType S) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    L (S.cl (g * S.z * g⁻¹)) ≠ 0 ∧ qModel minus (L (S.cl (g * S.z * g⁻¹))) = 0 ∧
      Cert690.CensusCond minus (mbarModel S L)
        (((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom) (L (S.cl (g * S.z * g⁻¹))) := by
  have hb0 : S.cl (g * S.z * g⁻¹) ≠ 0 := S.cl_conj_z_ne_zero haQ hne
  have hq0 : S.q (S.cl (g * S.z * g⁻¹)) = 0 := S.q_cl_conj_z haQ
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hb0 (L.injective (by rw [h, map_zero]))
  · rw [hL, hq0]
  · let φ : S.O →* (V₀ ≃ₗ[ZMod 2] V₀) := (conjL L).toMonoidHom.comp S.O.subtype
    have hφinj : Function.Injective φ :=
      (conjL L).injective.comp S.O.subtype_injective
    have hH : mbarModel S L = S.Mbar.map φ := by
      rw [mbarModel, Subgroup.map_map]
    have hLm : ((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom =
        (S.Lbar g).map φ := by
      rw [Subgroup.map_map]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hLm, hH]
      exact Subgroup.map_mono (S.Lbar_le_Mbar g)
    · intro x hx
      rw [hLm] at hx
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
      have hφt : φ t = conjL L ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := rfl
      rw [hφt, conjL_apply, LinearEquiv.symm_apply_apply, S.s12_Lbar_apply_cl_a haQ ht]
    · intro x hx
      rw [hLm] at hx
      haveI : IsElementaryAbelian 2 ↥(S.Lbar g) := S.isElementaryAbelian_Lbar haQ
      haveI : IsElementaryAbelian 2 ↥((S.Lbar g).map φ) := IsElementaryAbelian.map φ
      have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
      simpa [pow_two] using h2
    · have hcard : Nat.card (((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom) =
          Nat.card ↥(S.Lbar g) := by
        rw [Subgroup.card_map_of_injective (conjL L).injective,
          Subgroup.card_map_of_injective S.O.subtype_injective]
      rw [hcard]
      cases minus with
      | false => simpa using four_le_card_Lbar (S := S) hw haQ hne
      | true =>
          have hnot : ¬ QtPlusType S := hminus.mp rfl
          simpa using eight_le_card_Lbar (S := S) hw hnot haQ hne
    · intro h hh
      rw [hH] at hh
      obtain ⟨m, hmM, rfl⟩ := Subgroup.mem_map.mp hh
      have hnorm : φ m ∈ Subgroup.normalizer
          (((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom :
            Set (V₀ ≃ₗ[ZMod 2] V₀)) ↔ m ∈ Subgroup.normalizer (S.Lbar g : Set S.O) := by
        rw [hLm, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
        have h2 : ∀ u : S.O, φ m * φ u * (φ m)⁻¹ = φ (m * u * m⁻¹) := by
          intro u
          rw [map_mul, map_mul, map_inv]
        constructor
        · intro hN u
          constructor
          · intro hu
            have h1 := (hN (φ u)).mp (Subgroup.mem_map_of_mem φ hu)
            rw [h2 u, Subgroup.mem_map_iff_mem hφinj] at h1
            exact h1
          · intro hu
            have h1 : φ (m * u * m⁻¹) ∈ (S.Lbar g).map φ :=
              Subgroup.mem_map_of_mem φ hu
            rw [← h2 u] at h1
            exact (Subgroup.mem_map_iff_mem hφinj).mp ((hN (φ u)).mpr h1)
        · intro hN x
          constructor
          · intro hx
            obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
            have h1 : m * u * m⁻¹ ∈ S.Lbar g := (hN u).mp hu
            rw [h2 u]
            exact Subgroup.mem_map_of_mem φ h1
          · intro hx
            obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp hx
            refine ⟨m⁻¹ * u * m, ?_, ?_⟩
            · have hm : m⁻¹ ∈ Subgroup.normalizer (S.Lbar g : Set S.O) := inv_mem hN
              exact (Subgroup.mem_normalizer_iff.mp hm u).mp hu
            · rw [map_mul, map_mul, map_inv, hu']
              group
      have hee : φ m (L (S.cl (g * S.z * g⁻¹))) = L (S.cl (g * S.z * g⁻¹)) ↔
          ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
            S.cl (g * S.z * g⁻¹) := by
        have hφm : φ m = conjL L ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := rfl
        rw [hφm, conjL_apply, LinearEquiv.symm_apply_apply]
        exact ⟨fun h => L.injective h, fun h => by rw [h]⟩
      rw [hnorm, hee]
      rw [show S.Mbar = S.ρ.range from rfl] at hmM
      obtain ⟨y, hy⟩ := hmM
      rw [← hy]
      exact S.timmesfeld_12_4_1 haQ hne (by omega) y
    · intro y
      obtain ⟨hyH, hyC⟩ := y.2
      have hyH' : y.val ∈ S.Mbar.map φ := hH ▸ hyH
      obtain ⟨m, hmM, hm⟩ := Subgroup.mem_map.mp hyH'
      have hyC0 : y.val ∈ Subgroup.centralizer
          (((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom :
            Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
        rw [← Subgroup.mem_toSubmonoid]
        exact hyC
      rw [Subgroup.mem_centralizer_iff] at hyC0
      have hmC : m ∈ Subgroup.centralizer (S.Lbar g : Set S.O) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have h1 := hyC0 (φ u) (by rw [hLm]; exact Subgroup.mem_map_of_mem φ hu)
        rw [← hm] at h1
        refine hφinj ?_
        rw [map_mul, map_mul]
        exact h1
      obtain ⟨k, hk⟩ := S.timmesfeld_12_4_2 haQ hne (by omega) ⟨m, hmM, hmC⟩
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : m ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      change y.val ^ 2 ^ k = 1
      rw [← hm]
      rw [← map_pow, hk', map_one]

theorem exists_isTypeA_mem {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G)
    (L : S.Qt ≃ₗ[ZMod 2] V₀) (minus : Bool) (hL : ∀ v, qModel minus (L v) = S.q v) {g : G}
    (h : S.HasTypeAInL g) :
    ∃ t ∈ ((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom,
      IsTypeA (qModel minus) t 2 := by
  obtain ⟨α, hαLa, hαQ, hα⟩ := h
  have hα' : IsTypeA S.q ((S.ρ α : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := hα
  have hρα : S.ρ α ∈ S.Lbar g := by
    rw [← S.map_La_eq_Lbar g]
    exact Subgroup.mem_map.mpr ⟨α, hαLa, rfl⟩
  refine ⟨conjL L (S.ρ α : S.Qt ≃ₗ[ZMod 2] S.Qt), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨S.ρ α, hρα, rfl⟩, rfl⟩
  · intro v
    rw [conjL_apply, hL, hα'.1, ← hL (L.symm v), LinearEquiv.apply_symm_apply]
  · intro h1
    have h2 : ((S.ρ α : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
      simpa using congrArg (conjL L).symm h1
    exact hαQ ((S.ρ_eq_one_iff α).mp (Subtype.ext h2))
  · have h2 : ((S.ρ α : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        ((S.ρ α : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := hα'.2.2.1
    show conjL L (S.ρ α : S.Qt ≃ₗ[ZMod 2] S.Qt) *
      conjL L (S.ρ α : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1
    rw [← map_mul, h2, map_one]
  · rw [finrank_commSpace_conjL]
    exact hα'.2.2.2.1
  · intro x hx
    rw [commSpace_conjL] at hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    simpa using (hL y).trans (hα'.2.2.2.2 y hy)

private theorem card_mbarModel_of_conj_KPGL {G : Type} [Group G] [Finite G] (S : Setting G)
    (L : S.Qt ≃ₗ[ZMod 2] V₀) {k : V₀ ≃ₗ[ZMod 2] V₀}
    (hk : ∀ x, x ∈ mbarModel S L ↔ k⁻¹ * x * k ∈ Cert690.KPGL)
    (hcard : Nat.card Cert690.KPGL = 336) : Nat.card (mbarModel S L) = 336 := by
  have hmap : (mbarModel S L).map (MulAut.conj k⁻¹).toMonoidHom = Cert690.KPGL := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hk y).mp hy
    · intro hx
      refine ⟨k * x * k⁻¹, (hk (k * x * k⁻¹)).mpr ?_, ?_⟩
      · simpa [mul_assoc] using hx
      · simp [MulAut.conj_apply, mul_assoc]
  have h1 : Nat.card (mbarModel S L) = Nat.card Cert690.KPGL := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective).symm
  rw [h1, hcard]

private theorem censusPlus_mbarModel {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 3) (hirr : ¬ S.IsReducible)
    (hb : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g)
    (L : S.Qt ≃ₗ[ZMod 2] V₀) (hL : ∀ v, qPlus (L v) = S.q v)
    (hP : Cert690.CensusPlusProp) :
    mbarModel S L = Ω₀ false ∨ mbarModel S L = O₀ false ∨
      ∃ k ∈ O₀ false, ∀ x, x ∈ mbarModel S L ↔ k⁻¹ * x * k ∈ Cert690.KPGL := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) S.Qt = 6 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hhL : ∀ v, qModel false (L v) = S.q v := hL
  have hplus : QtPlusType S := qtPlusType_of_qPlus S L hL hdim
  have hminus : (false = true) ↔ ¬ QtPlusType S :=
    ⟨fun h => absurd h (by decide), fun h => absurd hplus h⟩
  have hHle : mbarModel S L ≤ O₀ false := mbarModel_le_O₀ S L hhL
  have hO2 : ∀ N : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), N ≤ mbarModel S L →
      (∀ h ∈ mbarModel S L, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N → N = ⊥ :=
    fun N hN1 hN2 hN3 => mbarModel_normal_two_eq_bot S L N hN1 hN2 hN3
  have hIrr := mbarModel_irreducible S L hirr
  have hb' := hb
  obtain ⟨g, hgQ, hgne, hgA⟩ := hb'
  obtain ⟨he0, heq, hcond⟩ := censusCond_conj S L false hw hhL hminus hgQ hgne
  obtain ⟨t, htmem, htA⟩ := exists_isTypeA_mem S L false hhL hgA
  exact hP (mbarModel S L) hHle hO2 hIrr
    ⟨L (S.cl (g * S.z * g⁻¹)), he0, heq,
      ⟨((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom, hcond, t, htmem, htA⟩⟩

private theorem censusMinus_mbarModel {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 3) (hirr : ¬ S.IsReducible)
    (hb : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g)
    (L : S.Qt ≃ₗ[ZMod 2] V₀) (hL : ∀ v, qMinus (L v) = S.q v)
    (hM : Cert690.CensusMinusProp) : mbarModel S L = Ω₀ true ∨ mbarModel S L = O₀ true := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) S.Qt = 6 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hhL : ∀ v, qModel true (L v) = S.q v := hL
  have hnot : ¬ QtPlusType S := not_qtPlusType_of_qMinus S L hL hdim
  have hminus : (true = true) ↔ ¬ QtPlusType S := ⟨fun _ => hnot, fun _ => rfl⟩
  have hHle : mbarModel S L ≤ O₀ true := mbarModel_le_O₀ S L hhL
  have hO2 : ∀ N : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), N ≤ mbarModel S L →
      (∀ h ∈ mbarModel S L, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N → N = ⊥ :=
    fun N hN1 hN2 hN3 => mbarModel_normal_two_eq_bot S L N hN1 hN2 hN3
  have hIrr := mbarModel_irreducible S L hirr
  have hb' := hb
  obtain ⟨g, hgQ, hgne, hgA⟩ := hb'
  obtain ⟨he0, heq, hcond⟩ := censusCond_conj S L true hw hhL hminus hgQ hgne
  obtain ⟨t, htmem, htA⟩ := exists_isTypeA_mem S L true hhL hgA
  exact hM (mbarModel S L) hHle hO2 hIrr
    ⟨L (S.cl (g * S.z * g⁻¹)), he0, heq,
      ⟨((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom, hcond, t, htmem, htA⟩⟩

theorem t1216W3Census_of (hP : Cert690.CensusPlusProp) (hM : Cert690.CensusMinusProp)
    (hF : Cert690.PGLFactsProp) : T1216W3Census := by
  intro G _ _ _ S hw hirr hb
  have hdim : Module.finrank (ZMod 2) S.Qt = 6 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  obtain ⟨L, hL | hL⟩ := exists_linearEquiv_model (V := S.Qt) (Q := S.q) hdim S.q_nondegenerate
  · have hplus : QtPlusType S := qtPlusType_of_qPlus S L hL hdim
    refine Or.inl ⟨hplus, ?_⟩
    rcases censusPlus_mbarModel S hw hirr hb L hL hP with hΩ | hO | ⟨k, hkO, hk⟩
    · exact Or.inr (Or.inl (by rw [← card_mbarModel S L, hΩ]; exact card_Ω₀_false))
    · exact Or.inr (Or.inr (by rw [← card_mbarModel S L, hO]; exact card_O₀_false))
    · exact Or.inl (by rw [← card_mbarModel S L]; exact card_mbarModel_of_conj_KPGL S L hk hF.2.1)
  · have hnot : ¬ QtPlusType S := not_qtPlusType_of_qMinus S L hL hdim
    refine Or.inr ⟨hnot, ?_⟩
    rcases censusMinus_mbarModel S hw hirr hb L hL hM with hΩ | hO
    · exact Or.inl (by rw [← card_mbarModel S L, hΩ]; exact card_Ω₀_true)
    · exact Or.inr (by rw [← card_mbarModel S L, hO]; exact card_O₀_true)

theorem exists_mbarModel_eq_KPGL (hP : Cert690.CensusPlusProp) (hF : Cert690.PGLFactsProp)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (hw : S.width = 3)
    (hirr : ¬ S.IsReducible)
    (hb : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g)
    (h336 : Nat.card S.Mbar = 336) :
    ∃ L : S.Qt ≃ₗ[ZMod 2] V₀, (∀ v, qModel false (L v) = S.q v) ∧
      mbarModel S L = Cert690.KPGL := by
  have hdim : Module.finrank (ZMod 2) S.Qt = 6 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  obtain ⟨L, hL | hL⟩ := exists_linearEquiv_model (V := S.Qt) (Q := S.q) hdim S.q_nondegenerate
  · rcases censusPlus_mbarModel S hw hirr hb L hL hP with hΩ | hO | ⟨k, hkO, hk⟩
    · exfalso
      have hc : Nat.card (mbarModel S L) = 20160 := by rw [hΩ]; exact card_Ω₀_false
      rw [card_mbarModel, h336] at hc
      norm_num at hc
    · exfalso
      have hc : Nat.card (mbarModel S L) = 40320 := by rw [hO]; exact card_O₀_false
      rw [card_mbarModel, h336] at hc
      norm_num at hc
    · refine ⟨L.trans k.symm, ?_, ?_⟩
      · intro v
        have hhL : ∀ v, qModel false (L v) = S.q v := hL
        have h1 : qModel false (L v) = qModel false (k.symm (L v)) := by
          have h0 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hkO (k.symm (L v))
          rwa [k.apply_symm_apply] at h0
        change qModel false (k.symm (L v)) = S.q v
        rw [← h1, hhL]
      · ext x
        constructor
        · intro hx
          rw [mem_mbarModel_iff] at hx
          obtain ⟨m, hm⟩ := hx
          have hxy : x = k⁻¹ * conjL L (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) * k := by
            rw [← hm]
            ext v
            simp [conjL_apply, LinearEquiv.trans_apply, MulAut.conj_apply, mul_assoc]
          rw [hxy]
          exact (hk (conjL L (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt))).mp
            (conjL_ρ_mem_mbarModel S L m)
        · intro hx
          rw [mem_mbarModel_iff]
          have hy : k * x * k⁻¹ ∈ mbarModel S L :=
            (hk (k * x * k⁻¹)).mpr (by simpa [mul_assoc] using hx)
          rw [mem_mbarModel_iff] at hy
          obtain ⟨m, hm⟩ := hy
          refine ⟨m, ?_⟩
          have hcomp : conjL (L.trans k.symm) (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) =
              k⁻¹ * conjL L (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) * k := by
            ext v
            simp [conjL_apply, LinearEquiv.trans_apply, mul_assoc]
          rw [hcomp, hm]
          group
  · exfalso
    haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
    have hdvd : Nat.card S.Mbar ∣ 51840 := by
      have hle : mbarModel S L ≤ O₀ true := mbarModel_le_O₀ S L hL
      have h := Subgroup.card_dvd_of_le hle
      rwa [card_mbarModel, card_O₀_true] at h
    rw [h336] at hdvd
    exact absurd hdvd (by decide)

theorem mbarModel_eq_omega (hP : Cert690.CensusPlusProp) (hF : Cert690.PGLFactsProp)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (hw : S.width = 3)
    (hirr : ¬ S.IsReducible)
    (hb : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g)
    (h20160 : Nat.card S.Mbar = 20160) (L : S.Qt ≃ₗ[ZMod 2] V₀)
    (hL : ∀ v, qModel false (L v) = S.q v) : mbarModel S L = Ω₀ false := by
  have hplus : ∀ v, qPlus (L v) = S.q v := hL
  rcases censusPlus_mbarModel S hw hirr hb L hplus hP with hΩ | hO | ⟨k, hkO, hk⟩
  · exact hΩ
  · exfalso
    have hc : Nat.card (mbarModel S L) = 40320 := by rw [hO]; exact card_O₀_false
    rw [card_mbarModel, h20160] at hc
    norm_num at hc
  · exfalso
    have hc : Nat.card (mbarModel S L) = 336 :=
      card_mbarModel_of_conj_KPGL S L hk hF.2.1
    rw [card_mbarModel, h20160] at hc
    norm_num at hc

theorem qtPlusType_of_card {G : Type} [Group G] [Finite G] (S : Setting G) (hw : S.width = 3)
    (hc : Nat.card S.Mbar = 336 ∨ Nat.card S.Mbar = 20160) : QtPlusType S := by
  have hdim : Module.finrank (ZMod 2) S.Qt = 6 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  obtain ⟨L, hL | hL⟩ := exists_linearEquiv_model (V := S.Qt) (Q := S.q) hdim S.q_nondegenerate
  · exact qtPlusType_of_qPlus S L hL hdim
  · exfalso
    haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
    have hdvd : Nat.card S.Mbar ∣ 51840 := by
      have hle : mbarModel S L ≤ O₀ true := mbarModel_le_O₀ S L hL
      have h := Subgroup.card_dvd_of_le hle
      rwa [card_mbarModel, card_O₀_true] at h
    rcases hc with h | h <;> rw [h] at hdvd <;> exact absurd hdvd (by decide)


end CFSG.GF2Type.Smith1979W3

end
