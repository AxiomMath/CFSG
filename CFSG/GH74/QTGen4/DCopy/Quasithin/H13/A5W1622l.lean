module

public import CFSG.Quasithin.H13.A5W1622l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622h

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.SL3Model (natAct3 natAct3_apply)

variable {F : Type} [Field F]

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_sumNatural_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    {M : Subgroup G} {F : Type} [Field F] [Fintype F] {n : ℕ} (hFn : Fintype.card F = 2 ^ n)
    {α : ↥K₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj K₀ α) {k : ℕ}
    (hM : IsSumOfNaturalModulesVia K₀ M ⊥ α false k)
    (hcommA : ∀ x ∈ K₀, x⁻¹ * S.a * x * S.a⁻¹ ∈ M) (he2M : S.e2 ∈ M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := n)
    (by rw [Nat.card_eq_fintype_card, hFn])
  obtain ⟨hKM, -, β, -, hβk, hβe⟩ := hM
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]

  have hN2 : ∀ w : Multiplicative (Fin k → Fin 3 → F), w ^ 2 = 1 := by
    intro w
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i j
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((2 : ℕ) : F) = 0 from CharP.cast_eq_zero F 2, zero_mul]
  have hA2 : ∀ x ∈ M, x ^ 2 = 1 := by
    intro x hx
    have h := hN2 (β ⟨x, hx⟩)
    rw [← map_pow] at h
    have h1 : (⟨x, hx⟩ : ↥M) ^ 2 = 1 := hβinj (h.trans (map_one β).symm)
    exact congrArg Subtype.val h1
  have hAc : ∀ x ∈ M, ∀ x' ∈ M, x * x' = x' * x := by
    intro x hx x' hx'
    have h : β (⟨x, hx⟩ * ⟨x', hx'⟩) = β (⟨x', hx'⟩ * ⟨x, hx⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (hβinj h)
  have hlA : ∀ y ∈ S.Lv, y * S.e2 * y⁻¹ ∈ M := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hKM (hLvK₀ hy)) _).mp he2M

  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  let α' : ↥K₀ →* Matrix.SpecialLinearGroup (Fin 3) F := e.symm.toMonoidHom.comp α
  have hα' : Function.Surjective α' := e.symm.surjective.comp hα.1
  have hβe' : ∀ (ℓ : ↥K₀) (u v : ↥M), (v : G) = ℓ * u * ℓ⁻¹ →
      β v = natActK k (α' ℓ) (β u) := by
    intro ℓ u v h
    apply Multiplicative.toAdd.injective
    funext i
    rw [natActK_apply, hβe ℓ u v h i]
    change _ = ((α' ℓ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ _
    rw [show α' ℓ = e.symm (α ℓ) from rfl, coe_symm_statedSL]
    rfl
  exact S.false_of_closing_model_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ hKM (Zc := ⊥) bot_le hA2 hAc hcommA he2M hlA hN2 (natActK k)
    (SzN2.isSylowTwoOf_unitriangular (K := F) (n := 3) (by norm_num)) (modelFix_natK k) α' hα'
    β (by rw [hβk]) hβe'

theorem false_of_sl3Block_gen_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hblk : IsSL3Block K₀) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, n, F, _, _, hFn, α, hα, -, β, hβ, hβk, hβe⟩ := hblk
  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := n)
    (by rw [Nat.card_eq_fintype_card, hFn])
  obtain ⟨hcommA, he2U, hlA, hU2, hUc⟩ :=
    S.closing_data_blockU_F4 h1222 h517 hK₀G hK₀ hTK₀ hLvK₀ hchar hshort
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  let α' : ↥K₀ →* Matrix.SpecialLinearGroup (Fin 3) F := e.symm.toMonoidHom.comp α
  have hα' : Function.Surjective α' := e.symm.surjective.comp hα
  have hβe' : ∀ (ℓ : ↥K₀) (u v : ↥(blockU K₀)), (v : G) = ℓ * u * ℓ⁻¹ →
      β v = natAct3 (α' ℓ) (β u) := by
    intro ℓ u v h
    rw [natAct3_apply]
    apply Multiplicative.toAdd.injective
    rw [hβe ℓ u v h, toAdd_ofAdd]
    change _ = ((α' ℓ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ _
    rw [show α' ℓ = e.symm (α ℓ) from rfl, coe_symm_statedSL]
  have hN2 : ∀ w : SL3Model.W3 F, w ^ 2 = 1 := by
    intro w
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((2 : ℕ) : F) = 0 from CharP.cast_eq_zero F 2, zero_mul]
  exact S.false_of_closing_model_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ (C1.le_normalizer_blockU K₀) (Zc := blockZ K₀) inf_le_right hU2 hUc hcommA
    he2U hlA hN2 natAct3 (SzN2.isSylowTwoOf_unitriangular (K := F) (n := 3) (by norm_num))
    modelFix_natAct3 α' hα' β hβk hβe'

end Setting

end CFSG.Quasithin.H13.A5
