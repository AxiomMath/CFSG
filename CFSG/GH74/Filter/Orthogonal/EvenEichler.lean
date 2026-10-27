module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.Witness
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.GH74.Filter

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin CFSG.SectionRank
  CFSG.SectionRank.ClassicalOdd CFSG.Assembly.LowTwoRank QuadraticMap Matrix

section EichlerRootGroup

variable {ι : Type} {K : Type} [Field K] {Q : QuadraticForm K (ι → K)}

def hypComplement (P : HypPair Q) : Submodule K (ι → K) :=
  LinearMap.ker ((polarBilin Q P.e).prod (polarBilin Q P.f))

theorem mem_hypComplement {P : HypPair Q} {w : ι → K} :
    w ∈ hypComplement P ↔ polar Q P.e w = 0 ∧ polar Q P.f w = 0 := by
  simp [hypComplement, LinearMap.mem_ker]

theorem finrank_hypComplement [Fintype ι] (P : HypPair Q) :
    Module.finrank K (hypComplement P) = Fintype.card ι - 2 := by
  have hsurj : Function.Surjective ((polarBilin Q P.e).prod (polarBilin Q P.f)) := by
    rintro ⟨a, b⟩
    refine ⟨a • P.f + b • P.e, ?_⟩
    simp [polar_add_right, polar_smul_right, P.polar_ef, P.polar_ee, P.polar_ff, P.polar_fe]
  have h := LinearMap.finrank_range_add_finrank_ker
    ((polarBilin Q P.e).prod (polarBilin Q P.f))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at h
  have h2 : 1 + 1 + Module.finrank K (hypComplement P) = Fintype.card ι := h
  omega

theorem card_hypComplement [Fintype ι] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (P : HypPair Q) :
    Nat.card (Multiplicative (hypComplement P)) = 2 ^ (f * (Fintype.card ι - 2)) := by
  rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := K),
    finrank_hypComplement, hK, ← pow_mul]

noncomputable def eichlerRootHom [Fintype ι] [DecidableEq ι] (P : HypPair Q) :
    Multiplicative (hypComplement P) →* GL ι K :=
  (toLinEquiv ι K).symm.toMonoidHom.comp
    { toFun := fun w => eichler Q P.e (w.toAdd : ι → K)
      map_one' := eichler_zero_right Q P.e
      map_mul' := fun a b => (eichler_mul (mem_hypComplement.1 a.toAdd.2).1
        (mem_hypComplement.1 b.toAdd.2).1).symm }

variable [Fintype ι] [DecidableEq ι]

theorem toLinEquiv_eichlerRootHom (P : HypPair Q) (w : Multiplicative (hypComplement P)) :
    toLinEquiv ι K (eichlerRootHom P w) = eichler Q P.e (w.toAdd : ι → K) := by
  simp [eichlerRootHom]

theorem eichlerRootHom_injective (P : HypPair Q) : Function.Injective (eichlerRootHom P) := by
  intro a b hab
  have h := congrArg (toLinEquiv ι K) hab
  rw [toLinEquiv_eichlerRootHom, toLinEquiv_eichlerRootHom] at h
  have hf : ∀ w : Multiplicative (hypComplement P),
      eichler Q P.e (w.toAdd : ι → K) P.f = P.f + (w.toAdd : ι → K) - Q w.toAdd • P.e := by
    intro w
    obtain ⟨h1, h2⟩ := mem_hypComplement.1 w.toAdd.2
    rw [eichler_apply P.Q_e h1, P.polar_fe, h2]
    simp
  have h1 := hf a
  rw [h, hf b] at h1
  have h2 : (a.toAdd : ι → K) - b.toAdd = (Q a.toAdd - Q b.toAdd) • P.e := by
    linear_combination (norm := module) h1.symm
  have h3 : Q a.toAdd - Q b.toAdd = 0 := by
    have h4 := congrArg (polar Q P.f) h2
    rw [polar_sub_right, polar_smul_right, P.polar_fe,
      (mem_hypComplement.1 a.toAdd.2).2, (mem_hypComplement.1 b.toAdd.2).2] at h4
    simpa using h4.symm
  rw [h3, zero_smul, sub_eq_zero] at h2
  exact Multiplicative.toAdd.injective (Subtype.ext h2)

theorem eichlerRootHom_apply_e (P : HypPair Q) (w : Multiplicative (hypComplement P)) :
    (eichlerRootHom P w : Matrix ι ι K) *ᵥ P.e = P.e := by
  rw [← toLinEquiv_apply, toLinEquiv_eichlerRootHom, eichler_apply_self]

theorem le_pRank_statedProj_statedOmega [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) (P : HypPair Q)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    f * (Fintype.card ι - 2) ≤
      CFSG.Open.pRank 2 (⊤ : Subgroup (StatedProj (StatedOmega Q₀))) := by
  have hΩ := statedOmega_eq_map_elementaryGroup hQ hE
  refine le_pRank_statedProj (by norm_num) multiplicative_comm
    (fun a => pow_char_eq_one (K := K) (p := 2) a) (card_hypComplement hK P) (eichlerRootHom P)
    (eichlerRootHom_injective P) (fun a => ?_) (v := P.e) P.e_ne_zero
    (eichlerRootHom_apply_e P)
  rw [hΩ]
  exact Subgroup.mem_map.2 ⟨eichler Q P.e (a.toAdd : ι → K), eichler_mem_elementaryGroup Q _ _, rfl⟩

end EichlerRootGroup

theorem t_POmegaPlus_even : S_POmegaPlus_even := by
  intro G _ _ n f hm
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have hn4 : 4 ≤ n := hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card hK
  have h := le_pRank_statedProj_statedOmega hK (coe_quadPlus n K)
    (plusPair K (⟨0, by omega⟩ : Fin n)) (commutator_orthogonalGroup_quadPlus (by omega))
  rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at h
  apply not_gen4_of_twoRank
  change 4 < CFSG.Open.pRank 2 (⊤ : Subgroup G)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  have h6 : 1 * 6 ≤ f * (n + n - 2) := Nat.mul_le_mul hf (by omega)
  omega

theorem t_POmegaMinus_even : S_POmegaMinus_even := by
  intro G _ _ n f hm
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
  have hn4 : 4 ≤ n := hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card hK
  have h := le_pRank_statedProj_statedOmega hK (coe_quadMinus n K b c)
    (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))) (commutator_orthogonalGroup_quadMinus hn4 hirr)
  rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at h
  apply not_gen4_of_twoRank
  change 4 < CFSG.Open.pRank 2 (⊤ : Subgroup G)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  have h6 : 1 * 6 ≤ f * (n - 1 + (n - 1 + 2) - 2) := Nat.mul_le_mul hf (by omega)
  omega

end CFSG.GH74.Filter
