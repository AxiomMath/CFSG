module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGenPCentral
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.AGLEmbedding.ThompsonGen

open scoped IsMulCommutative

theorem card_GL_fin_zmod (p : ℕ) [Fact p.Prime] (r : ℕ) :
    ∃ u : ℕ, ¬ p ∣ u ∧ Nat.card (GL (Fin r) (ZMod p)) = p ^ (r * (r - 1) / 2) * u := by
  have hp : p.Prime := Fact.out
  refine ⟨∏ i : Fin r, (p ^ (r - (i : ℕ)) - 1), ?_, ?_⟩
  · intro hdvd
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    have h1 : p ∣ p ^ (r - (i : ℕ)) := dvd_pow_self p (by have := i.2; omega)
    have h2 : p ∣ 1 := by
      have h3 := Nat.dvd_sub h1 hi
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  · refine (Matrix.card_GL_field (𝔽 := ZMod p) r).trans ?_
    rw [ZMod.card]
    have h : ∀ i : Fin r, p ^ r - p ^ (i : ℕ) = p ^ (i : ℕ) * (p ^ (r - (i : ℕ)) - 1) := by
      intro i
      rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' i.2.le]
    rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem rank_le_of_card_eq_pow {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
    (hY : IsPGroup p Y) {a : ℕ} (h : Nat.card Y = p ^ a) : Group.rank Y ≤ a := by
  have h1 := pow_rank_le_card_quotient_frattini hY
  have h2 : Nat.card (Y ⧸ frattini Y) ≤ Nat.card Y :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 (h1.trans (h2.trans h.le))

theorem rank_range_le_gl {p : ℕ} [Fact p.Prime] {B : Type*} [Group B] [Finite B]
    (hB : IsPGroup p B) {r : ℕ} (ψ : B →* GL (Fin r) (ZMod p)) :
    Group.rank ψ.range ≤ r * (r - 1) / 2 := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu, hcard⟩ := card_GL_fin_zmod p r
  have hY : IsPGroup p ψ.range := hB.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hY
  have hdvd : Nat.card ψ.range ∣ Nat.card (GL (Fin r) (ZMod p)) :=
    Subgroup.card_subgroup_dvd_card _
  rw [ha, hcard] at hdvd
  have hcop : Nat.Coprime (p ^ a) u :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hu)
  have hdvd' : p ^ a ∣ p ^ (r * (r - 1) / 2) := hcop.dvd_of_dvd_mul_right hdvd
  have ha_le : a ≤ r * (r - 1) / 2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd'
  exact (rank_le_of_card_eq_pow hY ha).trans ha_le

theorem exists_hom_gl {p : ℕ} [Fact p.Prime] {E B : Type*} [Group E] [Finite E]
    [CFSG.IsElementaryAbelian p E] [Group B] (φ : B →* MulAut E) :
    ∃ ψ : B →* GL (Fin (Module.finrank (ZMod p) (Additive E))) (ZMod p),
      ∀ b, ψ b = 1 → φ b = 1 := by
  let V := Additive E
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let ρ : B →* Module.End (ZMod p) V :=
    { toFun := fun b => (MonoidHom.toAdditive (φ b).toMonoidHom).toZModLinearMap p
      map_one' := by
        ext v
        simp only [map_one]
        rfl
      map_mul' := fun b b' => by
        ext v
        simp only [map_mul]
        rfl }
  let e : V ≃ₗ[ZMod p] (Fin (Module.finrank (ZMod p) V) → ZMod p) :=
    (Module.finBasis (ZMod p) V).equivFun
  let θ : LinearMap.GeneralLinearGroup (ZMod p) V ≃*
      GL (Fin (Module.finrank (ZMod p) V)) (ZMod p) :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans Matrix.GeneralLinearGroup.toLin.symm
  refine ⟨(θ : _ →* _).comp (MonoidHom.toHomUnits ρ), fun b hb => ?_⟩
  have h1 : MonoidHom.toHomUnits ρ b = 1 := (MulEquiv.map_eq_one_iff θ).1 hb
  have h2 : ρ b = 1 := by
    have := congrArg (fun u : (Module.End (ZMod p) V)ˣ => (u : Module.End (ZMod p) V)) h1
    simpa using this
  ext x
  have h3 := LinearMap.congr_fun h2 (Additive.ofMul x)
  exact congrArg Additive.toMul h3

theorem rank_le_rank_ker_add_rank_range {B A : Type*} [Group B] [Finite B] [Group A] [Finite A]
    (ψ : B →* A) : Group.rank B ≤ Group.rank ψ.ker + Group.rank ψ.range := by
  classical
  obtain ⟨S, hSc, hS⟩ := Group.rank_spec ψ.ker
  obtain ⟨T, hTc, hT⟩ := Group.rank_spec ψ.range
  have hlift : ∀ t : ψ.range, ∃ b : B, ψ b = t := fun t => t.2
  choose f hf using hlift
  let U : Finset B := S.image (fun s : ψ.ker => (s : B)) ∪ T.image f
  have hker : ψ.ker ≤ Subgroup.closure (U : Set B) := by
    have h1 : (Subgroup.closure S).map ψ.ker.subtype ≤ Subgroup.closure (U : Set B) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨s, hs, rfl⟩
      exact Subgroup.subset_closure (Finset.mem_coe.2 (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hs))))
    rwa [hS, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  have hrange : ψ.range ≤ (Subgroup.closure (U : Set B)).map ψ := by
    have h1 : (Subgroup.closure T).map ψ.range.subtype ≤
        (Subgroup.closure (U : Set B)).map ψ := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨f t, Subgroup.subset_closure (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image_of_mem f (Finset.mem_coe.1 ht)))), hf t⟩
    rwa [hT, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  have hU : Subgroup.closure (U : Set B) = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨l, hl, hlb⟩ := hrange ⟨b, rfl⟩
    have hk : l⁻¹ * b ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlb, inv_mul_cancel]
    have := Subgroup.mul_mem _ hl (hker hk)
    simpa using this
  calc Group.rank B ≤ U.card := Group.rank_le hU
    _ ≤ (S.image (fun s : ψ.ker => (s : B))).card + (T.image f).card := Finset.card_union_le _ _
    _ ≤ S.card + T.card := add_le_add Finset.card_image_le Finset.card_image_le
    _ = Group.rank ψ.ker + Group.rank ψ.range := by rw [hSc, hTc]

end CFSG.AGLEmbedding.ThompsonGen
