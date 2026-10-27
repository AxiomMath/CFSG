module

public import CFSG.LieType.Chevalley.OddRootPairPermutation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {τ : Tag} {K : Type} [Field K]

theorem rankOneRep_injective_of_charTwo
    [CharP K 2] (i : Fin τ.rank) :
    Function.Injective (rankOneRep τ K i) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨l, hl, hgl⟩ := rankOneRep_ker i g hg
  have hl1 : (l : K) = 1 := by
    have h2 : (l : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hl, Units.val_one]
    have h : ((l : K) - 1) ^ 2 = 0 := by
      linear_combination h2 + (1 - (l : K)) * CharTwo.two_eq_zero (R := K)
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)
  refine Subtype.ext ?_
  rw [hgl, hl1, one_smul]
  rfl

theorem exists_params_of_map_simple_of_charTwo
    [Finite K] [CharP K 2]
    {β : MulAut (adjointGroup τ K)} {i k : Fin τ.rank}
    (hX : (simplePosSubgroup τ K i).map β.toMonoidHom = simplePosSubgroup τ K k)
    (hY : (simpleNegSubgroup τ K i).map β.toMonoidHom = simpleNegSubgroup τ K k) :
    ∃ p : Kˣ × (K ≃+* K), (∀ c, β (adjX τ K i c) = adjX τ K k (p.1 * p.2 c)) ∧
      (∀ c, β (adjY τ K i c) = adjY τ K k (((p.1⁻¹ : Kˣ) : K) * p.2 c)) ∧
      ∀ t, β (adjD τ K i t) = adjD τ K k (Units.map p.2.toMonoidHom t) := by
  have hL : (rankOneSubgroup (τ := τ) (K := K) i).map β.toMonoidHom =
      rankOneSubgroup (τ := τ) (K := K) k := by
    rw [rankOneSubgroup, rankOneSubgroup, Subgroup.map_sup, hX, hY]
  have hbij : ∀ l : Fin τ.rank, Function.Bijective (rankOneRepL τ K l) := fun l =>
    ⟨fun _ _ hgh => rankOneRep_injective_of_charTwo l (congrArg Subtype.val hgh),
      rankOneRepL_surjective l⟩
  let ei := MulEquiv.ofBijective (rankOneRepL τ K i) (hbij i)
  let ek := MulEquiv.ofBijective (rankOneRepL τ K k) (hbij k)
  let γ : MulAut (SL(2, K)) :=
    (ei.trans ((β.subgroupMap _).trans (MulEquiv.subgroupCongr hL))).trans ek.symm
  have hγ : ∀ g, rankOneRep τ K k (γ g) = β (rankOneRep τ K i g) := fun g => by
    have h := congrArg Subtype.val (ek.apply_symm_apply
      (((β.subgroupMap _).trans (MulEquiv.subgroupCongr hL)) (ei g)))
    exact h
  have hρ : Function.Surjective (MonoidHom.id (SL(2, K))) := Function.surjective_id
  have hγmem : γ ∈ pairAutSubgroup (sl2RootX (MonoidHom.id (SL(2, K))))
      (sl2RootY (MonoidHom.id (SL(2, K)))) := by
    refine ⟨map_eq_of_intertwine (rankOneRep_injective_of_charTwo k) hγ ?_,
      map_eq_of_intertwine (rankOneRep_injective_of_charTwo k) hγ ?_⟩
    · rw [map_sl2RootX_id, map_sl2RootX_id, sl2RootX_rankOneRep, sl2RootX_rankOneRep, hX]
    · rw [map_sl2RootY_id, map_sl2RootY_id, sl2RootY_rankOneRep, sl2RootY_rankOneRep, hY]
  obtain ⟨p, ⟨hx, hy, hd⟩, -⟩ := (central_SL2_root_pair_semilinear_parameters
    (MonoidHom.id (SL(2, K))) hρ fun g hg => ⟨1, one_pow 2, by
      rw [MonoidHom.id_apply] at hg
      rw [hg, Units.val_one, one_smul]
      rfl⟩).1 γ hγmem
  refine ⟨p, fun c => ?_, fun c => ?_, fun t => ?_⟩
  · have := hx c
    simp only [MonoidHom.id_apply] at this
    rw [← rankOneRep_upper, ← hγ, this, rankOneRep_upper]
  · have := hy c
    simp only [MonoidHom.id_apply] at this
    rw [← rankOneRep_lower, ← hγ, this, rankOneRep_lower]
  · have := hd t
    simp only [MonoidHom.id_apply] at this
    rw [← rankOneRep_diag, ← hγ, this, rankOneRep_diag]

theorem card_le_two_of_ringEquiv_cube [Finite K] [CharP K 2] (θ : K ≃+* K)
    (hθ : ∀ s : K, s ≠ 0 → θ s = s ^ 3) : Nat.card K ≤ 2 := by
  classical
  have h01 : ∀ s : K, s = 0 ∨ s = 1 := by
    intro s
    by_cases hs0 : s = 0
    · exact Or.inl hs0
    right
    by_contra hs1
    have hs1' : s + 1 ≠ 0 := fun h => hs1 (by
      linear_combination h - CharTwo.two_eq_zero (R := K))
    have h1 := hθ (s + 1) hs1'
    rw [map_add, map_one, hθ s hs0] at h1
    have h2 : s * (s + 1) = 0 := by
      linear_combination -h1 - (s ^ 2 + s) * CharTwo.two_eq_zero (R := K)
    rcases mul_eq_zero.1 h2 with h | h
    · exact hs0 h
    · exact hs1' h
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  calc Fintype.card K = (Finset.univ : Finset K).card := Finset.card_univ.symm
    _ ≤ ({0, 1} : Finset K).card := Finset.card_le_card fun s _ => by
        rcases h01 s with rfl | rfl <;> simp
    _ ≤ 2 := Finset.card_le_two

theorem even_G2_opposite_Sylow_stabilizer_fixes_simple_pairs
    (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : 4 ≤ Nat.card K) {β : MulAut (adjointGroup Tag.G2 K)}
    (hβ : β ∈ unipotentPairAut Tag.G2 K) (i : Fin Tag.G2.rank) :
    (simplePosSubgroup Tag.G2 K i).map β.toMonoidHom = simplePosSubgroup Tag.G2 K i ∧
      (simpleNegSubgroup Tag.G2 K i).map β.toMonoidHom = simpleNegSubgroup Tag.G2 K i := by
  obtain ⟨π, hπ⟩ := exists_perm_map_simple hβ
  have hx : ∀ x : Fin Tag.G2.rank, x = ⟨0, by decide⟩ ∨ x = ⟨1, by decide⟩ := by decide
  have h0 : π ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
    rcases hx (π ⟨0, by decide⟩) with h0 | h0
    · exact h0
    exfalso
    have h1 : π ⟨1, by decide⟩ = ⟨0, by decide⟩ := by
      rcases hx (π ⟨1, by decide⟩) with h1 | h1
      · exact h1
      · exact absurd (π.injective (h1.trans h0.symm)) (by decide)
    obtain ⟨p0, hp0⟩ := exists_params_of_map_simple_of_charTwo (hπ ⟨0, by decide⟩).1
      (hπ ⟨0, by decide⟩).2
    obtain ⟨p1, hp1⟩ := exists_params_of_map_simple_of_charTwo (hπ ⟨1, by decide⟩).1
      (hπ ⟨1, by decide⟩).2
    have hcomp : ∀ t : Kˣ, Units.map p1.2.toMonoidHom
        (t ^ Tag.G2.cartan ⟨0, by decide⟩ ⟨1, by decide⟩) =
          Units.map p0.2.toMonoidHom t ^ Tag.G2.cartan (π ⟨0, by decide⟩) (π ⟨1, by decide⟩) :=
      fun t => torus_compat_of_params hp1.1 hp0.2.2 t
    have hc01 : Tag.G2.cartan ⟨0, by decide⟩ ⟨1, by decide⟩ = -1 := by decide
    have hc10 : Tag.G2.cartan ⟨1, by decide⟩ ⟨0, by decide⟩ = -3 := by decide
    have hcube : ∀ t : Kˣ, p1.2 (t : K) = p0.2 (t : K) ^ 3 := fun t => by
      have h := hcomp t
      rw [h0, h1, hc01, hc10, map_zpow, zpow_neg, zpow_neg, zpow_one, inv_inj] at h
      have h' := congrArg Units.val h
      rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map] at h'
      simpa using h'
    have hθ : ∀ s : K, s ≠ 0 → (p0.2.symm.trans p1.2) s = s ^ 3 := fun s hs => by
      have hs' : p0.2.symm s ≠ 0 := fun h => hs (by simpa using congrArg p0.2 h)
      have := hcube (Units.mk0 _ hs')
      simpa using this
    have := card_le_two_of_ringEquiv_cube (p0.2.symm.trans p1.2) hθ
    omega
  have h1 : π ⟨1, by decide⟩ = ⟨1, by decide⟩ := by
    rcases hx (π ⟨1, by decide⟩) with h1 | h1
    · exact absurd (π.injective (h1.trans h0.symm)) (by decide)
    · exact h1
  have hi : π i = i := by
    rcases hx i with rfl | rfl
    exacts [h0, h1]
  have := hπ i
  rwa [hi] at this

end CFSG.LieType.Chevalley
