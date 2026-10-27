module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeSpConj
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeProj
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeModelDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open Matrix CFSG.Open

namespace Sp6

section Main

variable {K : Type} [Field K]

theorem three_ne_zero_of_not_dvd_card [Finite K] (h : ¬ 3 ∣ Nat.card K) : (3 : K) ≠ 0 := by
  intro h0
  have : Fintype K := Fintype.ofFinite K
  have h3 : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
  haveI : CharP K 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr h3
  obtain ⟨m, -, hm⟩ := FiniteField.card K 3
  rw [← Nat.card_eq_fintype_card] at hm
  exact h (hm ▸ dvd_pow_self 3 m.pos.ne')

@[expose] def cycThree (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two_of]⟩

theorem cycThree_pow_three : cycThree K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem cycThree_ne_one : cycThree K ≠ 1 := by
  intro h
  have := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 1 0) h
  simp [cycThree] at this

theorem exists_order_three_commute {M : Matrix.SpecialLinearGroup (Fin 2) K} (hM : M ^ 3 = 1) :
    ∃ c : Matrix.SpecialLinearGroup (Fin 2) K, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute c M := by
  by_cases h1 : M = 1
  · exact ⟨cycThree K, cycThree_pow_three, cycThree_ne_one,
      by rw [h1]; exact Commute.one_right _⟩
  · exact ⟨M, hM, h1, Commute.refl M⟩

theorem le_pRank_of_conj_blkGL [Finite K] (g : StatedSp 3 K) (hg3 : g ^ 3 = 1)
    (P : GL (Fin 3 ⊕ Fin 3) K) (hP : P ∈ StatedSp 3 K)
    (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K)
    (hgM : (g : GL (Fin 3 ⊕ Fin 3) K) = P * blkGL M * P⁻¹) :
    3 ≤ pRank 3 (Subgroup.centralizer
      ({(QuotientGroup.mk g : StatedProj (StatedSp 3 K))} : Set (StatedProj (StatedSp 3 K)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconj : (g : GL (Fin 3 ⊕ Fin 3) K) = MulAut.conj P (blkGL M) := by
    rw [hgM, MulAut.conj_apply]
  have hM3 : ∀ i, M i ^ 3 = 1 := by
    have h1 : MulAut.conj P (blkGL (M ^ 3)) = MulAut.conj P (blkGL 1) := by
      rw [map_pow, map_pow, ← hconj, map_one, map_one, ← Subgroup.coe_pow, hg3]
      rfl
    have h2 := blkGL_injective ((MulAut.conj P).injective h1)
    intro i
    exact congrFun h2 i
  choose c hc3 hc1 hcM using fun i => exists_order_three_commute (hM3 i)
  have hcard : ∀ i, Nat.card (Subgroup.zpowers (c i)) = 3 := fun i => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hc3 i) (hc1 i)
  let ρ : (∀ i, Subgroup.zpowers (c i)) →* (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :=
    MonoidHom.pi fun i => (Subgroup.zpowers (c i)).subtype.comp
      (Pi.evalMonoidHom (fun j => ↥(Subgroup.zpowers (c j))) i)
  let φ : (∀ i, Subgroup.zpowers (c i)) →* GL (Fin 3 ⊕ Fin 3) K :=
    (MulAut.conj P).toMonoidHom.comp (blkGL.comp ρ)
  have hφ_apply : ∀ a, φ a = MulAut.conj P (blkGL (ρ a)) := fun a => rfl
  have hcomm : ∀ a b : (∀ i, Subgroup.zpowers (c i)), a * b = b * a := by
    intro a b
    funext i
    exact Subtype.ext (Subgroup.mul_comm_of_mem_isMulCommutative _ (a i).2 (b i).2)
  have hpow : ∀ a : (∀ i, Subgroup.zpowers (c i)), a ^ 3 = 1 := by
    intro a
    funext i
    have h := pow_card_eq_one' (G := Subgroup.zpowers (c i)) (x := a i)
    rw [hcard i] at h
    exact h
  have hA : Nat.card (∀ i, Subgroup.zpowers (c i)) = 3 ^ 3 := by
    rw [Nat.card_pi]
    simp [hcard]
  have hρ : Function.Injective ρ := by
    intro a a' h
    funext i
    exact Subtype.ext (congrFun h i)
  have hφ : Function.Injective φ := by
    intro a a' h
    exact hρ (blkGL_injective ((MulAut.conj P).injective h))
  have hH : ∀ a, φ a ∈ StatedSp 3 K := by
    intro a
    rw [hφ_apply, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hP (blkGL_mem_statedSp _))
      (Subgroup.inv_mem _ hP)
  have hsc : ∀ a, φ a ∈ StatedScalars (Fin 3 ⊕ Fin 3) K → a = 1 := by
    intro a ha
    rw [StatedScalars, MonoidHom.mem_range] at ha
    obtain ⟨u, hu⟩ := ha
    have hsp : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) u ∈ StatedSp 3 K := hu ▸ hH a
    have hu2 : u ^ 2 = 1 := (StatedAPI.scalar_mem_statedSp_iff (by norm_num) u).1 hsp
    have h2 : (φ a) ^ 2 = 1 := by
      rw [← hu, ← map_pow, hu2, map_one]
    have h3 : (φ a) ^ 3 = 1 := by rw [← map_pow, hpow a, map_one]
    have h1 : φ a = 1 := by
      calc φ a = (φ a) ^ 3 * ((φ a) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    exact hφ (h1.trans (map_one φ).symm)
  have hg : ∀ a, (g : GL (Fin 3 ⊕ Fin 3) K) * φ a = φ a * (g : GL (Fin 3 ⊕ Fin 3) K) := by
    intro a
    have hcommX : blkGL M * blkGL (ρ a) = blkGL (ρ a) * blkGL M := by
      rw [← map_mul, ← map_mul]
      congr 1
      funext i
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (a i).2
      have hk' : Commute (M i) (c i ^ k) := ((hcM i).zpow_left k).symm
      show M i * ((a i : Subgroup.zpowers (c i)) : Matrix.SpecialLinearGroup (Fin 2) K) =
        ((a i : Subgroup.zpowers (c i)) : Matrix.SpecialLinearGroup (Fin 2) K) * M i
      rw [← hk]
      exact hk'.eq
    rw [hconj, hφ_apply, ← map_mul (MulAut.conj P), ← map_mul (MulAut.conj P), hcommX]
  exact le_pRank_centralizer_statedProj hcomm hpow hA φ hφ hH hsc g hg

theorem statedSp_scalar_sq (z : StatedSp 3 K)
    (hz : z ∈ (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K)) : z ^ 2 = 1 := by
  have hz' := Subgroup.mem_subgroupOf.1 hz
  rw [StatedScalars, MonoidHom.mem_range] at hz'
  obtain ⟨u, hu⟩ := hz'
  have hsp : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) u ∈ StatedSp 3 K := hu ▸ z.2
  have hu2 : u ^ 2 = 1 := (StatedAPI.scalar_mem_statedSp_iff (by norm_num) u).1 hsp
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hu, ← map_pow, hu2, map_one]
  rfl

end Main

end Sp6

theorem i294CrossModelPSp6_holds : I294CrossModelPSp6 := by
  intro K _ _ hK x hx
  have h3 : (3 : K) ≠ 0 := Sp6.three_ne_zero_of_not_dvd_card hK
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  obtain ⟨g, hg3, rfl⟩ := exists_lift_pow_three (H := StatedSp 3 K) (N := 2) (by norm_num)
    (fun z hz => Sp6.statedSp_scalar_sq z hz) hx3
  have hg3' : (g : GL (Fin 3 ⊕ Fin 3) K) ^ 3 = 1 := by
    have := congrArg (fun h : StatedSp 3 K => (h : GL (Fin 3 ⊕ Fin 3) K)) hg3
    simpa using this
  obtain ⟨P, hP, M, hgM⟩ := Sp6.exists_conj_blkGL h3 (g : GL (Fin 3 ⊕ Fin 3) K) g.2 hg3'
  exact Sp6.le_pRank_of_conj_blkGL g hg3 P hP M hgM

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
