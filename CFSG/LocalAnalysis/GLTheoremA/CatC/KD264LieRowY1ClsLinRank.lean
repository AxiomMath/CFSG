module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsLinBound
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutLinCat
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDSp
public import CFSG.LocalAnalysis.SectionRank.PRankIndex

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag Matrix

variable {K : Type} [Field K]

theorem not_dvd_card_units_three [Finite K] (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0) :
    ¬ 3 ∣ Nat.card Kˣ := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype Kˣ := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 (by rwa [Nat.card_eq_fintype_card] at h)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    norm_num at hx
  have hxK : (x : K) ^ 3 = 1 := by
    have := congrArg Units.val hx3
    simpa using this
  have hxne : (x : K) ≠ 1 := fun h1 => hx1 (Units.ext h1)
  apply hω (x : K)
  have hfac : ((x : K) - 1) * ((x : K) ^ 2 + (x : K) + 1) = 0 := by linear_combination hxK
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact absurd (sub_eq_zero.mp h') hxne
  · exact h'

theorem not_dvd_card_scalars [Finite K] (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0) (n : ℕ) :
    ¬ 3 ∣ Nat.card (scalars n K) := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype (scalars n K) := Fintype.ofFinite _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 3 (by rwa [Nat.card_eq_fintype_card] at h)
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    norm_num at hz
  obtain ⟨c, -, hzc⟩ := mem_scalars.mp z.2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hz1 (Subsingleton.elim _ _)
  · have e1 : (z : Matrix.SpecialLinearGroup (Fin n) K) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hz3, Subgroup.coe_one]
    have h3m : ((z : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
      have h := Matrix.SpecialLinearGroup.coe_pow (z : Matrix.SpecialLinearGroup (Fin n) K) 3
      rw [e1, Matrix.SpecialLinearGroup.coe_one] at h
      exact h.symm
    have hm3 : scalar (Fin n) ((c : K) ^ 3) = 1 := by
      rw [hzc, ← map_pow] at h3m
      exact h3m
    have hc3 : (c : K) ^ 3 = 1 := by
      have h' := congrFun (congrFun hm3 ⟨0, hn⟩) ⟨0, hn⟩
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h'
    have hc1 : (c : K) ≠ 1 := by
      intro h1
      have hc1' : c = 1 := Units.ext h1
      have hzeq : ((z : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [hzc, hc1', Units.val_one, map_one]
      apply hz1
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      simp [hzeq]
    apply hω (c : K)
    have hfac : ((c : K) - 1) * ((c : K) ^ 2 + (c : K) + 1) = 0 := by linear_combination hc3
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact absurd (sub_eq_zero.mp h') hc1
    · exact h'

theorem sl_pRank_three_le [Finite K] (h3 : (3 : K) ≠ 0) (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0) (n : ℕ) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) ≤ n / 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (G := Matrix.SpecialLinearGroup (Fin n) K)
    Nat.prime_three.one_lt fun E _ hE => ?_
  let φ : Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K := Matrix.SpecialLinearGroup.toGL
  have hφ : Function.Injective φ := fun a b h => by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i j) h
    simpa [φ] using this
  have hcomm : ∀ g ∈ E.map φ, ∀ h ∈ E.map φ, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hexp : ∀ g ∈ E.map φ, g ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]
  have hcard : Nat.card (E.map φ) = Nat.card E := Subgroup.card_map_of_injective hφ
  have hb := card_le_pow_half_gl h3 hω (E.map φ) hcomm hexp
  rw [Fintype.card_fin, hcard] at hb
  exact hb

theorem projectiveSL_pRank_eq [Finite K] (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0) (n : ℕ) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL n K)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.SectionRank.pRank_quotient_eq (scalars n K) (not_dvd_card_scalars hω n)

theorem projectiveSL_pRank_le [Finite K] (h3 : (3 : K) ≠ 0) (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0)
    (n : ℕ) : CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL n K)) ≤ n / 2 := by
  rw [projectiveSL_pRank_eq hω n]
  exact sl_pRank_three_le h3 hω n

theorem projectiveSL_pRank_ge_four_of_two [Finite K] (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0)
    (hpK : ¬ 3 ∣ Nat.card K) (hpe : ∀ j : ℕ, 3 ∣ Nat.card K ^ j - 1 ↔ 2 ∣ j) {n : ℕ}
    (hn : 8 ≤ n) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL n K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGL : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (GL (Fin n) K)) :=
    CFSG.LocalAnalysis.RankFourTheoremC.le_pRank_GL_matrix (n := n) (e := 2) (r' := 4) hpK
      (by norm_num) hpe (by omega)
  let φ : Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K := Matrix.SpecialLinearGroup.toGL
  have hφ : Function.Injective φ := fun a b h => by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i j) h
    simpa [φ] using this
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (GL (Fin n) K)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) := by
    refine CFSG.SectionRank.pRank_top_le_of_mulEquiv_subgroup Nat.prime_three φ.range
      (MonoidHom.ofInjective hφ) ?_
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, Subgroup.index_ker]
    exact fun h => not_dvd_card_units_three hω (dvd_trans h (Subgroup.card_subgroup_dvd_card _))
  rw [projectiveSL_pRank_eq hω n]
  exact le_trans hGL hle

theorem projectiveSL_pRank_ge_four_of_five [Finite K] (h : 3 ∣ Nat.card K - 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL 5 K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := kdY1Out_exists_isPrimitiveRoot_three K h
  have hmu : Nat.card (kdY1Mu3 K) = 3 := hζ.card_rootsOfUnity
  let ψ : (Fin 4 → kdY1Mu3 K) →* projectiveSL 5 K :=
    (proj 5 K).comp ((kdY1Hom K (le_refl 5)).comp (kdY1Coord K))
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hx
    obtain ⟨c, hc5, hmat⟩ := hx
    rw [MonoidHom.comp_apply] at hmat
    have hentry : ∀ i : Fin 5, (kdY1Ent K (kdY1Coord K x) i : K) = (c : K) := by
      intro i
      have h' := congrFun (congrFun hmat i) i
      rw [kdY1Hom_apply_diag K (le_refl 5), Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h'
      exact h'
    have hc0 : c = ((x 0 : kdY1Mu3 K) : Kˣ) := by
      apply Units.ext
      have h' := hentry 0
      simpa [kdY1Ent, kdY1Coord] using h'.symm
    have hc3 : c ^ 3 = 1 := by
      rw [hc0]
      exact (mem_rootsOfUnity 3 _).mp (x 0).2
    have hc1 : c = 1 := by
      have h2 : c ^ 2 = 1 := by
        calc c ^ 2 = c ^ 5 * (c ^ 3)⁻¹ := by group
          _ = 1 := by rw [hc5, hc3, inv_one, mul_one]
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc3, h2, inv_one, mul_one]
    have hcoord : ∀ k : ℕ, (hk : k < 4) → ((x ⟨k, hk⟩ : kdY1Mu3 K) : Kˣ) = 1 := by
      intro k hk
      have h' := hentry ⟨k, by omega⟩
      rw [hc1, Units.val_one] at h'
      have h'' : kdY1Ent K (kdY1Coord K x) k = 1 := Units.ext (by simpa using h')
      simpa [kdY1Ent, hk, kdY1Coord] using h''
    rw [Subgroup.mem_bot]
    funext i
    exact Subtype.ext (by simpa using hcoord i.1 i.2)
  have hE : CFSG.Open.IsElemAbelian 3 ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
    · intro z hz
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hz
      have hy : y ^ 3 = 1 := by
        funext i
        have h3 : ((y i : kdY1Mu3 K) : Kˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp (y i).2
        apply Subtype.ext
        simpa using h3
      rw [← map_pow, hy, map_one]
  have hcard : Nat.card ψ.range = 3 ^ 4 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψ, Subgroup.card_top,
      Nat.card_fun, hmu]
    simp
  exact le_pRank_of_elemAbelian_card (k := 4) (by norm_num) le_top hE hcard

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
