module

public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  Polynomial
open scoped Matrix commutatorElement

set_option linter.unusedSectionVars false

theorem commutator_eq_top_of_simple_of_not_comm {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ x y : G, x * y ≠ y * x) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hb | ht
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    apply hxy
    have : ⁅x, y⁆ ∈ commutator G := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
      (Subgroup.mem_top y)
    rw [commutator_def] at hb
    have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := hb ▸ this
    have h2 : ⁅x, y⁆ = 1 := h1
    rw [commutatorElement_def] at h2
    calc x * y = x * y * (x⁻¹ * y⁻¹) * (x⁻¹ * y⁻¹)⁻¹ := by group
      _ = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h2, one_mul]
  · exact ht

section Arith

theorem ordTrialityD4_eq_eval (q : ℕ) (hq : 1 ≤ q) :
    ((ordTrialityD4 q : ℕ) : ℤ) =
      ((X ^ 12 : ℤ[X]) * (([1, 1, 2, 2, 3, 3, 6, 6, 12].map fun d => cyclotomic d ℤ).prod)).eval
        (q : ℤ) := by
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  unfold ordTrialityD4
  push_cast [Nat.cast_sub h6, Nat.cast_sub h2]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, eval_mul, eval_pow,
    eval_X, cyclotomic_one, cyclotomic_two, cyclotomic_three_eq, cyclotomic_six_eq,
    cyclotomic_twelve_eq, eval_sub, eval_add, eval_one, mul_one]
  ring

theorem ordProj_ordTrialityD4 {p q e : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hq2 : 2 ≤ q)
    (hpq : ¬ p ∣ q) (he : orderOf (q : ZMod p) = e) (hE : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6) :
    p ^ (ordTrialityD4 q).factorization p = (p ^ (q ^ e - 1).factorization p) ^ 2 := by
  have he0 : e ≠ 0 := by rcases hE with rfl | rfl | rfl | rfl <;> norm_num
  have hcount : ([1, 1, 2, 2, 3, 3, 6, 6, 12] : List ℕ).count e = 2 := by
    rcases hE with rfl | rfl | rfl | rfl <;> decide
  have hsplit := prod_cyclotomic_split e [1, 1, 2, 2, 3, 3, 6, 6, 12]
  have hR : ¬ (p : ℤ) ∣ ((X ^ 12 : ℤ[X]) *
      ((([1, 1, 2, 2, 3, 3, 6, 6, 12] : List ℕ).filter fun d => d ≠ e).map
        fun d => cyclotomic d ℤ).prod).eval (q : ℤ) := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [eval_mul, eval_pow, eval_X, eval_list_prod, hpz.dvd_mul]
    rintro (h | h)
    · exact hpq (Int.natCast_dvd_natCast.1 (hpz.dvd_of_dvd_pow h))
    · rw [hpz.dvd_prod_iff] at h
      obtain ⟨a, ha, hpa⟩ := h
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      rw [List.mem_filter] at hd
      have hde : d ≠ e := by simpa using hd.2
      have hd12 : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 ∨ d = 12 := by
        simpa using hd.1
      have hpd : ¬ p ∣ d := fun h' => by
        have hle := Nat.le_of_dvd (by rcases hd12 with rfl | rfl | rfl | rfl | rfl <;> norm_num) h'
        rcases hd12 with rfl | rfl | rfl | rfl | rfl <;>
          first | omega | (interval_cases p <;> first | omega | exact absurd hp (by norm_num))
      exact not_dvd_cyclotomic_eval_of_ne hp he hde hpd hpa
  have h1 := ordProj_cyclotomic_pow_mul_eval (m := 2) hp hq2 he he0 hR
  have h2 : ((ordTrialityD4 q : ℕ) : ℤ).natAbs = ordTrialityD4 q := Int.natAbs_natCast _
  rw [← h2, ordTrialityD4_eq_eval q (by omega), hsplit, hcount]
  rw [← h1]
  congr 3
  ring_nf

end Arith

section Descent

variable {ℓ f : ℕ} {K L : Type} [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]

theorem langDescent_triD4 (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (D : LangDatum Tag.D4 L) (hΦ : D.Φ = twistHom TwistTag.D4 L Fr) {p : ℕ} :
    LangDescent D p (triEmb K σ L) := by
  classical
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hrange := triEmb_range (K := K) (σ := σ) (L := L) hℓ hf hK hσ Fr hFr
  have hfix : D.fix = (triEmb K σ L).range := by
    rw [hrange]
    ext x
    rw [LangDatum.mem_fix, hΦ]
    rfl
  obtain ⟨-, -, -, hsimple, hnc⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f hℓ hf K hK L 1
      (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c) Fr hFr
  haveI := hsimple
  have hperf := commutator_eq_top_of_simple_of_not_comm hnc
  have hperfI : ⁅(triEmb K σ L).range, (triEmb K σ L).range⁆ = (triEmb K σ L).range := by
    have h1 : (triEmb K σ L).range = Subgroup.map (triEmb K σ L) ⊤ := MonoidHom.range_eq_map _
    calc ⁅(triEmb K σ L).range, (triEmb K σ L).range⁆
        = ⁅Subgroup.map (triEmb K σ L) ⊤, Subgroup.map (triEmb K σ L) ⊤⁆ := by rw [← h1]
      _ = Subgroup.map (triEmb K σ L) ⁅(⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :=
          (Subgroup.map_commutator _ _ _).symm
      _ = Subgroup.map (triEmb K σ L) ⊤ := by rw [← commutator_def, hperf]
      _ = (triEmb K σ L).range := h1.symm
  refine ⟨?_, hfix.ge, fun P hP _ => hfix ▸ hP, ?_⟩
  · rw [hfix]
    exact Finite.of_surjective (triEmb K σ L).rangeRestrict (triEmb K σ L).rangeRestrict_surjective
  · rw [hfix]
    exact hperfI

end Descent

end CFSG.HardMathSupport.Timmesfeld.LangTorus
