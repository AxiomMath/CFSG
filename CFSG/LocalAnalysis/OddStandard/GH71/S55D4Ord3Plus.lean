module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Move
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OddIdx
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MonoNF
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeNF
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2D4Leaf
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.OddAut


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

omit
  [Finite K] in
theorem weylY_eq_one_iff (n : monoY σ) :
    weylY σ n = 1 ↔ ((n : 𝒞) : ModGL TwistTag.D4.tag K) ∈
      graphFixedTorus TwistTag.D4 K σ.toRingHom := by
  change graphFixedWeylHom TwistTag.D4 K σ.toRingHom ⟨(n : 𝒞).1, n.2⟩ = 1 ↔ _
  rw [← MonoidHom.mem_ker, graphFixedWeylHom_ker, Subgroup.mem_subgroupOf]

theorem d4_fieldActor_cube {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [hσ3, map_one] at h
  exact h.symm

theorem d4_ord3Alt_inner_plus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1)
    (g : 𝒞) (hg : MulAut.conj g ^ 3 = 1) : Ord3Alt p (MulAut.conj g) := by
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  have hg3 : g * g * g = 1 := hinj (by rw [map_mul, map_mul, map_one, ← pow_three']; exact hg)
  obtain ⟨y, n, hnN, hconj⟩ := exists_conj_mem_of_index_not_dvd (1 : MulAut 𝒞) (fun _ => rfl)
    (monoY σ) (fun _ h => h) (d4_monomial_index_not_dvd hp hp2 hf K hK σ hσ hq) g
    (by change g * g * g = 1; exact hg3)
  rw [mul_one, mul_one] at hconj
  refine ord3Alt_of_conj (MulAut.conj y) ?_
  rw [hconj]
  set nm : monoY σ := ⟨n, hnN⟩
  by_cases hT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · have h := d4_normalizesPSub_toral σ (ℓ := p) hT 1
    rw [fieldActor_one, mul_one] at h
    exact Or.inl h
  · have hn3 : nm ^ 3 = 1 := by
      refine Subtype.ext (hinj ?_)
      change MulAut.conj (n ^ 3) = MulAut.conj 1
      rw [map_pow, ← hconj, conj_pow, hg, mul_one, mul_inv_cancel, map_one]
    have hw3 : weylY σ nm ^ 3 = 1 := by rw [← map_pow, hn3, map_one]
    have hw1 : weylY σ nm ≠ 1 := fun h => hT ((weylY_eq_one_iff σ nm).1 h)
    have h := d4_movesAbelianTwo σ hp hp2 hf hK hσ nm hw3 hw1 1
    rw [fieldActor_one, mul_one] at h
    exact Or.inr h

theorem d4_ord3Alt_outer_plus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1)
    (φ : MulAut 𝒞) (hφ : orderOf φ = 3)
    (hout : φ ∉ (MulAut.conj : 𝒞 →* MulAut 𝒞).range) : Ord3Alt p φ := by
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  obtain ⟨g, hg, hφg⟩ := d4_outer_three_normal_form hp hp2 hf K hK σ hσ φ hφ hout
  suffices key : Ord3Alt p (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) by
    rcases hφg with h | h
    · rw [h]
      exact key
    · apply ord3Alt_of_inv
      rw [h]
      exact key
  have hfA3 := d4_fieldActor_cube σ hK hσ
  obtain ⟨y, n, hnM, hconj⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
  refine ord3Alt_of_conj (MulAut.conj y) ?_
  rw [hconj]
  by_cases hT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · exact Or.inl (d4_normalizesPSub_toral σ hT σ)
  · set nm : monoY σ := ⟨n, Subgroup.mem_subgroupOf.2 hnM⟩
    have hψ3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
      rw [← hconj, conj_pow, conj_mul_pow_eq, hg, map_one, one_mul, hfA3, mul_one,
        mul_inv_cancel]
    have hNs : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1 :=
      normSeq_eq_one_of_pow_eq_one hZ hfA3 hψ3
    have hN3 : nm * actY σ σ nm * actY σ σ (actY σ σ nm) = 1 := by
      refine Subtype.ext ?_
      have h : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = n * fieldActor σ σ n *
          fieldActor σ σ (fieldActor σ σ n) := by
        simp only [normSeq, pow_two, MulAut.mul_apply, MulAut.one_apply, pow_zero, pow_one,
          one_mul]
      change n * fieldActor σ σ n * fieldActor σ σ (fieldActor σ σ n) = 1
      rw [← h]
      exact hNs
    have hw3 : weylY σ nm ^ 3 = 1 := by
      have h := congrArg (weylY σ) hN3
      simp only [map_mul, weylY_actY, map_one] at h
      rw [pow_three']
      exact h
    have hw1 : weylY σ nm ≠ 1 := fun h => hT ((weylY_eq_one_iff σ nm).1 h)
    exact Or.inr (d4_movesAbelianTwo σ hp hp2 hf hK hσ nm hw3 hw1 σ)

theorem d4_ord3Alt_plus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1)
    (b : MulAut 𝒞) (hb : orderOf b = 3) : Ord3Alt p b := by
  by_cases hin : b ∈ (MulAut.conj : 𝒞 →* MulAut 𝒞).range
  · obtain ⟨g, rfl⟩ := hin
    exact d4_ord3Alt_inner_plus σ hp hp2 hf hK hσ hq g (by rw [← hb]; exact pow_orderOf_eq_one _)
  · exact d4_ord3Alt_outer_plus σ hp hp2 hp3 hf hK hσ hq b hb hin

end CFSG.OddStandard.GH71.S55
